(*  Title:      Pure/Tools/codegen_names.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Naming policies for code generation: prefixing any name by corresponding theory name,
conversion to alphanumeric representation, name space identifier.
Mappings are incrementally cached.
*)

signature CODEGEN_NAMES =
sig
  type tyco = string
  type const = string
  val class: theory -> class -> class
  val class_rev: theory -> class -> class option
  val classrel: theory -> class * class -> string
  val classrel_rev: theory -> string -> (class * class) option
  val tyco: theory -> tyco -> tyco
  val tyco_rev: theory -> tyco -> tyco option
  val instance: theory -> class * tyco -> string
  val instance_rev: theory -> string -> (class * tyco) option
  val const: theory -> CodegenConsts.const -> const
  val const_rev: theory -> const -> CodegenConsts.const option
  val labelled_name: theory -> string -> string

  val check_modulename: string -> string
  val purify_var: string -> string
  val purify_tvar: string -> string
  
  type var_ctxt;
  val make_vars: string list -> var_ctxt;
  val intro_vars: string list -> var_ctxt -> var_ctxt;
  val lookup_var: var_ctxt -> string -> string;
end;

structure CodegenNames: CODEGEN_NAMES =
struct

(** purification **)

val purify_name =
  let
    fun is_valid s = Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s orelse s = "'";
    val is_junk = not o is_valid andf Symbol.not_eof;
    val junk = Scan.many is_junk;
    val scan_valids = Symbol.scanner "Malformed input"
      ((junk |--
        (Scan.optional (Scan.one Symbol.is_ascii_letter) "x" ^^ (Scan.many is_valid >> implode)
        --| junk))
      -- Scan.repeat ((Scan.many1 is_valid >> implode) --| junk) >> op ::);
  in explode #> scan_valids #> space_implode "_" end;

fun purify_op "0" = "zero"
  | purify_op "1" = "one"
  | purify_op s =
      let
        fun rep_op "+" = SOME "sum"
          | rep_op "-" = SOME "diff"
          | rep_op "*" = SOME "prod"
          | rep_op "/" = SOME "quotient"
          | rep_op "&" = SOME "conj"
          | rep_op "|" = SOME "disj"
          | rep_op "=" = SOME "eq"
          | rep_op "~" = SOME "inv"
          | rep_op "@" = SOME "append"
          | rep_op s = NONE;
        val scan_valids = Symbol.scanner "Malformed input"
           (Scan.repeat (Scan.some rep_op || Scan.one Symbol.not_eof));
      in (explode #> scan_valids #> implode) s end;

val purify_lower =
  explode
  #> (fn cs => (if forall Symbol.is_ascii_upper cs
        then map else nth_map 0) Symbol.to_ascii_lower cs)
  #> implode;

val purify_upper = explode #> nth_map 0 Symbol.to_ascii_upper #> implode;


(** global names (identifiers) **)

(* theory data *)

type tyco = string;
type const = string;
val string_pair_ord = prod_ord fast_string_ord fast_string_ord;
val eq_string_pair = is_equal o string_pair_ord;
structure Consttab = CodegenConsts.Consttab;

structure StringPairTab =
  TableFun(
    type key = string * string;
    val ord = string_pair_ord;
  );

datatype names = Names of {
  class: class Symtab.table * class Symtab.table,
  classrel: string StringPairTab.table * (class * class) Symtab.table,
  tyco: tyco Symtab.table * tyco Symtab.table,
  instance: string StringPairTab.table * (class * tyco) Symtab.table,
  const: const Consttab.table * (string * typ list) Symtab.table
}

val empty_names = Names {
  class = (Symtab.empty, Symtab.empty),
  classrel = (StringPairTab.empty, Symtab.empty),
  tyco = (Symtab.empty, Symtab.empty),
  instance = (StringPairTab.empty, Symtab.empty),
  const = (Consttab.empty, Symtab.empty)
};

local
  fun mk_names (class, classrel, tyco, instance, const) =
    Names { class = class, classrel = classrel, tyco = tyco, instance = instance, const = const};
  fun map_names f (Names { class, classrel, tyco, instance, const }) =
    mk_names (f (class, classrel, tyco, instance, const));
  val eq_string = op = : string * string -> bool;
in
  fun merge_names (Names { class = (class1, classrev1),
      classrel = (classrel1, classrelrev1), tyco = (tyco1, tycorev1),
      instance = (instance1, instancerev1), const = (const1, constrev1) },
    Names { class = (class2, classrev2),
      classrel = (classrel2, classrelrev2), tyco = (tyco2, tycorev2),
      instance = (instance2, instancerev2), const = (const2, constrev2) }) =
    mk_names ((Symtab.merge eq_string (class1, class2), Symtab.merge eq_string (classrev1, classrev2)),
      (StringPairTab.merge eq_string (classrel1, classrel2), Symtab.merge eq_string_pair (classrelrev1, classrelrev2)),
      (Symtab.merge eq_string (tyco1, tyco2), Symtab.merge eq_string (tycorev1, tycorev2)),
      (StringPairTab.merge eq_string (instance1, instance2), Symtab.merge eq_string_pair (instancerev1, instancerev2)),
      (Consttab.merge eq_string (const1, const2), Symtab.merge CodegenConsts.eq_const (constrev1, constrev2)));
  fun map_class f = map_names
    (fn (class, classrel, tyco, inst, const) => (f class, classrel, tyco, inst, const));
  fun map_classrel f = map_names
    (fn (class, classrel, tyco, inst, const) => (class, f classrel, tyco, inst, const));
  fun map_tyco f = map_names
    (fn (class, classrel, tyco, inst, const) => (class, classrel, f tyco, inst, const));
  fun map_inst f = map_names
    (fn (class, classrel, tyco, inst, const) => (class, classrel, tyco, f inst, const));
  fun map_const f = map_names
    (fn (class, classrel, tyco, inst, const) => (class, classrel, tyco, inst, f const));

end; (*local*)

structure CodeName = TheoryDataFun
(struct
  val name = "Pure/codegen_names";
  type T = names ref;
  val empty = ref empty_names;
  fun copy (ref names) = ref names;
  val extend = copy;
  fun merge _ (ref names1, ref names2) = ref (merge_names (names1, names2));
  fun print _ _ = ();
end);

val _ = Context.add_setup CodeName.init;


(* forward lookup with cache update *)

fun get thy get_tabs get upd_names upd policy x =
  let
    val names_ref = CodeName.get thy
    val (Names names) = ! names_ref;
    val tabs = get_tabs names;
    fun declare name =
      let
        val names' = upd_names (K (upd (x, name) (fst tabs),
          Symtab.update_new (name, x) (snd tabs))) (Names names)
      in (names_ref := names'; name) end;
  in case get (fst tabs) x
   of SOME name => name
    | NONE => 
        x
        |> policy thy
        |> Name.variant (Symtab.keys (snd tabs))
        |> declare
  end;


(* backward lookup *)

fun rev thy get_tabs errname name =
  let
    val names_ref = CodeName.get thy
    val (Names names) = ! names_ref;
    val tab = (snd o get_tabs) names;
  in case Symtab.lookup tab name
   of SOME x => x
    | NONE => error ("No such " ^ errname ^ ": " ^ quote name)
  end;


(* theory name lookup *)

fun thyname_of thy f errmsg x =
  let
    fun thy_of thy =
      if f thy x then case get_first thy_of (Theory.parents_of thy)
        of NONE => SOME thy
         | thy => thy
      else NONE;
  in case thy_of thy
   of SOME thy => Context.theory_name thy
    | NONE => error (errmsg x) end;

fun thyname_of_class thy =
  thyname_of thy (fn thy => member (op =) (Sign.all_classes thy))
    (fn class => "thyname_of_class: no such class: " ^ quote class);

fun thyname_of_classrel thy =
  thyname_of thy (fn thy => fn (class1, class2) => Sign.subsort thy ([class1], [class2]))
    (fn (class1, class2) => "thyname_of_classrel: no such classrel: " ^ quote class1 ^ " in " ^ quote class2);

fun thyname_of_tyco thy =
  thyname_of thy Sign.declared_tyname
    (fn tyco => "thyname_of_tyco: no such type constructor: " ^ quote tyco);

fun thyname_of_instance thy =
  let
    fun test_instance thy (class, tyco) =
      can (Sorts.mg_domain (Sign.classes_of thy) tyco) [class]
  in thyname_of thy test_instance
    (fn (class, tyco) => "thyname_of_instance: no such instance: " ^ quote class ^ ", " ^ quote tyco)
  end;

fun thyname_of_const thy =
  thyname_of thy Sign.declared_const
    (fn c => "thyname_of_const: no such constant: " ^ quote c);


(* naming policies *)

val purify_idf = purify_op #> purify_name;
val purify_prefix = map (purify_idf #> purify_upper);
val purify_base = purify_idf #> purify_lower;

val dotify =
  explode
  (*should disappear as soon as hierarchical theory name spaces are available*)
  #> Symbol.scanner "Malformed name"
      (Scan.repeat ($$ "_" |-- $$ "_" >> (fn _ => ".") || Scan.one Symbol.not_eof))
  #> implode;

fun policy thy get_basename get_thyname name =
  let
    val prefix = (purify_prefix o NameSpace.explode o dotify o get_thyname thy) name;
    val base = (purify_base o get_basename) name;
  in NameSpace.implode (prefix @ [base]) end;

fun class_policy thy = policy thy NameSpace.base thyname_of_class;
fun classrel_policy thy = policy thy (fn (class1, class2) => 
  NameSpace.base class2 ^ "_" ^ NameSpace.base class1) thyname_of_classrel;
fun tyco_policy thy = policy thy NameSpace.base thyname_of_tyco;
fun instance_policy thy = policy thy (fn (class, tyco) => 
  NameSpace.base class ^ "_" ^ NameSpace.base tyco) thyname_of_instance;

fun force_thyname thy (const as (c, tys)) =
  case AxClass.class_of_param thy c
   of SOME class => (case tys
       of [Type (tyco, _)] => SOME (thyname_of_instance thy (class, tyco))
        | _ => SOME (thyname_of_class thy class))
    | NONE => (case CodegenData.get_datatype_of_constr thy const
   of SOME dtco => SOME (thyname_of_tyco thy dtco)
    | NONE => (case CodegenConsts.find_def thy const
   of SOME ((thyname, _), _) => SOME thyname
    | NONE => NONE));

fun const_policy thy (c, tys) =
  case force_thyname thy (c, tys)
   of NONE => policy thy NameSpace.base thyname_of_const c
    | SOME thyname => let
        val prefix = (purify_prefix o NameSpace.explode o dotify) thyname;
        val tycos = map_filter (fn Type (tyco, _) => SOME tyco | _ => NONE) tys;
        val base = map (purify_base o NameSpace.base) (c :: tycos);
      in NameSpace.implode (prefix @ [space_implode "_" base]) end;


(* shallow name spaces *)

val nsp_class = "class";
val nsp_classrel = "clsrel"
val nsp_tyco = "tyco";
val nsp_inst = "inst";
val nsp_const = "const";

val nsp_mapping = [
  (nsp_class,       "class"),
  (nsp_classrel,    "class relation"),
  (nsp_tyco,        "type constructor"),
  (nsp_inst,        "instance"),
  (nsp_const,       "constant")
]

fun add_nsp nsp name =
  NameSpace.append name nsp

fun dest_nsp nsp name =
  if NameSpace.base name = nsp
  then SOME (NameSpace.qualifier name)
  else NONE;


(* external interfaces *)

fun class thy =
  get thy #class Symtab.lookup map_class Symtab.update class_policy
  #> add_nsp nsp_class;
fun classrel thy =
  get thy #classrel StringPairTab.lookup map_classrel StringPairTab.update classrel_policy
  #> add_nsp nsp_classrel;
fun tyco thy =
  get thy #tyco Symtab.lookup map_tyco Symtab.update tyco_policy
  #> add_nsp nsp_tyco;
fun instance thy =
  get thy #instance StringPairTab.lookup map_inst StringPairTab.update instance_policy
  #> add_nsp nsp_inst;
fun const thy =
  CodegenConsts.norm thy
  #> get thy #const Consttab.lookup map_const Consttab.update const_policy 
  #> add_nsp nsp_const;

fun class_rev thy =
  dest_nsp nsp_class
  #> Option.map (rev thy #class "class");
fun classrel_rev thy =
  dest_nsp nsp_classrel
  #> Option.map (rev thy #classrel "class relation");
fun tyco_rev thy =
  dest_nsp nsp_tyco
  #> Option.map (rev thy #tyco "type constructor");
fun instance_rev thy =
  dest_nsp nsp_inst
  #> Option.map (rev thy #instance "instance");
fun const_rev thy =
  dest_nsp nsp_const
  #> Option.map (rev thy #const "constant");

fun labelled_name thy name =
  let
    val (base, nsp) = NameSpace.split name
  in case AList.lookup (op =) nsp_mapping nsp
   of SOME msg => msg ^ " " ^ quote base
    | NONE => error ("illegal shallow name space: " ^ quote nsp)
  end;


(** variable and module names **)

fun purify_var "" = "x"
  | purify_var v = (purify_name #> purify_lower) v;

fun purify_tvar "" = "'a"
  | purify_tvar v =
      (unprefix "'" #> explode #> filter Symbol.is_ascii_letter #> cons "'" #> implode) v;

fun check_modulename mn =
  let
    val mns = NameSpace.explode mn;
    val mns' = map purify_upper mns;
  in
    if mns' = mns then mn else error ("Invalid module name: " ^ quote mn ^ "\n"
      ^ "perhaps try " ^ quote (NameSpace.implode mns'))
  end;


(** variable name contexts **)

type var_ctxt = string Symtab.table * Name.context;

fun make_vars names = (fold (fn name => Symtab.update_new (name, name)) names Symtab.empty,
  Name.make_context names);

fun intro_vars names (namemap, namectxt) =
  let
    val (names', namectxt') = Name.variants names namectxt;
    val namemap' = fold2 (curry Symtab.update) names names' namemap;
  in (namemap', namectxt') end;

fun lookup_var (namemap, _) name = case Symtab.lookup namemap name
 of SOME name' => name'
  | NONE => error ("invalid name in context: " ^ quote name);

end;
