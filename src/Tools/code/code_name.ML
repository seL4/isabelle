(*  Title:      Tools/code/code_name.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Naming policies for code generation: prefixing any name by corresponding
theory name, conversion to alphanumeric representation.
Mappings are incrementally cached.  Assumes non-concurrent processing
inside a single theory.
*)

signature CODE_NAME =
sig
  val read_const_exprs: theory -> string list -> string list * string list

  val purify_var: string -> string
  val purify_tvar: string -> string
  val purify_sym: string -> string
  val check_modulename: string -> string

  type var_ctxt;
  val make_vars: string list -> var_ctxt;
  val intro_vars: string list -> var_ctxt -> var_ctxt;
  val lookup_var: var_ctxt -> string -> string;

  val class: theory -> class -> class
  val class_rev: theory -> class -> class option
  val classrel: theory -> class * class -> string
  val classrel_rev: theory -> string -> (class * class) option
  val tyco: theory -> string -> string
  val tyco_rev: theory -> string -> string option
  val instance: theory -> class * string -> string
  val instance_rev: theory -> string -> (class * string) option
  val const: theory -> string -> string
  val const_rev: theory -> string -> string option
  val value_name: string
  val labelled_name: theory -> string -> string

  val setup: theory -> theory
end;

structure CodeName: CODE_NAME =
struct

(** constant expressions **)

fun read_const_exprs thy =
  let
    fun consts_of some_thyname =
      let
        val thy' = case some_thyname
         of SOME thyname => ThyInfo.the_theory thyname thy
          | NONE => thy;
        val raw_cs = Symtab.fold (fn (c, (_, NONE)) => cons c | _ => I)
          ((snd o #constants o Consts.dest o #consts o Sign.rep_sg) thy') [];
        val cs = map (CodeUnit.subst_alias thy') raw_cs;
        fun belongs_here c =
          not (exists (fn thy'' => Sign.declared_const thy'' c) (Theory.parents_of thy'))
      in case some_thyname
       of NONE => cs
        | SOME thyname => filter belongs_here cs
      end;
    fun read_const_expr "*" = ([], consts_of NONE)
      | read_const_expr s = if String.isSuffix ".*" s
          then ([], consts_of (SOME (unsuffix ".*" s)))
          else ([CodeUnit.read_const thy s], []);
  in pairself flat o split_list o map read_const_expr end;


(** purification **)

fun purify_name upper lower =
  let
    fun is_valid s = Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s orelse s = "'";
    val is_junk = not o is_valid andf Symbol.is_regular;
    val junk = Scan.many is_junk;
    val scan_valids = Symbol.scanner "Malformed input"
      ((junk |--
        (Scan.optional (Scan.one Symbol.is_ascii_letter) "x" ^^ (Scan.many is_valid >> implode)
        --| junk))
      ::: Scan.repeat ((Scan.many1 is_valid >> implode) --| junk));
    fun upper_lower cs = if upper then nth_map 0 Symbol.to_ascii_upper cs
      else if lower then (if forall Symbol.is_ascii_upper cs
        then map else nth_map 0) Symbol.to_ascii_lower cs
      else cs;
  in
    explode
    #> scan_valids
    #> space_implode "_"
    #> explode
    #> upper_lower
    #> implode
  end;

fun purify_var "" = "x"
  | purify_var v = purify_name false true v;

fun purify_tvar "" = "'a"
  | purify_tvar v =
      (unprefix "'" #> explode #> filter Symbol.is_ascii_letter #> cons "'" #> implode) v;

fun check_modulename mn =
  let
    val mns = NameSpace.explode mn;
    val mns' = map (purify_name true false) mns;
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
  | NONE => error ("Invalid name in context: " ^ quote name);


(** global names (identifiers) **)

(* identifier categories *)

val suffix_class = "class";
val suffix_classrel = "classrel"
val suffix_tyco = "tyco";
val suffix_instance = "inst";
val suffix_const = "const";

fun string_of_classrel (class, superclass) = class ^ " < " ^ superclass;
fun string_of_instance (class, tyco) = tyco ^ " :: " ^ class;

fun add_suffix nsp name =
  NameSpace.append name nsp;

fun dest_suffix nsp name =
  if NameSpace.base name = nsp
  then SOME (NameSpace.qualifier name)
  else NONE;

local

val name_mapping  = [
  (suffix_class,       "class"),
  (suffix_classrel,    "subclass relation"),
  (suffix_tyco,        "type constructor"),
  (suffix_instance,    "instance"),
  (suffix_const,       "constant")
]

in

val category_of = the o AList.lookup (op =) name_mapping o NameSpace.base;

end;


(* theory name lookup *)

fun thyname_of thy f x = the (AList.lookup (op =) (f x) Markup.theory_nameN);

fun thyname_of' thy f errmsg x =
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
  thyname_of' thy (fn thy => member (op =) (Sign.all_classes thy))
    (fn class => "thyname_of_class: no such class: " ^ quote class);

fun thyname_of_tyco thy = thyname_of thy (Type.the_tags (Sign.tsig_of thy));

fun thyname_of_instance thy =
  let
    fun test_instance thy (class, tyco) =
      can (Sorts.mg_domain (Sign.classes_of thy) tyco) [class]
  in thyname_of' thy test_instance
    (fn (class, tyco) => "thyname_of_instance: no such instance: "
      ^ (quote o string_of_instance) (class, tyco))
  end;

fun thyname_of_const thy = thyname_of thy (Consts.the_tags (Sign.consts_of thy));


(* naming policies *)

val purify_prefix =
  explode
  (*should disappear as soon as hierarchical theory name spaces are available*)
  #> Symbol.scanner "Malformed name"
      (Scan.repeat ($$ "_" |-- $$ "_" >> (fn _ => ".") || Scan.one Symbol.is_regular))
  #> implode
  #> NameSpace.explode
  #> map (purify_name true false);

fun purify_base _ "op &" = "and"
  | purify_base _ "op |" = "or"
  | purify_base _ "op -->" = "implies"
  | purify_base _ "{}" = "empty"
  | purify_base _ "op :" = "member"
  | purify_base _ "op Int" = "intersect"
  | purify_base _ "op Un" = "union"
  | purify_base _ "*" = "product"
  | purify_base _ "+" = "sum"
  | purify_base lower s = if String.isPrefix "op =" s
      then "eq" ^ purify_name false lower s
      else purify_name false lower s;

val purify_sym = purify_base false;

fun default_policy thy get_basename get_thyname name =
  let
    val prefix = (purify_prefix o get_thyname thy) name;
    val base = (purify_base true o get_basename) name;
  in NameSpace.implode (prefix @ [base]) end;

fun class_policy thy = default_policy thy NameSpace.base thyname_of_class;
fun classrel_policy thy = default_policy thy (fn (class1, class2) => 
  NameSpace.base class2 ^ "_" ^ NameSpace.base class1) (fn thy => thyname_of_class thy o fst);
  (*order fits nicely with composed projections*)
fun tyco_policy thy = default_policy thy NameSpace.base thyname_of_tyco;
fun instance_policy thy = default_policy thy (fn (class, tyco) => 
  NameSpace.base class ^ "_" ^ NameSpace.base tyco) thyname_of_instance;

fun force_thyname thy c = case Code.get_datatype_of_constr thy c
 of SOME dtco => SOME (thyname_of_tyco thy dtco)
  | NONE => (case AxClass.class_of_param thy c
     of SOME class => SOME (thyname_of_class thy class)
      | NONE => (case AxClass.inst_of_param thy c
         of SOME (c, tyco) => SOME (thyname_of_instance thy
              ((the o AxClass.class_of_param thy) c, tyco))
          | NONE => NONE));

fun const_policy thy c =
  case force_thyname thy c
   of NONE => default_policy thy NameSpace.base thyname_of_const c
    | SOME thyname => let
        val prefix = purify_prefix thyname;
        val base = (purify_base true o NameSpace.base) c;
      in NameSpace.implode (prefix @ [base]) end;


(* theory and code data *)

type tyco = string;
type const = string;

structure StringPairTab =
  TableFun(
    type key = string * string;
    val ord = prod_ord fast_string_ord fast_string_ord;
  );

datatype names = Names of {
  class: class Symtab.table * class Symtab.table,
  classrel: string StringPairTab.table * (class * class) Symtab.table,
  tyco: tyco Symtab.table * tyco Symtab.table,
  instance: string StringPairTab.table * (class * tyco) Symtab.table
}

val empty_names = Names {
  class = (Symtab.empty, Symtab.empty),
  classrel = (StringPairTab.empty, Symtab.empty),
  tyco = (Symtab.empty, Symtab.empty),
  instance = (StringPairTab.empty, Symtab.empty)
};

local
  fun mk_names (class, classrel, tyco, instance) =
    Names { class = class, classrel = classrel, tyco = tyco, instance = instance };
  fun map_names f (Names { class, classrel, tyco, instance }) =
    mk_names (f (class, classrel, tyco, instance));
in
  fun merge_names (Names { class = (class1, classrev1),
      classrel = (classrel1, classrelrev1), tyco = (tyco1, tycorev1),
      instance = (instance1, instancerev1) },
    Names { class = (class2, classrev2),
      classrel = (classrel2, classrelrev2), tyco = (tyco2, tycorev2),
      instance = (instance2, instancerev2) }) =
    mk_names ((Symtab.merge (op =) (class1, class2), Symtab.merge (op =) (classrev1, classrev2)),
      (StringPairTab.merge (op =) (classrel1, classrel2), Symtab.merge (op =) (classrelrev1, classrelrev2)),
      (Symtab.merge (op =) (tyco1, tyco2), Symtab.merge (op =) (tycorev1, tycorev2)),
      (StringPairTab.merge (op =) (instance1, instance2), Symtab.merge (op =) (instancerev1, instancerev2)));
  fun map_class f = map_names
    (fn (class, classrel, tyco, inst) => (f class, classrel, tyco, inst));
  fun map_classrel f = map_names
    (fn (class, classrel, tyco, inst) => (class, f classrel, tyco, inst));
  fun map_tyco f = map_names
    (fn (class, classrel, tyco, inst) => (class, classrel, f tyco, inst));
  fun map_instance f = map_names
    (fn (class, classrel, tyco, inst) => (class, classrel, tyco, f inst));
end; (*local*)

structure CodeName = TheoryDataFun
(
  type T = names ref;
  val empty = ref empty_names;
  fun copy (ref names) = ref names;
  val extend = copy;
  fun merge _ (ref names1, ref names2) = ref (merge_names (names1, names2));
);

structure ConstName = CodeDataFun
(
  type T = const Symtab.table * string Symtab.table;
  val empty = (Symtab.empty, Symtab.empty);
  fun merge _ ((const1, constrev1), (const2, constrev2)) : T =
    (Symtab.merge (op =) (const1, const2),
      Symtab.merge (op =) (constrev1, constrev2));
  fun purge _ NONE _ = empty
    | purge _ (SOME cs) (const, constrev) = (fold Symtab.delete_safe cs const,
        fold Symtab.delete_safe (map_filter (Symtab.lookup const) cs) constrev);
);

val setup = CodeName.init;


(* forward lookup with cache update *)

fun get thy get_tabs get upd_names upd policy x =
  let
    val names_ref = CodeName.get thy;
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

fun get_const thy const =
  let
    val tabs = ConstName.get thy;
    fun declare name =
      let
        val names' = (Symtab.update (const, name) (fst tabs),
          Symtab.update_new (name, const) (snd tabs))
      in (ConstName.change thy (K names'); name) end;
  in case Symtab.lookup (fst tabs) const
   of SOME name => name
    | NONE => 
        const
        |> const_policy thy
        |> Name.variant (Symtab.keys (snd tabs))
        |> declare
  end;


(* backward lookup *)

fun rev thy get_tabs name =
  let
    val names_ref = CodeName.get thy
    val (Names names) = ! names_ref;
    val tab = (snd o get_tabs) names;
  in case Symtab.lookup tab name
   of SOME x => x
    | NONE => error ("No such " ^ category_of name ^ ": " ^ quote name)
  end;

fun rev_const thy name =
  let
    val tab = snd (ConstName.get thy);
  in case Symtab.lookup tab name
   of SOME const => const
    | NONE => error ("No such " ^ category_of name ^ ": " ^ quote name)
  end;


(* external interfaces *)

fun class thy =
  get thy #class Symtab.lookup map_class Symtab.update class_policy
  #> add_suffix suffix_class;
fun classrel thy =
  get thy #classrel StringPairTab.lookup map_classrel StringPairTab.update classrel_policy
  #> add_suffix suffix_classrel;
fun tyco thy =
  get thy #tyco Symtab.lookup map_tyco Symtab.update tyco_policy
  #> add_suffix suffix_tyco;
fun instance thy =
  get thy #instance StringPairTab.lookup map_instance StringPairTab.update instance_policy
  #> add_suffix suffix_instance;
fun const thy =
  get_const thy
  #> add_suffix suffix_const;

fun class_rev thy =
  dest_suffix suffix_class
  #> Option.map (rev thy #class);
fun classrel_rev thy =
  dest_suffix suffix_classrel
  #> Option.map (rev thy #classrel);
fun tyco_rev thy =
  dest_suffix suffix_tyco
  #> Option.map (rev thy #tyco);
fun instance_rev thy =
  dest_suffix suffix_instance
  #> Option.map (rev thy #instance);
fun const_rev thy =
  dest_suffix suffix_const
  #> Option.map (rev_const thy);

local

val f_mapping = [
  (suffix_class,       class_rev),
  (suffix_classrel,    Option.map string_of_classrel oo classrel_rev),
  (suffix_tyco,        tyco_rev),
  (suffix_instance,    Option.map string_of_instance oo instance_rev),
  (suffix_const,       fn thy => Option.map (CodeUnit.string_of_const thy) o const_rev thy)
];

in

val value_name = "Isabelle_Eval.EVAL.EVAL"

fun labelled_name thy suffix_name = if suffix_name = value_name then "<term>" else
  let
    val category = category_of suffix_name;
    val name = NameSpace.qualifier suffix_name;
    val suffix = NameSpace.base suffix_name
  in case (the o AList.lookup (op =) f_mapping) suffix thy suffix_name
   of SOME thing => category ^ " " ^ quote thing
    | NONE => error ("Unknown name: " ^ quote name)
  end;

end;

end;
