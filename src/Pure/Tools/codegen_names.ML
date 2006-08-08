(*  Title:      Pure/Tools/codegen_names.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Name policies for code generation: dissolving ad-hoc overloaded
constants, prefixing any name by corresponding theory name,
conversion to alphanumeric representation.
Mappings are incrementally cached.
*)

signature CODEGEN_NAMES =
sig
  type tyco = string;
  type const = string;
  val class: theory -> class -> class
  val class_rev: theory -> class -> class
  val tyco: theory -> tyco -> tyco
  val tyco_rev: theory -> tyco -> tyco
  val instance: theory -> class * tyco -> string
  val instance_rev: theory -> string -> class * tyco
  val const: theory -> string * typ -> const
  val const_rev: theory -> const -> string * typ
  val force: (string * typ) * const -> theory -> theory
  val read_const_typ: theory -> string -> string * typ
  val read_const: theory -> string -> const
  val purify_var: string -> string
end;

structure CodegenNames: CODEGEN_NAMES =
struct


(* theory data *)

type tyco = string;
type const = string;
val inst_ord = prod_ord fast_string_ord fast_string_ord;
val eq_inst = is_equal o inst_ord;
val const_ord = prod_ord fast_string_ord (list_ord Term.typ_ord);
val eq_const = is_equal o const_ord;

structure Insttab =
  TableFun(
    type key = class * tyco;
    val ord = inst_ord;
  );

structure Consttab =
  TableFun(
    type key = string * typ list;
    val ord = const_ord;
  );

datatype names = Names of {
  class: class Symtab.table * class Symtab.table,
  tyco: tyco Symtab.table * tyco Symtab.table,
  instance: string Insttab.table * (class * tyco) Symtab.table,
  const: const Consttab.table * (string * typ list) Symtab.table
}

val empty_names = Names {
  class = (Symtab.empty, Symtab.empty),
  tyco = (Symtab.empty, Symtab.empty),
  instance = (Insttab.empty, Symtab.empty),
  const = (Consttab.empty, Symtab.empty)
};

local
  fun mk_names (class, tyco, instance, const) =
    Names { class = class, tyco = tyco, instance = instance, const = const};
  fun map_names f (Names { class, tyco, instance, const }) =
    mk_names (f (class, tyco, instance, const));
  val eq_string = op = : string * string -> bool;
in
  fun merge_names (Names { class = (class1, classrev1), tyco = (tyco1, tycorev1),
      instance = (instance1, instancerev1), const = (const1, constrev1) },
    Names { class = (class2, classrev2), tyco = (tyco2, tycorev2),
      instance = (instance2, instancerev2), const = (const2, constrev2) }) =
    mk_names ((Symtab.merge eq_string (class1, class2), Symtab.merge eq_string (classrev1, classrev2)),
      (Symtab.merge eq_string (tyco1, tyco2), Symtab.merge eq_string (tycorev1, tycorev2)),
      (Insttab.merge eq_string (instance1, instance2), Symtab.merge eq_inst (instancerev1, instancerev2)),
      (Consttab.merge eq_string (const1, const2), Symtab.merge eq_const (constrev1, constrev2)));
  fun map_class f = map_names
    (fn (class, tyco, inst, const) => (f class, tyco, inst, const));
  fun map_tyco f = map_names
    (fn (class, tyco, inst, const) => (class, f tyco, inst, const));
  fun map_inst f = map_names
    (fn (class, tyco, inst, const) => (class, tyco, f inst, const));
  fun map_const f = map_names
    (fn (class, tyco, inst, const) => (class, tyco, inst, f const));

end; (*local*)

structure CodegenNamesData = TheoryDataFun
(struct
  val name = "Pure/codegen_names";
  type T = names ref;
  val empty = ref empty_names;
  fun copy (ref names) = ref names;
  val extend = copy;
  fun merge _ (ref names1, ref names2) = ref (merge_names (names1, names2));
  fun print _ _ = ();
end);

val _ = Context.add_setup CodegenNamesData.init;


(* forward lookup with cache update *)

fun get thy get_tabs get upd_names upd policy x =
  let
    val names_ref = CodegenNamesData.get thy
    val (Names names) = ! names_ref;
    fun mk_unique used name =
      let
        fun mk_name 0 = name
          | mk_name i = name ^ "_" ^ string_of_int i
        fun find_name i =
          let
            val name = mk_name i
          in
            if used name
            then find_name (i+1)
            else name
          end;
        val name = find_name 0;
      in name end;
    val tabs = get_tabs names;
    fun declare name =
      let
        val names' = upd_names (K (upd (x, name) (fst tabs),
          Symtab.update_new (name, x) (snd tabs))) (Names names)
      in (names_ref := names'; name) end;
  in case get (fst tabs) x
   of SOME name => name
    | NONE => let
        val used = Symtab.defined (snd tabs);
        val raw_name = policy thy x;
        val name = mk_unique used raw_name;
      in declare name end
  end;


(* backward lookup *)

fun rev thy get_tabs errname name =
  let
    val names_ref = CodegenNamesData.get thy
    val (Names names) = ! names_ref;
    val tab = (snd o get_tabs) names;
  in case Symtab.lookup tab name
   of SOME x => x
    | NONE => error ("no such " ^ errname ^ ": " ^ quote name)
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
  thyname_of thy (fn thy => member (op =) (Sign.classes thy))
    (fn class => "thyname_of_class: no such class: " ^ quote class);

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


(* dissolving of ad-hoc overloading *)

fun typinst_of_typ thy (c, ty) =
  let
    fun disciplined _ [(Type (tyco, _))] =
          [Type (tyco, map (fn v => TFree (v, Sign.defaultS thy)) (*for monotonicity*)
            (Name.invents Name.context "'a" (Sign.arity_number thy tyco)))]
      | disciplined sort _ =
          [TFree ("'a", sort)];
    fun ad_hoc c tys =
      let
        val def_tyinsts =
          map (#lhs o snd) (Defs.specifications_of (Theory.defs_of thy) c);
        val tyinst = find_first
          (fn tys' => forall (Sign.typ_instance thy) (tys' ~~ tys)) def_tyinsts;
      in case tyinst
       of SOME tys => tys
        | NONE => Consts.typargs (Sign.consts_of thy)
            (c, (Logic.unvarifyT o Sign.the_const_type thy) c)
      end;
    val tyinsts = Consts.typargs (Sign.consts_of thy) (c, ty);
  in if c = "op =" then (c, disciplined (Sign.defaultS thy) tyinsts)
    else case AxClass.class_of_param thy c
     of SOME class => (c, disciplined [class] tyinsts)
      | _ => (c, ad_hoc c tyinsts)
  end;

fun get_overl_def_module thy ("op =", [Type (tyco, _)]) =
      SOME (thyname_of_tyco thy tyco)
  | get_overl_def_module thy (c, tys) =
      get_first (fn (_, { lhs, module, ...}) =>
        if forall (Sign.typ_instance thy) (lhs ~~ tys) then SOME module else NONE)
        (Defs.specifications_of (Theory.defs_of thy) c);

fun typ_of_typinst thy (c, tys) =
  (c, Consts.instance (Sign.consts_of thy) (c, tys));


(* purification of identifiers *)

val purify_name =
  let
    fun is_valid s = Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s orelse s = "'";
    val is_junk = not o is_valid andf Symbol.not_eof;
    val junk = Scan.any is_junk;
    val scan_valids = Symbol.scanner "Malformed input"
      ((junk |--
        (Scan.optional (Scan.one Symbol.is_ascii_letter) "x" ^^ (Scan.any is_valid >> implode)
        --| junk))
      -- Scan.repeat ((Scan.any1 is_valid >> implode) --| junk) >> op ::);
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
          (Scan.repeat (Scan.some rep_op || Scan.one (K true)));
      in (explode #> scan_valids #> implode) s end;

val purify_lower = explode #> nth_map 0 Symbol.to_ascii_lower #> implode;
val purify_upper = explode #> nth_map 0 Symbol.to_ascii_upper #> implode;

fun purify_var v =
  if nth (explode v) 0 = "'"
  then "'" ^ (purify_name #> purify_lower #> unprefix "'") v
  else (purify_name #> purify_lower) v;

val purify_idf = purify_op #> purify_name;
val purify_prefix = map (purify_idf #> purify_upper);
val purify_base = purify_idf #> purify_lower;


(* explicit given constant names with cache update *)

fun force (c_ty, name) thy =
  let
    val names = NameSpace.unpack name;
    val (prefix, base) = split_last (NameSpace.unpack name);
    val prefix' = purify_prefix prefix;
    val base' = purify_base base;
    val _ = if (base' = base) andalso forall (op =) (prefix' ~~ prefix)
      then ()
      else
        error ("name violates naming conventions: " ^ quote name
          ^ "; perhaps try with " ^ quote (NameSpace.pack (prefix' @ [base'])))
    val names_ref = CodegenNamesData.get thy;
    val (Names names) = ! names_ref;
    val (const, constrev) = #const names;
    val c_tys as (c, _) = typinst_of_typ thy c_ty;
    val _ = if Consttab.defined const c_tys
      then error ("constant already named: " ^
        quote (c ^ "::" ^ (Sign.string_of_typ thy o snd o typ_of_typinst thy) c_tys))
      else ();
    val _ = if Symtab.defined constrev name
      then error ("name already given to constant: " ^ quote name)
      else ();
    val _ = names_ref := map_const (K (Consttab.update_new (c_tys, name) const,
          Symtab.update_new (name, c_tys) constrev)) (Names names);
  in
    thy
  end;


(* naming policies *)

fun policy thy get_basename get_thyname name =
  let
    val prefix = (purify_prefix o NameSpace.unpack o get_thyname thy) name;
    val base = (purify_base o get_basename) name;
  in NameSpace.pack (prefix @ [base]) end;

fun class_policy thy = policy thy NameSpace.base thyname_of_class;
fun tyco_policy thy = policy thy NameSpace.base thyname_of_tyco;
fun instance_policy thy = policy thy (fn (class, tyco) => 
  NameSpace.base class ^ "_" ^ NameSpace.base tyco) thyname_of_instance;

fun const_policy thy (c, tys) =
  case get_overl_def_module thy (c, tys)
   of NONE => policy thy NameSpace.base thyname_of_const c
    | SOME thyname => let
        val prefix = (purify_prefix o NameSpace.unpack) thyname;
        val base = (purify_base o NameSpace.base) c;
        val tycos = map_filter (fn Type (tyco, _) => SOME tyco | _ => NONE) tys;
        val base' = space_implode "_" (base :: tycos);
      in NameSpace.pack (prefix @ [base']) end;


(* external interfaces *)

fun class thy =
  get thy #class Symtab.lookup map_class Symtab.update class_policy;
fun tyco thy =
  get thy #tyco Symtab.lookup map_tyco Symtab.update tyco_policy;
fun instance thy =
  get thy #instance Insttab.lookup map_inst Insttab.update instance_policy;
fun const thy =
  get thy #const Consttab.lookup map_const Consttab.update const_policy
    o typinst_of_typ thy;

fun class_rev thy = rev thy #class "class";
fun tyco_rev thy = rev thy #tyco "type constructor";
fun instance_rev thy = rev thy #instance "instance";
fun const_rev thy = rev thy #const "constant" #> typ_of_typinst thy;


(* reading constants as terms *)

fun read_const_typ thy raw_t =
  let
    val t = Sign.read_term thy raw_t
  in case try dest_Const t
   of SOME c_ty => c_ty
    | NONE => error ("not a constant: " ^ Sign.string_of_term thy t)
  end;

fun read_const thy =
  const thy o read_const_typ thy;


(* outer syntax *)

local

structure P = OuterParse
and K = OuterKeyword

fun force_e (raw_c, name) thy =
  force (read_const_typ thy raw_c, name) thy;

val constnameK = "code_constname";

val constnameP =
  OuterSyntax.command constnameK "declare code name for constant" K.thy_decl (
    P.term -- P.name
    >> (fn (raw_c, name) =>
          Toplevel.theory (force_e (raw_c, name)))
  );

in

val _ = OuterSyntax.add_parsers [constnameP];


end; (*local*)

end;
