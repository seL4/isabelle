(*  Title:      Pure/Tools/codegen_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Code generator from Isabelle theories to
intermediate language ("Thin-gol").
*)

(*NOTE: for simplifying developement, this package contains
some stuff which will finally be moved upwards to HOL*)

signature CODEGEN_PACKAGE =
sig
  type deftab;
  type codegen_type;
  type codegen_expr;
  type defgen;
  val add_codegen_type: string * codegen_type -> theory -> theory;
  val add_codegen_expr: string * codegen_expr -> theory -> theory;
  val add_defgen: string * defgen -> theory -> theory;
  val add_lookup_tyco: string * string -> theory -> theory;
  val add_lookup_const: (string * typ) * CodegenThingol.iexpr -> theory -> theory;
  val add_syntax_tyco: string -> (xstring * string)
    * (string option * (string * string list)) option
    -> theory -> theory;
  val add_syntax_tyco_i: string -> (string * CodegenThingol.itype Codegen.mixfix list)
    * (string * (string * string list)) option
    -> theory -> theory;
  val add_syntax_const: string -> ((xstring * string option) * string)
    * (string option * (string * string list)) option
    -> theory -> theory;
  val add_syntax_const_i: string -> (string * CodegenThingol.iexpr Codegen.mixfix list)
    * (string * (string * string list)) option
    -> theory -> theory;
  val add_alias: string * string -> theory -> theory;
  val set_is_datatype: (theory -> string -> bool) -> theory -> theory;

  val idf_of_name: theory -> string -> string -> string;
  val name_of_idf: theory -> string -> string -> string option;
  val idf_of_inst: theory -> deftab -> class * string -> string;
  val inst_of_idf: theory -> deftab -> string -> (class * string) option;
  val idf_of_tname: theory -> string -> string;
  val tname_of_idf: theory -> string -> string option;
  val idf_of_cname: theory -> deftab -> string * typ -> string;
  val cname_of_idf: theory -> deftab -> string -> (string * typ) option;

  val invoke_cg_type: theory -> deftab
    -> typ -> CodegenThingol.transact -> CodegenThingol.itype * CodegenThingol.transact;
  val invoke_cg_expr: theory -> deftab
    -> term -> CodegenThingol.transact -> CodegenThingol.iexpr * CodegenThingol.transact;
  val ensure_def_tyco: theory -> deftab
    -> string -> CodegenThingol.transact -> string * CodegenThingol.transact;
  val ensure_def_const: theory -> deftab
    -> string -> CodegenThingol.transact -> string * CodegenThingol.transact;

  val codegen_let: (int -> term -> term list * term)
    -> codegen_expr;
  val codegen_split: (int -> term -> term list * term)
    -> codegen_expr;
  val codegen_number_of: (term -> IntInf.int) -> (term -> term)
    -> codegen_expr;
  val codegen_case: (theory -> string -> (string * int) list option)
    -> codegen_expr;
  val defgen_datatype: (theory -> string -> (string list * string list) option)
    -> defgen;
  val defgen_datacons: (theory -> string * string -> typ list option)
    -> defgen;
  val defgen_recfun: (theory -> string * typ -> (term list * term) list * typ)
    -> defgen;

  val print_codegen_generated: theory -> unit;
  val mk_deftab: theory -> deftab;
  structure CodegenData: THEORY_DATA;
  structure Insttab: TABLE;
end;

structure CodegenPackage : CODEGEN_PACKAGE =
struct

open CodegenThingol;

(* auxiliary *)

fun perhaps f x = f x |> the_default x;


(* code generator instantiation, part 1 *)

structure Insttab = TableFun(
  type key = string * string
  val ord = prod_ord fast_string_ord fast_string_ord
);

type deftab = ((typ * string) list Symtab.table
    * (string * typ) Symtab.table)
  * (term list * term * typ) Symtab.table
    * (string Insttab.table
      * (string * string) Symtab.table
      * class Symtab.table);

type codegen_sort = theory -> deftab -> (sort, sort) gen_codegen;
type codegen_type = theory -> deftab -> (typ, itype) gen_codegen;
type codegen_expr = theory -> deftab -> (term, iexpr) gen_codegen;
type defgen = theory -> deftab -> gen_defgen;


(* namespace conventions *)

val nsp_class = "class";
val nsp_type = "type";
val nsp_const = "const";
val nsp_mem = "mem";
val nsp_inst = "inst";
val nsp_eq_class = "eq_class";
val nsp_eq = "eq";


(* serializer *)

val serializer_ml =
  let
    val name_root = "Generated";
    val nsp_conn = [
      [nsp_class, nsp_type, nsp_eq_class], [nsp_const, nsp_inst, nsp_mem, nsp_eq]
    ];
  in CodegenSerializer.ml_from_thingol nsp_conn name_root end;

val serializer_hs =
  let
    val name_root = "Generated";
    val nsp_conn = [
      [nsp_class, nsp_eq_class], [nsp_type], [nsp_const], [nsp_inst], [nsp_mem], [nsp_eq]
    ];
  in CodegenSerializer.haskell_from_thingol nsp_conn name_root end;


(* theory data for codegen *)

type gens = {
  codegens_sort: (string * (codegen_sort * stamp)) list,
  codegens_type: (string * (codegen_type * stamp)) list,
  codegens_expr: (string * (codegen_expr * stamp)) list,
  defgens: (string * (defgen * stamp)) list
};

val empty_gens = {
  codegens_sort = Symtab.empty, codegens_type = Symtab.empty,
  codegens_expr = Symtab.empty, defgens = Symtab.empty
};

fun map_gens f { codegens_sort, codegens_type, codegens_expr, defgens } =
  let
    val (codegens_sort, codegens_type, codegens_expr, defgens) =
      f (codegens_sort, codegens_type, codegens_expr, defgens)
  in { codegens_sort = codegens_sort, codegens_type = codegens_type,
       codegens_expr = codegens_expr, defgens = defgens } end;

fun merge_gens
  ({ codegens_sort = codegens_sort1, codegens_type = codegens_type1,
     codegens_expr = codegens_expr1, defgens = defgens1 },
   { codegens_sort = codegens_sort2, codegens_type = codegens_type2,
     codegens_expr = codegens_expr2, defgens = defgens2 }) =
  { codegens_sort = AList.merge (op =) (eq_snd (op =)) (codegens_sort1, codegens_sort2),
    codegens_type = AList.merge (op =) (eq_snd (op =)) (codegens_type1, codegens_type2),
    codegens_expr = AList.merge (op =) (eq_snd (op =)) (codegens_expr1, codegens_expr2),
    defgens = AList.merge (op =) (eq_snd (op =)) (defgens1, defgens2) };

type lookups = {
  lookups_tyco: string Symtab.table,
  lookups_const: (typ * iexpr) list Symtab.table
}

val empty_lookups = {
  lookups_tyco = Symtab.empty, lookups_const = Symtab.empty
};

fun map_lookups f { lookups_tyco, lookups_const } =
  let
    val (lookups_tyco, lookups_const) =
      f (lookups_tyco, lookups_const)
  in { lookups_tyco = lookups_tyco, lookups_const = lookups_const } end;

fun merge_lookups
  ({ lookups_tyco = lookups_tyco1, lookups_const = lookups_const1 },
   { lookups_tyco = lookups_tyco2, lookups_const = lookups_const2 }) =
  { lookups_tyco = Symtab.merge (op =) (lookups_tyco1, lookups_tyco2),
    lookups_const = Symtab.merge (op =) (lookups_const1, lookups_const2) };

type logic_data = {
  is_datatype: ((theory -> string -> bool) * stamp) option,
  alias: string Symtab.table * string Symtab.table
};

fun map_logic_data f { is_datatype, alias } =
  let
    val (is_datatype, alias) =
      f (is_datatype, alias)
  in { is_datatype = is_datatype, alias = alias } end;

fun merge_logic_data
  ({ is_datatype = is_datatype1, alias = alias1 },
   { is_datatype = is_datatype2, alias = alias2 }) =
  let
    fun merge_opt _ (x1, NONE) = x1
      | merge_opt _ (NONE, x2) = x2
      | merge_opt eq (SOME x1, SOME x2) =
          if eq (x1, x2) then SOME x1 else error ("incompatible options during merge");
  in
    { is_datatype = merge_opt (eq_snd (op =)) (is_datatype1, is_datatype2),
      alias = (Symtab.merge (op =) (fst alias1, fst alias2),
               Symtab.merge (op =) (snd alias1, snd alias2)) }
  end;

type serialize_data = {
  serializer: CodegenSerializer.serializer,
  primitives: CodegenSerializer.primitives,
  syntax_tyco: itype Codegen.mixfix list Symtab.table,
  syntax_const: iexpr Codegen.mixfix list Symtab.table
};

fun map_serialize_data f { serializer, primitives, syntax_tyco, syntax_const } =
  let
    val (primitives, syntax_tyco, syntax_const) =
      f (primitives, syntax_tyco, syntax_const)
  in { serializer = serializer, primitives = primitives,
       syntax_tyco = syntax_tyco, syntax_const = syntax_const } end;

fun merge_serialize_data
  ({ serializer = serializer, primitives = primitives1,
     syntax_tyco = syntax_tyco1, syntax_const = syntax_const1 },
   {serializer = _, primitives = primitives2,
     syntax_tyco = syntax_tyco2, syntax_const = syntax_const2 }) =
  { serializer = serializer,
    primitives = CodegenSerializer.merge_prims (primitives1, primitives2) : CodegenSerializer.primitives,
    syntax_tyco = Symtab.merge (op =) (syntax_tyco1, syntax_tyco2),
    syntax_const = Symtab.merge (op =) (syntax_const1, syntax_const2) };

structure CodegenData = TheoryDataFun
(struct
  val name = "Pure/codegen_package";
  type T = {
    modl: module,
    gens: gens,
    lookups: lookups,
    logic_data: logic_data,
    serialize_data: serialize_data Symtab.table
  };
  val empty = {
    modl = empty_module,
    gens = { codegens_sort = [], codegens_type = [], codegens_expr = [], defgens = [] } : gens,
    lookups = { lookups_tyco = Symtab.empty, lookups_const = Symtab.empty } : lookups,
    logic_data = { is_datatype = NONE, alias = (Symtab.empty, Symtab.empty) } : logic_data,
    serialize_data =
      Symtab.empty
      |> Symtab.update ("ml",
          { serializer = serializer_ml : CodegenSerializer.serializer,
            primitives =
              CodegenSerializer.empty_prims
              |> CodegenSerializer.add_prim ("fst", ("fun fst (x, _) = x;", []))
              |> CodegenSerializer.add_prim ("snd", ("fun snd (_, y) = y;", []))
              |> CodegenSerializer.add_prim ("wfrec", ("fun wfrec f x = f (wfrec f) x;", [])),
            syntax_tyco = Symtab.empty, syntax_const = Symtab.empty })
      |> Symtab.update ("haskell",
          { serializer = serializer_hs : CodegenSerializer.serializer, primitives = CodegenSerializer.empty_prims,
            syntax_tyco = Symtab.empty, syntax_const = Symtab.empty })
  } : T;
  val copy = I;
  val extend = I;
  fun merge _ (
    { modl = modl1, gens = gens1, lookups = lookups1,
      serialize_data = serialize_data1, logic_data = logic_data1 },
    { modl = modl2, gens = gens2, lookups = lookups2,
      serialize_data = serialize_data2, logic_data = logic_data2 }
  ) = {
    modl = merge_module (modl1, modl2),
    gens = merge_gens (gens1, gens2),
    lookups = merge_lookups (lookups1, lookups2),
    logic_data = merge_logic_data (logic_data1, logic_data2),
    serialize_data = Symtab.join (K (merge_serialize_data #> SOME))
      (serialize_data1, serialize_data2)
  };
  fun print thy _ = writeln "sorry, this stuff is too complicated...";
end);

fun map_codegen_data f thy =
  case CodegenData.get thy
   of { modl, gens, lookups, serialize_data, logic_data } =>
      let val (modl, gens, lookups, serialize_data, logic_data) =
        f (modl, gens, lookups, serialize_data, logic_data)
      in CodegenData.put { modl = modl, gens = gens, lookups = lookups,
           serialize_data = serialize_data, logic_data = logic_data } thy end;

val print_codegen_generated = writeln o Pretty.output o pretty_module o #modl o CodegenData.get;

fun add_codegen_sort (name, cg) =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (codegens_sort, codegens_type, codegens_expr, defgens) =>
            (codegens_sort
             |> Output.update_warn (op =) ("overwriting existing class code generator " ^ name) (name, (cg, stamp ())),
             codegens_type, codegens_expr, defgens)), lookups, serialize_data, logic_data));

fun add_codegen_type (name, cg) =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (codegens_sort, codegens_type, codegens_expr, defgens) =>
            (codegens_sort,
             codegens_type
             |> Output.update_warn (op =) ("overwriting existing type code generator " ^ name) (name, (cg, stamp ())),
             codegens_expr, defgens)), lookups, serialize_data, logic_data));

fun add_codegen_expr (name, cg) =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (codegens_sort, codegens_type, codegens_expr, defgens) =>
            (codegens_sort, codegens_type,
        codegens_expr
             |> Output.update_warn (op =) ("overwriting existing expression code generator " ^ name) (name, (cg, stamp ())),
             defgens)),
             lookups, serialize_data, logic_data));

fun add_defgen (name, dg) =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (codegens_sort, codegens_type, codegens_expr, defgens) =>
            (codegens_sort, codegens_type, codegens_expr,
             defgens
             |> Output.update_warn (op =) ("overwriting existing definition code generator " ^ name) (name, (dg, stamp ())))),
             lookups, serialize_data, logic_data));

val get_lookups_tyco = #lookups_tyco o #lookups o CodegenData.get;

fun add_lookup_tyco (src, dst) =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl, gens,
        lookups |> map_lookups
          (fn (lookups_tyco, lookups_const) =>
            (lookups_tyco |> Symtab.update_new (src, dst),
             lookups_const)),
        serialize_data, logic_data));

fun add_lookup_const ((src, ty), dst) =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl, gens,
        lookups |> map_lookups
          (fn (lookups_tyco, lookups_const) =>
            (lookups_tyco,
             lookups_const |> Symtab.update_multi (src, (ty, dst)))),
        serialize_data, logic_data));

fun set_is_datatype f =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl, gens, lookups, serialize_data,
        logic_data
        |> map_logic_data (apfst (K (SOME (f, stamp ()))))));

fun add_alias (src, dst) =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl, gens, lookups, serialize_data,
        logic_data |> map_logic_data
          (apsnd (fn (tab, tab_rev) =>
            (tab |> Symtab.update (src, dst),
             tab_rev |> Symtab.update (dst, src))))));


(* code generator name mangling *)

val is_number = is_some o Int.fromString;

val dtype_mangle = "dtype";
fun is_datatype thy =
  case (#is_datatype o #logic_data o CodegenData.get) thy
   of NONE => K false
    | SOME (f, _) => f thy;

fun idf_of_name thy shallow name =
  if is_number name
  then name
  else
    name
    |> NameSpace.unpack
    |> split_last
    |> apsnd ((perhaps o Symtab.lookup) ((fst o #alias o #logic_data o CodegenData.get) thy) #> single #> cons shallow)
    |> (op @)
    |> NameSpace.pack;

fun name_of_idf thy nsp idf =
  let
    val idf' = NameSpace.unpack idf;
    val (idf'', idf_base) = split_last idf';
    val (modl, shallow) = split_last idf'';
  in
    if nsp = shallow
    then SOME (NameSpace.pack (modl @ [
      (perhaps o Symtab.lookup) ((snd o #alias o #logic_data o CodegenData.get) thy) idf_base]))
    else NONE
  end;

fun idf_of_inst thy (_, _, (clstab, _, _)) (cls, tyco) =
  (the o Insttab.lookup clstab) (cls, tyco);

fun inst_of_idf thy (_, _, (_, clstab_rev, _)) idf =
  Symtab.lookup clstab_rev idf;

fun idf_of_tname thy tyco =
  if not (Symtab.defined (get_lookups_tyco thy) tyco)
    andalso tyco <> "nat" andalso is_datatype thy tyco
  then
    tyco
    |> (fn tyco => NameSpace.append tyco nsp_type)
    |> (fn tyco => NameSpace.append tyco dtype_mangle)
  else
    tyco
    |> idf_of_name thy nsp_type;

fun tname_of_idf thy idf =
  if NameSpace.base idf = dtype_mangle
    andalso (NameSpace.base o NameSpace.drop_base) idf = nsp_type
  then
    if is_datatype thy ((NameSpace.drop_base o NameSpace.drop_base) idf)
    then (NameSpace.drop_base o NameSpace.drop_base) idf |> SOME
    else name_of_idf thy nsp_type idf
  else name_of_idf thy nsp_type idf;

fun idf_of_cname thy ((overl, _), _, _) (name, ty) =
  case Symtab.lookup overl name
   of NONE => idf_of_name thy nsp_const name
    | SOME tab => (the o AList.lookup (Sign.typ_instance thy) tab) ty

fun cname_of_idf thy ((_, overl_rev), _, _) idf =
  case Symtab.lookup overl_rev idf
   of NONE =>
        (case name_of_idf thy nsp_const idf
    of NONE => (case name_of_idf thy nsp_mem idf
         of NONE => NONE
          | SOME n => SOME (n, Sign.the_const_constraint thy n))
          | SOME n => SOME (n, Sign.the_const_constraint thy n))
    | s => s;


(* auxiliary *)

fun find_lookup_expr thy (f, ty) =
  Symtab.lookup_multi ((#lookups_const o #lookups o CodegenData.get) thy) f
  |> (fn tab => AList.lookup (Sign.typ_instance thy) tab ty)

fun name_of_tvar (TFree (v, _)) = v |> unprefix "'"
  | name_of_tvar (TVar ((v, i), _)) =
      (if i=0 then v else v ^ string_of_int i) |> unprefix "'"


(* code generator instantiation, part 2 *)

fun invoke_cg_sort thy defs sort trns =
  gen_invoke
    ((map (apsnd (fn (cg, _) => cg thy defs)) o #codegens_sort o #gens o CodegenData.get) thy)
    ("generating sort " ^ (quote o Sign.string_of_sort thy) sort) sort trns;

fun invoke_cg_type thy defs ty trns =
  gen_invoke
    ((map (apsnd (fn (cg, _) => cg thy defs)) o #codegens_type o #gens o CodegenData.get) thy)
    ("generating type " ^ (quote o Sign.string_of_typ thy) ty) ty trns;

fun invoke_cg_expr thy defs t trns =
  gen_invoke
    ((map (apsnd (fn (cg, _) => cg thy defs)) o #codegens_expr o #gens o CodegenData.get) thy)
    ("generating expression " ^ (quote o Sign.string_of_term thy) t) t trns;

fun get_defgens thy defs =
  (map (apsnd (fn (dg, _) => dg thy defs)) o #defgens o #gens o CodegenData.get) thy;

fun ensure_def_class thy defs cls_or_inst trns =
  trns
  |> debug 4 (fn _ => "generating class or instance " ^ quote cls_or_inst)
  |> gen_ensure_def (get_defgens thy defs) ("generating class/instance " ^ quote cls_or_inst) cls_or_inst
  |> pair cls_or_inst;

fun ensure_def_tyco thy defs tyco trns =
  if NameSpace.is_qualified tyco
  then case Option.mapPartial (Symtab.lookup (get_lookups_tyco thy)) (tname_of_idf thy tyco)
   of NONE =>
        trns
        |> debug 4 (fn _ => "generating type constructor " ^ quote tyco)
        |> gen_ensure_def (get_defgens thy defs) ("generating type constructor " ^ quote tyco) tyco
        |> pair tyco
    | SOME tyco =>
        trns
        |> pair tyco
  else (tyco, trns);

fun ensure_def_const thy defs f trns =
  if NameSpace.is_qualified f
  then case Option.mapPartial (find_lookup_expr thy) (cname_of_idf thy defs f)
   of NONE =>
        trns
        |> debug 4 (fn _ => "generating constant " ^ quote f)
        |> invoke_cg_type thy defs (cname_of_idf thy defs f |> the |> snd)
        ||> gen_ensure_def (get_defgens thy defs) ("generating constant " ^ quote f) f
        |-> (fn ty' => pair f)
    | SOME (IConst (f, ty)) =>
        trns
        |> pair f
  else (f, trns);

fun mk_fun thy defs eqs ty trns =
  let
    val sortctxt = ClassPackage.extract_sortctxt thy ty;
    fun mk_sortvar (v, sort) trns =
      trns
      |> invoke_cg_sort thy defs sort
      |-> (fn sort => pair (unprefix "'" v, sort))
    fun mk_eq (args, rhs) trns =
      trns
      |> fold_map (invoke_cg_expr thy defs) args
      ||>> invoke_cg_expr thy defs rhs
      |-> (fn (args, rhs) => pair (map ipat_of_iexpr args, rhs))
  in
    trns
    |> fold_map mk_eq eqs
    ||>> invoke_cg_type thy defs ty
    ||>> fold_map mk_sortvar sortctxt
    |-> (fn ((eqs, ty), sortctxt) => pair (Fun (eqs, (sortctxt, ty))))
  end;

fun fix_nargs thy defs gen i (t, ts) trns =
  if length ts < i
  then
    trns
    |> debug 10 (fn _ => "eta-expanding")
    |> gen (strip_comb (Codegen.eta_expand t ts i))
  else
    trns
    |> debug 10 (fn _ => "splitting arguments (" ^ string_of_int i ^ ", " ^ string_of_int (length ts) ^ ")")
    |> gen (t, Library.take (i, ts))
    ||>> fold_map (invoke_cg_expr thy defs) (Library.drop (i, ts))
    |-> pair o mk_apps;

local
  open CodegenThingolOp;
  infix 8 `%%;
  infixr 6 `->;
  infixr 6 `-->;
  infix 4 `$;
  infix 4 `$$;
  infixr 5 `|->;
  infixr 5 `|-->;
in

(* code generators *)

fun codegen_sort_default thy defs sort trns =
  trns
  |> fold_map (ensure_def_class thy defs)
       (sort |> filter (ClassPackage.is_class thy) |> map (idf_of_name thy nsp_class))
  |-> (fn sort => succeed sort)

fun codegen_type_default thy defs(v as TVar (_, sort)) trns =
      trns
      |> invoke_cg_sort thy defs sort
      |-> (fn sort => succeed (IVarT (name_of_tvar v, sort)))
  | codegen_type_default thy defs (v as TFree (_, sort)) trns =
      trns
      |> invoke_cg_sort thy defs sort
      |-> (fn sort => succeed (IVarT (name_of_tvar v, sort)))
  | codegen_type_default thy defs (Type ("fun", [t1, t2])) trns =
      trns
      |> invoke_cg_type thy defs t1
      ||>> invoke_cg_type thy defs t2
      |-> (fn (t1', t2') => succeed (t1' `-> t2'))
  | codegen_type_default thy defs (Type (tyco, tys)) trns =
      trns
      |> ensure_def_tyco thy defs (idf_of_tname thy tyco)
      ||>> fold_map (invoke_cg_type thy defs) tys
      |-> (fn (tyco, tys) => succeed (tyco `%% tys))

fun codegen_expr_default thy defs (Const (f, ty)) trns =
      let
        val _ = debug 5 (fn _ => "making application of " ^ quote f) ();
        val ty_def = Sign.the_const_constraint thy f;
        val _ = debug 10 (fn _ => "making application (2)") ();
        fun mk_lookup (ClassPackage.Instance (i, ls)) trns =
              trns
              |> ensure_def_class thy defs ((idf_of_name thy nsp_class o fst) i)
              ||>> ensure_def_class thy defs (idf_of_inst thy defs i)
              ||>> (fold_map o fold_map) mk_lookup ls
              |-> (fn ((cls, i), ls) => pair (ClassPackage.Instance ((cls, i), ls)))
          | mk_lookup (ClassPackage.Lookup (clss, (v, i))) trns =
              trns
              |> fold_map (ensure_def_class thy defs) (map (idf_of_name thy nsp_class) clss)
              |-> (fn clss => pair (ClassPackage.Lookup (clss, (name_of_tvar (TFree (v, [])), i))));
        val _ = debug 10 (fn _ => "making application (3)") ();
        fun mk_itapp e [] = e
          | mk_itapp e lookup = IInst (e, lookup);
      in
        trns
        |> debug 10 (fn _ => "making application (4): " ^ f ^ "::" ^ Sign.string_of_typ thy ty ^ " <~> " ^ Sign.string_of_typ thy ty_def)
        |> ensure_def_const thy defs (idf_of_cname thy defs (f, ty))
        |> debug 10 (fn _ => "making application (5)")
        ||>> (fold_map o fold_map) mk_lookup (ClassPackage.extract_sortlookup thy (ty_def, ty))
        |> debug 10 (fn _ => "making application (6)")
        ||>> invoke_cg_type thy defs ty
        |> debug 10 (fn _ => "making application (7)")
        |-> (fn ((f, lookup), ty) =>
               succeed (mk_itapp (IConst (f, ty)) lookup))
      end
  | codegen_expr_default thy defs (Free (v, ty)) trns =
      trns
      |> invoke_cg_type thy defs ty
      |-> (fn ty => succeed (IVarE (v, ty)))
  | codegen_expr_default thy defs (Var ((v, i), ty)) trns =
      trns
      |> invoke_cg_type thy defs ty
      |-> (fn ty => succeed (IVarE (if i=0 then v else v ^ string_of_int i, ty)))
  | codegen_expr_default thy defs (Abs (v, ty, t)) trns =
      trns
      |> invoke_cg_type thy defs ty
      ||>> invoke_cg_expr thy defs (subst_bound (Free (v, ty), t))
      |-> (fn (ty, e) => succeed ((v, ty) `|-> e))
  | codegen_expr_default thy defs (t1 $ t2) trns =
      trns
      |> invoke_cg_expr thy defs t1
      ||>> invoke_cg_expr thy defs t2
      |-> (fn (e1, e2) => succeed (e1 `$ e2));

(*fun codegen_eq thy defs t trns =
 let
   fun cg_eq (Const ("op =", _), [t, u]) =
         trns
         |> invoke_cg_type thy defs (type_of t)
         |-> (fn ty => invoke_ensure_eqinst nsp_eq_class nsp_eq ty #> pair ty)
         ||>> invoke_cg_expr thy defs t
         ||>> invoke_cg_expr thy defs u
         |-> (fn ((ty, t'), u') => succeed (
               IConst (fun_eq, ty `-> ty `-> Type_bool)
                 `$ t' `$ u'))
     | cg_eq _ =
         trns
         |> fail ("no equality: " ^ Sign.string_of_term thy t)
  in cg_eq (strip_comb t) end;*)

fun codegen_neg thy defs t trns =
  let
    val (u, ts) = strip_comb t;
    fun cg_neg (Const ("neg", _)) =
         trns
         |> invoke_cg_expr thy defs (hd ts)
         |-> (fn e => succeed (Fun_lt `$ e `$ IConst ("0", Type_integer)))
      | cg_neg _ =
         trns
         |> fail ("no negation: " ^ Sign.string_of_term thy t)
  in cg_neg u end;


(* definition generators *)

fun defgen_tyco_fallback thy defs tyco trns =
  if Symtab.fold (fn (_, { syntax_tyco, ... }) => fn b => b orelse Symtab.defined syntax_tyco tyco)
    ((#serialize_data o CodegenData.get) thy) false
  then
    trns
    |> debug 5 (fn _ => "trying defgen tyco fallback for " ^ quote tyco)
    |> succeed (Nop, [])
  else
    trns
    |> fail ("no code generation fallback for " ^ quote tyco)

fun defgen_const_fallback thy defs f trns =
  if Symtab.fold (fn (_, { syntax_const, ... }) => fn b => b orelse Symtab.defined syntax_const f)
    ((#serialize_data o CodegenData.get) thy) false
  then
    trns
    |> debug 5 (fn _ => "trying defgen const fallback for " ^ quote f)
    |> succeed (Nop, [])
  else
    trns
    |> fail ("no code generation fallback for " ^ quote f)

fun defgen_defs thy (defs as (_, defs', _)) f trns =
  case Symtab.lookup defs' f
   of SOME (args, rhs, ty) =>
        trns
        |> debug 5 (fn _ => "trying defgen def for " ^ quote f)
        |> mk_fun thy defs [(args, rhs)] ty
        |-> (fn def => succeed (def, []))
      | _ => trns |> fail ("no definition found for " ^ quote f);

fun defgen_clsdecl thy defs cls trns =
  case name_of_idf thy nsp_class cls
   of SOME cls =>
        trns
        |> debug 5 (fn _ => "trying defgen class declaration for " ^ quote cls)
        |> fold_map (ensure_def_class thy defs)
             (map (idf_of_name thy nsp_class) (ClassPackage.get_superclasses thy cls))
        |-> (fn supcls => succeed (Class (supcls, [], []),
             map (idf_of_name thy nsp_mem) (ClassPackage.the_consts thy cls)
             @ map (curry (idf_of_inst thy defs) cls) ((map fst o ClassPackage.the_tycos thy) cls)))
    | _ =>
        trns
        |> fail ("no class definition found for " ^ quote cls);

fun defgen_clsmem thy (defs as (_, _, _)) f trns =
  case name_of_idf thy nsp_mem f
   of SOME clsmem =>
        let
          val _ = debug 10 (fn _ => "CLSMEM " ^ quote clsmem) ();
          val _ = debug 10 (fn _ => (the o ClassPackage.lookup_const_class thy) clsmem) ();
          val cls = idf_of_name thy nsp_class ((the o ClassPackage.lookup_const_class thy) clsmem);
          val (tvar, ty) = ClassPackage.get_const_sign thy clsmem;
        in
          trns
          |> debug 5 (fn _ => "trying defgen class member for " ^ quote f)
          |> invoke_cg_type thy defs ty
          |-> (fn ty => succeed (Classmember (cls, name_of_tvar (TFree (tvar, [])), ty), []))
        end
    | _ =>
        trns |> fail ("no class member found for " ^ quote f)

fun defgen_clsinst thy defs clsinst trns =
  case inst_of_idf thy defs clsinst
   of SOME (cls, tyco) =>
        let
          val arity = (map o map) (idf_of_name thy nsp_class)
            (ClassPackage.get_arities thy [cls] tyco);
          val clsmems = map (idf_of_name thy nsp_mem)
            (ClassPackage.the_consts thy cls);
          val instmem_idfs = map (idf_of_cname thy defs)
            (ClassPackage.get_inst_consts_sign thy (tyco, cls));
          fun add_vars arity clsmems (trns as (_, univ)) =
            ((invent_var_t_names
              (map ((fn Classmember (_, _, ty) => ty) o get_def univ)
              clsmems) (length arity) [] "a" ~~ arity, clsmems), trns)
        in
          trns
          |> debug 5 (fn _ => "trying defgen class instance for (" ^ quote cls ^ ", " ^ quote tyco ^ ")")
          |> (fold_map o fold_map) (ensure_def_class thy defs) arity
          ||>> fold_map (ensure_def_const thy defs) clsmems
          |-> (fn (arity, clsmems) => add_vars arity clsmems)
          ||>> ensure_def_class thy defs (idf_of_name thy nsp_class cls)
          ||>> ensure_def_tyco thy defs (idf_of_tname thy tyco)
          ||>> fold_map (ensure_def_const thy defs) instmem_idfs
          |-> (fn ((((arity, clsmems), cls), tyco), instmem_idfs) =>
                 succeed (Classinst (cls, (tyco, arity), clsmems ~~ instmem_idfs), []))
        end
    | _ =>
        trns |> fail ("no class instance found for " ^ quote clsinst);


(* parametrized generators, for instantiation in HOL *)

fun codegen_let strip_abs thy defs t trns =
  let
    fun dest_let (l as Const ("Let", _) $ t $ u) =
          (case strip_abs 1 u
           of ([p], u') => apfst (cons (p, t)) (dest_let u')
            | _ => ([], l))
      | dest_let t = ([], t);
    fun mk_let (l, r) trns =
      trns
      |> invoke_cg_expr thy defs l
      ||>> invoke_cg_expr thy defs r
      |-> (fn (l, r) => pair (r, ipat_of_iexpr l));
    fun cg_let' ([], _) _ =
          trns
          |> fail ("no let expression: " ^ Sign.string_of_term thy t)
      | cg_let' (lets, body) args =
          trns
          |> fold_map mk_let lets
          ||>> invoke_cg_expr thy defs body
          ||>> fold_map (invoke_cg_expr thy defs) args
          |-> (fn ((lets, body), args) =>
               succeed (Library.foldr (fn ((e, p), body) => ICase (e, [(p, body)])) (lets, body) `$$ args))
    fun cg_let (t1 as Const ("Let", _), t2 :: t3 :: ts) =
          cg_let' (dest_let (t1 $ t2 $ t3)) ts
      | cg_let _ =
          trns
          |> fail ("no let expression: " ^ Sign.string_of_term thy t);
  in cg_let (strip_comb t) end;

fun codegen_split strip_abs thy defs t trns =
  let
    fun cg_split' ([p], body) args =
          trns
          |> invoke_cg_expr thy defs p
          ||>> invoke_cg_expr thy defs body
          ||>> fold_map (invoke_cg_expr thy defs) args
          |-> (fn (((IVarE v), body), args) => succeed (IAbs (v, body) `$$ args))
      | cg_split' _ _ =
          trns
          |> fail ("no split expression: " ^ Sign.string_of_term thy t);
    fun cg_split (t1 as Const ("split", _), t2 :: ts) =
          cg_split' (strip_abs 1 (t1 $ t2)) ts
      | cg_split _ =
          trns
          |> fail ("no split expression: " ^ Sign.string_of_term thy t);
  in cg_split (strip_comb t) end;

fun codegen_number_of dest_binum mk_int_to_nat thy defs (Const ("Numeral.number_of",
      Type ("fun", [_, Type ("IntDef.int", [])])) $ bin) trns =
      trns
      |> (succeed (IConst ((IntInf.toString o dest_binum) bin, Type_integer))
          handle TERM _
          => fail ("not a number: " ^ Sign.string_of_term thy bin))
  | codegen_number_of dest_binum mk_int_to_nat thy defs (Const ("Numeral.number_of",
      Type ("fun", [_, Type ("nat", [])])) $ bin) trns =
      trns
      |> invoke_cg_expr thy defs (mk_int_to_nat bin)
      |-> (fn expr => succeed expr)
  | codegen_number_of dest_binum mk_int_to_nat thy defs t trns =
      trns
      |> fail ("not a number: " ^ Sign.string_of_term thy t);

fun codegen_case get_case_const_data thy defs t trns =
  let
    fun cg_case_d gen_names dty (((cname, i), ty), t) trns =
      let
        val vs = gen_names i;
        val tys = Library.take (i, (fst o strip_type) ty);
        val frees = map2 Free (vs, tys);
        val t' = Envir.beta_norm (list_comb (t, frees));
      in
        trns
        |> invoke_cg_expr thy defs (list_comb (Const (cname, tys ---> dty), frees))
        ||>> invoke_cg_expr thy defs t'
        |-> (fn (ep, e) => pair (ipat_of_iexpr ep, e))
      end;
    fun cg_case dty cs (_, ts) trns =
      let
        val (ts', t) = split_last ts
        val _ = debug 10 (fn _ => "  in " ^ Sign.string_of_typ thy dty ^ ", pairing "
          ^ (commas o map (fst o fst)) cs ^ " with " ^ (commas o map (Sign.string_of_term thy)) ts') ();
        fun gen_names i =
          variantlist (replicate i "x", foldr add_term_names
           (map (fst o fst o dest_Var) (foldr add_term_vars [] ts)) ts)
      in
        trns
        |> invoke_cg_expr thy defs t
        ||>> fold_map (cg_case_d gen_names dty) (cs ~~ ts')
        |-> (fn (t, ds) => pair (ICase (t, ds)))
      end;
  in case strip_comb t
   of (t as Const (f, ty), ts) =>
        (case get_case_const_data thy f
         of NONE =>
              trns
              |> fail ("not a case constant: " ^ quote f)
          | SOME cs =>
              let
                val (tys, dty) = (split_last o fst o strip_type) ty;
              in
                trns
                |> debug 9 (fn _ => "for case const " ^ f ^ "::"
                     ^ Sign.string_of_typ thy ty ^ ",\n  with " ^ AList.string_of_alist I string_of_int cs
                     ^ ",\n  given as args " ^ (commas o map (Sign.string_of_term thy)) ts
                     ^ ",\n  with significant length " ^ string_of_int (length cs + 1))
                |> fix_nargs thy defs (cg_case dty (cs ~~ tys))
                     (length cs + 1) (t, ts)
                |-> succeed
              end
        )
    | _ =>
        trns
        |> fail ("not a caseconstant expression: " ^ Sign.string_of_term thy t)
  end;

fun defgen_datatype get_datatype thy defs tyco trns =
  case tname_of_idf thy tyco
   of SOME dtname =>
        (case get_datatype thy tyco
         of SOME (vs, cnames) =>
              trns
              |> debug 5 (fn _ => "trying defgen datatype for " ^ quote dtname)
              |> succeed (Datatype (map (rpair [] o unprefix "'") vs, [], []),
                   cnames
                   |> map (idf_of_name thy nsp_const)
                   |> map (fn "0" => "const.Zero" | c => c))
              (*! VARIABLEN, EQTYPE !*)
          | NONE =>
              trns
              |> fail ("no datatype found for " ^ quote tyco))
    | NONE =>
        trns
        |> fail ("not a type constructor: " ^ quote tyco)
  end;

fun defgen_datacons get_datacons thy defs f trns =
  let
    fun the_type "0" = SOME "nat"
      | the_type c =
          case strip_type (Sign.the_const_constraint thy c)
           of (_, Type (dtname, _)) => SOME dtname
            | _ => NONE
  in
    case cname_of_idf thy defs f
     of SOME (c, _) =>
          (case the_type c
            of SOME dtname =>
                 (case get_datacons thy (c, dtname)
                   of SOME tyargs =>
                       trns
                       |> debug 5 (fn _ => "trying defgen datatype constructor for " ^ quote c)
                       |> ensure_def_tyco thy defs (idf_of_tname thy dtname)
                       ||>> fold_map (invoke_cg_type thy defs) tyargs
                       |-> (fn (dtname, tys) => succeed (Datatypecons (dtname, tys), []))
                    | NONE =>
                       trns
                       |> fail ("no datatype constructor found for " ^ quote f))
             | NONE =>
                trns
                |> fail ("no datatype constructor found for " ^ quote f))
      | _ =>
          trns
          |> fail ("not a constant: " ^ quote f)
  end;

fun defgen_recfun get_equations thy defs f trns =
  case cname_of_idf thy defs f
   of SOME (f, ty) =>
        let
          val (eqs, ty) = get_equations thy (f, ty);
        in
          case eqs
           of (_::_) =>
                trns
                |> debug 5 (fn _ => "trying defgen recfun for " ^ quote f)
                |> mk_fun thy defs eqs ty
                |-> (fn def => succeed (def, []))
            | _ =>
                trns
                |> fail ("no recursive definition found for " ^ quote f)
        end
    | NONE =>
        trns
        |> fail ("not a constant: " ^ quote f);


(* theory interface *)

fun mk_deftab thy =
  let
    fun mangle_tyname (ty_decl, ty_def) =
      let
        fun mangle (Type (tyco, tys)) =
              NameSpace.base tyco :: Library.flat (List.mapPartial mangle tys) |> SOME
          | mangle _ =
              NONE
      in
        Vartab.empty
        |> Sign.typ_match thy (ty_decl, ty_def)
        |> map (snd o snd) o Vartab.dest
        |> List.mapPartial mangle
        |> Library.flat
        |> null ? K ["x"]
        |> space_implode "_"
      end;
    fun mangle_instname thyname (cls, tyco) =
      idf_of_name thy nsp_inst
        (NameSpace.append thyname (NameSpace.base cls ^ "_" ^ NameSpace.base tyco))
    fun add_clsmems classtab ((overl, overl_rev), defs, (clstab, clstab_rev, clsmems)) =
      ((overl
        |> Symtab.fold
             (fn (class, (clsmems, _)) =>
               fold
                 (fn clsmem =>
                   Symtab.default (clsmem, [])
                   #> Symtab.map_entry clsmem
                        (cons (Sign.the_const_type thy clsmem, idf_of_name thy nsp_mem clsmem))
                 ) clsmems
             ) classtab,
        overl_rev
        |> Symtab.fold
             (fn (class, (clsmems, _)) =>
               fold
                 (fn clsmem =>
                   Symtab.update_new
                     (idf_of_name thy nsp_mem clsmem, (clsmem, Sign.the_const_type thy clsmem))
                 ) clsmems
             ) classtab),
       defs,
       (clstab
        |> Symtab.fold
             (fn (cls, (_, clsinsts)) => fold
                (fn (tyco, thyname) => Insttab.update ((cls, tyco), mangle_instname thyname (cls, tyco))) clsinsts)
             classtab,
        clstab_rev
        |> Symtab.fold
             (fn (cls, (_, clsinsts)) => fold
                (fn (tyco, thyname) => Symtab.update (mangle_instname thyname (cls, tyco), (cls, tyco))) clsinsts)
             classtab,
        clsmems
        |> Symtab.fold
             (fn (class, (clsmems, _)) => fold
                (fn clsmem => Symtab.update (clsmem, class)) clsmems)
             classtab))
    fun add_def (name, [(ty, (_, (args, rhs)))]) (overl, defs, clstab) =
          (overl,
           defs |> Symtab.update_new (idf_of_name thy nsp_const name, (args, rhs, ty)),
           clstab)
      | add_def (name, ds) ((overl, overl_rev), defs, clstab) =
          let
            val ty_decl = Sign.the_const_constraint thy name;
            fun mk_idf ("0", Type ("nat", [])) = "const.Zero"
              | mk_idf ("1", Type ("nat", [])) = "."
              | mk_idf (nm, ty) =
                  if is_number nm
                  then nm
                  else idf_of_name thy nsp_const nm
                     ^ "_" ^ mangle_tyname (ty_decl, ty)
            val overl_lookups = map
              (fn (ty, (_, (args, rhs))) => (ty, mk_idf (name, ty), args, rhs)) ds;
          in
            ((overl
              |> Symtab.default (name, [])
              |> Symtab.map_entry name (append (map (fn (ty, idf, _, _) => (ty, idf)) overl_lookups)),
              overl_rev
              |> fold Symtab.update_new (map (fn (ty, idf, _, _) => (idf, (name, ty))) overl_lookups)),
             defs
             |> fold Symtab.update_new (map (fn (ty, idf, args, rhs) => (idf, (args, rhs, ty))) overl_lookups), clstab)
          end;  in
    ((Symtab.empty, Symtab.empty), Symtab.empty, (Insttab.empty, Symtab.empty, Symtab.empty))
    |> add_clsmems (ClassPackage.get_classtab thy)
    |> fold add_def (Codegen.mk_deftab thy |> Symtab.dest)
  end;

fun expand_module defs gen thy =
  let
    fun put_module modl =
      map_codegen_data (fn (_, gens, lookups, serialize_data, logic_data) =>
        (modl, gens, lookups, serialize_data, logic_data));
    val _ = put_module : module -> theory -> theory;
  in
    (#modl o CodegenData.get) thy
    |> start_transact (gen thy defs)
    |-> (fn x => fn modl => (x, put_module modl thy))
  end;


(* syntax *)

fun gen_add_syntax_tyco prep_tyco prep_mfx prep_primname serial_name ((raw_tyco, raw_mfx), primdef) thy =
  let
    val tyco = prep_tyco thy raw_tyco;
    val _ = if member (op =) prims tyco
      then error ("attempted to re-define primitive " ^ quote tyco)
      else ()
    fun add_primdef NONE = I
      | add_primdef (SOME (name, (def, deps))) =
          CodegenSerializer.add_prim (prep_primname thy tyco name, (def, deps))
  in
    thy
    |> prep_mfx raw_mfx
    |-> (fn mfx => map_codegen_data
      (fn (modl, gens, lookups, serialize_data, logic_data) =>
         (modl, gens, lookups,
          serialize_data |> Symtab.map_entry serial_name
            (map_serialize_data
              (fn (primitives, syntax_tyco, syntax_const) =>
               (primitives |> add_primdef primdef,
                syntax_tyco |> Symtab.update_new (tyco, mfx),
                syntax_const))),
          logic_data)))
  end;

val add_syntax_tyco_i = gen_add_syntax_tyco (K I) pair ((K o K) I);
val add_syntax_tyco =
  let
    fun mk_name _ _ (SOME name) = name
      | mk_name thy tyco NONE =
          let
            val name = Sign.extern_type thy tyco
          in
            if NameSpace.is_qualified name
            then error ("no unique identifier for syntax definition: " ^ quote tyco)
            else name
          end;
    fun prep_mfx mfx thy =
      let
        val proto_mfx = Codegen.parse_mixfix
          (typ_of o read_ctyp thy) mfx;
        fun generate thy defs = fold_map (invoke_cg_type thy defs)
          (Codegen.quotes_of proto_mfx);
      in
        thy
        |> expand_module (mk_deftab thy) generate
        |-> (fn tys => pair (Codegen.replace_quotes tys proto_mfx))
      end;
  in
    gen_add_syntax_tyco (fn thy => idf_of_tname thy o Sign.intern_type thy)
      prep_mfx mk_name
  end;

fun gen_add_syntax_const prep_const prep_mfx prep_primname serial_name ((raw_f, raw_mfx), primdef) thy =
  let
    val f = prep_const thy raw_f;
    val _ = if member (op =) prims f
      then error ("attempted to re-define primitive " ^ quote f)
      else ()
    fun add_primdef NONE = I
      | add_primdef (SOME (name, (def, deps))) =
          CodegenSerializer.add_prim (prep_primname thy f name, (def, deps))
  in
    thy
    |> prep_mfx raw_mfx
    |-> (fn mfx => map_codegen_data
      (fn (modl, gens, lookups, serialize_data, logic_data) =>
         (modl, gens, lookups,
          serialize_data |> Symtab.map_entry serial_name
            (map_serialize_data
              (fn (primitives, syntax_tyco, syntax_const) =>
               (primitives |> add_primdef primdef,
                syntax_tyco,
                syntax_const |> Symtab.update_new (f, mfx)))),
          logic_data)))
  end;

val add_syntax_const_i = gen_add_syntax_const (K I) pair ((K o K) I);
val add_syntax_const =
  let
    fun prep_const thy (raw_f, raw_ty) =
      let
        val defs = mk_deftab thy;
        val f = Sign.intern_const thy raw_f;
        val ty =
          raw_ty
          |> Option.map (Sign.read_tyname thy)
          |> the_default (Sign.the_const_constraint thy f);
      in idf_of_cname thy defs (f, ty) end;
    fun mk_name _ _ (SOME name) = name
      | mk_name thy f NONE =
          let
            val name = Sign.extern_const thy f
          in
            if NameSpace.is_qualified name
            then error ("no unique identifier for syntax definition: " ^ quote f)
            else name
          end;
    fun prep_mfx mfx thy =
      let
        val proto_mfx = Codegen.parse_mixfix
          (term_of o read_cterm thy o rpair TypeInfer.logicT) mfx;
        fun generate thy defs = fold_map (invoke_cg_expr thy defs)
          (Codegen.quotes_of proto_mfx);
      in
        thy
        |> expand_module (mk_deftab thy) generate
        |-> (fn es => pair (Codegen.replace_quotes es proto_mfx))
      end;
  in
    gen_add_syntax_const prep_const prep_mfx mk_name
  end;


(* code generation *)

fun get_serializer thy serial_name =
  (#serializer o (fn data => (the oo Symtab.lookup) data serial_name)
    o #serialize_data o CodegenData.get) thy;

fun mk_const thy (f, s_ty) =
  let
    val f' = Sign.intern_const thy f;
    val ty = case s_ty
     of NONE => Sign.the_const_constraint thy f'
      | SOME s => Sign.read_typ (thy, K NONE) s;
  in (f', ty) end;

fun generate_code consts thy =
  let
    val defs = mk_deftab thy;
    val consts' = map (idf_of_cname thy defs o mk_const thy) consts;
    fun generate thy defs = fold_map (ensure_def_const thy defs) consts'
  in
    thy
    |> expand_module defs generate
    |-> (fn _ => pair consts')
  end;

fun serialize_code serial_name filename consts thy =
  let
    fun mk_sfun tab =
      let
        fun na name =
          Option.map Codegen.num_args_of (Symtab.lookup tab name)
        fun stx name =
          Codegen.fillin_mixfix ((the o Symtab.lookup tab) name)
      in (na, stx) end;
    val serialize_data =
      thy
      |> CodegenData.get
      |> #serialize_data
      |> (fn data => (the oo Symtab.lookup) data serial_name)
    val serializer' = (get_serializer thy serial_name)
      ((mk_sfun o #syntax_tyco) serialize_data)
      ((mk_sfun o #syntax_const) serialize_data)
      (#primitives serialize_data);
    val _ = serializer' : string list option -> module -> Pretty.T;
    val compile_it = serial_name = "ml" andalso filename = "-";
    fun use_code code =
      if compile_it
      then use_text Context.ml_output false code
      else File.write (Path.unpack filename) (code ^ "\n");
  in
    thy
    |> (if is_some consts then generate_code (the consts) else pair [])
    |-> (fn [] => `(serializer' NONE o #modl o CodegenData.get)
          | consts => `(serializer' (SOME consts) o #modl o CodegenData.get))
    |-> (fn code => (setmp print_mode [] (use_code o Pretty.output) code; I))
  end;


(* toplevel interface *)

local

structure P = OuterParse
and K = OuterKeyword

in

val (generateK, serializeK, extractingK, aliasK, definedK, dependingK, syntax_tycoK, syntax_constK) =
  ("code_generate", "code_serialize", "extracting", "defined_by", "depending_on", "code_alias", "code_syntax_tyco", "code_syntax_const");

val generateP =
  OuterSyntax.command generateK "generate executable code for constants" K.thy_decl (
    Scan.repeat1 (P.name -- Scan.option (P.$$$ "::" |-- P.typ))
    >> (fn consts =>
          Toplevel.theory (generate_code consts #> snd))
  );

val serializeP =
  OuterSyntax.command serializeK "serialize executable code for constants" K.thy_decl (
    P.name
    -- P.name
    -- Scan.option (
         P.$$$ extractingK
         |-- Scan.repeat1 (P.name -- Scan.option (P.$$$ "::" |-- P.typ))
       )
    >> (fn ((serial_name, filename), consts) =>
          Toplevel.theory (serialize_code serial_name filename consts))
  );

val aliasP =
  OuterSyntax.command aliasK "declare an alias for a theory identifier" K.thy_decl (
    P.name
    -- P.name
      >> (fn (src, dst) => Toplevel.theory (add_alias (src, dst)))
  );

val syntax_tycoP =
  OuterSyntax.command syntax_tycoK "define code syntax for type constructor" K.thy_decl (
    P.string
    -- Scan.repeat1 (
         P.xname -- (P.$$$ "(" |-- P.string --| P.$$$ ")")
         -- Scan.option (
              P.$$$ definedK
              |-- Scan.option (P.$$$ "(" |-- P.string --| P.$$$ ")")
              -- (P.string -- Scan.optional (P.$$$ dependingK |-- P.list1 P.string) [])
            )
       )
    >> (fn (serial_name, xs) =>
          (Toplevel.theory oo fold)
            (fn ((tyco, raw_mfx), raw_def) =>
              add_syntax_tyco serial_name ((tyco, raw_mfx), raw_def)) xs)
  );

val syntax_constP =
  OuterSyntax.command syntax_constK "define code syntax for constant" K.thy_decl (
    P.string
    -- Scan.repeat1 (
         (P.xname -- Scan.option (P.$$$ "::" |-- P.typ)) -- (P.$$$ "(" |-- P.string --| P.$$$ ")")
         -- Scan.option (
              P.$$$ definedK
              |-- Scan.option (P.$$$ "(" |-- P.string --| P.$$$ ")")
              -- (P.string -- Scan.optional (P.$$$ dependingK |-- P.list1 P.string) [])
            )
       )
    >> (fn (serial_name, xs) =>
          (Toplevel.theory oo fold)
            (fn ((f, raw_mfx), raw_def) =>
              add_syntax_const serial_name ((f, raw_mfx), raw_def)) xs)
  );

val _ = OuterSyntax.add_parsers [generateP, serializeP, aliasP, syntax_tycoP, syntax_constP];
val _ = OuterSyntax.add_keywords [extractingK, definedK, dependingK];


(* setup *)
val _ =
  let
    val bool = Type ("bool", []);
    val nat = Type ("nat", []);
    val int = Type ("IntDef.int", []);
    fun list t = Type ("List.list", [t]);
    fun pair t1 t2 = Type ("*", [t1, t2]);
    val A = TVar (("'a", 0), []);
    val B = TVar (("'b", 0), []);
  in Context.add_setup [
    CodegenData.init,
    add_codegen_sort ("default", codegen_sort_default),
    add_codegen_type ("default", codegen_type_default),
    add_codegen_expr ("default", codegen_expr_default),
(*     add_codegen_expr ("eq", codegen_eq),  *)
    add_codegen_expr ("neg", codegen_neg),
    add_defgen ("clsdecl", defgen_clsdecl),
    add_defgen ("tyco_fallback", defgen_tyco_fallback),
    add_defgen ("const_fallback", defgen_const_fallback),
    add_defgen ("defs", defgen_defs),
    add_defgen ("clsmem", defgen_clsmem),
    add_defgen ("clsinst", defgen_clsinst),
    add_alias ("op <>", "op_neq"),
    add_alias ("op >=", "op_ge"),
    add_alias ("op >", "op_gt"),
    add_alias ("op <=", "op_le"),
    add_alias ("op <", "op_lt"),
    add_alias ("op +", "op_add"),
    add_alias ("op -", "op_minus"),
    add_alias ("op *", "op_times"),
    add_alias ("op @", "op_append"),
    add_lookup_tyco ("bool", type_bool),
    add_lookup_tyco ("IntDef.int", type_integer),
    add_lookup_tyco ("List.list", type_list),
    add_lookup_tyco ("*", type_pair),
    add_lookup_const (("True", bool), Cons_true),
    add_lookup_const (("False", bool), Cons_false),
    add_lookup_const (("Not", bool --> bool), Fun_not),
    add_lookup_const (("op &", bool --> bool --> bool), Fun_and),
    add_lookup_const (("op |", bool --> bool --> bool), Fun_or),
    add_lookup_const (("HOL.If", bool --> A --> A --> A), Fun_if),
    add_lookup_const (("List.list.Cons", A --> list A --> list A), Cons_cons),
    add_lookup_const (("List.list.Nil", list A), Cons_nil),
    add_lookup_const (("Pair", A --> B --> pair A B), Cons_pair),
    add_lookup_const (("fst", pair A B --> A), Fun_fst),
    add_lookup_const (("snd", pair A B --> B), Fun_snd),
    add_lookup_const (("1", nat),
      IApp (
        IConst ("const.Suc", IFun (IType ("type.nat", []), IFun (IType ("type.nat", []), IType ("type.nat", [])))),
        IConst ("const.Zero", IType ("type.nat", []))
      )),
    add_lookup_const (("0", int), Fun_0),
    add_lookup_const (("1", int), Fun_1),
    add_lookup_const (("op +", int --> int --> int), Fun_add),
    add_lookup_const (("op *", int --> int --> int), Fun_mult),
    add_lookup_const (("uminus", int --> int), Fun_minus),
    add_lookup_const (("op <", int --> int --> bool), Fun_lt),
    add_lookup_const (("op <=", int --> int --> bool), Fun_le),
    add_lookup_const (("Wellfounded_Recursion.wfrec", ((A --> B) --> A --> B) --> A --> B), Fun_wfrec),
    add_lookup_const (("op =", A --> A --> bool), Fun_eq)
  ] end;

(* "op /" ??? *)

end; (* local *)

end; (* struct *)
