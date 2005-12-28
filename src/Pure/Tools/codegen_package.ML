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
  type auxtab;
  type appgen;
  type defgen;
  val add_appconst: string * ((int * int) * appgen) -> theory -> theory;
  val add_appconst_i: string * ((int * int) * appgen) -> theory -> theory;
  val add_appgen: string * appgen -> theory -> theory;
  val add_defgen: string * defgen -> theory -> theory;
  val add_lookup_tyco: string * string -> theory -> theory;
  val add_lookup_const: (string * typ) * CodegenThingol.iexpr -> theory -> theory;
  val add_syntax_tyco: string -> (xstring * string * CodegenSerializer.fixity)
    * (string option * (string * string list)) option
    -> theory -> theory;
  val add_syntax_tyco_i: string -> (string * CodegenThingol.itype Codegen.mixfix list * CodegenSerializer.fixity)
    * (string * (string * string list)) option
    -> theory -> theory;
  val add_syntax_const: string -> ((xstring * string option) * string * CodegenSerializer.fixity)
    * (string option * (string * string list)) option
    -> theory -> theory;
  val add_syntax_const_i: string -> ((string * typ) * CodegenThingol.iexpr Codegen.mixfix list * CodegenSerializer.fixity)
    * (string * (string * string list)) option
    -> theory -> theory;
  val add_prim_class: xstring -> (string * string) -> string list
    -> theory -> theory;
  val add_prim_tyco: xstring -> (string * string) -> string list
    -> theory -> theory;
  val add_prim_const: xstring * string -> (string * string) -> string list
    -> theory -> theory;
  val add_prim_i: string -> (string * Pretty.T) -> string list
    -> theory -> theory;
  val add_alias: string * string -> theory -> theory;
  val set_is_datatype: (theory -> string -> bool) -> theory -> theory;
  val set_get_all_datatype_cons : (theory -> (string * string) list)
    -> theory -> theory;

  val exprgen_type: theory -> auxtab
    -> typ -> CodegenThingol.transact -> CodegenThingol.itype * CodegenThingol.transact;
  val exprgen_term: theory -> auxtab
    -> term -> CodegenThingol.transact -> CodegenThingol.iexpr * CodegenThingol.transact;
  val ensure_def_tyco: theory -> auxtab
    -> string -> CodegenThingol.transact -> string * CodegenThingol.transact;
  val ensure_def_const: theory -> auxtab
    -> string * typ -> CodegenThingol.transact -> string * CodegenThingol.transact;

  val appgen_let: (int -> term -> term list * term)
    -> appgen;
  val appgen_split: (int -> term -> term list * term)
    -> appgen;
  val appgen_number_of: (term -> IntInf.int) -> (term -> term)
    -> appgen;
  val appgen_case: (theory -> string -> (string * int) list option)
    -> appgen;
  val defgen_datatype: (theory -> string -> ((string * sort) list * string list) option)
    -> (theory -> string * string -> typ list option)
    -> defgen;
  val defgen_datacons: (theory -> string * string -> typ list option)
    -> defgen;
  val defgen_recfun: (theory -> string * typ -> (term list * term) list * typ)
    -> defgen;

  val print_codegen_generated: theory -> unit;
  val rename_inconsistent: theory -> theory;

  (*debugging purpose only*)
  structure InstNameMangler: NAME_MANGLER;
  structure ConstNameMangler: NAME_MANGLER;
  structure DatatypeconsNameMangler: NAME_MANGLER;
  structure CodegenData: THEORY_DATA;
  val mk_tabs: theory -> auxtab;
  val alias_get: theory -> string -> string;
  val idf_of_name: theory -> string -> string -> string;
  val idf_of_const: theory -> auxtab -> string * typ -> string;
end;

structure CodegenPackage : CODEGEN_PACKAGE =
struct

open CodegenThingolOp;
infix 8 `%%;
infixr 6 `->;
infixr 6 `-->;
infix 4 `$;
infix 4 `$$;
infixr 5 `|->;
infixr 5 `|-->;

(* auxiliary *)

fun devarify_type ty = (fst o Type.freeze_thaw_type) ty;
fun devarify_term t = (fst o Type.freeze_thaw) t;

val is_number = is_some o Int.fromString;

fun newline_correct s =
  s
  |> space_explode "\n"
  |> map (implode o (fn [] => []
                      | (" "::xs) => xs
                      | xs => xs) o explode)
  |> space_implode "\n";


(* shallo name spaces *)

val nsp_class = "class";
val nsp_tyco = "tyco";
val nsp_const = "const";
val nsp_overl = "overl";
val nsp_dtcon = "dtcon";
val nsp_mem = "mem";
val nsp_inst = "inst";
val nsp_eq_inst = "eq_inst";
val nsp_eq_pred = "eq";


(* code generator data types *)

structure InstNameMangler = NameManglerFun (
  type ctxt = theory;
  type src = string * (class * string);
  val ord = prod_ord string_ord (prod_ord string_ord string_ord);
  fun mk thy ((thyname, (cls, tyco)), i) =
    NameSpace.base cls ^ "_" ^ NameSpace.base tyco ^ implode (replicate i "'")
    |> NameSpace.append thyname;
  fun is_valid _ _ = true;
  fun maybe_unique _ _ = NONE;
  fun re_mangle _ dst = error ("no such instance: " ^ quote dst);
);

structure ConstNameMangler = NameManglerFun (
  type ctxt = theory;
  type src = string * (typ * typ);
  val ord = prod_ord string_ord (prod_ord Term.typ_ord Term.typ_ord);
  fun mk thy ((c, (ty_decl, ty)), i) =
    let
      fun mangle (Type (tyco, tys)) =
            NameSpace.base tyco :: Library.flat (List.mapPartial mangle tys) |> SOME
        | mangle _ =
            NONE
    in
      Vartab.empty
      |> Sign.typ_match thy (ty_decl, ty)
      |> map (snd o snd) o Vartab.dest
      |> List.mapPartial mangle
      |> Library.flat
      |> null ? K ["x"]
      |> cons c
      |> space_implode "_"
      |> curry (op ^ o swap) ((implode oo replicate) i "'")
    end;
  fun is_valid _ _ = true;
  fun maybe_unique _ _ = NONE;
  fun re_mangle _ dst = error ("no such constant: " ^ quote dst);
);

structure DatatypeconsNameMangler = NameManglerFun (
  type ctxt = theory;
  type src = string * string;
  val ord = prod_ord string_ord string_ord;
  fun mk thy (("0", "nat"), _) =
         "Nat.Zero"
    | mk thy ((co, dtco), i) =
        let
          fun basename 0 = NameSpace.base co
            | basename 1 = NameSpace.base dtco ^ "_" ^ NameSpace.base co
            | basename i = NameSpace.base dtco ^ "_" ^ NameSpace.base co ^ "_" ^ (implode oo replicate) (i-1) "'";
          fun strip_dtco name =
            case (rev o NameSpace.unpack) name
             of x1::x2::xs =>
                  if x2 = NameSpace.base dtco
                  then NameSpace.pack (x1::xs)
                  else name
              | _ => name;
        in
          NameSpace.append (NameSpace.drop_base dtco) (basename i)
          |> strip_dtco
        end;
  fun is_valid _ _ = true;
  fun maybe_unique _ _ = NONE;
  fun re_mangle _ dst = error ("no such datatype constructor: " ^ quote dst);
);

type auxtab = ((typ * (term list * term)) Symtab.table * string Symtab.table)
  * (InstNameMangler.T * ((typ * typ list) Symtab.table * ConstNameMangler.T) * DatatypeconsNameMangler.T);

type appgen = theory -> auxtab -> ((string * typ) * term list, iexpr) gen_exprgen;
type defgen = theory -> auxtab -> gen_defgen;


(* serializer *)

val serializer_ml =
  let
    val name_root = "Generated";
    val nsp_conn = [
      [nsp_class, nsp_tyco], [nsp_const, nsp_overl, nsp_dtcon, nsp_mem, nsp_inst, nsp_eq_inst, nsp_eq_pred]
    ];
  in CodegenSerializer.ml_from_thingol nsp_conn nsp_class name_root end;

val serializer_hs =
  let
    val name_root = "Generated";
    val nsp_conn = [
      [nsp_class], [nsp_tyco], [nsp_const, nsp_overl, nsp_mem, nsp_eq_pred], [nsp_dtcon], [nsp_inst, nsp_eq_inst]
    ];
  in CodegenSerializer.haskell_from_thingol nsp_conn nsp_dtcon name_root end;


(* theory data for code generator *)

type gens = {
  appconst: ((int * int) * (appgen * stamp)) Symtab.table,
  appgens: (string * (appgen * stamp)) list,
  defgens: (string * (defgen * stamp)) list
};

fun map_gens f { appconst, appgens, defgens } =
  let
    val (appconst, appgens, defgens) =
      f (appconst, appgens, defgens)
  in { appconst = appconst, appgens = appgens, defgens = defgens } : gens end;

fun merge_gens
  ({ appconst = appconst1 , appgens = appgens1, defgens = defgens1 },
   { appconst = appconst2 , appgens = appgens2, defgens = defgens2 }) =
  { appconst = Symtab.merge
      (fn ((bounds1, (_, stamp1)), (bounds2, (_, stamp2))) => bounds1 = bounds2 andalso stamp1 = stamp2)
      (appconst1, appconst2),
    appgens = AList.merge (op =) (eq_snd (op =)) (appgens1, appgens2),
    defgens = AList.merge (op =) (eq_snd (op =)) (defgens1, defgens2) } : gens;

type lookups = {
  lookups_tyco: string Symtab.table,
  lookups_const: (typ * iexpr) list Symtab.table
}

fun map_lookups f { lookups_tyco, lookups_const } =
  let
    val (lookups_tyco, lookups_const) =
      f (lookups_tyco, lookups_const)
  in { lookups_tyco = lookups_tyco, lookups_const = lookups_const } : lookups end;

fun merge_lookups
  ({ lookups_tyco = lookups_tyco1, lookups_const = lookups_const1 },
   { lookups_tyco = lookups_tyco2, lookups_const = lookups_const2 }) =
  { lookups_tyco = Symtab.merge (op =) (lookups_tyco1, lookups_tyco2),
    lookups_const = Symtab.merge (op =) (lookups_const1, lookups_const2) } : lookups;

type logic_data = {
  is_datatype: ((theory -> string -> bool) * stamp) option,
  get_all_datatype_cons: ((theory -> (string * string) list) * stamp) option,
  alias: string Symtab.table * string Symtab.table
};

fun map_logic_data f { is_datatype, get_all_datatype_cons, alias } =
  let
    val ((is_datatype, get_all_datatype_cons), alias) =
      f ((is_datatype, get_all_datatype_cons), alias)
  in { is_datatype = is_datatype, get_all_datatype_cons = get_all_datatype_cons, alias = alias } : logic_data end;

fun merge_logic_data
  ({ is_datatype = is_datatype1, get_all_datatype_cons = get_all_datatype_cons1, alias = alias1 },
   { is_datatype = is_datatype2, get_all_datatype_cons = get_all_datatype_cons2, alias = alias2 }) =
  let
    fun merge_opt _ (x1, NONE) = x1
      | merge_opt _ (NONE, x2) = x2
      | merge_opt eq (SOME x1, SOME x2) =
          if eq (x1, x2) then SOME x1 else error ("incompatible options during merge");
  in
    { is_datatype = merge_opt (eq_snd (op =)) (is_datatype1, is_datatype2),
      get_all_datatype_cons = merge_opt (eq_snd (op =)) (get_all_datatype_cons1, get_all_datatype_cons2),
      alias = (Symtab.merge (op =) (fst alias1, fst alias2),
               Symtab.merge (op =) (snd alias1, snd alias2)) } : logic_data
  end;

type serialize_data = {
  serializer: CodegenSerializer.serializer,
  primitives: CodegenSerializer.primitives,
  syntax_tyco: (itype CodegenSerializer.pretty_syntax * stamp) Symtab.table,
  syntax_const: (iexpr CodegenSerializer.pretty_syntax * stamp) Symtab.table
};

fun map_serialize_data f { serializer, primitives, syntax_tyco, syntax_const } =
  let
    val (primitives, syntax_tyco, syntax_const) =
      f (primitives, syntax_tyco, syntax_const)
  in { serializer = serializer, primitives = primitives,
       syntax_tyco = syntax_tyco, syntax_const = syntax_const } : serialize_data
  end;

fun merge_serialize_data
  ({ serializer = serializer, primitives = primitives1,
     syntax_tyco = syntax_tyco1, syntax_const = syntax_const1 },
   {serializer = _, primitives = primitives2,
     syntax_tyco = syntax_tyco2, syntax_const = syntax_const2 }) =
  { serializer = serializer,
    primitives = CodegenSerializer.merge_prims (primitives1, primitives2) : CodegenSerializer.primitives,
    syntax_tyco = Symtab.merge (eq_snd (op =)) (syntax_tyco1, syntax_tyco2),
    syntax_const = Symtab.merge (eq_snd (op =)) (syntax_const1, syntax_const2) } : serialize_data;

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
    gens = { appconst = Symtab.empty, appgens = [], defgens = [] } : gens,
    lookups = { lookups_tyco = Symtab.empty, lookups_const = Symtab.empty } : lookups,
    logic_data = { is_datatype = NONE, get_all_datatype_cons = NONE,
      alias = (Symtab.empty, Symtab.empty) } : logic_data,
    serialize_data =
      Symtab.empty
      |> Symtab.update ("ml",
          { serializer = serializer_ml : CodegenSerializer.serializer,
            primitives =
              CodegenSerializer.empty_prims
              |> CodegenSerializer.add_prim ("Eq", ("type 'a Eq = {eq: 'a -> 'a -> bool};", []))
              |> CodegenSerializer.add_prim ("fst", ("fun fst (x, _) = x;", []))
              |> CodegenSerializer.add_prim ("snd", ("fun snd (_, y) = y;", []))
              |> CodegenSerializer.add_prim ("wfrec", ("fun wfrec f x = f (wfrec f) x;", [])),
            syntax_tyco = Symtab.empty, syntax_const = Symtab.empty })
      |> Symtab.update ("haskell",
          { serializer = serializer_hs : CodegenSerializer.serializer,
            primitives =
              CodegenSerializer.empty_prims
              |> CodegenSerializer.add_prim ("wfrec", ("wfrec f x = f (wfrec f) x", [])),
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

fun gen_add_appconst prep_const (raw_c, (bounds, ag)) thy =
  let
    val c = prep_const thy raw_c;
  in map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (appconst, appgens, defgens) =>
            (appconst
             |> Symtab.update (c, (bounds, (ag, stamp ()))),
             appgens, defgens)), lookups, serialize_data, logic_data)) thy
  end;

val add_appconst = gen_add_appconst Sign.intern_const;
val add_appconst_i = gen_add_appconst (K I);

fun add_appgen (name, ag) =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (appconst, appgens, defgens) =>
            (appconst, appgens
             |> Output.update_warn (op =) ("overwriting existing definition application generator " ^ name) (name, (ag, stamp ())),
             defgens)), lookups, serialize_data, logic_data));

fun add_defgen (name, dg) =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (appconst, appgens, defgens) =>
            (appconst, appgens, defgens
             |> Output.update_warn (op =) ("overwriting existing definition definition generator " ^ name) (name, (dg, stamp ())))),
             lookups, serialize_data, logic_data));

fun get_defgens thy tabs =
  (map (apsnd (fn (dg, _) => dg thy tabs)) o #defgens o #gens o CodegenData.get) thy;

fun add_lookup_tyco (src, dst) =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl, gens,
        lookups |> map_lookups
          (fn (lookups_tyco, lookups_const) =>
            (lookups_tyco |> Symtab.update_new (src, dst),
             lookups_const)),
        serialize_data, logic_data));

val lookup_tyco = Symtab.lookup o #lookups_tyco o #lookups o CodegenData.get;

fun add_lookup_const ((src, ty), dst) =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl, gens,
        lookups |> map_lookups
          (fn (lookups_tyco, lookups_const) =>
            (lookups_tyco,
             lookups_const |> Symtab.update_multi (src, (ty, dst)))),
        serialize_data, logic_data));

fun lookup_const thy (f, ty) =
  (Symtab.lookup_multi o #lookups_const o #lookups o CodegenData.get) thy f
  |> (fn tab => AList.lookup (Sign.typ_instance thy) tab ty);

fun set_is_datatype f =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl, gens, lookups, serialize_data,
        logic_data
        |> map_logic_data ((apfst o apfst) (K (SOME (f, stamp ()))))));

fun is_datatype thy =
  case (#is_datatype o #logic_data o CodegenData.get) thy
   of NONE => K false
    | SOME (f, _) => f thy;

fun set_get_all_datatype_cons f =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl, gens, lookups, serialize_data,
        logic_data
        |> map_logic_data ((apfst o apsnd) (K (SOME (f, stamp ()))))));

fun get_all_datatype_cons thy =
  case (#get_all_datatype_cons o #logic_data o CodegenData.get) thy
   of NONE => []
    | SOME (f, _) => f thy;

fun add_alias (src, dst) =
  map_codegen_data
    (fn (modl, gens, lookups, serialize_data, logic_data) =>
       (modl, gens, lookups, serialize_data,
        logic_data |> map_logic_data
          (apsnd (fn (tab, tab_rev) =>
            (tab |> Symtab.update (src, dst),
             tab_rev |> Symtab.update (dst, src))))));


(* name handling *)

val nsp_class = "class";
val nsp_tyco = "tyco";
val nsp_const = "const";
val nsp_overl = "overl";
val nsp_dtcon = "dtcon";
val nsp_mem = "mem";
val nsp_inst = "inst";
val nsp_eq_inst = "eq_inst";
val nsp_eq_pred = "eq";

val alias_get = perhaps o Symtab.lookup o fst o #alias o #logic_data o CodegenData.get;
val alias_rev = perhaps o Symtab.lookup o snd o #alias o #logic_data o CodegenData.get;

fun add_nsp shallow name =
  name
  |> NameSpace.unpack
  |> split_last
  |> apsnd (single #> cons shallow)
  |> (op @)
  |> NameSpace.pack;
fun dest_nsp nsp idf =
  let
    val idf' = NameSpace.unpack idf;
    val (idf'', idf_base) = split_last idf';
    val (modl, shallow) = split_last idf'';
  in
    if nsp = shallow
    then (SOME o NameSpace.pack) (modl @ [idf_base])
    else NONE
  end;

fun idf_of_name thy shallow name =
  if is_number name
  then name
  else
    name
    |> alias_get thy
    |> add_nsp shallow;
fun name_of_idf thy shallow idf =
  idf
  |> dest_nsp shallow
  |> Option.map (alias_rev thy);


(* code generator instantiation *)

fun ensure_def_class thy tabs cls trns =
  let
    val cls' = idf_of_name thy nsp_class cls;
  in
    trns
    |> debug 4 (fn _ => "generating class " ^ quote cls)
    |> gen_ensure_def (get_defgens thy tabs) ("generating class " ^ quote cls) cls'
    |> pair cls'
  end;

fun ensure_def_inst thy (tabs as (_, (insttab, _, _))) (cls, tyco) trns =
  let
    val thyname = (the o AList.lookup (op =) (ClassPackage.the_tycos thy cls)) tyco;
    val inst = idf_of_name thy nsp_inst (InstNameMangler.get thy insttab (thyname, (cls, tyco)));
  in
    trns
    |> debug 4 (fn _ => "generating instance " ^ quote cls ^ " / " ^ quote tyco)
    |> gen_ensure_def (get_defgens thy tabs) ("generating instance " ^ quote cls ^ " / " ^ quote tyco) inst
    |> pair inst
  end;

fun ensure_def_tyco thy tabs tyco trns =
  let
    val tyco' = idf_of_name thy nsp_tyco tyco;
  in case lookup_tyco thy tyco
   of NONE =>
        trns
        |> debug 4 (fn _ => "generating type constructor " ^ quote tyco)
        |> gen_ensure_def (get_defgens thy tabs) ("generating type constructor " ^ quote tyco) tyco'
        |> pair tyco'
    | SOME tyco =>
        trns
        |> pair tyco
  end;

fun idf_of_const thy (tabs as ((_, clsmemtab), (_, (overltab1, overltab2), dtcontab))) (c, ty) =
  let
    fun get_overloaded (c, ty) =
      case Symtab.lookup overltab1 c
       of SOME (ty_decl, tys) =>
            (case find_first (curry (Sign.typ_instance thy) ty) tys
             of SOME ty' => ConstNameMangler.get thy overltab2
                  (idf_of_name thy nsp_overl c, (ty_decl, ty')) |> SOME
              | _ => NONE)
        | _ => NONE
    fun get_datatypecons (c, ty) =
      case (snd o strip_type) ty
       of Type (tyco, _) =>
            try (DatatypeconsNameMangler.get thy dtcontab) (c, tyco)
        | _ => NONE;
  in case get_overloaded (c, ty)
   of SOME idf => idf
    | NONE => case get_datatypecons (c, ty)
   of SOME c' => idf_of_name thy nsp_dtcon c'
    | NONE => case Symtab.lookup clsmemtab c
   of SOME _ => idf_of_name thy nsp_mem c
    | NONE => idf_of_name thy nsp_const c
  end;

fun recconst_of_idf thy (_, (_, (_, overltab2), _)) idf =
  case name_of_idf thy nsp_const idf
   of SOME c => SOME (c, Sign.the_const_constraint thy c)
    | NONE => (
        case dest_nsp nsp_overl idf
         of SOME _ =>
              idf
              |> ConstNameMangler.rev thy overltab2
              |> apfst (the o name_of_idf thy nsp_overl)
              |> apsnd snd
              |> SOME
          | NONE => NONE
      );

fun ensure_def_const thy (tabs as ((_, clsmemtab), (_, overltab, dtcontab))) (c, ty) trns =
  let
    val c' = idf_of_const thy tabs (c, ty);
  in case lookup_const thy (c, ty)
   of NONE =>
        trns
        |> debug 4 (fn _ => "generating constant " ^ quote c)
        |> gen_ensure_def (get_defgens thy tabs) ("generating constant " ^ quote c) c'
        |> pair c'
    | SOME (IConst (c, ty)) =>
        trns
        |> pair c
  end;

fun ensure_def_eq thy tabs (dtco, (eqpred, arity)) trns =
  let
    val name_dtco = (the ooo name_of_idf) thy nsp_tyco dtco;
    val idf_eqinst = idf_of_name thy nsp_eq_inst name_dtco;
    val idf_eqpred = idf_of_name thy nsp_eq_pred name_dtco;
    val inst_sortlookup = map (fn (v, _) => [ClassPackage.Lookup ([], (v, 0))]) arity;
    fun mk_eq_pred _ trns =
      trns
      |> succeed (eqpred, [])
    fun mk_eq_inst _ trns =
      trns
      |> gen_ensure_def [("eqpred", mk_eq_pred)] ("generating equality predicate for " ^ quote dtco) idf_eqpred
      |> succeed (Classinst ((class_eq, (dtco, arity)), ([], [(fun_eq, (idf_eqpred, inst_sortlookup))])), []);
  in
    trns
    |> gen_ensure_def [("eqinst", mk_eq_inst)] ("generating equality instance for " ^ quote dtco) idf_eqinst
  end;

fun invoke_appgen thy tabs (app as ((f, ty), ts)) trns =
  gen_invoke
    ((map (apsnd (fn (ag, _) => ag thy tabs)) o #appgens o #gens o CodegenData.get) thy)
    ("generating application " ^ f ^ "::" ^ (Sign.string_of_typ thy) ty
     ^ " " ^ enclose "(" ")" (commas (map (Sign.string_of_term thy) ts))) app trns;


(* expression generators *)

fun exprgen_sort thy tabs sort trns =
  trns
  |> fold_map (ensure_def_class thy tabs) (ClassPackage.syntactic_sort_of thy sort)
  |-> (fn sort => pair sort);

fun exprgen_type thy tabs (TVar _) trns =
      error "TVar encountered during code generation"
  | exprgen_type thy tabs (TFree (v, sort)) trns =
      trns
      |> exprgen_sort thy tabs sort
      |-> (fn sort => pair (IVarT (v |> unprefix "'", sort)))
  | exprgen_type thy tabs (Type ("fun", [t1, t2])) trns =
      trns
      |> exprgen_type thy tabs t1
      ||>> exprgen_type thy tabs t2
      |-> (fn (t1', t2') => pair (t1' `-> t2'))
  | exprgen_type thy tabs (Type (tyco, tys)) trns =
      trns
      |> ensure_def_tyco thy tabs tyco
      ||>> fold_map (exprgen_type thy tabs) tys
      |-> (fn (tyco, tys) => pair (tyco `%% tys));

fun exprgen_term thy tabs (Const (f, ty)) trns =
      trns
      |> invoke_appgen thy tabs ((f, ty), [])
      |-> (fn e => pair e)
  | exprgen_term thy tabs (Var ((v, i), ty)) trns =
      trns
      |> exprgen_type thy tabs ty
      |-> (fn ty => pair (IVarE (if i = 0 then v else v ^ "_" ^ string_of_int i, ty)))
  | exprgen_term thy tabs (Free (v, ty)) trns =
      trns
      |> exprgen_type thy tabs ty
      |-> (fn ty => pair (IVarE (v, ty)))
  | exprgen_term thy tabs (Abs (v, ty, t)) trns =
      trns
      |> exprgen_type thy tabs ty
      ||>> exprgen_term thy tabs (subst_bound (Free (v, ty), t))
      |-> (fn (ty, e) => pair ((v, ty) `|-> e))
  | exprgen_term thy tabs (t as t1 $ t2) trns =
      let
        val (t', ts) = strip_comb t
      in case t'
       of Const (f, ty) =>
            trns
            |> invoke_appgen thy tabs ((f, ty), ts)
            |-> (fn e => pair e)
        | _ =>
            trns
            |> exprgen_term thy tabs t'
            ||>> fold_map (exprgen_term thy tabs) ts
            |-> (fn (e, es) => pair (e `$$ es))
      end;


(* code generator auxiliary *)

fun mk_fun thy tabs eqs ty trns =
  let
    val sortctxt = ClassPackage.extract_sortctxt thy ty;
    fun mk_sortvar (v, sort) trns =
      trns
      |> exprgen_sort thy tabs sort
      |-> (fn sort => pair (unprefix "'" v, sort))
    fun mk_eq (args, rhs) trns =
      trns
      |> fold_map (exprgen_term thy tabs o devarify_term) args
      ||>> (exprgen_term thy tabs o devarify_term) rhs
      |-> (fn (args, rhs) => pair (map ipat_of_iexpr args, rhs))
  in
    trns
    |> fold_map mk_eq eqs
    ||>> exprgen_type thy tabs (devarify_type ty)
    ||>> fold_map mk_sortvar sortctxt
    |-> (fn ((eqs, ty), sortctxt) => pair (Fun (eqs, (sortctxt, ty))))
  end;

fun mk_lookup thy tabs (ClassPackage.Instance (inst as (cls, tyco), ls)) trns =
      trns
      |> ensure_def_class thy tabs cls
      ||>> ensure_def_inst thy tabs inst
      ||>> (fold_map o fold_map) (mk_lookup thy tabs) ls
      |-> (fn ((cls, i), ls) => pair (ClassPackage.Instance ((cls, i), ls)))
  | mk_lookup thy tabs (ClassPackage.Lookup (clss, (v, i))) trns =
      trns
      |> fold_map (ensure_def_class thy tabs) clss
      |-> (fn clss => pair (ClassPackage.Lookup (clss, (v |> unprefix "'", i))));

fun mk_itapp e [] = e
  | mk_itapp e lookup = IInst (e, lookup);

fun fix_nargs thy tabs gen (imin, imax) ((f, ty), ts) trns =
  let
    fun invoke ts trns =
      trns
      |> gen_invoke [("const application", gen)] ("generating application " ^ f ^ "::" ^ (Sign.string_of_typ thy) ty
        ^ " " ^ enclose "(" ")" (commas (map (Sign.string_of_term thy) ts)))
        ((f, ty), ts)
  in if length ts < imin then
    let
      val d = imin - length ts;
      val vs = Term.invent_names (add_term_names (Const (f, ty), [])) "x" d;
      val tys = Library.take (d, ((fst o strip_type) ty));
    in
      trns
      |> debug 10 (fn _ => "eta-expanding")
      |> fold_map (exprgen_type thy tabs) tys
      ||>> invoke (ts @ map2 (curry Free) vs tys)
      |-> (fn (tys, e) => succeed ((vs ~~ tys) `|--> e))
    end
  else if length ts > imax then
    trns
    |> debug 10 (fn _ => "splitting arguments (" ^ string_of_int imax ^ ", " ^ string_of_int (length ts) ^ ")")
    |> invoke  (Library.take (imax, ts))
    ||>> fold_map (exprgen_term thy tabs) (Library.drop (imax, ts))
    |-> succeed o mk_apps
  else
    trns
    |> debug 10 (fn _ => "keeping arguments")
    |> invoke ts
    |-> succeed
  end;

(* application generators *)

fun appgen_default thy tabs ((f, ty), ts) trns =
  let
    val _ = debug 5 (fn _ => "making application of " ^ quote f) ();
    val ty_def = Sign.the_const_constraint thy f;
  in
    trns
    |> ensure_def_const thy tabs (f, ty)
    ||>> (fold_map o fold_map) (mk_lookup thy tabs) (ClassPackage.extract_sortlookup thy (ty_def, ty))
    ||>> exprgen_type thy tabs ty
    ||>> fold_map (exprgen_term thy tabs) ts
    |-> (fn (((f, lookup), ty), es) =>
           succeed (mk_itapp (IConst (f, ty)) lookup `$$ es))
  end;

fun appgen_appconst thy tabs ((f, ty), ts) trns =
  case Symtab.lookup ((#appconst o #gens o CodegenData.get) thy) f
   of SOME (bounds, (ag, _)) =>
        trns
        |> fix_nargs thy tabs (ag thy tabs) bounds ((f, ty), ts)
    | NONE =>
        trns
        |> fail ("no constant in application table: " ^ quote f);

fun appgen_neg thy tabs (("neg", Type ("fun", [ty, _])), ts) trns =
  trns
  |> exprgen_term thy tabs (Const ("op >", ty --> ty --> Type ("bool", [])) $ Const ("0", ty))
  |-> succeed;

fun appgen_eq thy tabs (("op =", Type ("fun", [ty, _])), [t1, t2]) trns =
  trns
  |> invoke_eq (exprgen_type thy tabs) (ensure_def_eq thy tabs) ty
  |-> (fn false => error ("could not derive equality for " ^ Sign.string_of_typ thy ty)
        | true => fn trns => trns
  |> exprgen_term thy tabs t1
  ||>> exprgen_term thy tabs t2
  |-> (fn (e1, e2) => succeed (Fun_eq `$ e1 `$ e2)));

(* definition generators *)

fun defgen_tyco_fallback thy tabs tyco trns =
  if Symtab.fold (fn (_, { syntax_tyco, ... }) => fn b => b orelse Symtab.defined syntax_tyco tyco)
    ((#serialize_data o CodegenData.get) thy) false
  then
    trns
    |> debug 5 (fn _ => "trying defgen tyco fallback for " ^ quote tyco)
    |> succeed (Nop, [])
  else
    trns
    |> fail ("no code generation fallback for " ^ quote tyco)

fun defgen_const_fallback thy tabs c trns =
  if Symtab.fold (fn (_, { syntax_const, ... }) => fn b => b orelse Symtab.defined syntax_const c)
    ((#serialize_data o CodegenData.get) thy) false
  then
    trns
    |> debug 5 (fn _ => "trying defgen const fallback for " ^ quote c)
    |> succeed (Nop, [])
  else
    trns
    |> fail ("no code generation fallback for " ^ quote c)

fun defgen_defs thy (tabs as ((deftab, _), _)) c trns =
  case Symtab.lookup deftab c
   of SOME (ty, (args, rhs)) =>
        trns
        |> debug 5 (fn _ => "trying defgen def for " ^ quote c)
        |> mk_fun thy tabs [(args, rhs)] (devarify_type ty)
        |-> (fn def => succeed (def, []))
      | _ => trns |> fail ("no definition found for " ^ quote c);

fun defgen_clsdecl thy (tabs as (_, (insttab, _, _))) (cls : string) trns =
  case name_of_idf thy nsp_class cls
   of SOME cls =>
        let
          val memnames = ClassPackage.the_consts thy (cls : string);
          val memtypes = map (devarify_type o ClassPackage.get_const_sign thy "'a") memnames;
          val memctxt = map (ClassPackage.extract_sortctxt thy) memtypes;
          val memidfs = map (idf_of_name thy nsp_mem) memnames;
          fun mk_instname (tyco, thyname) = idf_of_name thy nsp_inst (InstNameMangler.get thy insttab (thyname, (cls, tyco)))
          val instnames = map mk_instname (ClassPackage.the_tycos thy cls);
        in
          trns
          |> debug 5 (fn _ => "trying defgen class declaration for " ^ quote cls)
          |> fold_map (ensure_def_class thy tabs) (ClassPackage.get_superclasses thy cls)
          ||>> fold_map (exprgen_type thy tabs) memtypes
          |-> (fn (supcls, memtypes) => succeed (Class (supcls, "a", memidfs ~~ (memctxt ~~ memtypes), []),
                 memidfs @ instnames))
        end
    | _ =>
        trns
        |> fail ("no class definition found for " ^ quote cls);

fun defgen_clsmem thy tabs m trns =
  case name_of_idf thy nsp_mem m
   of SOME m =>
        trns
        |> debug 5 (fn _ => "trying defgen class member for " ^ quote m)
        |> ensure_def_class thy tabs ((the o ClassPackage.lookup_const_class thy) m)
        |-> (fn cls => succeed (Classmember cls, []))
    | _ =>
        trns |> fail ("no class member found for " ^ quote m)

fun defgen_clsinst thy (tabs as (_, (insttab, _, _))) inst trns =
  case Option.map (InstNameMangler.rev thy insttab) (name_of_idf thy nsp_inst inst)
   of SOME (_, (cls, tyco)) =>
        let
          val arity = ClassPackage.get_arities thy [cls] tyco;
          val ms = map (fn m => (m, Sign.the_const_constraint thy m)) (ClassPackage.the_consts thy cls);
          val instmem_idfs = ClassPackage.get_inst_consts_sign thy (tyco, cls);
          val supclss = ClassPackage.get_superclasses thy cls;
          fun add_vars arity clsmems (trns as (_, modl)) =
            case get_def modl (idf_of_name thy nsp_class cls)
             of Class (_, _, members, _) => ((Term.invent_names
              (tvars_of_itypes ((map (snd o snd)) members)) "a" (length arity) ~~ arity, clsmems), trns)
          val ad_hoc_arity = map (fn (v, sort) => map_index (fn (i, _) => (ClassPackage.Lookup ([], (v, i)))) sort);
          (*! THIS IS ACTUALLY VERY AD-HOC... !*)
        in
          (trns
          |> debug 5 (fn _ => "trying defgen class instance for (" ^ quote cls ^ ", " ^ quote tyco ^ ")")
          |> (fold_map o fold_map) (ensure_def_class thy tabs) arity
          ||>> fold_map (ensure_def_const thy tabs) ms
          |-> (fn (arity, ms) => add_vars arity ms)
          ||>> ensure_def_class thy tabs cls
          ||>> ensure_def_tyco thy tabs tyco
          ||>> fold_map (fn supcls => ensure_def_inst thy tabs (supcls, tyco)) supclss
          ||>> fold_map (fn supcls => (fold_map o fold_map) (mk_lookup thy tabs)
                 (ClassPackage.extract_sortlookup thy
                   (Type (tyco, map_index (fn (i, _) => TVar (("'a", i), [])) (ClassPackage.get_arities thy [supcls] tyco)),
                    Type (tyco, map_index (fn (i, sort) => TFree (string_of_int i, sort)) arity)))) supclss
          ||>> fold_map (ensure_def_const thy tabs) instmem_idfs)
          |-> (fn ((((((arity, ms), cls), tyco), supinsts), supinstlookup), instmem_idfs) 
                : ((((((string * string list) list * string list) * string) * string)
                * string list) * ClassPackage.sortlookup list list list) * string list
                =>
                 succeed (Classinst ((cls, (tyco, arity)), (supclss ~~ (supinsts ~~ supinstlookup), ms ~~ map (rpair (ad_hoc_arity arity)) instmem_idfs)), [])) 
        end
    | _ =>
        trns |> fail ("no class instance found for " ^ quote inst);


(*    trns
    |> ensure_def_const thy tabs (f, ty)

    ||>> exprgen_type thy tabs ty
    ||>> fold_map (exprgen_term thy tabs) ts
    |-> (fn (((f, lookup), ty), es) =>
           succeed (mk_itapp (IConst (f, ty)) lookup `$$ es))*)


(* parametrized generators, for instantiation in HOL *)

fun appgen_let strip_abs thy tabs (f as ("Let", _), ts) trns =
      let
        fun dest_let (l as Const ("Let", _) $ t $ u) =
              (case strip_abs 1 u
               of ([p], u') => apfst (cons (p, t)) (dest_let u')
                | _ => ([], l))
          | dest_let t = ([], t);
        fun mk_let (l, r) trns =
          trns
          |> exprgen_term thy tabs l
          ||>> exprgen_term thy tabs r
          |-> (fn (l, r) => pair (r, ipat_of_iexpr l));
        fun gen_let ((f, ty), [t2, t3]) trns =
          let
            val (lets, body) = dest_let (Const (f, ty) $ t2 $ t3)
          in
            trns
            |> fold_map mk_let lets
            ||>> exprgen_term thy tabs body
            |-> (fn (lets, body) =>
                 succeed (Library.foldr (fn ((e, p), body) => ICase (e, [(p, body)])) (lets, body)))
          end;
      in
        trns
        |> fix_nargs thy tabs gen_let (2, 2) (f, ts)
      end
  | appgen_let strip_abs thy tabs ((f, _), _) trns =
      trns
      |> fail ("not a let: " ^ quote f);

fun appgen_split strip_abs thy tabs (f as ("split", _), ts) trns =
      let
        fun gen_split ((f, ty), [t2]) trns =
          let
            val ([p], body) = strip_abs 1 (Const (f, ty) $ t2)
          in
            trns
            |> exprgen_term thy tabs p
            ||>> exprgen_term thy tabs body
            |-> (fn (IVarE v, body) => succeed (IAbs (v, body)))
          end
      in
        trns
        |> fix_nargs thy tabs gen_split (1, 1) (f, ts)
      end
  | appgen_split strip_abs thy tabs ((f, _), _) trns =
      trns
      |> fail ("not a split: " ^ quote f);

fun appgen_number_of dest_binum mk_int_to_nat thy tabs (f as ("Numeral.number_of",
      Type ("fun", [_, Type ("IntDef.int", [])])), ts) trns =
      let
        fun gen_num (_, [bin]) trns =
          trns
          |> (succeed (IConst ((IntInf.toString o dest_binum) bin, Type_integer))
              handle TERM _
              => error ("not a number: " ^ Sign.string_of_term thy bin))
      in
        trns
        |> fix_nargs thy tabs gen_num (1, 1) (f, ts)
      end
  | appgen_number_of dest_binum mk_int_to_nat thy tabs (f as ("Numeral.number_of",
      Type ("fun", [_, Type ("nat", [])])), ts) trns =
      let
        fun gen_num (_, [bin]) trns =
          trns
          |> exprgen_term thy tabs (mk_int_to_nat bin)
          |-> succeed
      in
        trns
        |> fix_nargs thy tabs gen_num (1, 1) (f, ts)
      end
  | appgen_number_of dest_binum mk_int_to_nat thy tabs ((f, _), _) trns =
      trns
      |> fail ("not a number_of: " ^ quote f);

fun appgen_case get_case_const_data thy tabs ((f, ty), ts) trns =
  let
    fun cg_case_d gen_names dty (((cname, i), ty), t) trns =
      let
        val vs = gen_names i;
        val tys = Library.take (i, (fst o strip_type) ty);
        val frees = map2 (curry Free) vs tys;
        val t' = Envir.beta_norm (list_comb (t, frees));
      in
        trns
        |> exprgen_term thy tabs (list_comb (Const (cname, tys ---> dty), frees))
        ||>> exprgen_term thy tabs t'
        |-> (fn (ep, e) => pair (ipat_of_iexpr ep, e))
      end;
    fun cg_case dty cs (_, ts) trns =
      let
        val (ts', t) = split_last ts
        fun gen_names i =
          variantlist (replicate i "x", foldr add_term_names
           (map (fst o fst o dest_Var) (foldr add_term_vars [] ts)) ts)
      in
        trns
        |> exprgen_term thy tabs t
        ||>> fold_map (cg_case_d gen_names dty) (cs ~~ ts')
        |-> (fn (t, ds) => succeed (ICase (t, ds)))
      end;
  in 
    case get_case_const_data thy f
     of NONE =>
          trns
          |> fail ("not a case constant: " ^ quote f)
      | SOME cs =>
          let
            val (tys, dty) = (split_last o fst o strip_type) ty;
          in
            trns
            |> fix_nargs thy tabs (cg_case dty (cs ~~ tys))
                 (length cs + 1, length cs + 1) ((f, ty), ts)
          end
  end;

fun defgen_datatype get_datatype get_datacons thy (tabs as (_, (_, _, dtcontab))) dtco trns =
  case name_of_idf thy nsp_tyco dtco
   of SOME dtco =>
        (case get_datatype thy dtco
         of SOME (vars, cos) =>
              let
                val cotys = map (the o get_datacons thy o rpair dtco) cos;
                val coidfs = map (fn co => (DatatypeconsNameMangler.get thy dtcontab (co, dtco)) |>
                  idf_of_name thy nsp_dtcon) cos;
              in
                trns
                |> debug 5 (fn _ => "trying defgen datatype for " ^ quote dtco)
                |> fold_map (exprgen_sort thy tabs) (map snd vars)
                ||>> (fold_map o fold_map) (exprgen_type thy tabs o devarify_type) cotys
                |-> (fn (sorts, tys) => succeed (Datatype
                     (map2 (fn (v, _) => fn sort => (unprefix "'" v, sort)) vars sorts, coidfs ~~ tys, []),
                     coidfs))
              end
          | NONE =>
              trns
              |> fail ("no datatype found for " ^ quote dtco))
    | NONE =>
        trns
        |> fail ("not a type constructor: " ^ quote dtco)

fun defgen_datacons get_datacons thy (tabs as (_, (_, _, dtcontab))) co trns =
  case Option.map (DatatypeconsNameMangler.rev thy dtcontab) (name_of_idf thy nsp_dtcon co)
   of SOME (co, dtco) =>
        trns
        |> debug 5 (fn _ => "trying defgen datatype constructor for " ^ quote co)
        |> ensure_def_tyco thy tabs dtco
        |-> (fn tyco => succeed (Datatypecons tyco, []))
    | _ =>
        trns
        |> fail ("not a datatype constructor: " ^ quote co);

fun defgen_recfun get_equations thy tabs c trns =
  case recconst_of_idf thy tabs c
   of SOME (c, ty) =>
        let
          val (eqs, ty) = get_equations thy (c, ty);
        in
          case eqs
           of (_::_) =>
                trns
                |> debug 5 (fn _ => "trying defgen recfun for " ^ quote c)
                |> mk_fun thy tabs eqs (devarify_type ty)
                |-> (fn def => succeed (def, []))
            | _ =>
                trns
                |> fail ("no recursive definition found for " ^ quote c)
        end
    | NONE =>
        trns
        |> fail ("not a constant: " ^ quote c);



(** theory interface **)

fun mk_tabs thy =
  let
    fun extract_defs thy =
      let
        fun dest t =
          let
            val (lhs, rhs) = Logic.dest_equals t;
            val (c, args) = strip_comb lhs;
            val (s, T) = dest_Const c
          in if forall is_Var args then SOME (s, (T, (args, rhs))) else NONE
          end handle TERM _ => NONE;
        fun prep_def def = (case Codegen.preprocess thy [def] of
          [def'] => prop_of def' | _ => error "mk_auxtab: bad preprocessor");
        fun add_def (name, t) defs = (case dest t of
            NONE => defs
          | SOME _ => (case (dest o prep_def oo Thm.get_axiom) thy name of
              NONE => defs
            | SOME (s, (T, (args, rhs))) => Symtab.update
                (s, (T, (split_last (args @ [rhs]))) ::
                if_none (Symtab.lookup defs s) []) defs))
      in
        Symtab.empty
        |> fold (Symtab.fold add_def) (map
             (snd o #axioms o Theory.rep_theory) (thy :: Theory.ancestors_of thy))
      end;
    fun mk_insttab thy =
      InstNameMangler.empty
      |> Symtab.fold_map
          (fn (cls, (_, clsinsts)) => fold_map
            (fn (tyco, thyname) => InstNameMangler.declare thy (thyname, (cls, tyco))) clsinsts)
                 (ClassPackage.get_classtab thy)
      |-> (fn _ => I);
    fun mk_overltabs thy defs =
      (Symtab.empty, ConstNameMangler.empty)
      |> Symtab.fold
          (fn (c, [_]) => I
            | ("0", _) => I
            | (c, tytab) =>
                (fn (overltab1, overltab2) => (
                  overltab1
                  |> Symtab.update_new (c, (Sign.the_const_constraint thy c, map fst tytab)),
                  overltab2
                  |> fold (fn (ty, _) => ConstNameMangler.declare thy (idf_of_name thy nsp_overl c, (Sign.the_const_constraint thy c, ty)) #> snd) tytab
                ))) defs;
    fun mk_dtcontab thy =
      DatatypeconsNameMangler.empty
      |> fold_map
          (fn (_, co_dtco) => DatatypeconsNameMangler.declare_multi thy co_dtco)
            (fold (fn (co, dtco) =>
              let
                val key = ((NameSpace.drop_base o NameSpace.drop_base) co, NameSpace.base co)
              in AList.default (op =) (key, []) #> AList.map_entry (op =) key (cons (co, dtco)) end
            ) (get_all_datatype_cons thy) [])
      |-> (fn _ => I);
    fun mk_deftab thy defs overltab =
      Symtab.empty
      |> Symtab.fold
          (fn (c, [ty_cdef]) =>
                Symtab.update_new (idf_of_name thy nsp_const c, ty_cdef)
            | ("0", _) => I
            | (c, cdefs) => fold (fn (ty, cdef) =>
                let
                  val c' = ConstNameMangler.get thy overltab
                    (idf_of_name thy nsp_overl c, (Sign.the_const_constraint thy c, ty))
                in Symtab.update_new (c', (ty, cdef)) end) cdefs) defs;
    fun mk_clsmemtab thy =
      Symtab.empty
      |> Symtab.fold
          (fn (class, (clsmems, _)) => fold
            (fn clsmem => Symtab.update (clsmem, class)) clsmems)
              (ClassPackage.get_classtab thy);
    val defs = extract_defs thy;
    val insttab = mk_insttab thy;
    val overltabs = mk_overltabs thy defs;
    val dtcontab = mk_dtcontab thy;
    val deftab = mk_deftab thy defs (snd overltabs);
    val clsmemtab = mk_clsmemtab thy;
  in ((deftab, clsmemtab), (insttab, overltabs, dtcontab)) end;

fun check_for_serializer serial_name serialize_data =
  if Symtab.defined serialize_data serial_name
  then serialize_data
  else error ("unknown code serializer: " ^ quote serial_name);

fun map_module f =
  map_codegen_data (fn (modl, gens, lookups, serialize_data, logic_data) =>
    (f modl, gens, lookups, serialize_data, logic_data));

fun expand_module defs gen thy =
  (#modl o CodegenData.get) thy
  |> start_transact (gen thy defs)
  |-> (fn x:'a => fn modl => (x, map_module (K modl) thy));

fun rename_inconsistent thy =
  let
    fun get_inconsistent thyname =
      let
        val thy = theory thyname;
        fun own_tables get =
          (get thy)
          |> fold (Symtab.fold (Symtab.remove (K true)) o get) (Theory.parents_of thy)
          |> Symtab.keys;
        val names = own_tables (#2 o #types o Type.rep_tsig o Sign.tsig_of)
          @ own_tables (#2 o #declarations o Consts.dest o #consts o Sign.rep_sg);
        fun diff names =
          fold (fn name =>
            if is_prefix (op =) (NameSpace.unpack thyname) (NameSpace.unpack name)
            then I
            else cons (name, NameSpace.append thyname (NameSpace.base name))) names [];
      in diff names end;
    val inconsistent = map get_inconsistent (ThyInfo.names ()) |> Library.flat;
    fun add (src, dst) thy =
      if (is_some oo Symtab.lookup o fst o #alias o #logic_data o CodegenData.get) thy src
      then (warning ("code generator alias already defined for " ^ quote src ^ ", will not overwrite"); thy)
      else add_alias (src, dst) thy
  in fold add inconsistent thy end;



(** target languages **)

(* primitive definitions *)

fun gen_add_prim prep_name prep_primdef raw_name (target, raw_primdef) deps thy =
  let
    val _ = if Symtab.defined ((#serialize_data o CodegenData.get) thy) target
      then () else error ("unknown target language: " ^ quote target);
    val tabs = mk_tabs thy;
    val name = prep_name thy tabs raw_name;
    val primdef = prep_primdef raw_primdef;
  in
    thy
    |> map_module (CodegenThingol.add_prim name (target, primdef) deps)
  end;

val add_prim_i = gen_add_prim ((K o K) I) I;
val add_prim_class = gen_add_prim
  (fn thy => K (idf_of_name thy nsp_class o Sign.intern_class thy))
  (Pretty.str o newline_correct o Symbol.strip_blanks);
val add_prim_tyco = gen_add_prim
  (fn thy => K (idf_of_name thy nsp_tyco o Sign.intern_type thy))
  (Pretty.str o newline_correct o Symbol.strip_blanks);
val add_prim_const = gen_add_prim
  (fn thy => fn tabs => idf_of_const thy tabs o
    (fn (c, ty) => (Sign.intern_const thy c, Sign.read_typ (thy, K NONE) ty)))
  (Pretty.str o newline_correct o Symbol.strip_blanks);

val ensure_prim = (map_module o CodegenThingol.ensure_prim);

(* syntax *)

fun gen_add_syntax_tyco prep_tyco prep_mfx prep_primname prep_primdef serial_name ((raw_tyco, raw_mfx, fixity), primdef) thy =
  let
    val tyco = prep_tyco thy raw_tyco;
    val _ = if member (op =) prims tyco
      then error ("attempted to re-define primitive " ^ quote tyco)
      else ()
    fun add_primdef NONE = I
      | add_primdef (SOME (name, (def, deps))) =
          CodegenSerializer.add_prim (prep_primname thy tyco name, (prep_primdef def, deps))
  in
    thy
    |> ensure_prim (idf_of_name thy nsp_tyco tyco)
    |> prep_mfx raw_mfx
    |-> (fn mfx => map_codegen_data
      (fn (modl, gens, lookups, serialize_data, logic_data) =>
         (modl, gens, lookups,
          serialize_data |> check_for_serializer serial_name |> Symtab.map_entry serial_name
            (map_serialize_data
              (fn (primitives, syntax_tyco, syntax_const) =>
               (primitives |> add_primdef primdef,
                syntax_tyco |> Symtab.update_new
                  (idf_of_name thy nsp_tyco tyco,
                   (((Codegen.num_args_of mfx, fixity), Codegen.fillin_mixfix mfx), stamp ())),
                syntax_const))),
          logic_data)))
  end;

val add_syntax_tyco_i = gen_add_syntax_tyco (K I) pair ((K o K) I) I;
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
        fun generate thy defs = fold_map (exprgen_type thy defs o devarify_type)
          (Codegen.quotes_of proto_mfx);
      in
        thy
        |> expand_module (mk_tabs thy) generate
        |-> (fn tys => pair (Codegen.replace_quotes tys proto_mfx))
      end;
  in
    gen_add_syntax_tyco Sign.intern_type
      prep_mfx mk_name (newline_correct o Symbol.strip_blanks)
  end;

fun gen_add_syntax_const prep_const prep_mfx prep_primname prep_primdef serial_name ((raw_c, raw_mfx, fixity), primdef) thy =
  let
    val (c, ty) = prep_const thy raw_c;
    val tabs = mk_tabs thy;
    val _ = if member (op =) prims c
      then error ("attempted to re-define primitive " ^ quote c)
      else ()
    fun add_primdef NONE = I
      | add_primdef (SOME (name, (def, deps))) =
          CodegenSerializer.add_prim (prep_primname thy c name, (prep_primdef def, deps))
  in
    thy
    |> ensure_prim (idf_of_const thy tabs (c, ty))
    |> prep_mfx raw_mfx
    |-> (fn mfx => map_codegen_data
      (fn (modl, gens, lookups, serialize_data, logic_data) =>
         (modl, gens, lookups,
          serialize_data |> check_for_serializer serial_name |> Symtab.map_entry serial_name
            (map_serialize_data
              (fn (primitives, syntax_tyco, syntax_const) =>
               (primitives |> add_primdef primdef,
                syntax_tyco,
                syntax_const |> Symtab.update_new
                  (idf_of_const thy tabs (c, ty),
                    (((Codegen.num_args_of mfx, fixity), Codegen.fillin_mixfix mfx), stamp ()))))),
          logic_data)))
  end;

val add_syntax_const_i = gen_add_syntax_const (K I) pair ((K o K) I) I;
val add_syntax_const =
  let
    fun prep_const thy (raw_c, raw_ty) =
      let
        val c = Sign.intern_const thy raw_c;
        val ty =
          raw_ty
          |> Option.map (Sign.read_tyname thy)
          |> the_default (Sign.the_const_constraint thy c);
      in (c, ty) end;
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
        fun generate thy defs = fold_map (exprgen_term thy defs o devarify_term)
          (Codegen.quotes_of proto_mfx);
      in
        thy
        |> expand_module (mk_tabs thy) generate
        |-> (fn es => pair (Codegen.replace_quotes es proto_mfx))
      end;
  in
    gen_add_syntax_const prep_const prep_mfx mk_name (newline_correct o Symbol.strip_blanks)
  end;



(** code generation **)

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
    val tabs = mk_tabs thy;
    val consts' = map (mk_const thy) consts;
    fun generate thy tabs = fold_map (ensure_def_const thy tabs) consts'
  in
    thy
    |> expand_module tabs generate
    |-> (fn consts => pair consts)
  end;

fun serialize_code serial_name filename consts thy =
  let
    val serialize_data =
      thy
      |> CodegenData.get
      |> #serialize_data
      |> check_for_serializer serial_name
      |> (fn data => (the oo Symtab.lookup) data serial_name)
    val serializer' = (get_serializer thy serial_name) serial_name
      ((Option.map fst oo Symtab.lookup o #syntax_tyco) serialize_data)
      ((Option.map fst oo Symtab.lookup o #syntax_const) serialize_data)
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
    |-> (fn code => ((use_code o Pretty.output) code; I))
  end;



(** toplevel interface **)

local

structure P = OuterParse
and K = OuterKeyword

in

val (classK, generateK, serializeK, syntax_tycoK, syntax_constK, aliasK) =
  ("code_class", "code_generate", "code_serialize", "code_syntax_tyco", "code_syntax_const", "code_alias");
val (constantsK, definedK, dependingK) =
  ("constants", "defined_by", "depending_on");

val classP =
  OuterSyntax.command classK "codegen data for classes" K.thy_decl (
    P.xname
    -- ((P.$$$ "\\<Rightarrow>" || P.$$$ "=>") |-- (P.list1 P.name))
    -- (Scan.optional ((P.$$$ "\\<Rightarrow>" || P.$$$ "=>") |-- (P.list1 P.name)) [])
    >> (fn ((name, tycos), consts) => (Toplevel.theory (ClassPackage.add_classentry name consts tycos)))
  )

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
         P.$$$ constantsK
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
    P.name
    -- Scan.repeat1 (
         P.xname -- (P.$$$ "(" |-- P.string --| P.$$$ ")")
         -- CodegenSerializer.parse_fixity
         -- Scan.option (
              P.$$$ definedK
              |-- Scan.option (P.$$$ "(" |-- P.string --| P.$$$ ")")
              -- (P.text -- Scan.optional (P.$$$ dependingK |-- P.list1 P.string) [])
            )
       )
    >> (fn (serial_name, xs) =>
          (Toplevel.theory oo fold)
            (fn (((tyco, raw_mfx), fixity), raw_def) =>
              add_syntax_tyco serial_name ((tyco, raw_mfx, fixity), raw_def)) xs)
  );

val syntax_constP =
  OuterSyntax.command syntax_constK "define code syntax for constant" K.thy_decl (
    P.name
    -- Scan.repeat1 (
         (P.xname -- Scan.option (P.$$$ "::" |-- P.typ)) -- (P.$$$ "(" |-- P.string --| P.$$$ ")")
         -- CodegenSerializer.parse_fixity
         -- Scan.option (
              P.$$$ definedK
              |-- Scan.option (P.$$$ "(" |-- P.string --| P.$$$ ")")
              -- (P.text -- Scan.optional (P.$$$ dependingK |-- P.list1 P.string) [])
            )
       )
    >> (fn (serial_name, xs) =>
          (Toplevel.theory oo fold)
            (fn (((c, raw_mfx), fixity), raw_def) =>
              add_syntax_const serial_name ((c, raw_mfx, fixity), raw_def)) xs)
  );

val _ = OuterSyntax.add_parsers [classP, generateP, serializeP, aliasP, syntax_tycoP, syntax_constP];
val _ = OuterSyntax.add_keywords ["\\<Rightarrow>", "=>", constantsK, definedK, dependingK];



(** setup **)

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
    add_appgen ("default", appgen_default),
    add_appgen ("appconst", appgen_appconst),
    add_appconst_i ("neg", ((0, 0), appgen_neg)),
    add_appconst_i ("op =", ((2, 2), appgen_eq)),
    add_defgen ("clsdecl", defgen_clsdecl),
    add_defgen ("tyco_fallback", defgen_tyco_fallback),
    add_defgen ("const_fallback", defgen_const_fallback),
    add_defgen ("defs", defgen_defs),
    add_defgen ("clsmem", defgen_clsmem),
    add_defgen ("clsinst", defgen_clsinst),
    add_alias ("op -->", "HOL.op_implies"),
    add_alias ("op +", "HOL.op_add"),
    add_alias ("op -", "HOL.op_minus"),
    add_alias ("op *", "HOL.op_times"),
    add_alias ("op <=", "Orderings.op_le"),
    add_alias ("op <", "Orderings.op_lt"),
    add_alias ("List.op @", "List.append"),
    add_alias ("List.op mem", "List.member"),
    add_alias ("Divides.op div", "Divides.div"),
    add_alias ("Divides.op dvd", "Divides.dvd"),
    add_alias ("Divides.op mod", "Divides.mod"),
    add_lookup_tyco ("bool", type_bool),
    add_lookup_tyco ("*", type_pair),
    add_lookup_tyco ("IntDef.int", type_integer),
    add_lookup_tyco ("List.list", type_list),
    add_lookup_const (("True", bool), Cons_true),
    add_lookup_const (("False", bool), Cons_false),
    add_lookup_const (("Not", bool --> bool), Fun_not),
    add_lookup_const (("op &", bool --> bool --> bool), Fun_and),
    add_lookup_const (("op |", bool --> bool --> bool), Fun_or),
    add_lookup_const (("HOL.If", bool --> A --> A --> A), Fun_if),
    add_lookup_const (("Pair", A --> B --> pair A B), Cons_pair),
    add_lookup_const (("fst", pair A B --> A), Fun_fst),
    add_lookup_const (("snd", pair A B --> B), Fun_snd),
    add_lookup_const (("List.list.Cons", A --> list A --> list A), Cons_cons),
    add_lookup_const (("List.list.Nil", list A), Cons_nil),
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
    add_lookup_const (("Wellfounded_Recursion.wfrec", ((A --> B) --> A --> B) --> A --> B), Fun_wfrec)
  ] end;

(* "op /" ??? *)

end; (* local *)

end; (* struct *)
