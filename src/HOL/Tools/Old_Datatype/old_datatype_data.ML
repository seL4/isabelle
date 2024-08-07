(*  Title:      HOL/Tools/Old_Datatype/old_datatype_data.ML
    Author:     Stefan Berghofer, TU Muenchen

Datatype package bookkeeping.
*)

signature OLD_DATATYPE_DATA =
sig
  include OLD_DATATYPE_COMMON

  val get_all : theory -> info Symtab.table
  val get_info : theory -> string -> info option
  val the_info : theory -> string -> info
  val info_of_constr : theory -> string * typ -> info option
  val info_of_constr_permissive : theory -> string * typ -> info option
  val info_of_case : theory -> string -> info option
  val register: (string * info) list -> theory -> theory
  val the_spec : theory -> string -> (string * sort) list * (string * typ list) list
  val the_descr : theory -> string list ->
    descr * (string * sort) list * string list * string *
    (string list * string list) * (typ list * typ list)
  val all_distincts : theory -> typ list -> thm list list
  val get_constrs : theory -> string -> (string * typ) list option
  val mk_case_names_induct: descr -> attribute
  val mk_case_names_exhausts: descr -> string list -> attribute list
  val interpretation : (config -> string list -> theory -> theory) -> theory -> theory
  val interpretation_data : config * string list -> theory -> theory
end;

structure Old_Datatype_Data: OLD_DATATYPE_DATA =
struct

(** theory data **)

(* data management *)

structure Data = Theory_Data
(
  type T =
    {types: Old_Datatype_Aux.info Symtab.table,
     constrs: (string * Old_Datatype_Aux.info) list Symtab.table,
     cases: Old_Datatype_Aux.info Symtab.table};

  val empty =
    {types = Symtab.empty, constrs = Symtab.empty, cases = Symtab.empty};
  fun merge
    ({types = types1, constrs = constrs1, cases = cases1},
     {types = types2, constrs = constrs2, cases = cases2}) : T =
    {types = Symtab.merge (K true) (types1, types2),
     constrs = Symtab.join (K (AList.merge (op =) (K true))) (constrs1, constrs2),
     cases = Symtab.merge (K true) (cases1, cases2)};
);

val get_all = #types o Data.get;
val get_info = Symtab.lookup o get_all;

fun the_info thy name =
  (case get_info thy name of
    SOME info => info
  | NONE => error ("Unknown old-style datatype " ^ quote name));

fun info_of_constr thy (c, T) =
  let
    val tab = Symtab.lookup_list (#constrs (Data.get thy)) c;
  in
    try (dest_Type_name o body_type) T
    |> Option.mapPartial (AList.lookup (op =) tab)
  end;

fun info_of_constr_permissive thy (c, T) =
  let
    val tab = Symtab.lookup_list (#constrs (Data.get thy)) c;
    val default = if null tab then NONE else SOME (snd (List.last tab));
    (*conservative wrt. overloaded constructors*)
  in
    (case try (dest_Type_name o body_type) T of
      NONE => default
    | SOME tyco =>
        (case AList.lookup (op =) tab tyco of
          NONE => default (*permissive*)
        | SOME info => SOME info))
  end;

val info_of_case = Symtab.lookup o #cases o Data.get;

fun ctrs_of_exhaust exhaust =
  Logic.strip_imp_prems (Thm.prop_of exhaust) |>
  map (head_of o snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o the_single
    o Logic.strip_assums_hyp);

fun case_of_case_rewrite case_rewrite =
  head_of (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of case_rewrite))));

fun ctr_sugar_of_info ({exhaust, nchotomy, inject, distinct, case_rewrites, case_cong,
    case_cong_weak, split, split_asm, ...} : Old_Datatype_Aux.info) =
  let val ctrs as ctr1 :: _ = ctrs_of_exhaust exhaust in
    {kind = Ctr_Sugar.Datatype,
     T = body_type (fastype_of ctr1),
     ctrs = ctrs,
     casex = case_of_case_rewrite (hd case_rewrites),
     discs = [],
     selss = [],
     exhaust = exhaust,
     nchotomy = nchotomy,
     injects = inject,
     distincts = distinct,
     case_thms = case_rewrites,
     case_cong = case_cong,
     case_cong_weak = case_cong_weak,
     case_distribs = [],
     split = split,
     split_asm = split_asm,
     disc_defs = [],
     disc_thmss = [],
     discIs = [],
     disc_eq_cases = [],
     sel_defs = [],
     sel_thmss = [],
     distinct_discsss = [],
     exhaust_discs = [],
     exhaust_sels = [],
     collapses = [],
     expands = [],
     split_sels = [],
     split_sel_asms = [],
     case_eq_ifs = []}
  end;

fun register dt_infos =
  Data.map (fn {types, constrs, cases} =>
    {types = types |> fold Symtab.update dt_infos,
     constrs = constrs |> fold (fn (constr, dtname_info) =>
         Symtab.map_default (constr, []) (cons dtname_info))
       (maps (fn (dtname, info as {descr, index, ...}) =>
          map (rpair (dtname, info) o fst) (#3 (the (AList.lookup op = descr index)))) dt_infos),
     cases = cases |> fold Symtab.update
       (map (fn (_, info as {case_name, ...}) => (case_name, info)) dt_infos)}) #>
  fold (Ctr_Sugar.default_register_ctr_sugar_global (K true) o ctr_sugar_of_info o snd) dt_infos;


(* complex queries *)

fun the_spec thy dtco =
  let
    val {descr, index, ...} = the_info thy dtco;
    val (_, dtys, raw_cos) = the (AList.lookup (op =) descr index);
    val args = map Old_Datatype_Aux.dest_DtTFree dtys;
    val cos = map (fn (co, tys) => (co, map (Old_Datatype_Aux.typ_of_dtyp descr) tys)) raw_cos;
  in (args, cos) end;

fun the_descr thy (raw_tycos as raw_tyco :: _) =
  let
    val info = the_info thy raw_tyco;
    val descr = #descr info;

    val (_, dtys, _) = the (AList.lookup (op =) descr (#index info));
    val vs = map Old_Datatype_Aux.dest_DtTFree dtys;

    fun is_DtTFree (Old_Datatype_Aux.DtTFree _) = true
      | is_DtTFree _ = false;
    val k = find_index (fn (_, (_, dTs, _)) => not (forall is_DtTFree dTs)) descr;
    val protoTs as (dataTs, _) =
      chop k descr
      |> (apply2 o map)
        (fn (_, (tyco, dTs, _)) => (tyco, map (Old_Datatype_Aux.typ_of_dtyp descr) dTs));

    val tycos = map fst dataTs;
    val _ =
      if eq_set (op =) (tycos, raw_tycos) then ()
      else
        error ("Type constructors " ^ commas_quote raw_tycos ^
          " do not belong exhaustively to one mutually recursive old-style datatype");

    val (Ts, Us) = apply2 (map Type) protoTs;

    val names = map Long_Name.base_name tycos;
    val (auxnames, _) =
      Name.make_context names
      |> fold_map (Name.variant o Old_Datatype_Aux.name_of_typ) Us;
    val prefix = space_implode "_" names;

  in (descr, vs, tycos, prefix, (names, auxnames), (Ts, Us)) end;

fun all_distincts thy Ts =
  let
    fun add_tycos T =
      if is_Type T
      then insert (op =) (dest_Type_name T) #> fold add_tycos (dest_Type_args T) else I;
    val tycos = fold add_tycos Ts [];
  in map_filter (Option.map #distinct o get_info thy) tycos end;

fun get_constrs thy dtco =
  (case try (the_spec thy) dtco of
    SOME (args, cos) =>
      let
        fun subst (v, sort) = TVar ((v, 0), sort);
        fun subst_ty (TFree v) = subst v
          | subst_ty ty = ty;
        val dty = Type (dtco, map subst args);
        fun mk_co (co, tys) = (co, map (Term.map_atyps subst_ty) tys ---> dty);
      in SOME (map mk_co cos) end
  | NONE => NONE);



(** various auxiliary **)

(* case names *)

local

fun dt_recs (Old_Datatype_Aux.DtTFree _) = []
  | dt_recs (Old_Datatype_Aux.DtType (_, dts)) = maps dt_recs dts
  | dt_recs (Old_Datatype_Aux.DtRec i) = [i];

fun dt_cases (descr: Old_Datatype_Aux.descr) (_, args, constrs) =
  let
    fun the_bname i = Long_Name.base_name (#1 (the (AList.lookup (op =) descr i)));
    val bnames = map the_bname (distinct (op =) (maps dt_recs args));
  in map (fn (c, _) => space_implode "_" (Long_Name.base_name c :: bnames)) constrs end;

fun induct_cases descr =
  Old_Datatype_Prop.indexify_names (maps (dt_cases descr) (map #2 descr));

fun exhaust_cases descr i = dt_cases descr (the (AList.lookup (op =) descr i));

in

fun mk_case_names_induct descr = Rule_Cases.case_names (induct_cases descr);

fun mk_case_names_exhausts descr new =
  map (Rule_Cases.case_names o exhaust_cases descr o #1)
    (filter (fn ((_, (name, _, _))) => member (op =) new name) descr);

end;



(** abstract theory extensions relative to a datatype characterisation **)

structure Old_Datatype_Plugin = Plugin(type T = Old_Datatype_Aux.config * string list);

val old_datatype_plugin = Plugin_Name.declare_setup \<^binding>\<open>old_datatype\<close>;

fun interpretation f =
  Old_Datatype_Plugin.interpretation old_datatype_plugin
    (fn (config, type_names as name :: _) =>
      Local_Theory.background_theory (fn thy =>
        thy
        |> Sign.root_path
        |> Sign.add_path (Long_Name.qualifier name)
        |> f config type_names
        |> Sign.restore_naming thy));

val interpretation_data = Named_Target.theory_map o Old_Datatype_Plugin.data_default;


open Old_Datatype_Aux;

end;
