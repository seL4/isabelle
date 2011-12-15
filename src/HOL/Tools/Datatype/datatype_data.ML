(*  Title:      HOL/Tools/Datatype/datatype_data.ML
    Author:     Stefan Berghofer, TU Muenchen

Datatype package bookkeeping.
*)

signature DATATYPE_DATA =
sig
  include DATATYPE_COMMON
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
  val make_case :  Proof.context -> Datatype_Case.config -> string list -> term ->
    (term * term) list -> term
  val strip_case : Proof.context -> bool -> term -> (term * (term * term) list) option
  val add_case_tr' : string list -> theory -> theory
  val setup: theory -> theory
end;

structure Datatype_Data: DATATYPE_DATA =
struct

(** theory data **)

(* data management *)

structure Data = Theory_Data
(
  type T =
    {types: Datatype_Aux.info Symtab.table,
     constrs: (string * Datatype_Aux.info) list Symtab.table,
     cases: Datatype_Aux.info Symtab.table};

  val empty =
    {types = Symtab.empty, constrs = Symtab.empty, cases = Symtab.empty};
  val extend = I;
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
  | NONE => error ("Unknown datatype " ^ quote name));

fun info_of_constr thy (c, T) =
  let
    val tab = Symtab.lookup_list (#constrs (Data.get thy)) c;
  in
    (case body_type T of
      Type (tyco, _) => AList.lookup (op =) tab tyco
    | _ => NONE)
  end;

fun info_of_constr_permissive thy (c, T) =
  let
    val tab = Symtab.lookup_list (#constrs (Data.get thy)) c;
    val hint = (case body_type T of Type (tyco, _) => SOME tyco | _ => NONE);
    val default = if null tab then NONE else SOME (snd (List.last tab));
    (*conservative wrt. overloaded constructors*)
  in
    (case hint of
      NONE => default
    | SOME tyco =>
        (case AList.lookup (op =) tab tyco of
          NONE => default (*permissive*)
        | SOME info => SOME info))
  end;

val info_of_case = Symtab.lookup o #cases o Data.get;

fun register (dt_infos : (string * Datatype_Aux.info) list) =
  Data.map (fn {types, constrs, cases} =>
    {types = types |> fold Symtab.update dt_infos,
     constrs = constrs |> fold (fn (constr, dtname_info) =>
         Symtab.map_default (constr, []) (cons dtname_info))
       (maps (fn (dtname, info as {descr, index, ...}) =>
          map (rpair (dtname, info) o fst)
            (#3 (the (AList.lookup op = descr index)))) dt_infos),
     cases = cases |> fold Symtab.update
       (map (fn (_, info as {case_name, ...}) => (case_name, info)) dt_infos)});


(* complex queries *)

fun the_spec thy dtco =
  let
    val {descr, index, ...} = the_info thy dtco;
    val (_, dtys, raw_cos) = the (AList.lookup (op =) descr index);
    val args = map Datatype_Aux.dest_DtTFree dtys;
    val cos = map (fn (co, tys) => (co, map (Datatype_Aux.typ_of_dtyp descr) tys)) raw_cos;
  in (args, cos) end;

fun the_descr thy (raw_tycos as raw_tyco :: _) =
  let
    val info = the_info thy raw_tyco;
    val descr = #descr info;

    val (_, dtys, _) = the (AList.lookup (op =) descr (#index info));
    val vs = map Datatype_Aux.dest_DtTFree dtys;

    fun is_DtTFree (Datatype_Aux.DtTFree _) = true
      | is_DtTFree _ = false;
    val k = find_index (fn (_, (_, dTs, _)) => not (forall is_DtTFree dTs)) descr;
    val protoTs as (dataTs, _) =
      chop k descr
      |> (pairself o map)
        (fn (_, (tyco, dTs, _)) => (tyco, map (Datatype_Aux.typ_of_dtyp descr) dTs));

    val tycos = map fst dataTs;
    val _ =
      if eq_set (op =) (tycos, raw_tycos) then ()
      else
        error ("Type constructors " ^ commas_quote raw_tycos ^
          " do not belong exhaustively to one mutual recursive datatype");

    val (Ts, Us) = (pairself o map) Type protoTs;

    val names = map Long_Name.base_name tycos;
    val (auxnames, _) =
      Name.make_context names
      |> fold_map (Name.variant o Datatype_Aux.name_of_typ) Us;
    val prefix = space_implode "_" names;

  in (descr, vs, tycos, prefix, (names, auxnames), (Ts, Us)) end;

fun all_distincts thy Ts =
  let
    fun add_tycos (Type (tyco, Ts)) = insert (op =) tyco #> fold add_tycos Ts
      | add_tycos _ = I;
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

fun dt_recs (Datatype_Aux.DtTFree _) = []
  | dt_recs (Datatype_Aux.DtType (_, dts)) = maps dt_recs dts
  | dt_recs (Datatype_Aux.DtRec i) = [i];

fun dt_cases (descr: Datatype_Aux.descr) (_, args, constrs) =
  let
    fun the_bname i = Long_Name.base_name (#1 (the (AList.lookup (op =) descr i)));
    val bnames = map the_bname (distinct (op =) (maps dt_recs args));
  in map (fn (c, _) => space_implode "_" (Long_Name.base_name c :: bnames)) constrs end;

fun induct_cases descr =
  Datatype_Prop.indexify_names (maps (dt_cases descr) (map #2 descr));

fun exhaust_cases descr i = dt_cases descr (the (AList.lookup (op =) descr i));

in

fun mk_case_names_induct descr = Rule_Cases.case_names (induct_cases descr);

fun mk_case_names_exhausts descr new =
  map (Rule_Cases.case_names o exhaust_cases descr o #1)
    (filter (fn ((_, (name, _, _))) => member (op =) new name) descr);

end;


(* translation rules for case *)

fun make_case ctxt =
  Datatype_Case.make_case (info_of_constr_permissive (Proof_Context.theory_of ctxt)) ctxt;

fun strip_case ctxt =
  Datatype_Case.strip_case (info_of_case (Proof_Context.theory_of ctxt));

fun add_case_tr' case_names thy =
  Sign.add_advanced_trfuns ([], [],
    map (fn case_name =>
      let val case_name' = Lexicon.mark_const case_name in
        (case_name', Datatype_Case.case_tr' info_of_case case_name')
      end) case_names, []) thy;

val trfun_setup =
  Sign.add_advanced_trfuns ([],
    [(@{syntax_const "_case_syntax"}, Datatype_Case.case_tr true info_of_constr_permissive)],
    [], []);



(** document antiquotation **)

val antiq_setup =
  Thy_Output.antiquotation @{binding datatype} (Args.type_name true)
    (fn {source = src, context = ctxt, ...} => fn dtco =>
      let
        val thy = Proof_Context.theory_of ctxt;
        val (vs, cos) = the_spec thy dtco;
        val ty = Type (dtco, map TFree vs);
        val pretty_typ_bracket = Syntax.pretty_typ (Config.put pretty_priority 1001 ctxt);
        fun pretty_constr (co, tys) =
          Pretty.block (Pretty.breaks
            (Syntax.pretty_term ctxt (Const (co, tys ---> ty)) ::
              map pretty_typ_bracket tys));
        val pretty_datatype =
          Pretty.block
           (Pretty.command "datatype" :: Pretty.brk 1 ::
            Syntax.pretty_typ ctxt ty ::
            Pretty.str " =" :: Pretty.brk 1 ::
            flat (separate [Pretty.brk 1, Pretty.str "| "] (map (single o pretty_constr) cos)));
      in
        Thy_Output.output ctxt
          (Thy_Output.maybe_pretty_source (K (K pretty_datatype)) ctxt src [()])
      end);



(** abstract theory extensions relative to a datatype characterisation **)

structure Datatype_Interpretation = Interpretation
(
  type T = Datatype_Aux.config * string list;
  val eq: T * T -> bool = eq_snd (op =);
);
fun interpretation f = Datatype_Interpretation.interpretation (uncurry f);
val interpretation_data = Datatype_Interpretation.data;



(** setup theory **)

val setup =
  trfun_setup #>
  antiq_setup #>
  Datatype_Interpretation.init;

open Datatype_Aux;

end;
