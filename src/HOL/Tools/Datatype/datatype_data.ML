(*  Title:      HOL/Tools/Datatype/datatype_data.ML
    Author:     Stefan Berghofer, TU Muenchen

Datatype package: bookkeeping; interpretation of existing types as datatypes.
*)

signature DATATYPE_DATA =
sig
  include DATATYPE_COMMON
  val derive_datatype_props : config -> string list -> string list option
    -> descr list -> (string * sort) list -> thm -> thm list list -> thm list list
    -> theory -> string list * theory
  val rep_datatype : config -> (string list -> Proof.context -> Proof.context)
    -> string list option -> term list -> theory -> Proof.state
  val rep_datatype_cmd : string list option -> string list -> theory -> Proof.state
  val get_info : theory -> string -> info option
  val the_info : theory -> string -> info
  val the_descr : theory -> string list
    -> descr * (string * sort) list * string list
      * string * (string list * string list) * (typ list * typ list)
  val the_spec : theory -> string -> (string * sort) list * (string * typ list) list
  val all_distincts : theory -> typ list -> thm list list
  val get_constrs : theory -> string -> (string * typ) list option
  val get_all : theory -> info Symtab.table
  val info_of_constr : theory -> string * typ -> info option
  val info_of_constr_permissive : theory -> string * typ -> info option
  val info_of_case : theory -> string -> info option
  val interpretation : (config -> string list -> theory -> theory) -> theory -> theory
  val make_case :  Proof.context -> Datatype_Case.config -> string list -> term ->
    (term * term) list -> term
  val strip_case : Proof.context -> bool -> term -> (term * (term * term) list) option
  val read_typ: theory -> string -> (string * sort) list -> typ * (string * sort) list
  val cert_typ: theory -> typ -> (string * sort) list -> typ * (string * sort) list
  val mk_case_names_induct: descr -> attribute
  val setup: theory -> theory
end;

structure Datatype_Data: DATATYPE_DATA =
struct

(** theory data **)

(* data management *)

structure DatatypesData = Theory_Data
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

val get_all = #types o DatatypesData.get;
val get_info = Symtab.lookup o get_all;

fun the_info thy name =
  (case get_info thy name of
    SOME info => info
  | NONE => error ("Unknown datatype " ^ quote name));

fun info_of_constr thy (c, T) =
  let
    val tab = Symtab.lookup_list ((#constrs o DatatypesData.get) thy) c;
  in
    (case body_type T of
      Type (tyco, _) => AList.lookup (op =) tab tyco
    | _ => NONE)
  end;

fun info_of_constr_permissive thy (c, T) =
  let
    val tab = Symtab.lookup_list (#constrs (DatatypesData.get thy)) c;
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

val info_of_case = Symtab.lookup o #cases o DatatypesData.get;

fun register (dt_infos : (string * Datatype_Aux.info) list) =
  DatatypesData.map (fn {types, constrs, cases} =>
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
    val { descr, index, sorts = raw_sorts, ... } = the_info thy dtco;
    val SOME (_, dtys, raw_cos) = AList.lookup (op =) descr index;
    val sorts =
      map ((fn v => (v, (the o AList.lookup (op =) raw_sorts) v)) o Datatype_Aux.dest_DtTFree) dtys;
    val cos = map (fn (co, tys) => (co, map (Datatype_Aux.typ_of_dtyp descr sorts) tys)) raw_cos;
  in (sorts, cos) end;

fun the_descr thy (raw_tycos as raw_tyco :: _) =
  let
    val info = the_info thy raw_tyco;
    val descr = #descr info;

    val SOME (_, dtys, _) = AList.lookup (op =) descr (#index info);
    val vs =
      map ((fn v => (v, the (AList.lookup (op =) (#sorts info) v))) o Datatype_Aux.dest_DtTFree)
        dtys;

    fun is_DtTFree (Datatype_Aux.DtTFree _) = true
      | is_DtTFree _ = false;
    val k = find_index (fn (_, (_, dTs, _)) => not (forall is_DtTFree dTs)) descr;
    val protoTs as (dataTs, _) =
      chop k descr
      |> (pairself o map)
        (fn (_, (tyco, dTs, _)) => (tyco, map (Datatype_Aux.typ_of_dtyp descr vs) dTs));

    val tycos = map fst dataTs;
    val _ =
      if eq_set (op =) (tycos, raw_tycos) then ()
      else
        error ("Type constructors " ^ commas_quote raw_tycos ^
          " do not belong exhaustively to one mutual recursive datatype");

    val (Ts, Us) = (pairself o map) Type protoTs;

    val names = map Long_Name.base_name (the_default tycos (#alt_names info));
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
    SOME (sorts, cos) =>
      let
        fun subst (v, sort) = TVar ((v, 0), sort);
        fun subst_ty (TFree v) = subst v
          | subst_ty ty = ty;
        val dty = Type (dtco, map subst sorts);
        fun mk_co (co, tys) = (co, map (Term.map_atyps subst_ty) tys ---> dty);
      in SOME (map mk_co cos) end
  | NONE => NONE);



(** various auxiliary **)

(* prepare datatype specifications *)

fun read_typ thy str sorts =
  let
    val ctxt = Proof_Context.init_global thy
      |> fold (Variable.declare_typ o TFree) sorts;
    val T = Syntax.read_typ ctxt str;
  in (T, Term.add_tfreesT T sorts) end;

fun cert_typ sign raw_T sorts =
  let
    val T = Type.no_tvars (Sign.certify_typ sign raw_T)
      handle TYPE (msg, _, _) => error msg;
    val sorts' = Term.add_tfreesT T sorts;
    val _ =
      (case duplicates (op =) (map fst sorts') of
        [] => ()
      | dups => error ("Inconsistent sort constraints for " ^ commas dups));
  in (T, sorts') end;


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

fun make_dt_info alt_names descr sorts induct inducts rec_names rec_rewrites
    (index, (((((((((((_, (tname, _, _))), inject), distinct),
      exhaust), nchotomy), case_name), case_rewrites), case_cong), weak_case_cong),
        (split, split_asm))) =
  (tname,
   {index = index,
    alt_names = alt_names,
    descr = descr,
    sorts = sorts,
    inject = inject,
    distinct = distinct,
    induct = induct,
    inducts = inducts,
    exhaust = exhaust,
    nchotomy = nchotomy,
    rec_names = rec_names,
    rec_rewrites = rec_rewrites,
    case_name = case_name,
    case_rewrites = case_rewrites,
    case_cong = case_cong,
    weak_case_cong = weak_case_cong,
    split = split,
    split_asm = split_asm});

fun derive_datatype_props config dt_names alt_names descr sorts
    induct inject distinct thy1 =
  let
    val thy2 = thy1 |> Theory.checkpoint;
    val flat_descr = flat descr;
    val new_type_names = map Long_Name.base_name (the_default dt_names alt_names);
    val _ =
      Datatype_Aux.message config
        ("Deriving properties for datatype(s) " ^ commas_quote new_type_names);

    val (exhaust, thy3) =
      Datatype_Abs_Proofs.prove_casedist_thms config new_type_names
        descr sorts induct (mk_case_names_exhausts flat_descr dt_names) thy2;
    val (nchotomys, thy4) =
      Datatype_Abs_Proofs.prove_nchotomys config new_type_names
        descr sorts exhaust thy3;
    val ((rec_names, rec_rewrites), thy5) =
      Datatype_Abs_Proofs.prove_primrec_thms
        config new_type_names descr sorts (#inject o the o Symtab.lookup (get_all thy4))
        inject (distinct, all_distincts thy2 (Datatype_Aux.get_rec_types flat_descr sorts))
        induct thy4;
    val ((case_rewrites, case_names), thy6) =
      Datatype_Abs_Proofs.prove_case_thms
        config new_type_names descr sorts rec_names rec_rewrites thy5;
    val (case_congs, thy7) =
      Datatype_Abs_Proofs.prove_case_congs new_type_names
        descr sorts nchotomys case_rewrites thy6;
    val (weak_case_congs, thy8) =
      Datatype_Abs_Proofs.prove_weak_case_congs new_type_names descr sorts thy7;
    val (splits, thy9) =
      Datatype_Abs_Proofs.prove_split_thms
        config new_type_names descr sorts inject distinct exhaust case_rewrites thy8;

    val inducts = Project_Rule.projections (Proof_Context.init_global thy2) induct;
    val dt_infos = map_index
      (make_dt_info alt_names flat_descr sorts induct inducts rec_names rec_rewrites)
      (hd descr ~~ inject ~~ distinct ~~ exhaust ~~ nchotomys ~~
        case_names ~~ case_rewrites ~~ case_congs ~~ weak_case_congs ~~ splits);
    val dt_names = map fst dt_infos;
    val prfx = Binding.qualify true (space_implode "_" new_type_names);
    val simps = flat (inject @ distinct @ case_rewrites) @ rec_rewrites;
    val named_rules = flat (map_index (fn (index, tname) =>
      [((Binding.empty, [nth inducts index]), [Induct.induct_type tname]),
       ((Binding.empty, [nth exhaust index]), [Induct.cases_type tname])]) dt_names);
    val unnamed_rules = map (fn induct =>
      ((Binding.empty, [induct]), [Rule_Cases.inner_rule, Induct.induct_type ""]))
        (drop (length dt_names) inducts);
  in
    thy9
    |> Global_Theory.add_thmss ([((prfx (Binding.name "simps"), simps), []),
        ((prfx (Binding.name "inducts"), inducts), []),
        ((prfx (Binding.name "splits"), maps (fn (x, y) => [x, y]) splits), []),
        ((Binding.empty, flat case_rewrites @ flat distinct @ rec_rewrites),
          [Simplifier.simp_add]),
        ((Binding.empty, rec_rewrites), [Code.add_default_eqn_attribute]),
        ((Binding.empty, flat inject), [iff_add]),
        ((Binding.empty, map (fn th => th RS notE) (flat distinct)),
          [Classical.safe_elim NONE]),
        ((Binding.empty, weak_case_congs), [Simplifier.cong_add]),
        ((Binding.empty, flat (distinct @ inject)), [Induct.induct_simp_add])] @
          named_rules @ unnamed_rules)
    |> snd
    |> add_case_tr' case_names
    |> register dt_infos
    |> Datatype_Interpretation.data (config, dt_names)
    |> pair dt_names
  end;



(** declare existing type as datatype **)

fun prove_rep_datatype config dt_names alt_names descr sorts
    raw_inject half_distinct raw_induct thy1 =
  let
    val raw_distinct = (map o maps) (fn thm => [thm, thm RS not_sym]) half_distinct;
    val new_type_names = map Long_Name.base_name (the_default dt_names alt_names);
    val prfx = Binding.qualify true (space_implode "_" new_type_names);
    val (((inject, distinct), [induct]), thy2) =
      thy1
      |> Datatype_Aux.store_thmss "inject" new_type_names raw_inject
      ||>> Datatype_Aux.store_thmss "distinct" new_type_names raw_distinct
      ||>> Global_Theory.add_thms
        [((prfx (Binding.name "induct"), raw_induct),
          [mk_case_names_induct descr])];
  in
    thy2
    |> derive_datatype_props config dt_names alt_names [descr] sorts
         induct inject distinct
 end;

fun gen_rep_datatype prep_term config after_qed alt_names raw_ts thy =
  let
    val ctxt = Proof_Context.init_global thy;

    fun constr_of_term (Const (c, T)) = (c, T)
      | constr_of_term t = error ("Not a constant: " ^ Syntax.string_of_term ctxt t);
    fun no_constr (c, T) =
      error ("Bad constructor: " ^ Proof_Context.extern_const ctxt c ^ "::" ^
        Syntax.string_of_typ ctxt T);
    fun type_of_constr (cT as (_, T)) =
      let
        val frees = Misc_Legacy.typ_tfrees T;
        val (tyco, vs) = (apsnd o map) dest_TFree (dest_Type (body_type T))
          handle TYPE _ => no_constr cT
        val _ = if has_duplicates (eq_fst (op =)) vs then no_constr cT else ();
        val _ = if length frees <> length vs then no_constr cT else ();
      in (tyco, (vs, cT)) end;

    val raw_cs =
      AList.group (op =) (map (type_of_constr o constr_of_term o prep_term thy) raw_ts);
    val _ =
      (case map_filter (fn (tyco, _) =>
          if Symtab.defined (get_all thy) tyco then SOME tyco else NONE) raw_cs of
        [] => ()
      | tycos => error ("Type(s) " ^ commas_quote tycos ^ " already represented inductivly"));
    val raw_vss = maps (map (map snd o fst) o snd) raw_cs;
    val ms =
      (case distinct (op =) (map length raw_vss) of
         [n] => 0 upto n - 1
      | _ => error "Different types in given constructors");
    fun inter_sort m =
      map (fn xs => nth xs m) raw_vss
      |> foldr1 (Sorts.inter_sort (Sign.classes_of thy));
    val sorts = map inter_sort ms;
    val vs = Name.invent_names Name.context Name.aT sorts;

    fun norm_constr (raw_vs, (c, T)) =
      (c, map_atyps
        (TFree o (the o AList.lookup (op =) (map fst raw_vs ~~ vs)) o fst o dest_TFree) T);

    val cs = map (apsnd (map norm_constr)) raw_cs;
    val dtyps_of_typ =
      map (Datatype_Aux.dtyp_of_typ (map (rpair (map fst vs) o fst) cs)) o binder_types;
    val dt_names = map fst cs;

    fun mk_spec (i, (tyco, constr)) =
      (i, (tyco,
        map (Datatype_Aux.DtTFree o fst) vs,
        (map o apsnd) dtyps_of_typ constr));
    val descr = map_index mk_spec cs;
    val injs = Datatype_Prop.make_injs [descr] vs;
    val half_distincts = map snd (Datatype_Prop.make_distincts [descr] vs);
    val ind = Datatype_Prop.make_ind [descr] vs;
    val rules = (map o map o map) Logic.close_form [[[ind]], injs, half_distincts];

    fun after_qed' raw_thms =
      let
        val [[[raw_induct]], raw_inject, half_distinct] =
          unflat rules (map Drule.zero_var_indexes_list raw_thms);
            (*FIXME somehow dubious*)
      in
        Proof_Context.background_theory_result  (* FIXME !? *)
          (prove_rep_datatype config dt_names alt_names descr vs
            raw_inject half_distinct raw_induct)
        #-> after_qed
      end;
  in
    ctxt
    |> Proof.theorem NONE after_qed' ((map o map) (rpair []) (flat rules))
  end;

val rep_datatype = gen_rep_datatype Sign.cert_term;
val rep_datatype_cmd = gen_rep_datatype Syntax.read_term_global Datatype_Aux.default_config (K I);



(** package setup **)

(* setup theory *)

val setup =
  trfun_setup #>
  antiq_setup #>
  Datatype_Interpretation.init;


(* outer syntax *)

val _ =
  Outer_Syntax.command "rep_datatype" "represent existing types inductively" Keyword.thy_goal
    (Scan.option (Parse.$$$ "(" |-- Scan.repeat1 Parse.name --| Parse.$$$ ")") --
      Scan.repeat1 Parse.term
      >> (fn (alt_names, ts) =>
          Toplevel.print o Toplevel.theory_to_proof (rep_datatype_cmd alt_names ts)));


open Datatype_Aux;

end;
