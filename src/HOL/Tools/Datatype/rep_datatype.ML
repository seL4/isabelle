(*  Title:      HOL/Tools/Datatype/rep_datatype.ML
    Author:     Stefan Berghofer, TU Muenchen

Representation of existing types as datatypes.
*)

signature REP_DATATYPE =
sig
  val derive_datatype_props : Datatype_Aux.config -> string list -> Datatype_Aux.descr list ->
    thm -> thm list list -> thm list list -> theory -> string list * theory
  val rep_datatype : Datatype_Aux.config -> (string list -> Proof.context -> Proof.context) ->
    term list -> theory -> Proof.state
  val rep_datatype_cmd : Datatype_Aux.config -> (string list -> Proof.context -> Proof.context) ->
    string list -> theory -> Proof.state
end;

structure Rep_Datatype: REP_DATATYPE =
struct

fun make_dt_info descr induct inducts rec_names rec_rewrites
    (index, (((((((((((_, (tname, _, _))), inject), distinct),
      exhaust), nchotomy), case_name), case_rewrites), case_cong), weak_case_cong),
        (split, split_asm))) =
  (tname,
   {index = index,
    descr = descr,
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

fun derive_datatype_props config dt_names descr induct inject distinct thy1 =
  let
    val thy2 = thy1 |> Theory.checkpoint;
    val flat_descr = flat descr;
    val new_type_names = map Long_Name.base_name dt_names;
    val _ =
      Datatype_Aux.message config
        ("Deriving properties for datatype(s) " ^ commas_quote new_type_names);

    val (exhaust, thy3) = thy2
      |> Datatype_Abs_Proofs.prove_casedist_thms config new_type_names
        descr induct (Datatype_Data.mk_case_names_exhausts flat_descr dt_names);
    val (nchotomys, thy4) = thy3
      |> Datatype_Abs_Proofs.prove_nchotomys config new_type_names descr exhaust;
    val ((rec_names, rec_rewrites), thy5) = thy4
      |> Datatype_Abs_Proofs.prove_primrec_thms
        config new_type_names descr (#inject o the o Symtab.lookup (Datatype_Data.get_all thy4))
        inject (distinct, Datatype_Data.all_distincts thy2 (Datatype_Aux.get_rec_types flat_descr))
        induct;
    val ((case_rewrites, case_names), thy6) = thy5
      |> Datatype_Abs_Proofs.prove_case_thms config new_type_names descr rec_names rec_rewrites;
    val (case_congs, thy7) = thy6
      |> Datatype_Abs_Proofs.prove_case_congs new_type_names case_names descr
        nchotomys case_rewrites;
    val (weak_case_congs, thy8) = thy7
      |> Datatype_Abs_Proofs.prove_weak_case_congs new_type_names case_names descr;
    val (splits, thy9) = thy8
      |> Datatype_Abs_Proofs.prove_split_thms
        config new_type_names case_names descr inject distinct exhaust case_rewrites;

    val inducts = Project_Rule.projections (Proof_Context.init_global thy2) induct;
    val dt_infos =
      map_index
        (make_dt_info flat_descr induct inducts rec_names rec_rewrites)
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
    |> Datatype_Data.add_case_tr' case_names
    |> Datatype_Data.register dt_infos
    |> Datatype_Data.interpretation_data (config, dt_names)
    |> pair dt_names
  end;



(** declare existing type as datatype **)

local

fun prove_rep_datatype config dt_names descr raw_inject half_distinct raw_induct thy1 =
  let
    val raw_distinct = (map o maps) (fn thm => [thm, thm RS not_sym]) half_distinct;
    val new_type_names = map Long_Name.base_name dt_names;
    val prfx = Binding.qualify true (space_implode "_" new_type_names);
    val (((inject, distinct), [induct]), thy2) =
      thy1
      |> Datatype_Aux.store_thmss "inject" new_type_names raw_inject
      ||>> Datatype_Aux.store_thmss "distinct" new_type_names raw_distinct
      ||>> Global_Theory.add_thms
        [((prfx (Binding.name "induct"), raw_induct),
          [Datatype_Data.mk_case_names_induct descr])];
  in
    thy2
    |> derive_datatype_props config dt_names [descr] induct inject distinct
 end;

fun gen_rep_datatype prep_term config after_qed raw_ts thy =
  let
    val ctxt = Proof_Context.init_global thy;

    fun constr_of_term (Const (c, T)) = (c, T)
      | constr_of_term t = error ("Not a constant: " ^ Syntax.string_of_term ctxt t);
    fun no_constr (c, T) =
      error ("Bad constructor: " ^ Proof_Context.extern_const ctxt c ^ "::" ^
        Syntax.string_of_typ ctxt T);
    fun type_of_constr (cT as (_, T)) =
      let
        val frees = Term.add_tfreesT T [];
        val (tyco, vs) = (apsnd o map) dest_TFree (dest_Type (body_type T))
          handle TYPE _ => no_constr cT
        val _ = if has_duplicates (eq_fst (op =)) vs then no_constr cT else ();
        val _ = if length frees <> length vs then no_constr cT else ();
      in (tyco, (vs, cT)) end;

    val raw_cs =
      AList.group (op =) (map (type_of_constr o constr_of_term o prep_term thy) raw_ts);
    val _ =
      (case map_filter (fn (tyco, _) =>
          if Symtab.defined (Datatype_Data.get_all thy) tyco then SOME tyco else NONE) raw_cs of
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
    val dtyps_of_typ = map (Datatype_Aux.dtyp_of_typ (map (rpair vs o fst) cs)) o binder_types;
    val dt_names = map fst cs;

    fun mk_spec (i, (tyco, constr)) =
      (i, (tyco, map Datatype_Aux.DtTFree vs, (map o apsnd) dtyps_of_typ constr));
    val descr = map_index mk_spec cs;
    val injs = Datatype_Prop.make_injs [descr];
    val half_distincts = Datatype_Prop.make_distincts [descr];
    val ind = Datatype_Prop.make_ind [descr];
    val rules = (map o map o map) Logic.close_form [[[ind]], injs, half_distincts];

    fun after_qed' raw_thms =
      let
        val [[[raw_induct]], raw_inject, half_distinct] =
          unflat rules (map Drule.zero_var_indexes_list raw_thms);
            (*FIXME somehow dubious*)
      in
        Proof_Context.background_theory_result  (* FIXME !? *)
          (prove_rep_datatype config dt_names descr raw_inject half_distinct raw_induct)
        #-> after_qed
      end;
  in
    ctxt
    |> Proof.theorem NONE after_qed' ((map o map) (rpair []) (flat rules))
  end;

in

val rep_datatype = gen_rep_datatype Sign.cert_term;
val rep_datatype_cmd = gen_rep_datatype Syntax.read_term_global;

end;


(* outer syntax *)

val _ =
  Outer_Syntax.command "rep_datatype" "represent existing types inductively" Keyword.thy_goal
    (Scan.repeat1 Parse.term >> (fn ts =>
      Toplevel.print o
      Toplevel.theory_to_proof (rep_datatype_cmd Datatype_Aux.default_config (K I) ts)));

end;
