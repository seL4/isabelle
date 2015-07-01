(*  Title:      Pure/subgoal.ML
    Author:     Makarius
    Author:     Daniel Matichuk, NICTA/UNSW

Tactical operations with explicit subgoal focus, based on canonical
proof decomposition.  The "visible" part of the text within the
context is fixed, the remaining goal may be schematic.

Isar subgoal command for proof structure within unstructured proof
scripts.
*)

signature SUBGOAL =
sig
  type focus = {context: Proof.context, params: (string * cterm) list, prems: thm list,
    asms: cterm list, concl: cterm, schematics: (ctyp * ctyp) list * (cterm * cterm) list}
  val focus_params: Proof.context -> int -> thm -> focus * thm
  val focus_params_fixed: Proof.context -> int -> thm -> focus * thm
  val focus_prems: Proof.context -> int -> thm -> focus * thm
  val focus: Proof.context -> int -> thm -> focus * thm
  val retrofit: Proof.context -> Proof.context -> (string * cterm) list -> cterm list ->
    int -> thm -> thm -> thm Seq.seq
  val FOCUS_PARAMS: (focus -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PARAMS_FIXED: (focus -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PREMS: (focus -> tactic) -> Proof.context -> int -> tactic
  val FOCUS: (focus -> tactic) -> Proof.context -> int -> tactic
  val SUBPROOF: (focus -> tactic) -> Proof.context -> int -> tactic
  val subgoal: Attrib.binding -> Attrib.binding option -> string option list ->
    Proof.state -> focus * Proof.state
  val subgoal_cmd: Attrib.binding -> Attrib.binding option -> string option list ->
    Proof.state -> focus * Proof.state
end;

structure Subgoal: SUBGOAL =
struct

(* focus *)

type focus = {context: Proof.context, params: (string * cterm) list, prems: thm list,
  asms: cterm list, concl: cterm, schematics: (ctyp * ctyp) list * (cterm * cterm) list};

fun gen_focus (do_prems, do_concl) ctxt i raw_st =
  let
    val st = raw_st
      |> Thm.transfer (Proof_Context.theory_of ctxt)
      |> Simplifier.norm_hhf_protect ctxt;
    val ((schematic_types, [st']), ctxt1) = Variable.importT [st] ctxt;
    val ((params, goal), ctxt2) = Variable.focus_cterm (Thm.cprem_of st' i) ctxt1;

    val (asms, concl) =
      if do_prems then (Drule.strip_imp_prems goal, Drule.strip_imp_concl goal)
      else ([], goal);
    val text = asms @ (if do_concl then [concl] else []);

    val (inst, ctxt3) = Variable.import_inst true (map Thm.term_of text) ctxt2;
    val (_, schematic_terms) = Thm.certify_inst ctxt3 inst;

    val schematics = (schematic_types, schematic_terms);
    val asms' = map (Thm.instantiate_cterm schematics) asms;
    val concl' = Thm.instantiate_cterm schematics concl;
    val (prems, context) = Assumption.add_assumes asms' ctxt3;
  in
    ({context = context, params = params, prems = prems,
      asms = asms', concl = concl', schematics = schematics}, Goal.init concl')
  end;

val focus_params = gen_focus (false, false);
val focus_params_fixed = gen_focus (false, true);
val focus_prems = gen_focus (true, false);
val focus = gen_focus (true, true);


(* lift and retrofit *)

(*
     B [?'b, ?y]
  ----------------
  B ['b, y params]
*)
fun lift_import idx params th ctxt =
  let
    val ((_, [th']), ctxt') = Variable.importT [th] ctxt;

    val Ts = map Thm.typ_of_cterm params;
    val ts = map Thm.term_of params;

    val prop = Thm.full_prop_of th';
    val concl_vars = Term.add_vars (Logic.strip_imp_concl prop) [];
    val vars = rev (Term.add_vars prop []);
    val (ys, ctxt'') = Variable.variant_fixes (map (Name.clean o #1 o #1) vars) ctxt';

    fun var_inst v y =
      let
        val ((x, i), T) = v;
        val (U, args) =
          if member (op =) concl_vars v then (T, [])
          else (Ts ---> T, ts);
        val u = Free (y, U);
        in ((Var v, list_comb (u, args)), (u, Var ((x, i + idx), U))) end;
    val (inst1, inst2) =
      split_list (map (apply2 (apply2 (Thm.cterm_of ctxt))) (map2 var_inst vars ys));

    val th'' = Thm.instantiate ([], inst1) th';
  in ((inst2, th''), ctxt'') end;

(*
       [x, A x]
          :
       B x ==> C
  ------------------
  [!!x. A x ==> B x]
          :
          C
*)
fun lift_subgoals params asms th =
  let
    fun lift ct = fold_rev Thm.all_name params (Drule.list_implies (asms, ct));
    val unlift =
      fold (Thm.elim_implies o Thm.assume) asms o
      Drule.forall_elim_list (map #2 params) o Thm.assume;
    val subgoals = map lift (Drule.strip_imp_prems (Thm.cprop_of th));
    val th' = fold (Thm.elim_implies o unlift) subgoals th;
  in (subgoals, th') end;

fun retrofit ctxt1 ctxt0 params asms i st1 st0 =
  let
    val idx = Thm.maxidx_of st0 + 1;
    val ps = map #2 params;
    val ((subgoal_inst, st2), ctxt2) = lift_import idx ps st1 ctxt1;
    val (subgoals, st3) = lift_subgoals params asms st2;
    val result = st3
      |> Goal.conclude
      |> Drule.implies_intr_list asms
      |> Drule.forall_intr_list ps
      |> Drule.implies_intr_list subgoals
      |> fold_rev (Thm.forall_intr o #1) subgoal_inst
      |> fold (Thm.forall_elim o #2) subgoal_inst
      |> Thm.adjust_maxidx_thm idx
      |> singleton (Variable.export ctxt2 ctxt0);
  in
    Thm.bicompose (SOME ctxt0) {flatten = true, match = false, incremented = false}
      (false, result, Thm.nprems_of st1) i st0
  end;


(* tacticals *)

fun GEN_FOCUS flags tac ctxt i st =
  if Thm.nprems_of st < i then Seq.empty
  else
    let val (args as {context = ctxt', params, asms, ...}, st') = gen_focus flags ctxt i st;
    in Seq.lifts (retrofit ctxt' ctxt params asms i) (tac args st') st end;

val FOCUS_PARAMS = GEN_FOCUS (false, false);
val FOCUS_PARAMS_FIXED = GEN_FOCUS (false, true);
val FOCUS_PREMS = GEN_FOCUS (true, false);
val FOCUS = GEN_FOCUS (true, true);

fun SUBPROOF tac ctxt = FOCUS (Seq.map (Goal.check_finished ctxt) oo tac) ctxt;


(* Isar subgoal command *)

local

fun rename_params ctxt param_specs st =
  let
    val _ = if Thm.no_prems st then error "No subgoals!" else ();
    val (A, C) = Logic.dest_implies (Thm.prop_of st);

    val params =
      map (apfst (Name.internal o Name.clean)) (Term.strip_all_vars A)
      |> Term.variant_frees A |> map #1;
    val _ =
      (case drop (length params) param_specs of
        [] => ()
      | bad => error ("Excessive subgoal parameters: " ^ commas_quote (map (the_default "_") bad)));

    fun rename_list (SOME x :: xs) (y :: ys) =
          (Proof_Context.cert_var (Binding.name x, NONE, NoSyn) ctxt; x :: rename_list xs ys)
      | rename_list (NONE :: xs) (y :: ys) = y :: rename_list xs ys
      | rename_list _ ys = ys;

    fun rename_prop (x :: xs) ((c as Const ("Pure.all", _)) $ Abs (_, T, t)) =
          (c $ Abs (x, T, rename_prop xs t))
      | rename_prop [] t = t;
  in
    Thm.renamed_prop (Logic.mk_implies (rename_prop (rename_list param_specs params) A, C)) st
  end;

fun gen_subgoal prep_atts raw_result_binding raw_prems_binding param_specs state =
  let
    val _ = Proof.assert_backward state;

    val state1 = state |> Proof.refine_insert [];
    val {context = ctxt, facts = facts, goal = st} = Proof.raw_goal state1;

    val result_binding = apsnd (map (prep_atts ctxt)) raw_result_binding;
    val (prems_binding, do_prems) =
      (case raw_prems_binding of
        SOME (b, raw_atts) => ((b, map (prep_atts ctxt) raw_atts), true)
      | NONE => ((Binding.empty, []), false));

    val (subgoal_focus, _) =
      rename_params ctxt param_specs st
      |> (if do_prems then focus else focus_params_fixed) ctxt 1;

    fun after_qed (ctxt'', [[result]]) =
      Proof.end_block #> (fn state' =>
        let
          val ctxt' = Proof.context_of state';
          val results' =
            Proof_Context.export ctxt'' ctxt' (Conjunction.elim_conjunctions result);
        in
          state'
          |> Proof.refine_primitive (fn _ => fn _ =>
            retrofit ctxt'' ctxt' (#params subgoal_focus) (#asms subgoal_focus) 1
              (Goal.protect 0 result) st
            |> Seq.hd)
          |> Proof.map_context
            (#2 o Proof_Context.note_thmss "" [(result_binding, [(results', [])])])
        end)
      #> Proof.reset_facts
      #> Proof.enter_backward;
  in
    state1
    |> Proof.enter_forward
    |> Proof.using_facts []
    |> Proof.begin_block
    |> Proof.map_context (fn _ =>
      #context subgoal_focus
      |> Proof_Context.note_thmss "" [(prems_binding, [(#prems subgoal_focus, [])])] |> #2)
    |> Proof.internal_goal (K (K ())) (Proof_Context.get_mode ctxt) true "subgoal"
        NONE after_qed [] [] [(Thm.empty_binding, [(Thm.term_of (#concl subgoal_focus), [])])] |> #2
    |> Proof.using_facts facts
    |> pair subgoal_focus
  end;

in

val subgoal = gen_subgoal Attrib.attribute;
val subgoal_cmd = gen_subgoal Attrib.attribute_cmd;

end;

end;

val SUBPROOF = Subgoal.SUBPROOF;
