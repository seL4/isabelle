(*  Title:      Pure/Isar/obtain.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The 'obtain' language element -- achieves (eliminated) existential
quantification proof command level.

The common case:

    <goal_facts>
    have/show C
      obtain a in P[a] <proof>          ==

    <goal_facts>
    have/show C
    proof succeed
      def thesis == C
      presume that: !!a. P a ==> thesis
      from goal_facts show thesis <proof>
    next
      fix a
      assume P a

The general case:

    <goal_facts>
    have/show !!x. G x ==> C x
      obtain a in P[a] <proof>          ==

    <goal_facts>
    have/show !!x. G x ==> C x
    proof succeed
      fix x
      assume antecedent: G x
      def thesis == ?thesis_prop x
      presume that: !!a. P a ==> thesis
      from goal_facts show thesis <proof>
    next
      fix a
      assume P a


TODO:
  - handle general case;
*)

signature OBTAIN =
sig
  val obtain: (string list * string option) list
    -> (string * Proof.context attribute list * (string * (string list * string list)) list) list
    -> Proof.state -> Proof.state Seq.seq
  val obtain_i: (string list * typ option) list
    -> (string * Proof.context attribute list * (term * (term list * term list)) list) list
    -> Proof.state -> Proof.state Seq.seq
end;

structure Obtain: OBTAIN =
struct

val thatN = "that";

fun gen_obtain prep_typ prep_prop fix assume raw_vars raw_asms state =
  let
    val (prop, (goal_facts, goal)) = Proof.get_goal (Proof.assert_backward state);

    val parms = Logic.strip_params prop;
    val hyps = Logic.strip_assums_hyp prop;
    val concl = Logic.strip_assums_concl prop;
    val _ =
      if null parms then () else raise Proof.STATE ("Cannot handle params in goal (yet)", state);

    val ((thesis_name, thesis_term), atomic_thesis) = AutoBind.atomic_thesis concl;


    fun fix_vars (ctxt, (xs, raw_T)) =
      let
        val T = apsome (prep_typ ctxt) raw_T;
        val ctxt' = ProofContext.fix_i [(xs, T)] ctxt;
      in (ctxt', map (ProofContext.cert_skolem ctxt') xs) end;

    fun prep_asm (ctxt, (_, _, raw_propps)) =
      let val ts = map (prep_prop ctxt) (map fst raw_propps);
      in (ctxt |> ProofContext.declare_terms ts, ts) end;

    val (fix_ctxt, skolems) = apsnd flat (foldl_map fix_vars (Proof.context_of state, raw_vars));
    val (asms_ctxt, asms) = apsnd flat (foldl_map prep_asm (fix_ctxt, raw_asms));

    fun find_free x t =
      (case Proof.find_free t x of Some (Free a) => Some a | _ => None);
    fun find_skolem x = Library.get_first (find_free x) asms;
    val skolemTs = mapfilter find_skolem skolems;

    val that_prop =
      Logic.list_rename_params (map (Syntax.dest_skolem o #1) skolemTs,
        Term.list_all_free (skolemTs, Logic.list_implies (asms, atomic_thesis)));

    val presume_stateq =
      state
      |> Method.proof (Some (Method.Basic (K Method.succeed)))
      |> Seq.map (fn st => st
        |> LocalDefs.def_i "" [] ((thesis_name, None), (thesis_term, []))
        |> Proof.presume_i [(thatN, [], [(that_prop, ([], []))])]);

    fun after_qed st =
      st
      |> Proof.next_block
      |> fix raw_vars           (*prepared twice!*)
      |> assume raw_asms        (*prepared twice!*)
      |> Seq.single;
  in
    presume_stateq
    |> Seq.map (fn st => st
      |> Proof.from_facts goal_facts
      |> Proof.show_i after_qed "" [] (atomic_thesis, ([], []))
      |> Method.refine (Method.Basic (K (Method.insert (Proof.the_facts st)))))
    |> Seq.flat
  end;


val obtain = gen_obtain ProofContext.read_typ ProofContext.read_prop Proof.fix Proof.assume;
val obtain_i = gen_obtain ProofContext.cert_typ ProofContext.cert_prop Proof.fix_i Proof.assume_i;


end;
