(*  Title:      HOL/Boogie/Tools/boogie_tactics.ML
    Author:     Sascha Boehme, TU Muenchen

Boogie tactics and Boogie methods.
*)

signature BOOGIE_TACTICS =
sig
  val unfold_labels_tac: Proof.context -> int -> tactic
  val boogie_tac: Proof.context -> thm list -> int -> tactic
  val boogie_all_tac: Proof.context -> thm list -> tactic
  val setup: theory -> theory
end

structure Boogie_Tactics: BOOGIE_TACTICS =
struct

fun as_meta_eq eq = eq RS @{thm eq_reflection}

val assert_at_def = as_meta_eq @{thm assert_at_def}
val block_at_def = as_meta_eq @{thm block_at_def}
val label_eqs = [assert_at_def, block_at_def]

fun unfold_labels_tac ctxt =
  let val unfold = More_Conv.rewrs_conv label_eqs
  in CONVERSION (More_Conv.top_sweep_conv (K unfold) ctxt) end

fun boogie_tac ctxt rules =
  unfold_labels_tac ctxt
  THEN' SMT_Solver.smt_tac ctxt (Boogie_Axioms.get ctxt @ rules)

fun boogie_all_tac ctxt rules =
  PARALLEL_GOALS (HEADGOAL (boogie_tac ctxt rules))

fun boogie_method all =
  Scan.optional Attrib.thms [] >> (fn thms => fn ctxt => METHOD (fn facts =>
    let val tac = if all then boogie_all_tac else HEADGOAL oo boogie_tac
    in tac ctxt (thms @ facts) end))

val setup_boogie = Method.setup @{binding boogie} (boogie_method false)
  ("Applies an SMT solver to the current goal " ^
   "using the current set of Boogie background axioms")

val setup_boogie_all = Method.setup @{binding boogie_all} (boogie_method true)
  ("Applies an SMT solver to all goals " ^
   "using the current set of Boogie background axioms")


local
  fun prep_tac facts =
    Method.insert_tac facts
    THEN' REPEAT_ALL_NEW
      (Tactic.resolve_tac [@{thm impI}, @{thm conjI}, @{thm TrueI}]
       ORELSE' Tactic.etac @{thm conjE})

  val drop_assert_at = Conv.concl_conv ~1 (Conv.try_conv (Conv.arg_conv
    (Conv.rewr_conv assert_at_def)))

  fun case_name_of t =
    (case HOLogic.dest_Trueprop (Logic.strip_imp_concl t) of
      @{term assert_at} $ Free (n, _) $ _ => n
    | _ => raise TERM ("case_name_of", [t]))

  fun boogie_cases ctxt = METHOD_CASES (fn facts =>
    ALLGOALS (prep_tac facts) #>
    Seq.maps (fn st =>
      st
      |> ALLGOALS (CONVERSION drop_assert_at)
      |> Seq.map (pair (map (rpair [] o case_name_of) (Thm.prems_of st)))) #>
    Seq.maps (fn (names, st) =>
      CASES
        (Rule_Cases.make_common
          (ProofContext.theory_of ctxt,
           Thm.prop_of (Rule_Cases.internalize_params st)) names)
        Tactical.all_tac st))
in
val setup_boogie_cases = Method.setup @{binding boogie_cases}
  (Scan.succeed boogie_cases)
  "Prepares a set of Boogie assertions for case-based proofs"
end


val setup =
  setup_boogie #>
  setup_boogie_all #>
  setup_boogie_cases

end
