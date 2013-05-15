(*  Title:      Pure/Tools/proof_general_pure.ML
    Author:     David Aspinall
    Author:     Makarius

Proof General preferences for Isabelle/Pure.
*)

(* display *)

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_display
    Printer.show_types_default
    "show-types"
    "Include types in display of Isabelle terms";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_display
    Printer.show_sorts_default
    "show-sorts"
    "Include sorts in display of Isabelle terms";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_display
    Goal_Display.show_consts_default
    "show-consts"
    "Show types of consts in Isabelle goal display";

val _ =
  ProofGeneral.preference_option ProofGeneral.category_display
    @{option names_long}
    "long-names"
    "Show fully qualified names in Isabelle terms";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_display
    Printer.show_brackets_default
    "show-brackets"
    "Show full bracketing in Isabelle terms";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_display
    Goal_Display.show_main_goal_default
    "show-main-goal"
    "Show main goal in proof state display";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_display
    Syntax_Trans.eta_contract_default
    "eta-contract"
    "Print terms eta-contracted";


(* advanced display *)

val _ =
  ProofGeneral.preference_option ProofGeneral.category_advanced_display
    @{option goals_limit}
    "goals-limit"
    "Setting for maximum number of subgoals to be printed";

val _ =
  ProofGeneral.preference ProofGeneral.category_advanced_display
    (Markup.print_int o get_print_depth)
    (print_depth o Markup.parse_int)
    ProofGeneral.pgipint
    "print-depth"
    "Setting for the ML print depth";

val _ =
  ProofGeneral.preference_option ProofGeneral.category_advanced_display
    @{option show_question_marks}
    "show-question-marks"
    "Show leading question mark of variable name";


(* tracing *)

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_tracing
    Raw_Simplifier.simp_trace_default
    "trace-simplifier"
    "Trace simplification rules";

val _ =
  ProofGeneral.preference_int ProofGeneral.category_tracing
    Raw_Simplifier.simp_trace_depth_limit_default
    "trace-simplifier-depth"
    "Trace simplifier depth limit";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_tracing
    Pattern.trace_unify_fail
    "trace-unification"
    "Output error diagnostics during unification";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_tracing
    Toplevel.timing
    "global-timing"
    "Whether to enable timing in Isabelle";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_tracing
    Toplevel.debug
    "debugging"
    "Whether to enable debugging";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_tracing
    ProofGeneral.thm_deps
    "theorem-dependencies"
    "Track theorem dependencies within Proof General";


(* proof *)

val _ =
  Unsynchronized.setmp quick_and_dirty true (fn () =>
    ProofGeneral.preference_bool ProofGeneral.category_proof
      quick_and_dirty
      "quick-and-dirty"
      "Take a few short cuts") ();

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_proof
    Goal.skip_proofs
    "skip-proofs"
    "Skip over proofs";

val _ =
  Unsynchronized.setmp Proofterm.proofs 1 (fn () =>
    ProofGeneral.preference ProofGeneral.category_proof
      (Markup.print_bool o Proofterm.proofs_enabled)
      (fn s => Proofterm.proofs := (if Markup.parse_bool s then 2 else 1))
      ProofGeneral.pgipbool
      "full-proofs"
      "Record full proof objects internally") ();

val _ =
  Unsynchronized.setmp Multithreading.max_threads 0 (fn () =>
    ProofGeneral.preference_int ProofGeneral.category_proof
      Multithreading.max_threads
      "max-threads"
      "Maximum number of threads") ();

val _ =
  ProofGeneral.preference ProofGeneral.category_proof
    (fn () => Markup.print_bool (! Goal.parallel_proofs >= 1))
    (fn s => Goal.parallel_proofs := (if Markup.parse_bool s then 1 else 0))
    ProofGeneral.pgipbool
    "parallel-proofs"
    "Check proofs in parallel";

