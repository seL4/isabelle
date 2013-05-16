(*  Title:      Pure/Tools/proof_general_pure.ML
    Author:     David Aspinall
    Author:     Makarius

Proof General preferences for Isabelle/Pure.
*)

(* display *)

val _ =
  ProofGeneral.preference_option ProofGeneral.category_display
    NONE
    @{option show_types}
    "show-types"
    "Include types in display of Isabelle terms";

val _ =
  ProofGeneral.preference_option ProofGeneral.category_display
    NONE
    @{option show_sorts}
    "show-sorts"
    "Include sorts in display of Isabelle types";

val _ =
  ProofGeneral.preference_option ProofGeneral.category_display
    NONE
    @{option show_consts}
    "show-consts"
    "Show types of consts in Isabelle goal display";

val _ =
  ProofGeneral.preference_option ProofGeneral.category_display
    NONE
    @{option names_long}
    "long-names"
    "Show fully qualified names in Isabelle terms";

val _ =
  ProofGeneral.preference_option ProofGeneral.category_display
    NONE
    @{option show_brackets}
    "show-brackets"
    "Show full bracketing in Isabelle terms";

val _ =
  ProofGeneral.preference_option ProofGeneral.category_display
    NONE
    @{option show_main_goal}
    "show-main-goal"
    "Show main goal in proof state display";

val _ =
  ProofGeneral.preference_option ProofGeneral.category_display
    NONE
    @{option eta_contract}
    "eta-contract"
    "Print terms eta-contracted";


(* advanced display *)

val _ =
  ProofGeneral.preference_option ProofGeneral.category_advanced_display
    NONE
    @{option goals_limit}
    "goals-limit"
    "Setting for maximum number of subgoals to be printed";

val _ =
  ProofGeneral.preference ProofGeneral.category_advanced_display
    NONE
    (Markup.print_int o get_print_depth)
    (print_depth o Markup.parse_int)
    ProofGeneral.pgipint
    "print-depth"
    "Setting for the ML print depth";

val _ =
  ProofGeneral.preference_option ProofGeneral.category_advanced_display
    NONE
    @{option show_question_marks}
    "show-question-marks"
    "Show leading question mark of variable name";


(* tracing *)

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_tracing
    NONE
    Raw_Simplifier.simp_trace_default
    "trace-simplifier"
    "Trace simplification rules";

val _ =
  ProofGeneral.preference_int ProofGeneral.category_tracing
    NONE
    Raw_Simplifier.simp_trace_depth_limit_default
    "trace-simplifier-depth"
    "Trace simplifier depth limit";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_tracing
    NONE
    Pattern.trace_unify_fail
    "trace-unification"
    "Output error diagnostics during unification";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_tracing
    NONE
    Toplevel.timing
    "global-timing"
    "Whether to enable timing in Isabelle";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_tracing
    NONE
    Toplevel.debug
    "debugging"
    "Whether to enable debugging";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_tracing
    NONE
    ProofGeneral.thm_deps
    "theorem-dependencies"
    "Track theorem dependencies within Proof General";


(* proof *)

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_proof
    (SOME "true")
    quick_and_dirty
    "quick-and-dirty"
    "Take a few short cuts";

val _ =
  ProofGeneral.preference_bool ProofGeneral.category_proof
    NONE
    Goal.skip_proofs
    "skip-proofs"
    "Skip over proofs";

val _ =
  ProofGeneral.preference ProofGeneral.category_proof
    NONE
    (Markup.print_bool o Proofterm.proofs_enabled)
    (fn s => Proofterm.proofs := (if Markup.parse_bool s then 2 else 1))
    ProofGeneral.pgipbool
    "full-proofs"
    "Record full proof objects internally";

val _ =
  ProofGeneral.preference_int ProofGeneral.category_proof
    NONE
    Multithreading.max_threads
    "max-threads"
    "Maximum number of threads";

val _ =
  ProofGeneral.preference ProofGeneral.category_proof
    NONE
    (fn () => Markup.print_bool (! Goal.parallel_proofs >= 1))
    (fn s => Goal.parallel_proofs := (if Markup.parse_bool s then 1 else 0))
    ProofGeneral.pgipbool
    "parallel-proofs"
    "Check proofs in parallel";

