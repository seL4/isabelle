(*  Title:      HOL/Tools/SMT/alethe/alethe_strategies.ML
    Author:     Mathias Fleury, ENS Rennes, MPI, JKU, University of Freiburg
    Author:     Hanna Lachnitt, Stanford University

Alethe strategies: option portfolio to call solvers with

*)

signature ALETHE_STRATEGIES =
sig
  (*Strategy related*)
  val smt_solver_strategy : string Config.T
  val smt_solver_current_strategy : string -> Context.generic -> string list
  val veriT_current_strategy : Context.generic -> string list
  val cvc5_current_strategy : Context.generic -> string list
  val all_smt_solver_stgies: string -> Context.generic -> string list;
  val all_veriT_stgies: Context.generic -> string list;
  val all_cvc5_stgies: Context.generic -> string list;

  val select_smt_solver_stgy: string -> string -> Context.generic -> Context.generic;
  val select_veriT_stgy: string -> Context.generic -> Context.generic;
  val valid_smt_solver_stgy: string -> string -> Context.generic -> bool;
  val smt_solver_add_stgy: (string * string) * string list -> Context.generic -> Context.generic
  val smt_solver_rm_stgy: string -> string -> Context.generic -> Context.generic

  (*Global tactic*)
  val verit_tac: Proof.context -> thm list -> int -> tactic
  val verit_tac_stgy: string -> Proof.context -> thm list -> int -> tactic
  val cvc5_tac: Proof.context -> thm list -> int -> tactic
  val cvc5_tac_stgy: string -> Proof.context -> thm list -> int -> tactic
end;

structure Alethe_Strategies: ALETHE_STRATEGIES =
struct

val verit_strategy_default_name = "default"; (*FUDGE*)
val verit_strategy_del_insts_name = "del_insts"; (*FUDGE*)
val verit_strategy_rm_insts_name = "ccfv_SIG"; (*FUDGE*)
val verit_strategy_ccfv_insts_name = "ccfv_threshold"; (*FUDGE*)
val verit_strategy_best_name = "best"; (*FUDGE*)

val verit_strategy_best = ["--index-sorts", "--index-fresh-sorts", "--triggers-new",
  "--triggers-sel-rm-specific"];
val verit_strategy_del_insts = ["--index-sorts", "--index-fresh-sorts", "--ccfv-breadth",
  "--inst-deletion", "--index-SAT-triggers", "--inst-deletion-loops", "--inst-deletion-track-vars",
  "--inst-deletion", "--index-SAT-triggers"];
val verit_strategy_rm_insts = ["--index-SIG", "--triggers-new", "--triggers-sel-rm-specific"];
val verit_strategy_ccfv_insts = ["--index-sorts", "--index-fresh-sorts", "--triggers-new",
  "--triggers-sel-rm-specific", "--triggers-restrict-combine", "--inst-deletion",
  "--index-SAT-triggers", "--inst-deletion-loops", "--inst-deletion-track-vars", "--inst-deletion",
  "--index-SAT-triggers", "--inst-sorts-threshold=100000", "--ematch-exp=10000000",
  "--ccfv-index=100000", "--ccfv-index-full=1000"]

(*
We obtained these strategies by probing cvc5 for its SMT-COMP portfolio
for some Isabelle generated problems from the 17 provers benchmark set using
--portfolio-dry-run --use-portfolio.  This resulted in 31 strategies.
Running the strategy on a benchmark with the option --safe-mode=safe, we obtain the options that
have a low count of holes, leaving 23 strategies.
Then, using Mirabelle we extracted goals that could not be solved by internal proof methods
(i.e., call to the smt method) and evaluated the remaining strategies. The focus is on having a
good portfolio, not several strategies that are fast on the same goals. 14 strategies did not
provide a benefit on our benchmark set containing around 480 goals originating from a part of
HOL-Library and two AFP entries (Simplex and Ordered_Resolution_Prover).
While best completely outperformed the remaining 7 strategies, there were some uniquely solved goals
by those so we picked the 4 whose combination resulted in the most goals solved.

Note: we always use --enum-inst at the moment because otherwise cvc5 will answer unknown too often.
Note: --full-saturate-quant is an alias of --enum-inst, which the cvc5 devs prefer we use.
Note: the results of this could be different if different strategies are picked for finding and
minimizing the proof in smt_systems.ML and should be re-run.
*)
val cvc5_stgy_default_name = "best"
val cvc5_stgy_default_insts = []
val cvc5_stgy_no_ematching_name ="no_ematching"
val cvc5_stgy_no_ematching = ["--no-e-matching"]
val cvc5_stgy_trigger_multi_name = "trigger_multi"
val cvc5_stgy_trigger_multi = ["--multi-trigger-when-single"]
val cvc5_stgy_dec_internal_enum_inst_sum_name ="dec_internal_enum_inst_sum"
val cvc5_stgy_dec_internal_enum_inst_sum = ["--decision=internal", "--enum-inst", "--enum-inst-sum"]
val cvc5_stgy_term_enum_inst_interleave_name= "interleave"
val cvc5_stgy_term_enum_inst_interleave = ["--enum-inst-interleave"]

val verit_strategy_default = [];

type verit_strategy = {default_strategy: string, strategies: ((string * string) * string list) list}
fun mk_verit_strategy default_strategy strategies : verit_strategy = {default_strategy=default_strategy,strategies=strategies}

val verit_name = "verit"
val cvc5_name = "cvc5_proof"
val empty_data = mk_verit_strategy verit_strategy_best_name
  [((verit_name, verit_strategy_default_name), verit_strategy_default),
   ((verit_name, verit_strategy_del_insts_name), verit_strategy_del_insts),
   ((verit_name, verit_strategy_rm_insts_name), verit_strategy_rm_insts),
   ((verit_name, verit_strategy_ccfv_insts_name), verit_strategy_ccfv_insts),
   ((verit_name, verit_strategy_best_name), verit_strategy_best),

   ((cvc5_name, cvc5_stgy_default_name), cvc5_stgy_default_insts),
   ((cvc5_name, cvc5_stgy_no_ematching_name), cvc5_stgy_no_ematching),
   ((cvc5_name, cvc5_stgy_trigger_multi_name), cvc5_stgy_trigger_multi),
   ((cvc5_name, cvc5_stgy_term_enum_inst_interleave_name), cvc5_stgy_term_enum_inst_interleave),
   ((cvc5_name, cvc5_stgy_dec_internal_enum_inst_sum_name), cvc5_stgy_dec_internal_enum_inst_sum)
]

fun merge_data ({strategies=strategies1,...}:verit_strategy,
    {default_strategy,strategies=strategies2}:verit_strategy) : verit_strategy =
  mk_verit_strategy default_strategy (AList.merge (op =) (op =) (strategies1, strategies2))

structure Data = Generic_Data
(
  type T = verit_strategy
  val empty = empty_data
  val merge = merge_data
)

fun smt_solver_current_strategy solver ctxt =
  let
    val {default_strategy,strategies} = (Data.get ctxt)
  in
    AList.lookup (op=) strategies (solver, default_strategy)
    |> the
  end

val smt_solver_strategy = Attrib.setup_config_string \<^binding>\<open>smt_verit_strategy\<close> (K verit_strategy_best_name);

fun valid_smt_solver_stgy solver stgy context =
  let
    val {strategies,...} = Data.get context
  in
    AList.defined (op =) strategies (solver, stgy)
  end

fun select_smt_solver_stgy solver stgy context =
  let
    val {strategies,...} = Data.get context
    val upd = Data.map (K (mk_verit_strategy stgy strategies))
  in
    if not (AList.defined (op =) strategies (solver, stgy)) then
      error ("Trying to select unknown " ^ quote solver ^ " strategy: " ^ quote stgy)
    else upd context
  end

val select_veriT_stgy = select_smt_solver_stgy verit_name
val select_cvc5_stgy = select_smt_solver_stgy cvc5_name

fun smt_solver_add_stgy stgy context =
  let
    val {default_strategy,strategies} = Data.get context
  in
    Data.map
      (K (mk_verit_strategy default_strategy (AList.update (op =) stgy strategies)))
      context
  end

fun smt_solver_rm_stgy solver stgy context =
  let
    val {default_strategy,strategies} = Data.get context
  in
    Data.map
      (K (mk_verit_strategy default_strategy (AList.delete (op =) (solver, stgy) strategies)))
      context
  end

fun all_smt_solver_stgies solver context =
  let
    val {strategies,...} = Data.get context
   in
    strategies
    |> map_filter (fn ((solver', name), _) => if solver=solver' then SOME name else NONE)
  end
val all_veriT_stgies = all_smt_solver_stgies verit_name
val all_cvc5_stgies = all_smt_solver_stgies cvc5_name

val veriT_current_strategy = smt_solver_current_strategy verit_name
val cvc5_current_strategy = smt_solver_current_strategy cvc5_name
val select_verit = SMT_Config.select_solver verit_name
fun verit_tac ctxt = SMT_Solver.smt_tac (Context.proof_map select_verit ctxt)
fun verit_tac_stgy stgy ctxt = verit_tac (Context.proof_of (select_veriT_stgy stgy (Context.Proof ctxt)))

val select_cvc5 = SMT_Config.select_solver cvc5_name
fun cvc5_tac ctxt = SMT_Solver.smt_tac (Context.proof_map select_cvc5 ctxt)
fun cvc5_tac_stgy stgy ctxt = cvc5_tac (Context.proof_of (select_cvc5_stgy stgy (Context.Proof ctxt)))

end;
