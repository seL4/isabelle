(*  Title:      HOL/Tools/SMT/verit_strategies.ML
    Author:     Mathias Fleury, ENS Rennes, MPI, JKU, Freiburg University

VeriT proofs: parsing and abstract syntax tree.
*)

signature VERIT_STRATEGIES =
sig
  (*Strategy related*)
  val veriT_strategy : string Config.T
  val veriT_current_strategy : Context.generic -> string list
  val all_veriT_stgies: Context.generic -> string list;

  val select_veriT_stgy: string -> Context.generic -> Context.generic;
  val valid_veriT_stgy: string -> Context.generic -> bool;
  val verit_add_stgy: string * string list -> Context.generic -> Context.generic
  val verit_rm_stgy: string -> Context.generic -> Context.generic

  (*Global tactic*)
  val verit_tac: Proof.context -> thm list -> int -> tactic
  val verit_tac_stgy: string -> Proof.context -> thm list -> int -> tactic
end;

structure Verit_Strategies: VERIT_STRATEGIES =
struct

open SMTLIB_Proof

val veriT_strategy_default_name = "default"; (*FUDGE*)
val veriT_strategy_del_insts_name = "del_insts"; (*FUDGE*)
val veriT_strategy_rm_insts_name = "ccfv_SIG"; (*FUDGE*)
val veriT_strategy_ccfv_insts_name = "ccfv_threshold"; (*FUDGE*)
val veriT_strategy_best_name = "best"; (*FUDGE*)

val veriT_strategy_best = ["--index-sorts", "--index-fresh-sorts", "--triggers-new",
  "--triggers-sel-rm-specific"];
val veriT_strategy_del_insts = ["--index-sorts", "--index-fresh-sorts", "--ccfv-breadth",
  "--inst-deletion", "--index-SAT-triggers", "--inst-deletion-loops", "--inst-deletion-track-vars",
  "--inst-deletion", "--index-SAT-triggers"];
val veriT_strategy_rm_insts = ["--index-SIG", "--triggers-new", "--triggers-sel-rm-specific"];
val veriT_strategy_ccfv_insts = ["--index-sorts", "--index-fresh-sorts", "--triggers-new",
  "--triggers-sel-rm-specific", "--triggers-restrict-combine", "--inst-deletion",
  "--index-SAT-triggers", "--inst-deletion-loops", "--inst-deletion-track-vars", "--inst-deletion",
  "--index-SAT-triggers", "--inst-sorts-threshold=100000", "--ematch-exp=10000000",
  "--ccfv-index=100000", "--ccfv-index-full=1000"]

val veriT_strategy_default = [];

type verit_strategy = {default_strategy: string, strategies: (string * string list) list}
fun mk_verit_strategy default_strategy strategies : verit_strategy = {default_strategy=default_strategy,strategies=strategies}

val empty_data = mk_verit_strategy veriT_strategy_best_name
  [(veriT_strategy_default_name, veriT_strategy_default),
   (veriT_strategy_del_insts_name, veriT_strategy_del_insts),
   (veriT_strategy_rm_insts_name, veriT_strategy_rm_insts),
   (veriT_strategy_ccfv_insts_name, veriT_strategy_ccfv_insts),
   (veriT_strategy_best_name, veriT_strategy_best)]

fun merge_data ({strategies=strategies1,...}:verit_strategy,
    {default_strategy,strategies=strategies2}:verit_strategy) : verit_strategy =
  mk_verit_strategy default_strategy (AList.merge (op =) (op =) (strategies1, strategies2))

structure Data = Generic_Data
(
  type T = verit_strategy
  val empty = empty_data
  val merge = merge_data
)

fun veriT_current_strategy ctxt =
  let
    val {default_strategy,strategies} = (Data.get ctxt)
  in
    AList.lookup (op=) strategies default_strategy
   |> the
  end

val veriT_strategy = Attrib.setup_config_string \<^binding>\<open>smt_verit_strategy\<close> (K veriT_strategy_best_name);

fun valid_veriT_stgy stgy context =
  let
    val {strategies,...} = Data.get context
  in
    AList.defined (op =) strategies stgy
  end

fun select_veriT_stgy stgy context =
  let
    val {strategies,...} = Data.get context
    val upd = Data.map (K (mk_verit_strategy stgy strategies))
  in
    if not (AList.defined (op =) strategies stgy) then
      error ("Trying to select unknown veriT strategy: " ^ quote stgy)
    else upd context
  end

fun verit_add_stgy stgy context =
  let
    val {default_strategy,strategies} = Data.get context
  in
    Data.map
      (K (mk_verit_strategy default_strategy (AList.update (op =) stgy strategies)))
      context
  end

fun verit_rm_stgy stgy context =
  let
    val {default_strategy,strategies} = Data.get context
  in
    Data.map
      (K (mk_verit_strategy default_strategy (AList.delete (op =) stgy strategies)))
      context
  end

fun all_veriT_stgies context =
  let
    val {strategies,...} = Data.get context
   in
    map fst strategies
  end

val select_verit = SMT_Config.select_solver "verit"
fun verit_tac ctxt = SMT_Solver.smt_tac (Config.put SMT_Config.native_bv false ((Context.proof_map select_verit ctxt)))
fun verit_tac_stgy stgy ctxt = verit_tac (Context.proof_of (select_veriT_stgy stgy (Context.Proof ctxt)))

end;
