(*  Title:      HOL/Tools/SMT/alethe/cvc5_replay.ML
    Author:     Mathias Fleury, JKU
    Author:     Hanna Lachnitt, Stanford University

Proof parsing and replay for cvc5.
*)

signature CVC5_REPLAY =
sig
  val replay: Proof.context -> SMT_Translate.replay_data -> string list -> thm
  val cvc_tac: Proof.context -> thm list -> int -> tactic
end;

structure CVC5_Replay: CVC5_REPLAY =
struct

val replay = Alethe_Replay.replay "cvc5_prover" CVC5_Replay_Methods.method_for

val select_cvc = SMT_Config.select_solver "cvc5_proof"
fun cvc_tac ctxt = SMT_Solver.smt_tac (Config.put SMT_Config.native_bv false ((Context.proof_map select_cvc ctxt)))

end
