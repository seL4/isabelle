(*  Title:      HOL/Tools/SMT/alethe/verit_replay.ML
    Author:     Mathias Fleury, MPII

VeriT proof parsing and replay.
*)

signature VERIT_REPLAY =
sig
  val replay: Proof.context -> SMT_Translate.replay_data -> string list -> thm
end;

structure Verit_Replay: VERIT_REPLAY =
struct

val replay = Alethe_Replay.replay "veriT" Verit_Replay_Methods.method_for

end
