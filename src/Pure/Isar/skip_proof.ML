(*  Title:      Pure/Isar/skip_proof.ML
    Author:     Markus Wenzel, TU Muenchen

Skipping proofs -- via oracle (in quick and dirty mode) or by forking
(parallel mode).
*)

signature SKIP_PROOF =
sig
  val make_thm: theory -> term -> thm
  val cheat_tac: theory -> tactic
  val prove: Proof.context -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
  val prove_global: theory -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
end;

structure Skip_Proof: SKIP_PROOF =
struct

(* oracle setup *)

val (_, skip_proof) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (Binding.name "skip_proof", fn (thy, prop) => Thm.cterm_of thy prop)));


(* basic cheating *)

fun make_thm thy prop = skip_proof (thy, prop);

fun cheat_tac thy st =
  ALLGOALS (Tactic.rtac (make_thm thy (Var (("A", 0), propT)))) st;

fun prove ctxt xs asms prop tac =
  (if Goal.future_enabled () then Goal.prove_future else Goal.prove) ctxt xs asms prop
    (fn args => fn st =>
      if ! quick_and_dirty
      then cheat_tac (ProofContext.theory_of ctxt) st
      else tac args st);

fun prove_global thy xs asms prop tac =
  Drule.standard (prove (ProofContext.init thy) xs asms prop tac);

end;
