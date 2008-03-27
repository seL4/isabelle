(*  Title:      Pure/Isar/skip_proof.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Skipping proofs -- quick_and_dirty mode.
*)

signature SKIP_PROOF =
sig
  val make_thm: theory -> term -> thm
  val cheat_tac: theory -> tactic
  val prove: Proof.context -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
end;

structure SkipProof: SKIP_PROOF =
struct

(* oracle setup *)

exception SkipProof of term;

fun skip_proof (_, SkipProof prop) =
  if ! quick_and_dirty then prop
  else error "Proof may be skipped in quick_and_dirty mode only!";

val _ = Context.>> (Theory.add_oracle ("skip_proof", skip_proof));


(* basic cheating *)

fun make_thm thy prop =
  Thm.invoke_oracle_i thy "Pure.skip_proof" (thy, SkipProof prop);

fun cheat_tac thy st =
  ALLGOALS (Tactic.rtac (make_thm thy (Var (("A", 0), propT)))) st;

fun prove ctxt xs asms prop tac =
  Goal.prove ctxt xs asms prop (fn args => fn st =>
    if ! quick_and_dirty
    then setmp quick_and_dirty true (cheat_tac (ProofContext.theory_of ctxt)) st
    else tac args st);

end;
