(*  Title:      Pure/Isar/skip_proof.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Skipping proofs -- quick_and_dirty mode.
*)

signature SKIP_PROOF =
sig
  val quick_and_dirty: bool ref
  val make_thm: theory -> term -> thm
  val cheat_tac: theory -> tactic
  val prove: theory -> string list -> term list -> term -> (thm list -> tactic) -> thm
  val local_skip_proof: ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val global_skip_proof: Proof.state -> theory * {kind: string, name: string, thm: thm}
  val setup: (theory -> theory) list
end;

structure SkipProof: SKIP_PROOF =
struct


(* quick_and_dirty *)

(*if true then some packages will OMIT SOME PROOFS*)
val quick_and_dirty = ref false;


(* oracle setup *)

val skip_proofN = "skip_proof";

exception SkipProof of term;

fun skip_proof (_, SkipProof t) =
  if ! quick_and_dirty then t
  else error "Proofs may be skipped in quick_and_dirty mode only!";

val setup = [Theory.add_oracle (skip_proofN, skip_proof)];


(* basic cheating *)

fun make_thm thy t =
  (*dynamic scoping of the oracle, cannot even qualify the name due to Pure/CPure!*)
  Thm.invoke_oracle thy skip_proofN (Theory.sign_of thy, SkipProof t);

fun cheat_tac thy st =
  ALLGOALS (Tactic.rtac (make_thm thy (Var (("A", 0), propT)))) st;

fun prove thy xs asms prop tac =
  Tactic.prove (Theory.sign_of thy) xs asms prop
    (if ! quick_and_dirty then (K (cheat_tac thy)) else tac);


(* "sorry" proof command *)

fun cheating ctxt = Method.METHOD (K (cheat_tac (ProofContext.theory_of ctxt)));

val local_skip_proof = Method.local_terminal_proof (Method.Basic cheating, None);
val global_skip_proof = Method.global_terminal_proof (Method.Basic cheating, None);

end;


val quick_and_dirty = SkipProof.quick_and_dirty;
