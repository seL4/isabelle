(*  Title:      Pure/Isar/skip_proof.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Skip subproofs (for quick_and_dirty mode only).
*)

signature SKIP_PROOF =
sig
  val local_skip_proof: ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val global_skip_proof: Proof.state -> theory * {kind: string, name: string, thm: thm}
  val setup: (theory -> theory) list
end;

structure SkipProof: SKIP_PROOF =
struct


(* oracle *)

val skip_proofN = "skip_proof";

exception SkipProof;
val any_prop = Var (("A", 0), propT);

fun any_thm (_, SkipProof) =
  if ! quick_and_dirty then any_prop
  else error "Proofs may be skipped in quick_and_dirty mode only!";


(* proof command *)

fun cheat_meth ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    (*too bad -- dynamic scoping of the oracle, cannot even qualify the name*)
    val thm = Thm.invoke_oracle thy skip_proofN (Theory.sign_of thy, SkipProof);
  in Method.METHOD (fn _ => ALLGOALS (Tactic.rtac thm)) end;

val local_skip_proof = Method.local_terminal_proof (Method.Basic cheat_meth, None);
val global_skip_proof = Method.global_terminal_proof (Method.Basic cheat_meth, None);


(* proof command *)


(* theory setup *)

val setup = [Theory.add_oracle (skip_proofN, any_thm)];


end;
