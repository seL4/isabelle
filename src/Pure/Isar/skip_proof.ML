(*  Title:      Pure/Isar/skip_proof.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Skipping proofs -- quick_and_dirty mode.
*)

signature SKIP_PROOF =
sig
  val quick_and_dirty: bool ref
  val local_skip_proof: ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val global_skip_proof: Proof.state -> theory * {kind: string, name: string, thm: thm}
  val prove_goalw_cterm: theory -> thm list -> cterm -> (thm list -> tactic list) -> thm
  val setup: (theory -> theory) list
end;

structure SkipProof: SKIP_PROOF =
struct


(* quick_and_dirty *)

(*if true then some packages will OMIT SOME PROOFS*)
val quick_and_dirty = ref false;


(* cheat_tac *)

val skip_proofN = "skip_proof";

exception SkipProof;
val any_prop = Var (("A", 0), propT);

fun any_thm (_, SkipProof) =
  if ! quick_and_dirty then any_prop
  else error "Proofs may be skipped in quick_and_dirty mode only!";


(*too bad -- dynamic scoping of the oracle, cannot even qualify the name*)
fun cheat_tac thy st =
  ALLGOALS (Tactic.rtac (Thm.invoke_oracle thy skip_proofN (Theory.sign_of thy, SkipProof))) st;


(* "sorry" proof command *)

fun cheating ctxt = Method.METHOD (K (cheat_tac (ProofContext.theory_of ctxt)));

val local_skip_proof = Method.local_terminal_proof (Method.Basic cheating, None);
val global_skip_proof = Method.global_terminal_proof (Method.Basic cheating, None);


(* conditional prove_goalw_cterm *)

fun prove_goalw_cterm thy rews ct tacs =
  Goals.prove_goalw_cterm rews ct
    (if ! quick_and_dirty then (K [cheat_tac thy]) else tacs);


(* theory setup *)

val setup = [Theory.add_oracle (skip_proofN, any_thm)];


end;


val quick_and_dirty = SkipProof.quick_and_dirty;
