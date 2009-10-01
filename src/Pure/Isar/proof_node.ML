(*  Title:      Pure/Isar/proof_node.ML
    Author:     Makarius

Proof nodes with linear position and backtracking.
*)

signature PROOF_NODE =
sig
  type T
  val init: Proof.state -> T
  val current: T -> Proof.state
  val position: T -> int
  val back: T -> T
  val applys: (Proof.state -> Proof.state Seq.seq) -> T -> T
  val apply: (Proof.state -> Proof.state) -> T -> T
end;

structure ProofNode: PROOF_NODE =
struct

(* datatype *)

datatype T = ProofNode of
  (Proof.state *                (*first result*)
   Proof.state Seq.seq) *       (*alternative results*)
  int;                          (*linear proof position*)

fun init st = ProofNode ((st, Seq.empty), 0);

fun current (ProofNode ((st, _), _)) = st;
fun position (ProofNode (_, n)) = n;


(* backtracking *)

fun back (ProofNode ((_, stq), n)) =
  (case Seq.pull stq of
    NONE => error "back: no alternatives"
  | SOME res => ProofNode (res, n));


(* apply transformer *)

fun applys f (ProofNode ((st, _), n)) =
  (case Seq.pull (f st) of
    NONE => error "empty result sequence -- proof command failed"
  | SOME res => ProofNode (res, n + 1));

fun apply f = applys (Seq.single o f);

end;
