(*  Title:      Pure/deriv.ML
    ID:         $Id$
    Author:     Makarius

Abstract derivations based on raw proof terms.
*)

signature DERIV =
sig
  type T
  val oracle_of: T -> bool
  val proof_of: T -> Proofterm.proof
  val uncond_rule: (Proofterm.proof -> Proofterm.proof) -> T -> T
  val rule0: Proofterm.proof -> T
  val rule1: (Proofterm.proof -> Proofterm.proof) -> T -> T
  val rule2: (Proofterm.proof -> Proofterm.proof -> Proofterm.proof) -> T -> T -> T
  val oracle: string -> term -> T
end;

structure Deriv: DERIV =
struct

datatype T = Der of bool * Proofterm.proof;

fun oracle_of (Der (ora, _)) = ora;
fun proof_of (Der (_, proof)) = proof;

fun uncond_rule f (Der (ora, prf)) = Der (ora, f prf);

fun rule0 prf = Der (Proofterm.infer_derivs' I (false, prf));
fun rule1 f (Der der) = Der (Proofterm.infer_derivs' f der);
fun rule2 f (Der der1) (Der der2) = Der (Proofterm.infer_derivs f der1 der2);

fun oracle name prop = Der (true, Proofterm.oracle_proof name prop);

end;
