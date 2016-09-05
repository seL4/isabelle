(* Author: Mathias Fleury, MPII


Simprocs for multisets, based on Larry Paulson's simprocs for
natural numbers and numerals.
*)

signature MULTISET_SIMPROCS =
sig
  val eq_cancel_msets: Proof.context -> cterm -> thm option
  val subset_cancel_msets: Proof.context -> cterm -> thm option
  val subseteq_cancel_msets: Proof.context -> cterm -> thm option
  val diff_cancel_msets: Proof.context -> cterm -> thm option
end;

structure Multiset_Simprocs : MULTISET_SIMPROCS =
struct

structure EqCancelMultiset = CancelNumeralsFun
 (open Multiset_Cancel_Common
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin @{const_name HOL.eq} dummyT
  val bal_add1 = @{thm mset_eq_add_iff1} RS trans
  val bal_add2 = @{thm mset_eq_add_iff2} RS trans
);

structure SubsetCancelMultiset = CancelNumeralsFun
 (open Multiset_Cancel_Common
  val mk_bal   = HOLogic.mk_binrel @{const_name subset_mset}
  val dest_bal = HOLogic.dest_bin @{const_name subset_mset} dummyT
  val bal_add1 = @{thm mset_subset_add_iff1} RS trans
  val bal_add2 = @{thm mset_subset_add_iff2} RS trans
);

structure SubseteqCancelMultiset = CancelNumeralsFun
 (open Multiset_Cancel_Common
  val mk_bal   = HOLogic.mk_binrel @{const_name subseteq_mset}
  val dest_bal = HOLogic.dest_bin @{const_name subseteq_mset} dummyT
  val bal_add1 = @{thm mset_subseteq_add_iff1} RS trans
  val bal_add2 = @{thm mset_subseteq_add_iff2} RS trans
);

structure DiffCancelMultiset = CancelNumeralsFun
 (open Multiset_Cancel_Common
  val mk_bal   = HOLogic.mk_binop @{const_name Groups.minus}
  val dest_bal = HOLogic.dest_bin @{const_name Groups.minus} dummyT
  val bal_add1 = @{thm mset_diff_add_eq1} RS trans
  val bal_add2 = @{thm mset_diff_add_eq2} RS trans
);

val eq_cancel_msets = EqCancelMultiset.proc;
val subset_cancel_msets = SubsetCancelMultiset.proc;
val subseteq_cancel_msets = SubseteqCancelMultiset.proc;
val diff_cancel_msets = DiffCancelMultiset.proc;

end
