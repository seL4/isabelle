(* Author: Mathias Fleury, MPII


Simprocs for multisets ordering, based on the simprocs for nat numerals.
*)

signature MULTISET_ORDER_SIMPROCS =
sig
  val less_cancel_msets: Proof.context -> cterm -> thm option
  val le_cancel_msets: Proof.context -> cterm -> thm option
end;

structure Multiset_Order_Simprocs : MULTISET_ORDER_SIMPROCS =
struct

structure LessCancelMultiset = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_binrel @{const_name Orderings.less}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less} dummyT
  val bal_add1 = @{thm mset_less_add_iff1[unfolded repeat_mset_iterate_add]} RS trans
  val bal_add2 = @{thm mset_less_add_iff2[unfolded repeat_mset_iterate_add]} RS trans
);

structure LeCancelMultiset = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_binrel @{const_name Orderings.less_eq}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less_eq} dummyT
  val bal_add1 = @{thm mset_le_add_iff1[unfolded repeat_mset_iterate_add]} RS trans
  val bal_add2 = @{thm mset_le_add_iff2[unfolded repeat_mset_iterate_add]} RS trans
);

val less_cancel_msets = LessCancelMultiset.proc;
val le_cancel_msets = LeCancelMultiset.proc;

end
