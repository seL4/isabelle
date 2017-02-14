(*  Title:      Provers/Arith/cancel_simprocs.ML
    Author:     Mathias Fleury, MPII
    Copyright   2017

Base on:
    Title:      Provers/Arith/nat_numeral_simprocs.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Cancelation simprocs declaration.
*)

signature CANCEL_SIMPROCS =
sig
  val eq_cancel: Proof.context -> cterm -> thm option
  val less_cancel: Proof.context -> cterm -> thm option
  val less_eq_cancel: Proof.context -> cterm -> thm option
  val diff_cancel: Proof.context -> cterm -> thm option
end;

structure Cancel_Simprocs : CANCEL_SIMPROCS =
struct

structure Eq_Cancel_Comm_Monoid_add = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin @{const_name HOL.eq} dummyT
  val bal_add1 = @{thm iterate_add_eq_add_iff1} RS trans
  val bal_add2 = @{thm iterate_add_eq_add_iff2} RS trans
);

structure Eq_Cancel_Comm_Monoid_less = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_binrel @{const_name Orderings.less}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less} dummyT
  val bal_add1 = @{thm iterate_add_less_iff1} RS trans
  val bal_add2 = @{thm iterate_add_less_iff2} RS trans
);

structure Eq_Cancel_Comm_Monoid_less_eq = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_binrel @{const_name Orderings.less_eq}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less_eq} dummyT
  val bal_add1 = @{thm iterate_add_less_eq_iff1} RS trans
  val bal_add2 = @{thm iterate_add_less_eq_iff2} RS trans
);

structure Diff_Cancel_Comm_Monoid_less_eq = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_binop @{const_name Groups.minus}
  val dest_bal = HOLogic.dest_bin @{const_name Groups.minus} dummyT
  val bal_add1 = @{thm iterate_add_add_eq1} RS trans
  val bal_add2 = @{thm iterate_add_diff_add_eq2} RS trans
);

val eq_cancel = Eq_Cancel_Comm_Monoid_add.proc;
val less_cancel = Eq_Cancel_Comm_Monoid_less.proc;
val less_eq_cancel = Eq_Cancel_Comm_Monoid_less_eq.proc;
val diff_cancel = Diff_Cancel_Comm_Monoid_less_eq.proc;

end
