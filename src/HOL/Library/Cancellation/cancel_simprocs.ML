(*  Title:      HOL/Library/Cancellation/cancel_simprocs.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Mathias Fleury, MPII

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
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>HOL.eq\<close> dummyT
  val bal_add1 = @{thm iterate_add_eq_add_iff1} RS trans
  val bal_add2 = @{thm iterate_add_eq_add_iff2} RS trans
);

structure Eq_Cancel_Comm_Monoid_less = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_binrel \<^const_name>\<open>Orderings.less\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Orderings.less\<close> dummyT
  val bal_add1 = @{thm iterate_add_less_iff1} RS trans
  val bal_add2 = @{thm iterate_add_less_iff2} RS trans
);

structure Eq_Cancel_Comm_Monoid_less_eq = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_binrel \<^const_name>\<open>Orderings.less_eq\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Orderings.less_eq\<close> dummyT
  val bal_add1 = @{thm iterate_add_less_eq_iff1} RS trans
  val bal_add2 = @{thm iterate_add_less_eq_iff2} RS trans
);

structure Diff_Cancel_Comm_Monoid_less_eq = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_binop \<^const_name>\<open>Groups.minus\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Groups.minus\<close> dummyT
  val bal_add1 = @{thm iterate_add_add_eq1} RS trans
  val bal_add2 = @{thm iterate_add_diff_add_eq2} RS trans
);

val eq_cancel = Eq_Cancel_Comm_Monoid_add.proc;
val less_cancel = Eq_Cancel_Comm_Monoid_less.proc;
val less_eq_cancel = Eq_Cancel_Comm_Monoid_less_eq.proc;
val diff_cancel = Diff_Cancel_Comm_Monoid_less_eq.proc;

end
