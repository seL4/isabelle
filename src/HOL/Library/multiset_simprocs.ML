(* Author: Mathias Fleury, MPII


Simprocs for multisets, based on Larry Paulson's simprocs for
natural numbers and numerals.
*)

signature MULTISET_SIMPROCS =
sig
  val subset_cancel_msets: Proof.context -> cterm -> thm option
  val subseteq_cancel_msets: Proof.context -> cterm -> thm option
end;

structure Multiset_Simprocs : MULTISET_SIMPROCS =
struct

structure Subset_Cancel_Multiset = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_binrel \<^const_name>\<open>subset_mset\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>subset_mset\<close> dummyT
  val bal_add1 = @{thm mset_subset_add_iff1[unfolded repeat_mset_iterate_add]} RS trans
  val bal_add2 = @{thm mset_subset_add_iff2[unfolded repeat_mset_iterate_add]} RS trans
);

structure Subseteq_Cancel_Multiset = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_binrel \<^const_name>\<open>subseteq_mset\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>subseteq_mset\<close> dummyT
  val bal_add1 = @{thm mset_subseteq_add_iff1[unfolded repeat_mset_iterate_add]} RS trans
  val bal_add2 = @{thm mset_subseteq_add_iff2[unfolded repeat_mset_iterate_add]} RS trans
);

val subset_cancel_msets = Subset_Cancel_Multiset.proc;
val subseteq_cancel_msets = Subseteq_Cancel_Multiset.proc;

end
