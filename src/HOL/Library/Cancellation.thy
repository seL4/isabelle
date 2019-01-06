(*  Title:      HOL/Library/Cancellation.thy
    Author:     Mathias Fleury, MPII
    Copyright   2017

This theory defines cancelation simprocs that work on cancel_comm_monoid_add and support the simplification of an operation
that repeats the additions.
*)

theory Cancellation
imports Main
begin

named_theorems cancelation_simproc_pre \<open>These theorems are here to normalise the term. Special
  handling of constructors should be here. Remark that only the simproc @{term NO_MATCH} is also
  included.\<close>

named_theorems cancelation_simproc_post \<open>These theorems are here to normalise the term, after the
  cancelation simproc. Normalisation of \<open>iterate_add\<close> back to the normale representation
  should be put here.\<close>

named_theorems cancelation_simproc_eq_elim \<open>These theorems are here to help deriving contradiction
  (e.g., \<open>Suc _ = 0\<close>).\<close>

definition iterate_add :: \<open>nat \<Rightarrow> 'a::cancel_comm_monoid_add \<Rightarrow> 'a\<close> where
  \<open>iterate_add n a = (((+) a) ^^ n) 0\<close>

lemma iterate_add_simps[simp]:
  \<open>iterate_add 0 a = 0\<close>
  \<open>iterate_add (Suc n) a = a + iterate_add n a\<close>
  unfolding iterate_add_def by auto

lemma iterate_add_empty[simp]: \<open>iterate_add n 0 = 0\<close>
  unfolding iterate_add_def by (induction n) auto

lemma iterate_add_distrib[simp]: \<open>iterate_add (m+n) a = iterate_add m a + iterate_add n a\<close>
  by (induction n) (auto simp: ac_simps)

lemma iterate_add_Numeral1: \<open>iterate_add n Numeral1 = of_nat n\<close>
  by (induction n) auto

lemma iterate_add_1: \<open>iterate_add n 1 = of_nat n\<close>
  using iterate_add_Numeral1 by auto

lemma iterate_add_eq_add_iff1:
  \<open>i \<le> j \<Longrightarrow> (iterate_add j u + m = iterate_add i u + n) = (iterate_add (j - i) u + m = n)\<close>
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_eq_add_iff2:
   \<open>i \<le> j \<Longrightarrow> (iterate_add i u + m = iterate_add j u + n) = (m = iterate_add (j - i) u + n)\<close>
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_less_iff1:
  "j \<le> (i::nat) \<Longrightarrow> (iterate_add i (u:: 'a :: {cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}) + m < iterate_add j u + n) = (iterate_add (i-j) u + m < n)"
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_less_iff2:
  "i \<le> (j::nat) \<Longrightarrow> (iterate_add i (u:: 'a :: {cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}) + m < iterate_add j u + n) = (m <iterate_add (j - i) u + n)"
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_less_eq_iff1:
  "j \<le> (i::nat) \<Longrightarrow> (iterate_add i (u:: 'a :: {cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}) + m \<le> iterate_add j u + n) = (iterate_add (i-j) u + m \<le> n)"
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_less_eq_iff2:
  "i \<le> (j::nat) \<Longrightarrow> (iterate_add i (u:: 'a :: {cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}) + m \<le> iterate_add j u + n) = (m \<le> iterate_add (j - i) u + n)"
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_add_eq1:
  "j \<le> (i::nat) \<Longrightarrow> ((iterate_add i u + m) - (iterate_add j u + n)) = ((iterate_add (i-j) u + m) - n)"
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_diff_add_eq2:
  "i \<le> (j::nat) \<Longrightarrow> ((iterate_add i u + m) - (iterate_add j u + n)) = (m - (iterate_add (j-i) u + n))"
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))


subsection \<open>Simproc Set-Up\<close>

ML_file \<open>Cancellation/cancel.ML\<close>
ML_file \<open>Cancellation/cancel_data.ML\<close>
ML_file \<open>Cancellation/cancel_simprocs.ML\<close>

end

