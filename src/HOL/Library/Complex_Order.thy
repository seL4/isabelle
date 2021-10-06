(*
  Title:    HOL/Library/Complex_Order.thy
  Author:   Dominique Unruh, University of Tartu

  Instantiation of complex numbers as an ordered set.
*)

theory Complex_Order
  imports Complex_Main
begin

instantiation complex :: order begin

definition \<open>x < y \<longleftrightarrow> Re x < Re y \<and> Im x = Im y\<close>
definition \<open>x \<le> y \<longleftrightarrow> Re x \<le> Re y \<and> Im x = Im y\<close>

instance
  apply standard
  by (auto simp: less_complex_def less_eq_complex_def complex_eq_iff)
end

lemma nonnegative_complex_is_real: \<open>(x::complex) \<ge> 0 \<Longrightarrow> x \<in> \<real>\<close>
  by (simp add: complex_is_Real_iff less_eq_complex_def)

lemma complex_is_real_iff_compare0: \<open>(x::complex) \<in> \<real> \<longleftrightarrow> x \<le> 0 \<or> x \<ge> 0\<close>
  using complex_is_Real_iff less_eq_complex_def by auto

instance complex :: ordered_comm_ring
  apply standard
  by (auto simp: less_complex_def less_eq_complex_def complex_eq_iff mult_left_mono mult_right_mono)

instance complex :: ordered_real_vector
  apply standard
  by (auto simp: less_complex_def less_eq_complex_def mult_left_mono mult_right_mono)

instance complex :: ordered_cancel_comm_semiring
  by standard

end
