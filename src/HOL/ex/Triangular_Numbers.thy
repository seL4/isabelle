(*
  Title:     HOL/ex/Triangular_Numbers.thy
  Author:    Manuel Eberl, TU München
*)
section \<open>Triangular Numbers\<close>
theory Triangular_Numbers
  imports Complex_Main
begin

definition triangle_num :: "nat \<Rightarrow> nat" where
  "triangle_num n = (n * (n + 1)) div 2"

lemma real_triangle_num:
  "real (triangle_num n) = real n * (real n + 1) / 2"
  by (simp add: triangle_num_def field_char_0_class.of_nat_div algebra_simps)

lemma triangle_num_altdef: "triangle_num n = (\<Sum>k\<le>n. k)"
  by (induction n) (auto simp: triangle_num_def)


lemma triangle_num_ge: "triangle_num n \<ge> n"
  unfolding triangle_num_altdef by (rule member_le_sum) auto

lemma triangle_num_Suc: "triangle_num (Suc n) = triangle_num n + Suc n"
  by (simp add: triangle_num_altdef)

lemma triangle_num_0 [simp]: "triangle_num 0 = 0"
  and triangle_num_1 [simp]: "triangle_num 1 = 1"
  by (simp_all add: triangle_num_def)

lemma triangle_num_numeral [simp]:
  "triangle_num (numeral n) = fst (divmod (n * Num.inc n) (Num.Bit0 Num.One))"
  unfolding fst_divmod numeral_mult numeral_inc triangle_num_def ..

lemma triangle_num_eq_0_iff [simp]: "triangle_num n = 0 \<longleftrightarrow> n = 0"
  using triangle_num_ge[of n] by auto

lemma triangle_num_gt_0_iff [simp]: "triangle_num n > 0 \<longleftrightarrow> n > 0"
  using triangle_num_eq_0_iff[of n] by linarith


lemma strict_mono_triangle_num: "strict_mono triangle_num"
  unfolding strict_mono_Suc_iff by (auto simp: triangle_num_altdef)

lemma triangle_num_le: "m \<le> n \<Longrightarrow> triangle_num m \<le> triangle_num n"
  using strict_mono_leD[OF strict_mono_triangle_num] .

lemma triangle_num_less: "m < n \<Longrightarrow> triangle_num m < triangle_num n"
  using strict_monoD[OF strict_mono_triangle_num] .

lemma triangle_num_less_iff: "triangle_num m < triangle_num n \<longleftrightarrow> m < n"
  using strict_mono_less[OF strict_mono_triangle_num] .

lemma triangle_num_le_iff: "triangle_num m \<le> triangle_num n \<longleftrightarrow> m \<le> n"
  using strict_mono_less_eq[OF strict_mono_triangle_num] .

lemma triangle_num_eq_iff: "triangle_num m = triangle_num n \<longleftrightarrow> m = n"
  using strict_mono_eq[OF strict_mono_triangle_num] .


theorem inverse_triangle_num_sums: "(\<lambda>n. 1 / triangle_num (Suc n)) sums 2"
proof -
  have "(\<lambda>n. inverse (real (Suc n)) - inverse (real (Suc (Suc n)))) sums
          (inverse (real (Suc 0)) - 0)"
    by (intro telescope_sums' LIMSEQ_inverse_real_of_nat)
  also have "(\<lambda>n. inverse (real (Suc n)) - inverse (real (Suc (Suc n)))) =
               (\<lambda>n. 1 / real (2 * triangle_num (Suc n)))"
    by (auto simp: field_simps triangle_num_def)
  also have "inverse (real (Suc 0)) - 0 = 1"
    by simp
  finally have "(\<lambda>n. 2 * (1 / real (2 * triangle_num (Suc n)))) sums (2 * 1)"
    by (intro sums_mult)
  thus ?thesis by simp
qed

end