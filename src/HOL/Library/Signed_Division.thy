(*  Author:  Stefan Berghofer et al.
*)

subsection \<open>Signed division: negative results rounded towards zero rather than minus infinity.\<close>

theory Signed_Division
  imports Main
begin

class signed_division = comm_semiring_1_cancel +
  fixes signed_divide :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>sdiv\<close> 70)
  and signed_modulo :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>smod\<close> 70)
  assumes sdiv_mult_smod_eq: \<open>a sdiv b * b + a smod b = a\<close>
begin

lemma mult_sdiv_smod_eq:
  \<open>b * (a sdiv b) + a smod b = a\<close>
  using sdiv_mult_smod_eq [of a b] by (simp add: ac_simps)

lemma smod_sdiv_mult_eq:
  \<open>a smod b + a sdiv b * b = a\<close>
  using sdiv_mult_smod_eq [of a b] by (simp add: ac_simps)

lemma smod_mult_sdiv_eq:
  \<open>a smod b + b * (a sdiv b) = a\<close>
  using sdiv_mult_smod_eq [of a b] by (simp add: ac_simps)

lemma minus_sdiv_mult_eq_smod:
  \<open>a - a sdiv b * b = a smod b\<close>
  by (rule add_implies_diff [symmetric]) (fact smod_sdiv_mult_eq)

lemma minus_mult_sdiv_eq_smod:
  \<open>a - b * (a sdiv b) = a smod b\<close>
  by (rule add_implies_diff [symmetric]) (fact smod_mult_sdiv_eq)

lemma minus_smod_eq_sdiv_mult:
  \<open>a - a smod b = a sdiv b * b\<close>
  by (rule add_implies_diff [symmetric]) (fact sdiv_mult_smod_eq)

lemma minus_smod_eq_mult_sdiv:
  \<open>a - a smod b = b * (a sdiv b)\<close>
  by (rule add_implies_diff [symmetric]) (fact mult_sdiv_smod_eq)

end

instantiation int :: signed_division
begin

definition signed_divide_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k sdiv l = sgn k * sgn l * (\<bar>k\<bar> div \<bar>l\<bar>)\<close> for k l :: int

definition signed_modulo_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k smod l = sgn k * (\<bar>k\<bar> mod \<bar>l\<bar>)\<close> for k l :: int

instance by standard
  (simp add: signed_divide_int_def signed_modulo_int_def div_abs_eq mod_abs_eq algebra_simps)

end

lemma divide_int_eq_signed_divide_int:
  \<open>k div l = k sdiv l - of_bool (l \<noteq> 0 \<and> sgn k \<noteq> sgn l \<and> \<not> l dvd k)\<close>
  for k l :: int
  by (simp add: div_eq_div_abs [of k l] signed_divide_int_def)

lemma signed_divide_int_eq_divide_int:
  \<open>k sdiv l = k div l + of_bool (l \<noteq> 0 \<and> sgn k \<noteq> sgn l \<and> \<not> l dvd k)\<close>
  for k l :: int
  by (simp add: divide_int_eq_signed_divide_int)

lemma modulo_int_eq_signed_modulo_int:
  \<open>k mod l = k smod l + l * of_bool (sgn k \<noteq> sgn l \<and> \<not> l dvd k)\<close>
  for k l :: int
  by (simp add: mod_eq_mod_abs [of k l] signed_modulo_int_def)

lemma signed_modulo_int_eq_modulo_int:
  \<open>k smod l = k mod l - l * of_bool (sgn k \<noteq> sgn l \<and> \<not> l dvd k)\<close>
  for k l :: int
  by (simp add: modulo_int_eq_signed_modulo_int)

lemma sdiv_int_div_0:
  "(x :: int) sdiv 0 = 0"
  by (clarsimp simp: signed_divide_int_def)

lemma sdiv_int_0_div [simp]:
  "0 sdiv (x :: int) = 0"
  by (clarsimp simp: signed_divide_int_def)

lemma smod_int_alt_def:
     "(a::int) smod b = sgn (a) * (abs a mod abs b)"
  by (fact signed_modulo_int_def)

lemma int_sdiv_simps [simp]:
    "(a :: int) sdiv 1 = a"
    "(a :: int) sdiv 0 = 0"
    "(a :: int) sdiv -1 = -a"
  apply (auto simp: signed_divide_int_def sgn_if)
  done

lemma smod_int_mod_0 [simp]:
  "x smod (0 :: int) = x"
  by (clarsimp simp: signed_modulo_int_def abs_mult_sgn ac_simps)

lemma smod_int_0_mod [simp]:
  "0 smod (x :: int) = 0"
  by (clarsimp simp: smod_int_alt_def)

lemma sgn_sdiv_eq_sgn_mult:
  "a sdiv b \<noteq> 0 \<Longrightarrow> sgn ((a :: int) sdiv b) = sgn (a * b)"
  by (auto simp: signed_divide_int_def sgn_div_eq_sgn_mult sgn_mult)

lemma int_sdiv_same_is_1 [simp]:
    "a \<noteq> 0 \<Longrightarrow> ((a :: int) sdiv b = a) = (b = 1)"
  apply (rule iffI)
   apply (clarsimp simp: signed_divide_int_def)
   apply (subgoal_tac "b > 0")
    apply (case_tac "a > 0")
     apply (clarsimp simp: sgn_if)
  apply (simp_all add: not_less algebra_split_simps sgn_if split: if_splits)
  using int_div_less_self [of a b] apply linarith
    apply (metis add.commute add.inverse_inverse group_cancel.rule0 int_div_less_self linorder_neqE_linordered_idom neg_0_le_iff_le not_less verit_comp_simplify1(1) zless_imp_add1_zle)
   apply (metis div_minus_right neg_imp_zdiv_neg_iff neg_le_0_iff_le not_less order.not_eq_order_implies_strict)
  apply (metis abs_le_zero_iff abs_of_nonneg neg_imp_zdiv_nonneg_iff order.not_eq_order_implies_strict)
  done

lemma int_sdiv_negated_is_minus1 [simp]:
    "a \<noteq> 0 \<Longrightarrow> ((a :: int) sdiv b = - a) = (b = -1)"
  apply (clarsimp simp: signed_divide_int_def)
  apply (rule iffI)
   apply (subgoal_tac "b < 0")
    apply (case_tac "a > 0")
     apply (clarsimp simp: sgn_if algebra_split_simps not_less)
     apply (case_tac "sgn (a * b) = -1")
      apply (simp_all add: not_less algebra_split_simps sgn_if split: if_splits)
     apply (metis add.inverse_inverse int_div_less_self int_one_le_iff_zero_less less_le neg_0_less_iff_less)
    apply (metis add.inverse_inverse div_minus_right int_div_less_self int_one_le_iff_zero_less less_le neg_0_less_iff_less)
   apply (metis less_le neg_less_0_iff_less not_less pos_imp_zdiv_neg_iff)
  apply (metis div_minus_right dual_order.eq_iff neg_imp_zdiv_nonneg_iff neg_less_0_iff_less)
  done

lemma sdiv_int_range:
  \<open>a sdiv b \<in> {- \<bar>a\<bar>..\<bar>a\<bar>}\<close> for a b :: int
  using zdiv_mono2 [of \<open>\<bar>a\<bar>\<close> 1 \<open>\<bar>b\<bar>\<close>]
  by (cases \<open>b = 0\<close>; cases \<open>sgn b = sgn a\<close>)
     (auto simp add: signed_divide_int_def pos_imp_zdiv_nonneg_iff
     dest!: sgn_not_eq_imp intro: order_trans [of _ 0])

lemma smod_int_range:
  \<open>a smod b \<in> {- \<bar>b\<bar> + 1..\<bar>b\<bar> - 1}\<close>
  if \<open>b \<noteq> 0\<close> for a b :: int
proof -
  define m n where \<open>m = nat \<bar>a\<bar>\<close> \<open>n = nat \<bar>b\<bar>\<close>
  then have \<open>\<bar>a\<bar> = int m\<close> \<open>\<bar>b\<bar> = int n\<close>
    by simp_all
  with that have \<open>n > 0\<close>
    by simp
  with signed_modulo_int_def [of a b] \<open>\<bar>a\<bar> = int m\<close> \<open>\<bar>b\<bar> = int n\<close>
  show ?thesis
    by (auto simp add: sgn_if diff_le_eq int_one_le_iff_zero_less simp flip: of_nat_mod of_nat_diff)
qed

lemma smod_int_compares:
   "\<lbrakk> 0 \<le> a; 0 < b \<rbrakk> \<Longrightarrow> (a :: int) smod b < b"
   "\<lbrakk> 0 \<le> a; 0 < b \<rbrakk> \<Longrightarrow> 0 \<le> (a :: int) smod b"
   "\<lbrakk> a \<le> 0; 0 < b \<rbrakk> \<Longrightarrow> -b < (a :: int) smod b"
   "\<lbrakk> a \<le> 0; 0 < b \<rbrakk> \<Longrightarrow> (a :: int) smod b \<le> 0"
   "\<lbrakk> 0 \<le> a; b < 0 \<rbrakk> \<Longrightarrow> (a :: int) smod b < - b"
   "\<lbrakk> 0 \<le> a; b < 0 \<rbrakk> \<Longrightarrow> 0 \<le> (a :: int) smod b"
   "\<lbrakk> a \<le> 0; b < 0 \<rbrakk> \<Longrightarrow> (a :: int) smod b \<le> 0"
   "\<lbrakk> a \<le> 0; b < 0 \<rbrakk> \<Longrightarrow> b \<le> (a :: int) smod b"
  apply (insert smod_int_range [where a=a and b=b])
  apply (auto simp: add1_zle_eq smod_int_alt_def sgn_if)
  done

lemma smod_mod_positive:
    "\<lbrakk> 0 \<le> (a :: int); 0 \<le> b \<rbrakk> \<Longrightarrow> a smod b = a mod b"
  by (clarsimp simp: smod_int_alt_def zsgn_def)

lemma minus_sdiv_eq [simp]:
  \<open>- k sdiv l = - (k sdiv l)\<close> for k l :: int
  by (simp add: signed_divide_int_def)

lemma sdiv_minus_eq [simp]:
  \<open>k sdiv - l = - (k sdiv l)\<close> for k l :: int
  by (simp add: signed_divide_int_def)

lemma sdiv_int_numeral_numeral [simp]:
  \<open>numeral m sdiv numeral n = numeral m div (numeral n :: int)\<close>
  by (simp add: signed_divide_int_def)

lemma minus_smod_eq [simp]:
  \<open>- k smod l = - (k smod l)\<close> for k l :: int
  by (simp add: smod_int_alt_def)

lemma smod_minus_eq [simp]:
  \<open>k smod - l = k smod l\<close> for k l :: int
  by (simp add: smod_int_alt_def)

lemma smod_int_numeral_numeral [simp]:
  \<open>numeral m smod numeral n = numeral m mod (numeral n :: int)\<close>
  by (simp add: smod_int_alt_def) 

end
