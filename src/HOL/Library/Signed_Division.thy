(*  Author:  Stefan Berghofer et al.
*)

subsection \<open>Signed division: negative results rounded towards zero rather than minus infinity.\<close>

theory Signed_Division
  imports Main
begin

class signed_division =
  fixes signed_divide :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl "sdiv" 70)
  and signed_modulo :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl "smod" 70)

instantiation int :: signed_division
begin

definition signed_divide_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k sdiv l = sgn k * sgn l * (\<bar>k\<bar> div \<bar>l\<bar>)\<close> for k l :: int

definition signed_modulo_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k smod l = k - (k sdiv l) * l\<close> for k l :: int

instance ..

end

lemma int_sdiv_simps [simp]:
    "(a :: int) sdiv 1 = a"
    "(a :: int) sdiv 0 = 0"
    "(a :: int) sdiv -1 = -a"
  apply (auto simp: signed_divide_int_def sgn_if)
  done

lemma sgn_div_eq_sgn_mult:
    "a div b \<noteq> 0 \<Longrightarrow> sgn ((a :: int) div b) = sgn (a * b)"
  apply (clarsimp simp: sgn_if zero_le_mult_iff neg_imp_zdiv_nonneg_iff not_less)
  apply (metis less_le mult_le_0_iff neg_imp_zdiv_neg_iff not_less pos_imp_zdiv_neg_iff zdiv_eq_0_iff)
  done

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
    "(a :: int) sdiv b \<in> { - (abs a) .. (abs a) }"
  apply (unfold signed_divide_int_def)
  apply (subgoal_tac "(abs a) div (abs b) \<le> (abs a)")
   apply (auto simp add: sgn_if not_less)
      apply (metis le_less le_less_trans neg_equal_0_iff_equal neg_less_iff_less not_le pos_imp_zdiv_neg_iff)
     apply (metis add.inverse_neutral div_int_pos_iff le_less neg_le_iff_le order_trans)
    apply (metis div_minus_right le_less_trans neg_imp_zdiv_neg_iff neg_less_0_iff_less not_le)
  using div_int_pos_iff apply fastforce
  apply (auto simp add: abs_if not_less)
     apply (metis add.inverse_inverse add_0_left div_by_1 div_minus_right less_le neg_0_le_iff_le not_le not_one_le_zero zdiv_mono2 zless_imp_add1_zle)
    apply (metis div_by_1 neg_0_less_iff_less pos_imp_zdiv_pos_iff zdiv_mono2 zero_less_one)
   apply (metis add.inverse_neutral div_by_0 div_by_1 int_div_less_self int_one_le_iff_zero_less less_le less_minus_iff order_refl)
  apply (metis div_by_1 divide_int_def int_div_less_self less_le linorder_neqE_linordered_idom order_refl unique_euclidean_semiring_numeral_class.div_less)
  done

lemma sdiv_int_div_0 [simp]:
  "(x :: int) sdiv 0 = 0"
  by (clarsimp simp: signed_divide_int_def)

lemma sdiv_int_0_div [simp]:
  "0 sdiv (x :: int) = 0"
  by (clarsimp simp: signed_divide_int_def)

lemma smod_int_alt_def:
     "(a::int) smod b = sgn (a) * (abs a mod abs b)"
  apply (clarsimp simp: signed_modulo_int_def signed_divide_int_def)
  apply (clarsimp simp: minus_div_mult_eq_mod [symmetric] abs_sgn sgn_mult sgn_if algebra_split_simps)
  done

lemma smod_int_range:
  "b \<noteq> 0 \<Longrightarrow> (a::int) smod b \<in> { - abs b + 1 .. abs b - 1 }"
  apply (case_tac  "b > 0")
   apply (insert pos_mod_conj [where a=a and b=b])[1]
   apply (insert pos_mod_conj [where a="-a" and b=b])[1]
   apply (auto simp: smod_int_alt_def algebra_simps sgn_if
              abs_if not_less add1_zle_eq [simplified add.commute])[1]
    apply (metis add_nonneg_nonneg int_one_le_iff_zero_less le_less less_add_same_cancel2 not_le pos_mod_conj)
  apply (metis (full_types) add.inverse_inverse eucl_rel_int eucl_rel_int_iff le_less_trans neg_0_le_iff_le)
  apply (insert neg_mod_conj [where a=a and b="b"])[1]
  apply (insert neg_mod_conj [where a="-a" and b="b"])[1]
  apply (clarsimp simp: smod_int_alt_def algebra_simps sgn_if
            abs_if not_less add1_zle_eq [simplified add.commute])
  apply (metis neg_0_less_iff_less neg_mod_conj not_le not_less_iff_gr_or_eq order_trans pos_mod_conj)
  done

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

lemma smod_int_mod_0 [simp]:
  "x smod (0 :: int) = x"
  by (clarsimp simp: signed_modulo_int_def)

lemma smod_int_0_mod [simp]:
  "0 smod (x :: int) = 0"
  by (clarsimp simp: smod_int_alt_def)

lemma smod_mod_positive:
    "\<lbrakk> 0 \<le> (a :: int); 0 \<le> b \<rbrakk> \<Longrightarrow> a smod b = a mod b"
  by (clarsimp simp: smod_int_alt_def zsgn_def)

end
