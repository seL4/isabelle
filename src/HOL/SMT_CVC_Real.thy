theory SMT_CVC_Real
  imports Alethe_Arith_Real_Rewrites HOL.Real
begin

cvc5_rare "Alethe_Arith_Real_Rewrites.rewrite_arith_geq_norm1_real"
cvc5_rare "Alethe_Arith_Real_Rewrites.rewrite_arith_eq_elim_real"
cvc5_rare "Alethe_Arith_Real_Rewrites.rewrite_arith_to_int_to_real"
cvc5_rare "Alethe_Arith_Real_Rewrites.rewrite_arith_int_eq_conflict"
cvc5_rare "Alethe_Arith_Real_Rewrites.rewrite_arith_int_geq_tighten"

lemma alethe_push_assumption_in_goal[no_atp]:
  "A \<Longrightarrow> (B \<equiv> C) \<Longrightarrow> (B \<equiv> (A \<and> C))"
  by simp

lemmas cvc_evaluate[no_atp] = of_rat_add of_rat_minus of_rat_diff of_rat_mult of_rat_divide of_rat_eq_iff
  of_rat_divide nonzero_of_rat_divide of_rat_neg_numeral_eq alethe_push_assumption_in_goal

lemmas [alethe_poly_norm] =
  ab_group_add_class.minus_add_distrib
  add_uminus_conv_diff add.inverse_inverse
  uminus_add_conv_diff right_diff_distrib_numeral
  mult_minus_left distrib_left_numeral mult_num_simps add_num_simps
  numeral_mult[symmetric] minus_diff_eq of_int_diff of_int_numeral of_int_add
  of_int_mult of_int_numeral mult_minus_left of_int_1 add.inverse_neutral
  diff_0 minus_diff_eq add.left_neutral mult.left_neutral of_int_0 divide_minus_left
  times_divide_eq_left add_divide_distrib divide_eq_eq_numeral1 eq_numeral_simps
  if_True if_False distrib_right_numeral left_diff_distrib_numeral times_divide_eq_left
  of_int_neg_numeral ring_1_class.of_int_diff ring_1_class.of_int_numeral ring_1_class.of_int_mult
  mult_numeral_left_semiring_numeral mult_num_simps of_int_minus mult_minus_right times_divide_eq_right
  of_int_of_nat_eq diff_divide_distrib add.right_neutral diff_cancel mult_minus_right
  mult_zero_left mult_zero_right div_0 div_by_1 add_uminus_conv_diff numeral_times_numeral
  mult_numeral_left_semiring_numeral mult_num_simps mult_numeral_left uminus_add_conv_diff
   div_by_1 divide_numeral_1 divide_divide_eq_right neg_equal_iff_equal numeral_One divide_divide_eq_left
  divide_self_if if_True if_False one_neq_zero more_arith_simps
  division_ring_class.times_divide_eq_right divide_cancel_left


section\<open>Lemmas to reconstruct alethe_poly_simp_rel\<close>

(*equality case*)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 cx cy::"real"
  shows "cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 = x2) = (y1 = y2))"
  by force

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 ::int and cx cy::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (real_of_int (x1 - x2))) = (cy * ((real_of_int y1) - (real_of_int y2)))) \<longrightarrow> ((x1 = x2) = ((real_of_int y1) = (real_of_int y2)))"
  by auto


(*lt case*)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 cx cy::"real"
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 < x2) = (y1 < y2))"
  by (metis less_iff_diff_less_0 mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 ::int and cx cy::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (real_of_int (x1 - x2))) = (cy * ((real_of_int y1) - (real_of_int y2)))) \<longrightarrow> ((x1 < x2) = ((real_of_int y1) < (real_of_int y2)))"
  by (metis less_iff_diff_less_0 mult_less_0_iff not_less_iff_gr_or_eq of_int_less_0_iff zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y2 ::int and cx cy y1::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (real_of_int (x1 - x2))) = (cy * (y1 - (real_of_int y2)))) \<longrightarrow> ((x1 < x2) = (y1 < (real_of_int y2)))"
  by (metis less_iff_diff_less_0 mult_less_0_iff not_less_iff_gr_or_eq of_int_less_0_iff zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 ::int and cx cy y2::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (real_of_int (x1 - x2))) = (cy * ((real_of_int y1) - y2))) \<longrightarrow> ((x1 < x2) = ((real_of_int y1) < y2))"
  by (metis less_iff_diff_less_0 mult_less_0_iff not_less_iff_gr_or_eq of_int_less_0_iff zero_less_mult_iff)


(*leq case*)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 cx cy::"real"
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<le> x2) = (y1 \<le> y2))"
  by (metis diff_gt_0_iff_gt linorder_not_le mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 ::int and cx cy::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * real_of_int (x1 - x2)) = (cy * ((real_of_int y1) - (real_of_int y2)))) \<longrightarrow> ((x1 \<le> x2) = (real_of_int y1 \<le> real_of_int y2))"
  apply (cases "x1 \<le> x2")
   apply (cases "(0 < cx)")
    apply simp_all
    apply (metis le_iff_diff_le_0 mult_le_cancel_left mult_zero_right not_less_iff_gr_or_eq of_int_le_iff)
  apply (metis diff_ge_0_iff_ge eq_iff_diff_eq_0 linorder_not_le mult_zero_right no_zero_divisors of_int_diff of_int_less_0_iff order_le_less zero_less_mult_iff)
  by (metis (no_types, opaque_lifting) cvc_arith_rewrite_defs(5) diff_gt_0_iff_gt mult_less_0_iff not_less_iff_gr_or_eq of_int_less_iff zero_less_mult_iff)
  
lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y2 ::int and cx cy y1::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (real_of_int (x2 - x1))) = (cy * ((real_of_int y2) - y1))) \<longrightarrow> ((x1 \<le> x2) = (y1 \<le> (real_of_int y2)))"
  apply (cases "x1 \<le> x2")
   apply (case_tac [!] "(0 < cx)")
    apply simp_all
  apply (metis diff_ge_0_iff_ge mult.commute mult_left_le_imp_le mult_zero_left of_int_0_le_iff of_int_diff split_mult_pos_le zero_le_square)
   apply (metis cvc_arith_rewrite_defs(5) diff_ge_0_iff_ge mult_le_0_iff of_int_0_le_iff of_int_diff order_le_less)
   apply (metis (no_types, lifting) diff_ge_0_iff_ge linorder_not_less mult_eq_0_iff mult_le_0_iff nle_le of_int_le_iff)
   by (metis diff_ge_0_iff_ge leI mult_le_0_iff of_int_le_iff order_antisym_conv)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 ::int and cx cy y2::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * real_of_int (x1 - x2)) = (cy * ((real_of_int y1) - y2))) \<longrightarrow> ((x1 \<le> x2) = (real_of_int y1 \<le> y2))"
  apply (cases "x1 \<le> x2")
   apply (cases "(0 < cx)")
    apply simp_all
    apply (metis le_iff_diff_le_0 mult_le_cancel_left mult_zero_right not_less_iff_gr_or_eq of_int_le_iff)
  apply (metis diff_ge_0_iff_ge eq_iff_diff_eq_0 linorder_not_le mult_zero_right no_zero_divisors of_int_diff of_int_less_0_iff order_le_less zero_less_mult_iff)
  by (metis (no_types, opaque_lifting) cvc_arith_rewrite_defs(5) diff_gt_0_iff_gt mult_less_0_iff not_less_iff_gr_or_eq of_int_less_iff zero_less_mult_iff)


(*gt case*)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 cx cy::"real"
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 > x2) = (y1 > y2))"
  by (metis le_iff_diff_le_0 linorder_not_le mult_less_0_iff nless_le zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 ::int and cx cy::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * real_of_int (x1 - x2)) = (cy * (real_of_int y1 - real_of_int y2))) \<longrightarrow> ((x1 > x2) = ((real_of_int y1) > (real_of_int y2)))"
  apply (cases "x1 > x2")
   apply (cases "(0 < cx)")
  apply (metis diff_gt_0_iff_gt of_int_diff of_int_less_iff order.asym zero_less_mult_iff)
  apply (metis diff_gt_0_iff_gt linorder_neqE_linordered_idom mult_less_0_iff of_int_0_less_iff)
  by (metis diff_gt_0_iff_gt mult_less_0_iff not_less_iff_gr_or_eq of_int_0 of_int_less_0_iff zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 ::int and cx cy y2::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * real_of_int (x1 - x2)) = (cy * (real_of_int y1 - y2))) \<longrightarrow> ((x1 > x2) = ((real_of_int y1) > y2))"
  apply (cases "x1 > x2")
   apply (cases "(0 < cx)")
    apply (metis of_int_0_less_iff diff_gt_0_iff_gt zero_less_mult_pos mult_pos_pos)
  apply (metis diff_gt_0_iff_gt mult_eq_0_iff not_less_iff_gr_or_eq of_int_0_less_iff zero_less_mult_iff)
  by (metis diff_gt_0_iff_gt mult_less_0_iff not_less_iff_gr_or_eq of_int_0 of_int_less_0_iff zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y2 ::int and cx cy y1::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * real_of_int (x1 - x2)) = (cy * (y1 - real_of_int y2))) \<longrightarrow> ((x1 > x2) = (y1 > (real_of_int y2)))"
  apply (cases "x1 > x2")
   apply (cases "(0 < cx)")
  apply (metis diff_gt_0_iff_gt of_int_diff of_int_less_iff order.asym zero_less_mult_iff)
  apply (metis diff_gt_0_iff_gt linorder_neqE_linordered_idom mult_less_0_iff of_int_0_less_iff)
  by (metis diff_gt_0_iff_gt mult_less_0_iff not_less_iff_gr_or_eq of_int_0 of_int_less_0_iff zero_less_mult_iff)


(*geq case*)
(*Note: these are basically the same statements as or leq but it might help reconstruction*)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 cx cy::"real"
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<ge> x2) = (y1 \<ge> y2))"
  by (metis diff_ge_0_iff_ge linorder_not_le mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 ::int and cx cy::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * real_of_int (x1 - x2)) = (cy * (real_of_int y1 - real_of_int y2))) \<longrightarrow> ((x1 \<ge> x2) = ((real_of_int y1) \<ge> (real_of_int y2)))"
  using SMT.alethe_poly_simp_rel(14) by blast

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 ::int and cx cy y2::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * real_of_int (x1 - x2)) = (cy * (real_of_int y1 - y2))) \<longrightarrow> ((x1 \<ge> x2) = ((real_of_int y1) \<ge> y2))"
  using SMT.alethe_poly_simp_rel(14) by blast

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y2 ::int and y1 cx cy::real
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * real_of_int (x1 - x2)) = (cy * (y1 - real_of_int y2))) \<longrightarrow> ((x1 \<ge> x2) = (y1 \<ge> (real_of_int y2)))"
    apply (cases "x1 \<ge> x2")
   apply (cases "(0 < cx)")
  apply (metis diff_ge_0_iff_ge less_eq_real_def not_less_iff_gr_or_eq of_int_nonneg zero_le_mult_iff)
  apply (metis cvc_arith_rewrite_defs(5) diff_ge_0_iff_ge mult_le_0_iff of_int_nonneg order_antisym_conv)
  by (metis cvc_arith_rewrite_defs(5) diff_ge_0_iff_ge linorder_le_cases of_int_0_le_iff order_antisym_conv zero_le_mult_iff zero_less_mult_iff)


end
