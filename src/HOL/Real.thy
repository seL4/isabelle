theory Real
imports RComplete RealVector
begin

lemma field_le_epsilon:
  fixes x y :: "'a:: {number_ring,division_by_zero,ordered_field}"
  assumes e: "(!!e. 0 < e ==> x \<le> y + e)"
  shows "x \<le> y"
proof (rule ccontr)
  assume xy: "\<not> x \<le> y"
  hence "(x-y)/2 > 0"
    by (metis half_gt_zero le_iff_diff_le_0 linorder_not_le local.xy)
  hence "x \<le> y + (x - y) / 2"
    by (rule e [of "(x-y)/2"])
  also have "... = (x - y + 2*y)/2"
    by auto
       (metis add_less_cancel_left add_numeral_0_right class_semiring.add_c xy e
           diff_add_cancel gt_half_sum less_half_sum linorder_not_le number_of_Pls)
  also have "... = (x + y) / 2" 
    by auto
  also have "... < x" using xy 
    by auto
  finally have "x<x" .
  thus False
    by auto 
qed


end
