theory Real
imports RComplete RealVector
begin

lemma field_le_epsilon:
  fixes x y :: "'a:: {number_ring,division_by_zero,linordered_field}"
  assumes e: "(!!e. 0 < e ==> x \<le> y + e)"
  shows "x \<le> y"
proof (rule ccontr)
  assume xy: "\<not> x \<le> y"
  hence "(x-y)/2 > 0"
    by simp
  hence "x \<le> y + (x - y) / 2"
    by (rule e [of "(x-y)/2"])
  also have "... = (x - y + 2*y)/2"
    by (simp add: diff_divide_distrib)
  also have "... = (x + y) / 2" 
    by simp
  also have "... < x" using xy 
    by simp
  finally have "x<x" .
  thus False
    by simp
qed

end
