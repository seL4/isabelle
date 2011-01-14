(*  Title:      HOL/Matrix/LP.thy
    Author:     Steven Obua
*)

theory LP 
imports Main "~~/src/HOL/Library/Lattice_Algebras"
begin

lemma le_add_right_mono: 
  assumes 
  "a <= b + (c::'a::ordered_ab_group_add)"
  "c <= d"    
  shows "a <= b + d"
  apply (rule_tac order_trans[where y = "b+c"])
  apply (simp_all add: assms)
  done

lemma linprog_dual_estimate:
  assumes
  "A * x \<le> (b::'a::lattice_ring)"
  "0 \<le> y"
  "abs (A - A') \<le> \<delta>A"
  "b \<le> b'"
  "abs (c - c') \<le> \<delta>c"
  "abs x \<le> r"
  shows
  "c * x \<le> y * b' + (y * \<delta>A + abs (y * A' - c') + \<delta>c) * r"
proof -
  from assms have 1: "y * b <= y * b'" by (simp add: mult_left_mono)
  from assms have 2: "y * (A * x) <= y * b" by (simp add: mult_left_mono) 
  have 3: "y * (A * x) = c * x + (y * (A - A') + (y * A' - c') + (c'-c)) * x" by (simp add: algebra_simps)  
  from 1 2 3 have 4: "c * x + (y * (A - A') + (y * A' - c') + (c'-c)) * x <= y * b'" by simp
  have 5: "c * x <= y * b' + abs((y * (A - A') + (y * A' - c') + (c'-c)) * x)"
    by (simp only: 4 estimate_by_abs)  
  have 6: "abs((y * (A - A') + (y * A' - c') + (c'-c)) * x) <= abs (y * (A - A') + (y * A' - c') + (c'-c)) * abs x"
    by (simp add: abs_le_mult)
  have 7: "(abs (y * (A - A') + (y * A' - c') + (c'-c))) * abs x <= (abs (y * (A-A') + (y*A'-c')) + abs(c'-c)) * abs x"
    by(rule abs_triangle_ineq [THEN mult_right_mono]) simp
  have 8: " (abs (y * (A-A') + (y*A'-c')) + abs(c'-c)) * abs x <=  (abs (y * (A-A')) + abs (y*A'-c') + abs(c'-c)) * abs x"
    by (simp add: abs_triangle_ineq mult_right_mono)    
  have 9: "(abs (y * (A-A')) + abs (y*A'-c') + abs(c'-c)) * abs x <= (abs y * abs (A-A') + abs (y*A'-c') + abs (c'-c)) * abs x"
    by (simp add: abs_le_mult mult_right_mono)  
  have 10: "c'-c = -(c-c')" by (simp add: algebra_simps)
  have 11: "abs (c'-c) = abs (c-c')" 
    by (subst 10, subst abs_minus_cancel, simp)
  have 12: "(abs y * abs (A-A') + abs (y*A'-c') + abs (c'-c)) * abs x <= (abs y * abs (A-A') + abs (y*A'-c') + \<delta>c) * abs x"
    by (simp add: 11 assms mult_right_mono)
  have 13: "(abs y * abs (A-A') + abs (y*A'-c') + \<delta>c) * abs x <= (abs y * \<delta>A + abs (y*A'-c') + \<delta>c) * abs x"
    by (simp add: assms mult_right_mono mult_left_mono)  
  have r: "(abs y * \<delta>A + abs (y*A'-c') + \<delta>c) * abs x <=  (abs y * \<delta>A + abs (y*A'-c') + \<delta>c) * r"
    apply (rule mult_left_mono)
    apply (simp add: assms)
    apply (rule_tac add_mono[of "0::'a" _ "0", simplified])+
    apply (rule mult_left_mono[of "0" "\<delta>A", simplified])
    apply (simp_all)
    apply (rule order_trans[where y="abs (A-A')"], simp_all add: assms)
    apply (rule order_trans[where y="abs (c-c')"], simp_all add: assms)
    done    
  from 6 7 8 9 12 13 r have 14:" abs((y * (A - A') + (y * A' - c') + (c'-c)) * x) <=(abs y * \<delta>A + abs (y*A'-c') + \<delta>c) * r"     
    by (simp)
  show ?thesis
    apply (rule le_add_right_mono[of _ _ "abs((y * (A - A') + (y * A' - c') + (c'-c)) * x)"])
    apply (simp_all only: 5 14[simplified abs_of_nonneg[of y, simplified assms]])
    done
qed

lemma le_ge_imp_abs_diff_1:
  assumes
  "A1 <= (A::'a::lattice_ring)"
  "A <= A2" 
  shows "abs (A-A1) <= A2-A1"
proof -
  have "0 <= A - A1"    
  proof -
    have 1: "A - A1 = A + (- A1)" by simp
    show ?thesis by (simp only: 1 add_right_mono[of A1 A "-A1", simplified, simplified assms])
  qed
  then have "abs (A-A1) = A-A1" by (rule abs_of_nonneg)
  with assms show "abs (A-A1) <= (A2-A1)" by simp
qed

lemma mult_le_prts:
  assumes
  "a1 <= (a::'a::lattice_ring)"
  "a <= a2"
  "b1 <= b"
  "b <= b2"
  shows
  "a * b <= pprt a2 * pprt b2 + pprt a1 * nprt b2 + nprt a2 * pprt b1 + nprt a1 * nprt b1"
proof - 
  have "a * b = (pprt a + nprt a) * (pprt b + nprt b)" 
    apply (subst prts[symmetric])+
    apply simp
    done
  then have "a * b = pprt a * pprt b + pprt a * nprt b + nprt a * pprt b + nprt a * nprt b"
    by (simp add: algebra_simps)
  moreover have "pprt a * pprt b <= pprt a2 * pprt b2"
    by (simp_all add: assms mult_mono)
  moreover have "pprt a * nprt b <= pprt a1 * nprt b2"
  proof -
    have "pprt a * nprt b <= pprt a * nprt b2"
      by (simp add: mult_left_mono assms)
    moreover have "pprt a * nprt b2 <= pprt a1 * nprt b2"
      by (simp add: mult_right_mono_neg assms)
    ultimately show ?thesis
      by simp
  qed
  moreover have "nprt a * pprt b <= nprt a2 * pprt b1"
  proof - 
    have "nprt a * pprt b <= nprt a2 * pprt b"
      by (simp add: mult_right_mono assms)
    moreover have "nprt a2 * pprt b <= nprt a2 * pprt b1"
      by (simp add: mult_left_mono_neg assms)
    ultimately show ?thesis
      by simp
  qed
  moreover have "nprt a * nprt b <= nprt a1 * nprt b1"
  proof -
    have "nprt a * nprt b <= nprt a * nprt b1"
      by (simp add: mult_left_mono_neg assms)
    moreover have "nprt a * nprt b1 <= nprt a1 * nprt b1"
      by (simp add: mult_right_mono_neg assms)
    ultimately show ?thesis
      by simp
  qed
  ultimately show ?thesis
    by - (rule add_mono | simp)+
qed
    
lemma mult_le_dual_prts: 
  assumes
  "A * x \<le> (b::'a::lattice_ring)"
  "0 \<le> y"
  "A1 \<le> A"
  "A \<le> A2"
  "c1 \<le> c"
  "c \<le> c2"
  "r1 \<le> x"
  "x \<le> r2"
  shows
  "c * x \<le> y * b + (let s1 = c1 - y * A2; s2 = c2 - y * A1 in pprt s2 * pprt r2 + pprt s1 * nprt r2 + nprt s2 * pprt r1 + nprt s1 * nprt r1)"
  (is "_ <= _ + ?C")
proof -
  from assms have "y * (A * x) <= y * b" by (simp add: mult_left_mono) 
  moreover have "y * (A * x) = c * x + (y * A - c) * x" by (simp add: algebra_simps)  
  ultimately have "c * x + (y * A - c) * x <= y * b" by simp
  then have "c * x <= y * b - (y * A - c) * x" by (simp add: le_diff_eq)
  then have cx: "c * x <= y * b + (c - y * A) * x" by (simp add: algebra_simps)
  have s2: "c - y * A <= c2 - y * A1"
    by (simp add: diff_minus assms add_mono mult_left_mono)
  have s1: "c1 - y * A2 <= c - y * A"
    by (simp add: diff_minus assms add_mono mult_left_mono)
  have prts: "(c - y * A) * x <= ?C"
    apply (simp add: Let_def)
    apply (rule mult_le_prts)
    apply (simp_all add: assms s1 s2)
    done
  then have "y * b + (c - y * A) * x <= y * b + ?C"
    by simp
  with cx show ?thesis
    by(simp only:)
qed

end