(*  Title       : MacLaurin.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
    Description : MacLaurin series
*)

theory MacLaurin = Log
files ("MacLaurin_lemmas.ML"):

use "MacLaurin_lemmas.ML"

lemma Maclaurin_sin_bound: 
  "abs(sin x - sumr 0 n (%m. (if even m then 0 else ((- 1) ^ ((m - (Suc 0)) div 2)) / real (fact m)) * 
  x ^ m))  <= inverse(real (fact n)) * abs(x) ^ n"
proof -
  have "!! x (y::real). x <= 1 \<Longrightarrow> 0 <= y \<Longrightarrow> x * y \<le> 1 * y" 
    by (rule_tac mult_right_mono,simp_all)
  note est = this[simplified]
  show ?thesis
    apply (cut_tac f=sin and n=n and x=x and 
      diff = "%n x. if n mod 4 = 0 then sin(x) else if n mod 4 = 1 then cos(x) else if n mod 4 = 2 then -sin(x) else -cos(x)"
      in Maclaurin_all_le_objl)
    apply (tactic{* (Step_tac 1) *})
    apply (simp)
    apply (subst mod_Suc_eq_Suc_mod)
    apply (tactic{* cut_inst_tac [("m1","m")] (CLAIM "0 < (4::nat)" RS mod_less_divisor RS lemma_exhaust_less_4) 1*})
    apply (tactic{* Step_tac 1 *})
    apply (simp)+
    apply (rule DERIV_minus, simp+)
    apply (rule lemma_DERIV_subst, rule DERIV_minus, rule DERIV_cos, simp)
    apply (tactic{* dtac ssubst 1 THEN assume_tac 2 *})
    apply (tactic {* rtac (ARITH_PROVE "[|x = y; abs u <= (v::real) |] ==> abs ((x + u) - y) <= v") 1 *})
    apply (rule sumr_fun_eq)
    apply (tactic{* Step_tac 1 *})
    apply (tactic{*rtac (CLAIM "x = y ==> x * z = y * (z::real)") 1*})
    apply (subst even_even_mod_4_iff)
    apply (tactic{* cut_inst_tac [("m1","r")] (CLAIM "0 < (4::nat)" RS mod_less_divisor RS lemma_exhaust_less_4) 1 *})
    apply (tactic{* Step_tac 1 *})
    apply (simp)
    apply (simp_all add:even_num_iff)
    apply (drule lemma_even_mod_4_div_2[simplified])
    apply(simp add: numeral_2_eq_2 real_divide_def)
    apply (drule lemma_odd_mod_4_div_2 );
    apply (simp add: numeral_2_eq_2 real_divide_def)
    apply (auto intro: real_mult_le_lemma mult_right_mono simp add: est mult_pos_le mult_ac real_divide_def abs_mult abs_inverse power_abs[symmetric])
    done
qed

end