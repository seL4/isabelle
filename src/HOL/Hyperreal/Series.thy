(*  Title       : Series.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp
Converted to setsum and polished yet more by TNN
*) 

header{*Finite Summation and Infinite Series*}

theory Series
imports SEQ Lim
begin
thm atLeastLessThan_empty
(* FIXME why not globally? *)
declare atLeastLessThan_empty[simp];
declare atLeastLessThan_iff[iff]

constdefs
   sums  :: "(nat => real) => real => bool"     (infixr "sums" 80)
   "f sums s  == (%n. setsum f {0..<n}) ----> s"

   summable :: "(nat=>real) => bool"
   "summable f == (\<exists>s. f sums s)"

   suminf   :: "(nat=>real) => real"
   "suminf f == SOME s. f sums s"

syntax
  "_suminf" :: "idt => real => real"    ("\<Sum>_. _" [0, 10] 10)
translations
  "\<Sum>i. b" == "suminf (%i. b)"

lemma setsum_Suc[simp]:
  "setsum f {m..<Suc n} = (if n < m then 0 else setsum f {m..<n} + f(n))"
by (simp add: atLeastLessThanSuc add_commute)

lemma sumr_diff_mult_const:
 "setsum f {0..<n} - (real n*r) = setsum (%i. f i - r) {0..<n::nat}"
by (simp add: diff_minus setsum_addf real_of_nat_def)

lemma real_setsum_nat_ivl_bounded:
     "(!!p. p < n \<Longrightarrow> f(p) \<le> K)
      \<Longrightarrow> setsum f {0..<n::nat} \<le> real n * K"
using setsum_bounded[where A = "{0..<n}"]
by (auto simp:real_of_nat_def)

(* Generalize from real to some algebraic structure? *)
lemma sumr_minus_one_realpow_zero [simp]:
  "(\<Sum>i=0..<2*n. (-1) ^ Suc i) = (0::real)"
by (induct "n", auto)

(* FIXME this is an awful lemma! *)
lemma sumr_one_lb_realpow_zero [simp]:
  "(\<Sum>n=Suc 0..<n. f(n) * (0::real) ^ n) = 0"
apply (induct "n")
apply (case_tac [2] "n", auto)
done

lemma sumr_group:
     "(\<Sum>m=0..<n::nat. setsum f {m * k ..< m*k + k}) = setsum f {0 ..< n * k}"
apply (subgoal_tac "k = 0 | 0 < k", auto)
apply (induct "n")
apply (simp_all add: setsum_add_nat_ivl add_commute)
done


subsection{* Infinite Sums, by the Properties of Limits*}

(*----------------------
   suminf is the sum   
 ---------------------*)
lemma sums_summable: "f sums l ==> summable f"
by (simp add: sums_def summable_def, blast)

lemma summable_sums: "summable f ==> f sums (suminf f)"
apply (simp add: summable_def suminf_def)
apply (blast intro: someI2)
done

lemma summable_sumr_LIMSEQ_suminf: 
     "summable f ==> (%n. setsum f {0..<n}) ----> (suminf f)"
apply (simp add: summable_def suminf_def sums_def)
apply (blast intro: someI2)
done

(*-------------------
    sum is unique                    
 ------------------*)
lemma sums_unique: "f sums s ==> (s = suminf f)"
apply (frule sums_summable [THEN summable_sums])
apply (auto intro!: LIMSEQ_unique simp add: sums_def)
done

lemma series_zero: 
     "(\<forall>m. n \<le> m --> f(m) = 0) ==> f sums (setsum f {0..<n})"
apply (simp add: sums_def LIMSEQ_def diff_minus[symmetric], safe)
apply (rule_tac x = n in exI)
apply (clarsimp simp add:setsum_diff[symmetric] cong:setsum_ivl_cong)
done


lemma sums_mult: "x sums x0 ==> (%n. c * x(n)) sums (c * x0)"
by (auto simp add: sums_def setsum_mult [symmetric]
         intro!: LIMSEQ_mult intro: LIMSEQ_const)

lemma sums_divide: "x sums x' ==> (%n. x(n)/c) sums (x'/c)"
by (simp add: real_divide_def sums_mult mult_commute [of _ "inverse c"])

lemma sums_diff: "[| x sums x0; y sums y0 |] ==> (%n. x n - y n) sums (x0-y0)"
by (auto simp add: sums_def setsum_subtractf intro: LIMSEQ_diff)

lemma suminf_mult: "summable f ==> suminf f * c = (\<Sum>n. f n * c)"
by (auto intro!: sums_unique sums_mult summable_sums simp add: mult_commute)

lemma suminf_mult2: "summable f ==> c * suminf f  = (\<Sum>n. c * f n)"
by (auto intro!: sums_unique sums_mult summable_sums)

lemma suminf_diff:
     "[| summable f; summable g |]   
      ==> suminf f - suminf g  = (\<Sum>n. f n - g n)"
by (auto intro!: sums_diff sums_unique summable_sums)

lemma sums_minus: "x sums x0 ==> (%n. - x n) sums - x0"
by (auto simp add: sums_def intro!: LIMSEQ_minus simp add: setsum_negf)

lemma sums_group:
     "[|summable f; 0 < k |] ==> (%n. setsum f {n*k..<n*k+k}) sums (suminf f)"
apply (drule summable_sums)
apply (auto simp add: sums_def LIMSEQ_def sumr_group)
apply (drule_tac x = r in spec, safe)
apply (rule_tac x = no in exI, safe)
apply (drule_tac x = "n*k" in spec)
apply (auto dest!: not_leE)
apply (drule_tac j = no in less_le_trans, auto)
done

lemma sumr_pos_lt_pair_lemma:
  "[|\<forall>d. - f (n + (d + d)) < (f (Suc (n + (d + d))) :: real) |]
   ==> setsum f {0..<n+Suc(Suc 0)} \<le> setsum f {0..<Suc(Suc 0) * Suc no + n}"
apply (induct "no", auto)
apply (drule_tac x = "Suc no" in spec)
apply (simp add: add_ac)
done


lemma sumr_pos_lt_pair:
     "[|summable f; 
        \<forall>d. 0 < (f(n + (Suc(Suc 0) * d))) + f(n + ((Suc(Suc 0) * d) + 1))|]  
      ==> setsum f {0..<n} < suminf f"
apply (drule summable_sums)
apply (auto simp add: sums_def LIMSEQ_def)
apply (drule_tac x = "f (n) + f (n + 1)" in spec)
apply (auto iff: real_0_less_add_iff)
   --{*legacy proof: not necessarily better!*}
apply (rule_tac [2] ccontr, drule_tac [2] linorder_not_less [THEN iffD1])
apply (frule_tac [2] no=no in sumr_pos_lt_pair_lemma) 
apply (drule_tac x = 0 in spec, simp)
apply (rotate_tac 1, drule_tac x = "Suc (Suc 0) * (Suc no) + n" in spec)
apply (safe, simp)
apply (subgoal_tac "suminf f + (f (n) + f (n + 1)) \<le>
 setsum f {0 ..< Suc (Suc 0) * (Suc no) + n}")
apply (rule_tac [2] y = "setsum f {0..<n+ Suc (Suc 0)}" in order_trans)
prefer 3 apply assumption
apply (rule_tac [2] y = "setsum f {0..<n} + (f (n) + f (n + 1))" in order_trans)
apply simp_all 
apply (subgoal_tac "suminf f \<le> setsum f {0..< Suc (Suc 0) * (Suc no) + n}")
apply (rule_tac [2] y = "suminf f + (f (n) + f (n + 1))" in order_trans)
prefer 3 apply simp
apply (drule_tac [2] x = 0 in spec)
 prefer 2 apply simp 
apply (subgoal_tac "0 \<le> setsum f {0 ..< Suc (Suc 0) * Suc no + n} + - suminf f")
apply (simp add: abs_if)
apply (auto simp add: linorder_not_less [symmetric])
done

text{*A summable series of positive terms has limit that is at least as
great as any partial sum.*}

lemma series_pos_le: 
     "[| summable f; \<forall>m \<ge> n. 0 \<le> f(m) |] ==> setsum f {0..<n} \<le> suminf f"
apply (drule summable_sums)
apply (simp add: sums_def)
apply (cut_tac k = "setsum f {0..<n}" in LIMSEQ_const)
apply (erule LIMSEQ_le, blast)
apply (rule_tac x = n in exI, clarify)
apply (rule setsum_mono2)
apply auto
done

lemma series_pos_less:
     "[| summable f; \<forall>m \<ge> n. 0 < f(m) |] ==> setsum f {0..<n} < suminf f"
apply (rule_tac y = "setsum f {0..<Suc n}" in order_less_le_trans)
apply (rule_tac [2] series_pos_le, auto)
apply (drule_tac x = m in spec, auto)
done

text{*Sum of a geometric progression.*}

lemma sumr_geometric:
 "x ~= 1 ==> (\<Sum>i=0..<n. x ^ i) = (x ^ n - 1) / (x - 1::real)"
apply (induct "n", auto)
apply (rule_tac c1 = "x - 1" in real_mult_right_cancel [THEN iffD1])
apply (auto simp add: mult_assoc left_distrib)
apply (simp add: right_distrib diff_minus mult_commute)
done

lemma geometric_sums: "abs(x) < 1 ==> (%n. x ^ n) sums (1/(1 - x))"
apply (case_tac "x = 1")
apply (auto dest!: LIMSEQ_rabs_realpow_zero2 
        simp add: sumr_geometric sums_def diff_minus add_divide_distrib)
apply (subgoal_tac "1 / (1 + -x) = 0/ (x - 1) + - 1/ (x - 1) ")
apply (erule ssubst)
apply (rule LIMSEQ_add, rule LIMSEQ_divide)
apply (auto intro: LIMSEQ_const simp add: diff_minus minus_divide_right LIMSEQ_rabs_realpow_zero2)
done

text{*Cauchy-type criterion for convergence of series (c.f. Harrison)*}

lemma summable_convergent_sumr_iff:
 "summable f = convergent (%n. setsum f {0..<n})"
by (simp add: summable_def sums_def convergent_def)

lemma summable_Cauchy:
     "summable f =  
      (\<forall>e > 0. \<exists>N. \<forall>m \<ge> N. \<forall>n. abs(setsum f {m..<n}) < e)"
apply (auto simp add: summable_convergent_sumr_iff Cauchy_convergent_iff [symmetric] Cauchy_def diff_minus[symmetric])
apply (drule_tac [!] spec, auto)
apply (rule_tac x = M in exI)
apply (rule_tac [2] x = N in exI, auto)
apply (cut_tac [!] m = m and n = n in less_linear, auto)
apply (frule le_less_trans [THEN less_imp_le], assumption)
apply (drule_tac x = n in spec, simp)
apply (drule_tac x = m in spec)
apply(simp add: setsum_diff[symmetric])
apply(subst abs_minus_commute)
apply(simp add: setsum_diff[symmetric])
apply(simp add: setsum_diff[symmetric])
done

text{*Comparison test*}

lemma summable_comparison_test:
     "[| \<exists>N. \<forall>n \<ge> N. abs(f n) \<le> g n; summable g |] ==> summable f"
apply (auto simp add: summable_Cauchy)
apply (drule spec, auto)
apply (rule_tac x = "N + Na" in exI, auto)
apply (rotate_tac 2)
apply (drule_tac x = m in spec)
apply (auto, rotate_tac 2, drule_tac x = n in spec)
apply (rule_tac y = "\<Sum>k=m..<n. abs(f k)" in order_le_less_trans)
apply (rule setsum_abs)
apply (rule_tac y = "setsum g {m..<n}" in order_le_less_trans)
apply (auto intro: setsum_mono simp add: abs_interval_iff)
done

lemma summable_rabs_comparison_test:
     "[| \<exists>N. \<forall>n \<ge> N. abs(f n) \<le> g n; summable g |] 
      ==> summable (%k. abs (f k))"
apply (rule summable_comparison_test)
apply (auto)
done

text{*Limit comparison property for series (c.f. jrh)*}

lemma summable_le:
     "[|\<forall>n. f n \<le> g n; summable f; summable g |] ==> suminf f \<le> suminf g"
apply (drule summable_sums)+
apply (auto intro!: LIMSEQ_le simp add: sums_def)
apply (rule exI)
apply (auto intro!: setsum_mono)
done

lemma summable_le2:
     "[|\<forall>n. abs(f n) \<le> g n; summable g |]  
      ==> summable f & suminf f \<le> suminf g"
apply (auto intro: summable_comparison_test intro!: summable_le)
apply (simp add: abs_le_interval_iff)
done

text{*Absolute convergence imples normal convergence*}
lemma summable_rabs_cancel: "summable (%n. abs (f n)) ==> summable f"
apply (auto simp add: summable_Cauchy)
apply (drule spec, auto)
apply (rule_tac x = N in exI, auto)
apply (drule spec, auto)
apply (rule_tac y = "\<Sum>n=m..<n. abs(f n)" in order_le_less_trans)
apply (auto)
done

text{*Absolute convergence of series*}
lemma summable_rabs:
     "summable (%n. abs (f n)) ==> abs(suminf f) \<le> (\<Sum>n. abs(f n))"
by (auto intro: LIMSEQ_le LIMSEQ_imp_rabs summable_rabs_cancel summable_sumr_LIMSEQ_suminf)


subsection{* The Ratio Test*}

lemma rabs_ratiotest_lemma: "[| c \<le> 0; abs x \<le> c * abs y |] ==> x = (0::real)"
apply (drule order_le_imp_less_or_eq, auto)
apply (subgoal_tac "0 \<le> c * abs y")
apply (simp add: zero_le_mult_iff, arith)
done

lemma le_Suc_ex: "(k::nat) \<le> l ==> (\<exists>n. l = k + n)"
apply (drule le_imp_less_or_eq)
apply (auto dest: less_imp_Suc_add)
done

lemma le_Suc_ex_iff: "((k::nat) \<le> l) = (\<exists>n. l = k + n)"
by (auto simp add: le_Suc_ex)

(*All this trouble just to get 0<c *)
lemma ratio_test_lemma2:
     "[| \<forall>n \<ge> N. abs(f(Suc n)) \<le> c*abs(f n) |]  
      ==> 0 < c | summable f"
apply (simp (no_asm) add: linorder_not_le [symmetric])
apply (simp add: summable_Cauchy)
apply (safe, subgoal_tac "\<forall>n. N < n --> f (n) = 0")
 prefer 2
 apply clarify
 apply(erule_tac x = "n - 1" in allE)
 apply (simp add:diff_Suc split:nat.splits)
 apply (blast intro: rabs_ratiotest_lemma)
apply (rule_tac x = "Suc N" in exI, clarify)
apply(simp cong:setsum_ivl_cong)
done

lemma ratio_test:
     "[| c < 1; \<forall>n \<ge> N. abs(f(Suc n)) \<le> c*abs(f n) |]  
      ==> summable f"
apply (frule ratio_test_lemma2, auto)
apply (rule_tac g = "%n. (abs (f N) / (c ^ N))*c ^ n" 
       in summable_comparison_test)
apply (rule_tac x = N in exI, safe)
apply (drule le_Suc_ex_iff [THEN iffD1])
apply (auto simp add: power_add realpow_not_zero)
apply (induct_tac "na", auto)
apply (rule_tac y = "c*abs (f (N + n))" in order_trans)
apply (auto intro: mult_right_mono simp add: summable_def)
apply (simp add: mult_ac)
apply (rule_tac x = "abs (f N) * (1/ (1 - c)) / (c ^ N)" in exI)
apply (rule sums_divide) 
apply (rule sums_mult) 
apply (auto intro!: geometric_sums)
done


text{*Differentiation of finite sum*}

lemma DERIV_sumr [rule_format (no_asm)]:
     "(\<forall>r. m \<le> r & r < (m + n) --> DERIV (%x. f r x) x :> (f' r x))  
      --> DERIV (%x. \<Sum>n=m..<n::nat. f n x) x :> (\<Sum>r=m..<n. f' r x)"
apply (induct "n")
apply (auto intro: DERIV_add)
done

ML
{*
val sums_def = thm"sums_def";
val summable_def = thm"summable_def";
val suminf_def = thm"suminf_def";

val sumr_minus_one_realpow_zero = thm "sumr_minus_one_realpow_zero";
val sumr_one_lb_realpow_zero = thm "sumr_one_lb_realpow_zero";
val sumr_group = thm "sumr_group";
val sums_summable = thm "sums_summable";
val summable_sums = thm "summable_sums";
val summable_sumr_LIMSEQ_suminf = thm "summable_sumr_LIMSEQ_suminf";
val sums_unique = thm "sums_unique";
val series_zero = thm "series_zero";
val sums_mult = thm "sums_mult";
val sums_divide = thm "sums_divide";
val sums_diff = thm "sums_diff";
val suminf_mult = thm "suminf_mult";
val suminf_mult2 = thm "suminf_mult2";
val suminf_diff = thm "suminf_diff";
val sums_minus = thm "sums_minus";
val sums_group = thm "sums_group";
val sumr_pos_lt_pair_lemma = thm "sumr_pos_lt_pair_lemma";
val sumr_pos_lt_pair = thm "sumr_pos_lt_pair";
val series_pos_le = thm "series_pos_le";
val series_pos_less = thm "series_pos_less";
val sumr_geometric = thm "sumr_geometric";
val geometric_sums = thm "geometric_sums";
val summable_convergent_sumr_iff = thm "summable_convergent_sumr_iff";
val summable_Cauchy = thm "summable_Cauchy";
val summable_comparison_test = thm "summable_comparison_test";
val summable_rabs_comparison_test = thm "summable_rabs_comparison_test";
val summable_le = thm "summable_le";
val summable_le2 = thm "summable_le2";
val summable_rabs_cancel = thm "summable_rabs_cancel";
val summable_rabs = thm "summable_rabs";
val rabs_ratiotest_lemma = thm "rabs_ratiotest_lemma";
val le_Suc_ex = thm "le_Suc_ex";
val le_Suc_ex_iff = thm "le_Suc_ex_iff";
val ratio_test_lemma2 = thm "ratio_test_lemma2";
val ratio_test = thm "ratio_test";
val DERIV_sumr = thm "DERIV_sumr";
*}

end
