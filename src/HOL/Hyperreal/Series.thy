(*  Title       : Series.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp
Converted to setsum and polished yet more by TNN
Additional contributions by Jeremy Avigad
*) 

header{*Finite Summation and Infinite Series*}

theory Series
imports SEQ
begin

definition
   sums  :: "(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool"
     (infixr "sums" 80) where
   "f sums s = (%n. setsum f {0..<n}) ----> s"

definition
   summable :: "(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> bool" where
   "summable f = (\<exists>s. f sums s)"

definition
   suminf   :: "(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> 'a" where
   "suminf f = (THE s. f sums s)"

syntax
  "_suminf" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a" ("\<Sum>_. _" [0, 10] 10)
translations
  "\<Sum>i. b" == "CONST suminf (%i. b)"


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
by (rule setsum_0', simp)

lemma sumr_group:
     "(\<Sum>m=0..<n::nat. setsum f {m * k ..< m*k + k}) = setsum f {0 ..< n * k}"
apply (subgoal_tac "k = 0 | 0 < k", auto)
apply (induct "n")
apply (simp_all add: setsum_add_nat_ivl add_commute)
done

lemma sumr_offset3:
  "setsum f {0::nat..<n+k} = (\<Sum>m=0..<n. f (m+k)) + setsum f {0..<k}"
apply (subst setsum_shift_bounds_nat_ivl [symmetric])
apply (simp add: setsum_add_nat_ivl add_commute)
done

lemma sumr_offset:
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
  shows "(\<Sum>m=0..<n. f(m+k)) = setsum f {0..<n+k} - setsum f {0..<k}"
by (simp add: sumr_offset3)

lemma sumr_offset2:
 "\<forall>f. (\<Sum>m=0..<n::nat. f(m+k)::real) = setsum f {0..<n+k} - setsum f {0..<k}"
by (simp add: sumr_offset)

lemma sumr_offset4:
  "\<forall>n f. setsum f {0::nat..<n+k} = (\<Sum>m=0..<n. f (m+k)::real) + setsum f {0..<k}"
by (clarify, rule sumr_offset3)

(*
lemma sumr_from_1_from_0: "0 < n ==>
      (\<Sum>n=Suc 0 ..< Suc n. if even(n) then 0 else
             ((- 1) ^ ((n - (Suc 0)) div 2))/(real (fact n))) * a ^ n =
      (\<Sum>n=0..<Suc n. if even(n) then 0 else
             ((- 1) ^ ((n - (Suc 0)) div 2))/(real (fact n))) * a ^ n"
by (rule_tac n1 = 1 in sumr_split_add [THEN subst], auto)
*)

subsection{* Infinite Sums, by the Properties of Limits*}

(*----------------------
   suminf is the sum   
 ---------------------*)
lemma sums_summable: "f sums l ==> summable f"
by (simp add: sums_def summable_def, blast)

lemma summable_sums: "summable f ==> f sums (suminf f)"
apply (simp add: summable_def suminf_def sums_def)
apply (blast intro: theI LIMSEQ_unique)
done

lemma summable_sumr_LIMSEQ_suminf: 
     "summable f ==> (%n. setsum f {0..<n}) ----> (suminf f)"
by (rule summable_sums [unfolded sums_def])

(*-------------------
    sum is unique                    
 ------------------*)
lemma sums_unique: "f sums s ==> (s = suminf f)"
apply (frule sums_summable [THEN summable_sums])
apply (auto intro!: LIMSEQ_unique simp add: sums_def)
done

lemma sums_split_initial_segment: "f sums s ==> 
  (%n. f(n + k)) sums (s - (SUM i = 0..< k. f i))"
  apply (unfold sums_def);
  apply (simp add: sumr_offset); 
  apply (rule LIMSEQ_diff_const)
  apply (rule LIMSEQ_ignore_initial_segment)
  apply assumption
done

lemma summable_ignore_initial_segment: "summable f ==> 
    summable (%n. f(n + k))"
  apply (unfold summable_def)
  apply (auto intro: sums_split_initial_segment)
done

lemma suminf_minus_initial_segment: "summable f ==>
    suminf f = s ==> suminf (%n. f(n + k)) = s - (SUM i = 0..< k. f i)"
  apply (frule summable_ignore_initial_segment)
  apply (rule sums_unique [THEN sym])
  apply (frule summable_sums)
  apply (rule sums_split_initial_segment)
  apply auto
done

lemma suminf_split_initial_segment: "summable f ==> 
    suminf f = (SUM i = 0..< k. f i) + suminf (%n. f(n + k))"
by (auto simp add: suminf_minus_initial_segment)

lemma series_zero: 
     "(\<forall>m. n \<le> m --> f(m) = 0) ==> f sums (setsum f {0..<n})"
apply (simp add: sums_def LIMSEQ_def diff_minus[symmetric], safe)
apply (rule_tac x = n in exI)
apply (clarsimp simp add:setsum_diff[symmetric] cong:setsum_ivl_cong)
done

lemma sums_zero: "(%n. 0) sums 0";
  apply (unfold sums_def);
  apply simp;
  apply (rule LIMSEQ_const);
done;

lemma summable_zero: "summable (%n. 0)";
  apply (rule sums_summable);
  apply (rule sums_zero);
done;

lemma suminf_zero: "suminf (%n. 0) = 0";
  apply (rule sym);
  apply (rule sums_unique);
  apply (rule sums_zero);
done;
  
lemma sums_mult:
  fixes c :: "'a::real_normed_algebra"
  shows "f sums a \<Longrightarrow> (\<lambda>n. c * f n) sums (c * a)"
by (auto simp add: sums_def setsum_right_distrib [symmetric]
         intro!: LIMSEQ_mult intro: LIMSEQ_const)

lemma summable_mult:
  fixes c :: "'a::real_normed_algebra"
  shows "summable f \<Longrightarrow> summable (%n. c * f n)";
  apply (unfold summable_def);
  apply (auto intro: sums_mult);
done;

lemma suminf_mult:
  fixes c :: "'a::real_normed_algebra"
  shows "summable f \<Longrightarrow> suminf (\<lambda>n. c * f n) = c * suminf f";
  apply (rule sym);
  apply (rule sums_unique);
  apply (rule sums_mult);
  apply (erule summable_sums);
done;

lemma sums_mult2:
  fixes c :: "'a::real_normed_algebra"
  shows "f sums a \<Longrightarrow> (\<lambda>n. f n * c) sums (a * c)"
by (auto simp add: sums_def setsum_left_distrib [symmetric]
         intro!: LIMSEQ_mult LIMSEQ_const)

lemma summable_mult2:
  fixes c :: "'a::real_normed_algebra"
  shows "summable f \<Longrightarrow> summable (\<lambda>n. f n * c)"
  apply (unfold summable_def)
  apply (auto intro: sums_mult2)
done

lemma suminf_mult2:
  fixes c :: "'a::real_normed_algebra"
  shows "summable f \<Longrightarrow> suminf f * c = (\<Sum>n. f n * c)"
by (auto intro!: sums_unique sums_mult2 summable_sums)

lemma sums_divide:
  fixes c :: "'a::real_normed_field"
  shows "f sums a \<Longrightarrow> (\<lambda>n. f n / c) sums (a / c)"
by (simp add: divide_inverse sums_mult2)

lemma summable_divide:
  fixes c :: "'a::real_normed_field"
  shows "summable f \<Longrightarrow> summable (\<lambda>n. f n / c)"
  apply (unfold summable_def);
  apply (auto intro: sums_divide);
done;

lemma suminf_divide:
  fixes c :: "'a::real_normed_field"
  shows "summable f \<Longrightarrow> suminf (\<lambda>n. f n / c) = suminf f / c"
  apply (rule sym);
  apply (rule sums_unique);
  apply (rule sums_divide);
  apply (erule summable_sums);
done;

lemma sums_add: "[| x sums x0; y sums y0 |] ==> (%n. x n + y n) sums (x0+y0)"
by (auto simp add: sums_def setsum_addf intro: LIMSEQ_add)

lemma summable_add: "summable f ==> summable g ==> summable (%x. f x + g x)";
  apply (unfold summable_def);
  apply clarify;
  apply (rule exI);
  apply (erule sums_add);
  apply assumption;
done;

lemma suminf_add:
     "[| summable f; summable g |]   
      ==> suminf f + suminf g  = (\<Sum>n. f n + g n)"
by (auto intro!: sums_add sums_unique summable_sums)

lemma sums_diff: "[| x sums x0; y sums y0 |] ==> (%n. x n - y n) sums (x0-y0)"
by (auto simp add: sums_def setsum_subtractf intro: LIMSEQ_diff)

lemma summable_diff: "summable f ==> summable g ==> summable (%x. f x - g x)";
  apply (unfold summable_def);
  apply clarify;
  apply (rule exI);
  apply (erule sums_diff);
  apply assumption;
done;

lemma suminf_diff:
     "[| summable f; summable g |]   
      ==> suminf f - suminf g  = (\<Sum>n. f n - g n)"
by (auto intro!: sums_diff sums_unique summable_sums)

lemma sums_minus: "f sums s ==> (%x. - f x) sums (- s)";
  by (simp add: sums_def setsum_negf LIMSEQ_minus);

lemma summable_minus: "summable f ==> summable (%x. - f x)";
  by (auto simp add: summable_def intro: sums_minus);

lemma suminf_minus: "summable f ==> suminf (%x. - f x) = - (suminf f)";
  apply (rule sym);
  apply (rule sums_unique);
  apply (rule sums_minus);
  apply (erule summable_sums);
done;

lemma sums_group:
     "[|summable f; 0 < k |] ==> (%n. setsum f {n*k..<n*k+k}) sums (suminf f)"
apply (drule summable_sums)
apply (simp only: sums_def sumr_group)
apply (unfold LIMSEQ_def, safe)
apply (drule_tac x="r" in spec, safe)
apply (rule_tac x="no" in exI, safe)
apply (drule_tac x="n*k" in spec)
apply (erule mp)
apply (erule order_trans)
apply simp
done

text{*A summable series of positive terms has limit that is at least as
great as any partial sum.*}

lemma series_pos_le:
  fixes f :: "nat \<Rightarrow> real"
  shows "\<lbrakk>summable f; \<forall>m\<ge>n. 0 \<le> f m\<rbrakk> \<Longrightarrow> setsum f {0..<n} \<le> suminf f"
apply (drule summable_sums)
apply (simp add: sums_def)
apply (cut_tac k = "setsum f {0..<n}" in LIMSEQ_const)
apply (erule LIMSEQ_le, blast)
apply (rule_tac x="n" in exI, clarify)
apply (rule setsum_mono2)
apply auto
done

lemma series_pos_less:
  fixes f :: "nat \<Rightarrow> real"
  shows "\<lbrakk>summable f; \<forall>m\<ge>n. 0 < f m\<rbrakk> \<Longrightarrow> setsum f {0..<n} < suminf f"
apply (rule_tac y="setsum f {0..<Suc n}" in order_less_le_trans)
apply simp
apply (erule series_pos_le)
apply (simp add: order_less_imp_le)
done

lemma suminf_gt_zero:
  fixes f :: "nat \<Rightarrow> real"
  shows "\<lbrakk>summable f; \<forall>n. 0 < f n\<rbrakk> \<Longrightarrow> 0 < suminf f"
by (drule_tac n="0" in series_pos_less, simp_all)

lemma suminf_ge_zero:
  fixes f :: "nat \<Rightarrow> real"
  shows "\<lbrakk>summable f; \<forall>n. 0 \<le> f n\<rbrakk> \<Longrightarrow> 0 \<le> suminf f"
by (drule_tac n="0" in series_pos_le, simp_all)

lemma sumr_pos_lt_pair:
  fixes f :: "nat \<Rightarrow> real"
  shows "\<lbrakk>summable f;
        \<forall>d. 0 < f (k + (Suc(Suc 0) * d)) + f (k + ((Suc(Suc 0) * d) + 1))\<rbrakk>
      \<Longrightarrow> setsum f {0..<k} < suminf f"
apply (subst suminf_split_initial_segment [where k="k"])
apply assumption
apply simp
apply (drule_tac k="k" in summable_ignore_initial_segment)
apply (drule_tac k="Suc (Suc 0)" in sums_group, simp)
apply simp
apply (frule sums_unique)
apply (drule sums_summable)
apply simp
apply (erule suminf_gt_zero)
apply (simp add: add_ac)
done

text{*Sum of a geometric progression.*}

lemmas sumr_geometric = geometric_sum [where 'a = real]

lemma geometric_sums:
  fixes x :: "'a::{real_normed_field,recpower}"
  shows "norm x < 1 \<Longrightarrow> (\<lambda>n. x ^ n) sums (1 / (1 - x))"
proof -
  assume less_1: "norm x < 1"
  hence neq_1: "x \<noteq> 1" by auto
  hence neq_0: "x - 1 \<noteq> 0" by simp
  from less_1 have lim_0: "(\<lambda>n. x ^ n) ----> 0"
    by (rule LIMSEQ_power_zero)
  hence "(\<lambda>n. x ^ n / (x - 1) - 1 / (x - 1)) ----> 0 / (x - 1) - 1 / (x - 1)"
    using neq_0 by (intro LIMSEQ_divide LIMSEQ_diff LIMSEQ_const)
  hence "(\<lambda>n. (x ^ n - 1) / (x - 1)) ----> 1 / (1 - x)"
    by (simp add: nonzero_minus_divide_right [OF neq_0] diff_divide_distrib)
  thus "(\<lambda>n. x ^ n) sums (1 / (1 - x))"
    by (simp add: sums_def geometric_sum neq_1)
qed

lemma summable_geometric:
  fixes x :: "'a::{real_normed_field,recpower}"
  shows "norm x < 1 \<Longrightarrow> summable (\<lambda>n. x ^ n)"
by (rule geometric_sums [THEN sums_summable])

text{*Cauchy-type criterion for convergence of series (c.f. Harrison)*}

lemma summable_convergent_sumr_iff:
 "summable f = convergent (%n. setsum f {0..<n})"
by (simp add: summable_def sums_def convergent_def)

lemma summable_LIMSEQ_zero: "summable f \<Longrightarrow> f ----> 0"
apply (drule summable_convergent_sumr_iff [THEN iffD1])
apply (drule convergent_Cauchy)
apply (simp only: Cauchy_def LIMSEQ_def, safe)
apply (drule_tac x="r" in spec, safe)
apply (rule_tac x="M" in exI, safe)
apply (drule_tac x="Suc n" in spec, simp)
apply (drule_tac x="n" in spec, simp)
done

lemma summable_Cauchy:
     "summable (f::nat \<Rightarrow> 'a::banach) =  
      (\<forall>e > 0. \<exists>N. \<forall>m \<ge> N. \<forall>n. norm (setsum f {m..<n}) < e)"
apply (simp only: summable_convergent_sumr_iff Cauchy_convergent_iff [symmetric] Cauchy_def, safe)
apply (drule spec, drule (1) mp)
apply (erule exE, rule_tac x="M" in exI, clarify)
apply (rule_tac x="m" and y="n" in linorder_le_cases)
apply (frule (1) order_trans)
apply (drule_tac x="n" in spec, drule (1) mp)
apply (drule_tac x="m" in spec, drule (1) mp)
apply (simp add: setsum_diff [symmetric])
apply simp
apply (drule spec, drule (1) mp)
apply (erule exE, rule_tac x="N" in exI, clarify)
apply (rule_tac x="m" and y="n" in linorder_le_cases)
apply (subst norm_minus_commute)
apply (simp add: setsum_diff [symmetric])
apply (simp add: setsum_diff [symmetric])
done

text{*Comparison test*}

lemma norm_setsum:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "norm (setsum f A) \<le> (\<Sum>i\<in>A. norm (f i))"
apply (case_tac "finite A")
apply (erule finite_induct)
apply simp
apply simp
apply (erule order_trans [OF norm_triangle_ineq add_left_mono])
apply simp
done

lemma summable_comparison_test:
  fixes f :: "nat \<Rightarrow> 'a::banach"
  shows "\<lbrakk>\<exists>N. \<forall>n\<ge>N. norm (f n) \<le> g n; summable g\<rbrakk> \<Longrightarrow> summable f"
apply (simp add: summable_Cauchy, safe)
apply (drule_tac x="e" in spec, safe)
apply (rule_tac x = "N + Na" in exI, safe)
apply (rotate_tac 2)
apply (drule_tac x = m in spec)
apply (auto, rotate_tac 2, drule_tac x = n in spec)
apply (rule_tac y = "\<Sum>k=m..<n. norm (f k)" in order_le_less_trans)
apply (rule norm_setsum)
apply (rule_tac y = "setsum g {m..<n}" in order_le_less_trans)
apply (auto intro: setsum_mono simp add: abs_interval_iff)
done

lemma summable_norm_comparison_test:
  fixes f :: "nat \<Rightarrow> 'a::banach"
  shows "\<lbrakk>\<exists>N. \<forall>n\<ge>N. norm (f n) \<le> g n; summable g\<rbrakk>
         \<Longrightarrow> summable (\<lambda>n. norm (f n))"
apply (rule summable_comparison_test)
apply (auto)
done

lemma summable_rabs_comparison_test:
  fixes f :: "nat \<Rightarrow> real"
  shows "\<lbrakk>\<exists>N. \<forall>n\<ge>N. \<bar>f n\<bar> \<le> g n; summable g\<rbrakk> \<Longrightarrow> summable (\<lambda>n. \<bar>f n\<bar>)"
apply (rule summable_comparison_test)
apply (auto)
done

text{*Limit comparison property for series (c.f. jrh)*}

lemma summable_le:
  fixes f g :: "nat \<Rightarrow> real"
  shows "\<lbrakk>\<forall>n. f n \<le> g n; summable f; summable g\<rbrakk> \<Longrightarrow> suminf f \<le> suminf g"
apply (drule summable_sums)+
apply (simp only: sums_def, erule (1) LIMSEQ_le)
apply (rule exI)
apply (auto intro!: setsum_mono)
done

lemma summable_le2:
  fixes f g :: "nat \<Rightarrow> real"
  shows "\<lbrakk>\<forall>n. \<bar>f n\<bar> \<le> g n; summable g\<rbrakk> \<Longrightarrow> summable f \<and> suminf f \<le> suminf g"
apply (subgoal_tac "summable f")
apply (auto intro!: summable_le)
apply (simp add: abs_le_interval_iff)
apply (rule_tac g="g" in summable_comparison_test, simp_all)
done

(* specialisation for the common 0 case *)
lemma suminf_0_le:
  fixes f::"nat\<Rightarrow>real"
  assumes gt0: "\<forall>n. 0 \<le> f n" and sm: "summable f"
  shows "0 \<le> suminf f"
proof -
  let ?g = "(\<lambda>n. (0::real))"
  from gt0 have "\<forall>n. ?g n \<le> f n" by simp
  moreover have "summable ?g" by (rule summable_zero)
  moreover from sm have "summable f" .
  ultimately have "suminf ?g \<le> suminf f" by (rule summable_le)
  then show "0 \<le> suminf f" by (simp add: suminf_zero)
qed 


text{*Absolute convergence imples normal convergence*}
lemma summable_norm_cancel:
  fixes f :: "nat \<Rightarrow> 'a::banach"
  shows "summable (\<lambda>n. norm (f n)) \<Longrightarrow> summable f"
apply (simp only: summable_Cauchy, safe)
apply (drule_tac x="e" in spec, safe)
apply (rule_tac x="N" in exI, safe)
apply (drule_tac x="m" in spec, safe)
apply (rule order_le_less_trans [OF norm_setsum])
apply (rule order_le_less_trans [OF abs_ge_self])
apply simp
done

lemma summable_rabs_cancel:
  fixes f :: "nat \<Rightarrow> real"
  shows "summable (\<lambda>n. \<bar>f n\<bar>) \<Longrightarrow> summable f"
by (rule summable_norm_cancel, simp)

text{*Absolute convergence of series*}
lemma summable_norm:
  fixes f :: "nat \<Rightarrow> 'a::banach"
  shows "summable (\<lambda>n. norm (f n)) \<Longrightarrow> norm (suminf f) \<le> (\<Sum>n. norm (f n))"
by (auto intro: LIMSEQ_le LIMSEQ_norm summable_norm_cancel
                summable_sumr_LIMSEQ_suminf norm_setsum)

lemma summable_rabs:
  fixes f :: "nat \<Rightarrow> real"
  shows "summable (\<lambda>n. \<bar>f n\<bar>) \<Longrightarrow> \<bar>suminf f\<bar> \<le> (\<Sum>n. \<bar>f n\<bar>)"
by (fold real_norm_def, rule summable_norm)

subsection{* The Ratio Test*}

lemma norm_ratiotest_lemma:
  fixes x y :: "'a::normed"
  shows "\<lbrakk>c \<le> 0; norm x \<le> c * norm y\<rbrakk> \<Longrightarrow> x = 0"
apply (subgoal_tac "norm x \<le> 0", simp)
apply (erule order_trans)
apply (simp add: mult_le_0_iff)
done

lemma rabs_ratiotest_lemma: "[| c \<le> 0; abs x \<le> c * abs y |] ==> x = (0::real)"
by (erule norm_ratiotest_lemma, simp)

lemma le_Suc_ex: "(k::nat) \<le> l ==> (\<exists>n. l = k + n)"
apply (drule le_imp_less_or_eq)
apply (auto dest: less_imp_Suc_add)
done

lemma le_Suc_ex_iff: "((k::nat) \<le> l) = (\<exists>n. l = k + n)"
by (auto simp add: le_Suc_ex)

(*All this trouble just to get 0<c *)
lemma ratio_test_lemma2:
  fixes f :: "nat \<Rightarrow> 'a::banach"
  shows "\<lbrakk>\<forall>n\<ge>N. norm (f (Suc n)) \<le> c * norm (f n)\<rbrakk> \<Longrightarrow> 0 < c \<or> summable f"
apply (simp (no_asm) add: linorder_not_le [symmetric])
apply (simp add: summable_Cauchy)
apply (safe, subgoal_tac "\<forall>n. N < n --> f (n) = 0")
 prefer 2
 apply clarify
 apply(erule_tac x = "n - 1" in allE)
 apply (simp add:diff_Suc split:nat.splits)
 apply (blast intro: norm_ratiotest_lemma)
apply (rule_tac x = "Suc N" in exI, clarify)
apply(simp cong:setsum_ivl_cong)
done

lemma ratio_test:
  fixes f :: "nat \<Rightarrow> 'a::banach"
  shows "\<lbrakk>c < 1; \<forall>n\<ge>N. norm (f (Suc n)) \<le> c * norm (f n)\<rbrakk> \<Longrightarrow> summable f"
apply (frule ratio_test_lemma2, auto)
apply (rule_tac g = "%n. (norm (f N) / (c ^ N))*c ^ n" 
       in summable_comparison_test)
apply (rule_tac x = N in exI, safe)
apply (drule le_Suc_ex_iff [THEN iffD1])
apply (auto simp add: power_add realpow_not_zero)
apply (induct_tac "na", auto)
apply (rule_tac y = "c * norm (f (N + n))" in order_trans)
apply (auto intro: mult_right_mono simp add: summable_def)
apply (simp add: mult_ac)
apply (rule_tac x = "norm (f N) * (1/ (1 - c)) / (c ^ N)" in exI)
apply (rule sums_divide) 
apply (rule sums_mult) 
apply (auto intro!: geometric_sums)
done

end
