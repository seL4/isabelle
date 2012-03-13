(*  Title       : Series.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp
Converted to setsum and polished yet more by TNN
Additional contributions by Jeremy Avigad
*)

header{*Finite Summation and Infinite Series*}

theory Series
imports SEQ Deriv
begin

definition
   sums  :: "(nat \<Rightarrow> 'a::{topological_space, comm_monoid_add}) \<Rightarrow> 'a \<Rightarrow> bool"
     (infixr "sums" 80) where
   "f sums s = (%n. setsum f {0..<n}) ----> s"

definition
   summable :: "(nat \<Rightarrow> 'a::{topological_space, comm_monoid_add}) \<Rightarrow> bool" where
   "summable f = (\<exists>s. f sums s)"

definition
   suminf   :: "(nat \<Rightarrow> 'a::{topological_space, comm_monoid_add}) \<Rightarrow> 'a" where
   "suminf f = (THE s. f sums s)"

notation suminf (binder "\<Sum>" 10)


lemma [trans]: "f=g ==> g sums z ==> f sums z"
  by simp

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

subsection{* Infinite Sums, by the Properties of Limits*}

(*----------------------
   suminf is the sum
 ---------------------*)
lemma sums_summable: "f sums l ==> summable f"
  by (simp add: sums_def summable_def, blast)

lemma summable_sums:
  fixes f :: "nat \<Rightarrow> 'a::{t2_space, comm_monoid_add}"
  assumes "summable f"
  shows "f sums (suminf f)"
proof -
  from assms obtain s where s: "(\<lambda>n. setsum f {0..<n}) ----> s"
    unfolding summable_def sums_def [abs_def] ..
  then show ?thesis unfolding sums_def [abs_def] suminf_def
    by (rule theI, auto intro!: tendsto_unique[OF trivial_limit_sequentially])
qed

lemma summable_sumr_LIMSEQ_suminf:
  fixes f :: "nat \<Rightarrow> 'a::{t2_space, comm_monoid_add}"
  shows "summable f \<Longrightarrow> (\<lambda>n. setsum f {0..<n}) ----> suminf f"
by (rule summable_sums [unfolded sums_def])

lemma suminf_eq_lim: "suminf f = lim (%n. setsum f {0..<n})"
  by (simp add: suminf_def sums_def lim_def)

(*-------------------
    sum is unique
 ------------------*)
lemma sums_unique:
  fixes f :: "nat \<Rightarrow> 'a::{t2_space, comm_monoid_add}"
  shows "f sums s \<Longrightarrow> (s = suminf f)"
apply (frule sums_summable[THEN summable_sums])
apply (auto intro!: tendsto_unique[OF trivial_limit_sequentially] simp add: sums_def)
done

lemma sums_iff:
  fixes f :: "nat \<Rightarrow> 'a::{t2_space, comm_monoid_add}"
  shows "f sums x \<longleftrightarrow> summable f \<and> (suminf f = x)"
  by (metis summable_sums sums_summable sums_unique)

lemma sums_split_initial_segment:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "f sums s ==> (\<lambda>n. f(n + k)) sums (s - (SUM i = 0..< k. f i))"
  apply (unfold sums_def)
  apply (simp add: sumr_offset)
  apply (rule tendsto_diff [OF _ tendsto_const])
  apply (rule LIMSEQ_ignore_initial_segment)
  apply assumption
done

lemma summable_ignore_initial_segment:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "summable f ==> summable (%n. f(n + k))"
  apply (unfold summable_def)
  apply (auto intro: sums_split_initial_segment)
done

lemma suminf_minus_initial_segment:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "summable f ==>
    suminf f = s ==> suminf (%n. f(n + k)) = s - (SUM i = 0..< k. f i)"
  apply (frule summable_ignore_initial_segment)
  apply (rule sums_unique [THEN sym])
  apply (frule summable_sums)
  apply (rule sums_split_initial_segment)
  apply auto
done

lemma suminf_split_initial_segment:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "summable f ==>
    suminf f = (SUM i = 0..< k. f i) + (\<Sum>n. f(n + k))"
by (auto simp add: suminf_minus_initial_segment)

lemma suminf_exist_split: fixes r :: real assumes "0 < r" and "summable a"
  shows "\<exists> N. \<forall> n \<ge> N. \<bar> \<Sum> i. a (i + n) \<bar> < r"
proof -
  from LIMSEQ_D[OF summable_sumr_LIMSEQ_suminf[OF `summable a`] `0 < r`]
  obtain N :: nat where "\<forall> n \<ge> N. norm (setsum a {0..<n} - suminf a) < r" by auto
  thus ?thesis unfolding suminf_minus_initial_segment[OF `summable a` refl] abs_minus_commute real_norm_def
    by auto
qed

lemma sums_Suc:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes sumSuc: "(\<lambda> n. f (Suc n)) sums l" shows "f sums (l + f 0)"
proof -
  from sumSuc[unfolded sums_def]
  have "(\<lambda>i. \<Sum>n = Suc 0..<Suc i. f n) ----> l" unfolding setsum_reindex[OF inj_Suc] image_Suc_atLeastLessThan[symmetric] comp_def .
  from tendsto_add[OF this tendsto_const, where b="f 0"]
  have "(\<lambda>i. \<Sum>n = 0..<Suc i. f n) ----> l + f 0" unfolding add_commute setsum_head_upt_Suc[OF zero_less_Suc] .
  thus ?thesis unfolding sums_def by (rule LIMSEQ_imp_Suc)
qed

lemma series_zero:
  fixes f :: "nat \<Rightarrow> 'a::{t2_space, comm_monoid_add}"
  assumes "\<forall>m. n \<le> m \<longrightarrow> f m = 0"
  shows "f sums (setsum f {0..<n})"
proof -
  { fix k :: nat have "setsum f {0..<k + n} = setsum f {0..<n}"
      using assms by (induct k) auto }
  note setsum_const = this
  show ?thesis
    unfolding sums_def
    apply (rule LIMSEQ_offset[of _ n])
    unfolding setsum_const
    apply (rule tendsto_const)
    done
qed

lemma sums_zero[simp, intro]: "(\<lambda>n. 0) sums 0"
  unfolding sums_def by (simp add: tendsto_const)

lemma summable_zero[simp, intro]: "summable (\<lambda>n. 0)"
by (rule sums_zero [THEN sums_summable])

lemma suminf_zero[simp]: "suminf (\<lambda>n. 0::'a::{t2_space, comm_monoid_add}) = 0"
by (rule sums_zero [THEN sums_unique, symmetric])

lemma (in bounded_linear) sums:
  "(\<lambda>n. X n) sums a \<Longrightarrow> (\<lambda>n. f (X n)) sums (f a)"
  unfolding sums_def by (drule tendsto, simp only: setsum)

lemma (in bounded_linear) summable:
  "summable (\<lambda>n. X n) \<Longrightarrow> summable (\<lambda>n. f (X n))"
unfolding summable_def by (auto intro: sums)

lemma (in bounded_linear) suminf:
  "summable (\<lambda>n. X n) \<Longrightarrow> f (\<Sum>n. X n) = (\<Sum>n. f (X n))"
by (intro sums_unique sums summable_sums)

lemmas sums_of_real = bounded_linear.sums [OF bounded_linear_of_real]
lemmas summable_of_real = bounded_linear.summable [OF bounded_linear_of_real]
lemmas suminf_of_real = bounded_linear.suminf [OF bounded_linear_of_real]

lemma sums_mult:
  fixes c :: "'a::real_normed_algebra"
  shows "f sums a \<Longrightarrow> (\<lambda>n. c * f n) sums (c * a)"
  by (rule bounded_linear.sums [OF bounded_linear_mult_right])

lemma summable_mult:
  fixes c :: "'a::real_normed_algebra"
  shows "summable f \<Longrightarrow> summable (%n. c * f n)"
  by (rule bounded_linear.summable [OF bounded_linear_mult_right])

lemma suminf_mult:
  fixes c :: "'a::real_normed_algebra"
  shows "summable f \<Longrightarrow> suminf (\<lambda>n. c * f n) = c * suminf f"
  by (rule bounded_linear.suminf [OF bounded_linear_mult_right, symmetric])

lemma sums_mult2:
  fixes c :: "'a::real_normed_algebra"
  shows "f sums a \<Longrightarrow> (\<lambda>n. f n * c) sums (a * c)"
  by (rule bounded_linear.sums [OF bounded_linear_mult_left])

lemma summable_mult2:
  fixes c :: "'a::real_normed_algebra"
  shows "summable f \<Longrightarrow> summable (\<lambda>n. f n * c)"
  by (rule bounded_linear.summable [OF bounded_linear_mult_left])

lemma suminf_mult2:
  fixes c :: "'a::real_normed_algebra"
  shows "summable f \<Longrightarrow> suminf f * c = (\<Sum>n. f n * c)"
  by (rule bounded_linear.suminf [OF bounded_linear_mult_left])

lemma sums_divide:
  fixes c :: "'a::real_normed_field"
  shows "f sums a \<Longrightarrow> (\<lambda>n. f n / c) sums (a / c)"
  by (rule bounded_linear.sums [OF bounded_linear_divide])

lemma summable_divide:
  fixes c :: "'a::real_normed_field"
  shows "summable f \<Longrightarrow> summable (\<lambda>n. f n / c)"
  by (rule bounded_linear.summable [OF bounded_linear_divide])

lemma suminf_divide:
  fixes c :: "'a::real_normed_field"
  shows "summable f \<Longrightarrow> suminf (\<lambda>n. f n / c) = suminf f / c"
  by (rule bounded_linear.suminf [OF bounded_linear_divide, symmetric])

lemma sums_add:
  fixes a b :: "'a::real_normed_field"
  shows "\<lbrakk>X sums a; Y sums b\<rbrakk> \<Longrightarrow> (\<lambda>n. X n + Y n) sums (a + b)"
  unfolding sums_def by (simp add: setsum_addf tendsto_add)

lemma summable_add:
  fixes X Y :: "nat \<Rightarrow> 'a::real_normed_field"
  shows "\<lbrakk>summable X; summable Y\<rbrakk> \<Longrightarrow> summable (\<lambda>n. X n + Y n)"
unfolding summable_def by (auto intro: sums_add)

lemma suminf_add:
  fixes X Y :: "nat \<Rightarrow> 'a::real_normed_field"
  shows "\<lbrakk>summable X; summable Y\<rbrakk> \<Longrightarrow> suminf X + suminf Y = (\<Sum>n. X n + Y n)"
by (intro sums_unique sums_add summable_sums)

lemma sums_diff:
  fixes X Y :: "nat \<Rightarrow> 'a::real_normed_field"
  shows "\<lbrakk>X sums a; Y sums b\<rbrakk> \<Longrightarrow> (\<lambda>n. X n - Y n) sums (a - b)"
  unfolding sums_def by (simp add: setsum_subtractf tendsto_diff)

lemma summable_diff:
  fixes X Y :: "nat \<Rightarrow> 'a::real_normed_field"
  shows "\<lbrakk>summable X; summable Y\<rbrakk> \<Longrightarrow> summable (\<lambda>n. X n - Y n)"
unfolding summable_def by (auto intro: sums_diff)

lemma suminf_diff:
  fixes X Y :: "nat \<Rightarrow> 'a::real_normed_field"
  shows "\<lbrakk>summable X; summable Y\<rbrakk> \<Longrightarrow> suminf X - suminf Y = (\<Sum>n. X n - Y n)"
by (intro sums_unique sums_diff summable_sums)

lemma sums_minus:
  fixes X :: "nat \<Rightarrow> 'a::real_normed_field"
  shows "X sums a ==> (\<lambda>n. - X n) sums (- a)"
  unfolding sums_def by (simp add: setsum_negf tendsto_minus)

lemma summable_minus:
  fixes X :: "nat \<Rightarrow> 'a::real_normed_field"
  shows "summable X \<Longrightarrow> summable (\<lambda>n. - X n)"
unfolding summable_def by (auto intro: sums_minus)

lemma suminf_minus:
  fixes X :: "nat \<Rightarrow> 'a::real_normed_field"
  shows "summable X \<Longrightarrow> (\<Sum>n. - X n) = - (\<Sum>n. X n)"
by (intro sums_unique [symmetric] sums_minus summable_sums)

lemma sums_group:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_field"
  shows "\<lbrakk>f sums s; 0 < k\<rbrakk> \<Longrightarrow> (\<lambda>n. setsum f {n*k..<n*k+k}) sums s"
apply (simp only: sums_def sumr_group)
apply (unfold LIMSEQ_iff, safe)
apply (drule_tac x="r" in spec, safe)
apply (rule_tac x="no" in exI, safe)
apply (drule_tac x="n*k" in spec)
apply (erule mp)
apply (erule order_trans)
apply simp
done

text{*A summable series of positive terms has limit that is at least as
great as any partial sum.*}

lemma pos_summable:
  fixes f:: "nat \<Rightarrow> real"
  assumes pos: "!!n. 0 \<le> f n" and le: "!!n. setsum f {0..<n} \<le> x"
  shows "summable f"
proof -
  have "convergent (\<lambda>n. setsum f {0..<n})"
    proof (rule Bseq_mono_convergent)
      show "Bseq (\<lambda>n. setsum f {0..<n})"
        by (rule f_inc_g_dec_Beq_f [of "(\<lambda>n. setsum f {0..<n})" "\<lambda>n. x"])
           (auto simp add: le pos)
    next
      show "\<forall>m n. m \<le> n \<longrightarrow> setsum f {0..<m} \<le> setsum f {0..<n}"
        by (auto intro: setsum_mono2 pos)
    qed
  then obtain L where "(%n. setsum f {0..<n}) ----> L"
    by (blast dest: convergentD)
  thus ?thesis
    by (force simp add: summable_def sums_def)
qed

lemma series_pos_le:
  fixes f :: "nat \<Rightarrow> real"
  shows "\<lbrakk>summable f; \<forall>m\<ge>n. 0 \<le> f m\<rbrakk> \<Longrightarrow> setsum f {0..<n} \<le> suminf f"
apply (drule summable_sums)
apply (simp add: sums_def)
apply (cut_tac k = "setsum f {0..<n}" in tendsto_const)
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
unfolding One_nat_def
apply (subst suminf_split_initial_segment [where k="k"])
apply assumption
apply simp
apply (drule_tac k="k" in summable_ignore_initial_segment)
apply (drule_tac k="Suc (Suc 0)" in sums_group [OF summable_sums], simp)
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
  fixes x :: "'a::{real_normed_field}"
  shows "norm x < 1 \<Longrightarrow> (\<lambda>n. x ^ n) sums (1 / (1 - x))"
proof -
  assume less_1: "norm x < 1"
  hence neq_1: "x \<noteq> 1" by auto
  hence neq_0: "x - 1 \<noteq> 0" by simp
  from less_1 have lim_0: "(\<lambda>n. x ^ n) ----> 0"
    by (rule LIMSEQ_power_zero)
  hence "(\<lambda>n. x ^ n / (x - 1) - 1 / (x - 1)) ----> 0 / (x - 1) - 1 / (x - 1)"
    using neq_0 by (intro tendsto_intros)
  hence "(\<lambda>n. (x ^ n - 1) / (x - 1)) ----> 1 / (1 - x)"
    by (simp add: nonzero_minus_divide_right [OF neq_0] diff_divide_distrib)
  thus "(\<lambda>n. x ^ n) sums (1 / (1 - x))"
    by (simp add: sums_def geometric_sum neq_1)
qed

lemma summable_geometric:
  fixes x :: "'a::{real_normed_field}"
  shows "norm x < 1 \<Longrightarrow> summable (\<lambda>n. x ^ n)"
by (rule geometric_sums [THEN sums_summable])

lemma half: "0 < 1 / (2::'a::{number_ring,linordered_field_inverse_zero})"
  by arith

lemma power_half_series: "(\<lambda>n. (1/2::real)^Suc n) sums 1"
proof -
  have 2: "(\<lambda>n. (1/2::real)^n) sums 2" using geometric_sums [of "1/2::real"]
    by auto
  have "(\<lambda>n. (1/2::real)^Suc n) = (\<lambda>n. (1 / 2) ^ n / 2)"
    by simp
  thus ?thesis using sums_divide [OF 2, of 2]
    by simp
qed

text{*Cauchy-type criterion for convergence of series (c.f. Harrison)*}

lemma summable_convergent_sumr_iff:
 "summable f = convergent (%n. setsum f {0..<n})"
by (simp add: summable_def sums_def convergent_def)

lemma summable_LIMSEQ_zero:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "summable f \<Longrightarrow> f ----> 0"
apply (drule summable_convergent_sumr_iff [THEN iffD1])
apply (drule convergent_Cauchy)
apply (simp only: Cauchy_iff LIMSEQ_iff, safe)
apply (drule_tac x="r" in spec, safe)
apply (rule_tac x="M" in exI, safe)
apply (drule_tac x="Suc n" in spec, simp)
apply (drule_tac x="n" in spec, simp)
done

lemma suminf_le:
  fixes x :: real
  shows "summable f \<Longrightarrow> (!!n. setsum f {0..<n} \<le> x) \<Longrightarrow> suminf f \<le> x"
  by (simp add: summable_convergent_sumr_iff suminf_eq_lim lim_le)

lemma summable_Cauchy:
     "summable (f::nat \<Rightarrow> 'a::banach) =
      (\<forall>e > 0. \<exists>N. \<forall>m \<ge> N. \<forall>n. norm (setsum f {m..<n}) < e)"
apply (simp only: summable_convergent_sumr_iff Cauchy_convergent_iff [symmetric] Cauchy_iff, safe)
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
apply (auto intro: setsum_mono simp add: abs_less_iff)
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

text{*Summability of geometric series for real algebras*}

lemma complete_algebra_summable_geometric:
  fixes x :: "'a::{real_normed_algebra_1,banach}"
  shows "norm x < 1 \<Longrightarrow> summable (\<lambda>n. x ^ n)"
proof (rule summable_comparison_test)
  show "\<exists>N. \<forall>n\<ge>N. norm (x ^ n) \<le> norm x ^ n"
    by (simp add: norm_power_ineq)
  show "norm x < 1 \<Longrightarrow> summable (\<lambda>n. norm x ^ n)"
    by (simp add: summable_geometric)
qed

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
apply (simp add: abs_le_iff)
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
  then show "0 \<le> suminf f" by simp
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
  by (auto intro: LIMSEQ_le tendsto_norm summable_norm_cancel
                summable_sumr_LIMSEQ_suminf norm_setsum)

lemma summable_rabs:
  fixes f :: "nat \<Rightarrow> real"
  shows "summable (\<lambda>n. \<bar>f n\<bar>) \<Longrightarrow> \<bar>suminf f\<bar> \<le> (\<Sum>n. \<bar>f n\<bar>)"
by (fold real_norm_def, rule summable_norm)

subsection{* The Ratio Test*}

lemma norm_ratiotest_lemma:
  fixes x y :: "'a::real_normed_vector"
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
 apply(erule_tac x = "n - Suc 0" in allE)
 apply (simp add:diff_Suc split:nat.splits)
 apply (blast intro: norm_ratiotest_lemma)
apply (rule_tac x = "Suc N" in exI, clarify)
apply(simp cong del: setsum_cong cong: setsum_ivl_cong)
done

lemma ratio_test:
  fixes f :: "nat \<Rightarrow> 'a::banach"
  shows "\<lbrakk>c < 1; \<forall>n\<ge>N. norm (f (Suc n)) \<le> c * norm (f n)\<rbrakk> \<Longrightarrow> summable f"
apply (frule ratio_test_lemma2, auto)
apply (rule_tac g = "%n. (norm (f N) / (c ^ N))*c ^ n"
       in summable_comparison_test)
apply (rule_tac x = N in exI, safe)
apply (drule le_Suc_ex_iff [THEN iffD1])
apply (auto simp add: power_add field_power_not_zero)
apply (induct_tac "na", auto)
apply (rule_tac y = "c * norm (f (N + n))" in order_trans)
apply (auto intro: mult_right_mono simp add: summable_def)
apply (rule_tac x = "norm (f N) * (1/ (1 - c)) / (c ^ N)" in exI)
apply (rule sums_divide)
apply (rule sums_mult)
apply (auto intro!: geometric_sums)
done

subsection {* Cauchy Product Formula *}

(* Proof based on Analysis WebNotes: Chapter 07, Class 41
http://www.math.unl.edu/~webnotes/classes/class41/prp77.htm *)

lemma setsum_triangle_reindex:
  fixes n :: nat
  shows "(\<Sum>(i,j)\<in>{(i,j). i+j < n}. f i j) = (\<Sum>k=0..<n. \<Sum>i=0..k. f i (k - i))"
proof -
  have "(\<Sum>(i, j)\<in>{(i, j). i + j < n}. f i j) =
    (\<Sum>(k, i)\<in>(SIGMA k:{0..<n}. {0..k}). f i (k - i))"
  proof (rule setsum_reindex_cong)
    show "inj_on (\<lambda>(k,i). (i, k - i)) (SIGMA k:{0..<n}. {0..k})"
      by (rule inj_on_inverseI [where g="\<lambda>(i,j). (i+j, i)"], auto)
    show "{(i,j). i + j < n} = (\<lambda>(k,i). (i, k - i)) ` (SIGMA k:{0..<n}. {0..k})"
      by (safe, rule_tac x="(a+b,a)" in image_eqI, auto)
    show "\<And>a. (\<lambda>(k, i). f i (k - i)) a = split f ((\<lambda>(k, i). (i, k - i)) a)"
      by clarify
  qed
  thus ?thesis by (simp add: setsum_Sigma)
qed

lemma Cauchy_product_sums:
  fixes a b :: "nat \<Rightarrow> 'a::{real_normed_algebra,banach}"
  assumes a: "summable (\<lambda>k. norm (a k))"
  assumes b: "summable (\<lambda>k. norm (b k))"
  shows "(\<lambda>k. \<Sum>i=0..k. a i * b (k - i)) sums ((\<Sum>k. a k) * (\<Sum>k. b k))"
proof -
  let ?S1 = "\<lambda>n::nat. {0..<n} \<times> {0..<n}"
  let ?S2 = "\<lambda>n::nat. {(i,j). i + j < n}"
  have S1_mono: "\<And>m n. m \<le> n \<Longrightarrow> ?S1 m \<subseteq> ?S1 n" by auto
  have S2_le_S1: "\<And>n. ?S2 n \<subseteq> ?S1 n" by auto
  have S1_le_S2: "\<And>n. ?S1 (n div 2) \<subseteq> ?S2 n" by auto
  have finite_S1: "\<And>n. finite (?S1 n)" by simp
  with S2_le_S1 have finite_S2: "\<And>n. finite (?S2 n)" by (rule finite_subset)

  let ?g = "\<lambda>(i,j). a i * b j"
  let ?f = "\<lambda>(i,j). norm (a i) * norm (b j)"
  have f_nonneg: "\<And>x. 0 \<le> ?f x"
    by (auto simp add: mult_nonneg_nonneg)
  hence norm_setsum_f: "\<And>A. norm (setsum ?f A) = setsum ?f A"
    unfolding real_norm_def
    by (simp only: abs_of_nonneg setsum_nonneg [rule_format])

  have "(\<lambda>n. (\<Sum>k=0..<n. a k) * (\<Sum>k=0..<n. b k))
           ----> (\<Sum>k. a k) * (\<Sum>k. b k)"
    by (intro tendsto_mult summable_sumr_LIMSEQ_suminf
        summable_norm_cancel [OF a] summable_norm_cancel [OF b])
  hence 1: "(\<lambda>n. setsum ?g (?S1 n)) ----> (\<Sum>k. a k) * (\<Sum>k. b k)"
    by (simp only: setsum_product setsum_Sigma [rule_format]
                   finite_atLeastLessThan)

  have "(\<lambda>n. (\<Sum>k=0..<n. norm (a k)) * (\<Sum>k=0..<n. norm (b k)))
       ----> (\<Sum>k. norm (a k)) * (\<Sum>k. norm (b k))"
    using a b by (intro tendsto_mult summable_sumr_LIMSEQ_suminf)
  hence "(\<lambda>n. setsum ?f (?S1 n)) ----> (\<Sum>k. norm (a k)) * (\<Sum>k. norm (b k))"
    by (simp only: setsum_product setsum_Sigma [rule_format]
                   finite_atLeastLessThan)
  hence "convergent (\<lambda>n. setsum ?f (?S1 n))"
    by (rule convergentI)
  hence Cauchy: "Cauchy (\<lambda>n. setsum ?f (?S1 n))"
    by (rule convergent_Cauchy)
  have "Zfun (\<lambda>n. setsum ?f (?S1 n - ?S2 n)) sequentially"
  proof (rule ZfunI, simp only: eventually_sequentially norm_setsum_f)
    fix r :: real
    assume r: "0 < r"
    from CauchyD [OF Cauchy r] obtain N
    where "\<forall>m\<ge>N. \<forall>n\<ge>N. norm (setsum ?f (?S1 m) - setsum ?f (?S1 n)) < r" ..
    hence "\<And>m n. \<lbrakk>N \<le> n; n \<le> m\<rbrakk> \<Longrightarrow> norm (setsum ?f (?S1 m - ?S1 n)) < r"
      by (simp only: setsum_diff finite_S1 S1_mono)
    hence N: "\<And>m n. \<lbrakk>N \<le> n; n \<le> m\<rbrakk> \<Longrightarrow> setsum ?f (?S1 m - ?S1 n) < r"
      by (simp only: norm_setsum_f)
    show "\<exists>N. \<forall>n\<ge>N. setsum ?f (?S1 n - ?S2 n) < r"
    proof (intro exI allI impI)
      fix n assume "2 * N \<le> n"
      hence n: "N \<le> n div 2" by simp
      have "setsum ?f (?S1 n - ?S2 n) \<le> setsum ?f (?S1 n - ?S1 (n div 2))"
        by (intro setsum_mono2 finite_Diff finite_S1 f_nonneg
                  Diff_mono subset_refl S1_le_S2)
      also have "\<dots> < r"
        using n div_le_dividend by (rule N)
      finally show "setsum ?f (?S1 n - ?S2 n) < r" .
    qed
  qed
  hence "Zfun (\<lambda>n. setsum ?g (?S1 n - ?S2 n)) sequentially"
    apply (rule Zfun_le [rule_format])
    apply (simp only: norm_setsum_f)
    apply (rule order_trans [OF norm_setsum setsum_mono])
    apply (auto simp add: norm_mult_ineq)
    done
  hence 2: "(\<lambda>n. setsum ?g (?S1 n) - setsum ?g (?S2 n)) ----> 0"
    unfolding tendsto_Zfun_iff diff_0_right
    by (simp only: setsum_diff finite_S1 S2_le_S1)

  with 1 have "(\<lambda>n. setsum ?g (?S2 n)) ----> (\<Sum>k. a k) * (\<Sum>k. b k)"
    by (rule LIMSEQ_diff_approach_zero2)
  thus ?thesis by (simp only: sums_def setsum_triangle_reindex)
qed

lemma Cauchy_product:
  fixes a b :: "nat \<Rightarrow> 'a::{real_normed_algebra,banach}"
  assumes a: "summable (\<lambda>k. norm (a k))"
  assumes b: "summable (\<lambda>k. norm (b k))"
  shows "(\<Sum>k. a k) * (\<Sum>k. b k) = (\<Sum>k. \<Sum>i=0..k. a i * b (k - i))"
using a b
by (rule Cauchy_product_sums [THEN sums_unique])

end
