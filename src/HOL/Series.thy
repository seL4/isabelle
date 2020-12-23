(*  Title       : Series.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp
Converted to sum and polished yet more by TNN
Additional contributions by Jeremy Avigad
*)

section \<open>Infinite Series\<close>

theory Series
imports Limits Inequalities
begin

subsection \<open>Definition of infinite summability\<close>

definition sums :: "(nat \<Rightarrow> 'a::{topological_space, comm_monoid_add}) \<Rightarrow> 'a \<Rightarrow> bool"
    (infixr "sums" 80)
  where "f sums s \<longleftrightarrow> (\<lambda>n. \<Sum>i<n. f i) \<longlonglongrightarrow> s"

definition summable :: "(nat \<Rightarrow> 'a::{topological_space, comm_monoid_add}) \<Rightarrow> bool"
  where "summable f \<longleftrightarrow> (\<exists>s. f sums s)"

definition suminf :: "(nat \<Rightarrow> 'a::{topological_space, comm_monoid_add}) \<Rightarrow> 'a"
    (binder "\<Sum>" 10)
  where "suminf f = (THE s. f sums s)"

text\<open>Variants of the definition\<close>
lemma sums_def': "f sums s \<longleftrightarrow> (\<lambda>n. \<Sum>i = 0..n. f i) \<longlonglongrightarrow> s"
  unfolding sums_def
  apply (subst filterlim_sequentially_Suc [symmetric])
  apply (simp only: lessThan_Suc_atMost atLeast0AtMost)
  done

lemma sums_def_le: "f sums s \<longleftrightarrow> (\<lambda>n. \<Sum>i\<le>n. f i) \<longlonglongrightarrow> s"
  by (simp add: sums_def' atMost_atLeast0)

lemma bounded_imp_summable:
  fixes a :: "nat \<Rightarrow> 'a::{conditionally_complete_linorder,linorder_topology,linordered_comm_semiring_strict}"
  assumes 0: "\<And>n. a n \<ge> 0" and bounded: "\<And>n. (\<Sum>k\<le>n. a k) \<le> B"
  shows "summable a" 
proof -
  have "bdd_above (range(\<lambda>n. \<Sum>k\<le>n. a k))"
    by (meson bdd_aboveI2 bounded)
  moreover have "incseq (\<lambda>n. \<Sum>k\<le>n. a k)"
    by (simp add: mono_def "0" sum_mono2)
  ultimately obtain s where "(\<lambda>n. \<Sum>k\<le>n. a k) \<longlonglongrightarrow> s"
    using LIMSEQ_incseq_SUP by blast
  then show ?thesis
    by (auto simp: sums_def_le summable_def)
qed


subsection \<open>Infinite summability on topological monoids\<close>

lemma sums_subst[trans]: "f = g \<Longrightarrow> g sums z \<Longrightarrow> f sums z"
  by simp

lemma sums_cong: "(\<And>n. f n = g n) \<Longrightarrow> f sums c \<longleftrightarrow> g sums c"
  by (drule ext) simp

lemma sums_summable: "f sums l \<Longrightarrow> summable f"
  by (simp add: sums_def summable_def, blast)

lemma summable_iff_convergent: "summable f \<longleftrightarrow> convergent (\<lambda>n. \<Sum>i<n. f i)"
  by (simp add: summable_def sums_def convergent_def)

lemma summable_iff_convergent': "summable f \<longleftrightarrow> convergent (\<lambda>n. sum f {..n})"
  by (simp_all only: summable_iff_convergent convergent_def
        lessThan_Suc_atMost [symmetric] filterlim_sequentially_Suc[of "\<lambda>n. sum f {..<n}"])

lemma suminf_eq_lim: "suminf f = lim (\<lambda>n. \<Sum>i<n. f i)"
  by (simp add: suminf_def sums_def lim_def)

lemma sums_zero[simp, intro]: "(\<lambda>n. 0) sums 0"
  unfolding sums_def by simp

lemma summable_zero[simp, intro]: "summable (\<lambda>n. 0)"
  by (rule sums_zero [THEN sums_summable])

lemma sums_group: "f sums s \<Longrightarrow> 0 < k \<Longrightarrow> (\<lambda>n. sum f {n * k ..< n * k + k}) sums s"
  apply (simp only: sums_def sum.nat_group tendsto_def eventually_sequentially)
  apply (erule all_forward imp_forward exE| assumption)+
  apply (rule_tac x="N" in exI)
  by (metis le_square mult.commute mult.left_neutral mult_le_cancel2 mult_le_mono)

lemma suminf_cong: "(\<And>n. f n = g n) \<Longrightarrow> suminf f = suminf g"
  by (rule arg_cong[of f g], rule ext) simp

lemma summable_cong:
  fixes f g :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes "eventually (\<lambda>x. f x = g x) sequentially"
  shows "summable f = summable g"
proof -
  from assms obtain N where N: "\<forall>n\<ge>N. f n = g n"
    by (auto simp: eventually_at_top_linorder)
  define C where "C = (\<Sum>k<N. f k - g k)"
  from eventually_ge_at_top[of N]
  have "eventually (\<lambda>n. sum f {..<n} = C + sum g {..<n}) sequentially"
  proof eventually_elim
    case (elim n)
    then have "{..<n} = {..<N} \<union> {N..<n}"
      by auto
    also have "sum f ... = sum f {..<N} + sum f {N..<n}"
      by (intro sum.union_disjoint) auto
    also from N have "sum f {N..<n} = sum g {N..<n}"
      by (intro sum.cong) simp_all
    also have "sum f {..<N} + sum g {N..<n} = C + (sum g {..<N} + sum g {N..<n})"
      unfolding C_def by (simp add: algebra_simps sum_subtractf)
    also have "sum g {..<N} + sum g {N..<n} = sum g ({..<N} \<union> {N..<n})"
      by (intro sum.union_disjoint [symmetric]) auto
    also from elim have "{..<N} \<union> {N..<n} = {..<n}"
      by auto
    finally show "sum f {..<n} = C + sum g {..<n}" .
  qed
  from convergent_cong[OF this] show ?thesis
    by (simp add: summable_iff_convergent convergent_add_const_iff)
qed

lemma sums_finite:
  assumes [simp]: "finite N"
    and f: "\<And>n. n \<notin> N \<Longrightarrow> f n = 0"
  shows "f sums (\<Sum>n\<in>N. f n)"
proof -
  have eq: "sum f {..<n + Suc (Max N)} = sum f N" for n
    by (rule sum.mono_neutral_right) (auto simp: add_increasing less_Suc_eq_le f)
  show ?thesis
    unfolding sums_def
    by (rule LIMSEQ_offset[of _ "Suc (Max N)"])
      (simp add: eq atLeast0LessThan del: add_Suc_right)
qed

corollary sums_0: "(\<And>n. f n = 0) \<Longrightarrow> (f sums 0)"
    by (metis (no_types) finite.emptyI sum.empty sums_finite)

lemma summable_finite: "finite N \<Longrightarrow> (\<And>n. n \<notin> N \<Longrightarrow> f n = 0) \<Longrightarrow> summable f"
  by (rule sums_summable) (rule sums_finite)

lemma sums_If_finite_set: "finite A \<Longrightarrow> (\<lambda>r. if r \<in> A then f r else 0) sums (\<Sum>r\<in>A. f r)"
  using sums_finite[of A "(\<lambda>r. if r \<in> A then f r else 0)"] by simp

lemma summable_If_finite_set[simp, intro]: "finite A \<Longrightarrow> summable (\<lambda>r. if r \<in> A then f r else 0)"
  by (rule sums_summable) (rule sums_If_finite_set)

lemma sums_If_finite: "finite {r. P r} \<Longrightarrow> (\<lambda>r. if P r then f r else 0) sums (\<Sum>r | P r. f r)"
  using sums_If_finite_set[of "{r. P r}"] by simp

lemma summable_If_finite[simp, intro]: "finite {r. P r} \<Longrightarrow> summable (\<lambda>r. if P r then f r else 0)"
  by (rule sums_summable) (rule sums_If_finite)

lemma sums_single: "(\<lambda>r. if r = i then f r else 0) sums f i"
  using sums_If_finite[of "\<lambda>r. r = i"] by simp

lemma summable_single[simp, intro]: "summable (\<lambda>r. if r = i then f r else 0)"
  by (rule sums_summable) (rule sums_single)

context
  fixes f :: "nat \<Rightarrow> 'a::{t2_space,comm_monoid_add}"
begin

lemma summable_sums[intro]: "summable f \<Longrightarrow> f sums (suminf f)"
  by (simp add: summable_def sums_def suminf_def)
     (metis convergent_LIMSEQ_iff convergent_def lim_def)

lemma summable_LIMSEQ: "summable f \<Longrightarrow> (\<lambda>n. \<Sum>i<n. f i) \<longlonglongrightarrow> suminf f"
  by (rule summable_sums [unfolded sums_def])

lemma summable_LIMSEQ': "summable f \<Longrightarrow> (\<lambda>n. \<Sum>i\<le>n. f i) \<longlonglongrightarrow> suminf f"
  using sums_def_le by blast

lemma sums_unique: "f sums s \<Longrightarrow> s = suminf f"
  by (metis limI suminf_eq_lim sums_def)

lemma sums_iff: "f sums x \<longleftrightarrow> summable f \<and> suminf f = x"
  by (metis summable_sums sums_summable sums_unique)

lemma summable_sums_iff: "summable f \<longleftrightarrow> f sums suminf f"
  by (auto simp: sums_iff summable_sums)

lemma sums_unique2: "f sums a \<Longrightarrow> f sums b \<Longrightarrow> a = b"
  for a b :: 'a
  by (simp add: sums_iff)

lemma sums_Uniq: "\<exists>\<^sub>\<le>\<^sub>1a. f sums a"
  for a b :: 'a
  by (simp add: sums_unique2 Uniq_def)

lemma suminf_finite:
  assumes N: "finite N"
    and f: "\<And>n. n \<notin> N \<Longrightarrow> f n = 0"
  shows "suminf f = (\<Sum>n\<in>N. f n)"
  using sums_finite[OF assms, THEN sums_unique] by simp

end

lemma suminf_zero[simp]: "suminf (\<lambda>n. 0::'a::{t2_space, comm_monoid_add}) = 0"
  by (rule sums_zero [THEN sums_unique, symmetric])


subsection \<open>Infinite summability on ordered, topological monoids\<close>

lemma sums_le: "(\<And>n. f n \<le> g n) \<Longrightarrow> f sums s \<Longrightarrow> g sums t \<Longrightarrow> s \<le> t"
  for f g :: "nat \<Rightarrow> 'a::{ordered_comm_monoid_add,linorder_topology}"
  by (rule LIMSEQ_le) (auto intro: sum_mono simp: sums_def)

context
  fixes f :: "nat \<Rightarrow> 'a::{ordered_comm_monoid_add,linorder_topology}"
begin

lemma suminf_le: "(\<And>n. f n \<le> g n) \<Longrightarrow> summable f \<Longrightarrow> summable g \<Longrightarrow> suminf f \<le> suminf g"
  using sums_le by blast

lemma sum_le_suminf:
  shows "summable f \<Longrightarrow> finite I \<Longrightarrow> (\<And>n. n \<in>- I \<Longrightarrow> 0 \<le> f n) \<Longrightarrow> sum f I \<le> suminf f"
  by (rule sums_le[OF _ sums_If_finite_set summable_sums]) auto

lemma suminf_nonneg: "summable f \<Longrightarrow> (\<And>n. 0 \<le> f n) \<Longrightarrow> 0 \<le> suminf f"
  using sum_le_suminf by force

lemma suminf_le_const: "summable f \<Longrightarrow> (\<And>n. sum f {..<n} \<le> x) \<Longrightarrow> suminf f \<le> x"
  by (metis LIMSEQ_le_const2 summable_LIMSEQ)

lemma suminf_eq_zero_iff: 
  assumes "summable f" and pos: "\<And>n. 0 \<le> f n"
  shows "suminf f = 0 \<longleftrightarrow> (\<forall>n. f n = 0)"
proof
  assume "suminf f = 0" 
  then have f: "(\<lambda>n. \<Sum>i<n. f i) \<longlonglongrightarrow> 0"
    using summable_LIMSEQ[of f] assms by simp
  then have "\<And>i. (\<Sum>n\<in>{i}. f n) \<le> 0"
  proof (rule LIMSEQ_le_const)
    show "\<exists>N. \<forall>n\<ge>N. (\<Sum>n\<in>{i}. f n) \<le> sum f {..<n}" for i
      using pos by (intro exI[of _ "Suc i"] allI impI sum_mono2) auto
  qed
  with pos show "\<forall>n. f n = 0"
    by (auto intro!: antisym)
qed (metis suminf_zero fun_eq_iff)

lemma suminf_pos_iff: "summable f \<Longrightarrow> (\<And>n. 0 \<le> f n) \<Longrightarrow> 0 < suminf f \<longleftrightarrow> (\<exists>i. 0 < f i)"
  using sum_le_suminf[of "{}"] suminf_eq_zero_iff by (simp add: less_le)

lemma suminf_pos2:
  assumes "summable f" "\<And>n. 0 \<le> f n" "0 < f i"
  shows "0 < suminf f"
proof -
  have "0 < (\<Sum>n<Suc i. f n)"
    using assms by (intro sum_pos2[where i=i]) auto
  also have "\<dots> \<le> suminf f"
    using assms by (intro sum_le_suminf) auto
  finally show ?thesis .
qed

lemma suminf_pos: "summable f \<Longrightarrow> (\<And>n. 0 < f n) \<Longrightarrow> 0 < suminf f"
  by (intro suminf_pos2[where i=0]) (auto intro: less_imp_le)

end

context
  fixes f :: "nat \<Rightarrow> 'a::{ordered_cancel_comm_monoid_add,linorder_topology}"
begin

lemma sum_less_suminf2:
  "summable f \<Longrightarrow> (\<And>m. m\<ge>n \<Longrightarrow> 0 \<le> f m) \<Longrightarrow> n \<le> i \<Longrightarrow> 0 < f i \<Longrightarrow> sum f {..<n} < suminf f"
  using sum_le_suminf[of f "{..< Suc i}"]
    and add_strict_increasing[of "f i" "sum f {..<n}" "sum f {..<i}"]
    and sum_mono2[of "{..<i}" "{..<n}" f]
  by (auto simp: less_imp_le ac_simps)

lemma sum_less_suminf: "summable f \<Longrightarrow> (\<And>m. m\<ge>n \<Longrightarrow> 0 < f m) \<Longrightarrow> sum f {..<n} < suminf f"
  using sum_less_suminf2[of n n] by (simp add: less_imp_le)

end

lemma summableI_nonneg_bounded:
  fixes f :: "nat \<Rightarrow> 'a::{ordered_comm_monoid_add,linorder_topology,conditionally_complete_linorder}"
  assumes pos[simp]: "\<And>n. 0 \<le> f n"
    and le: "\<And>n. (\<Sum>i<n. f i) \<le> x"
  shows "summable f"
  unfolding summable_def sums_def [abs_def]
proof (rule exI LIMSEQ_incseq_SUP)+
  show "bdd_above (range (\<lambda>n. sum f {..<n}))"
    using le by (auto simp: bdd_above_def)
  show "incseq (\<lambda>n. sum f {..<n})"
    by (auto simp: mono_def intro!: sum_mono2)
qed

lemma summableI[intro, simp]: "summable f"
  for f :: "nat \<Rightarrow> 'a::{canonically_ordered_monoid_add,linorder_topology,complete_linorder}"
  by (intro summableI_nonneg_bounded[where x=top] zero_le top_greatest)

lemma suminf_eq_SUP_real:
  assumes X: "summable X" "\<And>i. 0 \<le> X i" shows "suminf X = (SUP i. \<Sum>n<i. X n::real)"
  by (intro LIMSEQ_unique[OF summable_LIMSEQ] X LIMSEQ_incseq_SUP)
     (auto intro!: bdd_aboveI2[where M="\<Sum>i. X i"] sum_le_suminf X monoI sum_mono2)


subsection \<open>Infinite summability on topological monoids\<close>

context
  fixes f g :: "nat \<Rightarrow> 'a::{t2_space,topological_comm_monoid_add}"
begin

lemma sums_Suc:
  assumes "(\<lambda>n. f (Suc n)) sums l"
  shows "f sums (l + f 0)"
proof  -
  have "(\<lambda>n. (\<Sum>i<n. f (Suc i)) + f 0) \<longlonglongrightarrow> l + f 0"
    using assms by (auto intro!: tendsto_add simp: sums_def)
  moreover have "(\<Sum>i<n. f (Suc i)) + f 0 = (\<Sum>i<Suc n. f i)" for n
    unfolding lessThan_Suc_eq_insert_0
    by (simp add: ac_simps sum.atLeast1_atMost_eq image_Suc_lessThan)
  ultimately show ?thesis
    by (auto simp: sums_def simp del: sum.lessThan_Suc intro: filterlim_sequentially_Suc[THEN iffD1])
qed

lemma sums_add: "f sums a \<Longrightarrow> g sums b \<Longrightarrow> (\<lambda>n. f n + g n) sums (a + b)"
  unfolding sums_def by (simp add: sum.distrib tendsto_add)

lemma summable_add: "summable f \<Longrightarrow> summable g \<Longrightarrow> summable (\<lambda>n. f n + g n)"
  unfolding summable_def by (auto intro: sums_add)

lemma suminf_add: "summable f \<Longrightarrow> summable g \<Longrightarrow> suminf f + suminf g = (\<Sum>n. f n + g n)"
  by (intro sums_unique sums_add summable_sums)

end

context
  fixes f :: "'i \<Rightarrow> nat \<Rightarrow> 'a::{t2_space,topological_comm_monoid_add}"
    and I :: "'i set"
begin

lemma sums_sum: "(\<And>i. i \<in> I \<Longrightarrow> (f i) sums (x i)) \<Longrightarrow> (\<lambda>n. \<Sum>i\<in>I. f i n) sums (\<Sum>i\<in>I. x i)"
  by (induct I rule: infinite_finite_induct) (auto intro!: sums_add)

lemma suminf_sum: "(\<And>i. i \<in> I \<Longrightarrow> summable (f i)) \<Longrightarrow> (\<Sum>n. \<Sum>i\<in>I. f i n) = (\<Sum>i\<in>I. \<Sum>n. f i n)"
  using sums_unique[OF sums_sum, OF summable_sums] by simp

lemma summable_sum: "(\<And>i. i \<in> I \<Longrightarrow> summable (f i)) \<Longrightarrow> summable (\<lambda>n. \<Sum>i\<in>I. f i n)"
  using sums_summable[OF sums_sum[OF summable_sums]] .

end

lemma sums_If_finite_set':
  fixes f g :: "nat \<Rightarrow> 'a::{t2_space,topological_ab_group_add}"
  assumes "g sums S" and "finite A" and "S' = S + (\<Sum>n\<in>A. f n - g n)"
  shows   "(\<lambda>n. if n \<in> A then f n else g n) sums S'"
proof -
  have "(\<lambda>n. g n + (if n \<in> A then f n - g n else 0)) sums (S + (\<Sum>n\<in>A. f n - g n))"
    by (intro sums_add assms sums_If_finite_set)
  also have "(\<lambda>n. g n + (if n \<in> A then f n - g n else 0)) = (\<lambda>n. if n \<in> A then f n else g n)"
    by (simp add: fun_eq_iff)
  finally show ?thesis using assms by simp
qed

subsection \<open>Infinite summability on real normed vector spaces\<close>

context
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
begin

lemma sums_Suc_iff: "(\<lambda>n. f (Suc n)) sums s \<longleftrightarrow> f sums (s + f 0)"
proof -
  have "f sums (s + f 0) \<longleftrightarrow> (\<lambda>i. \<Sum>j<Suc i. f j) \<longlonglongrightarrow> s + f 0"
    by (subst filterlim_sequentially_Suc) (simp add: sums_def)
  also have "\<dots> \<longleftrightarrow> (\<lambda>i. (\<Sum>j<i. f (Suc j)) + f 0) \<longlonglongrightarrow> s + f 0"
    by (simp add: ac_simps lessThan_Suc_eq_insert_0 image_Suc_lessThan sum.atLeast1_atMost_eq)
  also have "\<dots> \<longleftrightarrow> (\<lambda>n. f (Suc n)) sums s"
  proof
    assume "(\<lambda>i. (\<Sum>j<i. f (Suc j)) + f 0) \<longlonglongrightarrow> s + f 0"
    with tendsto_add[OF this tendsto_const, of "- f 0"] show "(\<lambda>i. f (Suc i)) sums s"
      by (simp add: sums_def)
  qed (auto intro: tendsto_add simp: sums_def)
  finally show ?thesis ..
qed

lemma summable_Suc_iff: "summable (\<lambda>n. f (Suc n)) = summable f"
proof
  assume "summable f"
  then have "f sums suminf f"
    by (rule summable_sums)
  then have "(\<lambda>n. f (Suc n)) sums (suminf f - f 0)"
    by (simp add: sums_Suc_iff)
  then show "summable (\<lambda>n. f (Suc n))"
    unfolding summable_def by blast
qed (auto simp: sums_Suc_iff summable_def)

lemma sums_Suc_imp: "f 0 = 0 \<Longrightarrow> (\<lambda>n. f (Suc n)) sums s \<Longrightarrow> (\<lambda>n. f n) sums s"
  using sums_Suc_iff by simp

end

context (* Separate contexts are necessary to allow general use of the results above, here. *)
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
begin

lemma sums_diff: "f sums a \<Longrightarrow> g sums b \<Longrightarrow> (\<lambda>n. f n - g n) sums (a - b)"
  unfolding sums_def by (simp add: sum_subtractf tendsto_diff)

lemma summable_diff: "summable f \<Longrightarrow> summable g \<Longrightarrow> summable (\<lambda>n. f n - g n)"
  unfolding summable_def by (auto intro: sums_diff)

lemma suminf_diff: "summable f \<Longrightarrow> summable g \<Longrightarrow> suminf f - suminf g = (\<Sum>n. f n - g n)"
  by (intro sums_unique sums_diff summable_sums)

lemma sums_minus: "f sums a \<Longrightarrow> (\<lambda>n. - f n) sums (- a)"
  unfolding sums_def by (simp add: sum_negf tendsto_minus)

lemma summable_minus: "summable f \<Longrightarrow> summable (\<lambda>n. - f n)"
  unfolding summable_def by (auto intro: sums_minus)

lemma suminf_minus: "summable f \<Longrightarrow> (\<Sum>n. - f n) = - (\<Sum>n. f n)"
  by (intro sums_unique [symmetric] sums_minus summable_sums)

lemma sums_iff_shift: "(\<lambda>i. f (i + n)) sums s \<longleftrightarrow> f sums (s + (\<Sum>i<n. f i))"
proof (induct n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "(\<lambda>i. f (Suc i + n)) sums s \<longleftrightarrow> (\<lambda>i. f (i + n)) sums (s + f n)"
    by (subst sums_Suc_iff) simp
  with Suc show ?case
    by (simp add: ac_simps)
qed

corollary sums_iff_shift': "(\<lambda>i. f (i + n)) sums (s - (\<Sum>i<n. f i)) \<longleftrightarrow> f sums s"
  by (simp add: sums_iff_shift)

lemma sums_zero_iff_shift:
  assumes "\<And>i. i < n \<Longrightarrow> f i = 0"
  shows "(\<lambda>i. f (i+n)) sums s \<longleftrightarrow> (\<lambda>i. f i) sums s"
  by (simp add: assms sums_iff_shift)

lemma summable_iff_shift: "summable (\<lambda>n. f (n + k)) \<longleftrightarrow> summable f"
  by (metis diff_add_cancel summable_def sums_iff_shift [abs_def])

lemma sums_split_initial_segment: "f sums s \<Longrightarrow> (\<lambda>i. f (i + n)) sums (s - (\<Sum>i<n. f i))"
  by (simp add: sums_iff_shift)

lemma summable_ignore_initial_segment: "summable f \<Longrightarrow> summable (\<lambda>n. f(n + k))"
  by (simp add: summable_iff_shift)

lemma suminf_minus_initial_segment: "summable f \<Longrightarrow> (\<Sum>n. f (n + k)) = (\<Sum>n. f n) - (\<Sum>i<k. f i)"
  by (rule sums_unique[symmetric]) (auto simp: sums_iff_shift)

lemma suminf_split_initial_segment: "summable f \<Longrightarrow> suminf f = (\<Sum>n. f(n + k)) + (\<Sum>i<k. f i)"
  by (auto simp add: suminf_minus_initial_segment)

lemma suminf_split_head: "summable f \<Longrightarrow> (\<Sum>n. f (Suc n)) = suminf f - f 0"
  using suminf_split_initial_segment[of 1] by simp

lemma suminf_exist_split:
  fixes r :: real
  assumes "0 < r" and "summable f"
  shows "\<exists>N. \<forall>n\<ge>N. norm (\<Sum>i. f (i + n)) < r"
proof -
  from LIMSEQ_D[OF summable_LIMSEQ[OF \<open>summable f\<close>] \<open>0 < r\<close>]
  obtain N :: nat where "\<forall> n \<ge> N. norm (sum f {..<n} - suminf f) < r"
    by auto
  then show ?thesis
    by (auto simp: norm_minus_commute suminf_minus_initial_segment[OF \<open>summable f\<close>])
qed

lemma summable_LIMSEQ_zero: 
  assumes "summable f" shows "f \<longlonglongrightarrow> 0"
proof -
  have "Cauchy (\<lambda>n. sum f {..<n})"
    using LIMSEQ_imp_Cauchy assms summable_LIMSEQ by blast
  then show ?thesis
    unfolding  Cauchy_iff LIMSEQ_iff
    by (metis add.commute add_diff_cancel_right' diff_zero le_SucI sum.lessThan_Suc)
qed

lemma summable_imp_convergent: "summable f \<Longrightarrow> convergent f"
  by (force dest!: summable_LIMSEQ_zero simp: convergent_def)

lemma summable_imp_Bseq: "summable f \<Longrightarrow> Bseq f"
  by (simp add: convergent_imp_Bseq summable_imp_convergent)

end

lemma summable_minus_iff: "summable (\<lambda>n. - f n) \<longleftrightarrow> summable f"
  for f :: "nat \<Rightarrow> 'a::real_normed_vector"
  by (auto dest: summable_minus)  (* used two ways, hence must be outside the context above *)

lemma (in bounded_linear) sums: "(\<lambda>n. X n) sums a \<Longrightarrow> (\<lambda>n. f (X n)) sums (f a)"
  unfolding sums_def by (drule tendsto) (simp only: sum)

lemma (in bounded_linear) summable: "summable (\<lambda>n. X n) \<Longrightarrow> summable (\<lambda>n. f (X n))"
  unfolding summable_def by (auto intro: sums)

lemma (in bounded_linear) suminf: "summable (\<lambda>n. X n) \<Longrightarrow> f (\<Sum>n. X n) = (\<Sum>n. f (X n))"
  by (intro sums_unique sums summable_sums)

lemmas sums_of_real = bounded_linear.sums [OF bounded_linear_of_real]
lemmas summable_of_real = bounded_linear.summable [OF bounded_linear_of_real]
lemmas suminf_of_real = bounded_linear.suminf [OF bounded_linear_of_real]

lemmas sums_scaleR_left = bounded_linear.sums[OF bounded_linear_scaleR_left]
lemmas summable_scaleR_left = bounded_linear.summable[OF bounded_linear_scaleR_left]
lemmas suminf_scaleR_left = bounded_linear.suminf[OF bounded_linear_scaleR_left]

lemmas sums_scaleR_right = bounded_linear.sums[OF bounded_linear_scaleR_right]
lemmas summable_scaleR_right = bounded_linear.summable[OF bounded_linear_scaleR_right]
lemmas suminf_scaleR_right = bounded_linear.suminf[OF bounded_linear_scaleR_right]

lemma summable_const_iff: "summable (\<lambda>_. c) \<longleftrightarrow> c = 0"
  for c :: "'a::real_normed_vector"
proof -
  have "\<not> summable (\<lambda>_. c)" if "c \<noteq> 0"
  proof -
    from that have "filterlim (\<lambda>n. of_nat n * norm c) at_top sequentially"
      by (subst mult.commute)
        (auto intro!: filterlim_tendsto_pos_mult_at_top filterlim_real_sequentially)
    then have "\<not> convergent (\<lambda>n. norm (\<Sum>k<n. c))"
      by (intro filterlim_at_infinity_imp_not_convergent filterlim_at_top_imp_at_infinity)
        (simp_all add: sum_constant_scaleR)
    then show ?thesis
      unfolding summable_iff_convergent using convergent_norm by blast
  qed
  then show ?thesis by auto
qed


subsection \<open>Infinite summability on real normed algebras\<close>

context
  fixes f :: "nat \<Rightarrow> 'a::real_normed_algebra"
begin

lemma sums_mult: "f sums a \<Longrightarrow> (\<lambda>n. c * f n) sums (c * a)"
  by (rule bounded_linear.sums [OF bounded_linear_mult_right])

lemma summable_mult: "summable f \<Longrightarrow> summable (\<lambda>n. c * f n)"
  by (rule bounded_linear.summable [OF bounded_linear_mult_right])

lemma suminf_mult: "summable f \<Longrightarrow> suminf (\<lambda>n. c * f n) = c * suminf f"
  by (rule bounded_linear.suminf [OF bounded_linear_mult_right, symmetric])

lemma sums_mult2: "f sums a \<Longrightarrow> (\<lambda>n. f n * c) sums (a * c)"
  by (rule bounded_linear.sums [OF bounded_linear_mult_left])

lemma summable_mult2: "summable f \<Longrightarrow> summable (\<lambda>n. f n * c)"
  by (rule bounded_linear.summable [OF bounded_linear_mult_left])

lemma suminf_mult2: "summable f \<Longrightarrow> suminf f * c = (\<Sum>n. f n * c)"
  by (rule bounded_linear.suminf [OF bounded_linear_mult_left])

end

lemma sums_mult_iff:
  fixes f :: "nat \<Rightarrow> 'a::{real_normed_algebra,field}"
  assumes "c \<noteq> 0"
  shows "(\<lambda>n. c * f n) sums (c * d) \<longleftrightarrow> f sums d"
  using sums_mult[of f d c] sums_mult[of "\<lambda>n. c * f n" "c * d" "inverse c"]
  by (force simp: field_simps assms)

lemma sums_mult2_iff:
  fixes f :: "nat \<Rightarrow> 'a::{real_normed_algebra,field}"
  assumes "c \<noteq> 0"
  shows   "(\<lambda>n. f n * c) sums (d * c) \<longleftrightarrow> f sums d"
  using sums_mult_iff[OF assms, of f d] by (simp add: mult.commute)

lemma sums_of_real_iff:
  "(\<lambda>n. of_real (f n) :: 'a::real_normed_div_algebra) sums of_real c \<longleftrightarrow> f sums c"
  by (simp add: sums_def of_real_sum[symmetric] tendsto_of_real_iff del: of_real_sum)


subsection \<open>Infinite summability on real normed fields\<close>

context
  fixes c :: "'a::real_normed_field"
begin

lemma sums_divide: "f sums a \<Longrightarrow> (\<lambda>n. f n / c) sums (a / c)"
  by (rule bounded_linear.sums [OF bounded_linear_divide])

lemma summable_divide: "summable f \<Longrightarrow> summable (\<lambda>n. f n / c)"
  by (rule bounded_linear.summable [OF bounded_linear_divide])

lemma suminf_divide: "summable f \<Longrightarrow> suminf (\<lambda>n. f n / c) = suminf f / c"
  by (rule bounded_linear.suminf [OF bounded_linear_divide, symmetric])

lemma summable_inverse_divide: "summable (inverse \<circ> f) \<Longrightarrow> summable (\<lambda>n. c / f n)"
  by (auto dest: summable_mult [of _ c] simp: field_simps)

lemma sums_mult_D: "(\<lambda>n. c * f n) sums a \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> f sums (a/c)"
  using sums_mult_iff by fastforce

lemma summable_mult_D: "summable (\<lambda>n. c * f n) \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> summable f"
  by (auto dest: summable_divide)


text \<open>Sum of a geometric progression.\<close>

lemma geometric_sums:
  assumes "norm c < 1"
  shows "(\<lambda>n. c^n) sums (1 / (1 - c))"
proof -
  have neq_0: "c - 1 \<noteq> 0"
    using assms by auto
  then have "(\<lambda>n. c ^ n / (c - 1) - 1 / (c - 1)) \<longlonglongrightarrow> 0 / (c - 1) - 1 / (c - 1)"
    by (intro tendsto_intros assms)
  then have "(\<lambda>n. (c ^ n - 1) / (c - 1)) \<longlonglongrightarrow> 1 / (1 - c)"
    by (simp add: nonzero_minus_divide_right [OF neq_0] diff_divide_distrib)
  with neq_0 show "(\<lambda>n. c ^ n) sums (1 / (1 - c))"
    by (simp add: sums_def geometric_sum)
qed

lemma summable_geometric: "norm c < 1 \<Longrightarrow> summable (\<lambda>n. c^n)"
  by (rule geometric_sums [THEN sums_summable])

lemma suminf_geometric: "norm c < 1 \<Longrightarrow> suminf (\<lambda>n. c^n) = 1 / (1 - c)"
  by (rule sums_unique[symmetric]) (rule geometric_sums)

lemma summable_geometric_iff [simp]: "summable (\<lambda>n. c ^ n) \<longleftrightarrow> norm c < 1"
proof
  assume "summable (\<lambda>n. c ^ n :: 'a :: real_normed_field)"
  then have "(\<lambda>n. norm c ^ n) \<longlonglongrightarrow> 0"
    by (simp add: norm_power [symmetric] tendsto_norm_zero_iff summable_LIMSEQ_zero)
  from order_tendstoD(2)[OF this zero_less_one] obtain n where "norm c ^ n < 1"
    by (auto simp: eventually_at_top_linorder)
  then show "norm c < 1" using one_le_power[of "norm c" n]
    by (cases "norm c \<ge> 1") (linarith, simp)
qed (rule summable_geometric)

end

lemma power_half_series: "(\<lambda>n. (1/2::real)^Suc n) sums 1"
proof -
  have 2: "(\<lambda>n. (1/2::real)^n) sums 2"
    using geometric_sums [of "1/2::real"] by auto
  have "(\<lambda>n. (1/2::real)^Suc n) = (\<lambda>n. (1 / 2) ^ n / 2)"
    by (simp add: mult.commute)
  then show ?thesis
    using sums_divide [OF 2, of 2] by simp
qed


subsection \<open>Telescoping\<close>

lemma telescope_sums:
  fixes c :: "'a::real_normed_vector"
  assumes "f \<longlonglongrightarrow> c"
  shows "(\<lambda>n. f (Suc n) - f n) sums (c - f 0)"
  unfolding sums_def
proof (subst filterlim_sequentially_Suc [symmetric])
  have "(\<lambda>n. \<Sum>k<Suc n. f (Suc k) - f k) = (\<lambda>n. f (Suc n) - f 0)"
    by (simp add: lessThan_Suc_atMost atLeast0AtMost [symmetric] sum_Suc_diff)
  also have "\<dots> \<longlonglongrightarrow> c - f 0"
    by (intro tendsto_diff LIMSEQ_Suc[OF assms] tendsto_const)
  finally show "(\<lambda>n. \<Sum>n<Suc n. f (Suc n) - f n) \<longlonglongrightarrow> c - f 0" .
qed

lemma telescope_sums':
  fixes c :: "'a::real_normed_vector"
  assumes "f \<longlonglongrightarrow> c"
  shows "(\<lambda>n. f n - f (Suc n)) sums (f 0 - c)"
  using sums_minus[OF telescope_sums[OF assms]] by (simp add: algebra_simps)

lemma telescope_summable:
  fixes c :: "'a::real_normed_vector"
  assumes "f \<longlonglongrightarrow> c"
  shows "summable (\<lambda>n. f (Suc n) - f n)"
  using telescope_sums[OF assms] by (simp add: sums_iff)

lemma telescope_summable':
  fixes c :: "'a::real_normed_vector"
  assumes "f \<longlonglongrightarrow> c"
  shows "summable (\<lambda>n. f n - f (Suc n))"
  using summable_minus[OF telescope_summable[OF assms]] by (simp add: algebra_simps)


subsection \<open>Infinite summability on Banach spaces\<close>

text \<open>Cauchy-type criterion for convergence of series (c.f. Harrison).\<close>

lemma summable_Cauchy: "summable f \<longleftrightarrow> (\<forall>e>0. \<exists>N. \<forall>m\<ge>N. \<forall>n. norm (sum f {m..<n}) < e)" (is "_ = ?rhs")
  for f :: "nat \<Rightarrow> 'a::banach"
proof
  assume f: "summable f"
  show ?rhs
  proof clarify
    fix e :: real
    assume "0 < e"
    then obtain M where M: "\<And>m n. \<lbrakk>m\<ge>M; n\<ge>M\<rbrakk> \<Longrightarrow> norm (sum f {..<m} - sum f {..<n}) < e"
      using f by (force simp add: summable_iff_convergent Cauchy_convergent_iff [symmetric] Cauchy_iff)
    have "norm (sum f {m..<n}) < e" if "m \<ge> M" for m n
    proof (cases m n rule: linorder_class.le_cases)
      assume "m \<le> n"
      then show ?thesis
        by (metis (mono_tags, hide_lams) M atLeast0LessThan order_trans sum_diff_nat_ivl that zero_le)
    next
      assume "n \<le> m"
      then show ?thesis
        by (simp add: \<open>0 < e\<close>)
    qed
    then show "\<exists>N. \<forall>m\<ge>N. \<forall>n. norm (sum f {m..<n}) < e"
      by blast
  qed
next
  assume r: ?rhs
  then show "summable f"
    unfolding summable_iff_convergent Cauchy_convergent_iff [symmetric] Cauchy_iff
  proof clarify
    fix e :: real
    assume "0 < e"
    with r obtain N where N: "\<And>m n. m \<ge> N \<Longrightarrow> norm (sum f {m..<n}) < e"
      by blast
    have "norm (sum f {..<m} - sum f {..<n}) < e" if "m\<ge>N" "n\<ge>N" for m n
    proof (cases m n rule: linorder_class.le_cases)
      assume "m \<le> n"
      then show ?thesis
        by (metis Groups_Big.sum_diff N finite_lessThan lessThan_minus_lessThan lessThan_subset_iff norm_minus_commute \<open>m\<ge>N\<close>)
    next
      assume "n \<le> m"
      then show ?thesis
        by (metis Groups_Big.sum_diff N finite_lessThan lessThan_minus_lessThan lessThan_subset_iff \<open>n\<ge>N\<close>)
    qed
    then show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (sum f {..<m} - sum f {..<n}) < e"
      by blast
  qed
qed

lemma summable_Cauchy':
  fixes f :: "nat \<Rightarrow> 'a :: banach"
  assumes "eventually (\<lambda>m. \<forall>n\<ge>m. norm (sum f {m..<n}) \<le> g m) sequentially"
  assumes "filterlim g (nhds 0) sequentially"
  shows "summable f"
proof (subst summable_Cauchy, intro allI impI, goal_cases)
  case (1 e)
  from order_tendstoD(2)[OF assms(2) this] and assms(1)
  have "eventually (\<lambda>m. \<forall>n. norm (sum f {m..<n}) < e) at_top"
  proof eventually_elim
    case (elim m)
    show ?case
    proof
      fix n
      from elim show "norm (sum f {m..<n}) < e"
        by (cases "n \<ge> m") auto
    qed
  qed
  thus ?case by (auto simp: eventually_at_top_linorder)
qed

context
  fixes f :: "nat \<Rightarrow> 'a::banach"
begin

text \<open>Absolute convergence imples normal convergence.\<close>

lemma summable_norm_cancel: "summable (\<lambda>n. norm (f n)) \<Longrightarrow> summable f"
  unfolding summable_Cauchy
  apply (erule all_forward imp_forward ex_forward | assumption)+
  apply (fastforce simp add: order_le_less_trans [OF norm_sum] order_le_less_trans [OF abs_ge_self])
  done

lemma summable_norm: "summable (\<lambda>n. norm (f n)) \<Longrightarrow> norm (suminf f) \<le> (\<Sum>n. norm (f n))"
  by (auto intro: LIMSEQ_le tendsto_norm summable_norm_cancel summable_LIMSEQ norm_sum)

text \<open>Comparison tests.\<close>

lemma summable_comparison_test: 
  assumes fg: "\<exists>N. \<forall>n\<ge>N. norm (f n) \<le> g n" and g: "summable g"
  shows "summable f"
proof -
  obtain N where N: "\<And>n. n\<ge>N \<Longrightarrow> norm (f n) \<le> g n" 
    using assms by blast
  show ?thesis
  proof (clarsimp simp add: summable_Cauchy)
    fix e :: real
    assume "0 < e"
    then obtain Ng where Ng: "\<And>m n. m \<ge> Ng \<Longrightarrow> norm (sum g {m..<n}) < e" 
      using g by (fastforce simp: summable_Cauchy)
    with N have "norm (sum f {m..<n}) < e" if "m\<ge>max N Ng" for m n
    proof -
      have "norm (sum f {m..<n}) \<le> sum g {m..<n}"
        using N that by (force intro: sum_norm_le)
      also have "... \<le> norm (sum g {m..<n})"
        by simp
      also have "... < e"
        using Ng that by auto
      finally show ?thesis .
    qed
    then show "\<exists>N. \<forall>m\<ge>N. \<forall>n. norm (sum f {m..<n}) < e" 
      by blast
  qed
qed

lemma summable_comparison_test_ev:
  "eventually (\<lambda>n. norm (f n) \<le> g n) sequentially \<Longrightarrow> summable g \<Longrightarrow> summable f"
  by (rule summable_comparison_test) (auto simp: eventually_at_top_linorder)

text \<open>A better argument order.\<close>
lemma summable_comparison_test': "summable g \<Longrightarrow> (\<And>n. n \<ge> N \<Longrightarrow> norm (f n) \<le> g n) \<Longrightarrow> summable f"
  by (rule summable_comparison_test) auto


subsection \<open>The Ratio Test\<close>

lemma summable_ratio_test:
  assumes "c < 1" "\<And>n. n \<ge> N \<Longrightarrow> norm (f (Suc n)) \<le> c * norm (f n)"
  shows "summable f"
proof (cases "0 < c")
  case True
  show "summable f"
  proof (rule summable_comparison_test)
    show "\<exists>N'. \<forall>n\<ge>N'. norm (f n) \<le> (norm (f N) / (c ^ N)) * c ^ n"
    proof (intro exI allI impI)
      fix n
      assume "N \<le> n"
      then show "norm (f n) \<le> (norm (f N) / (c ^ N)) * c ^ n"
      proof (induct rule: inc_induct)
        case base
        with True show ?case by simp
      next
        case (step m)
        have "norm (f (Suc m)) / c ^ Suc m * c ^ n \<le> norm (f m) / c ^ m * c ^ n"
          using \<open>0 < c\<close> \<open>c < 1\<close> assms(2)[OF \<open>N \<le> m\<close>] by (simp add: field_simps)
        with step show ?case by simp
      qed
    qed
    show "summable (\<lambda>n. norm (f N) / c ^ N * c ^ n)"
      using \<open>0 < c\<close> \<open>c < 1\<close> by (intro summable_mult summable_geometric) simp
  qed
next
  case False
  have "f (Suc n) = 0" if "n \<ge> N" for n
  proof -
    from that have "norm (f (Suc n)) \<le> c * norm (f n)"
      by (rule assms(2))
    also have "\<dots> \<le> 0"
      using False by (simp add: not_less mult_nonpos_nonneg)
    finally show ?thesis
      by auto
  qed
  then show "summable f"
    by (intro sums_summable[OF sums_finite, of "{.. Suc N}"]) (auto simp: not_le Suc_less_eq2)
qed

end


text \<open>Relations among convergence and absolute convergence for power series.\<close>

lemma Abel_lemma:
  fixes a :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes r: "0 \<le> r"
    and r0: "r < r0"
    and M: "\<And>n. norm (a n) * r0^n \<le> M"
  shows "summable (\<lambda>n. norm (a n) * r^n)"
proof (rule summable_comparison_test')
  show "summable (\<lambda>n. M * (r / r0) ^ n)"
    using assms by (auto simp add: summable_mult summable_geometric)
  show "norm (norm (a n) * r ^ n) \<le> M * (r / r0) ^ n" for n
    using r r0 M [of n] dual_order.order_iff_strict
    by (fastforce simp add: abs_mult field_simps)
qed


text \<open>Summability of geometric series for real algebras.\<close>

lemma complete_algebra_summable_geometric:
  fixes x :: "'a::{real_normed_algebra_1,banach}"
  assumes "norm x < 1"
  shows "summable (\<lambda>n. x ^ n)"
proof (rule summable_comparison_test)
  show "\<exists>N. \<forall>n\<ge>N. norm (x ^ n) \<le> norm x ^ n"
    by (simp add: norm_power_ineq)
  from assms show "summable (\<lambda>n. norm x ^ n)"
    by (simp add: summable_geometric)
qed


subsection \<open>Cauchy Product Formula\<close>

text \<open>
  Proof based on Analysis WebNotes: Chapter 07, Class 41
  \<^url>\<open>http://www.math.unl.edu/~webnotes/classes/class41/prp77.htm\<close>
\<close>

lemma Cauchy_product_sums:
  fixes a b :: "nat \<Rightarrow> 'a::{real_normed_algebra,banach}"
  assumes a: "summable (\<lambda>k. norm (a k))"
    and b: "summable (\<lambda>k. norm (b k))"
  shows "(\<lambda>k. \<Sum>i\<le>k. a i * b (k - i)) sums ((\<Sum>k. a k) * (\<Sum>k. b k))"
proof -
  let ?S1 = "\<lambda>n::nat. {..<n} \<times> {..<n}"
  let ?S2 = "\<lambda>n::nat. {(i,j). i + j < n}"
  have S1_mono: "\<And>m n. m \<le> n \<Longrightarrow> ?S1 m \<subseteq> ?S1 n" by auto
  have S2_le_S1: "\<And>n. ?S2 n \<subseteq> ?S1 n" by auto
  have S1_le_S2: "\<And>n. ?S1 (n div 2) \<subseteq> ?S2 n" by auto
  have finite_S1: "\<And>n. finite (?S1 n)" by simp
  with S2_le_S1 have finite_S2: "\<And>n. finite (?S2 n)" by (rule finite_subset)

  let ?g = "\<lambda>(i,j). a i * b j"
  let ?f = "\<lambda>(i,j). norm (a i) * norm (b j)"
  have f_nonneg: "\<And>x. 0 \<le> ?f x" by auto
  then have norm_sum_f: "\<And>A. norm (sum ?f A) = sum ?f A"
    unfolding real_norm_def
    by (simp only: abs_of_nonneg sum_nonneg [rule_format])

  have "(\<lambda>n. (\<Sum>k<n. a k) * (\<Sum>k<n. b k)) \<longlonglongrightarrow> (\<Sum>k. a k) * (\<Sum>k. b k)"
    by (intro tendsto_mult summable_LIMSEQ summable_norm_cancel [OF a] summable_norm_cancel [OF b])
  then have 1: "(\<lambda>n. sum ?g (?S1 n)) \<longlonglongrightarrow> (\<Sum>k. a k) * (\<Sum>k. b k)"
    by (simp only: sum_product sum.Sigma [rule_format] finite_lessThan)

  have "(\<lambda>n. (\<Sum>k<n. norm (a k)) * (\<Sum>k<n. norm (b k))) \<longlonglongrightarrow> (\<Sum>k. norm (a k)) * (\<Sum>k. norm (b k))"
    using a b by (intro tendsto_mult summable_LIMSEQ)
  then have "(\<lambda>n. sum ?f (?S1 n)) \<longlonglongrightarrow> (\<Sum>k. norm (a k)) * (\<Sum>k. norm (b k))"
    by (simp only: sum_product sum.Sigma [rule_format] finite_lessThan)
  then have "convergent (\<lambda>n. sum ?f (?S1 n))"
    by (rule convergentI)
  then have Cauchy: "Cauchy (\<lambda>n. sum ?f (?S1 n))"
    by (rule convergent_Cauchy)
  have "Zfun (\<lambda>n. sum ?f (?S1 n - ?S2 n)) sequentially"
  proof (rule ZfunI, simp only: eventually_sequentially norm_sum_f)
    fix r :: real
    assume r: "0 < r"
    from CauchyD [OF Cauchy r] obtain N
      where "\<forall>m\<ge>N. \<forall>n\<ge>N. norm (sum ?f (?S1 m) - sum ?f (?S1 n)) < r" ..
    then have "\<And>m n. N \<le> n \<Longrightarrow> n \<le> m \<Longrightarrow> norm (sum ?f (?S1 m - ?S1 n)) < r"
      by (simp only: sum_diff finite_S1 S1_mono)
    then have N: "\<And>m n. N \<le> n \<Longrightarrow> n \<le> m \<Longrightarrow> sum ?f (?S1 m - ?S1 n) < r"
      by (simp only: norm_sum_f)
    show "\<exists>N. \<forall>n\<ge>N. sum ?f (?S1 n - ?S2 n) < r"
    proof (intro exI allI impI)
      fix n
      assume "2 * N \<le> n"
      then have n: "N \<le> n div 2" by simp
      have "sum ?f (?S1 n - ?S2 n) \<le> sum ?f (?S1 n - ?S1 (n div 2))"
        by (intro sum_mono2 finite_Diff finite_S1 f_nonneg Diff_mono subset_refl S1_le_S2)
      also have "\<dots> < r"
        using n div_le_dividend by (rule N)
      finally show "sum ?f (?S1 n - ?S2 n) < r" .
    qed
  qed
  then have "Zfun (\<lambda>n. sum ?g (?S1 n - ?S2 n)) sequentially"
    apply (rule Zfun_le [rule_format])
    apply (simp only: norm_sum_f)
    apply (rule order_trans [OF norm_sum sum_mono])
    apply (auto simp add: norm_mult_ineq)
    done
  then have 2: "(\<lambda>n. sum ?g (?S1 n) - sum ?g (?S2 n)) \<longlonglongrightarrow> 0"
    unfolding tendsto_Zfun_iff diff_0_right
    by (simp only: sum_diff finite_S1 S2_le_S1)
  with 1 have "(\<lambda>n. sum ?g (?S2 n)) \<longlonglongrightarrow> (\<Sum>k. a k) * (\<Sum>k. b k)"
    by (rule Lim_transform2)
  then show ?thesis
    by (simp only: sums_def sum.triangle_reindex)
qed

lemma Cauchy_product:
  fixes a b :: "nat \<Rightarrow> 'a::{real_normed_algebra,banach}"
  assumes "summable (\<lambda>k. norm (a k))"
    and "summable (\<lambda>k. norm (b k))"
  shows "(\<Sum>k. a k) * (\<Sum>k. b k) = (\<Sum>k. \<Sum>i\<le>k. a i * b (k - i))"
  using assms by (rule Cauchy_product_sums [THEN sums_unique])

lemma summable_Cauchy_product:
  fixes a b :: "nat \<Rightarrow> 'a::{real_normed_algebra,banach}"
  assumes "summable (\<lambda>k. norm (a k))"
    and "summable (\<lambda>k. norm (b k))"
  shows "summable (\<lambda>k. \<Sum>i\<le>k. a i * b (k - i))"
  using Cauchy_product_sums[OF assms] by (simp add: sums_iff)


subsection \<open>Series on \<^typ>\<open>real\<close>s\<close>

lemma summable_norm_comparison_test:
  "\<exists>N. \<forall>n\<ge>N. norm (f n) \<le> g n \<Longrightarrow> summable g \<Longrightarrow> summable (\<lambda>n. norm (f n))"
  by (rule summable_comparison_test) auto

lemma summable_rabs_comparison_test: "\<exists>N. \<forall>n\<ge>N. \<bar>f n\<bar> \<le> g n \<Longrightarrow> summable g \<Longrightarrow> summable (\<lambda>n. \<bar>f n\<bar>)"
  for f :: "nat \<Rightarrow> real"
  by (rule summable_comparison_test) auto

lemma summable_rabs_cancel: "summable (\<lambda>n. \<bar>f n\<bar>) \<Longrightarrow> summable f"
  for f :: "nat \<Rightarrow> real"
  by (rule summable_norm_cancel) simp

lemma summable_rabs: "summable (\<lambda>n. \<bar>f n\<bar>) \<Longrightarrow> \<bar>suminf f\<bar> \<le> (\<Sum>n. \<bar>f n\<bar>)"
  for f :: "nat \<Rightarrow> real"
  by (fold real_norm_def) (rule summable_norm)

lemma summable_zero_power [simp]: "summable (\<lambda>n. 0 ^ n :: 'a::{comm_ring_1,topological_space})"
proof -
  have "(\<lambda>n. 0 ^ n :: 'a) = (\<lambda>n. if n = 0 then 0^0 else 0)"
    by (intro ext) (simp add: zero_power)
  moreover have "summable \<dots>" by simp
  ultimately show ?thesis by simp
qed

lemma summable_zero_power' [simp]: "summable (\<lambda>n. f n * 0 ^ n :: 'a::{ring_1,topological_space})"
proof -
  have "(\<lambda>n. f n * 0 ^ n :: 'a) = (\<lambda>n. if n = 0 then f 0 * 0^0 else 0)"
    by (intro ext) (simp add: zero_power)
  moreover have "summable \<dots>" by simp
  ultimately show ?thesis by simp
qed

lemma summable_power_series:
  fixes z :: real
  assumes le_1: "\<And>i. f i \<le> 1"
    and nonneg: "\<And>i. 0 \<le> f i"
    and z: "0 \<le> z" "z < 1"
  shows "summable (\<lambda>i. f i * z^i)"
proof (rule summable_comparison_test[OF _ summable_geometric])
  show "norm z < 1"
    using z by (auto simp: less_imp_le)
  show "\<And>n. \<exists>N. \<forall>na\<ge>N. norm (f na * z ^ na) \<le> z ^ na"
    using z
    by (auto intro!: exI[of _ 0] mult_left_le_one_le simp: abs_mult nonneg power_abs less_imp_le le_1)
qed

lemma summable_0_powser: "summable (\<lambda>n. f n * 0 ^ n :: 'a::real_normed_div_algebra)"
proof -
  have A: "(\<lambda>n. f n * 0 ^ n) = (\<lambda>n. if n = 0 then f n else 0)"
    by (intro ext) auto
  then show ?thesis
    by (subst A) simp_all
qed

lemma summable_powser_split_head:
  "summable (\<lambda>n. f (Suc n) * z ^ n :: 'a::real_normed_div_algebra) = summable (\<lambda>n. f n * z ^ n)"
proof -
  have "summable (\<lambda>n. f (Suc n) * z ^ n) \<longleftrightarrow> summable (\<lambda>n. f (Suc n) * z ^ Suc n)"
    (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    show ?rhs if ?lhs
      using summable_mult2[OF that, of z]
      by (simp add: power_commutes algebra_simps)
    show ?lhs if ?rhs
      using summable_mult2[OF that, of "inverse z"]
      by (cases "z \<noteq> 0", subst (asm) power_Suc2) (simp_all add: algebra_simps)
  qed
  also have "\<dots> \<longleftrightarrow> summable (\<lambda>n. f n * z ^ n)" by (rule summable_Suc_iff)
  finally show ?thesis .
qed

lemma summable_powser_ignore_initial_segment:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_div_algebra"
  shows "summable (\<lambda>n. f (n + m) * z ^ n) \<longleftrightarrow> summable (\<lambda>n. f n * z ^ n)"
proof (induction m)
  case (Suc m)
  have "summable (\<lambda>n. f (n + Suc m) * z ^ n) = summable (\<lambda>n. f (Suc n + m) * z ^ n)"
    by simp
  also have "\<dots> = summable (\<lambda>n. f (n + m) * z ^ n)"
    by (rule summable_powser_split_head)
  also have "\<dots> = summable (\<lambda>n. f n * z ^ n)"
    by (rule Suc.IH)
  finally show ?case .
qed simp_all

lemma powser_split_head:
  fixes f :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,banach}"
  assumes "summable (\<lambda>n. f n * z ^ n)"
  shows "suminf (\<lambda>n. f n * z ^ n) = f 0 + suminf (\<lambda>n. f (Suc n) * z ^ n) * z"
    and "suminf (\<lambda>n. f (Suc n) * z ^ n) * z = suminf (\<lambda>n. f n * z ^ n) - f 0"
    and "summable (\<lambda>n. f (Suc n) * z ^ n)"
proof -
  from assms show "summable (\<lambda>n. f (Suc n) * z ^ n)"
    by (subst summable_powser_split_head)
  from suminf_mult2[OF this, of z]
    have "(\<Sum>n. f (Suc n) * z ^ n) * z = (\<Sum>n. f (Suc n) * z ^ Suc n)"
    by (simp add: power_commutes algebra_simps)
  also from assms have "\<dots> = suminf (\<lambda>n. f n * z ^ n) - f 0"
    by (subst suminf_split_head) simp_all
  finally show "suminf (\<lambda>n. f n * z ^ n) = f 0 + suminf (\<lambda>n. f (Suc n) * z ^ n) * z"
    by simp
  then show "suminf (\<lambda>n. f (Suc n) * z ^ n) * z = suminf (\<lambda>n. f n * z ^ n) - f 0"
    by simp
qed

lemma summable_partial_sum_bound:
  fixes f :: "nat \<Rightarrow> 'a :: banach"
    and e :: real
  assumes summable: "summable f"
    and e: "e > 0"
  obtains N where "\<And>m n. m \<ge> N \<Longrightarrow> norm (\<Sum>k=m..n. f k) < e"
proof -
  from summable have "Cauchy (\<lambda>n. \<Sum>k<n. f k)"
    by (simp add: Cauchy_convergent_iff summable_iff_convergent)
  from CauchyD [OF this e] obtain N
    where N: "\<And>m n. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> norm ((\<Sum>k<m. f k) - (\<Sum>k<n. f k)) < e"
    by blast
  have "norm (\<Sum>k=m..n. f k) < e" if m: "m \<ge> N" for m n
  proof (cases "n \<ge> m")
    case True
    with m have "norm ((\<Sum>k<Suc n. f k) - (\<Sum>k<m. f k)) < e"
      by (intro N) simp_all
    also from True have "(\<Sum>k<Suc n. f k) - (\<Sum>k<m. f k) = (\<Sum>k=m..n. f k)"
      by (subst sum_diff [symmetric]) (simp_all add: sum.last_plus)
    finally show ?thesis .
  next
    case False
    with e show ?thesis by simp_all
  qed
  then show ?thesis by (rule that)
qed

lemma powser_sums_if:
  "(\<lambda>n. (if n = m then (1 :: 'a::{ring_1,topological_space}) else 0) * z^n) sums z^m"
proof -
  have "(\<lambda>n. (if n = m then 1 else 0) * z^n) = (\<lambda>n. if n = m then z^n else 0)"
    by (intro ext) auto
  then show ?thesis
    by (simp add: sums_single)
qed

lemma
  fixes f :: "nat \<Rightarrow> real"
  assumes "summable f"
    and "inj g"
    and pos: "\<And>x. 0 \<le> f x"
  shows summable_reindex: "summable (f \<circ> g)"
    and suminf_reindex_mono: "suminf (f \<circ> g) \<le> suminf f"
    and suminf_reindex: "(\<And>x. x \<notin> range g \<Longrightarrow> f x = 0) \<Longrightarrow> suminf (f \<circ> g) = suminf f"
proof -
  from \<open>inj g\<close> have [simp]: "\<And>A. inj_on g A"
    by (rule subset_inj_on) simp

  have smaller: "\<forall>n. (\<Sum>i<n. (f \<circ> g) i) \<le> suminf f"
  proof
    fix n
    have "\<forall> n' \<in> (g ` {..<n}). n' < Suc (Max (g ` {..<n}))"
      by (metis Max_ge finite_imageI finite_lessThan not_le not_less_eq)
    then obtain m where n: "\<And>n'. n' < n \<Longrightarrow> g n' < m"
      by blast

    have "(\<Sum>i<n. f (g i)) = sum f (g ` {..<n})"
      by (simp add: sum.reindex)
    also have "\<dots> \<le> (\<Sum>i<m. f i)"
      by (rule sum_mono2) (auto simp add: pos n[rule_format])
    also have "\<dots> \<le> suminf f"
      using \<open>summable f\<close>
      by (rule sum_le_suminf) (simp_all add: pos)
    finally show "(\<Sum>i<n. (f \<circ>  g) i) \<le> suminf f"
      by simp
  qed

  have "incseq (\<lambda>n. \<Sum>i<n. (f \<circ> g) i)"
    by (rule incseq_SucI) (auto simp add: pos)
  then obtain  L where L: "(\<lambda> n. \<Sum>i<n. (f \<circ> g) i) \<longlonglongrightarrow> L"
    using smaller by(rule incseq_convergent)
  then have "(f \<circ> g) sums L"
    by (simp add: sums_def)
  then show "summable (f \<circ> g)"
    by (auto simp add: sums_iff)

  then have "(\<lambda>n. \<Sum>i<n. (f \<circ> g) i) \<longlonglongrightarrow> suminf (f \<circ> g)"
    by (rule summable_LIMSEQ)
  then show le: "suminf (f \<circ> g) \<le> suminf f"
    by(rule LIMSEQ_le_const2)(blast intro: smaller[rule_format])

  assume f: "\<And>x. x \<notin> range g \<Longrightarrow> f x = 0"

  from \<open>summable f\<close> have "suminf f \<le> suminf (f \<circ> g)"
  proof (rule suminf_le_const)
    fix n
    have "\<forall> n' \<in> (g -` {..<n}). n' < Suc (Max (g -` {..<n}))"
      by(auto intro: Max_ge simp add: finite_vimageI less_Suc_eq_le)
    then obtain m where n: "\<And>n'. g n' < n \<Longrightarrow> n' < m"
      by blast
    have "(\<Sum>i<n. f i) = (\<Sum>i\<in>{..<n} \<inter> range g. f i)"
      using f by(auto intro: sum.mono_neutral_cong_right)
    also have "\<dots> = (\<Sum>i\<in>g -` {..<n}. (f \<circ> g) i)"
      by (rule sum.reindex_cong[where l=g])(auto)
    also have "\<dots> \<le> (\<Sum>i<m. (f \<circ> g) i)"
      by (rule sum_mono2)(auto simp add: pos n)
    also have "\<dots> \<le> suminf (f \<circ> g)"
      using \<open>summable (f \<circ> g)\<close> by (rule sum_le_suminf) (simp_all add: pos)
    finally show "sum f {..<n} \<le> suminf (f \<circ> g)" .
  qed
  with le show "suminf (f \<circ> g) = suminf f"
    by (rule antisym)
qed

lemma sums_mono_reindex:
  assumes subseq: "strict_mono g"
    and zero: "\<And>n. n \<notin> range g \<Longrightarrow> f n = 0"
  shows "(\<lambda>n. f (g n)) sums c \<longleftrightarrow> f sums c"
  unfolding sums_def
proof
  assume lim: "(\<lambda>n. \<Sum>k<n. f k) \<longlonglongrightarrow> c"
  have "(\<lambda>n. \<Sum>k<n. f (g k)) = (\<lambda>n. \<Sum>k<g n. f k)"
  proof
    fix n :: nat
    from subseq have "(\<Sum>k<n. f (g k)) = (\<Sum>k\<in>g`{..<n}. f k)"
      by (subst sum.reindex) (auto intro: strict_mono_imp_inj_on)
    also from subseq have "\<dots> = (\<Sum>k<g n. f k)"
      by (intro sum.mono_neutral_left ballI zero)
        (auto simp: strict_mono_less strict_mono_less_eq)
    finally show "(\<Sum>k<n. f (g k)) = (\<Sum>k<g n. f k)" .
  qed
  also from LIMSEQ_subseq_LIMSEQ[OF lim subseq] have "\<dots> \<longlonglongrightarrow> c"
    by (simp only: o_def)
  finally show "(\<lambda>n. \<Sum>k<n. f (g k)) \<longlonglongrightarrow> c" .
next
  assume lim: "(\<lambda>n. \<Sum>k<n. f (g k)) \<longlonglongrightarrow> c"
  define g_inv where "g_inv n = (LEAST m. g m \<ge> n)" for n
  from filterlim_subseq[OF subseq] have g_inv_ex: "\<exists>m. g m \<ge> n" for n
    by (auto simp: filterlim_at_top eventually_at_top_linorder)
  then have g_inv: "g (g_inv n) \<ge> n" for n
    unfolding g_inv_def by (rule LeastI_ex)
  have g_inv_least: "m \<ge> g_inv n" if "g m \<ge> n" for m n
    using that unfolding g_inv_def by (rule Least_le)
  have g_inv_least': "g m < n" if "m < g_inv n" for m n
    using that g_inv_least[of n m] by linarith
  have "(\<lambda>n. \<Sum>k<n. f k) = (\<lambda>n. \<Sum>k<g_inv n. f (g k))"
  proof
    fix n :: nat
    {
      fix k
      assume k: "k \<in> {..<n} - g`{..<g_inv n}"
      have "k \<notin> range g"
      proof (rule notI, elim imageE)
        fix l
        assume l: "k = g l"
        have "g l < g (g_inv n)"
          by (rule less_le_trans[OF _ g_inv]) (use k l in simp_all)
        with subseq have "l < g_inv n"
          by (simp add: strict_mono_less)
        with k l show False
          by simp
      qed
      then have "f k = 0"
        by (rule zero)
    }
    with g_inv_least' g_inv have "(\<Sum>k<n. f k) = (\<Sum>k\<in>g`{..<g_inv n}. f k)"
      by (intro sum.mono_neutral_right) auto
    also from subseq have "\<dots> = (\<Sum>k<g_inv n. f (g k))"
      using strict_mono_imp_inj_on by (subst sum.reindex) simp_all
    finally show "(\<Sum>k<n. f k) = (\<Sum>k<g_inv n. f (g k))" .
  qed
  also {
    fix K n :: nat
    assume "g K \<le> n"
    also have "n \<le> g (g_inv n)"
      by (rule g_inv)
    finally have "K \<le> g_inv n"
      using subseq by (simp add: strict_mono_less_eq)
  }
  then have "filterlim g_inv at_top sequentially"
    by (auto simp: filterlim_at_top eventually_at_top_linorder)
  with lim have "(\<lambda>n. \<Sum>k<g_inv n. f (g k)) \<longlonglongrightarrow> c"
    by (rule filterlim_compose)
  finally show "(\<lambda>n. \<Sum>k<n. f k) \<longlonglongrightarrow> c" .
qed

lemma summable_mono_reindex:
  assumes subseq: "strict_mono g"
    and zero: "\<And>n. n \<notin> range g \<Longrightarrow> f n = 0"
  shows "summable (\<lambda>n. f (g n)) \<longleftrightarrow> summable f"
  using sums_mono_reindex[of g f, OF assms] by (simp add: summable_def)

lemma suminf_mono_reindex:
  fixes f :: "nat \<Rightarrow> 'a::{t2_space,comm_monoid_add}"
  assumes "strict_mono g" "\<And>n. n \<notin> range g \<Longrightarrow> f n = 0"
  shows   "suminf (\<lambda>n. f (g n)) = suminf f"
proof (cases "summable f")
  case True
  with sums_mono_reindex [of g f, OF assms]
    and summable_mono_reindex [of g f, OF assms]
  show ?thesis
    by (simp add: sums_iff)
next
  case False
  then have "\<not>(\<exists>c. f sums c)"
    unfolding summable_def by blast
  then have "suminf f = The (\<lambda>_. False)"
    by (simp add: suminf_def)
  moreover from False have "\<not> summable (\<lambda>n. f (g n))"
    using summable_mono_reindex[of g f, OF assms] by simp
  then have "\<not>(\<exists>c. (\<lambda>n. f (g n)) sums c)"
    unfolding summable_def by blast
  then have "suminf (\<lambda>n. f (g n)) = The (\<lambda>_. False)"
    by (simp add: suminf_def)
  ultimately show ?thesis by simp
qed

lemma summable_bounded_partials:
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_vector,complete_space}"
  assumes bound: "eventually (\<lambda>x0. \<forall>a\<ge>x0. \<forall>b>a. norm (sum f {a<..b}) \<le> g a) sequentially"
  assumes g: "g \<longlonglongrightarrow> 0"
  shows   "summable f" unfolding summable_iff_convergent'
proof (intro Cauchy_convergent CauchyI', goal_cases)
  case (1 \<epsilon>)
  with g have "eventually (\<lambda>x. \<bar>g x\<bar> < \<epsilon>) sequentially"
    by (auto simp: tendsto_iff)
  from eventually_conj[OF this bound] obtain x0 where x0:
    "\<And>x. x \<ge> x0 \<Longrightarrow> \<bar>g x\<bar> < \<epsilon>" "\<And>a b. x0 \<le> a \<Longrightarrow> a < b \<Longrightarrow> norm (sum f {a<..b}) \<le> g a" 
    unfolding eventually_at_top_linorder by auto
  show ?case
  proof (intro exI[of _ x0] allI impI)
    fix m n assume mn: "x0 \<le> m" "m < n"
    have "dist (sum f {..m}) (sum f {..n}) = norm (sum f {..n} - sum f {..m})"
      by (simp add: dist_norm norm_minus_commute)
    also have "sum f {..n} - sum f {..m} = sum f ({..n} - {..m})"
      using mn by (intro Groups_Big.sum_diff [symmetric]) auto
    also have "{..n} - {..m} = {m<..n}" using mn by auto
    also have "norm (sum f {m<..n}) \<le> g m" using mn by (intro x0) auto
    also have "\<dots> \<le> \<bar>g m\<bar>" by simp
    also have "\<dots> < \<epsilon>" using mn by (intro x0) auto
    finally show "dist (sum f {..m}) (sum f {..n}) < \<epsilon>" .
  qed
qed

end
