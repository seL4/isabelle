(*  Title       : Series.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp
Converted to setsum and polished yet more by TNN
Additional contributions by Jeremy Avigad
*)

section \<open>Infinite Series\<close>

theory Series
imports Limits Inequalities
begin

subsection \<open>Definition of infinite summability\<close>

definition
  sums :: "(nat \<Rightarrow> 'a::{topological_space, comm_monoid_add}) \<Rightarrow> 'a \<Rightarrow> bool"
  (infixr "sums" 80)
where
  "f sums s \<longleftrightarrow> (\<lambda>n. \<Sum>i<n. f i) \<longlonglongrightarrow> s"

definition summable :: "(nat \<Rightarrow> 'a::{topological_space, comm_monoid_add}) \<Rightarrow> bool" where
   "summable f \<longleftrightarrow> (\<exists>s. f sums s)"

definition
  suminf :: "(nat \<Rightarrow> 'a::{topological_space, comm_monoid_add}) \<Rightarrow> 'a"
  (binder "\<Sum>" 10)
where
  "suminf f = (THE s. f sums s)"

lemma sums_def': "f sums s \<longleftrightarrow> (\<lambda>n. \<Sum>i = 0..n. f i) \<longlonglongrightarrow> s"
  apply (simp add: sums_def)
  apply (subst LIMSEQ_Suc_iff [symmetric])
  apply (simp only: lessThan_Suc_atMost atLeast0AtMost)
  done

subsection \<open>Infinite summability on topological monoids\<close>

lemma sums_subst[trans]: "f = g \<Longrightarrow> g sums z \<Longrightarrow> f sums z"
  by simp

lemma sums_cong: "(\<And>n. f n = g n) \<Longrightarrow> f sums c \<longleftrightarrow> g sums c"
  by (drule ext) simp

lemma sums_summable: "f sums l \<Longrightarrow> summable f"
  by (simp add: sums_def summable_def, blast)

lemma summable_iff_convergent: "summable f \<longleftrightarrow> convergent (\<lambda>n. \<Sum>i<n. f i)"
  by (simp add: summable_def sums_def convergent_def)

lemma summable_iff_convergent':
  "summable f \<longleftrightarrow> convergent (\<lambda>n. setsum f {..n})"
  by (simp_all only: summable_iff_convergent convergent_def
        lessThan_Suc_atMost [symmetric] LIMSEQ_Suc_iff[of "\<lambda>n. setsum f {..<n}"])

lemma suminf_eq_lim: "suminf f = lim (\<lambda>n. \<Sum>i<n. f i)"
  by (simp add: suminf_def sums_def lim_def)

lemma sums_zero[simp, intro]: "(\<lambda>n. 0) sums 0"
  unfolding sums_def by simp

lemma summable_zero[simp, intro]: "summable (\<lambda>n. 0)"
  by (rule sums_zero [THEN sums_summable])

lemma sums_group: "f sums s \<Longrightarrow> 0 < k \<Longrightarrow> (\<lambda>n. setsum f {n * k ..< n * k + k}) sums s"
  apply (simp only: sums_def setsum_nat_group tendsto_def eventually_sequentially)
  apply safe
  apply (erule_tac x=S in allE)
  apply safe
  apply (rule_tac x="N" in exI, safe)
  apply (drule_tac x="n*k" in spec)
  apply (erule mp)
  apply (erule order_trans)
  apply simp
  done

lemma suminf_cong: "(\<And>n. f n = g n) \<Longrightarrow> suminf f = suminf g"
  by (rule arg_cong[of f g], rule ext) simp

lemma summable_cong:
  assumes "eventually (\<lambda>x. f x = (g x :: 'a :: real_normed_vector)) sequentially"
  shows   "summable f = summable g"
proof -
  from assms obtain N where N: "\<forall>n\<ge>N. f n = g n" by (auto simp: eventually_at_top_linorder)
  define C where "C = (\<Sum>k<N. f k - g k)"
  from eventually_ge_at_top[of N]
    have "eventually (\<lambda>n. setsum f {..<n} = C + setsum g {..<n}) sequentially"
  proof eventually_elim
    fix n assume n: "n \<ge> N"
    from n have "{..<n} = {..<N} \<union> {N..<n}" by auto
    also have "setsum f ... = setsum f {..<N} + setsum f {N..<n}"
      by (intro setsum.union_disjoint) auto
    also from N have "setsum f {N..<n} = setsum g {N..<n}" by (intro setsum.cong) simp_all
    also have "setsum f {..<N} + setsum g {N..<n} = C + (setsum g {..<N} + setsum g {N..<n})"
      unfolding C_def by (simp add: algebra_simps setsum_subtractf)
    also have "setsum g {..<N} + setsum g {N..<n} = setsum g ({..<N} \<union> {N..<n})"
      by (intro setsum.union_disjoint [symmetric]) auto
    also from n have "{..<N} \<union> {N..<n} = {..<n}" by auto
    finally show "setsum f {..<n} = C + setsum g {..<n}" .
  qed
  from convergent_cong[OF this] show ?thesis
    by (simp add: summable_iff_convergent convergent_add_const_iff)
qed

lemma sums_finite:
  assumes [simp]: "finite N" and f: "\<And>n. n \<notin> N \<Longrightarrow> f n = 0"
  shows "f sums (\<Sum>n\<in>N. f n)"
proof -
  { fix n
    have "setsum f {..<n + Suc (Max N)} = setsum f N"
    proof cases
      assume "N = {}"
      with f have "f = (\<lambda>x. 0)" by auto
      then show ?thesis by simp
    next
      assume [simp]: "N \<noteq> {}"
      show ?thesis
      proof (safe intro!: setsum.mono_neutral_right f)
        fix i assume "i \<in> N"
        then have "i \<le> Max N" by simp
        then show "i < n + Suc (Max N)" by simp
      qed
    qed }
  note eq = this
  show ?thesis unfolding sums_def
    by (rule LIMSEQ_offset[of _ "Suc (Max N)"])
       (simp add: eq atLeast0LessThan del: add_Suc_right)
qed

corollary sums_0:
   "(\<And>n. f n = 0) \<Longrightarrow> (f sums 0)"
    by (metis (no_types) finite.emptyI setsum.empty sums_finite)

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
  fixes f :: "nat \<Rightarrow> 'a::{t2_space, comm_monoid_add}"
begin

lemma summable_sums[intro]: "summable f \<Longrightarrow> f sums (suminf f)"
  by (simp add: summable_def sums_def suminf_def)
     (metis convergent_LIMSEQ_iff convergent_def lim_def)

lemma summable_LIMSEQ: "summable f \<Longrightarrow> (\<lambda>n. \<Sum>i<n. f i) \<longlonglongrightarrow> suminf f"
  by (rule summable_sums [unfolded sums_def])

lemma sums_unique: "f sums s \<Longrightarrow> s = suminf f"
  by (metis limI suminf_eq_lim sums_def)

lemma sums_iff: "f sums x \<longleftrightarrow> summable f \<and> (suminf f = x)"
  by (metis summable_sums sums_summable sums_unique)

lemma summable_sums_iff:
  "summable (f :: nat \<Rightarrow> 'a :: {comm_monoid_add,t2_space}) \<longleftrightarrow> f sums suminf f"
  by (auto simp: sums_iff summable_sums)

lemma sums_unique2:
  fixes a b :: "'a::{comm_monoid_add,t2_space}"
  shows "f sums a \<Longrightarrow> f sums b \<Longrightarrow> a = b"
by (simp add: sums_iff)

lemma suminf_finite:
  assumes N: "finite N" and f: "\<And>n. n \<notin> N \<Longrightarrow> f n = 0"
  shows "suminf f = (\<Sum>n\<in>N. f n)"
  using sums_finite[OF assms, THEN sums_unique] by simp

end

lemma suminf_zero[simp]: "suminf (\<lambda>n. 0::'a::{t2_space, comm_monoid_add}) = 0"
  by (rule sums_zero [THEN sums_unique, symmetric])


subsection \<open>Infinite summability on ordered, topological monoids\<close>

lemma sums_le:
  fixes f g :: "nat \<Rightarrow> 'a::{ordered_comm_monoid_add, linorder_topology}"
  shows "\<forall>n. f n \<le> g n \<Longrightarrow> f sums s \<Longrightarrow> g sums t \<Longrightarrow> s \<le> t"
  by (rule LIMSEQ_le) (auto intro: setsum_mono simp: sums_def)

context
  fixes f :: "nat \<Rightarrow> 'a::{ordered_comm_monoid_add, linorder_topology}"
begin

lemma suminf_le: "\<lbrakk>\<forall>n. f n \<le> g n; summable f; summable g\<rbrakk> \<Longrightarrow> suminf f \<le> suminf g"
  by (auto dest: sums_summable intro: sums_le)

lemma setsum_le_suminf: "summable f \<Longrightarrow> \<forall>m\<ge>n. 0 \<le> f m \<Longrightarrow> setsum f {..<n} \<le> suminf f"
  by (rule sums_le[OF _ sums_If_finite_set summable_sums]) auto

lemma suminf_nonneg: "summable f \<Longrightarrow> \<forall>n. 0 \<le> f n \<Longrightarrow> 0 \<le> suminf f"
  using setsum_le_suminf[of 0] by simp

lemma suminf_le_const: "summable f \<Longrightarrow> (\<And>n. setsum f {..<n} \<le> x) \<Longrightarrow> suminf f \<le> x"
  by (metis LIMSEQ_le_const2 summable_LIMSEQ)

lemma suminf_eq_zero_iff: "summable f \<Longrightarrow> \<forall>n. 0 \<le> f n \<Longrightarrow> suminf f = 0 \<longleftrightarrow> (\<forall>n. f n = 0)"
proof
  assume "summable f" "suminf f = 0" and pos: "\<forall>n. 0 \<le> f n"
  then have f: "(\<lambda>n. \<Sum>i<n. f i) \<longlonglongrightarrow> 0"
    using summable_LIMSEQ[of f] by simp
  then have "\<And>i. (\<Sum>n\<in>{i}. f n) \<le> 0"
  proof (rule LIMSEQ_le_const)
    fix i show "\<exists>N. \<forall>n\<ge>N. (\<Sum>n\<in>{i}. f n) \<le> setsum f {..<n}"
      using pos by (intro exI[of _ "Suc i"] allI impI setsum_mono2) auto
  qed
  with pos show "\<forall>n. f n = 0"
    by (auto intro!: antisym)
qed (metis suminf_zero fun_eq_iff)

lemma suminf_pos_iff:
  "summable f \<Longrightarrow> \<forall>n. 0 \<le> f n \<Longrightarrow> 0 < suminf f \<longleftrightarrow> (\<exists>i. 0 < f i)"
  using setsum_le_suminf[of 0] suminf_eq_zero_iff by (simp add: less_le)

lemma suminf_pos2:
  assumes "summable f" "\<forall>n. 0 \<le> f n" "0 < f i"
  shows "0 < suminf f"
proof -
  have "0 < (\<Sum>n<Suc i. f n)"
    using assms by (intro setsum_pos2[where i=i]) auto
  also have "\<dots> \<le> suminf f"
    using assms by (intro setsum_le_suminf) auto
  finally show ?thesis .
qed

lemma suminf_pos: "summable f \<Longrightarrow> \<forall>n. 0 < f n \<Longrightarrow> 0 < suminf f"
  by (intro suminf_pos2[where i=0]) (auto intro: less_imp_le)

end

context
  fixes f :: "nat \<Rightarrow> 'a::{ordered_cancel_comm_monoid_add, linorder_topology}"
begin

lemma setsum_less_suminf2: "summable f \<Longrightarrow> \<forall>m\<ge>n. 0 \<le> f m \<Longrightarrow> n \<le> i \<Longrightarrow> 0 < f i \<Longrightarrow> setsum f {..<n} < suminf f"
  using
    setsum_le_suminf[of f "Suc i"]
    add_strict_increasing[of "f i" "setsum f {..<n}" "setsum f {..<i}"]
    setsum_mono2[of "{..<i}" "{..<n}" f]
  by (auto simp: less_imp_le ac_simps)

lemma setsum_less_suminf: "summable f \<Longrightarrow> \<forall>m\<ge>n. 0 < f m \<Longrightarrow> setsum f {..<n} < suminf f"
  using setsum_less_suminf2[of n n] by (simp add: less_imp_le)

end

lemma summableI_nonneg_bounded:
  fixes f:: "nat \<Rightarrow> 'a::{ordered_comm_monoid_add, linorder_topology, conditionally_complete_linorder}"
  assumes pos[simp]: "\<And>n. 0 \<le> f n" and le: "\<And>n. (\<Sum>i<n. f i) \<le> x"
  shows "summable f"
  unfolding summable_def sums_def[abs_def]
proof (rule exI LIMSEQ_incseq_SUP)+
  show "bdd_above (range (\<lambda>n. setsum f {..<n}))"
    using le by (auto simp: bdd_above_def)
  show "incseq (\<lambda>n. setsum f {..<n})"
    by (auto simp: mono_def intro!: setsum_mono2)
qed

lemma summableI[intro, simp]:
  fixes f:: "nat \<Rightarrow> 'a::{canonically_ordered_monoid_add, linorder_topology, complete_linorder}"
  shows "summable f"
  by (intro summableI_nonneg_bounded[where x=top] zero_le top_greatest)

subsection \<open>Infinite summability on topological monoids\<close>

lemma Zero_notin_Suc: "0 \<notin> Suc ` A"
  by auto

context
  fixes f g :: "nat \<Rightarrow> 'a :: {t2_space, topological_comm_monoid_add}"
begin

lemma sums_Suc:
  assumes "(\<lambda>n. f (Suc n)) sums l" shows "f sums (l + f 0)"
proof  -
  have "(\<lambda>n. (\<Sum>i<n. f (Suc i)) + f 0) \<longlonglongrightarrow> l + f 0"
    using assms by (auto intro!: tendsto_add simp: sums_def)
  moreover have "(\<Sum>i<n. f (Suc i)) + f 0 = (\<Sum>i<Suc n. f i)" for n
    unfolding lessThan_Suc_eq_insert_0 by (simp add: Zero_notin_Suc ac_simps setsum.reindex)
  ultimately show ?thesis
    by (auto simp add: sums_def simp del: setsum_lessThan_Suc intro: LIMSEQ_Suc_iff[THEN iffD1])
qed

lemma sums_add: "f sums a \<Longrightarrow> g sums b \<Longrightarrow> (\<lambda>n. f n + g n) sums (a + b)"
  unfolding sums_def by (simp add: setsum.distrib tendsto_add)

lemma summable_add: "summable f \<Longrightarrow> summable g \<Longrightarrow> summable (\<lambda>n. f n + g n)"
  unfolding summable_def by (auto intro: sums_add)

lemma suminf_add: "summable f \<Longrightarrow> summable g \<Longrightarrow> suminf f + suminf g = (\<Sum>n. f n + g n)"
  by (intro sums_unique sums_add summable_sums)

end

context
  fixes f :: "'i \<Rightarrow> nat \<Rightarrow> 'a::{t2_space, topological_comm_monoid_add}" and I :: "'i set"
begin

lemma sums_setsum: "(\<And>i. i \<in> I \<Longrightarrow> (f i) sums (x i)) \<Longrightarrow> (\<lambda>n. \<Sum>i\<in>I. f i n) sums (\<Sum>i\<in>I. x i)"
  by (induct I rule: infinite_finite_induct) (auto intro!: sums_add)

lemma suminf_setsum: "(\<And>i. i \<in> I \<Longrightarrow> summable (f i)) \<Longrightarrow> (\<Sum>n. \<Sum>i\<in>I. f i n) = (\<Sum>i\<in>I. \<Sum>n. f i n)"
  using sums_unique[OF sums_setsum, OF summable_sums] by simp

lemma summable_setsum: "(\<And>i. i \<in> I \<Longrightarrow> summable (f i)) \<Longrightarrow> summable (\<lambda>n. \<Sum>i\<in>I. f i n)"
  using sums_summable[OF sums_setsum[OF summable_sums]] .

end

subsection \<open>Infinite summability on real normed vector spaces\<close>

context
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
begin

lemma sums_Suc_iff: "(\<lambda>n. f (Suc n)) sums s \<longleftrightarrow> f sums (s + f 0)"
proof -
  have "f sums (s + f 0) \<longleftrightarrow> (\<lambda>i. \<Sum>j<Suc i. f j) \<longlonglongrightarrow> s + f 0"
    by (subst LIMSEQ_Suc_iff) (simp add: sums_def)
  also have "\<dots> \<longleftrightarrow> (\<lambda>i. (\<Sum>j<i. f (Suc j)) + f 0) \<longlonglongrightarrow> s + f 0"
    by (simp add: ac_simps setsum.reindex image_iff lessThan_Suc_eq_insert_0)
  also have "\<dots> \<longleftrightarrow> (\<lambda>n. f (Suc n)) sums s"
  proof
    assume "(\<lambda>i. (\<Sum>j<i. f (Suc j)) + f 0) \<longlonglongrightarrow> s + f 0"
    with tendsto_add[OF this tendsto_const, of "- f 0"]
    show "(\<lambda>i. f (Suc i)) sums s"
      by (simp add: sums_def)
  qed (auto intro: tendsto_add simp: sums_def)
  finally show ?thesis ..
qed

lemma summable_Suc_iff: "summable (\<lambda>n. f (Suc n)) = summable f"
proof
  assume "summable f"
  hence "f sums suminf f" by (rule summable_sums)
  hence "(\<lambda>n. f (Suc n)) sums (suminf f - f 0)" by (simp add: sums_Suc_iff)
  thus "summable (\<lambda>n. f (Suc n))" unfolding summable_def by blast
qed (auto simp: sums_Suc_iff summable_def)

lemma sums_Suc_imp: "f 0 = 0 \<Longrightarrow> (\<lambda>n. f (Suc n)) sums s \<Longrightarrow> (\<lambda>n. f n) sums s"
  using sums_Suc_iff by simp

end

context \<comment>\<open>Separate contexts are necessary to allow general use of the results above, here.\<close>
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
begin

lemma sums_diff: "f sums a \<Longrightarrow> g sums b \<Longrightarrow> (\<lambda>n. f n - g n) sums (a - b)"
  unfolding sums_def by (simp add: setsum_subtractf tendsto_diff)

lemma summable_diff: "summable f \<Longrightarrow> summable g \<Longrightarrow> summable (\<lambda>n. f n - g n)"
  unfolding summable_def by (auto intro: sums_diff)

lemma suminf_diff: "summable f \<Longrightarrow> summable g \<Longrightarrow> suminf f - suminf g = (\<Sum>n. f n - g n)"
  by (intro sums_unique sums_diff summable_sums)

lemma sums_minus: "f sums a \<Longrightarrow> (\<lambda>n. - f n) sums (- a)"
  unfolding sums_def by (simp add: setsum_negf tendsto_minus)

lemma summable_minus: "summable f \<Longrightarrow> summable (\<lambda>n. - f n)"
  unfolding summable_def by (auto intro: sums_minus)

lemma suminf_minus: "summable f \<Longrightarrow> (\<Sum>n. - f n) = - (\<Sum>n. f n)"
  by (intro sums_unique [symmetric] sums_minus summable_sums)

lemma sums_iff_shift: "(\<lambda>i. f (i + n)) sums s \<longleftrightarrow> f sums (s + (\<Sum>i<n. f i))"
proof (induct n arbitrary: s)
  case (Suc n)
  moreover have "(\<lambda>i. f (Suc i + n)) sums s \<longleftrightarrow> (\<lambda>i. f (i + n)) sums (s + f n)"
    by (subst sums_Suc_iff) simp
  ultimately show ?case
    by (simp add: ac_simps)
qed simp

corollary sums_iff_shift': "(\<lambda>i. f (i + n)) sums (s - (\<Sum>i<n. f i)) \<longleftrightarrow> f sums s"
  by (simp add: sums_iff_shift)

lemma sums_zero_iff_shift:
  assumes "\<And>i. i < n \<Longrightarrow> f i = 0"
  shows "(\<lambda>i. f (i+n)) sums s \<longleftrightarrow> (\<lambda>i. f i) sums s"
by (simp add: assms sums_iff_shift)

lemma summable_iff_shift: "summable (\<lambda>n. f (n + k)) \<longleftrightarrow> summable f"
  by (metis diff_add_cancel summable_def sums_iff_shift[abs_def])

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
  fixes r :: real assumes "0 < r" and "summable f"
  shows "\<exists>N. \<forall>n\<ge>N. norm (\<Sum>i. f (i + n)) < r"
proof -
  from LIMSEQ_D[OF summable_LIMSEQ[OF \<open>summable f\<close>] \<open>0 < r\<close>]
  obtain N :: nat where "\<forall> n \<ge> N. norm (setsum f {..<n} - suminf f) < r" by auto
  thus ?thesis
    by (auto simp: norm_minus_commute suminf_minus_initial_segment[OF \<open>summable f\<close>])
qed

lemma summable_LIMSEQ_zero: "summable f \<Longrightarrow> f \<longlonglongrightarrow> 0"
  apply (drule summable_iff_convergent [THEN iffD1])
  apply (drule convergent_Cauchy)
  apply (simp only: Cauchy_iff LIMSEQ_iff, safe)
  apply (drule_tac x="r" in spec, safe)
  apply (rule_tac x="M" in exI, safe)
  apply (drule_tac x="Suc n" in spec, simp)
  apply (drule_tac x="n" in spec, simp)
  done

lemma summable_imp_convergent: "summable f \<Longrightarrow> convergent f"
  by (force dest!: summable_LIMSEQ_zero simp: convergent_def)

lemma summable_imp_Bseq: "summable f \<Longrightarrow> Bseq f"
  by (simp add: convergent_imp_Bseq summable_imp_convergent)

end

lemma summable_minus_iff:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "summable (\<lambda>n. - f n) \<longleftrightarrow> summable f"
  by (auto dest: summable_minus) \<comment>\<open>used two ways, hence must be outside the context above\<close>

lemma (in bounded_linear) sums: "(\<lambda>n. X n) sums a \<Longrightarrow> (\<lambda>n. f (X n)) sums (f a)"
  unfolding sums_def by (drule tendsto, simp only: setsum)

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

lemma summable_const_iff: "summable (\<lambda>_. c) \<longleftrightarrow> (c :: 'a :: real_normed_vector) = 0"
proof -
  {
    assume "c \<noteq> 0"
    hence "filterlim (\<lambda>n. of_nat n * norm c) at_top sequentially"
      by (subst mult.commute)
         (auto intro!: filterlim_tendsto_pos_mult_at_top filterlim_real_sequentially)
    hence "\<not>convergent (\<lambda>n. norm (\<Sum>k<n. c))"
      by (intro filterlim_at_infinity_imp_not_convergent filterlim_at_top_imp_at_infinity)
         (simp_all add: setsum_constant_scaleR)
    hence "\<not>summable (\<lambda>_. c)" unfolding summable_iff_convergent using convergent_norm by blast
  }
  thus ?thesis by auto
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
  assumes "c \<noteq> 0"
  shows   "(\<lambda>n. c * f n :: 'a :: {real_normed_algebra,field}) sums (c * d) \<longleftrightarrow> f sums d"
  using sums_mult[of f d c] sums_mult[of "\<lambda>n. c * f n" "c * d" "inverse c"]
  by (force simp: field_simps assms)

lemma sums_mult2_iff:
  assumes "c \<noteq> (0 :: 'a :: {real_normed_algebra, field})"
  shows   "(\<lambda>n. f n * c) sums (d * c) \<longleftrightarrow> f sums d"
  using sums_mult_iff[OF assms, of f d] by (simp add: mult.commute)

lemma sums_of_real_iff:
  "(\<lambda>n. of_real (f n) :: 'a :: real_normed_div_algebra) sums of_real c \<longleftrightarrow> f sums c"
  by (simp add: sums_def of_real_setsum[symmetric] tendsto_of_real_iff del: of_real_setsum)


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

lemma sums_mult_D: "\<lbrakk>(\<lambda>n. c * f n) sums a; c \<noteq> 0\<rbrakk> \<Longrightarrow> f sums (a/c)"
  using sums_mult_iff by fastforce

lemma summable_mult_D: "\<lbrakk>summable (\<lambda>n. c * f n); c \<noteq> 0\<rbrakk> \<Longrightarrow> summable f"
  by (auto dest: summable_divide)

text\<open>Sum of a geometric progression.\<close>

lemma geometric_sums: "norm c < 1 \<Longrightarrow> (\<lambda>n. c^n) sums (1 / (1 - c))"
proof -
  assume less_1: "norm c < 1"
  hence neq_1: "c \<noteq> 1" by auto
  hence neq_0: "c - 1 \<noteq> 0" by simp
  from less_1 have lim_0: "(\<lambda>n. c^n) \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_power_zero)
  hence "(\<lambda>n. c ^ n / (c - 1) - 1 / (c - 1)) \<longlonglongrightarrow> 0 / (c - 1) - 1 / (c - 1)"
    using neq_0 by (intro tendsto_intros)
  hence "(\<lambda>n. (c ^ n - 1) / (c - 1)) \<longlonglongrightarrow> 1 / (1 - c)"
    by (simp add: nonzero_minus_divide_right [OF neq_0] diff_divide_distrib)
  thus "(\<lambda>n. c ^ n) sums (1 / (1 - c))"
    by (simp add: sums_def geometric_sum neq_1)
qed

lemma summable_geometric: "norm c < 1 \<Longrightarrow> summable (\<lambda>n. c^n)"
  by (rule geometric_sums [THEN sums_summable])

lemma suminf_geometric: "norm c < 1 \<Longrightarrow> suminf (\<lambda>n. c^n) = 1 / (1 - c)"
  by (rule sums_unique[symmetric]) (rule geometric_sums)

lemma summable_geometric_iff: "summable (\<lambda>n. c ^ n) \<longleftrightarrow> norm c < 1"
proof
  assume "summable (\<lambda>n. c ^ n :: 'a :: real_normed_field)"
  hence "(\<lambda>n. norm c ^ n) \<longlonglongrightarrow> 0"
    by (simp add: norm_power [symmetric] tendsto_norm_zero_iff summable_LIMSEQ_zero)
  from order_tendstoD(2)[OF this zero_less_one] obtain n where "norm c ^ n < 1"
    by (auto simp: eventually_at_top_linorder)
  thus "norm c < 1" using one_le_power[of "norm c" n] by (cases "norm c \<ge> 1") (linarith, simp)
qed (rule summable_geometric)

end

lemma power_half_series: "(\<lambda>n. (1/2::real)^Suc n) sums 1"
proof -
  have 2: "(\<lambda>n. (1/2::real)^n) sums 2" using geometric_sums [of "1/2::real"]
    by auto
  have "(\<lambda>n. (1/2::real)^Suc n) = (\<lambda>n. (1 / 2) ^ n / 2)"
    by (simp add: mult.commute)
  thus ?thesis using sums_divide [OF 2, of 2]
    by simp
qed


subsection \<open>Telescoping\<close>

lemma telescope_sums:
  assumes "f \<longlonglongrightarrow> (c :: 'a :: real_normed_vector)"
  shows   "(\<lambda>n. f (Suc n) - f n) sums (c - f 0)"
  unfolding sums_def
proof (subst LIMSEQ_Suc_iff [symmetric])
  have "(\<lambda>n. \<Sum>k<Suc n. f (Suc k) - f k) = (\<lambda>n. f (Suc n) - f 0)"
    by (simp add: lessThan_Suc_atMost atLeast0AtMost [symmetric] setsum_Suc_diff)
  also have "\<dots> \<longlonglongrightarrow> c - f 0" by (intro tendsto_diff LIMSEQ_Suc[OF assms] tendsto_const)
  finally show "(\<lambda>n. \<Sum>n<Suc n. f (Suc n) - f n) \<longlonglongrightarrow> c - f 0" .
qed

lemma telescope_sums':
  assumes "f \<longlonglongrightarrow> (c :: 'a :: real_normed_vector)"
  shows   "(\<lambda>n. f n - f (Suc n)) sums (f 0 - c)"
  using sums_minus[OF telescope_sums[OF assms]] by (simp add: algebra_simps)

lemma telescope_summable:
  assumes "f \<longlonglongrightarrow> (c :: 'a :: real_normed_vector)"
  shows   "summable (\<lambda>n. f (Suc n) - f n)"
  using telescope_sums[OF assms] by (simp add: sums_iff)

lemma telescope_summable':
  assumes "f \<longlonglongrightarrow> (c :: 'a :: real_normed_vector)"
  shows   "summable (\<lambda>n. f n - f (Suc n))"
  using summable_minus[OF telescope_summable[OF assms]] by (simp add: algebra_simps)


subsection \<open>Infinite summability on Banach spaces\<close>

text\<open>Cauchy-type criterion for convergence of series (c.f. Harrison)\<close>

lemma summable_Cauchy:
  fixes f :: "nat \<Rightarrow> 'a::banach"
  shows "summable f \<longleftrightarrow> (\<forall>e>0. \<exists>N. \<forall>m\<ge>N. \<forall>n. norm (setsum f {m..<n}) < e)"
  apply (simp only: summable_iff_convergent Cauchy_convergent_iff [symmetric] Cauchy_iff, safe)
  apply (drule spec, drule (1) mp)
  apply (erule exE, rule_tac x="M" in exI, clarify)
  apply (rule_tac x="m" and y="n" in linorder_le_cases)
  apply (frule (1) order_trans)
  apply (drule_tac x="n" in spec, drule (1) mp)
  apply (drule_tac x="m" in spec, drule (1) mp)
  apply (simp_all add: setsum_diff [symmetric])
  apply (drule spec, drule (1) mp)
  apply (erule exE, rule_tac x="N" in exI, clarify)
  apply (rule_tac x="m" and y="n" in linorder_le_cases)
  apply (subst norm_minus_commute)
  apply (simp_all add: setsum_diff [symmetric])
  done

context
  fixes f :: "nat \<Rightarrow> 'a::banach"
begin

text\<open>Absolute convergence imples normal convergence\<close>

lemma summable_norm_cancel: "summable (\<lambda>n. norm (f n)) \<Longrightarrow> summable f"
  apply (simp only: summable_Cauchy, safe)
  apply (drule_tac x="e" in spec, safe)
  apply (rule_tac x="N" in exI, safe)
  apply (drule_tac x="m" in spec, safe)
  apply (rule order_le_less_trans [OF norm_setsum])
  apply (rule order_le_less_trans [OF abs_ge_self])
  apply simp
  done

lemma summable_norm: "summable (\<lambda>n. norm (f n)) \<Longrightarrow> norm (suminf f) \<le> (\<Sum>n. norm (f n))"
  by (auto intro: LIMSEQ_le tendsto_norm summable_norm_cancel summable_LIMSEQ norm_setsum)

text \<open>Comparison tests\<close>

lemma summable_comparison_test: "\<exists>N. \<forall>n\<ge>N. norm (f n) \<le> g n \<Longrightarrow> summable g \<Longrightarrow> summable f"
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

lemma summable_comparison_test_ev:
  shows "eventually (\<lambda>n. norm (f n) \<le> g n) sequentially \<Longrightarrow> summable g \<Longrightarrow> summable f"
  by (rule summable_comparison_test) (auto simp: eventually_at_top_linorder)

(*A better argument order*)
lemma summable_comparison_test': "summable g \<Longrightarrow> (\<And>n. n \<ge> N \<Longrightarrow> norm(f n) \<le> g n) \<Longrightarrow> summable f"
  by (rule summable_comparison_test) auto

subsection \<open>The Ratio Test\<close>

lemma summable_ratio_test:
  assumes "c < 1" "\<And>n. n \<ge> N \<Longrightarrow> norm (f (Suc n)) \<le> c * norm (f n)"
  shows "summable f"
proof cases
  assume "0 < c"
  show "summable f"
  proof (rule summable_comparison_test)
    show "\<exists>N'. \<forall>n\<ge>N'. norm (f n) \<le> (norm (f N) / (c ^ N)) * c ^ n"
    proof (intro exI allI impI)
      fix n assume "N \<le> n" then show "norm (f n) \<le> (norm (f N) / (c ^ N)) * c ^ n"
      proof (induct rule: inc_induct)
        case (step m)
        moreover have "norm (f (Suc m)) / c ^ Suc m * c ^ n \<le> norm (f m) / c ^ m * c ^ n"
          using \<open>0 < c\<close> \<open>c < 1\<close> assms(2)[OF \<open>N \<le> m\<close>] by (simp add: field_simps)
        ultimately show ?case by simp
      qed (insert \<open>0 < c\<close>, simp)
    qed
    show "summable (\<lambda>n. norm (f N) / c ^ N * c ^ n)"
      using \<open>0 < c\<close> \<open>c < 1\<close> by (intro summable_mult summable_geometric) simp
  qed
next
  assume c: "\<not> 0 < c"
  { fix n assume "n \<ge> N"
    then have "norm (f (Suc n)) \<le> c * norm (f n)"
      by fact
    also have "\<dots> \<le> 0"
      using c by (simp add: not_less mult_nonpos_nonneg)
    finally have "f (Suc n) = 0"
      by auto }
  then show "summable f"
    by (intro sums_summable[OF sums_finite, of "{.. Suc N}"]) (auto simp: not_le Suc_less_eq2)
qed

end

text\<open>Relations among convergence and absolute convergence for power series.\<close>

lemma Abel_lemma:
  fixes a :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes r: "0 \<le> r" and r0: "r < r0" and M: "\<And>n. norm (a n) * r0^n \<le> M"
    shows "summable (\<lambda>n. norm (a n) * r^n)"
proof (rule summable_comparison_test')
  show "summable (\<lambda>n. M * (r / r0) ^ n)"
    using assms
    by (auto simp add: summable_mult summable_geometric)
next
  fix n
  show "norm (norm (a n) * r ^ n) \<le> M * (r / r0) ^ n"
    using r r0 M [of n]
    apply (auto simp add: abs_mult field_simps)
    apply (cases "r=0", simp)
    apply (cases n, auto)
    done
qed


text\<open>Summability of geometric series for real algebras\<close>

lemma complete_algebra_summable_geometric:
  fixes x :: "'a::{real_normed_algebra_1,banach}"
  shows "norm x < 1 \<Longrightarrow> summable (\<lambda>n. x ^ n)"
proof (rule summable_comparison_test)
  show "\<exists>N. \<forall>n\<ge>N. norm (x ^ n) \<le> norm x ^ n"
    by (simp add: norm_power_ineq)
  show "norm x < 1 \<Longrightarrow> summable (\<lambda>n. norm x ^ n)"
    by (simp add: summable_geometric)
qed

subsection \<open>Cauchy Product Formula\<close>

text \<open>
  Proof based on Analysis WebNotes: Chapter 07, Class 41
  @{url "http://www.math.unl.edu/~webnotes/classes/class41/prp77.htm"}
\<close>

lemma Cauchy_product_sums:
  fixes a b :: "nat \<Rightarrow> 'a::{real_normed_algebra,banach}"
  assumes a: "summable (\<lambda>k. norm (a k))"
  assumes b: "summable (\<lambda>k. norm (b k))"
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
  have f_nonneg: "\<And>x. 0 \<le> ?f x" by (auto)
  hence norm_setsum_f: "\<And>A. norm (setsum ?f A) = setsum ?f A"
    unfolding real_norm_def
    by (simp only: abs_of_nonneg setsum_nonneg [rule_format])

  have "(\<lambda>n. (\<Sum>k<n. a k) * (\<Sum>k<n. b k)) \<longlonglongrightarrow> (\<Sum>k. a k) * (\<Sum>k. b k)"
    by (intro tendsto_mult summable_LIMSEQ summable_norm_cancel [OF a] summable_norm_cancel [OF b])
  hence 1: "(\<lambda>n. setsum ?g (?S1 n)) \<longlonglongrightarrow> (\<Sum>k. a k) * (\<Sum>k. b k)"
    by (simp only: setsum_product setsum.Sigma [rule_format] finite_lessThan)

  have "(\<lambda>n. (\<Sum>k<n. norm (a k)) * (\<Sum>k<n. norm (b k))) \<longlonglongrightarrow> (\<Sum>k. norm (a k)) * (\<Sum>k. norm (b k))"
    using a b by (intro tendsto_mult summable_LIMSEQ)
  hence "(\<lambda>n. setsum ?f (?S1 n)) \<longlonglongrightarrow> (\<Sum>k. norm (a k)) * (\<Sum>k. norm (b k))"
    by (simp only: setsum_product setsum.Sigma [rule_format] finite_lessThan)
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
  hence 2: "(\<lambda>n. setsum ?g (?S1 n) - setsum ?g (?S2 n)) \<longlonglongrightarrow> 0"
    unfolding tendsto_Zfun_iff diff_0_right
    by (simp only: setsum_diff finite_S1 S2_le_S1)

  with 1 have "(\<lambda>n. setsum ?g (?S2 n)) \<longlonglongrightarrow> (\<Sum>k. a k) * (\<Sum>k. b k)"
    by (rule Lim_transform2)
  thus ?thesis by (simp only: sums_def setsum_triangle_reindex)
qed

lemma Cauchy_product:
  fixes a b :: "nat \<Rightarrow> 'a::{real_normed_algebra,banach}"
  assumes a: "summable (\<lambda>k. norm (a k))"
  assumes b: "summable (\<lambda>k. norm (b k))"
  shows "(\<Sum>k. a k) * (\<Sum>k. b k) = (\<Sum>k. \<Sum>i\<le>k. a i * b (k - i))"
  using a b
  by (rule Cauchy_product_sums [THEN sums_unique])

lemma summable_Cauchy_product:
  assumes "summable (\<lambda>k. norm (a k :: 'a :: {real_normed_algebra,banach}))"
          "summable (\<lambda>k. norm (b k))"
  shows   "summable (\<lambda>k. \<Sum>i\<le>k. a i * b (k - i))"
  using Cauchy_product_sums[OF assms] by (simp add: sums_iff)

subsection \<open>Series on @{typ real}s\<close>

lemma summable_norm_comparison_test: "\<exists>N. \<forall>n\<ge>N. norm (f n) \<le> g n \<Longrightarrow> summable g \<Longrightarrow> summable (\<lambda>n. norm (f n))"
  by (rule summable_comparison_test) auto

lemma summable_rabs_comparison_test: "\<lbrakk>\<exists>N. \<forall>n\<ge>N. \<bar>f n\<bar> \<le> g n; summable g\<rbrakk> \<Longrightarrow> summable (\<lambda>n. \<bar>f n :: real\<bar>)"
  by (rule summable_comparison_test) auto

lemma summable_rabs_cancel: "summable (\<lambda>n. \<bar>f n :: real\<bar>) \<Longrightarrow> summable f"
  by (rule summable_norm_cancel) simp

lemma summable_rabs: "summable (\<lambda>n. \<bar>f n :: real\<bar>) \<Longrightarrow> \<bar>suminf f\<bar> \<le> (\<Sum>n. \<bar>f n\<bar>)"
  by (fold real_norm_def) (rule summable_norm)

lemma summable_zero_power [simp]: "summable (\<lambda>n. 0 ^ n :: 'a :: {comm_ring_1,topological_space})"
proof -
  have "(\<lambda>n. 0 ^ n :: 'a) = (\<lambda>n. if n = 0 then 0^0 else 0)" by (intro ext) (simp add: zero_power)
  moreover have "summable \<dots>" by simp
  ultimately show ?thesis by simp
qed

lemma summable_zero_power' [simp]: "summable (\<lambda>n. f n * 0 ^ n :: 'a :: {ring_1,topological_space})"
proof -
  have "(\<lambda>n. f n * 0 ^ n :: 'a) = (\<lambda>n. if n = 0 then f 0 * 0^0 else 0)"
    by (intro ext) (simp add: zero_power)
  moreover have "summable \<dots>" by simp
  ultimately show ?thesis by simp
qed

lemma summable_power_series:
  fixes z :: real
  assumes le_1: "\<And>i. f i \<le> 1" and nonneg: "\<And>i. 0 \<le> f i" and z: "0 \<le> z" "z < 1"
  shows "summable (\<lambda>i. f i * z^i)"
proof (rule summable_comparison_test[OF _ summable_geometric])
  show "norm z < 1" using z by (auto simp: less_imp_le)
  show "\<And>n. \<exists>N. \<forall>na\<ge>N. norm (f na * z ^ na) \<le> z ^ na"
    using z by (auto intro!: exI[of _ 0] mult_left_le_one_le simp: abs_mult nonneg power_abs less_imp_le le_1)
qed

lemma summable_0_powser:
  "summable (\<lambda>n. f n * 0 ^ n :: 'a :: real_normed_div_algebra)"
proof -
  have A: "(\<lambda>n. f n * 0 ^ n) = (\<lambda>n. if n = 0 then f n else 0)"
    by (intro ext) auto
  thus ?thesis by (subst A) simp_all
qed

lemma summable_powser_split_head:
  "summable (\<lambda>n. f (Suc n) * z ^ n :: 'a :: real_normed_div_algebra) = summable (\<lambda>n. f n * z ^ n)"
proof -
  have "summable (\<lambda>n. f (Suc n) * z ^ n) \<longleftrightarrow> summable (\<lambda>n. f (Suc n) * z ^ Suc n)"
  proof
    assume "summable (\<lambda>n. f (Suc n) * z ^ n)"
    from summable_mult2[OF this, of z] show "summable (\<lambda>n. f (Suc n) * z ^ Suc n)"
      by (simp add: power_commutes algebra_simps)
  next
    assume "summable (\<lambda>n. f (Suc n) * z ^ Suc n)"
    from summable_mult2[OF this, of "inverse z"] show "summable (\<lambda>n. f (Suc n) * z ^ n)"
      by (cases "z \<noteq> 0", subst (asm) power_Suc2) (simp_all add: algebra_simps)
  qed
  also have "\<dots> \<longleftrightarrow> summable (\<lambda>n. f n * z ^ n)" by (rule summable_Suc_iff)
  finally show ?thesis .
qed

lemma powser_split_head:
  assumes "summable (\<lambda>n. f n * z ^ n :: 'a :: {real_normed_div_algebra,banach})"
  shows   "suminf (\<lambda>n. f n * z ^ n) = f 0 + suminf (\<lambda>n. f (Suc n) * z ^ n) * z"
          "suminf (\<lambda>n. f (Suc n) * z ^ n) * z = suminf (\<lambda>n. f n * z ^ n) - f 0"
          "summable (\<lambda>n. f (Suc n) * z ^ n)"
proof -
  from assms show "summable (\<lambda>n. f (Suc n) * z ^ n)" by (subst summable_powser_split_head)

  from suminf_mult2[OF this, of z]
    have "(\<Sum>n. f (Suc n) * z ^ n) * z = (\<Sum>n. f (Suc n) * z ^ Suc n)"
    by (simp add: power_commutes algebra_simps)
  also from assms have "\<dots> = suminf (\<lambda>n. f n * z ^ n) - f 0"
    by (subst suminf_split_head) simp_all
  finally show "suminf (\<lambda>n. f n * z ^ n) = f 0 + suminf (\<lambda>n. f (Suc n) * z ^ n) * z" by simp
  thus "suminf (\<lambda>n. f (Suc n) * z ^ n) * z = suminf (\<lambda>n. f n * z ^ n) - f 0" by simp
qed

lemma summable_partial_sum_bound:
  fixes f :: "nat \<Rightarrow> 'a :: banach"
  assumes summable: "summable f" and e: "e > (0::real)"
  obtains N where "\<And>m n. m \<ge> N \<Longrightarrow> norm (\<Sum>k=m..n. f k) < e"
proof -
  from summable have "Cauchy (\<lambda>n. \<Sum>k<n. f k)"
    by (simp add: Cauchy_convergent_iff summable_iff_convergent)
  from CauchyD[OF this e] obtain N
    where N: "\<And>m n. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> norm ((\<Sum>k<m. f k) - (\<Sum>k<n. f k)) < e" by blast
  {
    fix m n :: nat assume m: "m \<ge> N"
    have "norm (\<Sum>k=m..n. f k) < e"
    proof (cases "n \<ge> m")
      assume n: "n \<ge> m"
      with m have "norm ((\<Sum>k<Suc n. f k) - (\<Sum>k<m. f k)) < e" by (intro N) simp_all
      also from n have "(\<Sum>k<Suc n. f k) - (\<Sum>k<m. f k) = (\<Sum>k=m..n. f k)"
        by (subst setsum_diff [symmetric]) (simp_all add: setsum_last_plus)
      finally show ?thesis .
    qed (insert e, simp_all)
  }
  thus ?thesis by (rule that)
qed

lemma powser_sums_if:
  "(\<lambda>n. (if n = m then (1 :: 'a :: {ring_1,topological_space}) else 0) * z^n) sums z^m"
proof -
  have "(\<lambda>n. (if n = m then 1 else 0) * z^n) = (\<lambda>n. if n = m then z^n else 0)"
    by (intro ext) auto
  thus ?thesis by (simp add: sums_single)
qed

lemma
   fixes f :: "nat \<Rightarrow> real"
   assumes "summable f"
   and "inj g"
   and pos: "\<And>x. 0 \<le> f x"
   shows summable_reindex: "summable (f o g)"
   and suminf_reindex_mono: "suminf (f o g) \<le> suminf f"
   and suminf_reindex: "(\<And>x. x \<notin> range g \<Longrightarrow> f x = 0) \<Longrightarrow> suminf (f \<circ> g) = suminf f"
proof -
  from \<open>inj g\<close> have [simp]: "\<And>A. inj_on g A" by(rule subset_inj_on) simp

  have smaller: "\<forall>n. (\<Sum>i<n. (f \<circ> g) i) \<le> suminf f"
  proof
    fix n
    have "\<forall> n' \<in> (g ` {..<n}). n' < Suc (Max (g ` {..<n}))"
      by(metis Max_ge finite_imageI finite_lessThan not_le not_less_eq)
    then obtain m where n: "\<And>n'. n' < n \<Longrightarrow> g n' < m" by blast

    have "(\<Sum>i<n. f (g i)) = setsum f (g ` {..<n})"
      by (simp add: setsum.reindex)
    also have "\<dots> \<le> (\<Sum>i<m. f i)"
      by (rule setsum_mono3) (auto simp add: pos n[rule_format])
    also have "\<dots> \<le> suminf f"
      using \<open>summable f\<close>
      by (rule setsum_le_suminf) (simp add: pos)
    finally show "(\<Sum>i<n. (f \<circ>  g) i) \<le> suminf f" by simp
  qed

  have "incseq (\<lambda>n. \<Sum>i<n. (f \<circ> g) i)"
    by (rule incseq_SucI) (auto simp add: pos)
  then obtain  L where L: "(\<lambda> n. \<Sum>i<n. (f \<circ> g) i) \<longlonglongrightarrow> L"
    using smaller by(rule incseq_convergent)
  hence "(f \<circ> g) sums L" by (simp add: sums_def)
  thus "summable (f o g)" by (auto simp add: sums_iff)

  hence "(\<lambda>n. \<Sum>i<n. (f \<circ> g) i) \<longlonglongrightarrow> suminf (f \<circ> g)"
    by(rule summable_LIMSEQ)
  thus le: "suminf (f \<circ> g) \<le> suminf f"
    by(rule LIMSEQ_le_const2)(blast intro: smaller[rule_format])

  assume f: "\<And>x. x \<notin> range g \<Longrightarrow> f x = 0"

  from \<open>summable f\<close> have "suminf f \<le> suminf (f \<circ> g)"
  proof(rule suminf_le_const)
    fix n
    have "\<forall> n' \<in> (g -` {..<n}). n' < Suc (Max (g -` {..<n}))"
      by(auto intro: Max_ge simp add: finite_vimageI less_Suc_eq_le)
    then obtain m where n: "\<And>n'. g n' < n \<Longrightarrow> n' < m" by blast

    have "(\<Sum>i<n. f i) = (\<Sum>i\<in>{..<n} \<inter> range g. f i)"
      using f by(auto intro: setsum.mono_neutral_cong_right)
    also have "\<dots> = (\<Sum>i\<in>g -` {..<n}. (f \<circ> g) i)"
      by(rule setsum.reindex_cong[where l=g])(auto)
    also have "\<dots> \<le> (\<Sum>i<m. (f \<circ> g) i)"
      by(rule setsum_mono3)(auto simp add: pos n)
    also have "\<dots> \<le> suminf (f \<circ> g)"
      using \<open>summable (f o g)\<close>
      by(rule setsum_le_suminf)(simp add: pos)
    finally show "setsum f {..<n} \<le> suminf (f \<circ> g)" .
  qed
  with le show "suminf (f \<circ> g) = suminf f" by(rule antisym)
qed

lemma sums_mono_reindex:
  assumes subseq: "subseq g" and zero: "\<And>n. n \<notin> range g \<Longrightarrow> f n = 0"
  shows   "(\<lambda>n. f (g n)) sums c \<longleftrightarrow> f sums c"
unfolding sums_def
proof
  assume lim: "(\<lambda>n. \<Sum>k<n. f k) \<longlonglongrightarrow> c"
  have "(\<lambda>n. \<Sum>k<n. f (g k)) = (\<lambda>n. \<Sum>k<g n. f k)"
  proof
    fix n :: nat
    from subseq have "(\<Sum>k<n. f (g k)) = (\<Sum>k\<in>g`{..<n}. f k)"
      by (subst setsum.reindex) (auto intro: subseq_imp_inj_on)
    also from subseq have "\<dots> = (\<Sum>k<g n. f k)"
      by (intro setsum.mono_neutral_left ballI zero)
         (auto dest: subseq_strict_mono simp: strict_mono_less strict_mono_less_eq)
    finally show "(\<Sum>k<n. f (g k)) = (\<Sum>k<g n. f k)" .
  qed
  also from LIMSEQ_subseq_LIMSEQ[OF lim subseq] have "\<dots> \<longlonglongrightarrow> c" unfolding o_def .
  finally show "(\<lambda>n. \<Sum>k<n. f (g k)) \<longlonglongrightarrow> c" .
next
  assume lim: "(\<lambda>n. \<Sum>k<n. f (g k)) \<longlonglongrightarrow> c"
  define g_inv where "g_inv n = (LEAST m. g m \<ge> n)" for n
  from filterlim_subseq[OF subseq] have g_inv_ex: "\<exists>m. g m \<ge> n" for n
    by (auto simp: filterlim_at_top eventually_at_top_linorder)
  hence g_inv: "g (g_inv n) \<ge> n" for n unfolding g_inv_def by (rule LeastI_ex)
  have g_inv_least: "m \<ge> g_inv n" if "g m \<ge> n" for m n using that
    unfolding g_inv_def by (rule Least_le)
  have g_inv_least': "g m < n" if "m < g_inv n" for m n using that g_inv_least[of n m] by linarith
  have "(\<lambda>n. \<Sum>k<n. f k) = (\<lambda>n. \<Sum>k<g_inv n. f (g k))"
  proof
    fix n :: nat
    {
      fix k assume k: "k \<in> {..<n} - g`{..<g_inv n}"
      have "k \<notin> range g"
      proof (rule notI, elim imageE)
        fix l assume l: "k = g l"
        have "g l < g (g_inv n)" by (rule less_le_trans[OF _ g_inv]) (insert k l, simp_all)
        with subseq have "l < g_inv n" by (simp add: subseq_strict_mono strict_mono_less)
        with k l show False by simp
      qed
      hence "f k = 0" by (rule zero)
    }
    with g_inv_least' g_inv have "(\<Sum>k<n. f k) = (\<Sum>k\<in>g`{..<g_inv n}. f k)"
      by (intro setsum.mono_neutral_right) auto
    also from subseq have "\<dots> = (\<Sum>k<g_inv n. f (g k))" using subseq_imp_inj_on
      by (subst setsum.reindex) simp_all
    finally show "(\<Sum>k<n. f k) = (\<Sum>k<g_inv n. f (g k))" .
  qed
  also {
    fix K n :: nat assume "g K \<le> n"
    also have "n \<le> g (g_inv n)" by (rule g_inv)
    finally have "K \<le> g_inv n" using subseq by (simp add: strict_mono_less_eq subseq_strict_mono)
  }
  hence "filterlim g_inv at_top sequentially"
    by (auto simp: filterlim_at_top eventually_at_top_linorder)
  from lim and this have "(\<lambda>n. \<Sum>k<g_inv n. f (g k)) \<longlonglongrightarrow> c" by (rule filterlim_compose)
  finally show "(\<lambda>n. \<Sum>k<n. f k) \<longlonglongrightarrow> c" .
qed

lemma summable_mono_reindex:
  assumes subseq: "subseq g" and zero: "\<And>n. n \<notin> range g \<Longrightarrow> f n = 0"
  shows   "summable (\<lambda>n. f (g n)) \<longleftrightarrow> summable f"
  using sums_mono_reindex[of g f, OF assms] by (simp add: summable_def)

lemma suminf_mono_reindex:
  assumes "subseq g" "\<And>n. n \<notin> range g \<Longrightarrow> f n = (0 :: 'a :: {t2_space,comm_monoid_add})"
  shows   "suminf (\<lambda>n. f (g n)) = suminf f"
proof (cases "summable f")
  case False
  hence "\<not>(\<exists>c. f sums c)" unfolding summable_def by blast
  hence "suminf f = The (\<lambda>_. False)" by (simp add: suminf_def)
  moreover from False have "\<not>summable (\<lambda>n. f (g n))"
    using summable_mono_reindex[of g f, OF assms] by simp
  hence "\<not>(\<exists>c. (\<lambda>n. f (g n)) sums c)" unfolding summable_def by blast
  hence "suminf (\<lambda>n. f (g n)) = The (\<lambda>_. False)" by (simp add: suminf_def)
  ultimately show ?thesis by simp
qed (insert sums_mono_reindex[of g f, OF assms] summable_mono_reindex[of g f, OF assms],
     simp_all add: sums_iff)

end
