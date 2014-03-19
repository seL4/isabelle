(*  Title       : Series.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp
Converted to setsum and polished yet more by TNN
Additional contributions by Jeremy Avigad
*)

header {* Infinite Series *}

theory Series
imports Limits
begin

subsection {* Definition of infinite summability *}

definition
  sums :: "(nat \<Rightarrow> 'a::{topological_space, comm_monoid_add}) \<Rightarrow> 'a \<Rightarrow> bool"
  (infixr "sums" 80)
where
  "f sums s \<longleftrightarrow> (\<lambda>n. \<Sum>i<n. f i) ----> s"

definition summable :: "(nat \<Rightarrow> 'a::{topological_space, comm_monoid_add}) \<Rightarrow> bool" where
   "summable f \<longleftrightarrow> (\<exists>s. f sums s)"

definition
  suminf :: "(nat \<Rightarrow> 'a::{topological_space, comm_monoid_add}) \<Rightarrow> 'a"
  (binder "\<Sum>" 10)
where
  "suminf f = (THE s. f sums s)"

subsection {* Infinite summability on topological monoids *}

lemma sums_subst[trans]: "f = g \<Longrightarrow> g sums z \<Longrightarrow> f sums z"
  by simp

lemma sums_summable: "f sums l \<Longrightarrow> summable f"
  by (simp add: sums_def summable_def, blast)

lemma summable_iff_convergent: "summable f \<longleftrightarrow> convergent (\<lambda>n. \<Sum>i<n. f i)"
  by (simp add: summable_def sums_def convergent_def)

lemma suminf_eq_lim: "suminf f = lim (\<lambda>n. \<Sum>i<n. f i)"
  by (simp add: suminf_def sums_def lim_def)

lemma sums_zero[simp, intro]: "(\<lambda>n. 0) sums 0"
  unfolding sums_def by (simp add: tendsto_const)

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
      proof (safe intro!: setsum_mono_zero_right f)
        fix i assume "i \<in> N"
        then have "i \<le> Max N" by simp
        then show "i < n + Suc (Max N)" by simp
      qed
    qed }
  note eq = this
  show ?thesis unfolding sums_def
    by (rule LIMSEQ_offset[of _ "Suc (Max N)"])
       (simp add: eq atLeast0LessThan tendsto_const del: add_Suc_right)
qed

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

lemma summable_LIMSEQ: "summable f \<Longrightarrow> (\<lambda>n. \<Sum>i<n. f i) ----> suminf f"
  by (rule summable_sums [unfolded sums_def])

lemma sums_unique: "f sums s \<Longrightarrow> s = suminf f"
  by (metis limI suminf_eq_lim sums_def)

lemma sums_iff: "f sums x \<longleftrightarrow> summable f \<and> (suminf f = x)"
  by (metis summable_sums sums_summable sums_unique)

lemma suminf_finite:
  assumes N: "finite N" and f: "\<And>n. n \<notin> N \<Longrightarrow> f n = 0"
  shows "suminf f = (\<Sum>n\<in>N. f n)"
  using sums_finite[OF assms, THEN sums_unique] by simp

end

lemma suminf_zero[simp]: "suminf (\<lambda>n. 0::'a::{t2_space, comm_monoid_add}) = 0"
  by (rule sums_zero [THEN sums_unique, symmetric])


subsection {* Infinite summability on ordered, topological monoids *}

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

lemma setsum_less_suminf2: "summable f \<Longrightarrow> \<forall>m\<ge>n. 0 \<le> f m \<Longrightarrow> n \<le> i \<Longrightarrow> 0 < f i \<Longrightarrow> setsum f {..<n} < suminf f"
  using
    setsum_le_suminf[of "Suc i"]
    add_strict_increasing[of "f i" "setsum f {..<n}" "setsum f {..<i}"]
    setsum_mono2[of "{..<i}" "{..<n}" f]
  by (auto simp: less_imp_le ac_simps)

lemma setsum_less_suminf: "summable f \<Longrightarrow> \<forall>m\<ge>n. 0 < f m \<Longrightarrow> setsum f {..<n} < suminf f"
  using setsum_less_suminf2[of n n] by (simp add: less_imp_le)

lemma suminf_pos2: "summable f \<Longrightarrow> \<forall>n. 0 \<le> f n \<Longrightarrow> 0 < f i \<Longrightarrow> 0 < suminf f"
  using setsum_less_suminf2[of 0 i] by simp

lemma suminf_pos: "summable f \<Longrightarrow> \<forall>n. 0 < f n \<Longrightarrow> 0 < suminf f"
  using suminf_pos2[of 0] by (simp add: less_imp_le)

lemma suminf_le_const: "summable f \<Longrightarrow> (\<And>n. setsum f {..<n} \<le> x) \<Longrightarrow> suminf f \<le> x"
  by (metis LIMSEQ_le_const2 summable_LIMSEQ)

lemma suminf_eq_zero_iff: "summable f \<Longrightarrow> \<forall>n. 0 \<le> f n \<Longrightarrow> suminf f = 0 \<longleftrightarrow> (\<forall>n. f n = 0)"
proof
  assume "summable f" "suminf f = 0" and pos: "\<forall>n. 0 \<le> f n"
  then have f: "(\<lambda>n. \<Sum>i<n. f i) ----> 0"
    using summable_LIMSEQ[of f] by simp
  then have "\<And>i. (\<Sum>n\<in>{i}. f n) \<le> 0"
  proof (rule LIMSEQ_le_const)
    fix i show "\<exists>N. \<forall>n\<ge>N. (\<Sum>n\<in>{i}. f n) \<le> setsum f {..<n}"
      using pos by (intro exI[of _ "Suc i"] allI impI setsum_mono2) auto
  qed
  with pos show "\<forall>n. f n = 0"
    by (auto intro!: antisym)
qed (metis suminf_zero fun_eq_iff)

lemma suminf_pos_iff: "summable f \<Longrightarrow> \<forall>n. 0 \<le> f n \<Longrightarrow> 0 < suminf f \<longleftrightarrow> (\<exists>i. 0 < f i)"
  using setsum_le_suminf[of 0] suminf_eq_zero_iff by (simp add: less_le)

end

lemma summableI_nonneg_bounded:
  fixes f:: "nat \<Rightarrow> 'a::{ordered_comm_monoid_add, linorder_topology, conditionally_complete_linorder}"
  assumes pos[simp]: "\<And>n. 0 \<le> f n" and le: "\<And>n. (\<Sum>i<n. f i) \<le> x"
  shows "summable f"
  unfolding summable_def sums_def[abs_def]
proof (intro exI order_tendstoI)
  have [simp, intro]: "bdd_above (range (\<lambda>n. \<Sum>i<n. f i))"
    using le by (auto simp: bdd_above_def)
  { fix a assume "a < (SUP n. \<Sum>i<n. f i)"
    then obtain n where "a < (\<Sum>i<n. f i)"
      by (auto simp add: less_cSUP_iff)
    then have "\<And>m. n \<le> m \<Longrightarrow> a < (\<Sum>i<m. f i)"
      by (rule less_le_trans) (auto intro!: setsum_mono2)
    then show "eventually (\<lambda>n. a < (\<Sum>i<n. f i)) sequentially"
      by (auto simp: eventually_sequentially) }
  { fix a assume "(SUP n. \<Sum>i<n. f i) < a"
    moreover have "\<And>n. (\<Sum>i<n. f i) \<le> (SUP n. \<Sum>i<n. f i)"
      by (auto intro: cSUP_upper)
    ultimately show "eventually (\<lambda>n. (\<Sum>i<n. f i) < a) sequentially"
      by (auto intro: le_less_trans simp: eventually_sequentially) }
qed

subsection {* Infinite summability on real normed vector spaces *}

lemma sums_Suc_iff:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "(\<lambda>n. f (Suc n)) sums s \<longleftrightarrow> f sums (s + f 0)"
proof -
  have "f sums (s + f 0) \<longleftrightarrow> (\<lambda>i. \<Sum>j<Suc i. f j) ----> s + f 0"
    by (subst LIMSEQ_Suc_iff) (simp add: sums_def)
  also have "\<dots> \<longleftrightarrow> (\<lambda>i. (\<Sum>j<i. f (Suc j)) + f 0) ----> s + f 0"
    by (simp add: ac_simps setsum_reindex image_iff lessThan_Suc_eq_insert_0)
  also have "\<dots> \<longleftrightarrow> (\<lambda>n. f (Suc n)) sums s"
  proof
    assume "(\<lambda>i. (\<Sum>j<i. f (Suc j)) + f 0) ----> s + f 0"
    with tendsto_add[OF this tendsto_const, of "- f 0"]
    show "(\<lambda>i. f (Suc i)) sums s"
      by (simp add: sums_def)
  qed (auto intro: tendsto_add tendsto_const simp: sums_def)
  finally show ?thesis ..
qed

context
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
begin

lemma sums_add: "f sums a \<Longrightarrow> g sums b \<Longrightarrow> (\<lambda>n. f n + g n) sums (a + b)"
  unfolding sums_def by (simp add: setsum_addf tendsto_add)

lemma summable_add: "summable f \<Longrightarrow> summable g \<Longrightarrow> summable (\<lambda>n. f n + g n)"
  unfolding summable_def by (auto intro: sums_add)

lemma suminf_add: "summable f \<Longrightarrow> summable g \<Longrightarrow> suminf f + suminf g = (\<Sum>n. f n + g n)"
  by (intro sums_unique sums_add summable_sums)

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

lemma sums_Suc: "(\<lambda> n. f (Suc n)) sums l \<Longrightarrow> f sums (l + f 0)"
  by (simp add: sums_Suc_iff)

lemma sums_iff_shift: "(\<lambda>i. f (i + n)) sums s \<longleftrightarrow> f sums (s + (\<Sum>i<n. f i))"
proof (induct n arbitrary: s)
  case (Suc n)
  moreover have "(\<lambda>i. f (Suc i + n)) sums s \<longleftrightarrow> (\<lambda>i. f (i + n)) sums (s + f n)"
    by (subst sums_Suc_iff) simp
  ultimately show ?case
    by (simp add: ac_simps)
qed simp

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

lemma suminf_exist_split: 
  fixes r :: real assumes "0 < r" and "summable f"
  shows "\<exists>N. \<forall>n\<ge>N. norm (\<Sum>i. f (i + n)) < r"
proof -
  from LIMSEQ_D[OF summable_LIMSEQ[OF `summable f`] `0 < r`]
  obtain N :: nat where "\<forall> n \<ge> N. norm (setsum f {..<n} - suminf f) < r" by auto
  thus ?thesis
    by (auto simp: norm_minus_commute suminf_minus_initial_segment[OF `summable f`])
qed

lemma summable_LIMSEQ_zero: "summable f \<Longrightarrow> f ----> 0"
  apply (drule summable_iff_convergent [THEN iffD1])
  apply (drule convergent_Cauchy)
  apply (simp only: Cauchy_iff LIMSEQ_iff, safe)
  apply (drule_tac x="r" in spec, safe)
  apply (rule_tac x="M" in exI, safe)
  apply (drule_tac x="Suc n" in spec, simp)
  apply (drule_tac x="n" in spec, simp)
  done

end

lemma (in bounded_linear) sums: "(\<lambda>n. X n) sums a \<Longrightarrow> (\<lambda>n. f (X n)) sums (f a)"
  unfolding sums_def by (drule tendsto, simp only: setsum)

lemma (in bounded_linear) summable: "summable (\<lambda>n. X n) \<Longrightarrow> summable (\<lambda>n. f (X n))"
  unfolding summable_def by (auto intro: sums)

lemma (in bounded_linear) suminf: "summable (\<lambda>n. X n) \<Longrightarrow> f (\<Sum>n. X n) = (\<Sum>n. f (X n))"
  by (intro sums_unique sums summable_sums)

lemmas sums_of_real = bounded_linear.sums [OF bounded_linear_of_real]
lemmas summable_of_real = bounded_linear.summable [OF bounded_linear_of_real]
lemmas suminf_of_real = bounded_linear.suminf [OF bounded_linear_of_real]

subsection {* Infinite summability on real normed algebras *}

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

subsection {* Infinite summability on real normed fields *}

context
  fixes c :: "'a::real_normed_field"
begin

lemma sums_divide: "f sums a \<Longrightarrow> (\<lambda>n. f n / c) sums (a / c)"
  by (rule bounded_linear.sums [OF bounded_linear_divide])

lemma summable_divide: "summable f \<Longrightarrow> summable (\<lambda>n. f n / c)"
  by (rule bounded_linear.summable [OF bounded_linear_divide])

lemma suminf_divide: "summable f \<Longrightarrow> suminf (\<lambda>n. f n / c) = suminf f / c"
  by (rule bounded_linear.suminf [OF bounded_linear_divide, symmetric])

text{*Sum of a geometric progression.*}

lemma geometric_sums: "norm c < 1 \<Longrightarrow> (\<lambda>n. c^n) sums (1 / (1 - c))"
proof -
  assume less_1: "norm c < 1"
  hence neq_1: "c \<noteq> 1" by auto
  hence neq_0: "c - 1 \<noteq> 0" by simp
  from less_1 have lim_0: "(\<lambda>n. c^n) ----> 0"
    by (rule LIMSEQ_power_zero)
  hence "(\<lambda>n. c ^ n / (c - 1) - 1 / (c - 1)) ----> 0 / (c - 1) - 1 / (c - 1)"
    using neq_0 by (intro tendsto_intros)
  hence "(\<lambda>n. (c ^ n - 1) / (c - 1)) ----> 1 / (1 - c)"
    by (simp add: nonzero_minus_divide_right [OF neq_0] diff_divide_distrib)
  thus "(\<lambda>n. c ^ n) sums (1 / (1 - c))"
    by (simp add: sums_def geometric_sum neq_1)
qed

lemma summable_geometric: "norm c < 1 \<Longrightarrow> summable (\<lambda>n. c^n)"
  by (rule geometric_sums [THEN sums_summable])

lemma suminf_geometric: "norm c < 1 \<Longrightarrow> suminf (\<lambda>n. c^n) = 1 / (1 - c)"
  by (rule sums_unique[symmetric]) (rule geometric_sums)

end

lemma power_half_series: "(\<lambda>n. (1/2::real)^Suc n) sums 1"
proof -
  have 2: "(\<lambda>n. (1/2::real)^n) sums 2" using geometric_sums [of "1/2::real"]
    by auto
  have "(\<lambda>n. (1/2::real)^Suc n) = (\<lambda>n. (1 / 2) ^ n / 2)"
    by simp
  thus ?thesis using sums_divide [OF 2, of 2]
    by simp
qed

subsection {* Infinite summability on Banach spaces *}

text{*Cauchy-type criterion for convergence of series (c.f. Harrison)*}

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

text{*Absolute convergence imples normal convergence*}

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

text {* Comparison tests *}

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

(*A better argument order*)
lemma summable_comparison_test': "summable g \<Longrightarrow> (\<And>n. n \<ge> N \<Longrightarrow> norm(f n) \<le> g n) \<Longrightarrow> summable f"
by (rule summable_comparison_test) auto

subsection {* The Ratio Test*}

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
          using `0 < c` `c < 1` assms(2)[OF `N \<le> m`] by (simp add: field_simps)
        ultimately show ?case by simp
      qed (insert `0 < c`, simp)
    qed
    show "summable (\<lambda>n. norm (f N) / c ^ N * c ^ n)"
      using `0 < c` `c < 1` by (intro summable_mult summable_geometric) simp
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

subsection {* Cauchy Product Formula *}

text {*
  Proof based on Analysis WebNotes: Chapter 07, Class 41
  @{url "http://www.math.unl.edu/~webnotes/classes/class41/prp77.htm"}
*}

lemma setsum_triangle_reindex:
  fixes n :: nat
  shows "(\<Sum>(i,j)\<in>{(i,j). i+j < n}. f i j) = (\<Sum>k<n. \<Sum>i\<le>k. f i (k - i))"
proof -
  have "(\<Sum>(i, j)\<in>{(i, j). i + j < n}. f i j) =
    (\<Sum>(k, i)\<in>(SIGMA k:{..<n}. {..k}). f i (k - i))"
  proof (rule setsum_reindex_cong)
    show "inj_on (\<lambda>(k,i). (i, k - i)) (SIGMA k:{..<n}. {..k})"
      by (rule inj_on_inverseI [where g="\<lambda>(i,j). (i+j, i)"], auto)
    show "{(i,j). i + j < n} = (\<lambda>(k,i). (i, k - i)) ` (SIGMA k:{..<n}. {..k})"
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
  have f_nonneg: "\<And>x. 0 \<le> ?f x"
    by (auto simp add: mult_nonneg_nonneg)
  hence norm_setsum_f: "\<And>A. norm (setsum ?f A) = setsum ?f A"
    unfolding real_norm_def
    by (simp only: abs_of_nonneg setsum_nonneg [rule_format])

  have "(\<lambda>n. (\<Sum>k<n. a k) * (\<Sum>k<n. b k)) ----> (\<Sum>k. a k) * (\<Sum>k. b k)"
    by (intro tendsto_mult summable_LIMSEQ summable_norm_cancel [OF a] summable_norm_cancel [OF b])
  hence 1: "(\<lambda>n. setsum ?g (?S1 n)) ----> (\<Sum>k. a k) * (\<Sum>k. b k)"
    by (simp only: setsum_product setsum_Sigma [rule_format] finite_lessThan)

  have "(\<lambda>n. (\<Sum>k<n. norm (a k)) * (\<Sum>k<n. norm (b k))) ----> (\<Sum>k. norm (a k)) * (\<Sum>k. norm (b k))"
    using a b by (intro tendsto_mult summable_LIMSEQ)
  hence "(\<lambda>n. setsum ?f (?S1 n)) ----> (\<Sum>k. norm (a k)) * (\<Sum>k. norm (b k))"
    by (simp only: setsum_product setsum_Sigma [rule_format] finite_lessThan)
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
  shows "(\<Sum>k. a k) * (\<Sum>k. b k) = (\<Sum>k. \<Sum>i\<le>k. a i * b (k - i))"
  using a b
  by (rule Cauchy_product_sums [THEN sums_unique])

subsection {* Series on @{typ real}s *}

lemma summable_norm_comparison_test: "\<exists>N. \<forall>n\<ge>N. norm (f n) \<le> g n \<Longrightarrow> summable g \<Longrightarrow> summable (\<lambda>n. norm (f n))"
  by (rule summable_comparison_test) auto

lemma summable_rabs_comparison_test: "\<lbrakk>\<exists>N. \<forall>n\<ge>N. \<bar>f n\<bar> \<le> g n; summable g\<rbrakk> \<Longrightarrow> summable (\<lambda>n. \<bar>f n :: real\<bar>)"
  by (rule summable_comparison_test) auto

lemma summable_rabs_cancel: "summable (\<lambda>n. \<bar>f n :: real\<bar>) \<Longrightarrow> summable f"
  by (rule summable_norm_cancel) simp

lemma summable_rabs: "summable (\<lambda>n. \<bar>f n :: real\<bar>) \<Longrightarrow> \<bar>suminf f\<bar> \<le> (\<Sum>n. \<bar>f n\<bar>)"
  by (fold real_norm_def) (rule summable_norm)

end
