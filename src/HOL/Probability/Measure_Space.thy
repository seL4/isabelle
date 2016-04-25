(*  Title:      HOL/Probability/Measure_Space.thy
    Author:     Lawrence C Paulson
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

section \<open>Measure spaces and their properties\<close>

theory Measure_Space
imports
  Measurable "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
begin

subsection "Relate extended reals and the indicator function"

lemma suminf_cmult_indicator:
  fixes f :: "nat \<Rightarrow> ennreal"
  assumes "disjoint_family A" "x \<in> A i"
  shows "(\<Sum>n. f n * indicator (A n) x) = f i"
proof -
  have **: "\<And>n. f n * indicator (A n) x = (if n = i then f n else 0 :: ennreal)"
    using \<open>x \<in> A i\<close> assms unfolding disjoint_family_on_def indicator_def by auto
  then have "\<And>n. (\<Sum>j<n. f j * indicator (A j) x) = (if i < n then f i else 0 :: ennreal)"
    by (auto simp: setsum.If_cases)
  moreover have "(SUP n. if i < n then f i else 0) = (f i :: ennreal)"
  proof (rule SUP_eqI)
    fix y :: ennreal assume "\<And>n. n \<in> UNIV \<Longrightarrow> (if i < n then f i else 0) \<le> y"
    from this[of "Suc i"] show "f i \<le> y" by auto
  qed (insert assms, simp add: zero_le)
  ultimately show ?thesis using assms
    by (subst suminf_eq_SUP) (auto simp: indicator_def)
qed

lemma suminf_indicator:
  assumes "disjoint_family A"
  shows "(\<Sum>n. indicator (A n) x :: ennreal) = indicator (\<Union>i. A i) x"
proof cases
  assume *: "x \<in> (\<Union>i. A i)"
  then obtain i where "x \<in> A i" by auto
  from suminf_cmult_indicator[OF assms(1), OF \<open>x \<in> A i\<close>, of "\<lambda>k. 1"]
  show ?thesis using * by simp
qed simp

lemma setsum_indicator_disjoint_family:
  fixes f :: "'d \<Rightarrow> 'e::semiring_1"
  assumes d: "disjoint_family_on A P" and "x \<in> A j" and "finite P" and "j \<in> P"
  shows "(\<Sum>i\<in>P. f i * indicator (A i) x) = f j"
proof -
  have "P \<inter> {i. x \<in> A i} = {j}"
    using d \<open>x \<in> A j\<close> \<open>j \<in> P\<close> unfolding disjoint_family_on_def
    by auto
  thus ?thesis
    unfolding indicator_def
    by (simp add: if_distrib setsum.If_cases[OF \<open>finite P\<close>])
qed

text \<open>
  The type for emeasure spaces is already defined in @{theory Sigma_Algebra}, as it is also used to
  represent sigma algebras (with an arbitrary emeasure).
\<close>

subsection "Extend binary sets"

lemma LIMSEQ_binaryset:
  assumes f: "f {} = 0"
  shows  "(\<lambda>n. \<Sum>i<n. f (binaryset A B i)) \<longlonglongrightarrow> f A + f B"
proof -
  have "(\<lambda>n. \<Sum>i < Suc (Suc n). f (binaryset A B i)) = (\<lambda>n. f A + f B)"
    proof
      fix n
      show "(\<Sum>i < Suc (Suc n). f (binaryset A B i)) = f A + f B"
        by (induct n)  (auto simp add: binaryset_def f)
    qed
  moreover
  have "... \<longlonglongrightarrow> f A + f B" by (rule tendsto_const)
  ultimately
  have "(\<lambda>n. \<Sum>i< Suc (Suc n). f (binaryset A B i)) \<longlonglongrightarrow> f A + f B"
    by metis
  hence "(\<lambda>n. \<Sum>i< n+2. f (binaryset A B i)) \<longlonglongrightarrow> f A + f B"
    by simp
  thus ?thesis by (rule LIMSEQ_offset [where k=2])
qed

lemma binaryset_sums:
  assumes f: "f {} = 0"
  shows  "(\<lambda>n. f (binaryset A B n)) sums (f A + f B)"
    by (simp add: sums_def LIMSEQ_binaryset [where f=f, OF f] atLeast0LessThan)

lemma suminf_binaryset_eq:
  fixes f :: "'a set \<Rightarrow> 'b::{comm_monoid_add, t2_space}"
  shows "f {} = 0 \<Longrightarrow> (\<Sum>n. f (binaryset A B n)) = f A + f B"
  by (metis binaryset_sums sums_unique)

subsection \<open>Properties of a premeasure @{term \<mu>}\<close>

text \<open>
  The definitions for @{const positive} and @{const countably_additive} should be here, by they are
  necessary to define @{typ "'a measure"} in @{theory Sigma_Algebra}.
\<close>

definition subadditive where
  "subadditive M f \<longleftrightarrow> (\<forall>x\<in>M. \<forall>y\<in>M. x \<inter> y = {} \<longrightarrow> f (x \<union> y) \<le> f x + f y)"

lemma subadditiveD: "subadditive M f \<Longrightarrow> x \<inter> y = {} \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> f (x \<union> y) \<le> f x + f y"
  by (auto simp add: subadditive_def)

definition countably_subadditive where
  "countably_subadditive M f \<longleftrightarrow>
    (\<forall>A. range A \<subseteq> M \<longrightarrow> disjoint_family A \<longrightarrow> (\<Union>i. A i) \<in> M \<longrightarrow> (f (\<Union>i. A i) \<le> (\<Sum>i. f (A i))))"

lemma (in ring_of_sets) countably_subadditive_subadditive:
  fixes f :: "'a set \<Rightarrow> ennreal"
  assumes f: "positive M f" and cs: "countably_subadditive M f"
  shows  "subadditive M f"
proof (auto simp add: subadditive_def)
  fix x y
  assume x: "x \<in> M" and y: "y \<in> M" and "x \<inter> y = {}"
  hence "disjoint_family (binaryset x y)"
    by (auto simp add: disjoint_family_on_def binaryset_def)
  hence "range (binaryset x y) \<subseteq> M \<longrightarrow>
         (\<Union>i. binaryset x y i) \<in> M \<longrightarrow>
         f (\<Union>i. binaryset x y i) \<le> (\<Sum> n. f (binaryset x y n))"
    using cs by (auto simp add: countably_subadditive_def)
  hence "{x,y,{}} \<subseteq> M \<longrightarrow> x \<union> y \<in> M \<longrightarrow>
         f (x \<union> y) \<le> (\<Sum> n. f (binaryset x y n))"
    by (simp add: range_binaryset_eq UN_binaryset_eq)
  thus "f (x \<union> y) \<le>  f x + f y" using f x y
    by (auto simp add: Un o_def suminf_binaryset_eq positive_def)
qed

definition additive where
  "additive M \<mu> \<longleftrightarrow> (\<forall>x\<in>M. \<forall>y\<in>M. x \<inter> y = {} \<longrightarrow> \<mu> (x \<union> y) = \<mu> x + \<mu> y)"

definition increasing where
  "increasing M \<mu> \<longleftrightarrow> (\<forall>x\<in>M. \<forall>y\<in>M. x \<subseteq> y \<longrightarrow> \<mu> x \<le> \<mu> y)"

lemma positiveD1: "positive M f \<Longrightarrow> f {} = 0" by (auto simp: positive_def)

lemma positiveD_empty:
  "positive M f \<Longrightarrow> f {} = 0"
  by (auto simp add: positive_def)

lemma additiveD:
  "additive M f \<Longrightarrow> x \<inter> y = {} \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> f (x \<union> y) = f x + f y"
  by (auto simp add: additive_def)

lemma increasingD:
  "increasing M f \<Longrightarrow> x \<subseteq> y \<Longrightarrow> x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> f x \<le> f y"
  by (auto simp add: increasing_def)

lemma countably_additiveI[case_names countably]:
  "(\<And>A. range A \<subseteq> M \<Longrightarrow> disjoint_family A \<Longrightarrow> (\<Union>i. A i) \<in> M \<Longrightarrow> (\<Sum>i. f (A i)) = f (\<Union>i. A i))
  \<Longrightarrow> countably_additive M f"
  by (simp add: countably_additive_def)

lemma (in ring_of_sets) disjointed_additive:
  assumes f: "positive M f" "additive M f" and A: "range A \<subseteq> M" "incseq A"
  shows "(\<Sum>i\<le>n. f (disjointed A i)) = f (A n)"
proof (induct n)
  case (Suc n)
  then have "(\<Sum>i\<le>Suc n. f (disjointed A i)) = f (A n) + f (disjointed A (Suc n))"
    by simp
  also have "\<dots> = f (A n \<union> disjointed A (Suc n))"
    using A by (subst f(2)[THEN additiveD]) (auto simp: disjointed_mono)
  also have "A n \<union> disjointed A (Suc n) = A (Suc n)"
    using \<open>incseq A\<close> by (auto dest: incseq_SucD simp: disjointed_mono)
  finally show ?case .
qed simp

lemma (in ring_of_sets) additive_sum:
  fixes A:: "'i \<Rightarrow> 'a set"
  assumes f: "positive M f" and ad: "additive M f" and "finite S"
      and A: "A`S \<subseteq> M"
      and disj: "disjoint_family_on A S"
  shows  "(\<Sum>i\<in>S. f (A i)) = f (\<Union>i\<in>S. A i)"
  using \<open>finite S\<close> disj A
proof induct
  case empty show ?case using f by (simp add: positive_def)
next
  case (insert s S)
  then have "A s \<inter> (\<Union>i\<in>S. A i) = {}"
    by (auto simp add: disjoint_family_on_def neq_iff)
  moreover
  have "A s \<in> M" using insert by blast
  moreover have "(\<Union>i\<in>S. A i) \<in> M"
    using insert \<open>finite S\<close> by auto
  ultimately have "f (A s \<union> (\<Union>i\<in>S. A i)) = f (A s) + f(\<Union>i\<in>S. A i)"
    using ad UNION_in_sets A by (auto simp add: additive_def)
  with insert show ?case using ad disjoint_family_on_mono[of S "insert s S" A]
    by (auto simp add: additive_def subset_insertI)
qed

lemma (in ring_of_sets) additive_increasing:
  fixes f :: "'a set \<Rightarrow> ennreal"
  assumes posf: "positive M f" and addf: "additive M f"
  shows "increasing M f"
proof (auto simp add: increasing_def)
  fix x y
  assume xy: "x \<in> M" "y \<in> M" "x \<subseteq> y"
  then have "y - x \<in> M" by auto
  then have "f x + 0 \<le> f x + f (y-x)" by (intro add_left_mono zero_le)
  also have "... = f (x \<union> (y-x))" using addf
    by (auto simp add: additive_def) (metis Diff_disjoint Un_Diff_cancel Diff xy(1,2))
  also have "... = f y"
    by (metis Un_Diff_cancel Un_absorb1 xy(3))
  finally show "f x \<le> f y" by simp
qed

lemma (in ring_of_sets) subadditive:
  fixes f :: "'a set \<Rightarrow> ennreal"
  assumes f: "positive M f" "additive M f" and A: "A`S \<subseteq> M" and S: "finite S"
  shows "f (\<Union>i\<in>S. A i) \<le> (\<Sum>i\<in>S. f (A i))"
using S A
proof (induct S)
  case empty thus ?case using f by (auto simp: positive_def)
next
  case (insert x F)
  hence in_M: "A x \<in> M" "(\<Union>i\<in>F. A i) \<in> M" "(\<Union>i\<in>F. A i) - A x \<in> M" using A by force+
  have subs: "(\<Union>i\<in>F. A i) - A x \<subseteq> (\<Union>i\<in>F. A i)" by auto
  have "(\<Union>i\<in>(insert x F). A i) = A x \<union> ((\<Union>i\<in>F. A i) - A x)" by auto
  hence "f (\<Union>i\<in>(insert x F). A i) = f (A x \<union> ((\<Union>i\<in>F. A i) - A x))"
    by simp
  also have "\<dots> = f (A x) + f ((\<Union>i\<in>F. A i) - A x)"
    using f(2) by (rule additiveD) (insert in_M, auto)
  also have "\<dots> \<le> f (A x) + f (\<Union>i\<in>F. A i)"
    using additive_increasing[OF f] in_M subs by (auto simp: increasing_def intro: add_left_mono)
  also have "\<dots> \<le> f (A x) + (\<Sum>i\<in>F. f (A i))" using insert by (auto intro: add_left_mono)
  finally show "f (\<Union>i\<in>(insert x F). A i) \<le> (\<Sum>i\<in>(insert x F). f (A i))" using insert by simp
qed

lemma (in ring_of_sets) countably_additive_additive:
  fixes f :: "'a set \<Rightarrow> ennreal"
  assumes posf: "positive M f" and ca: "countably_additive M f"
  shows "additive M f"
proof (auto simp add: additive_def)
  fix x y
  assume x: "x \<in> M" and y: "y \<in> M" and "x \<inter> y = {}"
  hence "disjoint_family (binaryset x y)"
    by (auto simp add: disjoint_family_on_def binaryset_def)
  hence "range (binaryset x y) \<subseteq> M \<longrightarrow>
         (\<Union>i. binaryset x y i) \<in> M \<longrightarrow>
         f (\<Union>i. binaryset x y i) = (\<Sum> n. f (binaryset x y n))"
    using ca
    by (simp add: countably_additive_def)
  hence "{x,y,{}} \<subseteq> M \<longrightarrow> x \<union> y \<in> M \<longrightarrow>
         f (x \<union> y) = (\<Sum>n. f (binaryset x y n))"
    by (simp add: range_binaryset_eq UN_binaryset_eq)
  thus "f (x \<union> y) = f x + f y" using posf x y
    by (auto simp add: Un suminf_binaryset_eq positive_def)
qed

lemma (in algebra) increasing_additive_bound:
  fixes A:: "nat \<Rightarrow> 'a set" and  f :: "'a set \<Rightarrow> ennreal"
  assumes f: "positive M f" and ad: "additive M f"
      and inc: "increasing M f"
      and A: "range A \<subseteq> M"
      and disj: "disjoint_family A"
  shows  "(\<Sum>i. f (A i)) \<le> f \<Omega>"
proof (safe intro!: suminf_le_const)
  fix N
  note disj_N = disjoint_family_on_mono[OF _ disj, of "{..<N}"]
  have "(\<Sum>i<N. f (A i)) = f (\<Union>i\<in>{..<N}. A i)"
    using A by (intro additive_sum [OF f ad _ _]) (auto simp: disj_N)
  also have "... \<le> f \<Omega>" using space_closed A
    by (intro increasingD[OF inc] finite_UN) auto
  finally show "(\<Sum>i<N. f (A i)) \<le> f \<Omega>" by simp
qed (insert f A, auto simp: positive_def)

lemma (in ring_of_sets) countably_additiveI_finite:
  fixes \<mu> :: "'a set \<Rightarrow> ennreal"
  assumes "finite \<Omega>" "positive M \<mu>" "additive M \<mu>"
  shows "countably_additive M \<mu>"
proof (rule countably_additiveI)
  fix F :: "nat \<Rightarrow> 'a set" assume F: "range F \<subseteq> M" "(\<Union>i. F i) \<in> M" and disj: "disjoint_family F"

  have "\<forall>i\<in>{i. F i \<noteq> {}}. \<exists>x. x \<in> F i" by auto
  from bchoice[OF this] obtain f where f: "\<And>i. F i \<noteq> {} \<Longrightarrow> f i \<in> F i" by auto

  have inj_f: "inj_on f {i. F i \<noteq> {}}"
  proof (rule inj_onI, simp)
    fix i j a b assume *: "f i = f j" "F i \<noteq> {}" "F j \<noteq> {}"
    then have "f i \<in> F i" "f j \<in> F j" using f by force+
    with disj * show "i = j" by (auto simp: disjoint_family_on_def)
  qed
  have "finite (\<Union>i. F i)"
    by (metis F(2) assms(1) infinite_super sets_into_space)

  have F_subset: "{i. \<mu> (F i) \<noteq> 0} \<subseteq> {i. F i \<noteq> {}}"
    by (auto simp: positiveD_empty[OF \<open>positive M \<mu>\<close>])
  moreover have fin_not_empty: "finite {i. F i \<noteq> {}}"
  proof (rule finite_imageD)
    from f have "f`{i. F i \<noteq> {}} \<subseteq> (\<Union>i. F i)" by auto
    then show "finite (f`{i. F i \<noteq> {}})"
      by (rule finite_subset) fact
  qed fact
  ultimately have fin_not_0: "finite {i. \<mu> (F i) \<noteq> 0}"
    by (rule finite_subset)

  have disj_not_empty: "disjoint_family_on F {i. F i \<noteq> {}}"
    using disj by (auto simp: disjoint_family_on_def)

  from fin_not_0 have "(\<Sum>i. \<mu> (F i)) = (\<Sum>i | \<mu> (F i) \<noteq> 0. \<mu> (F i))"
    by (rule suminf_finite) auto
  also have "\<dots> = (\<Sum>i | F i \<noteq> {}. \<mu> (F i))"
    using fin_not_empty F_subset by (rule setsum.mono_neutral_left) auto
  also have "\<dots> = \<mu> (\<Union>i\<in>{i. F i \<noteq> {}}. F i)"
    using \<open>positive M \<mu>\<close> \<open>additive M \<mu>\<close> fin_not_empty disj_not_empty F by (intro additive_sum) auto
  also have "\<dots> = \<mu> (\<Union>i. F i)"
    by (rule arg_cong[where f=\<mu>]) auto
  finally show "(\<Sum>i. \<mu> (F i)) = \<mu> (\<Union>i. F i)" .
qed

lemma (in ring_of_sets) countably_additive_iff_continuous_from_below:
  fixes f :: "'a set \<Rightarrow> ennreal"
  assumes f: "positive M f" "additive M f"
  shows "countably_additive M f \<longleftrightarrow>
    (\<forall>A. range A \<subseteq> M \<longrightarrow> incseq A \<longrightarrow> (\<Union>i. A i) \<in> M \<longrightarrow> (\<lambda>i. f (A i)) \<longlonglongrightarrow> f (\<Union>i. A i))"
  unfolding countably_additive_def
proof safe
  assume count_sum: "\<forall>A. range A \<subseteq> M \<longrightarrow> disjoint_family A \<longrightarrow> UNION UNIV A \<in> M \<longrightarrow> (\<Sum>i. f (A i)) = f (UNION UNIV A)"
  fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> M" "incseq A" "(\<Union>i. A i) \<in> M"
  then have dA: "range (disjointed A) \<subseteq> M" by (auto simp: range_disjointed_sets)
  with count_sum[THEN spec, of "disjointed A"] A(3)
  have f_UN: "(\<Sum>i. f (disjointed A i)) = f (\<Union>i. A i)"
    by (auto simp: UN_disjointed_eq disjoint_family_disjointed)
  moreover have "(\<lambda>n. (\<Sum>i<n. f (disjointed A i))) \<longlonglongrightarrow> (\<Sum>i. f (disjointed A i))"
    using f(1)[unfolded positive_def] dA
    by (auto intro!: summable_LIMSEQ summableI)
  from LIMSEQ_Suc[OF this]
  have "(\<lambda>n. (\<Sum>i\<le>n. f (disjointed A i))) \<longlonglongrightarrow> (\<Sum>i. f (disjointed A i))"
    unfolding lessThan_Suc_atMost .
  moreover have "\<And>n. (\<Sum>i\<le>n. f (disjointed A i)) = f (A n)"
    using disjointed_additive[OF f A(1,2)] .
  ultimately show "(\<lambda>i. f (A i)) \<longlonglongrightarrow> f (\<Union>i. A i)" by simp
next
  assume cont: "\<forall>A. range A \<subseteq> M \<longrightarrow> incseq A \<longrightarrow> (\<Union>i. A i) \<in> M \<longrightarrow> (\<lambda>i. f (A i)) \<longlonglongrightarrow> f (\<Union>i. A i)"
  fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> M" "disjoint_family A" "(\<Union>i. A i) \<in> M"
  have *: "(\<Union>n. (\<Union>i<n. A i)) = (\<Union>i. A i)" by auto
  have "(\<lambda>n. f (\<Union>i<n. A i)) \<longlonglongrightarrow> f (\<Union>i. A i)"
  proof (unfold *[symmetric], intro cont[rule_format])
    show "range (\<lambda>i. \<Union>i<i. A i) \<subseteq> M" "(\<Union>i. \<Union>i<i. A i) \<in> M"
      using A * by auto
  qed (force intro!: incseq_SucI)
  moreover have "\<And>n. f (\<Union>i<n. A i) = (\<Sum>i<n. f (A i))"
    using A
    by (intro additive_sum[OF f, of _ A, symmetric])
       (auto intro: disjoint_family_on_mono[where B=UNIV])
  ultimately
  have "(\<lambda>i. f (A i)) sums f (\<Union>i. A i)"
    unfolding sums_def by simp
  from sums_unique[OF this]
  show "(\<Sum>i. f (A i)) = f (\<Union>i. A i)" by simp
qed

lemma (in ring_of_sets) continuous_from_above_iff_empty_continuous:
  fixes f :: "'a set \<Rightarrow> ennreal"
  assumes f: "positive M f" "additive M f"
  shows "(\<forall>A. range A \<subseteq> M \<longrightarrow> decseq A \<longrightarrow> (\<Inter>i. A i) \<in> M \<longrightarrow> (\<forall>i. f (A i) \<noteq> \<infinity>) \<longrightarrow> (\<lambda>i. f (A i)) \<longlonglongrightarrow> f (\<Inter>i. A i))
     \<longleftrightarrow> (\<forall>A. range A \<subseteq> M \<longrightarrow> decseq A \<longrightarrow> (\<Inter>i. A i) = {} \<longrightarrow> (\<forall>i. f (A i) \<noteq> \<infinity>) \<longrightarrow> (\<lambda>i. f (A i)) \<longlonglongrightarrow> 0)"
proof safe
  assume cont: "(\<forall>A. range A \<subseteq> M \<longrightarrow> decseq A \<longrightarrow> (\<Inter>i. A i) \<in> M \<longrightarrow> (\<forall>i. f (A i) \<noteq> \<infinity>) \<longrightarrow> (\<lambda>i. f (A i)) \<longlonglongrightarrow> f (\<Inter>i. A i))"
  fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> M" "decseq A" "(\<Inter>i. A i) = {}" "\<forall>i. f (A i) \<noteq> \<infinity>"
  with cont[THEN spec, of A] show "(\<lambda>i. f (A i)) \<longlonglongrightarrow> 0"
    using \<open>positive M f\<close>[unfolded positive_def] by auto
next
  assume cont: "\<forall>A. range A \<subseteq> M \<longrightarrow> decseq A \<longrightarrow> (\<Inter>i. A i) = {} \<longrightarrow> (\<forall>i. f (A i) \<noteq> \<infinity>) \<longrightarrow> (\<lambda>i. f (A i)) \<longlonglongrightarrow> 0"
  fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> M" "decseq A" "(\<Inter>i. A i) \<in> M" "\<forall>i. f (A i) \<noteq> \<infinity>"

  have f_mono: "\<And>a b. a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> a \<subseteq> b \<Longrightarrow> f a \<le> f b"
    using additive_increasing[OF f] unfolding increasing_def by simp

  have decseq_fA: "decseq (\<lambda>i. f (A i))"
    using A by (auto simp: decseq_def intro!: f_mono)
  have decseq: "decseq (\<lambda>i. A i - (\<Inter>i. A i))"
    using A by (auto simp: decseq_def)
  then have decseq_f: "decseq (\<lambda>i. f (A i - (\<Inter>i. A i)))"
    using A unfolding decseq_def by (auto intro!: f_mono Diff)
  have "f (\<Inter>x. A x) \<le> f (A 0)"
    using A by (auto intro!: f_mono)
  then have f_Int_fin: "f (\<Inter>x. A x) \<noteq> \<infinity>"
    using A by (auto simp: top_unique)
  { fix i
    have "f (A i - (\<Inter>i. A i)) \<le> f (A i)" using A by (auto intro!: f_mono)
    then have "f (A i - (\<Inter>i. A i)) \<noteq> \<infinity>"
      using A by (auto simp: top_unique) }
  note f_fin = this
  have "(\<lambda>i. f (A i - (\<Inter>i. A i))) \<longlonglongrightarrow> 0"
  proof (intro cont[rule_format, OF _ decseq _ f_fin])
    show "range (\<lambda>i. A i - (\<Inter>i. A i)) \<subseteq> M" "(\<Inter>i. A i - (\<Inter>i. A i)) = {}"
      using A by auto
  qed
  from INF_Lim_ereal[OF decseq_f this]
  have "(INF n. f (A n - (\<Inter>i. A i))) = 0" .
  moreover have "(INF n. f (\<Inter>i. A i)) = f (\<Inter>i. A i)"
    by auto
  ultimately have "(INF n. f (A n - (\<Inter>i. A i)) + f (\<Inter>i. A i)) = 0 + f (\<Inter>i. A i)"
    using A(4) f_fin f_Int_fin
    by (subst INF_ennreal_add_const) (auto simp: decseq_f)
  moreover {
    fix n
    have "f (A n - (\<Inter>i. A i)) + f (\<Inter>i. A i) = f ((A n - (\<Inter>i. A i)) \<union> (\<Inter>i. A i))"
      using A by (subst f(2)[THEN additiveD]) auto
    also have "(A n - (\<Inter>i. A i)) \<union> (\<Inter>i. A i) = A n"
      by auto
    finally have "f (A n - (\<Inter>i. A i)) + f (\<Inter>i. A i) = f (A n)" . }
  ultimately have "(INF n. f (A n)) = f (\<Inter>i. A i)"
    by simp
  with LIMSEQ_INF[OF decseq_fA]
  show "(\<lambda>i. f (A i)) \<longlonglongrightarrow> f (\<Inter>i. A i)" by simp
qed

lemma (in ring_of_sets) empty_continuous_imp_continuous_from_below:
  fixes f :: "'a set \<Rightarrow> ennreal"
  assumes f: "positive M f" "additive M f" "\<forall>A\<in>M. f A \<noteq> \<infinity>"
  assumes cont: "\<forall>A. range A \<subseteq> M \<longrightarrow> decseq A \<longrightarrow> (\<Inter>i. A i) = {} \<longrightarrow> (\<lambda>i. f (A i)) \<longlonglongrightarrow> 0"
  assumes A: "range A \<subseteq> M" "incseq A" "(\<Union>i. A i) \<in> M"
  shows "(\<lambda>i. f (A i)) \<longlonglongrightarrow> f (\<Union>i. A i)"
proof -
  from A have "(\<lambda>i. f ((\<Union>i. A i) - A i)) \<longlonglongrightarrow> 0"
    by (intro cont[rule_format]) (auto simp: decseq_def incseq_def)
  moreover
  { fix i
    have "f ((\<Union>i. A i) - A i \<union> A i) = f ((\<Union>i. A i) - A i) + f (A i)"
      using A by (intro f(2)[THEN additiveD]) auto
    also have "((\<Union>i. A i) - A i) \<union> A i = (\<Union>i. A i)"
      by auto
    finally have "f ((\<Union>i. A i) - A i) = f (\<Union>i. A i) - f (A i)"
      using f(3)[rule_format, of "A i"] A by (auto simp: ennreal_add_diff_cancel subset_eq) }
  moreover have "\<forall>\<^sub>F i in sequentially. f (A i) \<le> f (\<Union>i. A i)"
    using increasingD[OF additive_increasing[OF f(1, 2)], of "A _" "\<Union>i. A i"] A
    by (auto intro!: always_eventually simp: subset_eq)
  ultimately show "(\<lambda>i. f (A i)) \<longlonglongrightarrow> f (\<Union>i. A i)"
    by (auto intro: ennreal_tendsto_const_minus)
qed

lemma (in ring_of_sets) empty_continuous_imp_countably_additive:
  fixes f :: "'a set \<Rightarrow> ennreal"
  assumes f: "positive M f" "additive M f" and fin: "\<forall>A\<in>M. f A \<noteq> \<infinity>"
  assumes cont: "\<And>A. range A \<subseteq> M \<Longrightarrow> decseq A \<Longrightarrow> (\<Inter>i. A i) = {} \<Longrightarrow> (\<lambda>i. f (A i)) \<longlonglongrightarrow> 0"
  shows "countably_additive M f"
  using countably_additive_iff_continuous_from_below[OF f]
  using empty_continuous_imp_continuous_from_below[OF f fin] cont
  by blast

subsection \<open>Properties of @{const emeasure}\<close>

lemma emeasure_positive: "positive (sets M) (emeasure M)"
  by (cases M) (auto simp: sets_def emeasure_def Abs_measure_inverse measure_space_def)

lemma emeasure_empty[simp, intro]: "emeasure M {} = 0"
  using emeasure_positive[of M] by (simp add: positive_def)

lemma emeasure_single_in_space: "emeasure M {x} \<noteq> 0 \<Longrightarrow> x \<in> space M"
  using emeasure_notin_sets[of "{x}" M] by (auto dest: sets.sets_into_space zero_less_iff_neq_zero[THEN iffD2])

lemma emeasure_countably_additive: "countably_additive (sets M) (emeasure M)"
  by (cases M) (auto simp: sets_def emeasure_def Abs_measure_inverse measure_space_def)

lemma suminf_emeasure:
  "range A \<subseteq> sets M \<Longrightarrow> disjoint_family A \<Longrightarrow> (\<Sum>i. emeasure M (A i)) = emeasure M (\<Union>i. A i)"
  using sets.countable_UN[of A UNIV M] emeasure_countably_additive[of M]
  by (simp add: countably_additive_def)

lemma sums_emeasure:
  "disjoint_family F \<Longrightarrow> (\<And>i. F i \<in> sets M) \<Longrightarrow> (\<lambda>i. emeasure M (F i)) sums emeasure M (\<Union>i. F i)"
  unfolding sums_iff by (intro conjI suminf_emeasure) auto

lemma emeasure_additive: "additive (sets M) (emeasure M)"
  by (metis sets.countably_additive_additive emeasure_positive emeasure_countably_additive)

lemma plus_emeasure:
  "a \<in> sets M \<Longrightarrow> b \<in> sets M \<Longrightarrow> a \<inter> b = {} \<Longrightarrow> emeasure M a + emeasure M b = emeasure M (a \<union> b)"
  using additiveD[OF emeasure_additive] ..

lemma setsum_emeasure:
  "F`I \<subseteq> sets M \<Longrightarrow> disjoint_family_on F I \<Longrightarrow> finite I \<Longrightarrow>
    (\<Sum>i\<in>I. emeasure M (F i)) = emeasure M (\<Union>i\<in>I. F i)"
  by (metis sets.additive_sum emeasure_positive emeasure_additive)

lemma emeasure_mono:
  "a \<subseteq> b \<Longrightarrow> b \<in> sets M \<Longrightarrow> emeasure M a \<le> emeasure M b"
  by (metis zero_le sets.additive_increasing emeasure_additive emeasure_notin_sets emeasure_positive increasingD)

lemma emeasure_space:
  "emeasure M A \<le> emeasure M (space M)"
  by (metis emeasure_mono emeasure_notin_sets sets.sets_into_space sets.top zero_le)

lemma emeasure_Diff:
  assumes finite: "emeasure M B \<noteq> \<infinity>"
  and [measurable]: "A \<in> sets M" "B \<in> sets M" and "B \<subseteq> A"
  shows "emeasure M (A - B) = emeasure M A - emeasure M B"
proof -
  have "(A - B) \<union> B = A" using \<open>B \<subseteq> A\<close> by auto
  then have "emeasure M A = emeasure M ((A - B) \<union> B)" by simp
  also have "\<dots> = emeasure M (A - B) + emeasure M B"
    by (subst plus_emeasure[symmetric]) auto
  finally show "emeasure M (A - B) = emeasure M A - emeasure M B"
    using finite by simp
qed

lemma emeasure_compl:
  "s \<in> sets M \<Longrightarrow> emeasure M s \<noteq> \<infinity> \<Longrightarrow> emeasure M (space M - s) = emeasure M (space M) - emeasure M s"
  by (rule emeasure_Diff) (auto dest: sets.sets_into_space)

lemma Lim_emeasure_incseq:
  "range A \<subseteq> sets M \<Longrightarrow> incseq A \<Longrightarrow> (\<lambda>i. (emeasure M (A i))) \<longlonglongrightarrow> emeasure M (\<Union>i. A i)"
  using emeasure_countably_additive
  by (auto simp add: sets.countably_additive_iff_continuous_from_below emeasure_positive
    emeasure_additive)

lemma incseq_emeasure:
  assumes "range B \<subseteq> sets M" "incseq B"
  shows "incseq (\<lambda>i. emeasure M (B i))"
  using assms by (auto simp: incseq_def intro!: emeasure_mono)

lemma SUP_emeasure_incseq:
  assumes A: "range A \<subseteq> sets M" "incseq A"
  shows "(SUP n. emeasure M (A n)) = emeasure M (\<Union>i. A i)"
  using LIMSEQ_SUP[OF incseq_emeasure, OF A] Lim_emeasure_incseq[OF A]
  by (simp add: LIMSEQ_unique)

lemma decseq_emeasure:
  assumes "range B \<subseteq> sets M" "decseq B"
  shows "decseq (\<lambda>i. emeasure M (B i))"
  using assms by (auto simp: decseq_def intro!: emeasure_mono)

lemma INF_emeasure_decseq:
  assumes A: "range A \<subseteq> sets M" and "decseq A"
  and finite: "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
  shows "(INF n. emeasure M (A n)) = emeasure M (\<Inter>i. A i)"
proof -
  have le_MI: "emeasure M (\<Inter>i. A i) \<le> emeasure M (A 0)"
    using A by (auto intro!: emeasure_mono)
  hence *: "emeasure M (\<Inter>i. A i) \<noteq> \<infinity>" using finite[of 0] by (auto simp: top_unique)

  have "emeasure M (A 0) - (INF n. emeasure M (A n)) = (SUP n. emeasure M (A 0) - emeasure M (A n))"
    by (simp add: ennreal_INF_const_minus)
  also have "\<dots> = (SUP n. emeasure M (A 0 - A n))"
    using A finite \<open>decseq A\<close>[unfolded decseq_def] by (subst emeasure_Diff) auto
  also have "\<dots> = emeasure M (\<Union>i. A 0 - A i)"
  proof (rule SUP_emeasure_incseq)
    show "range (\<lambda>n. A 0 - A n) \<subseteq> sets M"
      using A by auto
    show "incseq (\<lambda>n. A 0 - A n)"
      using \<open>decseq A\<close> by (auto simp add: incseq_def decseq_def)
  qed
  also have "\<dots> = emeasure M (A 0) - emeasure M (\<Inter>i. A i)"
    using A finite * by (simp, subst emeasure_Diff) auto
  finally show ?thesis
    by (rule ennreal_minus_cancel[rotated 3])
       (insert finite A, auto intro: INF_lower emeasure_mono)
qed

lemma emeasure_INT_decseq_subset:
  fixes F :: "nat \<Rightarrow> 'a set"
  assumes I: "I \<noteq> {}" and F: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<le> j \<Longrightarrow> F j \<subseteq> F i"
  assumes F_sets[measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> sets M"
    and fin: "\<And>i. i \<in> I \<Longrightarrow> emeasure M (F i) \<noteq> \<infinity>"
  shows "emeasure M (\<Inter>i\<in>I. F i) = (INF i:I. emeasure M (F i))"
proof cases
  assume "finite I"
  have "(\<Inter>i\<in>I. F i) = F (Max I)"
    using I \<open>finite I\<close> by (intro antisym INF_lower INF_greatest F) auto
  moreover have "(INF i:I. emeasure M (F i)) = emeasure M (F (Max I))"
    using I \<open>finite I\<close> by (intro antisym INF_lower INF_greatest F emeasure_mono) auto
  ultimately show ?thesis
    by simp
next
  assume "infinite I"
  define L where "L n = (LEAST i. i \<in> I \<and> i \<ge> n)" for n
  have L: "L n \<in> I \<and> n \<le> L n" for n
    unfolding L_def
  proof (rule LeastI_ex)
    show "\<exists>x. x \<in> I \<and> n \<le> x"
      using \<open>infinite I\<close> finite_subset[of I "{..< n}"]
      by (rule_tac ccontr) (auto simp: not_le)
  qed
  have L_eq[simp]: "i \<in> I \<Longrightarrow> L i = i" for i
    unfolding L_def by (intro Least_equality) auto
  have L_mono: "i \<le> j \<Longrightarrow> L i \<le> L j" for i j
    using L[of j] unfolding L_def by (intro Least_le) (auto simp: L_def)

  have "emeasure M (\<Inter>i. F (L i)) = (INF i. emeasure M (F (L i)))"
  proof (intro INF_emeasure_decseq[symmetric])
    show "decseq (\<lambda>i. F (L i))"
      using L by (intro antimonoI F L_mono) auto
  qed (insert L fin, auto)
  also have "\<dots> = (INF i:I. emeasure M (F i))"
  proof (intro antisym INF_greatest)
    show "i \<in> I \<Longrightarrow> (INF i. emeasure M (F (L i))) \<le> emeasure M (F i)" for i
      by (intro INF_lower2[of i]) auto
  qed (insert L, auto intro: INF_lower)
  also have "(\<Inter>i. F (L i)) = (\<Inter>i\<in>I. F i)"
  proof (intro antisym INF_greatest)
    show "i \<in> I \<Longrightarrow> (\<Inter>i. F (L i)) \<subseteq> F i" for i
      by (intro INF_lower2[of i]) auto
  qed (insert L, auto)
  finally show ?thesis .
qed

lemma Lim_emeasure_decseq:
  assumes A: "range A \<subseteq> sets M" "decseq A" and fin: "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
  shows "(\<lambda>i. emeasure M (A i)) \<longlonglongrightarrow> emeasure M (\<Inter>i. A i)"
  using LIMSEQ_INF[OF decseq_emeasure, OF A]
  using INF_emeasure_decseq[OF A fin] by simp

lemma emeasure_lfp'[consumes 1, case_names cont measurable]:
  assumes "P M"
  assumes cont: "sup_continuous F"
  assumes *: "\<And>M A. P M \<Longrightarrow> (\<And>N. P N \<Longrightarrow> Measurable.pred N A) \<Longrightarrow> Measurable.pred M (F A)"
  shows "emeasure M {x\<in>space M. lfp F x} = (SUP i. emeasure M {x\<in>space M. (F ^^ i) (\<lambda>x. False) x})"
proof -
  have "emeasure M {x\<in>space M. lfp F x} = emeasure M (\<Union>i. {x\<in>space M. (F ^^ i) (\<lambda>x. False) x})"
    using sup_continuous_lfp[OF cont] by (auto simp add: bot_fun_def intro!: arg_cong2[where f=emeasure])
  moreover { fix i from \<open>P M\<close> have "{x\<in>space M. (F ^^ i) (\<lambda>x. False) x} \<in> sets M"
    by (induct i arbitrary: M) (auto simp add: pred_def[symmetric] intro: *) }
  moreover have "incseq (\<lambda>i. {x\<in>space M. (F ^^ i) (\<lambda>x. False) x})"
  proof (rule incseq_SucI)
    fix i
    have "(F ^^ i) (\<lambda>x. False) \<le> (F ^^ (Suc i)) (\<lambda>x. False)"
    proof (induct i)
      case 0 show ?case by (simp add: le_fun_def)
    next
      case Suc thus ?case using monoD[OF sup_continuous_mono[OF cont] Suc] by auto
    qed
    then show "{x \<in> space M. (F ^^ i) (\<lambda>x. False) x} \<subseteq> {x \<in> space M. (F ^^ Suc i) (\<lambda>x. False) x}"
      by auto
  qed
  ultimately show ?thesis
    by (subst SUP_emeasure_incseq) auto
qed

lemma emeasure_lfp:
  assumes [simp]: "\<And>s. sets (M s) = sets N"
  assumes cont: "sup_continuous F" "sup_continuous f"
  assumes meas: "\<And>P. Measurable.pred N P \<Longrightarrow> Measurable.pred N (F P)"
  assumes iter: "\<And>P s. Measurable.pred N P \<Longrightarrow> P \<le> lfp F \<Longrightarrow> emeasure (M s) {x\<in>space N. F P x} = f (\<lambda>s. emeasure (M s) {x\<in>space N. P x}) s"
  shows "emeasure (M s) {x\<in>space N. lfp F x} = lfp f s"
proof (subst lfp_transfer_bounded[where \<alpha>="\<lambda>F s. emeasure (M s) {x\<in>space N. F x}" and g=f and f=F and P="Measurable.pred N", symmetric])
  fix C assume "incseq C" "\<And>i. Measurable.pred N (C i)"
  then show "(\<lambda>s. emeasure (M s) {x \<in> space N. (SUP i. C i) x}) = (SUP i. (\<lambda>s. emeasure (M s) {x \<in> space N. C i x}))"
    unfolding SUP_apply[abs_def]
    by (subst SUP_emeasure_incseq) (auto simp: mono_def fun_eq_iff intro!: arg_cong2[where f=emeasure])
qed (auto simp add: iter le_fun_def SUP_apply[abs_def] intro!: meas cont)

lemma emeasure_subadditive_finite:
  "finite I \<Longrightarrow> A ` I \<subseteq> sets M \<Longrightarrow> emeasure M (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. emeasure M (A i))"
  by (rule sets.subadditive[OF emeasure_positive emeasure_additive]) auto

lemma emeasure_subadditive:
  "A \<in> sets M \<Longrightarrow> B \<in> sets M \<Longrightarrow> emeasure M (A \<union> B) \<le> emeasure M A + emeasure M B"
  using emeasure_subadditive_finite[of "{True, False}" "\<lambda>True \<Rightarrow> A | False \<Rightarrow> B" M] by simp

lemma emeasure_subadditive_countably:
  assumes "range f \<subseteq> sets M"
  shows "emeasure M (\<Union>i. f i) \<le> (\<Sum>i. emeasure M (f i))"
proof -
  have "emeasure M (\<Union>i. f i) = emeasure M (\<Union>i. disjointed f i)"
    unfolding UN_disjointed_eq ..
  also have "\<dots> = (\<Sum>i. emeasure M (disjointed f i))"
    using sets.range_disjointed_sets[OF assms] suminf_emeasure[of "disjointed f"]
    by (simp add:  disjoint_family_disjointed comp_def)
  also have "\<dots> \<le> (\<Sum>i. emeasure M (f i))"
    using sets.range_disjointed_sets[OF assms] assms
    by (auto intro!: suminf_le emeasure_mono disjointed_subset)
  finally show ?thesis .
qed

lemma emeasure_insert:
  assumes sets: "{x} \<in> sets M" "A \<in> sets M" and "x \<notin> A"
  shows "emeasure M (insert x A) = emeasure M {x} + emeasure M A"
proof -
  have "{x} \<inter> A = {}" using \<open>x \<notin> A\<close> by auto
  from plus_emeasure[OF sets this] show ?thesis by simp
qed

lemma emeasure_insert_ne:
  "A \<noteq> {} \<Longrightarrow> {x} \<in> sets M \<Longrightarrow> A \<in> sets M \<Longrightarrow> x \<notin> A \<Longrightarrow> emeasure M (insert x A) = emeasure M {x} + emeasure M A"
  by (rule emeasure_insert)

lemma emeasure_eq_setsum_singleton:
  assumes "finite S" "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  shows "emeasure M S = (\<Sum>x\<in>S. emeasure M {x})"
  using setsum_emeasure[of "\<lambda>x. {x}" S M] assms
  by (auto simp: disjoint_family_on_def subset_eq)

lemma setsum_emeasure_cover:
  assumes "finite S" and "A \<in> sets M" and br_in_M: "B ` S \<subseteq> sets M"
  assumes A: "A \<subseteq> (\<Union>i\<in>S. B i)"
  assumes disj: "disjoint_family_on B S"
  shows "emeasure M A = (\<Sum>i\<in>S. emeasure M (A \<inter> (B i)))"
proof -
  have "(\<Sum>i\<in>S. emeasure M (A \<inter> (B i))) = emeasure M (\<Union>i\<in>S. A \<inter> (B i))"
  proof (rule setsum_emeasure)
    show "disjoint_family_on (\<lambda>i. A \<inter> B i) S"
      using \<open>disjoint_family_on B S\<close>
      unfolding disjoint_family_on_def by auto
  qed (insert assms, auto)
  also have "(\<Union>i\<in>S. A \<inter> (B i)) = A"
    using A by auto
  finally show ?thesis by simp
qed

lemma emeasure_eq_0:
  "N \<in> sets M \<Longrightarrow> emeasure M N = 0 \<Longrightarrow> K \<subseteq> N \<Longrightarrow> emeasure M K = 0"
  by (metis emeasure_mono order_eq_iff zero_le)

lemma emeasure_UN_eq_0:
  assumes "\<And>i::nat. emeasure M (N i) = 0" and "range N \<subseteq> sets M"
  shows "emeasure M (\<Union>i. N i) = 0"
proof -
  have "emeasure M (\<Union>i. N i) \<le> 0"
    using emeasure_subadditive_countably[OF assms(2)] assms(1) by simp
  then show ?thesis
    by (auto intro: antisym zero_le)
qed

lemma measure_eqI_finite:
  assumes [simp]: "sets M = Pow A" "sets N = Pow A" and "finite A"
  assumes eq: "\<And>a. a \<in> A \<Longrightarrow> emeasure M {a} = emeasure N {a}"
  shows "M = N"
proof (rule measure_eqI)
  fix X assume "X \<in> sets M"
  then have X: "X \<subseteq> A" by auto
  then have "emeasure M X = (\<Sum>a\<in>X. emeasure M {a})"
    using \<open>finite A\<close> by (subst emeasure_eq_setsum_singleton) (auto dest: finite_subset)
  also have "\<dots> = (\<Sum>a\<in>X. emeasure N {a})"
    using X eq by (auto intro!: setsum.cong)
  also have "\<dots> = emeasure N X"
    using X \<open>finite A\<close> by (subst emeasure_eq_setsum_singleton) (auto dest: finite_subset)
  finally show "emeasure M X = emeasure N X" .
qed simp

lemma measure_eqI_generator_eq:
  fixes M N :: "'a measure" and E :: "'a set set" and A :: "nat \<Rightarrow> 'a set"
  assumes "Int_stable E" "E \<subseteq> Pow \<Omega>"
  and eq: "\<And>X. X \<in> E \<Longrightarrow> emeasure M X = emeasure N X"
  and M: "sets M = sigma_sets \<Omega> E"
  and N: "sets N = sigma_sets \<Omega> E"
  and A: "range A \<subseteq> E" "(\<Union>i. A i) = \<Omega>" "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
  shows "M = N"
proof -
  let ?\<mu>  = "emeasure M" and ?\<nu> = "emeasure N"
  interpret S: sigma_algebra \<Omega> "sigma_sets \<Omega> E" by (rule sigma_algebra_sigma_sets) fact
  have "space M = \<Omega>"
    using sets.top[of M] sets.space_closed[of M] S.top S.space_closed \<open>sets M = sigma_sets \<Omega> E\<close>
    by blast

  { fix F D assume "F \<in> E" and "?\<mu> F \<noteq> \<infinity>"
    then have [intro]: "F \<in> sigma_sets \<Omega> E" by auto
    have "?\<nu> F \<noteq> \<infinity>" using \<open>?\<mu> F \<noteq> \<infinity>\<close> \<open>F \<in> E\<close> eq by simp
    assume "D \<in> sets M"
    with \<open>Int_stable E\<close> \<open>E \<subseteq> Pow \<Omega>\<close> have "emeasure M (F \<inter> D) = emeasure N (F \<inter> D)"
      unfolding M
    proof (induct rule: sigma_sets_induct_disjoint)
      case (basic A)
      then have "F \<inter> A \<in> E" using \<open>Int_stable E\<close> \<open>F \<in> E\<close> by (auto simp: Int_stable_def)
      then show ?case using eq by auto
    next
      case empty then show ?case by simp
    next
      case (compl A)
      then have **: "F \<inter> (\<Omega> - A) = F - (F \<inter> A)"
        and [intro]: "F \<inter> A \<in> sigma_sets \<Omega> E"
        using \<open>F \<in> E\<close> S.sets_into_space by (auto simp: M)
      have "?\<nu> (F \<inter> A) \<le> ?\<nu> F" by (auto intro!: emeasure_mono simp: M N)
      then have "?\<nu> (F \<inter> A) \<noteq> \<infinity>" using \<open>?\<nu> F \<noteq> \<infinity>\<close> by (auto simp: top_unique)
      have "?\<mu> (F \<inter> A) \<le> ?\<mu> F" by (auto intro!: emeasure_mono simp: M N)
      then have "?\<mu> (F \<inter> A) \<noteq> \<infinity>" using \<open>?\<mu> F \<noteq> \<infinity>\<close> by (auto simp: top_unique)
      then have "?\<mu> (F \<inter> (\<Omega> - A)) = ?\<mu> F - ?\<mu> (F \<inter> A)" unfolding **
        using \<open>F \<inter> A \<in> sigma_sets \<Omega> E\<close> by (auto intro!: emeasure_Diff simp: M N)
      also have "\<dots> = ?\<nu> F - ?\<nu> (F \<inter> A)" using eq \<open>F \<in> E\<close> compl by simp
      also have "\<dots> = ?\<nu> (F \<inter> (\<Omega> - A))" unfolding **
        using \<open>F \<inter> A \<in> sigma_sets \<Omega> E\<close> \<open>?\<nu> (F \<inter> A) \<noteq> \<infinity>\<close>
        by (auto intro!: emeasure_Diff[symmetric] simp: M N)
      finally show ?case
        using \<open>space M = \<Omega>\<close> by auto
    next
      case (union A)
      then have "?\<mu> (\<Union>x. F \<inter> A x) = ?\<nu> (\<Union>x. F \<inter> A x)"
        by (subst (1 2) suminf_emeasure[symmetric]) (auto simp: disjoint_family_on_def subset_eq M N)
      with A show ?case
        by auto
    qed }
  note * = this
  show "M = N"
  proof (rule measure_eqI)
    show "sets M = sets N"
      using M N by simp
    have [simp, intro]: "\<And>i. A i \<in> sets M"
      using A(1) by (auto simp: subset_eq M)
    fix F assume "F \<in> sets M"
    let ?D = "disjointed (\<lambda>i. F \<inter> A i)"
    from \<open>space M = \<Omega>\<close> have F_eq: "F = (\<Union>i. ?D i)"
      using \<open>F \<in> sets M\<close>[THEN sets.sets_into_space] A(2)[symmetric] by (auto simp: UN_disjointed_eq)
    have [simp, intro]: "\<And>i. ?D i \<in> sets M"
      using sets.range_disjointed_sets[of "\<lambda>i. F \<inter> A i" M] \<open>F \<in> sets M\<close>
      by (auto simp: subset_eq)
    have "disjoint_family ?D"
      by (auto simp: disjoint_family_disjointed)
    moreover
    have "(\<Sum>i. emeasure M (?D i)) = (\<Sum>i. emeasure N (?D i))"
    proof (intro arg_cong[where f=suminf] ext)
      fix i
      have "A i \<inter> ?D i = ?D i"
        by (auto simp: disjointed_def)
      then show "emeasure M (?D i) = emeasure N (?D i)"
        using *[of "A i" "?D i", OF _ A(3)] A(1) by auto
    qed
    ultimately show "emeasure M F = emeasure N F"
      by (simp add: image_subset_iff \<open>sets M = sets N\<close>[symmetric] F_eq[symmetric] suminf_emeasure)
  qed
qed

lemma measure_of_of_measure: "measure_of (space M) (sets M) (emeasure M) = M"
proof (intro measure_eqI emeasure_measure_of_sigma)
  show "sigma_algebra (space M) (sets M)" ..
  show "positive (sets M) (emeasure M)"
    by (simp add: positive_def)
  show "countably_additive (sets M) (emeasure M)"
    by (simp add: emeasure_countably_additive)
qed simp_all

subsection \<open>\<open>\<mu>\<close>-null sets\<close>

definition null_sets :: "'a measure \<Rightarrow> 'a set set" where
  "null_sets M = {N\<in>sets M. emeasure M N = 0}"

lemma null_setsD1[dest]: "A \<in> null_sets M \<Longrightarrow> emeasure M A = 0"
  by (simp add: null_sets_def)

lemma null_setsD2[dest]: "A \<in> null_sets M \<Longrightarrow> A \<in> sets M"
  unfolding null_sets_def by simp

lemma null_setsI[intro]: "emeasure M A = 0 \<Longrightarrow> A \<in> sets M \<Longrightarrow> A \<in> null_sets M"
  unfolding null_sets_def by simp

interpretation null_sets: ring_of_sets "space M" "null_sets M" for M
proof (rule ring_of_setsI)
  show "null_sets M \<subseteq> Pow (space M)"
    using sets.sets_into_space by auto
  show "{} \<in> null_sets M"
    by auto
  fix A B assume null_sets: "A \<in> null_sets M" "B \<in> null_sets M"
  then have sets: "A \<in> sets M" "B \<in> sets M"
    by auto
  then have *: "emeasure M (A \<union> B) \<le> emeasure M A + emeasure M B"
    "emeasure M (A - B) \<le> emeasure M A"
    by (auto intro!: emeasure_subadditive emeasure_mono)
  then have "emeasure M B = 0" "emeasure M A = 0"
    using null_sets by auto
  with sets * show "A - B \<in> null_sets M" "A \<union> B \<in> null_sets M"
    by (auto intro!: antisym zero_le)
qed

lemma UN_from_nat_into:
  assumes I: "countable I" "I \<noteq> {}"
  shows "(\<Union>i\<in>I. N i) = (\<Union>i. N (from_nat_into I i))"
proof -
  have "(\<Union>i\<in>I. N i) = \<Union>(N ` range (from_nat_into I))"
    using I by simp
  also have "\<dots> = (\<Union>i. (N \<circ> from_nat_into I) i)"
    by simp
  finally show ?thesis by simp
qed

lemma null_sets_UN':
  assumes "countable I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> N i \<in> null_sets M"
  shows "(\<Union>i\<in>I. N i) \<in> null_sets M"
proof cases
  assume "I = {}" then show ?thesis by simp
next
  assume "I \<noteq> {}"
  show ?thesis
  proof (intro conjI CollectI null_setsI)
    show "(\<Union>i\<in>I. N i) \<in> sets M"
      using assms by (intro sets.countable_UN') auto
    have "emeasure M (\<Union>i\<in>I. N i) \<le> (\<Sum>n. emeasure M (N (from_nat_into I n)))"
      unfolding UN_from_nat_into[OF \<open>countable I\<close> \<open>I \<noteq> {}\<close>]
      using assms \<open>I \<noteq> {}\<close> by (intro emeasure_subadditive_countably) (auto intro: from_nat_into)
    also have "(\<lambda>n. emeasure M (N (from_nat_into I n))) = (\<lambda>_. 0)"
      using assms \<open>I \<noteq> {}\<close> by (auto intro: from_nat_into)
    finally show "emeasure M (\<Union>i\<in>I. N i) = 0"
      by (intro antisym zero_le) simp
  qed
qed

lemma null_sets_UN[intro]:
  "(\<And>i::'i::countable. N i \<in> null_sets M) \<Longrightarrow> (\<Union>i. N i) \<in> null_sets M"
  by (rule null_sets_UN') auto

lemma null_set_Int1:
  assumes "B \<in> null_sets M" "A \<in> sets M" shows "A \<inter> B \<in> null_sets M"
proof (intro CollectI conjI null_setsI)
  show "emeasure M (A \<inter> B) = 0" using assms
    by (intro emeasure_eq_0[of B _ "A \<inter> B"]) auto
qed (insert assms, auto)

lemma null_set_Int2:
  assumes "B \<in> null_sets M" "A \<in> sets M" shows "B \<inter> A \<in> null_sets M"
  using assms by (subst Int_commute) (rule null_set_Int1)

lemma emeasure_Diff_null_set:
  assumes "B \<in> null_sets M" "A \<in> sets M"
  shows "emeasure M (A - B) = emeasure M A"
proof -
  have *: "A - B = (A - (A \<inter> B))" by auto
  have "A \<inter> B \<in> null_sets M" using assms by (rule null_set_Int1)
  then show ?thesis
    unfolding * using assms
    by (subst emeasure_Diff) auto
qed

lemma null_set_Diff:
  assumes "B \<in> null_sets M" "A \<in> sets M" shows "B - A \<in> null_sets M"
proof (intro CollectI conjI null_setsI)
  show "emeasure M (B - A) = 0" using assms by (intro emeasure_eq_0[of B _ "B - A"]) auto
qed (insert assms, auto)

lemma emeasure_Un_null_set:
  assumes "A \<in> sets M" "B \<in> null_sets M"
  shows "emeasure M (A \<union> B) = emeasure M A"
proof -
  have *: "A \<union> B = A \<union> (B - A)" by auto
  have "B - A \<in> null_sets M" using assms(2,1) by (rule null_set_Diff)
  then show ?thesis
    unfolding * using assms
    by (subst plus_emeasure[symmetric]) auto
qed

subsection \<open>The almost everywhere filter (i.e.\ quantifier)\<close>

definition ae_filter :: "'a measure \<Rightarrow> 'a filter" where
  "ae_filter M = (INF N:null_sets M. principal (space M - N))"

abbreviation almost_everywhere :: "'a measure \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "almost_everywhere M P \<equiv> eventually P (ae_filter M)"

syntax
  "_almost_everywhere" :: "pttrn \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool" ("AE _ in _. _" [0,0,10] 10)

translations
  "AE x in M. P" \<rightleftharpoons> "CONST almost_everywhere M (\<lambda>x. P)"

lemma eventually_ae_filter: "eventually P (ae_filter M) \<longleftrightarrow> (\<exists>N\<in>null_sets M. {x \<in> space M. \<not> P x} \<subseteq> N)"
  unfolding ae_filter_def by (subst eventually_INF_base) (auto simp: eventually_principal subset_eq)

lemma AE_I':
  "N \<in> null_sets M \<Longrightarrow> {x\<in>space M. \<not> P x} \<subseteq> N \<Longrightarrow> (AE x in M. P x)"
  unfolding eventually_ae_filter by auto

lemma AE_iff_null:
  assumes "{x\<in>space M. \<not> P x} \<in> sets M" (is "?P \<in> sets M")
  shows "(AE x in M. P x) \<longleftrightarrow> {x\<in>space M. \<not> P x} \<in> null_sets M"
proof
  assume "AE x in M. P x" then obtain N where N: "N \<in> sets M" "?P \<subseteq> N" "emeasure M N = 0"
    unfolding eventually_ae_filter by auto
  have "emeasure M ?P \<le> emeasure M N"
    using assms N(1,2) by (auto intro: emeasure_mono)
  then have "emeasure M ?P = 0"
    unfolding \<open>emeasure M N = 0\<close> by auto
  then show "?P \<in> null_sets M" using assms by auto
next
  assume "?P \<in> null_sets M" with assms show "AE x in M. P x" by (auto intro: AE_I')
qed

lemma AE_iff_null_sets:
  "N \<in> sets M \<Longrightarrow> N \<in> null_sets M \<longleftrightarrow> (AE x in M. x \<notin> N)"
  using Int_absorb1[OF sets.sets_into_space, of N M]
  by (subst AE_iff_null) (auto simp: Int_def[symmetric])

lemma AE_not_in:
  "N \<in> null_sets M \<Longrightarrow> AE x in M. x \<notin> N"
  by (metis AE_iff_null_sets null_setsD2)

lemma AE_iff_measurable:
  "N \<in> sets M \<Longrightarrow> {x\<in>space M. \<not> P x} = N \<Longrightarrow> (AE x in M. P x) \<longleftrightarrow> emeasure M N = 0"
  using AE_iff_null[of _ P] by auto

lemma AE_E[consumes 1]:
  assumes "AE x in M. P x"
  obtains N where "{x \<in> space M. \<not> P x} \<subseteq> N" "emeasure M N = 0" "N \<in> sets M"
  using assms unfolding eventually_ae_filter by auto

lemma AE_E2:
  assumes "AE x in M. P x" "{x\<in>space M. P x} \<in> sets M"
  shows "emeasure M {x\<in>space M. \<not> P x} = 0" (is "emeasure M ?P = 0")
proof -
  have "{x\<in>space M. \<not> P x} = space M - {x\<in>space M. P x}" by auto
  with AE_iff_null[of M P] assms show ?thesis by auto
qed

lemma AE_I:
  assumes "{x \<in> space M. \<not> P x} \<subseteq> N" "emeasure M N = 0" "N \<in> sets M"
  shows "AE x in M. P x"
  using assms unfolding eventually_ae_filter by auto

lemma AE_mp[elim!]:
  assumes AE_P: "AE x in M. P x" and AE_imp: "AE x in M. P x \<longrightarrow> Q x"
  shows "AE x in M. Q x"
proof -
  from AE_P obtain A where P: "{x\<in>space M. \<not> P x} \<subseteq> A"
    and A: "A \<in> sets M" "emeasure M A = 0"
    by (auto elim!: AE_E)

  from AE_imp obtain B where imp: "{x\<in>space M. P x \<and> \<not> Q x} \<subseteq> B"
    and B: "B \<in> sets M" "emeasure M B = 0"
    by (auto elim!: AE_E)

  show ?thesis
  proof (intro AE_I)
    have "emeasure M (A \<union> B) \<le> 0"
      using emeasure_subadditive[of A M B] A B by auto
    then show "A \<union> B \<in> sets M" "emeasure M (A \<union> B) = 0"
      using A B by auto
    show "{x\<in>space M. \<not> Q x} \<subseteq> A \<union> B"
      using P imp by auto
  qed
qed

(* depricated replace by laws about eventually *)
lemma
  shows AE_iffI: "AE x in M. P x \<Longrightarrow> AE x in M. P x \<longleftrightarrow> Q x \<Longrightarrow> AE x in M. Q x"
    and AE_disjI1: "AE x in M. P x \<Longrightarrow> AE x in M. P x \<or> Q x"
    and AE_disjI2: "AE x in M. Q x \<Longrightarrow> AE x in M. P x \<or> Q x"
    and AE_conjI: "AE x in M. P x \<Longrightarrow> AE x in M. Q x \<Longrightarrow> AE x in M. P x \<and> Q x"
    and AE_conj_iff[simp]: "(AE x in M. P x \<and> Q x) \<longleftrightarrow> (AE x in M. P x) \<and> (AE x in M. Q x)"
  by auto

lemma AE_impI:
  "(P \<Longrightarrow> AE x in M. Q x) \<Longrightarrow> AE x in M. P \<longrightarrow> Q x"
  by (cases P) auto

lemma AE_measure:
  assumes AE: "AE x in M. P x" and sets: "{x\<in>space M. P x} \<in> sets M" (is "?P \<in> sets M")
  shows "emeasure M {x\<in>space M. P x} = emeasure M (space M)"
proof -
  from AE_E[OF AE] guess N . note N = this
  with sets have "emeasure M (space M) \<le> emeasure M (?P \<union> N)"
    by (intro emeasure_mono) auto
  also have "\<dots> \<le> emeasure M ?P + emeasure M N"
    using sets N by (intro emeasure_subadditive) auto
  also have "\<dots> = emeasure M ?P" using N by simp
  finally show "emeasure M ?P = emeasure M (space M)"
    using emeasure_space[of M "?P"] by auto
qed

lemma AE_space: "AE x in M. x \<in> space M"
  by (rule AE_I[where N="{}"]) auto

lemma AE_I2[simp, intro]:
  "(\<And>x. x \<in> space M \<Longrightarrow> P x) \<Longrightarrow> AE x in M. P x"
  using AE_space by force

lemma AE_Ball_mp:
  "\<forall>x\<in>space M. P x \<Longrightarrow> AE x in M. P x \<longrightarrow> Q x \<Longrightarrow> AE x in M. Q x"
  by auto

lemma AE_cong[cong]:
  "(\<And>x. x \<in> space M \<Longrightarrow> P x \<longleftrightarrow> Q x) \<Longrightarrow> (AE x in M. P x) \<longleftrightarrow> (AE x in M. Q x)"
  by auto

lemma AE_all_countable:
  "(AE x in M. \<forall>i. P i x) \<longleftrightarrow> (\<forall>i::'i::countable. AE x in M. P i x)"
proof
  assume "\<forall>i. AE x in M. P i x"
  from this[unfolded eventually_ae_filter Bex_def, THEN choice]
  obtain N where N: "\<And>i. N i \<in> null_sets M" "\<And>i. {x\<in>space M. \<not> P i x} \<subseteq> N i" by auto
  have "{x\<in>space M. \<not> (\<forall>i. P i x)} \<subseteq> (\<Union>i. {x\<in>space M. \<not> P i x})" by auto
  also have "\<dots> \<subseteq> (\<Union>i. N i)" using N by auto
  finally have "{x\<in>space M. \<not> (\<forall>i. P i x)} \<subseteq> (\<Union>i. N i)" .
  moreover from N have "(\<Union>i. N i) \<in> null_sets M"
    by (intro null_sets_UN) auto
  ultimately show "AE x in M. \<forall>i. P i x"
    unfolding eventually_ae_filter by auto
qed auto

lemma AE_ball_countable:
  assumes [intro]: "countable X"
  shows "(AE x in M. \<forall>y\<in>X. P x y) \<longleftrightarrow> (\<forall>y\<in>X. AE x in M. P x y)"
proof
  assume "\<forall>y\<in>X. AE x in M. P x y"
  from this[unfolded eventually_ae_filter Bex_def, THEN bchoice]
  obtain N where N: "\<And>y. y \<in> X \<Longrightarrow> N y \<in> null_sets M" "\<And>y. y \<in> X \<Longrightarrow> {x\<in>space M. \<not> P x y} \<subseteq> N y"
    by auto
  have "{x\<in>space M. \<not> (\<forall>y\<in>X. P x y)} \<subseteq> (\<Union>y\<in>X. {x\<in>space M. \<not> P x y})"
    by auto
  also have "\<dots> \<subseteq> (\<Union>y\<in>X. N y)"
    using N by auto
  finally have "{x\<in>space M. \<not> (\<forall>y\<in>X. P x y)} \<subseteq> (\<Union>y\<in>X. N y)" .
  moreover from N have "(\<Union>y\<in>X. N y) \<in> null_sets M"
    by (intro null_sets_UN') auto
  ultimately show "AE x in M. \<forall>y\<in>X. P x y"
    unfolding eventually_ae_filter by auto
qed auto

lemma AE_discrete_difference:
  assumes X: "countable X"
  assumes null: "\<And>x. x \<in> X \<Longrightarrow> emeasure M {x} = 0"
  assumes sets: "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M"
  shows "AE x in M. x \<notin> X"
proof -
  have "(\<Union>x\<in>X. {x}) \<in> null_sets M"
    using assms by (intro null_sets_UN') auto
  from AE_not_in[OF this] show "AE x in M. x \<notin> X"
    by auto
qed

lemma AE_finite_all:
  assumes f: "finite S" shows "(AE x in M. \<forall>i\<in>S. P i x) \<longleftrightarrow> (\<forall>i\<in>S. AE x in M. P i x)"
  using f by induct auto

lemma AE_finite_allI:
  assumes "finite S"
  shows "(\<And>s. s \<in> S \<Longrightarrow> AE x in M. Q s x) \<Longrightarrow> AE x in M. \<forall>s\<in>S. Q s x"
  using AE_finite_all[OF \<open>finite S\<close>] by auto

lemma emeasure_mono_AE:
  assumes imp: "AE x in M. x \<in> A \<longrightarrow> x \<in> B"
    and B: "B \<in> sets M"
  shows "emeasure M A \<le> emeasure M B"
proof cases
  assume A: "A \<in> sets M"
  from imp obtain N where N: "{x\<in>space M. \<not> (x \<in> A \<longrightarrow> x \<in> B)} \<subseteq> N" "N \<in> null_sets M"
    by (auto simp: eventually_ae_filter)
  have "emeasure M A = emeasure M (A - N)"
    using N A by (subst emeasure_Diff_null_set) auto
  also have "emeasure M (A - N) \<le> emeasure M (B - N)"
    using N A B sets.sets_into_space by (auto intro!: emeasure_mono)
  also have "emeasure M (B - N) = emeasure M B"
    using N B by (subst emeasure_Diff_null_set) auto
  finally show ?thesis .
qed (simp add: emeasure_notin_sets)

lemma emeasure_eq_AE:
  assumes iff: "AE x in M. x \<in> A \<longleftrightarrow> x \<in> B"
  assumes A: "A \<in> sets M" and B: "B \<in> sets M"
  shows "emeasure M A = emeasure M B"
  using assms by (safe intro!: antisym emeasure_mono_AE) auto

lemma emeasure_Collect_eq_AE:
  "AE x in M. P x \<longleftrightarrow> Q x \<Longrightarrow> Measurable.pred M Q \<Longrightarrow> Measurable.pred M P \<Longrightarrow>
   emeasure M {x\<in>space M. P x} = emeasure M {x\<in>space M. Q x}"
   by (intro emeasure_eq_AE) auto

lemma emeasure_eq_0_AE: "AE x in M. \<not> P x \<Longrightarrow> emeasure M {x\<in>space M. P x} = 0"
  using AE_iff_measurable[OF _ refl, of M "\<lambda>x. \<not> P x"]
  by (cases "{x\<in>space M. P x} \<in> sets M") (simp_all add: emeasure_notin_sets)

lemma emeasure_add_AE:
  assumes [measurable]: "A \<in> sets M" "B \<in> sets M" "C \<in> sets M"
  assumes 1: "AE x in M. x \<in> C \<longleftrightarrow> x \<in> A \<or> x \<in> B"
  assumes 2: "AE x in M. \<not> (x \<in> A \<and> x \<in> B)"
  shows "emeasure M C = emeasure M A + emeasure M B"
proof -
  have "emeasure M C = emeasure M (A \<union> B)"
    by (rule emeasure_eq_AE) (insert 1, auto)
  also have "\<dots> = emeasure M A + emeasure M (B - A)"
    by (subst plus_emeasure) auto
  also have "emeasure M (B - A) = emeasure M B"
    by (rule emeasure_eq_AE) (insert 2, auto)
  finally show ?thesis .
qed

subsection \<open>\<open>\<sigma>\<close>-finite Measures\<close>

locale sigma_finite_measure =
  fixes M :: "'a measure"
  assumes sigma_finite_countable:
    "\<exists>A::'a set set. countable A \<and> A \<subseteq> sets M \<and> (\<Union>A) = space M \<and> (\<forall>a\<in>A. emeasure M a \<noteq> \<infinity>)"

lemma (in sigma_finite_measure) sigma_finite:
  obtains A :: "nat \<Rightarrow> 'a set"
  where "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
proof -
  obtain A :: "'a set set" where
    [simp]: "countable A" and
    A: "A \<subseteq> sets M" "(\<Union>A) = space M" "\<And>a. a \<in> A \<Longrightarrow> emeasure M a \<noteq> \<infinity>"
    using sigma_finite_countable by metis
  show thesis
  proof cases
    assume "A = {}" with \<open>(\<Union>A) = space M\<close> show thesis
      by (intro that[of "\<lambda>_. {}"]) auto
  next
    assume "A \<noteq> {}"
    show thesis
    proof
      show "range (from_nat_into A) \<subseteq> sets M"
        using \<open>A \<noteq> {}\<close> A by auto
      have "(\<Union>i. from_nat_into A i) = \<Union>A"
        using range_from_nat_into[OF \<open>A \<noteq> {}\<close> \<open>countable A\<close>] by auto
      with A show "(\<Union>i. from_nat_into A i) = space M"
        by auto
    qed (intro A from_nat_into \<open>A \<noteq> {}\<close>)
  qed
qed

lemma (in sigma_finite_measure) sigma_finite_disjoint:
  obtains A :: "nat \<Rightarrow> 'a set"
  where "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" "\<And>i. emeasure M (A i) \<noteq> \<infinity>" "disjoint_family A"
proof -
  obtain A :: "nat \<Rightarrow> 'a set" where
    range: "range A \<subseteq> sets M" and
    space: "(\<Union>i. A i) = space M" and
    measure: "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
    using sigma_finite by blast
  show thesis
  proof (rule that[of "disjointed A"])
    show "range (disjointed A) \<subseteq> sets M"
      by (rule sets.range_disjointed_sets[OF range])
    show "(\<Union>i. disjointed A i) = space M"
      and "disjoint_family (disjointed A)"
      using disjoint_family_disjointed UN_disjointed_eq[of A] space range
      by auto
    show "emeasure M (disjointed A i) \<noteq> \<infinity>" for i
    proof -
      have "emeasure M (disjointed A i) \<le> emeasure M (A i)"
        using range disjointed_subset[of A i] by (auto intro!: emeasure_mono)
      then show ?thesis using measure[of i] by (auto simp: top_unique)
    qed
  qed
qed

lemma (in sigma_finite_measure) sigma_finite_incseq:
  obtains A :: "nat \<Rightarrow> 'a set"
  where "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" "\<And>i. emeasure M (A i) \<noteq> \<infinity>" "incseq A"
proof -
  obtain F :: "nat \<Rightarrow> 'a set" where
    F: "range F \<subseteq> sets M" "(\<Union>i. F i) = space M" "\<And>i. emeasure M (F i) \<noteq> \<infinity>"
    using sigma_finite by blast
  show thesis
  proof (rule that[of "\<lambda>n. \<Union>i\<le>n. F i"])
    show "range (\<lambda>n. \<Union>i\<le>n. F i) \<subseteq> sets M"
      using F by (force simp: incseq_def)
    show "(\<Union>n. \<Union>i\<le>n. F i) = space M"
    proof -
      from F have "\<And>x. x \<in> space M \<Longrightarrow> \<exists>i. x \<in> F i" by auto
      with F show ?thesis by fastforce
    qed
    show "emeasure M (\<Union>i\<le>n. F i) \<noteq> \<infinity>" for n
    proof -
      have "emeasure M (\<Union>i\<le>n. F i) \<le> (\<Sum>i\<le>n. emeasure M (F i))"
        using F by (auto intro!: emeasure_subadditive_finite)
      also have "\<dots> < \<infinity>"
        using F by (auto simp: setsum_Pinfty less_top)
      finally show ?thesis by simp
    qed
    show "incseq (\<lambda>n. \<Union>i\<le>n. F i)"
      by (force simp: incseq_def)
  qed
qed

subsection \<open>Measure space induced by distribution of @{const measurable}-functions\<close>

definition distr :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b measure" where
  "distr M N f = measure_of (space N) (sets N) (\<lambda>A. emeasure M (f -` A \<inter> space M))"

lemma
  shows sets_distr[simp, measurable_cong]: "sets (distr M N f) = sets N"
    and space_distr[simp]: "space (distr M N f) = space N"
  by (auto simp: distr_def)

lemma
  shows measurable_distr_eq1[simp]: "measurable (distr Mf Nf f) Mf' = measurable Nf Mf'"
    and measurable_distr_eq2[simp]: "measurable Mg' (distr Mg Ng g) = measurable Mg' Ng"
  by (auto simp: measurable_def)

lemma distr_cong:
  "M = K \<Longrightarrow> sets N = sets L \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> distr M N f = distr K L g"
  using sets_eq_imp_space_eq[of N L] by (simp add: distr_def Int_def cong: rev_conj_cong)

lemma emeasure_distr:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes f: "f \<in> measurable M N" and A: "A \<in> sets N"
  shows "emeasure (distr M N f) A = emeasure M (f -` A \<inter> space M)" (is "_ = ?\<mu> A")
  unfolding distr_def
proof (rule emeasure_measure_of_sigma)
  show "positive (sets N) ?\<mu>"
    by (auto simp: positive_def)

  show "countably_additive (sets N) ?\<mu>"
  proof (intro countably_additiveI)
    fix A :: "nat \<Rightarrow> 'b set" assume "range A \<subseteq> sets N" "disjoint_family A"
    then have A: "\<And>i. A i \<in> sets N" "(\<Union>i. A i) \<in> sets N" by auto
    then have *: "range (\<lambda>i. f -` (A i) \<inter> space M) \<subseteq> sets M"
      using f by (auto simp: measurable_def)
    moreover have "(\<Union>i. f -`  A i \<inter> space M) \<in> sets M"
      using * by blast
    moreover have **: "disjoint_family (\<lambda>i. f -` A i \<inter> space M)"
      using \<open>disjoint_family A\<close> by (auto simp: disjoint_family_on_def)
    ultimately show "(\<Sum>i. ?\<mu> (A i)) = ?\<mu> (\<Union>i. A i)"
      using suminf_emeasure[OF _ **] A f
      by (auto simp: comp_def vimage_UN)
  qed
  show "sigma_algebra (space N) (sets N)" ..
qed fact

lemma emeasure_Collect_distr:
  assumes X[measurable]: "X \<in> measurable M N" "Measurable.pred N P"
  shows "emeasure (distr M N X) {x\<in>space N. P x} = emeasure M {x\<in>space M. P (X x)}"
  by (subst emeasure_distr)
     (auto intro!: arg_cong2[where f=emeasure] X(1)[THEN measurable_space])

lemma emeasure_lfp2[consumes 1, case_names cont f measurable]:
  assumes "P M"
  assumes cont: "sup_continuous F"
  assumes f: "\<And>M. P M \<Longrightarrow> f \<in> measurable M' M"
  assumes *: "\<And>M A. P M \<Longrightarrow> (\<And>N. P N \<Longrightarrow> Measurable.pred N A) \<Longrightarrow> Measurable.pred M (F A)"
  shows "emeasure M' {x\<in>space M'. lfp F (f x)} = (SUP i. emeasure M' {x\<in>space M'. (F ^^ i) (\<lambda>x. False) (f x)})"
proof (subst (1 2) emeasure_Collect_distr[symmetric, where X=f])
  show "f \<in> measurable M' M"  "f \<in> measurable M' M"
    using f[OF \<open>P M\<close>] by auto
  { fix i show "Measurable.pred M ((F ^^ i) (\<lambda>x. False))"
    using \<open>P M\<close> by (induction i arbitrary: M) (auto intro!: *) }
  show "Measurable.pred M (lfp F)"
    using \<open>P M\<close> cont * by (rule measurable_lfp_coinduct[of P])

  have "emeasure (distr M' M f) {x \<in> space (distr M' M f). lfp F x} =
    (SUP i. emeasure (distr M' M f) {x \<in> space (distr M' M f). (F ^^ i) (\<lambda>x. False) x})"
    using \<open>P M\<close>
  proof (coinduction arbitrary: M rule: emeasure_lfp')
    case (measurable A N) then have "\<And>N. P N \<Longrightarrow> Measurable.pred (distr M' N f) A"
      by metis
    then have "\<And>N. P N \<Longrightarrow> Measurable.pred N A"
      by simp
    with \<open>P N\<close>[THEN *] show ?case
      by auto
  qed fact
  then show "emeasure (distr M' M f) {x \<in> space M. lfp F x} =
    (SUP i. emeasure (distr M' M f) {x \<in> space M. (F ^^ i) (\<lambda>x. False) x})"
   by simp
qed

lemma distr_id[simp]: "distr N N (\<lambda>x. x) = N"
  by (rule measure_eqI) (auto simp: emeasure_distr)

lemma measure_distr:
  "f \<in> measurable M N \<Longrightarrow> S \<in> sets N \<Longrightarrow> measure (distr M N f) S = measure M (f -` S \<inter> space M)"
  by (simp add: emeasure_distr measure_def)

lemma distr_cong_AE:
  assumes 1: "M = K" "sets N = sets L" and
    2: "(AE x in M. f x = g x)" and "f \<in> measurable M N" and "g \<in> measurable K L"
  shows "distr M N f = distr K L g"
proof (rule measure_eqI)
  fix A assume "A \<in> sets (distr M N f)"
  with assms show "emeasure (distr M N f) A = emeasure (distr K L g) A"
    by (auto simp add: emeasure_distr intro!: emeasure_eq_AE measurable_sets)
qed (insert 1, simp)

lemma AE_distrD:
  assumes f: "f \<in> measurable M M'"
    and AE: "AE x in distr M M' f. P x"
  shows "AE x in M. P (f x)"
proof -
  from AE[THEN AE_E] guess N .
  with f show ?thesis
    unfolding eventually_ae_filter
    by (intro bexI[of _ "f -` N \<inter> space M"])
       (auto simp: emeasure_distr measurable_def)
qed

lemma AE_distr_iff:
  assumes f[measurable]: "f \<in> measurable M N" and P[measurable]: "{x \<in> space N. P x} \<in> sets N"
  shows "(AE x in distr M N f. P x) \<longleftrightarrow> (AE x in M. P (f x))"
proof (subst (1 2) AE_iff_measurable[OF _ refl])
  have "f -` {x\<in>space N. \<not> P x} \<inter> space M = {x \<in> space M. \<not> P (f x)}"
    using f[THEN measurable_space] by auto
  then show "(emeasure (distr M N f) {x \<in> space (distr M N f). \<not> P x} = 0) =
    (emeasure M {x \<in> space M. \<not> P (f x)} = 0)"
    by (simp add: emeasure_distr)
qed auto

lemma null_sets_distr_iff:
  "f \<in> measurable M N \<Longrightarrow> A \<in> null_sets (distr M N f) \<longleftrightarrow> f -` A \<inter> space M \<in> null_sets M \<and> A \<in> sets N"
  by (auto simp add: null_sets_def emeasure_distr)

lemma distr_distr:
  "g \<in> measurable N L \<Longrightarrow> f \<in> measurable M N \<Longrightarrow> distr (distr M N f) L g = distr M L (g \<circ> f)"
  by (auto simp add: emeasure_distr measurable_space
           intro!: arg_cong[where f="emeasure M"] measure_eqI)

subsection \<open>Real measure values\<close>

lemma ring_of_finite_sets: "ring_of_sets (space M) {A\<in>sets M. emeasure M A \<noteq> top}"
proof (rule ring_of_setsI)
  show "a \<in> {A \<in> sets M. emeasure M A \<noteq> top} \<Longrightarrow> b \<in> {A \<in> sets M. emeasure M A \<noteq> top} \<Longrightarrow>
    a \<union> b \<in> {A \<in> sets M. emeasure M A \<noteq> top}" for a b
    using emeasure_subadditive[of a M b] by (auto simp: top_unique)

  show "a \<in> {A \<in> sets M. emeasure M A \<noteq> top} \<Longrightarrow> b \<in> {A \<in> sets M. emeasure M A \<noteq> top} \<Longrightarrow>
    a - b \<in> {A \<in> sets M. emeasure M A \<noteq> top}" for a b
    using emeasure_mono[of "a - b" a M] by (auto simp: Diff_subset top_unique)
qed (auto dest: sets.sets_into_space)

lemma measure_nonneg[simp]: "0 \<le> measure M A"
  unfolding measure_def by (auto simp: enn2real_nonneg)

lemma zero_less_measure_iff: "0 < measure M A \<longleftrightarrow> measure M A \<noteq> 0"
  using measure_nonneg[of M A] by (auto simp add: le_less)

lemma measure_le_0_iff: "measure M X \<le> 0 \<longleftrightarrow> measure M X = 0"
  using measure_nonneg[of M X] by linarith

lemma measure_empty[simp]: "measure M {} = 0"
  unfolding measure_def by (simp add: zero_ennreal.rep_eq)

lemma emeasure_eq_ennreal_measure:
  "emeasure M A \<noteq> top \<Longrightarrow> emeasure M A = ennreal (measure M A)"
  by (cases "emeasure M A" rule: ennreal_cases) (auto simp: measure_def)

lemma measure_zero_top: "emeasure M A = top \<Longrightarrow> measure M A = 0"
  by (simp add: measure_def enn2ereal_top)

lemma measure_eq_emeasure_eq_ennreal: "0 \<le> x \<Longrightarrow> emeasure M A = ennreal x \<Longrightarrow> measure M A = x"
  using emeasure_eq_ennreal_measure[of M A]
  by (cases "A \<in> M") (auto simp: measure_notin_sets emeasure_notin_sets)

lemma enn2real_plus:"a < top \<Longrightarrow> b < top \<Longrightarrow> enn2real (a + b) = enn2real a + enn2real b"
  by (simp add: enn2real_def plus_ennreal.rep_eq real_of_ereal_add enn2ereal_nonneg less_top
           del: real_of_ereal_enn2ereal)

lemma measure_Union:
  "emeasure M A \<noteq> \<infinity> \<Longrightarrow> emeasure M B \<noteq> \<infinity> \<Longrightarrow> A \<in> sets M \<Longrightarrow> B \<in> sets M \<Longrightarrow> A \<inter> B = {} \<Longrightarrow>
    measure M (A \<union> B) = measure M A + measure M B"
  by (simp add: measure_def enn2ereal_nonneg plus_emeasure[symmetric] enn2real_plus less_top)

lemma disjoint_family_on_insert:
  "i \<notin> I \<Longrightarrow> disjoint_family_on A (insert i I) \<longleftrightarrow> A i \<inter> (\<Union>i\<in>I. A i) = {} \<and> disjoint_family_on A I"
  by (fastforce simp: disjoint_family_on_def)

lemma measure_finite_Union:
  "finite S \<Longrightarrow> A`S \<subseteq> sets M \<Longrightarrow> disjoint_family_on A S \<Longrightarrow> (\<And>i. i \<in> S \<Longrightarrow> emeasure M (A i) \<noteq> \<infinity>) \<Longrightarrow>
    measure M (\<Union>i\<in>S. A i) = (\<Sum>i\<in>S. measure M (A i))"
  by (induction S rule: finite_induct)
     (auto simp: disjoint_family_on_insert measure_Union setsum_emeasure[symmetric] sets.countable_UN'[OF countable_finite])

lemma measure_Diff:
  assumes finite: "emeasure M A \<noteq> \<infinity>"
  and measurable: "A \<in> sets M" "B \<in> sets M" "B \<subseteq> A"
  shows "measure M (A - B) = measure M A - measure M B"
proof -
  have "emeasure M (A - B) \<le> emeasure M A" "emeasure M B \<le> emeasure M A"
    using measurable by (auto intro!: emeasure_mono)
  hence "measure M ((A - B) \<union> B) = measure M (A - B) + measure M B"
    using measurable finite by (rule_tac measure_Union) (auto simp: top_unique)
  thus ?thesis using \<open>B \<subseteq> A\<close> by (auto simp: Un_absorb2)
qed

lemma measure_UNION:
  assumes measurable: "range A \<subseteq> sets M" "disjoint_family A"
  assumes finite: "emeasure M (\<Union>i. A i) \<noteq> \<infinity>"
  shows "(\<lambda>i. measure M (A i)) sums (measure M (\<Union>i. A i))"
proof -
  have "(\<lambda>i. emeasure M (A i)) sums (emeasure M (\<Union>i. A i))"
    unfolding suminf_emeasure[OF measurable, symmetric] by (simp add: summable_sums)
  moreover
  { fix i
    have "emeasure M (A i) \<le> emeasure M (\<Union>i. A i)"
      using measurable by (auto intro!: emeasure_mono)
    then have "emeasure M (A i) = ennreal ((measure M (A i)))"
      using finite by (intro emeasure_eq_ennreal_measure) (auto simp: top_unique) }
  ultimately show ?thesis using finite
    by (subst (asm) (2) emeasure_eq_ennreal_measure)
       (simp_all add: measure_nonneg)
qed

lemma measure_subadditive:
  assumes measurable: "A \<in> sets M" "B \<in> sets M"
  and fin: "emeasure M A \<noteq> \<infinity>" "emeasure M B \<noteq> \<infinity>"
  shows "measure M (A \<union> B) \<le> measure M A + measure M B"
proof -
  have "emeasure M (A \<union> B) \<noteq> \<infinity>"
    using emeasure_subadditive[OF measurable] fin by (auto simp: top_unique)
  then show "(measure M (A \<union> B)) \<le> (measure M A) + (measure M B)"
    using emeasure_subadditive[OF measurable] fin
    apply simp
    apply (subst (asm) (2 3 4) emeasure_eq_ennreal_measure)
    apply (auto simp add: ennreal_plus[symmetric] simp del: ennreal_plus)
    done
qed

lemma measure_subadditive_finite:
  assumes A: "finite I" "A`I \<subseteq> sets M" and fin: "\<And>i. i \<in> I \<Longrightarrow> emeasure M (A i) \<noteq> \<infinity>"
  shows "measure M (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. measure M (A i))"
proof -
  { have "emeasure M (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. emeasure M (A i))"
      using emeasure_subadditive_finite[OF A] .
    also have "\<dots> < \<infinity>"
      using fin by (simp add: less_top A)
    finally have "emeasure M (\<Union>i\<in>I. A i) \<noteq> top" by simp }
  note * = this
  show ?thesis
    using emeasure_subadditive_finite[OF A] fin
    unfolding emeasure_eq_ennreal_measure[OF *]
    by (simp_all add: setsum_ennreal measure_nonneg setsum_nonneg emeasure_eq_ennreal_measure)
qed

lemma measure_subadditive_countably:
  assumes A: "range A \<subseteq> sets M" and fin: "(\<Sum>i. emeasure M (A i)) \<noteq> \<infinity>"
  shows "measure M (\<Union>i. A i) \<le> (\<Sum>i. measure M (A i))"
proof -
  from fin have **: "\<And>i. emeasure M (A i) \<noteq> top"
    using ennreal_suminf_lessD[of "\<lambda>i. emeasure M (A i)"] by (simp add: less_top)
  { have "emeasure M (\<Union>i. A i) \<le> (\<Sum>i. emeasure M (A i))"
      using emeasure_subadditive_countably[OF A] .
    also have "\<dots> < \<infinity>"
      using fin by (simp add: less_top)
    finally have "emeasure M (\<Union>i. A i) \<noteq> top" by simp }
  then have "ennreal (measure M (\<Union>i. A i)) = emeasure M (\<Union>i. A i)"
    by (rule emeasure_eq_ennreal_measure[symmetric])
  also have "\<dots> \<le> (\<Sum>i. emeasure M (A i))"
    using emeasure_subadditive_countably[OF A] .
  also have "\<dots> = ennreal (\<Sum>i. measure M (A i))"
    using fin unfolding emeasure_eq_ennreal_measure[OF **]
    by (subst suminf_ennreal) (auto simp: **)
  finally show ?thesis
    apply (rule ennreal_le_iff[THEN iffD1, rotated])
    apply (intro suminf_nonneg allI measure_nonneg summable_suminf_not_top)
    using fin
    apply (simp add: emeasure_eq_ennreal_measure[OF **])
    done
qed

lemma measure_eq_setsum_singleton:
  "finite S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M) \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> emeasure M {x} \<noteq> \<infinity>) \<Longrightarrow>
    measure M S = (\<Sum>x\<in>S. measure M {x})"
  using emeasure_eq_setsum_singleton[of S M]
  by (intro measure_eq_emeasure_eq_ennreal) (auto simp: setsum_nonneg emeasure_eq_ennreal_measure)

lemma Lim_measure_incseq:
  assumes A: "range A \<subseteq> sets M" "incseq A" and fin: "emeasure M (\<Union>i. A i) \<noteq> \<infinity>"
  shows "(\<lambda>i. measure M (A i)) \<longlonglongrightarrow> measure M (\<Union>i. A i)"
proof (rule tendsto_ennrealD)
  have "ennreal (measure M (\<Union>i. A i)) = emeasure M (\<Union>i. A i)"
    using fin by (auto simp: emeasure_eq_ennreal_measure)
  moreover have "ennreal (measure M (A i)) = emeasure M (A i)" for i
    using assms emeasure_mono[of "A _" "\<Union>i. A i" M]
    by (intro emeasure_eq_ennreal_measure[symmetric]) (auto simp: less_top UN_upper intro: le_less_trans)
  ultimately show "(\<lambda>x. ennreal (Sigma_Algebra.measure M (A x))) \<longlonglongrightarrow> ennreal (Sigma_Algebra.measure M (\<Union>i. A i))"
    using A by (auto intro!: Lim_emeasure_incseq)
qed auto

lemma Lim_measure_decseq:
  assumes A: "range A \<subseteq> sets M" "decseq A" and fin: "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
  shows "(\<lambda>n. measure M (A n)) \<longlonglongrightarrow> measure M (\<Inter>i. A i)"
proof (rule tendsto_ennrealD)
  have "ennreal (measure M (\<Inter>i. A i)) = emeasure M (\<Inter>i. A i)"
    using fin[of 0] A emeasure_mono[of "\<Inter>i. A i" "A 0" M]
    by (auto intro!: emeasure_eq_ennreal_measure[symmetric] simp: INT_lower less_top intro: le_less_trans)
  moreover have "ennreal (measure M (A i)) = emeasure M (A i)" for i
    using A fin[of i] by (intro emeasure_eq_ennreal_measure[symmetric]) auto
  ultimately show "(\<lambda>x. ennreal (Sigma_Algebra.measure M (A x))) \<longlonglongrightarrow> ennreal (Sigma_Algebra.measure M (\<Inter>i. A i))"
    using fin A by (auto intro!: Lim_emeasure_decseq)
qed auto

subsection \<open>Measure spaces with @{term "emeasure M (space M) < \<infinity>"}\<close>

locale finite_measure = sigma_finite_measure M for M +
  assumes finite_emeasure_space: "emeasure M (space M) \<noteq> top"

lemma finite_measureI[Pure.intro!]:
  "emeasure M (space M) \<noteq> \<infinity> \<Longrightarrow> finite_measure M"
  proof qed (auto intro!: exI[of _ "{space M}"])

lemma (in finite_measure) emeasure_finite[simp, intro]: "emeasure M A \<noteq> top"
  using finite_emeasure_space emeasure_space[of M A] by (auto simp: top_unique)

lemma (in finite_measure) emeasure_eq_measure: "emeasure M A = ennreal (measure M A)"
  by (intro emeasure_eq_ennreal_measure) simp

lemma (in finite_measure) emeasure_real: "\<exists>r. 0 \<le> r \<and> emeasure M A = ennreal r"
  using emeasure_finite[of A] by (cases "emeasure M A" rule: ennreal_cases) auto

lemma (in finite_measure) bounded_measure: "measure M A \<le> measure M (space M)"
  using emeasure_space[of M A] emeasure_real[of A] emeasure_real[of "space M"] by (auto simp: measure_def)

lemma (in finite_measure) finite_measure_Diff:
  assumes sets: "A \<in> sets M" "B \<in> sets M" and "B \<subseteq> A"
  shows "measure M (A - B) = measure M A - measure M B"
  using measure_Diff[OF _ assms] by simp

lemma (in finite_measure) finite_measure_Union:
  assumes sets: "A \<in> sets M" "B \<in> sets M" and "A \<inter> B = {}"
  shows "measure M (A \<union> B) = measure M A + measure M B"
  using measure_Union[OF _ _ assms] by simp

lemma (in finite_measure) finite_measure_finite_Union:
  assumes measurable: "finite S" "A`S \<subseteq> sets M" "disjoint_family_on A S"
  shows "measure M (\<Union>i\<in>S. A i) = (\<Sum>i\<in>S. measure M (A i))"
  using measure_finite_Union[OF assms] by simp

lemma (in finite_measure) finite_measure_UNION:
  assumes A: "range A \<subseteq> sets M" "disjoint_family A"
  shows "(\<lambda>i. measure M (A i)) sums (measure M (\<Union>i. A i))"
  using measure_UNION[OF A] by simp

lemma (in finite_measure) finite_measure_mono:
  assumes "A \<subseteq> B" "B \<in> sets M" shows "measure M A \<le> measure M B"
  using emeasure_mono[OF assms] emeasure_real[of A] emeasure_real[of B] by (auto simp: measure_def)

lemma (in finite_measure) finite_measure_subadditive:
  assumes m: "A \<in> sets M" "B \<in> sets M"
  shows "measure M (A \<union> B) \<le> measure M A + measure M B"
  using measure_subadditive[OF m] by simp

lemma (in finite_measure) finite_measure_subadditive_finite:
  assumes "finite I" "A`I \<subseteq> sets M" shows "measure M (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. measure M (A i))"
  using measure_subadditive_finite[OF assms] by simp

lemma (in finite_measure) finite_measure_subadditive_countably:
  "range A \<subseteq> sets M \<Longrightarrow> summable (\<lambda>i. measure M (A i)) \<Longrightarrow> measure M (\<Union>i. A i) \<le> (\<Sum>i. measure M (A i))"
  by (rule measure_subadditive_countably)
     (simp_all add: ennreal_suminf_neq_top emeasure_eq_measure)

lemma (in finite_measure) finite_measure_eq_setsum_singleton:
  assumes "finite S" and *: "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  shows "measure M S = (\<Sum>x\<in>S. measure M {x})"
  using measure_eq_setsum_singleton[OF assms] by simp

lemma (in finite_measure) finite_Lim_measure_incseq:
  assumes A: "range A \<subseteq> sets M" "incseq A"
  shows "(\<lambda>i. measure M (A i)) \<longlonglongrightarrow> measure M (\<Union>i. A i)"
  using Lim_measure_incseq[OF A] by simp

lemma (in finite_measure) finite_Lim_measure_decseq:
  assumes A: "range A \<subseteq> sets M" "decseq A"
  shows "(\<lambda>n. measure M (A n)) \<longlonglongrightarrow> measure M (\<Inter>i. A i)"
  using Lim_measure_decseq[OF A] by simp

lemma (in finite_measure) finite_measure_compl:
  assumes S: "S \<in> sets M"
  shows "measure M (space M - S) = measure M (space M) - measure M S"
  using measure_Diff[OF _ sets.top S sets.sets_into_space] S by simp

lemma (in finite_measure) finite_measure_mono_AE:
  assumes imp: "AE x in M. x \<in> A \<longrightarrow> x \<in> B" and B: "B \<in> sets M"
  shows "measure M A \<le> measure M B"
  using assms emeasure_mono_AE[OF imp B]
  by (simp add: emeasure_eq_measure)

lemma (in finite_measure) finite_measure_eq_AE:
  assumes iff: "AE x in M. x \<in> A \<longleftrightarrow> x \<in> B"
  assumes A: "A \<in> sets M" and B: "B \<in> sets M"
  shows "measure M A = measure M B"
  using assms emeasure_eq_AE[OF assms] by (simp add: emeasure_eq_measure)

lemma (in finite_measure) measure_increasing: "increasing M (measure M)"
  by (auto intro!: finite_measure_mono simp: increasing_def)

lemma (in finite_measure) measure_zero_union:
  assumes "s \<in> sets M" "t \<in> sets M" "measure M t = 0"
  shows "measure M (s \<union> t) = measure M s"
using assms
proof -
  have "measure M (s \<union> t) \<le> measure M s"
    using finite_measure_subadditive[of s t] assms by auto
  moreover have "measure M (s \<union> t) \<ge> measure M s"
    using assms by (blast intro: finite_measure_mono)
  ultimately show ?thesis by simp
qed

lemma (in finite_measure) measure_eq_compl:
  assumes "s \<in> sets M" "t \<in> sets M"
  assumes "measure M (space M - s) = measure M (space M - t)"
  shows "measure M s = measure M t"
  using assms finite_measure_compl by auto

lemma (in finite_measure) measure_eq_bigunion_image:
  assumes "range f \<subseteq> sets M" "range g \<subseteq> sets M"
  assumes "disjoint_family f" "disjoint_family g"
  assumes "\<And> n :: nat. measure M (f n) = measure M (g n)"
  shows "measure M (\<Union>i. f i) = measure M (\<Union>i. g i)"
using assms
proof -
  have a: "(\<lambda> i. measure M (f i)) sums (measure M (\<Union>i. f i))"
    by (rule finite_measure_UNION[OF assms(1,3)])
  have b: "(\<lambda> i. measure M (g i)) sums (measure M (\<Union>i. g i))"
    by (rule finite_measure_UNION[OF assms(2,4)])
  show ?thesis using sums_unique[OF b] sums_unique[OF a] assms by simp
qed

lemma (in finite_measure) measure_countably_zero:
  assumes "range c \<subseteq> sets M"
  assumes "\<And> i. measure M (c i) = 0"
  shows "measure M (\<Union>i :: nat. c i) = 0"
proof (rule antisym)
  show "measure M (\<Union>i :: nat. c i) \<le> 0"
    using finite_measure_subadditive_countably[OF assms(1)] by (simp add: assms(2))
qed simp

lemma (in finite_measure) measure_space_inter:
  assumes events:"s \<in> sets M" "t \<in> sets M"
  assumes "measure M t = measure M (space M)"
  shows "measure M (s \<inter> t) = measure M s"
proof -
  have "measure M ((space M - s) \<union> (space M - t)) = measure M (space M - s)"
    using events assms finite_measure_compl[of "t"] by (auto intro!: measure_zero_union)
  also have "(space M - s) \<union> (space M - t) = space M - (s \<inter> t)"
    by blast
  finally show "measure M (s \<inter> t) = measure M s"
    using events by (auto intro!: measure_eq_compl[of "s \<inter> t" s])
qed

lemma (in finite_measure) measure_equiprobable_finite_unions:
  assumes s: "finite s" "\<And>x. x \<in> s \<Longrightarrow> {x} \<in> sets M"
  assumes "\<And> x y. \<lbrakk>x \<in> s; y \<in> s\<rbrakk> \<Longrightarrow> measure M {x} = measure M {y}"
  shows "measure M s = real (card s) * measure M {SOME x. x \<in> s}"
proof cases
  assume "s \<noteq> {}"
  then have "\<exists> x. x \<in> s" by blast
  from someI_ex[OF this] assms
  have prob_some: "\<And> x. x \<in> s \<Longrightarrow> measure M {x} = measure M {SOME y. y \<in> s}" by blast
  have "measure M s = (\<Sum> x \<in> s. measure M {x})"
    using finite_measure_eq_setsum_singleton[OF s] by simp
  also have "\<dots> = (\<Sum> x \<in> s. measure M {SOME y. y \<in> s})" using prob_some by auto
  also have "\<dots> = real (card s) * measure M {(SOME x. x \<in> s)}"
    using setsum_constant assms by simp
  finally show ?thesis by simp
qed simp

lemma (in finite_measure) measure_real_sum_image_fn:
  assumes "e \<in> sets M"
  assumes "\<And> x. x \<in> s \<Longrightarrow> e \<inter> f x \<in> sets M"
  assumes "finite s"
  assumes disjoint: "\<And> x y. \<lbrakk>x \<in> s ; y \<in> s ; x \<noteq> y\<rbrakk> \<Longrightarrow> f x \<inter> f y = {}"
  assumes upper: "space M \<subseteq> (\<Union>i \<in> s. f i)"
  shows "measure M e = (\<Sum> x \<in> s. measure M (e \<inter> f x))"
proof -
  have "e \<subseteq> (\<Union>i\<in>s. f i)"
    using \<open>e \<in> sets M\<close> sets.sets_into_space upper by blast
  then have e: "e = (\<Union>i \<in> s. e \<inter> f i)"
    by auto
  hence "measure M e = measure M (\<Union>i \<in> s. e \<inter> f i)" by simp
  also have "\<dots> = (\<Sum> x \<in> s. measure M (e \<inter> f x))"
  proof (rule finite_measure_finite_Union)
    show "finite s" by fact
    show "(\<lambda>i. e \<inter> f i)`s \<subseteq> sets M" using assms(2) by auto
    show "disjoint_family_on (\<lambda>i. e \<inter> f i) s"
      using disjoint by (auto simp: disjoint_family_on_def)
  qed
  finally show ?thesis .
qed

lemma (in finite_measure) measure_exclude:
  assumes "A \<in> sets M" "B \<in> sets M"
  assumes "measure M A = measure M (space M)" "A \<inter> B = {}"
  shows "measure M B = 0"
  using measure_space_inter[of B A] assms by (auto simp: ac_simps)
lemma (in finite_measure) finite_measure_distr:
  assumes f: "f \<in> measurable M M'"
  shows "finite_measure (distr M M' f)"
proof (rule finite_measureI)
  have "f -` space M' \<inter> space M = space M" using f by (auto dest: measurable_space)
  with f show "emeasure (distr M M' f) (space (distr M M' f)) \<noteq> \<infinity>" by (auto simp: emeasure_distr)
qed

lemma emeasure_gfp[consumes 1, case_names cont measurable]:
  assumes sets[simp]: "\<And>s. sets (M s) = sets N"
  assumes "\<And>s. finite_measure (M s)"
  assumes cont: "inf_continuous F" "inf_continuous f"
  assumes meas: "\<And>P. Measurable.pred N P \<Longrightarrow> Measurable.pred N (F P)"
  assumes iter: "\<And>P s. Measurable.pred N P \<Longrightarrow> emeasure (M s) {x\<in>space N. F P x} = f (\<lambda>s. emeasure (M s) {x\<in>space N. P x}) s"
  assumes bound: "\<And>P. f P \<le> f (\<lambda>s. emeasure (M s) (space (M s)))"
  shows "emeasure (M s) {x\<in>space N. gfp F x} = gfp f s"
proof (subst gfp_transfer_bounded[where \<alpha>="\<lambda>F s. emeasure (M s) {x\<in>space N. F x}" and g=f and f=F and
    P="Measurable.pred N", symmetric])
  interpret finite_measure "M s" for s by fact
  fix C assume "decseq C" "\<And>i. Measurable.pred N (C i)"
  then show "(\<lambda>s. emeasure (M s) {x \<in> space N. (INF i. C i) x}) = (INF i. (\<lambda>s. emeasure (M s) {x \<in> space N. C i x}))"
    unfolding INF_apply[abs_def]
    by (subst INF_emeasure_decseq) (auto simp: antimono_def fun_eq_iff intro!: arg_cong2[where f=emeasure])
next
  show "f x \<le> (\<lambda>s. emeasure (M s) {x \<in> space N. F top x})" for x
    using bound[of x] sets_eq_imp_space_eq[OF sets] by (simp add: iter)
qed (auto simp add: iter le_fun_def INF_apply[abs_def] intro!: meas cont)

subsection \<open>Counting space\<close>

lemma strict_monoI_Suc:
  assumes ord [simp]: "(\<And>n. f n < f (Suc n))" shows "strict_mono f"
  unfolding strict_mono_def
proof safe
  fix n m :: nat assume "n < m" then show "f n < f m"
    by (induct m) (auto simp: less_Suc_eq intro: less_trans ord)
qed

lemma emeasure_count_space:
  assumes "X \<subseteq> A" shows "emeasure (count_space A) X = (if finite X then of_nat (card X) else \<infinity>)"
    (is "_ = ?M X")
  unfolding count_space_def
proof (rule emeasure_measure_of_sigma)
  show "X \<in> Pow A" using \<open>X \<subseteq> A\<close> by auto
  show "sigma_algebra A (Pow A)" by (rule sigma_algebra_Pow)
  show positive: "positive (Pow A) ?M"
    by (auto simp: positive_def)
  have additive: "additive (Pow A) ?M"
    by (auto simp: card_Un_disjoint additive_def)

  interpret ring_of_sets A "Pow A"
    by (rule ring_of_setsI) auto
  show "countably_additive (Pow A) ?M"
    unfolding countably_additive_iff_continuous_from_below[OF positive additive]
  proof safe
    fix F :: "nat \<Rightarrow> 'a set" assume "incseq F"
    show "(\<lambda>i. ?M (F i)) \<longlonglongrightarrow> ?M (\<Union>i. F i)"
    proof cases
      assume "\<exists>i. \<forall>j\<ge>i. F i = F j"
      then guess i .. note i = this
      { fix j from i \<open>incseq F\<close> have "F j \<subseteq> F i"
          by (cases "i \<le> j") (auto simp: incseq_def) }
      then have eq: "(\<Union>i. F i) = F i"
        by auto
      with i show ?thesis
        by (auto intro!: Lim_eventually eventually_sequentiallyI[where c=i])
    next
      assume "\<not> (\<exists>i. \<forall>j\<ge>i. F i = F j)"
      then obtain f where f: "\<And>i. i \<le> f i" "\<And>i. F i \<noteq> F (f i)" by metis
      then have "\<And>i. F i \<subseteq> F (f i)" using \<open>incseq F\<close> by (auto simp: incseq_def)
      with f have *: "\<And>i. F i \<subset> F (f i)" by auto

      have "incseq (\<lambda>i. ?M (F i))"
        using \<open>incseq F\<close> unfolding incseq_def by (auto simp: card_mono dest: finite_subset)
      then have "(\<lambda>i. ?M (F i)) \<longlonglongrightarrow> (SUP n. ?M (F n))"
        by (rule LIMSEQ_SUP)

      moreover have "(SUP n. ?M (F n)) = top"
      proof (rule ennreal_SUP_eq_top)
        fix n :: nat show "\<exists>k::nat\<in>UNIV. of_nat n \<le> ?M (F k)"
        proof (induct n)
          case (Suc n)
          then guess k .. note k = this
          moreover have "finite (F k) \<Longrightarrow> finite (F (f k)) \<Longrightarrow> card (F k) < card (F (f k))"
            using \<open>F k \<subset> F (f k)\<close> by (simp add: psubset_card_mono)
          moreover have "finite (F (f k)) \<Longrightarrow> finite (F k)"
            using \<open>k \<le> f k\<close> \<open>incseq F\<close> by (auto simp: incseq_def dest: finite_subset)
          ultimately show ?case
            by (auto intro!: exI[of _ "f k"] simp del: of_nat_Suc)
        qed auto
      qed

      moreover
      have "inj (\<lambda>n. F ((f ^^ n) 0))"
        by (intro strict_mono_imp_inj_on strict_monoI_Suc) (simp add: *)
      then have 1: "infinite (range (\<lambda>i. F ((f ^^ i) 0)))"
        by (rule range_inj_infinite)
      have "infinite (Pow (\<Union>i. F i))"
        by (rule infinite_super[OF _ 1]) auto
      then have "infinite (\<Union>i. F i)"
        by auto

      ultimately show ?thesis by auto
    qed
  qed
qed

lemma distr_bij_count_space:
  assumes f: "bij_betw f A B"
  shows "distr (count_space A) (count_space B) f = count_space B"
proof (rule measure_eqI)
  have f': "f \<in> measurable (count_space A) (count_space B)"
    using f unfolding Pi_def bij_betw_def by auto
  fix X assume "X \<in> sets (distr (count_space A) (count_space B) f)"
  then have X: "X \<in> sets (count_space B)" by auto
  moreover then have "f -` X \<inter> A = the_inv_into A f ` X"
    using f by (auto simp: bij_betw_def subset_image_iff image_iff the_inv_into_f_f intro: the_inv_into_f_f[symmetric])
  moreover have "inj_on (the_inv_into A f) B"
    using X f by (auto simp: bij_betw_def inj_on_the_inv_into)
  with X have "inj_on (the_inv_into A f) X"
    by (auto intro: subset_inj_on)
  ultimately show "emeasure (distr (count_space A) (count_space B) f) X = emeasure (count_space B) X"
    using f unfolding emeasure_distr[OF f' X]
    by (subst (1 2) emeasure_count_space) (auto simp: card_image dest: finite_imageD)
qed simp

lemma emeasure_count_space_finite[simp]:
  "X \<subseteq> A \<Longrightarrow> finite X \<Longrightarrow> emeasure (count_space A) X = of_nat (card X)"
  using emeasure_count_space[of X A] by simp

lemma emeasure_count_space_infinite[simp]:
  "X \<subseteq> A \<Longrightarrow> infinite X \<Longrightarrow> emeasure (count_space A) X = \<infinity>"
  using emeasure_count_space[of X A] by simp

lemma measure_count_space: "measure (count_space A) X = (if X \<subseteq> A then of_nat (card X) else 0)"
  by (cases "finite X") (auto simp: measure_notin_sets ennreal_of_nat_eq_real_of_nat
                                    measure_zero_top measure_eq_emeasure_eq_ennreal)

lemma emeasure_count_space_eq_0:
  "emeasure (count_space A) X = 0 \<longleftrightarrow> (X \<subseteq> A \<longrightarrow> X = {})"
proof cases
  assume X: "X \<subseteq> A"
  then show ?thesis
  proof (intro iffI impI)
    assume "emeasure (count_space A) X = 0"
    with X show "X = {}"
      by (subst (asm) emeasure_count_space) (auto split: if_split_asm)
  qed simp
qed (simp add: emeasure_notin_sets)

lemma space_empty: "space M = {} \<Longrightarrow> M = count_space {}"
  by (rule measure_eqI) (simp_all add: space_empty_iff)

lemma null_sets_count_space: "null_sets (count_space A) = { {} }"
  unfolding null_sets_def by (auto simp add: emeasure_count_space_eq_0)

lemma AE_count_space: "(AE x in count_space A. P x) \<longleftrightarrow> (\<forall>x\<in>A. P x)"
  unfolding eventually_ae_filter by (auto simp add: null_sets_count_space)

lemma sigma_finite_measure_count_space_countable:
  assumes A: "countable A"
  shows "sigma_finite_measure (count_space A)"
  proof qed (insert A, auto intro!: exI[of _ "(\<lambda>a. {a}) ` A"])

lemma sigma_finite_measure_count_space:
  fixes A :: "'a::countable set" shows "sigma_finite_measure (count_space A)"
  by (rule sigma_finite_measure_count_space_countable) auto

lemma finite_measure_count_space:
  assumes [simp]: "finite A"
  shows "finite_measure (count_space A)"
  by rule simp

lemma sigma_finite_measure_count_space_finite:
  assumes A: "finite A" shows "sigma_finite_measure (count_space A)"
proof -
  interpret finite_measure "count_space A" using A by (rule finite_measure_count_space)
  show "sigma_finite_measure (count_space A)" ..
qed

subsection \<open>Measure restricted to space\<close>

lemma emeasure_restrict_space:
  assumes "\<Omega> \<inter> space M \<in> sets M" "A \<subseteq> \<Omega>"
  shows "emeasure (restrict_space M \<Omega>) A = emeasure M A"
proof cases
  assume "A \<in> sets M"
  show ?thesis
  proof (rule emeasure_measure_of[OF restrict_space_def])
    show "op \<inter> \<Omega> ` sets M \<subseteq> Pow (\<Omega> \<inter> space M)" "A \<in> sets (restrict_space M \<Omega>)"
      using \<open>A \<subseteq> \<Omega>\<close> \<open>A \<in> sets M\<close> sets.space_closed by (auto simp: sets_restrict_space)
    show "positive (sets (restrict_space M \<Omega>)) (emeasure M)"
      by (auto simp: positive_def)
    show "countably_additive (sets (restrict_space M \<Omega>)) (emeasure M)"
    proof (rule countably_additiveI)
      fix A :: "nat \<Rightarrow> _" assume "range A \<subseteq> sets (restrict_space M \<Omega>)" "disjoint_family A"
      with assms have "\<And>i. A i \<in> sets M" "\<And>i. A i \<subseteq> space M" "disjoint_family A"
        by (fastforce simp: sets_restrict_space_iff[OF assms(1)] image_subset_iff
                      dest: sets.sets_into_space)+
      then show "(\<Sum>i. emeasure M (A i)) = emeasure M (\<Union>i. A i)"
        by (subst suminf_emeasure) (auto simp: disjoint_family_subset)
    qed
  qed
next
  assume "A \<notin> sets M"
  moreover with assms have "A \<notin> sets (restrict_space M \<Omega>)"
    by (simp add: sets_restrict_space_iff)
  ultimately show ?thesis
    by (simp add: emeasure_notin_sets)
qed

lemma measure_restrict_space:
  assumes "\<Omega> \<inter> space M \<in> sets M" "A \<subseteq> \<Omega>"
  shows "measure (restrict_space M \<Omega>) A = measure M A"
  using emeasure_restrict_space[OF assms] by (simp add: measure_def)

lemma AE_restrict_space_iff:
  assumes "\<Omega> \<inter> space M \<in> sets M"
  shows "(AE x in restrict_space M \<Omega>. P x) \<longleftrightarrow> (AE x in M. x \<in> \<Omega> \<longrightarrow> P x)"
proof -
  have ex_cong: "\<And>P Q f. (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> (\<And>x. Q x \<Longrightarrow> P (f x)) \<Longrightarrow> (\<exists>x. P x) \<longleftrightarrow> (\<exists>x. Q x)"
    by auto
  { fix X assume X: "X \<in> sets M" "emeasure M X = 0"
    then have "emeasure M (\<Omega> \<inter> space M \<inter> X) \<le> emeasure M X"
      by (intro emeasure_mono) auto
    then have "emeasure M (\<Omega> \<inter> space M \<inter> X) = 0"
      using X by (auto intro!: antisym) }
  with assms show ?thesis
    unfolding eventually_ae_filter
    by (auto simp add: space_restrict_space null_sets_def sets_restrict_space_iff
                       emeasure_restrict_space cong: conj_cong
             intro!: ex_cong[where f="\<lambda>X. (\<Omega> \<inter> space M) \<inter> X"])
qed

lemma restrict_restrict_space:
  assumes "A \<inter> space M \<in> sets M" "B \<inter> space M \<in> sets M"
  shows "restrict_space (restrict_space M A) B = restrict_space M (A \<inter> B)" (is "?l = ?r")
proof (rule measure_eqI[symmetric])
  show "sets ?r = sets ?l"
    unfolding sets_restrict_space image_comp by (intro image_cong) auto
next
  fix X assume "X \<in> sets (restrict_space M (A \<inter> B))"
  then obtain Y where "Y \<in> sets M" "X = Y \<inter> A \<inter> B"
    by (auto simp: sets_restrict_space)
  with assms sets.Int[OF assms] show "emeasure ?r X = emeasure ?l X"
    by (subst (1 2) emeasure_restrict_space)
       (auto simp: space_restrict_space sets_restrict_space_iff emeasure_restrict_space ac_simps)
qed

lemma restrict_count_space: "restrict_space (count_space B) A = count_space (A \<inter> B)"
proof (rule measure_eqI)
  show "sets (restrict_space (count_space B) A) = sets (count_space (A \<inter> B))"
    by (subst sets_restrict_space) auto
  moreover fix X assume "X \<in> sets (restrict_space (count_space B) A)"
  ultimately have "X \<subseteq> A \<inter> B" by auto
  then show "emeasure (restrict_space (count_space B) A) X = emeasure (count_space (A \<inter> B)) X"
    by (cases "finite X") (auto simp add: emeasure_restrict_space)
qed

lemma sigma_finite_measure_restrict_space:
  assumes "sigma_finite_measure M"
  and A: "A \<in> sets M"
  shows "sigma_finite_measure (restrict_space M A)"
proof -
  interpret sigma_finite_measure M by fact
  from sigma_finite_countable obtain C
    where C: "countable C" "C \<subseteq> sets M" "(\<Union>C) = space M" "\<forall>a\<in>C. emeasure M a \<noteq> \<infinity>"
    by blast
  let ?C = "op \<inter> A ` C"
  from C have "countable ?C" "?C \<subseteq> sets (restrict_space M A)" "(\<Union>?C) = space (restrict_space M A)"
    by(auto simp add: sets_restrict_space space_restrict_space)
  moreover {
    fix a
    assume "a \<in> ?C"
    then obtain a' where "a = A \<inter> a'" "a' \<in> C" ..
    then have "emeasure (restrict_space M A) a \<le> emeasure M a'"
      using A C by(auto simp add: emeasure_restrict_space intro: emeasure_mono)
    also have "\<dots> < \<infinity>" using C(4)[rule_format, of a'] \<open>a' \<in> C\<close> by (simp add: less_top)
    finally have "emeasure (restrict_space M A) a \<noteq> \<infinity>" by simp }
  ultimately show ?thesis
    by unfold_locales (rule exI conjI|assumption|blast)+
qed

lemma finite_measure_restrict_space:
  assumes "finite_measure M"
  and A: "A \<in> sets M"
  shows "finite_measure (restrict_space M A)"
proof -
  interpret finite_measure M by fact
  show ?thesis
    by(rule finite_measureI)(simp add: emeasure_restrict_space A space_restrict_space)
qed

lemma restrict_distr:
  assumes [measurable]: "f \<in> measurable M N"
  assumes [simp]: "\<Omega> \<inter> space N \<in> sets N" and restrict: "f \<in> space M \<rightarrow> \<Omega>"
  shows "restrict_space (distr M N f) \<Omega> = distr M (restrict_space N \<Omega>) f"
  (is "?l = ?r")
proof (rule measure_eqI)
  fix A assume "A \<in> sets (restrict_space (distr M N f) \<Omega>)"
  with restrict show "emeasure ?l A = emeasure ?r A"
    by (subst emeasure_distr)
       (auto simp: sets_restrict_space_iff emeasure_restrict_space emeasure_distr
             intro!: measurable_restrict_space2)
qed (simp add: sets_restrict_space)

lemma measure_eqI_restrict_generator:
  assumes E: "Int_stable E" "E \<subseteq> Pow \<Omega>" "\<And>X. X \<in> E \<Longrightarrow> emeasure M X = emeasure N X"
  assumes sets_eq: "sets M = sets N" and \<Omega>: "\<Omega> \<in> sets M"
  assumes "sets (restrict_space M \<Omega>) = sigma_sets \<Omega> E"
  assumes "sets (restrict_space N \<Omega>) = sigma_sets \<Omega> E"
  assumes ae: "AE x in M. x \<in> \<Omega>" "AE x in N. x \<in> \<Omega>"
  assumes A: "countable A" "A \<noteq> {}" "A \<subseteq> E" "\<Union>A = \<Omega>" "\<And>a. a \<in> A \<Longrightarrow> emeasure M a \<noteq> \<infinity>"
  shows "M = N"
proof (rule measure_eqI)
  fix X assume X: "X \<in> sets M"
  then have "emeasure M X = emeasure (restrict_space M \<Omega>) (X \<inter> \<Omega>)"
    using ae \<Omega> by (auto simp add: emeasure_restrict_space intro!: emeasure_eq_AE)
  also have "restrict_space M \<Omega> = restrict_space N \<Omega>"
  proof (rule measure_eqI_generator_eq)
    fix X assume "X \<in> E"
    then show "emeasure (restrict_space M \<Omega>) X = emeasure (restrict_space N \<Omega>) X"
      using E \<Omega> by (subst (1 2) emeasure_restrict_space) (auto simp: sets_eq sets_eq[THEN sets_eq_imp_space_eq])
  next
    show "range (from_nat_into A) \<subseteq> E" "(\<Union>i. from_nat_into A i) = \<Omega>"
      using A by (auto cong del: strong_SUP_cong)
  next
    fix i
    have "emeasure (restrict_space M \<Omega>) (from_nat_into A i) = emeasure M (from_nat_into A i)"
      using A \<Omega> by (subst emeasure_restrict_space)
                   (auto simp: sets_eq sets_eq[THEN sets_eq_imp_space_eq] intro: from_nat_into)
    with A show "emeasure (restrict_space M \<Omega>) (from_nat_into A i) \<noteq> \<infinity>"
      by (auto intro: from_nat_into)
  qed fact+
  also have "emeasure (restrict_space N \<Omega>) (X \<inter> \<Omega>) = emeasure N X"
    using X ae \<Omega> by (auto simp add: emeasure_restrict_space sets_eq intro!: emeasure_eq_AE)
  finally show "emeasure M X = emeasure N X" .
qed fact

subsection \<open>Null measure\<close>

definition "null_measure M = sigma (space M) (sets M)"

lemma space_null_measure[simp]: "space (null_measure M) = space M"
  by (simp add: null_measure_def)

lemma sets_null_measure[simp, measurable_cong]: "sets (null_measure M) = sets M"
  by (simp add: null_measure_def)

lemma emeasure_null_measure[simp]: "emeasure (null_measure M) X = 0"
  by (cases "X \<in> sets M", rule emeasure_measure_of)
     (auto simp: positive_def countably_additive_def emeasure_notin_sets null_measure_def
           dest: sets.sets_into_space)

lemma measure_null_measure[simp]: "measure (null_measure M) X = 0"
  by (intro measure_eq_emeasure_eq_ennreal) auto

lemma null_measure_idem [simp]: "null_measure (null_measure M) = null_measure M"
  by(rule measure_eqI) simp_all

subsection \<open>Scaling a measure\<close>

definition scale_measure :: "ennreal \<Rightarrow> 'a measure \<Rightarrow> 'a measure"
where
  "scale_measure r M = measure_of (space M) (sets M) (\<lambda>A. r * emeasure M A)"

lemma space_scale_measure: "space (scale_measure r M) = space M"
  by (simp add: scale_measure_def)

lemma sets_scale_measure [simp, measurable_cong]: "sets (scale_measure r M) = sets M"
  by (simp add: scale_measure_def)

lemma emeasure_scale_measure [simp]:
  "emeasure (scale_measure r M) A = r * emeasure M A"
  (is "_ = ?\<mu> A")
proof(cases "A \<in> sets M")
  case True
  show ?thesis unfolding scale_measure_def
  proof(rule emeasure_measure_of_sigma)
    show "sigma_algebra (space M) (sets M)" ..
    show "positive (sets M) ?\<mu>" by (simp add: positive_def)
    show "countably_additive (sets M) ?\<mu>"
    proof (rule countably_additiveI)
      fix A :: "nat \<Rightarrow> _"  assume *: "range A \<subseteq> sets M" "disjoint_family A"
      have "(\<Sum>i. ?\<mu> (A i)) = r * (\<Sum>i. emeasure M (A i))"
        by simp
      also have "\<dots> = ?\<mu> (\<Union>i. A i)" using * by(simp add: suminf_emeasure)
      finally show "(\<Sum>i. ?\<mu> (A i)) = ?\<mu> (\<Union>i. A i)" .
    qed
  qed(fact True)
qed(simp add: emeasure_notin_sets)

lemma scale_measure_1 [simp]: "scale_measure 1 M = M"
  by(rule measure_eqI) simp_all

lemma scale_measure_0[simp]: "scale_measure 0 M = null_measure M"
  by(rule measure_eqI) simp_all

lemma measure_scale_measure [simp]: "0 \<le> r \<Longrightarrow> measure (scale_measure r M) A = r * measure M A"
  using emeasure_scale_measure[of r M A]
    emeasure_eq_ennreal_measure[of M A]
    measure_eq_emeasure_eq_ennreal[of _ "scale_measure r M" A]
  by (cases "emeasure (scale_measure r M) A = top")
     (auto simp del: emeasure_scale_measure
           simp: ennreal_top_eq_mult_iff ennreal_mult_eq_top_iff measure_zero_top ennreal_mult[symmetric])

lemma scale_scale_measure [simp]:
  "scale_measure r (scale_measure r' M) = scale_measure (r * r') M"
  by (rule measure_eqI) (simp_all add: max_def mult.assoc)

lemma scale_null_measure [simp]: "scale_measure r (null_measure M) = null_measure M"
  by (rule measure_eqI) simp_all

subsection \<open>Measures form a chain-complete partial order\<close>

instantiation measure :: (type) order_bot
begin

definition bot_measure :: "'a measure" where
  "bot_measure = sigma {} {{}}"

lemma space_bot[simp]: "space bot = {}"
  unfolding bot_measure_def by (rule space_measure_of) auto

lemma sets_bot[simp]: "sets bot = {{}}"
  unfolding bot_measure_def by (subst sets_measure_of) auto

lemma emeasure_bot[simp]: "emeasure bot = (\<lambda>x. 0)"
  unfolding bot_measure_def by (rule emeasure_sigma)

inductive less_eq_measure :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "sets N = sets M \<Longrightarrow> (\<And>A. A \<in> sets M \<Longrightarrow> emeasure M A \<le> emeasure N A) \<Longrightarrow> less_eq_measure M N"
| "less_eq_measure bot N"

definition less_measure :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "less_measure M N \<longleftrightarrow> (M \<le> N \<and> \<not> N \<le> M)"

instance
proof (standard, goal_cases)
  case 1 then show ?case
    unfolding less_measure_def ..
next
  case (2 M) then show ?case
    by (intro less_eq_measure.intros) auto
next
  case (3 M N L) then show ?case
    apply (safe elim!: less_eq_measure.cases)
    apply (simp_all add: less_eq_measure.intros)
    apply (rule less_eq_measure.intros)
    apply simp
    apply (blast intro: order_trans) []
    unfolding less_eq_measure.simps
    apply (rule disjI2)
    apply simp
    apply (rule measure_eqI)
    apply (auto intro!: antisym)
    done
next
  case (4 M N) then show ?case
    apply (safe elim!: less_eq_measure.cases intro!: measure_eqI)
    apply simp
    apply simp
    apply (blast intro: antisym)
    apply (simp)
    apply simp
    done
qed (rule less_eq_measure.intros)
end

lemma le_emeasureD: "M \<le> N \<Longrightarrow> emeasure M A \<le> emeasure N A"
  by (cases "A \<in> sets M") (auto elim!: less_eq_measure.cases simp: emeasure_notin_sets)

lemma le_sets: "N \<le> M \<Longrightarrow> sets N \<le> sets M"
  unfolding less_eq_measure.simps by auto

instantiation measure :: (type) ccpo
begin

definition Sup_measure :: "'a measure set \<Rightarrow> 'a measure" where
  "Sup_measure A = measure_of (SUP a:A. space a) (SUP a:A. sets a) (SUP a:A. emeasure a)"

lemma
  assumes A: "Complete_Partial_Order.chain op \<le> A" and a: "a \<noteq> bot" "a \<in> A"
  shows space_Sup: "space (Sup A) = space a"
    and sets_Sup: "sets (Sup A) = sets a"
proof -
  have sets: "(SUP a:A. sets a) = sets a"
  proof (intro antisym SUP_least)
    fix a' show "a' \<in> A \<Longrightarrow> sets a' \<subseteq> sets a"
      using a chainD[OF A, of a a'] by (auto elim!: less_eq_measure.cases)
  qed (insert \<open>a\<in>A\<close>, auto)
  have space: "(SUP a:A. space a) = space a"
  proof (intro antisym SUP_least)
    fix a' show "a' \<in> A \<Longrightarrow> space a' \<subseteq> space a"
      using a chainD[OF A, of a a'] by (intro sets_le_imp_space_le) (auto elim!: less_eq_measure.cases)
  qed (insert \<open>a\<in>A\<close>, auto)
  show "space (Sup A) = space a"
    unfolding Sup_measure_def sets space sets.space_measure_of_eq ..
  show "sets (Sup A) = sets a"
    unfolding Sup_measure_def sets space sets.sets_measure_of_eq ..
qed

lemma emeasure_Sup:
  assumes A: "Complete_Partial_Order.chain op \<le> A" "A \<noteq> {}"
  assumes "X \<in> sets (Sup A)"
  shows "emeasure (Sup A) X = (SUP a:A. emeasure a) X"
proof (rule emeasure_measure_of[OF Sup_measure_def])
  show "countably_additive (sets (Sup A)) (SUP a:A. emeasure a)"
    unfolding countably_additive_def
  proof safe
    fix F :: "nat \<Rightarrow> 'a set" assume F: "range F \<subseteq> sets (Sup A)" "disjoint_family F"
    show "(\<Sum>i. (SUP a:A. emeasure a) (F i)) = SUPREMUM A emeasure (UNION UNIV F)"
      unfolding SUP_apply
    proof (subst ennreal_suminf_SUP_eq_directed)
      fix N i j assume "i \<in> A" "j \<in> A"
      with A(1)
      show "\<exists>k\<in>A. \<forall>n\<in>N. emeasure i (F n) \<le> emeasure k (F n) \<and> emeasure j (F n) \<le> emeasure k (F n)"
        by (blast elim: chainE dest: le_emeasureD)
    next
      show "(SUP n:A. \<Sum>i. emeasure n (F i)) = (SUP y:A. emeasure y (UNION UNIV F))"
      proof (intro SUP_cong refl)
        fix a assume "a \<in> A" then show "(\<Sum>i. emeasure a (F i)) = emeasure a (UNION UNIV F)"
          using sets_Sup[OF A(1), of a] F by (cases "a = bot") (auto simp: suminf_emeasure)
      qed
    qed
  qed
qed (insert \<open>A \<noteq> {}\<close> \<open>X \<in> sets (Sup A)\<close>, auto simp: positive_def dest: sets.sets_into_space intro: SUP_upper2)

instance
proof
  fix A and x :: "'a measure" assume A: "Complete_Partial_Order.chain op \<le> A" and x: "x \<in> A"
  show "x \<le> Sup A"
  proof cases
    assume "x \<noteq> bot"
    show ?thesis
    proof
      show "sets (Sup A) = sets x"
        using A \<open>x \<noteq> bot\<close> x by (rule sets_Sup)
      with x show "\<And>a. a \<in> sets x \<Longrightarrow> emeasure x a \<le> emeasure (Sup A) a"
        by (subst emeasure_Sup[OF A]) (auto intro: SUP_upper)
    qed
  qed simp
next
  fix A and x :: "'a measure" assume A: "Complete_Partial_Order.chain op \<le> A" and x: "\<And>z. z \<in> A \<Longrightarrow> z \<le> x"
  consider "A = {}" | "A = {bot}" | x where "x\<in>A" "x \<noteq> bot"
    by blast
  then show "Sup A \<le> x"
  proof cases
    assume "A = {}"
    moreover have "Sup ({}::'a measure set) = bot"
      by (auto simp add: Sup_measure_def sigma_sets_empty_eq intro!: measure_eqI)
    ultimately show ?thesis
      by simp
  next
    assume "A = {bot}"
    moreover have "Sup ({bot}::'a measure set) = bot"
      by (auto simp add: Sup_measure_def sigma_sets_empty_eq intro!: measure_eqI)
     ultimately show ?thesis
      by simp
  next
    fix a assume "a \<in> A" "a \<noteq> bot"
    then have "a \<le> x" "x \<noteq> bot" "a \<noteq> bot"
      using x[OF \<open>a \<in> A\<close>] by (auto simp: bot_unique)
    then have "sets x = sets a"
      by (auto elim: less_eq_measure.cases)

    show "Sup A \<le> x"
    proof (rule less_eq_measure.intros)
      show "sets x = sets (Sup A)"
        by (subst sets_Sup[OF A \<open>a \<noteq> bot\<close> \<open>a \<in> A\<close>]) fact
    next
      fix X assume "X \<in> sets (Sup A)"
      then have "emeasure (Sup A) X \<le> (SUP a:A. emeasure a X)"
        using \<open>a\<in>A\<close> by (subst emeasure_Sup[OF A _]) auto
      also have "\<dots> \<le> emeasure x X"
        by (intro SUP_least le_emeasureD x)
      finally show "emeasure (Sup A) X \<le> emeasure x X" .
    qed
  qed
qed
end

lemma
  assumes A: "Complete_Partial_Order.chain op \<le> (f ` A)" and a: "a \<in> A" "f a \<noteq> bot"
  shows space_SUP: "space (SUP M:A. f M) = space (f a)"
    and sets_SUP: "sets (SUP M:A. f M) = sets (f a)"
by(rule space_Sup[OF A a(2) imageI[OF a(1)]] sets_Sup[OF A a(2) imageI[OF a(1)]])+

lemma emeasure_SUP:
  assumes A: "Complete_Partial_Order.chain op \<le> (f ` A)" "A \<noteq> {}"
  assumes "X \<in> sets (SUP M:A. f M)"
  shows "emeasure (SUP M:A. f M) X = (SUP M:A. emeasure (f M)) X"
using \<open>X \<in> _\<close> by(subst emeasure_Sup[OF A(1)]; simp add: A)

end
