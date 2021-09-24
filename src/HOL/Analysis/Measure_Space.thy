(*  Title:      HOL/Analysis/Measure_Space.thy
    Author:     Lawrence C Paulson
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

section \<open>Measure Spaces\<close>

theory Measure_Space
imports
  Measurable "HOL-Library.Extended_Nonnegative_Real"
begin

subsection\<^marker>\<open>tag unimportant\<close> "Relate extended reals and the indicator function"

lemma suminf_cmult_indicator:
  fixes f :: "nat \<Rightarrow> ennreal"
  assumes "disjoint_family A" "x \<in> A i"
  shows "(\<Sum>n. f n * indicator (A n) x) = f i"
proof -
  have **: "\<And>n. f n * indicator (A n) x = (if n = i then f n else 0 :: ennreal)"
    using \<open>x \<in> A i\<close> assms unfolding disjoint_family_on_def indicator_def by auto
  then have "\<And>n. (\<Sum>j<n. f j * indicator (A j) x) = (if i < n then f i else 0 :: ennreal)"
    by (auto simp: sum.If_cases)
  moreover have "(SUP n. if i < n then f i else 0) = (f i :: ennreal)"
  proof (rule SUP_eqI)
    fix y :: ennreal assume "\<And>n. n \<in> UNIV \<Longrightarrow> (if i < n then f i else 0) \<le> y"
    from this[of "Suc i"] show "f i \<le> y" by auto
  qed (insert assms, simp)
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

lemma sum_indicator_disjoint_family:
  fixes f :: "'d \<Rightarrow> 'e::semiring_1"
  assumes d: "disjoint_family_on A P" and "x \<in> A j" and "finite P" and "j \<in> P"
  shows "(\<Sum>i\<in>P. f i * indicator (A i) x) = f j"
proof -
  have "P \<inter> {i. x \<in> A i} = {j}"
    using d \<open>x \<in> A j\<close> \<open>j \<in> P\<close> unfolding disjoint_family_on_def
    by auto
  with \<open>finite P\<close> show ?thesis
    by (simp add: indicator_def)
qed

text \<open>
  The type for emeasure spaces is already defined in \<^theory>\<open>HOL-Analysis.Sigma_Algebra\<close>, as it
  is also used to represent sigma algebras (with an arbitrary emeasure).
\<close>

subsection\<^marker>\<open>tag unimportant\<close> "Extend binary sets"

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

subsection\<^marker>\<open>tag unimportant\<close> \<open>Properties of a premeasure \<^term>\<open>\<mu>\<close>\<close>

text \<open>
  The definitions for \<^const>\<open>positive\<close> and \<^const>\<open>countably_additive\<close> should be here, by they are
  necessary to define \<^typ>\<open>'a measure\<close> in \<^theory>\<open>HOL-Analysis.Sigma_Algebra\<close>.
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
    using fin_not_empty F_subset by (rule sum.mono_neutral_left) auto
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
  assume count_sum: "\<forall>A. range A \<subseteq> M \<longrightarrow> disjoint_family A \<longrightarrow> \<Union>(A ` UNIV) \<in> M \<longrightarrow> (\<Sum>i. f (A i)) = f (\<Union>(A ` UNIV))"
  fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> M" "incseq A" "(\<Union>i. A i) \<in> M"
  then have dA: "range (disjointed A) \<subseteq> M" by (auto simp: range_disjointed_sets)
  with count_sum[THEN spec, of "disjointed A"] A(3)
  have f_UN: "(\<Sum>i. f (disjointed A i)) = f (\<Union>i. A i)"
    by (auto simp: UN_disjointed_eq disjoint_family_disjointed)
  moreover have "(\<lambda>n. (\<Sum>i<n. f (disjointed A i))) \<longlonglongrightarrow> (\<Sum>i. f (disjointed A i))"
    using f(1)[unfolded positive_def] dA
    by (auto intro!: summable_LIMSEQ)
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
  from INF_Lim[OF decseq_f this]
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

subsection\<^marker>\<open>tag unimportant\<close> \<open>Properties of \<^const>\<open>emeasure\<close>\<close>

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

lemma emeasure_Un:
  "A \<in> sets M \<Longrightarrow> B \<in> sets M \<Longrightarrow> emeasure M (A \<union> B) = emeasure M A + emeasure M (B - A)"
  using plus_emeasure[of A M "B - A"] by auto

lemma emeasure_Un_Int:
  assumes "A \<in> sets M" "B \<in> sets M"
  shows "emeasure M A + emeasure M B = emeasure M (A \<union> B) + emeasure M (A \<inter> B)"
proof -
  have "A = (A-B) \<union> (A \<inter> B)" by auto
  then have "emeasure M A = emeasure M (A-B) + emeasure M (A \<inter> B)"
    by (metis Diff_Diff_Int Diff_disjoint assms plus_emeasure sets.Diff)
  moreover have "A \<union> B = (A-B) \<union> B" by auto
  then have "emeasure M (A \<union> B) = emeasure M (A-B) + emeasure M B"
    by (metis Diff_disjoint Int_commute assms plus_emeasure sets.Diff)
  ultimately show ?thesis by (metis add.assoc add.commute)
qed

lemma sum_emeasure:
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

lemma INF_emeasure_decseq':
  assumes A: "\<And>i. A i \<in> sets M" and "decseq A"
  and finite: "\<exists>i. emeasure M (A i) \<noteq> \<infinity>"
  shows "(INF n. emeasure M (A n)) = emeasure M (\<Inter>i. A i)"
proof -
  from finite obtain i where i: "emeasure M (A i) < \<infinity>"
    by (auto simp: less_top)
  have fin: "i \<le> j \<Longrightarrow> emeasure M (A j) < \<infinity>" for j
    by (rule le_less_trans[OF emeasure_mono i]) (auto intro!: decseqD[OF \<open>decseq A\<close>] A)

  have "(INF n. emeasure M (A n)) = (INF n. emeasure M (A (n + i)))"
  proof (rule INF_eq)
    show "\<exists>j\<in>UNIV. emeasure M (A (j + i)) \<le> emeasure M (A i')" for i'
      by (intro bexI[of _ i'] emeasure_mono decseqD[OF \<open>decseq A\<close>] A) auto
  qed auto
  also have "\<dots> = emeasure M (INF n. (A (n + i)))"
    using A \<open>decseq A\<close> fin by (intro INF_emeasure_decseq) (auto simp: decseq_def less_top)
  also have "(INF n. (A (n + i))) = (INF n. A n)"
    by (meson INF_eq UNIV_I assms(2) decseqD le_add1)
  finally show ?thesis .
qed

lemma emeasure_INT_decseq_subset:
  fixes F :: "nat \<Rightarrow> 'a set"
  assumes I: "I \<noteq> {}" and F: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<le> j \<Longrightarrow> F j \<subseteq> F i"
  assumes F_sets[measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> sets M"
    and fin: "\<And>i. i \<in> I \<Longrightarrow> emeasure M (F i) \<noteq> \<infinity>"
  shows "emeasure M (\<Inter>i\<in>I. F i) = (INF i\<in>I. emeasure M (F i))"
proof cases
  assume "finite I"
  have "(\<Inter>i\<in>I. F i) = F (Max I)"
    using I \<open>finite I\<close> by (intro antisym INF_lower INF_greatest F) auto
  moreover have "(INF i\<in>I. emeasure M (F i)) = emeasure M (F (Max I))"
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
  also have "\<dots> = (INF i\<in>I. emeasure M (F i))"
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

lemma emeasure_eq_sum_singleton:
  assumes "finite S" "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  shows "emeasure M S = (\<Sum>x\<in>S. emeasure M {x})"
  using sum_emeasure[of "\<lambda>x. {x}" S M] assms
  by (auto simp: disjoint_family_on_def subset_eq)

lemma sum_emeasure_cover:
  assumes "finite S" and "A \<in> sets M" and br_in_M: "B ` S \<subseteq> sets M"
  assumes A: "A \<subseteq> (\<Union>i\<in>S. B i)"
  assumes disj: "disjoint_family_on B S"
  shows "emeasure M A = (\<Sum>i\<in>S. emeasure M (A \<inter> (B i)))"
proof -
  have "(\<Sum>i\<in>S. emeasure M (A \<inter> (B i))) = emeasure M (\<Union>i\<in>S. A \<inter> (B i))"
  proof (rule sum_emeasure)
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
    using \<open>finite A\<close> by (subst emeasure_eq_sum_singleton) (auto dest: finite_subset)
  also have "\<dots> = (\<Sum>a\<in>X. emeasure N {a})"
    using X eq by (auto intro!: sum.cong)
  also have "\<dots> = emeasure N X"
    using X \<open>finite A\<close> by (subst emeasure_eq_sum_singleton) (auto dest: finite_subset)
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

lemma space_empty: "space M = {} \<Longrightarrow> M = count_space {}"
  by (rule measure_eqI) (simp_all add: space_empty_iff)

lemma measure_eqI_generator_eq_countable:
  fixes M N :: "'a measure" and E :: "'a set set" and A :: "'a set set"
  assumes E: "Int_stable E" "E \<subseteq> Pow \<Omega>" "\<And>X. X \<in> E \<Longrightarrow> emeasure M X = emeasure N X"
    and sets: "sets M = sigma_sets \<Omega> E" "sets N = sigma_sets \<Omega> E"
  and A: "A \<subseteq> E" "(\<Union>A) = \<Omega>" "countable A" "\<And>a. a \<in> A \<Longrightarrow> emeasure M a \<noteq> \<infinity>"
  shows "M = N"
proof cases
  assume "\<Omega> = {}"
  have *: "sigma_sets \<Omega> E = sets (sigma \<Omega> E)"
    using E(2) by simp
  have "space M = \<Omega>" "space N = \<Omega>"
    using sets E(2) unfolding * by (auto dest: sets_eq_imp_space_eq simp del: sets_measure_of)
  then show "M = N"
    unfolding \<open>\<Omega> = {}\<close> by (auto dest: space_empty)
next
  assume "\<Omega> \<noteq> {}" with \<open>\<Union>A = \<Omega>\<close> have "A \<noteq> {}" by auto
  from this \<open>countable A\<close> have rng: "range (from_nat_into A) = A"
    by (rule range_from_nat_into)
  show "M = N"
  proof (rule measure_eqI_generator_eq[OF E sets])
    show "range (from_nat_into A) \<subseteq> E"
      unfolding rng using \<open>A \<subseteq> E\<close> .
    show "(\<Union>i. from_nat_into A i) = \<Omega>"
      unfolding rng using \<open>\<Union>A = \<Omega>\<close> .
    show "emeasure M (from_nat_into A i) \<noteq> \<infinity>" for i
      using rng by (intro A) auto
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

definition\<^marker>\<open>tag important\<close> null_sets :: "'a measure \<Rightarrow> 'a set set" where
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

lemma emeasure_Un':
  assumes "A \<in> sets M" "B \<in> sets M" "A \<inter> B \<in> null_sets M"
  shows   "emeasure M (A \<union> B) = emeasure M A + emeasure M B"
proof -
  have "A \<union> B = A \<union> (B - A \<inter> B)" by blast
  also have "emeasure M \<dots> = emeasure M A + emeasure M (B - A \<inter> B)"
    using assms by (subst plus_emeasure) auto
  also have "emeasure M (B - A \<inter> B) = emeasure M B"
    using assms by (intro emeasure_Diff_null_set) auto
  finally show ?thesis .
qed

subsection \<open>The almost everywhere filter (i.e.\ quantifier)\<close>

definition\<^marker>\<open>tag important\<close> ae_filter :: "'a measure \<Rightarrow> 'a filter" where
  "ae_filter M = (INF N\<in>null_sets M. principal (space M - N))"

abbreviation almost_everywhere :: "'a measure \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "almost_everywhere M P \<equiv> eventually P (ae_filter M)"

syntax
  "_almost_everywhere" :: "pttrn \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool" ("AE _ in _. _" [0,0,10] 10)

translations
  "AE x in M. P" \<rightleftharpoons> "CONST almost_everywhere M (\<lambda>x. P)"

abbreviation
  "set_almost_everywhere A M P \<equiv> AE x in M. x \<in> A \<longrightarrow> P x"

syntax
  "_set_almost_everywhere" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool"
  ("AE _\<in>_ in _./ _" [0,0,0,10] 10)

translations
  "AE x\<in>A in M. P" \<rightleftharpoons> "CONST set_almost_everywhere A M (\<lambda>x. P)"

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

lemma AE_E3:
  assumes "AE x in M. P x"
  obtains N where "\<And>x. x \<in> space M - N \<Longrightarrow> P x" "N \<in> null_sets M"
using assms unfolding eventually_ae_filter by auto

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

text \<open>The next lemma is convenient to combine with a lemma whose conclusion is of the
form \<open>AE x in M. P x = Q x\<close>: for such a lemma, there is no \<open>[symmetric]\<close> variant,
but using \<open>AE_symmetric[OF...]\<close> will replace it.\<close>

(* depricated replace by laws about eventually *)
lemma
  shows AE_iffI: "AE x in M. P x \<Longrightarrow> AE x in M. P x \<longleftrightarrow> Q x \<Longrightarrow> AE x in M. Q x"
    and AE_disjI1: "AE x in M. P x \<Longrightarrow> AE x in M. P x \<or> Q x"
    and AE_disjI2: "AE x in M. Q x \<Longrightarrow> AE x in M. P x \<or> Q x"
    and AE_conjI: "AE x in M. P x \<Longrightarrow> AE x in M. Q x \<Longrightarrow> AE x in M. P x \<and> Q x"
    and AE_conj_iff[simp]: "(AE x in M. P x \<and> Q x) \<longleftrightarrow> (AE x in M. P x) \<and> (AE x in M. Q x)"
  by auto

lemma AE_symmetric:
  assumes "AE x in M. P x = Q x"
  shows "AE x in M. Q x = P x"
  using assms by auto

lemma AE_impI:
  "(P \<Longrightarrow> AE x in M. Q x) \<Longrightarrow> AE x in M. P \<longrightarrow> Q x"
  by fastforce

lemma AE_measure:
  assumes AE: "AE x in M. P x" and sets: "{x\<in>space M. P x} \<in> sets M" (is "?P \<in> sets M")
  shows "emeasure M {x\<in>space M. P x} = emeasure M (space M)"
proof -
  from AE_E[OF AE] obtain N
    where N: "{x \<in> space M. \<not> P x} \<subseteq> N" "emeasure M N = 0" "N \<in> sets M"
    by auto
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

lemma AE_cong_simp: "M = N \<Longrightarrow> (\<And>x. x \<in> space N =simp=> P x = Q x) \<Longrightarrow> (AE x in M. P x) \<longleftrightarrow> (AE x in N. Q x)"
  by (auto simp: simp_implies_def)

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

lemma AE_ball_countable':
  "(\<And>N. N \<in> I \<Longrightarrow> AE x in M. P N x) \<Longrightarrow> countable I \<Longrightarrow> AE x in M. \<forall>N \<in> I. P N x"
  unfolding AE_ball_countable by simp

lemma AE_pairwise: "countable F \<Longrightarrow> pairwise (\<lambda>A B. AE x in M. R x A B) F \<longleftrightarrow> (AE x in M. pairwise (R x) F)"
  unfolding pairwise_alt by (simp add: AE_ball_countable)

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

lemma emeasure_0_AE:
  assumes "emeasure M (space M) = 0"
  shows "AE x in M. P x"
using eventually_ae_filter assms by blast

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

locale\<^marker>\<open>tag important\<close> sigma_finite_measure =
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
        using F by (auto simp: sum_Pinfty less_top)
      finally show ?thesis by simp
    qed
    show "incseq (\<lambda>n. \<Union>i\<le>n. F i)"
      by (force simp: incseq_def)
  qed
qed

lemma (in sigma_finite_measure) approx_PInf_emeasure_with_finite:
  fixes C::real
  assumes W_meas: "W \<in> sets M"
      and W_inf: "emeasure M W = \<infinity>"
  obtains Z where "Z \<in> sets M" "Z \<subseteq> W" "emeasure M Z < \<infinity>" "emeasure M Z > C"
proof -
  obtain A :: "nat \<Rightarrow> 'a set"
    where A: "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" "\<And>i. emeasure M (A i) \<noteq> \<infinity>" "incseq A"
    using sigma_finite_incseq by blast
  define B where "B = (\<lambda>i. W \<inter> A i)"
  have B_meas: "\<And>i. B i \<in> sets M" using W_meas \<open>range A \<subseteq> sets M\<close> B_def by blast
  have b: "\<And>i. B i \<subseteq> W" using B_def by blast

  { fix i
    have "emeasure M (B i) \<le> emeasure M (A i)"
      using A by (intro emeasure_mono) (auto simp: B_def)
    also have "emeasure M (A i) < \<infinity>"
      using \<open>\<And>i. emeasure M (A i) \<noteq> \<infinity>\<close> by (simp add: less_top)
    finally have "emeasure M (B i) < \<infinity>" . }
  note c = this

  have "W = (\<Union>i. B i)" using B_def \<open>(\<Union>i. A i) = space M\<close> W_meas by auto
  moreover have "incseq B" using B_def \<open>incseq A\<close> by (simp add: incseq_def subset_eq)
  ultimately have "(\<lambda>i. emeasure M (B i)) \<longlonglongrightarrow> emeasure M W" using W_meas B_meas
    by (simp add: B_meas Lim_emeasure_incseq image_subset_iff)
  then have "(\<lambda>i. emeasure M (B i)) \<longlonglongrightarrow> \<infinity>" using W_inf by simp
  from order_tendstoD(1)[OF this, of C]
  obtain i where d: "emeasure M (B i) > C"
    by (auto simp: eventually_sequentially)
  have "B i \<in> sets M" "B i \<subseteq> W" "emeasure M (B i) < \<infinity>" "emeasure M (B i) > C"
    using B_meas b c d by auto
  then show ?thesis using that by blast
qed

subsection \<open>Measure space induced by distribution of \<^const>\<open>measurable\<close>-functions\<close>

definition\<^marker>\<open>tag important\<close> distr :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b measure" where
"distr M N f =
  measure_of (space N) (sets N) (\<lambda>A. emeasure M (f -` A \<inter> space M))"

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

lemma distr_id2: "sets M = sets N \<Longrightarrow> distr N M (\<lambda>x. x) = N"
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
  from AE[THEN AE_E] obtain N
    where "{x \<in> space (distr M M' f). \<not> P x} \<subseteq> N"
      "emeasure (distr M M' f) N = 0"
      "N \<in> sets (distr M M' f)"
    by auto
  with f show ?thesis
    by (simp add: eventually_ae_filter, intro bexI[of _ "f -` N \<inter> space M"])
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

proposition distr_distr:
  "g \<in> measurable N L \<Longrightarrow> f \<in> measurable M N \<Longrightarrow> distr (distr M N f) L g = distr M L (g \<circ> f)"
  by (auto simp add: emeasure_distr measurable_space
           intro!: arg_cong[where f="emeasure M"] measure_eqI)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Real measure values\<close>

lemma ring_of_finite_sets: "ring_of_sets (space M) {A\<in>sets M. emeasure M A \<noteq> top}"
proof (rule ring_of_setsI)
  show "a \<in> {A \<in> sets M. emeasure M A \<noteq> top} \<Longrightarrow> b \<in> {A \<in> sets M. emeasure M A \<noteq> top} \<Longrightarrow>
    a \<union> b \<in> {A \<in> sets M. emeasure M A \<noteq> top}" for a b
    using emeasure_subadditive[of a M b] by (auto simp: top_unique)

  show "a \<in> {A \<in> sets M. emeasure M A \<noteq> top} \<Longrightarrow> b \<in> {A \<in> sets M. emeasure M A \<noteq> top} \<Longrightarrow>
    a - b \<in> {A \<in> sets M. emeasure M A \<noteq> top}" for a b
    using emeasure_mono[of "a - b" a M] by (auto simp: top_unique)
qed (auto dest: sets.sets_into_space)

lemma measure_nonneg[simp]: "0 \<le> measure M A"
  unfolding measure_def by auto

lemma measure_nonneg' [simp]: "\<not> measure M A < 0"
  using measure_nonneg not_le by blast

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
  by (simp add: measure_def)

lemma measure_eq_emeasure_eq_ennreal: "0 \<le> x \<Longrightarrow> emeasure M A = ennreal x \<Longrightarrow> measure M A = x"
  using emeasure_eq_ennreal_measure[of M A]
  by (cases "A \<in> M") (auto simp: measure_notin_sets emeasure_notin_sets)

lemma enn2real_plus:"a < top \<Longrightarrow> b < top \<Longrightarrow> enn2real (a + b) = enn2real a + enn2real b"
  by (simp add: enn2real_def plus_ennreal.rep_eq real_of_ereal_add less_top
           del: real_of_ereal_enn2ereal)

lemma enn2real_sum:"(\<And>i. i \<in> I \<Longrightarrow> f i < top) \<Longrightarrow> enn2real (sum f I) = sum (enn2real \<circ> f) I"
  by (induction I rule: infinite_finite_induct) (auto simp: enn2real_plus)

lemma measure_eq_AE:
  assumes iff: "AE x in M. x \<in> A \<longleftrightarrow> x \<in> B"
  assumes A: "A \<in> sets M" and B: "B \<in> sets M"
  shows "measure M A = measure M B"
  using assms emeasure_eq_AE[OF assms] by (simp add: measure_def)

lemma measure_Union:
  "emeasure M A \<noteq> \<infinity> \<Longrightarrow> emeasure M B \<noteq> \<infinity> \<Longrightarrow> A \<in> sets M \<Longrightarrow> B \<in> sets M \<Longrightarrow> A \<inter> B = {} \<Longrightarrow>
    measure M (A \<union> B) = measure M A + measure M B"
  by (simp add: measure_def plus_emeasure[symmetric] enn2real_plus less_top)

lemma disjoint_family_on_insert:
  "i \<notin> I \<Longrightarrow> disjoint_family_on A (insert i I) \<longleftrightarrow> A i \<inter> (\<Union>i\<in>I. A i) = {} \<and> disjoint_family_on A I"
  by (fastforce simp: disjoint_family_on_def)

lemma measure_finite_Union:
  "finite S \<Longrightarrow> A`S \<subseteq> sets M \<Longrightarrow> disjoint_family_on A S \<Longrightarrow> (\<And>i. i \<in> S \<Longrightarrow> emeasure M (A i) \<noteq> \<infinity>) \<Longrightarrow>
    measure M (\<Union>i\<in>S. A i) = (\<Sum>i\<in>S. measure M (A i))"
  by (induction S rule: finite_induct)
     (auto simp: disjoint_family_on_insert measure_Union sum_emeasure[symmetric] sets.countable_UN'[OF countable_finite])

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
    by (subst (asm) (2) emeasure_eq_ennreal_measure) simp_all
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
    apply (auto simp flip: ennreal_plus)
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
    by (simp_all add: sum_nonneg emeasure_eq_ennreal_measure)
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

lemma measure_Un_null_set: "A \<in> sets M \<Longrightarrow> B \<in> null_sets M \<Longrightarrow> measure M (A \<union> B) = measure M A"
  by (simp add: measure_def emeasure_Un_null_set)

lemma measure_Diff_null_set: "A \<in> sets M \<Longrightarrow> B \<in> null_sets M \<Longrightarrow> measure M (A - B) = measure M A"
  by (simp add: measure_def emeasure_Diff_null_set)

lemma measure_eq_sum_singleton:
  "finite S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M) \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> emeasure M {x} \<noteq> \<infinity>) \<Longrightarrow>
    measure M S = (\<Sum>x\<in>S. measure M {x})"
  using emeasure_eq_sum_singleton[of S M]
  by (intro measure_eq_emeasure_eq_ennreal) (auto simp: sum_nonneg emeasure_eq_ennreal_measure)

lemma Lim_measure_incseq:
  assumes A: "range A \<subseteq> sets M" "incseq A" and fin: "emeasure M (\<Union>i. A i) \<noteq> \<infinity>"
  shows "(\<lambda>i. measure M (A i)) \<longlonglongrightarrow> measure M (\<Union>i. A i)"
proof (rule tendsto_ennrealD)
  have "ennreal (measure M (\<Union>i. A i)) = emeasure M (\<Union>i. A i)"
    using fin by (auto simp: emeasure_eq_ennreal_measure)
  moreover have "ennreal (measure M (A i)) = emeasure M (A i)" for i
    using assms emeasure_mono[of "A _" "\<Union>i. A i" M]
    by (intro emeasure_eq_ennreal_measure[symmetric]) (auto simp: less_top UN_upper intro: le_less_trans)
  ultimately show "(\<lambda>x. ennreal (measure M (A x))) \<longlonglongrightarrow> ennreal (measure M (\<Union>i. A i))"
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
  ultimately show "(\<lambda>x. ennreal (measure M (A x))) \<longlonglongrightarrow> ennreal (measure M (\<Inter>i. A i))"
    using fin A by (auto intro!: Lim_emeasure_decseq)
qed auto

subsection \<open>Set of measurable sets with finite measure\<close>

definition\<^marker>\<open>tag important\<close> fmeasurable :: "'a measure \<Rightarrow> 'a set set" where
"fmeasurable M = {A\<in>sets M. emeasure M A < \<infinity>}"

lemma fmeasurableD[dest, measurable_dest]: "A \<in> fmeasurable M \<Longrightarrow> A \<in> sets M"
  by (auto simp: fmeasurable_def)

lemma fmeasurableD2: "A \<in> fmeasurable M \<Longrightarrow> emeasure M A \<noteq> top"
  by (auto simp: fmeasurable_def)

lemma fmeasurableI: "A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> A \<in> fmeasurable M"
  by (auto simp: fmeasurable_def)

lemma fmeasurableI_null_sets: "A \<in> null_sets M \<Longrightarrow> A \<in> fmeasurable M"
  by (auto simp: fmeasurable_def)

lemma fmeasurableI2: "A \<in> fmeasurable M \<Longrightarrow> B \<subseteq> A \<Longrightarrow> B \<in> sets M \<Longrightarrow> B \<in> fmeasurable M"
  using emeasure_mono[of B A M] by (auto simp: fmeasurable_def)

lemma measure_mono_fmeasurable:
  "A \<subseteq> B \<Longrightarrow> A \<in> sets M \<Longrightarrow> B \<in> fmeasurable M \<Longrightarrow> measure M A \<le> measure M B"
  by (auto simp: measure_def fmeasurable_def intro!: emeasure_mono enn2real_mono)

lemma emeasure_eq_measure2: "A \<in> fmeasurable M \<Longrightarrow> emeasure M A = measure M A"
  by (simp add: emeasure_eq_ennreal_measure fmeasurable_def less_top)

interpretation fmeasurable: ring_of_sets "space M" "fmeasurable M"
proof (rule ring_of_setsI)
  show "fmeasurable M \<subseteq> Pow (space M)" "{} \<in> fmeasurable M"
    by (auto simp: fmeasurable_def dest: sets.sets_into_space)
  fix a b assume *: "a \<in> fmeasurable M" "b \<in> fmeasurable M"
  then have "emeasure M (a \<union> b) \<le> emeasure M a + emeasure M b"
    by (intro emeasure_subadditive) auto
  also have "\<dots> < top"
    using * by (auto simp: fmeasurable_def)
  finally show  "a \<union> b \<in> fmeasurable M"
    using * by (auto intro: fmeasurableI)
  show "a - b \<in> fmeasurable M"
    using emeasure_mono[of "a - b" a M] * by (auto simp: fmeasurable_def)
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>Measurable sets formed by unions and intersections\<close>

lemma fmeasurable_Diff: "A \<in> fmeasurable M \<Longrightarrow> B \<in> sets M \<Longrightarrow> A - B \<in> fmeasurable M"
  using fmeasurableI2[of A M "A - B"] by auto

lemma fmeasurable_Int_fmeasurable:
   "\<lbrakk>S \<in> fmeasurable M; T \<in> sets M\<rbrakk> \<Longrightarrow> (S \<inter> T) \<in> fmeasurable M"
  by (meson fmeasurableD fmeasurableI2 inf_le1 sets.Int)

lemma fmeasurable_UN:
  assumes "countable I" "\<And>i. i \<in> I \<Longrightarrow> F i \<subseteq> A" "\<And>i. i \<in> I \<Longrightarrow> F i \<in> sets M" "A \<in> fmeasurable M"
  shows "(\<Union>i\<in>I. F i) \<in> fmeasurable M"
proof (rule fmeasurableI2)
  show "A \<in> fmeasurable M" "(\<Union>i\<in>I. F i) \<subseteq> A" using assms by auto
  show "(\<Union>i\<in>I. F i) \<in> sets M"
    using assms by (intro sets.countable_UN') auto
qed

lemma fmeasurable_INT:
  assumes "countable I" "i \<in> I" "\<And>i. i \<in> I \<Longrightarrow> F i \<in> sets M" "F i \<in> fmeasurable M"
  shows "(\<Inter>i\<in>I. F i) \<in> fmeasurable M"
proof (rule fmeasurableI2)
  show "F i \<in> fmeasurable M" "(\<Inter>i\<in>I. F i) \<subseteq> F i"
    using assms by auto
  show "(\<Inter>i\<in>I. F i) \<in> sets M"
    using assms by (intro sets.countable_INT') auto
qed

lemma measurable_measure_Diff:
  assumes "A \<in> fmeasurable M" "B \<in> sets M" "B \<subseteq> A"
  shows "measure M (A - B) = measure M A - measure M B"
  by (simp add: assms fmeasurableD fmeasurableD2 measure_Diff)

lemma measurable_Un_null_set:
  assumes "B \<in> null_sets M"
  shows "(A \<union> B \<in> fmeasurable M \<and> A \<in> sets M) \<longleftrightarrow> A \<in> fmeasurable M"
  using assms  by (fastforce simp add: fmeasurable.Un fmeasurableI_null_sets intro: fmeasurableI2)

lemma measurable_Diff_null_set:
  assumes "B \<in> null_sets M"
  shows "(A - B) \<in> fmeasurable M \<and> A \<in> sets M \<longleftrightarrow> A \<in> fmeasurable M"
  using assms
  by (metis Un_Diff_cancel2 fmeasurable.Diff fmeasurableD fmeasurableI_null_sets measurable_Un_null_set)

lemma fmeasurable_Diff_D:
    assumes m: "T - S \<in> fmeasurable M" "S \<in> fmeasurable M" and sub: "S \<subseteq> T"
    shows "T \<in> fmeasurable M"
proof -
  have "T = S \<union> (T - S)"
    using assms by blast
  then show ?thesis
    by (metis m fmeasurable.Un)
qed

lemma measure_Un2:
  "A \<in> fmeasurable M \<Longrightarrow> B \<in> fmeasurable M \<Longrightarrow> measure M (A \<union> B) = measure M A + measure M (B - A)"
  using measure_Union[of M A "B - A"] by (auto simp: fmeasurableD2 fmeasurable.Diff)

lemma measure_Un3:
  assumes "A \<in> fmeasurable M" "B \<in> fmeasurable M"
  shows "measure M (A \<union> B) = measure M A + measure M B - measure M (A \<inter> B)"
proof -
  have "measure M (A \<union> B) = measure M A + measure M (B - A)"
    using assms by (rule measure_Un2)
  also have "B - A = B - (A \<inter> B)"
    by auto
  also have "measure M (B - (A \<inter> B)) = measure M B - measure M (A \<inter> B)"
    using assms by (intro measure_Diff) (auto simp: fmeasurable_def)
  finally show ?thesis
    by simp
qed

lemma measure_Un_AE:
  "AE x in M. x \<notin> A \<or> x \<notin> B \<Longrightarrow> A \<in> fmeasurable M \<Longrightarrow> B \<in> fmeasurable M \<Longrightarrow>
  measure M (A \<union> B) = measure M A + measure M B"
  by (subst measure_Un2) (auto intro!: measure_eq_AE)

lemma measure_UNION_AE:
  assumes I: "finite I"
  shows "(\<And>i. i \<in> I \<Longrightarrow> F i \<in> fmeasurable M) \<Longrightarrow> pairwise (\<lambda>i j. AE x in M. x \<notin> F i \<or> x \<notin> F j) I \<Longrightarrow>
    measure M (\<Union>i\<in>I. F i) = (\<Sum>i\<in>I. measure M (F i))"
  unfolding AE_pairwise[OF countable_finite, OF I]
  using I
proof (induction I rule: finite_induct)
  case (insert x I)
  have "measure M (F x \<union> \<Union>(F ` I)) = measure M (F x) + measure M (\<Union>(F ` I))"
    by (rule measure_Un_AE) (use insert in \<open>auto simp: pairwise_insert\<close>)
    with insert show ?case
      by (simp add: pairwise_insert )
qed simp

lemma measure_UNION':
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> F i \<in> fmeasurable M) \<Longrightarrow> pairwise (\<lambda>i j. disjnt (F i) (F j)) I \<Longrightarrow>
    measure M (\<Union>i\<in>I. F i) = (\<Sum>i\<in>I. measure M (F i))"
  by (intro measure_UNION_AE) (auto simp: disjnt_def elim!: pairwise_mono intro!: always_eventually)

lemma measure_Union_AE:
  "finite F \<Longrightarrow> (\<And>S. S \<in> F \<Longrightarrow> S \<in> fmeasurable M) \<Longrightarrow> pairwise (\<lambda>S T. AE x in M. x \<notin> S \<or> x \<notin> T) F \<Longrightarrow>
    measure M (\<Union>F) = (\<Sum>S\<in>F. measure M S)"
  using measure_UNION_AE[of F "\<lambda>x. x" M] by simp

lemma measure_Union':
  "finite F \<Longrightarrow> (\<And>S. S \<in> F \<Longrightarrow> S \<in> fmeasurable M) \<Longrightarrow> pairwise disjnt F \<Longrightarrow> measure M (\<Union>F) = (\<Sum>S\<in>F. measure M S)"
  using measure_UNION'[of F "\<lambda>x. x" M] by simp

lemma measure_Un_le:
  assumes "A \<in> sets M" "B \<in> sets M" shows "measure M (A \<union> B) \<le> measure M A + measure M B"
proof cases
  assume "A \<in> fmeasurable M \<and> B \<in> fmeasurable M"
  with measure_subadditive[of A M B] assms show ?thesis
    by (auto simp: fmeasurableD2)
next
  assume "\<not> (A \<in> fmeasurable M \<and> B \<in> fmeasurable M)"
  then have "A \<union> B \<notin> fmeasurable M"
    using fmeasurableI2[of "A \<union> B" M A] fmeasurableI2[of "A \<union> B" M B] assms by auto
  with assms show ?thesis
    by (auto simp: fmeasurable_def measure_def less_top[symmetric])
qed

lemma measure_UNION_le:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> F i \<in> sets M) \<Longrightarrow> measure M (\<Union>i\<in>I. F i) \<le> (\<Sum>i\<in>I. measure M (F i))"
proof (induction I rule: finite_induct)
  case (insert i I)
  then have "measure M (\<Union>i\<in>insert i I. F i) = measure M (F i \<union> \<Union> (F ` I))"
    by simp
  also from insert have "measure M (F i \<union> \<Union> (F ` I)) \<le> measure M (F i) + measure M (\<Union> (F ` I))"
    by (intro measure_Un_le sets.finite_Union) auto
  also have "measure M (\<Union>i\<in>I. F i) \<le> (\<Sum>i\<in>I. measure M (F i))"
    using insert by auto
  finally show ?case
    using insert by simp
qed simp

lemma measure_Union_le:
  "finite F \<Longrightarrow> (\<And>S. S \<in> F \<Longrightarrow> S \<in> sets M) \<Longrightarrow> measure M (\<Union>F) \<le> (\<Sum>S\<in>F. measure M S)"
  using measure_UNION_le[of F "\<lambda>x. x" M] by simp

text\<open>Version for indexed union over a countable set\<close>
lemma
  assumes "countable I" and I: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> fmeasurable M"
    and bound: "\<And>I'. I' \<subseteq> I \<Longrightarrow> finite I' \<Longrightarrow> measure M (\<Union>i\<in>I'. A i) \<le> B"
  shows fmeasurable_UN_bound: "(\<Union>i\<in>I. A i) \<in> fmeasurable M" (is ?fm)
    and measure_UN_bound: "measure M (\<Union>i\<in>I. A i) \<le> B" (is ?m)
proof -
  have "B \<ge> 0"
    using bound by force
  have "?fm \<and> ?m"
  proof cases
    assume "I = {}"
    with \<open>B \<ge> 0\<close> show ?thesis
      by simp
  next
    assume "I \<noteq> {}"
    have "(\<Union>i\<in>I. A i) = (\<Union>i. (\<Union>n\<le>i. A (from_nat_into I n)))"
      by (subst range_from_nat_into[symmetric, OF \<open>I \<noteq> {}\<close> \<open>countable I\<close>]) auto
    then have "emeasure M (\<Union>i\<in>I. A i) = emeasure M (\<Union>i. (\<Union>n\<le>i. A (from_nat_into I n)))" by simp
    also have "\<dots> = (SUP i. emeasure M (\<Union>n\<le>i. A (from_nat_into I n)))"
      using I \<open>I \<noteq> {}\<close>[THEN from_nat_into] by (intro SUP_emeasure_incseq[symmetric]) (fastforce simp: incseq_Suc_iff)+
    also have "\<dots> \<le> B"
    proof (intro SUP_least)
      fix i :: nat
      have "emeasure M (\<Union>n\<le>i. A (from_nat_into I n)) = measure M (\<Union>n\<le>i. A (from_nat_into I n))"
        using I \<open>I \<noteq> {}\<close>[THEN from_nat_into] by (intro emeasure_eq_measure2 fmeasurable.finite_UN) auto
      also have "\<dots> = measure M (\<Union>n\<in>from_nat_into I ` {..i}. A n)"
        by simp
      also have "\<dots> \<le> B"
        by (intro ennreal_leI bound) (auto intro:  from_nat_into[OF \<open>I \<noteq> {}\<close>])
      finally show "emeasure M (\<Union>n\<le>i. A (from_nat_into I n)) \<le> ennreal B" .
    qed
    finally have *: "emeasure M (\<Union>i\<in>I. A i) \<le> B" .
    then have ?fm
      using I \<open>countable I\<close> by (intro fmeasurableI conjI) (auto simp: less_top[symmetric] top_unique)
    with * \<open>0\<le>B\<close> show ?thesis
      by (simp add: emeasure_eq_measure2)
  qed
  then show ?fm ?m by auto
qed

text\<open>Version for big union of a countable set\<close>
lemma
  assumes "countable \<D>"
    and meas: "\<And>D. D \<in> \<D> \<Longrightarrow> D \<in> fmeasurable M"
    and bound:  "\<And>\<E>. \<lbrakk>\<E> \<subseteq> \<D>; finite \<E>\<rbrakk> \<Longrightarrow> measure M (\<Union>\<E>) \<le> B"
 shows fmeasurable_Union_bound: "\<Union>\<D> \<in> fmeasurable M"  (is ?fm)
    and measure_Union_bound: "measure M (\<Union>\<D>) \<le> B"     (is ?m)
proof -
  have "B \<ge> 0"
    using bound by force
  have "?fm \<and> ?m"
  proof (cases "\<D> = {}")
    case True
    with \<open>B \<ge> 0\<close> show ?thesis
      by auto
  next
    case False
    then obtain D :: "nat \<Rightarrow> 'a set" where D: "\<D> = range D"
      using \<open>countable \<D>\<close> uncountable_def by force
      have 1: "\<And>i. D i \<in> fmeasurable M"
        by (simp add: D meas)
      have 2: "\<And>I'. finite I' \<Longrightarrow> measure M (\<Union>x\<in>I'. D x) \<le> B"
        by (simp add: D bound image_subset_iff)
      show ?thesis
        unfolding D
        by (intro conjI fmeasurable_UN_bound [OF _ 1 2] measure_UN_bound [OF _ 1 2]) auto
    qed
    then show ?fm ?m by auto
qed

text\<open>Version for indexed union over the type of naturals\<close>
lemma
  fixes S :: "nat \<Rightarrow> 'a set"
  assumes S: "\<And>i. S i \<in> fmeasurable M" and B: "\<And>n. measure M (\<Union>i\<le>n. S i) \<le> B"
  shows fmeasurable_countable_Union: "(\<Union>i. S i) \<in> fmeasurable M"
    and measure_countable_Union_le: "measure M (\<Union>i. S i) \<le> B"
proof -
  have mB: "measure M (\<Union>i\<in>I. S i) \<le> B" if "finite I" for I
  proof -
    have "(\<Union>i\<in>I. S i) \<subseteq> (\<Union>i\<le>Max I. S i)"
      using Max_ge that by force
    then have "measure M (\<Union>i\<in>I. S i) \<le> measure M (\<Union>i \<le> Max I. S i)"
      by (rule measure_mono_fmeasurable) (use S in \<open>blast+\<close>)
    then show ?thesis
      using B order_trans by blast
  qed
  show "(\<Union>i. S i) \<in> fmeasurable M"
    by (auto intro: fmeasurable_UN_bound [OF _ S mB])
  show "measure M (\<Union>n. S n) \<le> B"
    by (auto intro: measure_UN_bound [OF _ S mB])
qed

lemma measure_diff_le_measure_setdiff:
  assumes "S \<in> fmeasurable M" "T \<in> fmeasurable M"
  shows "measure M S - measure M T \<le> measure M (S - T)"
proof -
  have "measure M S \<le> measure M ((S - T) \<union> T)"
    by (simp add: assms fmeasurable.Un fmeasurableD measure_mono_fmeasurable)
  also have "\<dots> \<le> measure M (S - T) + measure M T"
    using assms by (blast intro: measure_Un_le)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma suminf_exist_split2:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes "summable f"
  shows "(\<lambda>n. (\<Sum>k. f(k+n))) \<longlonglongrightarrow> 0"
by (subst lim_sequentially, auto simp add: dist_norm suminf_exist_split[OF _ assms])

lemma emeasure_union_summable:
  assumes [measurable]: "\<And>n. A n \<in> sets M"
    and "\<And>n. emeasure M (A n) < \<infinity>" "summable (\<lambda>n. measure M (A n))"
  shows "emeasure M (\<Union>n. A n) < \<infinity>" "emeasure M (\<Union>n. A n) \<le> (\<Sum>n. measure M (A n))"
proof -
  define B where "B = (\<lambda>N. (\<Union>n\<in>{..<N}. A n))"
  have [measurable]: "B N \<in> sets M" for N unfolding B_def by auto
  have "(\<lambda>N. emeasure M (B N)) \<longlonglongrightarrow> emeasure M (\<Union>N. B N)"
    apply (rule Lim_emeasure_incseq) unfolding B_def by (auto simp add: SUP_subset_mono incseq_def)
  moreover have "emeasure M (B N) \<le> ennreal (\<Sum>n. measure M (A n))" for N
  proof -
    have *: "(\<Sum>n\<in>{..<N}. measure M (A n)) \<le> (\<Sum>n. measure M (A n))"
      using assms(3) measure_nonneg sum_le_suminf by blast

    have "emeasure M (B N) \<le> (\<Sum>n\<in>{..<N}. emeasure M (A n))"
      unfolding B_def by (rule emeasure_subadditive_finite, auto)
    also have "... = (\<Sum>n\<in>{..<N}. ennreal(measure M (A n)))"
      using assms(2) by (simp add: emeasure_eq_ennreal_measure less_top)
    also have "... = ennreal (\<Sum>n\<in>{..<N}. measure M (A n))"
      by auto
    also have "... \<le> ennreal (\<Sum>n. measure M (A n))"
      using * by (auto simp: ennreal_leI)
    finally show ?thesis by simp
  qed
  ultimately have "emeasure M (\<Union>N. B N) \<le> ennreal (\<Sum>n. measure M (A n))"
    by (simp add: Lim_bounded)
  then show "emeasure M (\<Union>n. A n) \<le> (\<Sum>n. measure M (A n))"
    unfolding B_def by (metis UN_UN_flatten UN_lessThan_UNIV)
  then show "emeasure M (\<Union>n. A n) < \<infinity>"
    by (auto simp: less_top[symmetric] top_unique)
qed

lemma borel_cantelli_limsup1:
  assumes [measurable]: "\<And>n. A n \<in> sets M"
    and "\<And>n. emeasure M (A n) < \<infinity>" "summable (\<lambda>n. measure M (A n))"
  shows "limsup A \<in> null_sets M"
proof -
  have "emeasure M (limsup A) \<le> 0"
  proof (rule LIMSEQ_le_const)
    have "(\<lambda>n. (\<Sum>k. measure M (A (k+n)))) \<longlonglongrightarrow> 0" by (rule suminf_exist_split2[OF assms(3)])
    then show "(\<lambda>n. ennreal (\<Sum>k. measure M (A (k+n)))) \<longlonglongrightarrow> 0"
      unfolding ennreal_0[symmetric] by (intro tendsto_ennrealI)
    have "emeasure M (limsup A) \<le> (\<Sum>k. measure M (A (k+n)))" for n
    proof -
      have I: "(\<Union>k\<in>{n..}. A k) = (\<Union>k. A (k+n))" by (auto, metis le_add_diff_inverse2, fastforce)
      have "emeasure M (limsup A) \<le> emeasure M (\<Union>k\<in>{n..}. A k)"
        by (rule emeasure_mono, auto simp add: limsup_INF_SUP)
      also have "... = emeasure M (\<Union>k. A (k+n))"
        using I by auto
      also have "... \<le> (\<Sum>k. measure M (A (k+n)))"
        apply (rule emeasure_union_summable)
        using assms summable_ignore_initial_segment[OF assms(3), of n] by auto
      finally show ?thesis by simp
    qed
    then show "\<exists>N. \<forall>n\<ge>N. emeasure M (limsup A) \<le> (\<Sum>k. measure M (A (k+n)))"
      by auto
  qed
  then show ?thesis using assms(1) measurable_limsup by auto
qed

lemma borel_cantelli_AE1:
  assumes [measurable]: "\<And>n. A n \<in> sets M"
    and "\<And>n. emeasure M (A n) < \<infinity>" "summable (\<lambda>n. measure M (A n))"
  shows "AE x in M. eventually (\<lambda>n. x \<in> space M - A n) sequentially"
proof -
  have "AE x in M. x \<notin> limsup A"
    using borel_cantelli_limsup1[OF assms] unfolding eventually_ae_filter by auto
  moreover
  {
    fix x assume "x \<notin> limsup A"
    then obtain N where "x \<notin> (\<Union>n\<in>{N..}. A n)" unfolding limsup_INF_SUP by blast
    then have "eventually (\<lambda>n. x \<notin> A n) sequentially" using eventually_sequentially by auto
  }
  ultimately show ?thesis by auto
qed

subsection \<open>Measure spaces with \<^term>\<open>emeasure M (space M) < \<infinity>\<close>\<close>

locale\<^marker>\<open>tag important\<close> finite_measure = sigma_finite_measure M for M +
  assumes finite_emeasure_space: "emeasure M (space M) \<noteq> top"

lemma finite_measureI[Pure.intro!]:
  "emeasure M (space M) \<noteq> \<infinity> \<Longrightarrow> finite_measure M"
  proof qed (auto intro!: exI[of _ "{space M}"])

lemma (in finite_measure) emeasure_finite[simp, intro]: "emeasure M A \<noteq> top"
  using finite_emeasure_space emeasure_space[of M A] by (auto simp: top_unique)

lemma (in finite_measure) fmeasurable_eq_sets: "fmeasurable M = sets M"
  by (auto simp: fmeasurable_def less_top[symmetric])

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

lemma (in finite_measure) finite_measure_eq_sum_singleton:
  assumes "finite S" and *: "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  shows "measure M S = (\<Sum>x\<in>S. measure M {x})"
  using measure_eq_sum_singleton[OF assms] by simp

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
    using finite_measure_eq_sum_singleton[OF s] by simp
  also have "\<dots> = (\<Sum> x \<in> s. measure M {SOME y. y \<in> s})" using prob_some by auto
  also have "\<dots> = real (card s) * measure M {(SOME x. x \<in> s)}"
    using sum_constant assms by simp
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

subsection\<^marker>\<open>tag unimportant\<close> \<open>Counting space\<close>

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
      then obtain i where i: "\<forall>j\<ge>i. F i = F j" ..
      with \<open>incseq F\<close> have "F j \<subseteq> F i" for j
        by (cases "i \<le> j") (auto simp: incseq_def)
      then have eq: "(\<Union>i. F i) = F i"
        by auto
      with i show ?thesis
        by (auto intro!: Lim_transform_eventually[OF tendsto_const] eventually_sequentiallyI[where c=i])
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
          then obtain k where "of_nat n \<le> ?M (F k)" ..
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
      ultimately show ?thesis by (simp only:) simp
         
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
  moreover from X have "f -` X \<inter> A = the_inv_into A f ` X"
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

subsection\<^marker>\<open>tag unimportant\<close> \<open>Measure restricted to space\<close>

lemma emeasure_restrict_space:
  assumes "\<Omega> \<inter> space M \<in> sets M" "A \<subseteq> \<Omega>"
  shows "emeasure (restrict_space M \<Omega>) A = emeasure M A"
proof (cases "A \<in> sets M")
  case True
  show ?thesis
  proof (rule emeasure_measure_of[OF restrict_space_def])
    show "(\<inter>) \<Omega> ` sets M \<subseteq> Pow (\<Omega> \<inter> space M)" "A \<in> sets (restrict_space M \<Omega>)"
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
  case False
  with assms have "A \<notin> sets (restrict_space M \<Omega>)"
    by (simp add: sets_restrict_space_iff)
  with False show ?thesis
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
  let ?C = "(\<inter>) A ` C"
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
      using A by (auto cong del: SUP_cong_simp)
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

subsection\<^marker>\<open>tag unimportant\<close> \<open>Null measure\<close>

definition null_measure :: "'a measure \<Rightarrow> 'a measure" where
"null_measure M = sigma (space M) (sets M)"

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

definition\<^marker>\<open>tag important\<close> scale_measure :: "ennreal \<Rightarrow> 'a measure \<Rightarrow> 'a measure" where
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


subsection \<open>Complete lattice structure on measures\<close>

lemma (in finite_measure) finite_measure_Diff':
  "A \<in> sets M \<Longrightarrow> B \<in> sets M \<Longrightarrow> measure M (A - B) = measure M A - measure M (A \<inter> B)"
  using finite_measure_Diff[of A "A \<inter> B"] by (auto simp: Diff_Int)

lemma (in finite_measure) finite_measure_Union':
  "A \<in> sets M \<Longrightarrow> B \<in> sets M \<Longrightarrow> measure M (A \<union> B) = measure M A + measure M (B - A)"
  using finite_measure_Union[of A "B - A"] by auto

lemma finite_unsigned_Hahn_decomposition:
  assumes "finite_measure M" "finite_measure N" and [simp]: "sets N = sets M"
  shows "\<exists>Y\<in>sets M. (\<forall>X\<in>sets M. X \<subseteq> Y \<longrightarrow> N X \<le> M X) \<and> (\<forall>X\<in>sets M. X \<inter> Y = {} \<longrightarrow> M X \<le> N X)"
proof -
  interpret M: finite_measure M by fact
  interpret N: finite_measure N by fact

  define d where "d X = measure M X - measure N X" for X

  have [intro]: "bdd_above (d`sets M)"
    using sets.sets_into_space[of _ M]
    by (intro bdd_aboveI[where M="measure M (space M)"])
       (auto simp: d_def field_simps subset_eq intro!: add_increasing M.finite_measure_mono)

  define \<gamma> where "\<gamma> = (SUP X\<in>sets M. d X)"
  have le_\<gamma>[intro]: "X \<in> sets M \<Longrightarrow> d X \<le> \<gamma>" for X
    by (auto simp: \<gamma>_def intro!: cSUP_upper)

  have "\<exists>f. \<forall>n. f n \<in> sets M \<and> d (f n) > \<gamma> - 1 / 2^n"
  proof (intro choice_iff[THEN iffD1] allI)
    fix n
    have "\<exists>X\<in>sets M. \<gamma> - 1 / 2^n < d X"
      unfolding \<gamma>_def by (intro less_cSUP_iff[THEN iffD1]) auto
    then show "\<exists>y. y \<in> sets M \<and> \<gamma> - 1 / 2 ^ n < d y"
      by auto
  qed
  then obtain E where [measurable]: "E n \<in> sets M" and E: "d (E n) > \<gamma> - 1 / 2^n" for n
    by auto

  define F where "F m n = (if m \<le> n then \<Inter>i\<in>{m..n}. E i else space M)" for m n

  have [measurable]: "m \<le> n \<Longrightarrow> F m n \<in> sets M" for m n
    by (auto simp: F_def)

  have 1: "\<gamma> - 2 / 2 ^ m + 1 / 2 ^ n \<le> d (F m n)" if "m \<le> n" for m n
    using that
  proof (induct rule: dec_induct)
    case base with E[of m] show ?case
      by (simp add: F_def field_simps)
  next
    case (step i)
    have F_Suc: "F m (Suc i) = F m i \<inter> E (Suc i)"
      using \<open>m \<le> i\<close> by (auto simp: F_def le_Suc_eq)

    have "\<gamma> + (\<gamma> - 2 / 2^m + 1 / 2 ^ Suc i) \<le> (\<gamma> - 1 / 2^Suc i) + (\<gamma> - 2 / 2^m + 1 / 2^i)"
      by (simp add: field_simps)
    also have "\<dots> \<le> d (E (Suc i)) + d (F m i)"
      using E[of "Suc i"] by (intro add_mono step) auto
    also have "\<dots> = d (E (Suc i)) + d (F m i - E (Suc i)) + d (F m (Suc i))"
      using \<open>m \<le> i\<close> by (simp add: d_def field_simps F_Suc M.finite_measure_Diff' N.finite_measure_Diff')
    also have "\<dots> = d (E (Suc i) \<union> F m i) + d (F m (Suc i))"
      using \<open>m \<le> i\<close> by (simp add: d_def field_simps M.finite_measure_Union' N.finite_measure_Union')
    also have "\<dots> \<le> \<gamma> + d (F m (Suc i))"
      using \<open>m \<le> i\<close> by auto
    finally show ?case
      by auto
  qed

  define F' where "F' m = (\<Inter>i\<in>{m..}. E i)" for m
  have F'_eq: "F' m = (\<Inter>i. F m (i + m))" for m
    by (fastforce simp: le_iff_add[of m] F'_def F_def)

  have [measurable]: "F' m \<in> sets M" for m
    by (auto simp: F'_def)

  have \<gamma>_le: "\<gamma> - 0 \<le> d (\<Union>m. F' m)"
  proof (rule LIMSEQ_le)
    show "(\<lambda>n. \<gamma> - 2 / 2 ^ n) \<longlonglongrightarrow> \<gamma> - 0"
      by (intro tendsto_intros LIMSEQ_divide_realpow_zero) auto
    have "incseq F'"
      by (auto simp: incseq_def F'_def)
    then show "(\<lambda>m. d (F' m)) \<longlonglongrightarrow> d (\<Union>m. F' m)"
      unfolding d_def
      by (intro tendsto_diff M.finite_Lim_measure_incseq N.finite_Lim_measure_incseq) auto

    have "\<gamma> - 2 / 2 ^ m + 0 \<le> d (F' m)" for m
    proof (rule LIMSEQ_le)
      have *: "decseq (\<lambda>n. F m (n + m))"
        by (auto simp: decseq_def F_def)
      show "(\<lambda>n. d (F m n)) \<longlonglongrightarrow> d (F' m)"
        unfolding d_def F'_eq
        by (rule LIMSEQ_offset[where k=m])
           (auto intro!: tendsto_diff M.finite_Lim_measure_decseq N.finite_Lim_measure_decseq *)
      show "(\<lambda>n. \<gamma> - 2 / 2 ^ m + 1 / 2 ^ n) \<longlonglongrightarrow> \<gamma> - 2 / 2 ^ m + 0"
        by (intro tendsto_add LIMSEQ_divide_realpow_zero tendsto_const) auto
      show "\<exists>N. \<forall>n\<ge>N. \<gamma> - 2 / 2 ^ m + 1 / 2 ^ n \<le> d (F m n)"
        using 1[of m] by (intro exI[of _ m]) auto
    qed
    then show "\<exists>N. \<forall>n\<ge>N. \<gamma> - 2 / 2 ^ n \<le> d (F' n)"
      by auto
  qed

  show ?thesis
  proof (safe intro!: bexI[of _ "\<Union>m. F' m"])
    fix X assume [measurable]: "X \<in> sets M" and X: "X \<subseteq> (\<Union>m. F' m)"
    have "d (\<Union>m. F' m) - d X = d ((\<Union>m. F' m) - X)"
      using X by (auto simp: d_def M.finite_measure_Diff N.finite_measure_Diff)
    also have "\<dots> \<le> \<gamma>"
      by auto
    finally have "0 \<le> d X"
      using \<gamma>_le by auto
    then show "emeasure N X \<le> emeasure M X"
      by (auto simp: d_def M.emeasure_eq_measure N.emeasure_eq_measure)
  next
    fix X assume [measurable]: "X \<in> sets M" and X: "X \<inter> (\<Union>m. F' m) = {}"
    then have "d (\<Union>m. F' m) + d X = d (X \<union> (\<Union>m. F' m))"
      by (auto simp: d_def M.finite_measure_Union N.finite_measure_Union)
    also have "\<dots> \<le> \<gamma>"
      by auto
    finally have "d X \<le> 0"
      using \<gamma>_le by auto
    then show "emeasure M X \<le> emeasure N X"
      by (auto simp: d_def M.emeasure_eq_measure N.emeasure_eq_measure)
  qed auto
qed

proposition unsigned_Hahn_decomposition:
  assumes [simp]: "sets N = sets M" and [measurable]: "A \<in> sets M"
    and [simp]: "emeasure M A \<noteq> top" "emeasure N A \<noteq> top"
  shows "\<exists>Y\<in>sets M. Y \<subseteq> A \<and> (\<forall>X\<in>sets M. X \<subseteq> Y \<longrightarrow> N X \<le> M X) \<and> (\<forall>X\<in>sets M. X \<subseteq> A \<longrightarrow> X \<inter> Y = {} \<longrightarrow> M X \<le> N X)"
proof -
  have "\<exists>Y\<in>sets (restrict_space M A).
    (\<forall>X\<in>sets (restrict_space M A). X \<subseteq> Y \<longrightarrow> (restrict_space N A) X \<le> (restrict_space M A) X) \<and>
    (\<forall>X\<in>sets (restrict_space M A). X \<inter> Y = {} \<longrightarrow> (restrict_space M A) X \<le> (restrict_space N A) X)"
  proof (rule finite_unsigned_Hahn_decomposition)
    show "finite_measure (restrict_space M A)" "finite_measure (restrict_space N A)"
      by (auto simp: space_restrict_space emeasure_restrict_space less_top intro!: finite_measureI)
  qed (simp add: sets_restrict_space)
  then show ?thesis
    apply -
    apply (erule bexE)
    subgoal for Y
      apply (intro bexI[of _ Y] conjI ballI conjI)
         apply (simp_all add: sets_restrict_space emeasure_restrict_space)
         apply safe
      subgoal for X Z
        by (erule ballE[of _ _ X]) (auto simp add: Int_absorb1)
      subgoal for X Z
        by (erule ballE[of _ _ X])  (auto simp add: Int_absorb1 ac_simps)
      apply auto
      done
    done
qed

text\<^marker>\<open>tag important\<close> \<open>
  Define a lexicographical order on \<^type>\<open>measure\<close>, in the order space, sets and measure. The parts
  of the lexicographical order are point-wise ordered.
\<close>

instantiation measure :: (type) order_bot
begin

inductive less_eq_measure :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "space M \<subset> space N \<Longrightarrow> less_eq_measure M N"
| "space M = space N \<Longrightarrow> sets M \<subset> sets N \<Longrightarrow> less_eq_measure M N"
| "space M = space N \<Longrightarrow> sets M = sets N \<Longrightarrow> emeasure M \<le> emeasure N \<Longrightarrow> less_eq_measure M N"

lemma le_measure_iff:
  "M \<le> N \<longleftrightarrow> (if space M = space N then
    if sets M = sets N then emeasure M \<le> emeasure N else sets M \<subseteq> sets N else space M \<subseteq> space N)"
  by (auto elim: less_eq_measure.cases intro: less_eq_measure.intros)

definition\<^marker>\<open>tag important\<close> less_measure :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "less_measure M N \<longleftrightarrow> (M \<le> N \<and> \<not> N \<le> M)"

definition\<^marker>\<open>tag important\<close> bot_measure :: "'a measure" where
  "bot_measure = sigma {} {}"

lemma
  shows space_bot[simp]: "space bot = {}"
    and sets_bot[simp]: "sets bot = {{}}"
    and emeasure_bot[simp]: "emeasure bot X = 0"
  by (auto simp: bot_measure_def sigma_sets_empty_eq emeasure_sigma)

instance
proof standard
  show "bot \<le> a" for a :: "'a measure"
    by (simp add: le_measure_iff bot_measure_def sigma_sets_empty_eq emeasure_sigma le_fun_def)
qed (auto simp: le_measure_iff less_measure_def split: if_split_asm intro: measure_eqI)

end

proposition le_measure: "sets M = sets N \<Longrightarrow> M \<le> N \<longleftrightarrow> (\<forall>A\<in>sets M. emeasure M A \<le> emeasure N A)"
  apply -
  apply (auto simp: le_measure_iff le_fun_def dest: sets_eq_imp_space_eq)
  subgoal for X
    by (cases "X \<in> sets M") (auto simp: emeasure_notin_sets)
  done

definition\<^marker>\<open>tag important\<close> sup_measure' :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> 'a measure" where
"sup_measure' A B =
  measure_of (space A) (sets A)
    (\<lambda>X. SUP Y\<in>sets A. emeasure A (X \<inter> Y) + emeasure B (X \<inter> - Y))"

lemma assumes [simp]: "sets B = sets A"
  shows space_sup_measure'[simp]: "space (sup_measure' A B) = space A"
    and sets_sup_measure'[simp]: "sets (sup_measure' A B) = sets A"
  using sets_eq_imp_space_eq[OF assms] by (simp_all add: sup_measure'_def)

lemma emeasure_sup_measure':
  assumes sets_eq[simp]: "sets B = sets A" and [simp, intro]: "X \<in> sets A"
  shows "emeasure (sup_measure' A B) X = (SUP Y\<in>sets A. emeasure A (X \<inter> Y) + emeasure B (X \<inter> - Y))"
    (is "_ = ?S X")
proof -
  note sets_eq_imp_space_eq[OF sets_eq, simp]
  show ?thesis
    using sup_measure'_def
  proof (rule emeasure_measure_of)
    let ?d = "\<lambda>X Y. emeasure A (X \<inter> Y) + emeasure B (X \<inter> - Y)"
    show "countably_additive (sets (sup_measure' A B)) (\<lambda>X. SUP Y \<in> sets A. emeasure A (X \<inter> Y) + emeasure B (X \<inter> - Y))"
    proof (rule countably_additiveI, goal_cases)
      case (1 X)
      then have [measurable]: "\<And>i. X i \<in> sets A" and "disjoint_family X"
        by auto
      have disjoint: "disjoint_family (\<lambda>i. X i \<inter> Y)" "disjoint_family (\<lambda>i. X i - Y)" for Y
        by (auto intro: disjoint_family_on_bisimulation [OF \<open>disjoint_family X\<close>, simplified])
      have "(\<Sum>i. ?S (X i)) = (SUP Y\<in>sets A. \<Sum>i. ?d (X i) Y)"
      proof (rule ennreal_suminf_SUP_eq_directed)
        fix J :: "nat set" and a b assume "finite J" and [measurable]: "a \<in> sets A" "b \<in> sets A"
        have "\<exists>c\<in>sets A. c \<subseteq> X i \<and> (\<forall>a\<in>sets A. ?d (X i) a \<le> ?d (X i) c)" for i
        proof cases
          assume "emeasure A (X i) = top \<or> emeasure B (X i) = top"
          then show ?thesis
          proof
            assume "emeasure A (X i) = top" then show ?thesis
              by (intro bexI[of _ "X i"]) auto
          next
            assume "emeasure B (X i) = top" then show ?thesis
              by (intro bexI[of _ "{}"]) auto
          qed
        next
          assume finite: "\<not> (emeasure A (X i) = top \<or> emeasure B (X i) = top)"
          then have "\<exists>Y\<in>sets A. Y \<subseteq> X i \<and> (\<forall>C\<in>sets A. C \<subseteq> Y \<longrightarrow> B C \<le> A C) \<and> (\<forall>C\<in>sets A. C \<subseteq> X i \<longrightarrow> C \<inter> Y = {} \<longrightarrow> A C \<le> B C)"
            using unsigned_Hahn_decomposition[of B A "X i"] by simp
          then obtain Y where [measurable]: "Y \<in> sets A" and [simp]: "Y \<subseteq> X i"
            and B_le_A: "\<And>C. C \<in> sets A \<Longrightarrow> C \<subseteq> Y \<Longrightarrow> B C \<le> A C"
            and A_le_B: "\<And>C. C \<in> sets A \<Longrightarrow> C \<subseteq> X i \<Longrightarrow> C \<inter> Y = {} \<Longrightarrow> A C \<le> B C"
            by auto

          show ?thesis
          proof (intro bexI[of _ Y] ballI conjI)
            fix a assume [measurable]: "a \<in> sets A"
            have *: "(X i \<inter> a \<inter> Y \<union> (X i \<inter> a - Y)) = X i \<inter> a" "(X i - a) \<inter> Y \<union> (X i - a - Y) = X i \<inter> - a"
              for a Y by auto
            then have "?d (X i) a =
              (A (X i \<inter> a \<inter> Y) + A (X i \<inter> a \<inter> - Y)) + (B (X i \<inter> - a \<inter> Y) + B (X i \<inter> - a \<inter> - Y))"
              by (subst (1 2) plus_emeasure) (auto simp: Diff_eq[symmetric])
            also have "\<dots> \<le> (A (X i \<inter> a \<inter> Y) + B (X i \<inter> a \<inter> - Y)) + (A (X i \<inter> - a \<inter> Y) + B (X i \<inter> - a \<inter> - Y))"
              by (intro add_mono order_refl B_le_A A_le_B) (auto simp: Diff_eq[symmetric])
            also have "\<dots> \<le> (A (X i \<inter> Y \<inter> a) + A (X i \<inter> Y \<inter> - a)) + (B (X i \<inter> - Y \<inter> a) + B (X i \<inter> - Y \<inter> - a))"
              by (simp add: ac_simps)
            also have "\<dots> \<le> A (X i \<inter> Y) + B (X i \<inter> - Y)"
              by (subst (1 2) plus_emeasure) (auto simp: Diff_eq[symmetric] *)
            finally show "?d (X i) a \<le> ?d (X i) Y" .
          qed auto
        qed
        then obtain C where [measurable]: "C i \<in> sets A" and "C i \<subseteq> X i"
          and C: "\<And>a. a \<in> sets A \<Longrightarrow> ?d (X i) a \<le> ?d (X i) (C i)" for i
          by metis
        have *: "X i \<inter> (\<Union>i. C i) = X i \<inter> C i" for i
        proof safe
          fix x j assume "x \<in> X i" "x \<in> C j"
          moreover have "i = j \<or> X i \<inter> X j = {}"
            using \<open>disjoint_family X\<close> by (auto simp: disjoint_family_on_def)
          ultimately show "x \<in> C i"
            using \<open>C i \<subseteq> X i\<close> \<open>C j \<subseteq> X j\<close> by auto
        qed auto
        have **: "X i \<inter> - (\<Union>i. C i) = X i \<inter> - C i" for i
        proof safe
          fix x j assume "x \<in> X i" "x \<notin> C i" "x \<in> C j"
          moreover have "i = j \<or> X i \<inter> X j = {}"
            using \<open>disjoint_family X\<close> by (auto simp: disjoint_family_on_def)
          ultimately show False
            using \<open>C i \<subseteq> X i\<close> \<open>C j \<subseteq> X j\<close> by auto
        qed auto
        show "\<exists>c\<in>sets A. \<forall>i\<in>J. ?d (X i) a \<le> ?d (X i) c \<and> ?d (X i) b \<le> ?d (X i) c"
          apply (intro bexI[of _ "\<Union>i. C i"])
          unfolding * **
          apply (intro C ballI conjI)
          apply auto
          done
      qed
      also have "\<dots> = ?S (\<Union>i. X i)"
        apply (simp only: UN_extend_simps(4))
        apply (rule arg_cong [of _ _ Sup])
        apply (rule image_cong)
         apply (fact refl)
        using disjoint
        apply (auto simp add: suminf_add [symmetric] Diff_eq [symmetric] image_subset_iff suminf_emeasure simp del: UN_simps)
        done
      finally show "(\<Sum>i. ?S (X i)) = ?S (\<Union>i. X i)" .
    qed
  qed (auto dest: sets.sets_into_space simp: positive_def intro!: SUP_const)
qed

lemma le_emeasure_sup_measure'1:
  assumes "sets B = sets A" "X \<in> sets A" shows "emeasure A X \<le> emeasure (sup_measure' A B) X"
  by (subst emeasure_sup_measure'[OF assms]) (auto intro!: SUP_upper2[of "X"] assms)

lemma le_emeasure_sup_measure'2:
  assumes "sets B = sets A" "X \<in> sets A" shows "emeasure B X \<le> emeasure (sup_measure' A B) X"
  by (subst emeasure_sup_measure'[OF assms]) (auto intro!: SUP_upper2[of "{}"] assms)

lemma emeasure_sup_measure'_le2:
  assumes [simp]: "sets B = sets C" "sets A = sets C" and [measurable]: "X \<in> sets C"
  assumes A: "\<And>Y. Y \<subseteq> X \<Longrightarrow> Y \<in> sets A \<Longrightarrow> emeasure A Y \<le> emeasure C Y"
  assumes B: "\<And>Y. Y \<subseteq> X \<Longrightarrow> Y \<in> sets A \<Longrightarrow> emeasure B Y \<le> emeasure C Y"
  shows "emeasure (sup_measure' A B) X \<le> emeasure C X"
proof (subst emeasure_sup_measure')
  show "(SUP Y\<in>sets A. emeasure A (X \<inter> Y) + emeasure B (X \<inter> - Y)) \<le> emeasure C X"
    unfolding \<open>sets A = sets C\<close>
  proof (intro SUP_least)
    fix Y assume [measurable]: "Y \<in> sets C"
    have [simp]: "X \<inter> Y \<union> (X - Y) = X"
      by auto
    have "emeasure A (X \<inter> Y) + emeasure B (X \<inter> - Y) \<le> emeasure C (X \<inter> Y) + emeasure C (X \<inter> - Y)"
      by (intro add_mono A B) (auto simp: Diff_eq[symmetric])
    also have "\<dots> = emeasure C X"
      by (subst plus_emeasure) (auto simp: Diff_eq[symmetric])
    finally show "emeasure A (X \<inter> Y) + emeasure B (X \<inter> - Y) \<le> emeasure C X" .
  qed
qed simp_all

definition\<^marker>\<open>tag important\<close> sup_lexord :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b::order) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"sup_lexord A B k s c =
  (if k A = k B then c else
   if \<not> k A \<le> k B \<and> \<not> k B \<le> k A then s else
   if k B \<le> k A then A else B)"

lemma sup_lexord:
  "(k A < k B \<Longrightarrow> P B) \<Longrightarrow> (k B < k A \<Longrightarrow> P A) \<Longrightarrow> (k A = k B \<Longrightarrow> P c) \<Longrightarrow>
    (\<not> k B \<le> k A \<Longrightarrow> \<not> k A \<le> k B \<Longrightarrow> P s) \<Longrightarrow> P (sup_lexord A B k s c)"
  by (auto simp: sup_lexord_def)

lemmas le_sup_lexord = sup_lexord[where P="\<lambda>a. c \<le> a" for c]

lemma sup_lexord1: "k A = k B \<Longrightarrow> sup_lexord A B k s c = c"
  by (simp add: sup_lexord_def)

lemma sup_lexord_commute: "sup_lexord A B k s c = sup_lexord B A k s c"
  by (auto simp: sup_lexord_def)

lemma sigma_sets_le_sets_iff: "(sigma_sets (space x) \<A> \<subseteq> sets x) = (\<A> \<subseteq> sets x)"
  using sets.sigma_sets_subset[of \<A> x] by auto

lemma sigma_le_iff: "\<A> \<subseteq> Pow \<Omega> \<Longrightarrow> sigma \<Omega> \<A> \<le> x \<longleftrightarrow> (\<Omega> \<subseteq> space x \<and> (space x = \<Omega> \<longrightarrow> \<A> \<subseteq> sets x))"
  by (cases "\<Omega> = space x")
     (simp_all add: eq_commute[of _ "sets x"] le_measure_iff emeasure_sigma le_fun_def
                    sigma_sets_superset_generator sigma_sets_le_sets_iff)

instantiation measure :: (type) semilattice_sup
begin

definition\<^marker>\<open>tag important\<close> sup_measure :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> 'a measure" where
  "sup_measure A B =
    sup_lexord A B space (sigma (space A \<union> space B) {})
      (sup_lexord A B sets (sigma (space A) (sets A \<union> sets B)) (sup_measure' A B))"

instance
proof
  fix x y z :: "'a measure"
  show "x \<le> sup x y"
    unfolding sup_measure_def
  proof (intro le_sup_lexord)
    assume "space x = space y"
    then have *: "sets x \<union> sets y \<subseteq> Pow (space x)"
      using sets.space_closed by auto
    assume "\<not> sets y \<subseteq> sets x" "\<not> sets x \<subseteq> sets y"
    then have "sets x \<subset> sets x \<union> sets y"
      by auto
    also have "\<dots> \<le> sigma (space x) (sets x \<union> sets y)"
      by (subst sets_measure_of[OF *]) (rule sigma_sets_superset_generator)
    finally show "x \<le> sigma (space x) (sets x \<union> sets y)"
      by (simp add: space_measure_of[OF *] less_eq_measure.intros(2))
  next
    assume "\<not> space y \<subseteq> space x" "\<not> space x \<subseteq> space y"
    then show "x \<le> sigma (space x \<union> space y) {}"
      by (intro less_eq_measure.intros) auto
  next
    assume "sets x = sets y" then show "x \<le> sup_measure' x y"
      by (simp add: le_measure le_emeasure_sup_measure'1)
  qed (auto intro: less_eq_measure.intros)
  show "y \<le> sup x y"
    unfolding sup_measure_def
  proof (intro le_sup_lexord)
    assume **: "space x = space y"
    then have *: "sets x \<union> sets y \<subseteq> Pow (space y)"
      using sets.space_closed by auto
    assume "\<not> sets y \<subseteq> sets x" "\<not> sets x \<subseteq> sets y"
    then have "sets y \<subset> sets x \<union> sets y"
      by auto
    also have "\<dots> \<le> sigma (space y) (sets x \<union> sets y)"
      by (subst sets_measure_of[OF *]) (rule sigma_sets_superset_generator)
    finally show "y \<le> sigma (space x) (sets x \<union> sets y)"
      by (simp add: ** space_measure_of[OF *] less_eq_measure.intros(2))
  next
    assume "\<not> space y \<subseteq> space x" "\<not> space x \<subseteq> space y"
    then show "y \<le> sigma (space x \<union> space y) {}"
      by (intro less_eq_measure.intros) auto
  next
    assume "sets x = sets y" then show "y \<le> sup_measure' x y"
      by (simp add: le_measure le_emeasure_sup_measure'2)
  qed (auto intro: less_eq_measure.intros)
  show "x \<le> y \<Longrightarrow> z \<le> y \<Longrightarrow> sup x z \<le> y"
    unfolding sup_measure_def
  proof (intro sup_lexord[where P="\<lambda>x. x \<le> y"])
    assume "x \<le> y" "z \<le> y" and [simp]: "space x = space z" "sets x = sets z"
    from \<open>x \<le> y\<close> show "sup_measure' x z \<le> y"
    proof cases
      case 1 then show ?thesis
        by (intro less_eq_measure.intros(1)) simp
    next
      case 2 then show ?thesis
        by (intro less_eq_measure.intros(2)) simp_all
    next
      case 3 with \<open>z \<le> y\<close> \<open>x \<le> y\<close> show ?thesis
        by (auto simp add: le_measure intro!: emeasure_sup_measure'_le2)
    qed
  next
    assume **: "x \<le> y" "z \<le> y" "space x = space z" "\<not> sets z \<subseteq> sets x" "\<not> sets x \<subseteq> sets z"
    then have *: "sets x \<union> sets z \<subseteq> Pow (space x)"
      using sets.space_closed by auto
    show "sigma (space x) (sets x \<union> sets z) \<le> y"
      unfolding sigma_le_iff[OF *] using ** by (auto simp: le_measure_iff split: if_split_asm)
  next
    assume "x \<le> y" "z \<le> y" "\<not> space z \<subseteq> space x" "\<not> space x \<subseteq> space z"
    then have "space x \<subseteq> space y" "space z \<subseteq> space y"
      by (auto simp: le_measure_iff split: if_split_asm)
    then show "sigma (space x \<union> space z) {} \<le> y"
      by (simp add: sigma_le_iff)
  qed
qed

end

lemma space_empty_eq_bot: "space a = {} \<longleftrightarrow> a = bot"
  using space_empty[of a] by (auto intro!: measure_eqI)

lemma sets_eq_iff_bounded: "A \<le> B \<Longrightarrow> B \<le> C \<Longrightarrow> sets A = sets C \<Longrightarrow> sets B = sets A"
  by (auto dest: sets_eq_imp_space_eq simp add: le_measure_iff split: if_split_asm)

lemma sets_sup: "sets A = sets M \<Longrightarrow> sets B = sets M \<Longrightarrow> sets (sup A B) = sets M"
  by (auto simp add: sup_measure_def sup_lexord_def dest: sets_eq_imp_space_eq)

lemma le_measureD1: "A \<le> B \<Longrightarrow> space A \<le> space B"
  by (auto simp: le_measure_iff split: if_split_asm)

lemma le_measureD2: "A \<le> B \<Longrightarrow> space A = space B \<Longrightarrow> sets A \<le> sets B"
  by (auto simp: le_measure_iff split: if_split_asm)

lemma le_measureD3: "A \<le> B \<Longrightarrow> sets A = sets B \<Longrightarrow> emeasure A X \<le> emeasure B X"
  by (auto simp: le_measure_iff le_fun_def dest: sets_eq_imp_space_eq split: if_split_asm)

lemma UN_space_closed: "\<Union>(sets ` S) \<subseteq> Pow (\<Union>(space ` S))"
  using sets.space_closed by auto

definition\<^marker>\<open>tag important\<close>
  Sup_lexord :: "('a \<Rightarrow> 'b::complete_lattice) \<Rightarrow> ('a set \<Rightarrow> 'a) \<Rightarrow> ('a set \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a"
where
  "Sup_lexord k c s A =
  (let U = (SUP a\<in>A. k a)
   in if \<exists>a\<in>A. k a = U then c {a\<in>A. k a = U} else s A)"

lemma Sup_lexord:
  "(\<And>a S. a \<in> A \<Longrightarrow> k a = (SUP a\<in>A. k a) \<Longrightarrow> S = {a'\<in>A. k a' = k a} \<Longrightarrow> P (c S)) \<Longrightarrow> ((\<And>a. a \<in> A \<Longrightarrow> k a \<noteq> (SUP a\<in>A. k a)) \<Longrightarrow> P (s A)) \<Longrightarrow>
    P (Sup_lexord k c s A)"
  by (auto simp: Sup_lexord_def Let_def)

lemma Sup_lexord1:
  assumes A: "A \<noteq> {}" "(\<And>a. a \<in> A \<Longrightarrow> k a = (\<Union>a\<in>A. k a))" "P (c A)"
  shows "P (Sup_lexord k c s A)"
  unfolding Sup_lexord_def Let_def
proof (clarsimp, safe)
  show "\<forall>a\<in>A. k a \<noteq> (\<Union>x\<in>A. k x) \<Longrightarrow> P (s A)"
    by (metis assms(1,2) ex_in_conv)
next
  fix a assume "a \<in> A" "k a = (\<Union>x\<in>A. k x)"
  then have "{a \<in> A. k a = (\<Union>x\<in>A. k x)} = {a \<in> A. k a = k a}"
    by (metis A(2)[symmetric])
  then show "P (c {a \<in> A. k a = (\<Union>x\<in>A. k x)})"
    by (simp add: A(3))
qed

instantiation measure :: (type) complete_lattice
begin

interpretation sup_measure: comm_monoid_set sup "bot :: 'a measure"
  by standard (auto intro!: antisym)

lemma sup_measure_F_mono':
  "finite J \<Longrightarrow> finite I \<Longrightarrow> sup_measure.F id I \<le> sup_measure.F id (I \<union> J)"
proof (induction J rule: finite_induct)
  case empty then show ?case
    by simp
next
  case (insert i J)
  show ?case
  proof cases
    assume "i \<in> I" with insert show ?thesis
      by (auto simp: insert_absorb)
  next
    assume "i \<notin> I"
    have "sup_measure.F id I \<le> sup_measure.F id (I \<union> J)"
      by (intro insert)
    also have "\<dots> \<le> sup_measure.F id (insert i (I \<union> J))"
      using insert \<open>i \<notin> I\<close> by (subst sup_measure.insert) auto
    finally show ?thesis
      by auto
  qed
qed

lemma sup_measure_F_mono: "finite I \<Longrightarrow> J \<subseteq> I \<Longrightarrow> sup_measure.F id J \<le> sup_measure.F id I"
  using sup_measure_F_mono'[of I J] by (auto simp: finite_subset Un_absorb1)

lemma sets_sup_measure_F:
  "finite I \<Longrightarrow> I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> sets i = sets M) \<Longrightarrow> sets (sup_measure.F id I) = sets M"
  by (induction I rule: finite_ne_induct) (simp_all add: sets_sup)

definition\<^marker>\<open>tag important\<close> Sup_measure' :: "'a measure set \<Rightarrow> 'a measure" where
"Sup_measure' M =
  measure_of (\<Union>a\<in>M. space a) (\<Union>a\<in>M. sets a)
    (\<lambda>X. (SUP P\<in>{P. finite P \<and> P \<subseteq> M }. sup_measure.F id P X))"

lemma space_Sup_measure'2: "space (Sup_measure' M) = (\<Union>m\<in>M. space m)"
  unfolding Sup_measure'_def by (intro space_measure_of[OF UN_space_closed])

lemma sets_Sup_measure'2: "sets (Sup_measure' M) = sigma_sets (\<Union>m\<in>M. space m) (\<Union>m\<in>M. sets m)"
  unfolding Sup_measure'_def by (intro sets_measure_of[OF UN_space_closed])

lemma sets_Sup_measure':
  assumes sets_eq[simp]: "\<And>m. m \<in> M \<Longrightarrow> sets m = sets A" and "M \<noteq> {}"
  shows "sets (Sup_measure' M) = sets A"
  using sets_eq[THEN sets_eq_imp_space_eq, simp] \<open>M \<noteq> {}\<close> by (simp add: Sup_measure'_def)

lemma space_Sup_measure':
  assumes sets_eq[simp]: "\<And>m. m \<in> M \<Longrightarrow> sets m = sets A" and "M \<noteq> {}"
  shows "space (Sup_measure' M) = space A"
  using sets_eq[THEN sets_eq_imp_space_eq, simp] \<open>M \<noteq> {}\<close>
  by (simp add: Sup_measure'_def )

lemma emeasure_Sup_measure':
  assumes sets_eq[simp]: "\<And>m. m \<in> M \<Longrightarrow> sets m = sets A" and "X \<in> sets A" "M \<noteq> {}"
  shows "emeasure (Sup_measure' M) X = (SUP P\<in>{P. finite P \<and> P \<subseteq> M}. sup_measure.F id P X)"
    (is "_ = ?S X")
  using Sup_measure'_def
proof (rule emeasure_measure_of)
  note sets_eq[THEN sets_eq_imp_space_eq, simp]
  have *: "sets (Sup_measure' M) = sets A" "space (Sup_measure' M) = space A"
    using \<open>M \<noteq> {}\<close> by (simp_all add: Sup_measure'_def)
  let ?\<mu> = "sup_measure.F id"
  show "countably_additive (sets (Sup_measure' M)) ?S"
  proof (rule countably_additiveI, goal_cases)
    case (1 F)
    then have **: "range F \<subseteq> sets A"
      by (auto simp: *)
    show "(\<Sum>i. ?S (F i)) = ?S (\<Union>i. F i)"
    proof (subst ennreal_suminf_SUP_eq_directed)
      fix i j and N :: "nat set" assume ij: "i \<in> {P. finite P \<and> P \<subseteq> M}" "j \<in> {P. finite P \<and> P \<subseteq> M}"
      have "(i \<noteq> {} \<longrightarrow> sets (?\<mu> i) = sets A) \<and> (j \<noteq> {} \<longrightarrow> sets (?\<mu> j) = sets A) \<and>
        (i \<noteq> {} \<or> j \<noteq> {} \<longrightarrow> sets (?\<mu> (i \<union> j)) = sets A)"
        using ij by (intro impI sets_sup_measure_F conjI) auto
      then have "?\<mu> j (F n) \<le> ?\<mu> (i \<union> j) (F n) \<and> ?\<mu> i (F n) \<le> ?\<mu> (i \<union> j) (F n)" for n
        using ij
        by (cases "i = {}"; cases "j = {}")
           (auto intro!: le_measureD3 sup_measure_F_mono simp: sets_sup_measure_F
                 simp del: id_apply)
      with ij show "\<exists>k\<in>{P. finite P \<and> P \<subseteq> M}. \<forall>n\<in>N. ?\<mu> i (F n) \<le> ?\<mu> k (F n) \<and> ?\<mu> j (F n) \<le> ?\<mu> k (F n)"
        by (safe intro!: bexI[of _ "i \<union> j"]) auto
    next
      show "(SUP P \<in> {P. finite P \<and> P \<subseteq> M}. \<Sum>n. ?\<mu> P (F n)) = (SUP P \<in> {P. finite P \<and> P \<subseteq> M}. ?\<mu> P (\<Union>(F ` UNIV)))"
      proof (intro arg_cong [of _ _ Sup] image_cong refl)
        fix i assume i: "i \<in> {P. finite P \<and> P \<subseteq> M}"
        show "(\<Sum>n. ?\<mu> i (F n)) = ?\<mu> i (\<Union>(F ` UNIV))"
        proof cases
          assume "i \<noteq> {}" with i ** show ?thesis
            apply (intro suminf_emeasure \<open>disjoint_family F\<close>)
            apply (subst sets_sup_measure_F[OF _ _ sets_eq])
            apply auto
            done
        qed simp
      qed
    qed
  qed
  show "positive (sets (Sup_measure' M)) ?S"
    by (auto simp: positive_def bot_ennreal[symmetric])
  show "X \<in> sets (Sup_measure' M)"
    using assms * by auto
qed (rule UN_space_closed)

definition\<^marker>\<open>tag important\<close> Sup_measure :: "'a measure set \<Rightarrow> 'a measure" where
"Sup_measure =
  Sup_lexord space
    (Sup_lexord sets Sup_measure'
      (\<lambda>U. sigma (\<Union>u\<in>U. space u) (\<Union>u\<in>U. sets u)))
    (\<lambda>U. sigma (\<Union>u\<in>U. space u) {})"

definition\<^marker>\<open>tag important\<close> Inf_measure :: "'a measure set \<Rightarrow> 'a measure" where
  "Inf_measure A = Sup {x. \<forall>a\<in>A. x \<le> a}"

definition\<^marker>\<open>tag important\<close> inf_measure :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> 'a measure" where
  "inf_measure a b = Inf {a, b}"

definition\<^marker>\<open>tag important\<close> top_measure :: "'a measure" where
  "top_measure = Inf {}"

instance
proof
  note UN_space_closed [simp]
  show upper: "x \<le> Sup A" if x: "x \<in> A" for x :: "'a measure" and A
    unfolding Sup_measure_def
  proof (intro Sup_lexord[where P="\<lambda>y. x \<le> y"])
    assume "\<And>a. a \<in> A \<Longrightarrow> space a \<noteq> (\<Union>a\<in>A. space a)"
    from this[OF \<open>x \<in> A\<close>] \<open>x \<in> A\<close> show "x \<le> sigma (\<Union>a\<in>A. space a) {}"
      by (intro less_eq_measure.intros) auto
  next
    fix a S assume "a \<in> A" and a: "space a = (\<Union>a\<in>A. space a)" and S: "S = {a' \<in> A. space a' = space a}"
      and neq: "\<And>aa. aa \<in> S \<Longrightarrow> sets aa \<noteq> (\<Union>a\<in>S. sets a)"
    have sp_a: "space a = (\<Union>(space ` S))"
      using \<open>a\<in>A\<close> by (auto simp: S)
    show "x \<le> sigma (\<Union>(space ` S)) (\<Union>(sets ` S))"
    proof cases
      assume [simp]: "space x = space a"
      have "sets x \<subset> (\<Union>a\<in>S. sets a)"
        using \<open>x\<in>A\<close> neq[of x] by (auto simp: S)
      also have "\<dots> \<subseteq> sigma_sets (\<Union>x\<in>S. space x) (\<Union>x\<in>S. sets x)"
        by (rule sigma_sets_superset_generator)
      finally show ?thesis
        by (intro less_eq_measure.intros(2)) (simp_all add: sp_a)
    next
      assume "space x \<noteq> space a"
      moreover have "space x \<le> space a"
        unfolding a using \<open>x\<in>A\<close> by auto
      ultimately show ?thesis
        by (intro less_eq_measure.intros) (simp add: less_le sp_a)
    qed
  next
    fix a b S S' assume "a \<in> A" and a: "space a = (\<Union>a\<in>A. space a)" and S: "S = {a' \<in> A. space a' = space a}"
      and "b \<in> S" and b: "sets b = (\<Union>a\<in>S. sets a)" and S': "S' = {a' \<in> S. sets a' = sets b}"
    then have "S' \<noteq> {}" "space b = space a"
      by auto
    have sets_eq: "\<And>x. x \<in> S' \<Longrightarrow> sets x = sets b"
      by (auto simp: S')
    note sets_eq[THEN sets_eq_imp_space_eq, simp]
    have *: "sets (Sup_measure' S') = sets b" "space (Sup_measure' S') = space b"
      using \<open>S' \<noteq> {}\<close> by (simp_all add: Sup_measure'_def sets_eq)
    show "x \<le> Sup_measure' S'"
    proof cases
      assume "x \<in> S"
      with \<open>b \<in> S\<close> have "space x = space b"
        by (simp add: S)
      show ?thesis
      proof cases
        assume "x \<in> S'"
        show "x \<le> Sup_measure' S'"
        proof (intro le_measure[THEN iffD2] ballI)
          show "sets x = sets (Sup_measure' S')"
            using \<open>x\<in>S'\<close> * by (simp add: S')
          fix X assume "X \<in> sets x"
          show "emeasure x X \<le> emeasure (Sup_measure' S') X"
          proof (subst emeasure_Sup_measure'[OF _ \<open>X \<in> sets x\<close>])
            show "emeasure x X \<le> (SUP P \<in> {P. finite P \<and> P \<subseteq> S'}. emeasure (sup_measure.F id P) X)"
              using \<open>x\<in>S'\<close> by (intro SUP_upper2[where i="{x}"]) auto
          qed (insert \<open>x\<in>S'\<close> S', auto)
        qed
      next
        assume "x \<notin> S'"
        then have "sets x \<noteq> sets b"
          using \<open>x\<in>S\<close> by (auto simp: S')
        moreover have "sets x \<le> sets b"
          using \<open>x\<in>S\<close> unfolding b by auto
        ultimately show ?thesis
          using * \<open>x \<in> S\<close>
          by (intro less_eq_measure.intros(2))
             (simp_all add: * \<open>space x = space b\<close> less_le)
      qed
    next
      assume "x \<notin> S"
      with \<open>x\<in>A\<close> \<open>x \<notin> S\<close> \<open>space b = space a\<close> show ?thesis
        by (intro less_eq_measure.intros)
           (simp_all add: * less_le a SUP_upper S)
    qed
  qed
  show least: "Sup A \<le> x" if x: "\<And>z. z \<in> A \<Longrightarrow> z \<le> x" for x :: "'a measure" and A
    unfolding Sup_measure_def
  proof (intro Sup_lexord[where P="\<lambda>y. y \<le> x"])
    assume "\<And>a. a \<in> A \<Longrightarrow> space a \<noteq> (\<Union>a\<in>A. space a)"
    show "sigma (\<Union>(space ` A)) {} \<le> x"
      using x[THEN le_measureD1] by (subst sigma_le_iff) auto
  next
    fix a S assume "a \<in> A" "space a = (\<Union>a\<in>A. space a)" and S: "S = {a' \<in> A. space a' = space a}"
      "\<And>a. a \<in> S \<Longrightarrow> sets a \<noteq> (\<Union>a\<in>S. sets a)"
    have "\<Union>(space ` S) \<subseteq> space x"
      using S le_measureD1[OF x] by auto
    moreover
    have "\<Union>(space ` S) = space a"
      using \<open>a\<in>A\<close> S by auto
    then have "space x = \<Union>(space ` S) \<Longrightarrow> \<Union>(sets ` S) \<subseteq> sets x"
      using \<open>a \<in> A\<close> le_measureD2[OF x] by (auto simp: S)
    ultimately show "sigma (\<Union>(space ` S)) (\<Union>(sets ` S)) \<le> x"
      by (subst sigma_le_iff) simp_all
  next
    fix a b S S' assume "a \<in> A" and a: "space a = (\<Union>a\<in>A. space a)" and S: "S = {a' \<in> A. space a' = space a}"
      and "b \<in> S" and b: "sets b = (\<Union>a\<in>S. sets a)" and S': "S' = {a' \<in> S. sets a' = sets b}"
    then have "S' \<noteq> {}" "space b = space a"
      by auto
    have sets_eq: "\<And>x. x \<in> S' \<Longrightarrow> sets x = sets b"
      by (auto simp: S')
    note sets_eq[THEN sets_eq_imp_space_eq, simp]
    have *: "sets (Sup_measure' S') = sets b" "space (Sup_measure' S') = space b"
      using \<open>S' \<noteq> {}\<close> by (simp_all add: Sup_measure'_def sets_eq)
    show "Sup_measure' S' \<le> x"
    proof cases
      assume "space x = space a"
      show ?thesis
      proof cases
        assume **: "sets x = sets b"
        show ?thesis
        proof (intro le_measure[THEN iffD2] ballI)
          show ***: "sets (Sup_measure' S') = sets x"
            by (simp add: * **)
          fix X assume "X \<in> sets (Sup_measure' S')"
          show "emeasure (Sup_measure' S') X \<le> emeasure x X"
            unfolding ***
          proof (subst emeasure_Sup_measure'[OF _ \<open>X \<in> sets (Sup_measure' S')\<close>])
            show "(SUP P \<in> {P. finite P \<and> P \<subseteq> S'}. emeasure (sup_measure.F id P) X) \<le> emeasure x X"
            proof (safe intro!: SUP_least)
              fix P assume P: "finite P" "P \<subseteq> S'"
              show "emeasure (sup_measure.F id P) X \<le> emeasure x X"
              proof cases
                assume "P = {}" then show ?thesis
                  by auto
              next
                assume "P \<noteq> {}"
                from P have "finite P" "P \<subseteq> A"
                  unfolding S' S by (simp_all add: subset_eq)
                then have "sup_measure.F id P \<le> x"
                  by (induction P) (auto simp: x)
                moreover have "sets (sup_measure.F id P) = sets x"
                  using \<open>finite P\<close> \<open>P \<noteq> {}\<close> \<open>P \<subseteq> S'\<close> \<open>sets x = sets b\<close>
                  by (intro sets_sup_measure_F) (auto simp: S')
                ultimately show "emeasure (sup_measure.F id P) X \<le> emeasure x X"
                  by (rule le_measureD3)
              qed
            qed
            show "m \<in> S' \<Longrightarrow> sets m = sets (Sup_measure' S')" for m
              unfolding * by (simp add: S')
          qed fact
        qed
      next
        assume "sets x \<noteq> sets b"
        moreover have "sets b \<le> sets x"
          unfolding b S using x[THEN le_measureD2] \<open>space x = space a\<close> by auto
        ultimately show "Sup_measure' S' \<le> x"
          using \<open>space x = space a\<close> \<open>b \<in> S\<close>
          by (intro less_eq_measure.intros(2)) (simp_all add: * S)
      qed
    next
      assume "space x \<noteq> space a"
      then have "space a < space x"
        using le_measureD1[OF x[OF \<open>a\<in>A\<close>]] by auto
      then show "Sup_measure' S' \<le> x"
        by (intro less_eq_measure.intros) (simp add: * \<open>space b = space a\<close>)
    qed
  qed
  show "Sup {} = (bot::'a measure)" "Inf {} = (top::'a measure)"
    by (auto intro!: antisym least simp: top_measure_def)
  show lower: "x \<in> A \<Longrightarrow> Inf A \<le> x" for x :: "'a measure" and A
    unfolding Inf_measure_def by (intro least) auto
  show greatest: "(\<And>z. z \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> x \<le> Inf A" for x :: "'a measure" and A
    unfolding Inf_measure_def by (intro upper) auto
  show "inf x y \<le> x" "inf x y \<le> y" "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z" for x y z :: "'a measure"
    by (auto simp: inf_measure_def intro!: lower greatest)
qed

end

lemma sets_SUP:
  assumes "\<And>x. x \<in> I \<Longrightarrow> sets (M x) = sets N"
  shows "I \<noteq> {} \<Longrightarrow> sets (SUP i\<in>I. M i) = sets N"
  unfolding Sup_measure_def
  using assms assms[THEN sets_eq_imp_space_eq]
    sets_Sup_measure'[where A=N and M="M`I"]
  by (intro Sup_lexord1[where P="\<lambda>x. sets x = sets N"]) auto

lemma emeasure_SUP:
  assumes sets: "\<And>i. i \<in> I \<Longrightarrow> sets (M i) = sets N" "X \<in> sets N" "I \<noteq> {}"
  shows "emeasure (SUP i\<in>I. M i) X = (SUP J\<in>{J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I}. emeasure (SUP i\<in>J. M i) X)"
proof -
  interpret sup_measure: comm_monoid_set sup "bot :: 'b measure"
    by standard (auto intro!: antisym)
  have eq: "finite J \<Longrightarrow> sup_measure.F id J = (SUP i\<in>J. i)" for J :: "'b measure set"
    by (induction J rule: finite_induct) auto
  have 1: "J \<noteq> {} \<Longrightarrow> J \<subseteq> I \<Longrightarrow> sets (SUP x\<in>J. M x) = sets N" for J
    by (intro sets_SUP sets) (auto )
  from \<open>I \<noteq> {}\<close> obtain i where "i\<in>I" by auto
  have "Sup_measure' (M`I) X = (SUP P\<in>{P. finite P \<and> P \<subseteq> M`I}. sup_measure.F id P X)"
    using sets by (intro emeasure_Sup_measure') auto
  also have "Sup_measure' (M`I) = (SUP i\<in>I. M i)"
    unfolding Sup_measure_def using \<open>I \<noteq> {}\<close> sets sets(1)[THEN sets_eq_imp_space_eq]
    by (intro Sup_lexord1[where P="\<lambda>x. _ = x"]) auto
  also have "(SUP P\<in>{P. finite P \<and> P \<subseteq> M`I}. sup_measure.F id P X) =
    (SUP J\<in>{J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I}. (SUP i\<in>J. M i) X)"
  proof (intro SUP_eq)
    fix J assume "J \<in> {P. finite P \<and> P \<subseteq> M`I}"
    then obtain J' where J': "J' \<subseteq> I" "finite J'" and J: "J = M`J'" and "finite J"
      using finite_subset_image[of J M I] by auto
    show "\<exists>j\<in>{J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I}. sup_measure.F id J X \<le> (SUP i\<in>j. M i) X"
    proof cases
      assume "J' = {}" with \<open>i \<in> I\<close> show ?thesis
        by (auto simp add: J)
    next
      assume "J' \<noteq> {}" with J J' show ?thesis
        by (intro bexI[of _ "J'"]) (auto simp add: eq simp del: id_apply)
    qed
  next
    fix J assume J: "J \<in> {P. P \<noteq> {} \<and> finite P \<and> P \<subseteq> I}"
    show "\<exists>J'\<in>{J. finite J \<and> J \<subseteq> M`I}. (SUP i\<in>J. M i) X \<le> sup_measure.F id J' X"
      using J by (intro bexI[of _ "M`J"]) (auto simp add: eq simp del: id_apply)
  qed
  finally show ?thesis .
qed

lemma emeasure_SUP_chain:
  assumes sets: "\<And>i. i \<in> A \<Longrightarrow> sets (M i) = sets N" "X \<in> sets N"
  assumes ch: "Complete_Partial_Order.chain (\<le>) (M ` A)" and "A \<noteq> {}"
  shows "emeasure (SUP i\<in>A. M i) X = (SUP i\<in>A. emeasure (M i) X)"
proof (subst emeasure_SUP[OF sets \<open>A \<noteq> {}\<close>])
  show "(SUP J\<in>{J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> A}. emeasure (Sup (M ` J)) X) = (SUP i\<in>A. emeasure (M i) X)"
  proof (rule SUP_eq)
    fix J assume "J \<in> {J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> A}"
    then have J: "Complete_Partial_Order.chain (\<le>) (M ` J)" "finite J" "J \<noteq> {}" and "J \<subseteq> A"
      using ch[THEN chain_subset, of "M`J"] by auto
    with in_chain_finite[OF J(1)] obtain j where "j \<in> J" "(SUP j\<in>J. M j) = M j"
      by auto
    with \<open>J \<subseteq> A\<close> show "\<exists>j\<in>A. emeasure (Sup (M ` J)) X \<le> emeasure (M j) X"
      by auto
  next
    fix j assume "j\<in>A" then show "\<exists>i\<in>{J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> A}. emeasure (M j) X \<le> emeasure (Sup (M ` i)) X"
      by (intro bexI[of _ "{j}"]) auto
  qed
qed

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Supremum of a set of \<open>\<sigma>\<close>-algebras\<close>

lemma space_Sup_eq_UN: "space (Sup M) = (\<Union>x\<in>M. space x)"
  unfolding Sup_measure_def
  apply (intro Sup_lexord[where P="\<lambda>x. space x = _"])
  apply (subst space_Sup_measure'2)
  apply auto []
  apply (subst space_measure_of[OF UN_space_closed])
  apply auto
  done

lemma sets_Sup_eq:
  assumes *: "\<And>m. m \<in> M \<Longrightarrow> space m = X" and "M \<noteq> {}"
  shows "sets (Sup M) = sigma_sets X (\<Union>x\<in>M. sets x)"
  unfolding Sup_measure_def
  apply (rule Sup_lexord1)
  apply fact
  apply (simp add: assms)
  apply (rule Sup_lexord)
  subgoal premises that for a S
    unfolding that(3) that(2)[symmetric]
    using that(1)
    apply (subst sets_Sup_measure'2)
    apply (intro arg_cong2[where f=sigma_sets])
    apply (auto simp: *)
    done
  apply (subst sets_measure_of[OF UN_space_closed])
  apply (simp add:  assms)
  done

lemma in_sets_Sup: "(\<And>m. m \<in> M \<Longrightarrow> space m = X) \<Longrightarrow> m \<in> M \<Longrightarrow> A \<in> sets m \<Longrightarrow> A \<in> sets (Sup M)"
  by (subst sets_Sup_eq[where X=X]) auto

lemma Sup_lexord_rel:
  assumes "\<And>i. i \<in> I \<Longrightarrow> k (A i) = k (B i)"
    "R (c (A ` {a \<in> I. k (B a) = (SUP x\<in>I. k (B x))})) (c (B ` {a \<in> I. k (B a) = (SUP x\<in>I. k (B x))}))"
    "R (s (A`I)) (s (B`I))"
  shows "R (Sup_lexord k c s (A`I)) (Sup_lexord k c s (B`I))"
proof -
  have "A ` {a \<in> I. k (B a) = (SUP x\<in>I. k (B x))} =  {a \<in> A ` I. k a = (SUP x\<in>I. k (B x))}"
    using assms(1) by auto
  moreover have "B ` {a \<in> I. k (B a) = (SUP x\<in>I. k (B x))} =  {a \<in> B ` I. k a = (SUP x\<in>I. k (B x))}"
    by auto
  ultimately show ?thesis
    using assms by (auto simp: Sup_lexord_def Let_def image_comp)
qed

lemma sets_SUP_cong:
  assumes eq: "\<And>i. i \<in> I \<Longrightarrow> sets (M i) = sets (N i)" shows "sets (SUP i\<in>I. M i) = sets (SUP i\<in>I. N i)"
  unfolding Sup_measure_def
  using eq eq[THEN sets_eq_imp_space_eq]
  apply (intro Sup_lexord_rel[where R="\<lambda>x y. sets x = sets y"])
  apply simp
  apply simp
  apply (simp add: sets_Sup_measure'2)
  apply (intro arg_cong2[where f="\<lambda>x y. sets (sigma x y)"])
  apply auto
  done

lemma sets_Sup_in_sets:
  assumes "M \<noteq> {}"
  assumes "\<And>m. m \<in> M \<Longrightarrow> space m = space N"
  assumes "\<And>m. m \<in> M \<Longrightarrow> sets m \<subseteq> sets N"
  shows "sets (Sup M) \<subseteq> sets N"
proof -
  have *: "\<Union>(space ` M) = space N"
    using assms by auto
  show ?thesis
    unfolding * using assms by (subst sets_Sup_eq[of M "space N"]) (auto intro!: sets.sigma_sets_subset)
qed

lemma measurable_Sup1:
  assumes m: "m \<in> M" and f: "f \<in> measurable m N"
    and const_space: "\<And>m n. m \<in> M \<Longrightarrow> n \<in> M \<Longrightarrow> space m = space n"
  shows "f \<in> measurable (Sup M) N"
proof -
  have "space (Sup M) = space m"
    using m by (auto simp add: space_Sup_eq_UN dest: const_space)
  then show ?thesis
    using m f unfolding measurable_def by (auto intro: in_sets_Sup[OF const_space])
qed

lemma measurable_Sup2:
  assumes M: "M \<noteq> {}"
  assumes f: "\<And>m. m \<in> M \<Longrightarrow> f \<in> measurable N m"
    and const_space: "\<And>m n. m \<in> M \<Longrightarrow> n \<in> M \<Longrightarrow> space m = space n"
  shows "f \<in> measurable N (Sup M)"
proof -
  from M obtain m where "m \<in> M" by auto
  have space_eq: "\<And>n. n \<in> M \<Longrightarrow> space n = space m"
    by (intro const_space \<open>m \<in> M\<close>)
  have "f \<in> measurable N (sigma (\<Union>m\<in>M. space m) (\<Union>m\<in>M. sets m))"
  proof (rule measurable_measure_of)
    show "f \<in> space N \<rightarrow> \<Union>(space ` M)"
      using measurable_space[OF f] M by auto
  qed (auto intro: measurable_sets f dest: sets.sets_into_space)
  also have "measurable N (sigma (\<Union>m\<in>M. space m) (\<Union>m\<in>M. sets m)) = measurable N (Sup M)"
    apply (intro measurable_cong_sets refl)
    apply (subst sets_Sup_eq[OF space_eq M])
    apply simp
    apply (subst sets_measure_of[OF UN_space_closed])
    apply (simp add: space_eq M)
    done
  finally show ?thesis .
qed

lemma measurable_SUP2:
  "I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f \<in> measurable N (M i)) \<Longrightarrow>
    (\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> space (M i) = space (M j)) \<Longrightarrow> f \<in> measurable N (SUP i\<in>I. M i)"
  by (auto intro!: measurable_Sup2)

lemma sets_Sup_sigma:
  assumes [simp]: "M \<noteq> {}" and M: "\<And>m. m \<in> M \<Longrightarrow> m \<subseteq> Pow \<Omega>"
  shows "sets (SUP m\<in>M. sigma \<Omega> m) = sets (sigma \<Omega> (\<Union>M))"
proof -
  { fix a m assume "a \<in> sigma_sets \<Omega> m" "m \<in> M"
    then have "a \<in> sigma_sets \<Omega> (\<Union>M)"
     by induction (auto intro: sigma_sets.intros(2-)) }
  then show "sets (SUP m\<in>M. sigma \<Omega> m) = sets (sigma \<Omega> (\<Union>M))"
    apply (subst sets_Sup_eq[where X="\<Omega>"])
    apply (auto simp add: M) []
    apply auto []
    apply (simp add: space_measure_of_conv M Union_least)
    apply (rule sigma_sets_eqI)
    apply auto
    done
qed

lemma Sup_sigma:
  assumes [simp]: "M \<noteq> {}" and M: "\<And>m. m \<in> M \<Longrightarrow> m \<subseteq> Pow \<Omega>"
  shows "(SUP m\<in>M. sigma \<Omega> m) = (sigma \<Omega> (\<Union>M))"
proof (intro antisym SUP_least)
  have *: "\<Union>M \<subseteq> Pow \<Omega>"
    using M by auto
  show "sigma \<Omega> (\<Union>M) \<le> (SUP m\<in>M. sigma \<Omega> m)"
  proof (intro less_eq_measure.intros(3))
    show "space (sigma \<Omega> (\<Union>M)) = space (SUP m\<in>M. sigma \<Omega> m)"
      "sets (sigma \<Omega> (\<Union>M)) = sets (SUP m\<in>M. sigma \<Omega> m)"
      using sets_Sup_sigma[OF assms] sets_Sup_sigma[OF assms, THEN sets_eq_imp_space_eq]
      by auto
  qed (simp add: emeasure_sigma le_fun_def)
  fix m assume "m \<in> M" then show "sigma \<Omega> m \<le> sigma \<Omega> (\<Union>M)"
    by (subst sigma_le_iff) (auto simp add: M *)
qed

lemma SUP_sigma_sigma:
  "M \<noteq> {} \<Longrightarrow> (\<And>m. m \<in> M \<Longrightarrow> f m \<subseteq> Pow \<Omega>) \<Longrightarrow> (SUP m\<in>M. sigma \<Omega> (f m)) = sigma \<Omega> (\<Union>m\<in>M. f m)"
  using Sup_sigma[of "f`M" \<Omega>] by (auto simp: image_comp)

lemma sets_vimage_Sup_eq:
  assumes *: "M \<noteq> {}" "f \<in> X \<rightarrow> Y" "\<And>m. m \<in> M \<Longrightarrow> space m = Y"
  shows "sets (vimage_algebra X f (Sup M)) = sets (SUP m \<in> M. vimage_algebra X f m)"
  (is "?IS = ?SI")
proof
  show "?IS \<subseteq> ?SI"
    apply (intro sets_image_in_sets measurable_Sup2)
    apply (simp add: space_Sup_eq_UN *)
    apply (simp add: *)
    apply (intro measurable_Sup1)
    apply (rule imageI)
    apply assumption
    apply (rule measurable_vimage_algebra1)
    apply (auto simp: *)
    done
  show "?SI \<subseteq> ?IS"
    apply (intro sets_Sup_in_sets)
    apply (auto simp: *) []
    apply (auto simp: *) []
    apply (elim imageE)
    apply simp
    apply (rule sets_image_in_sets)
    apply simp
    apply (simp add: measurable_def)
    apply (simp add: * space_Sup_eq_UN sets_vimage_algebra2)
    apply (auto intro: in_sets_Sup[OF *(3)])
    done
qed

lemma restrict_space_eq_vimage_algebra':
  "sets (restrict_space M \<Omega>) = sets (vimage_algebra (\<Omega> \<inter> space M) (\<lambda>x. x) M)"
proof -
  have *: "{A \<inter> (\<Omega> \<inter> space M) |A. A \<in> sets M} = {A \<inter> \<Omega> |A. A \<in> sets M}"
    using sets.sets_into_space[of _ M] by blast

  show ?thesis
    unfolding restrict_space_def
    by (subst sets_measure_of)
       (auto simp add: image_subset_iff sets_vimage_algebra * dest: sets.sets_into_space intro!: arg_cong2[where f=sigma_sets])
qed

lemma sigma_le_sets:
  assumes [simp]: "A \<subseteq> Pow X" shows "sets (sigma X A) \<subseteq> sets N \<longleftrightarrow> X \<in> sets N \<and> A \<subseteq> sets N"
proof
  have "X \<in> sigma_sets X A" "A \<subseteq> sigma_sets X A"
    by (auto intro: sigma_sets_top)
  moreover assume "sets (sigma X A) \<subseteq> sets N"
  ultimately show "X \<in> sets N \<and> A \<subseteq> sets N"
    by auto
next
  assume *: "X \<in> sets N \<and> A \<subseteq> sets N"
  { fix Y assume "Y \<in> sigma_sets X A" from this * have "Y \<in> sets N"
      by induction auto }
  then show "sets (sigma X A) \<subseteq> sets N"
    by auto
qed

lemma measurable_iff_sets:
  "f \<in> measurable M N \<longleftrightarrow> (f \<in> space M \<rightarrow> space N \<and> sets (vimage_algebra (space M) f N) \<subseteq> sets M)"
proof -
  have *: "{f -` A \<inter> space M |A. A \<in> sets N} \<subseteq> Pow (space M)"
    by auto
  show ?thesis
    unfolding measurable_def
    by (auto simp add: vimage_algebra_def sigma_le_sets[OF *])
qed

lemma sets_vimage_algebra_space: "X \<in> sets (vimage_algebra X f M)"
  using sets.top[of "vimage_algebra X f M"] by simp

lemma measurable_mono:
  assumes N: "sets N' \<le> sets N" "space N = space N'"
  assumes M: "sets M \<le> sets M'" "space M = space M'"
  shows "measurable M N \<subseteq> measurable M' N'"
  unfolding measurable_def
proof safe
  fix f A assume "f \<in> space M \<rightarrow> space N" "A \<in> sets N'"
  moreover assume "\<forall>y\<in>sets N. f -` y \<inter> space M \<in> sets M" note this[THEN bspec, of A]
  ultimately show "f -` A \<inter> space M' \<in> sets M'"
    using assms by auto
qed (insert N M, auto)

lemma measurable_Sup_measurable:
  assumes f: "f \<in> space N \<rightarrow> A"
  shows "f \<in> measurable N (Sup {M. space M = A \<and> f \<in> measurable N M})"
proof (rule measurable_Sup2)
  show "{M. space M = A \<and> f \<in> measurable N M} \<noteq> {}"
    using f unfolding ex_in_conv[symmetric]
    by (intro exI[of _ "sigma A {}"]) (auto intro!: measurable_measure_of)
qed auto

lemma (in sigma_algebra) sigma_sets_subset':
  assumes a: "a \<subseteq> M" "\<Omega>' \<in> M"
  shows "sigma_sets \<Omega>' a \<subseteq> M"
proof
  show "x \<in> M" if x: "x \<in> sigma_sets \<Omega>' a" for x
    using x by (induct rule: sigma_sets.induct) (insert a, auto)
qed

lemma in_sets_SUP: "i \<in> I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> space (M i) = Y) \<Longrightarrow> X \<in> sets (M i) \<Longrightarrow> X \<in> sets (SUP i\<in>I. M i)"
  by (intro in_sets_Sup[where X=Y]) auto

lemma measurable_SUP1:
  "i \<in> I \<Longrightarrow> f \<in> measurable (M i) N \<Longrightarrow> (\<And>m n. m \<in> I \<Longrightarrow> n \<in> I \<Longrightarrow> space (M m) = space (M n)) \<Longrightarrow>
    f \<in> measurable (SUP i\<in>I. M i) N"
  by (auto intro: measurable_Sup1)

lemma sets_image_in_sets':
  assumes X: "X \<in> sets N"
  assumes f: "\<And>A. A \<in> sets M \<Longrightarrow> f -` A \<inter> X \<in> sets N"
  shows "sets (vimage_algebra X f M) \<subseteq> sets N"
  unfolding sets_vimage_algebra
  by (rule sets.sigma_sets_subset') (auto intro!: measurable_sets X f)

lemma mono_vimage_algebra:
  "sets M \<le> sets N \<Longrightarrow> sets (vimage_algebra X f M) \<subseteq> sets (vimage_algebra X f N)"
  using sets.top[of "sigma X {f -` A \<inter> X |A. A \<in> sets N}"]
  unfolding vimage_algebra_def
  apply (subst (asm) space_measure_of)
  apply auto []
  apply (subst sigma_le_sets)
  apply auto
  done

lemma mono_restrict_space: "sets M \<le> sets N \<Longrightarrow> sets (restrict_space M X) \<subseteq> sets (restrict_space N X)"
  unfolding sets_restrict_space by (rule image_mono)

lemma sets_eq_bot: "sets M = {{}} \<longleftrightarrow> M = bot"
  apply safe
  apply (intro measure_eqI)
  apply auto
  done

lemma sets_eq_bot2: "{{}} = sets M \<longleftrightarrow> M = bot"
  using sets_eq_bot[of M] by blast


lemma (in finite_measure) countable_support:
  "countable {x. measure M {x} \<noteq> 0}"
proof cases
  assume "measure M (space M) = 0"
  with bounded_measure measure_le_0_iff have "{x. measure M {x} \<noteq> 0} = {}"
    by auto
  then show ?thesis
    by simp
next
  let ?M = "measure M (space M)" and ?m = "\<lambda>x. measure M {x}"
  assume "?M \<noteq> 0"
  then have *: "{x. ?m x \<noteq> 0} = (\<Union>n. {x. ?M / Suc n < ?m x})"
    using reals_Archimedean[of "?m x / ?M" for x]
    by (auto simp: field_simps not_le[symmetric] divide_le_0_iff measure_le_0_iff)
  have **: "\<And>n. finite {x. ?M / Suc n < ?m x}"
  proof (rule ccontr)
    fix n assume "infinite {x. ?M / Suc n < ?m x}" (is "infinite ?X")
    then obtain X where "finite X" "card X = Suc (Suc n)" "X \<subseteq> ?X"
      by (metis infinite_arbitrarily_large)
    from this(3) have *: "\<And>x. x \<in> X \<Longrightarrow> ?M / Suc n \<le> ?m x"
      by auto
    { fix x assume "x \<in> X"
      from \<open>?M \<noteq> 0\<close> *[OF this] have "?m x \<noteq> 0" by (auto simp: field_simps measure_le_0_iff)
      then have "{x} \<in> sets M" by (auto dest: measure_notin_sets) }
    note singleton_sets = this
    have "?M < (\<Sum>x\<in>X. ?M / Suc n)"
      using \<open>?M \<noteq> 0\<close>
      by (simp add: \<open>card X = Suc (Suc n)\<close> field_simps less_le)
    also have "\<dots> \<le> (\<Sum>x\<in>X. ?m x)"
      by (rule sum_mono) fact
    also have "\<dots> = measure M (\<Union>x\<in>X. {x})"
      using singleton_sets \<open>finite X\<close>
      by (intro finite_measure_finite_Union[symmetric]) (auto simp: disjoint_family_on_def)
    finally have "?M < measure M (\<Union>x\<in>X. {x})" .
    moreover have "measure M (\<Union>x\<in>X. {x}) \<le> ?M"
      using singleton_sets[THEN sets.sets_into_space] by (intro finite_measure_mono) auto
    ultimately show False by simp
  qed
  show ?thesis
    unfolding * by (intro countable_UN countableI_type countable_finite[OF **])
qed

end
