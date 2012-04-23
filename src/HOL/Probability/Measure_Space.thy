(*  Title:      HOL/Probability/Measure_Space.thy
    Author:     Lawrence C Paulson
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

header {* Measure spaces and their properties *}

theory Measure_Space
imports
  Sigma_Algebra
  "~~/src/HOL/Multivariate_Analysis/Extended_Real_Limits"
begin

lemma suminf_eq_setsum:
  fixes f :: "nat \<Rightarrow> 'a::{comm_monoid_add, t2_space}"
  assumes "finite {i. f i \<noteq> 0}" (is "finite ?P")
  shows "(\<Sum>i. f i) = (\<Sum>i | f i \<noteq> 0. f i)"
proof cases
  assume "?P \<noteq> {}"
  have [dest!]: "\<And>i. Suc (Max ?P) \<le> i \<Longrightarrow> f i = 0"
    using `finite ?P` `?P \<noteq> {}` by (auto simp: Suc_le_eq) 
  have "(\<Sum>i. f i) = (\<Sum>i<Suc (Max ?P). f i)"
    by (rule suminf_finite) auto
  also have "\<dots> = (\<Sum>i | f i \<noteq> 0. f i)"
    using `finite ?P` `?P \<noteq> {}`
    by (intro setsum_mono_zero_right) (auto simp: less_Suc_eq_le)
  finally show ?thesis .
qed simp

lemma suminf_cmult_indicator:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "disjoint_family A" "x \<in> A i" "\<And>i. 0 \<le> f i"
  shows "(\<Sum>n. f n * indicator (A n) x) = f i"
proof -
  have **: "\<And>n. f n * indicator (A n) x = (if n = i then f n else 0 :: ereal)"
    using `x \<in> A i` assms unfolding disjoint_family_on_def indicator_def by auto
  then have "\<And>n. (\<Sum>j<n. f j * indicator (A j) x) = (if i < n then f i else 0 :: ereal)"
    by (auto simp: setsum_cases)
  moreover have "(SUP n. if i < n then f i else 0) = (f i :: ereal)"
  proof (rule ereal_SUPI)
    fix y :: ereal assume "\<And>n. n \<in> UNIV \<Longrightarrow> (if i < n then f i else 0) \<le> y"
    from this[of "Suc i"] show "f i \<le> y" by auto
  qed (insert assms, simp)
  ultimately show ?thesis using assms
    by (subst suminf_ereal_eq_SUPR) (auto simp: indicator_def)
qed

lemma suminf_indicator:
  assumes "disjoint_family A"
  shows "(\<Sum>n. indicator (A n) x :: ereal) = indicator (\<Union>i. A i) x"
proof cases
  assume *: "x \<in> (\<Union>i. A i)"
  then obtain i where "x \<in> A i" by auto
  from suminf_cmult_indicator[OF assms(1), OF `x \<in> A i`, of "\<lambda>k. 1"]
  show ?thesis using * by simp
qed simp

text {*
  The type for emeasure spaces is already defined in @{theory Sigma_Algebra}, as it is also used to
  represent sigma algebras (with an arbitrary emeasure).
*}

section "Extend binary sets"

lemma LIMSEQ_binaryset:
  assumes f: "f {} = 0"
  shows  "(\<lambda>n. \<Sum>i<n. f (binaryset A B i)) ----> f A + f B"
proof -
  have "(\<lambda>n. \<Sum>i < Suc (Suc n). f (binaryset A B i)) = (\<lambda>n. f A + f B)"
    proof
      fix n
      show "(\<Sum>i < Suc (Suc n). f (binaryset A B i)) = f A + f B"
        by (induct n)  (auto simp add: binaryset_def f)
    qed
  moreover
  have "... ----> f A + f B" by (rule tendsto_const)
  ultimately
  have "(\<lambda>n. \<Sum>i< Suc (Suc n). f (binaryset A B i)) ----> f A + f B"
    by metis
  hence "(\<lambda>n. \<Sum>i< n+2. f (binaryset A B i)) ----> f A + f B"
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

section {* Properties of a premeasure @{term \<mu>} *}

text {*
  The definitions for @{const positive} and @{const countably_additive} should be here, by they are
  necessary to define @{typ "'a measure"} in @{theory Sigma_Algebra}.
*}

definition additive where
  "additive M \<mu> \<longleftrightarrow> (\<forall>x\<in>M. \<forall>y\<in>M. x \<inter> y = {} \<longrightarrow> \<mu> (x \<union> y) = \<mu> x + \<mu> y)"

definition increasing where
  "increasing M \<mu> \<longleftrightarrow> (\<forall>x\<in>M. \<forall>y\<in>M. x \<subseteq> y \<longrightarrow> \<mu> x \<le> \<mu> y)"

lemma positiveD_empty:
  "positive M f \<Longrightarrow> f {} = 0"
  by (auto simp add: positive_def)

lemma additiveD:
  "additive M f \<Longrightarrow> x \<inter> y = {} \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> f (x \<union> y) = f x + f y"
  by (auto simp add: additive_def)

lemma increasingD:
  "increasing M f \<Longrightarrow> x \<subseteq> y \<Longrightarrow> x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> f x \<le> f y"
  by (auto simp add: increasing_def)

lemma countably_additiveI:
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
    using A by (subst f(2)[THEN additiveD]) (auto simp: disjointed_incseq)
  also have "A n \<union> disjointed A (Suc n) = A (Suc n)"
    using `incseq A` by (auto dest: incseq_SucD simp: disjointed_incseq)
  finally show ?case .
qed simp

lemma (in ring_of_sets) additive_sum:
  fixes A:: "'i \<Rightarrow> 'a set"
  assumes f: "positive M f" and ad: "additive M f" and "finite S"
      and A: "A`S \<subseteq> M"
      and disj: "disjoint_family_on A S"
  shows  "(\<Sum>i\<in>S. f (A i)) = f (\<Union>i\<in>S. A i)"
using `finite S` disj A proof induct
  case empty show ?case using f by (simp add: positive_def)
next
  case (insert s S)
  then have "A s \<inter> (\<Union>i\<in>S. A i) = {}"
    by (auto simp add: disjoint_family_on_def neq_iff)
  moreover
  have "A s \<in> M" using insert by blast
  moreover have "(\<Union>i\<in>S. A i) \<in> M"
    using insert `finite S` by auto
  moreover
  ultimately have "f (A s \<union> (\<Union>i\<in>S. A i)) = f (A s) + f(\<Union>i\<in>S. A i)"
    using ad UNION_in_sets A by (auto simp add: additive_def)
  with insert show ?case using ad disjoint_family_on_mono[of S "insert s S" A]
    by (auto simp add: additive_def subset_insertI)
qed

lemma (in ring_of_sets) additive_increasing:
  assumes posf: "positive M f" and addf: "additive M f"
  shows "increasing M f"
proof (auto simp add: increasing_def)
  fix x y
  assume xy: "x \<in> M" "y \<in> M" "x \<subseteq> y"
  then have "y - x \<in> M" by auto
  then have "0 \<le> f (y-x)" using posf[unfolded positive_def] by auto
  then have "f x + 0 \<le> f x + f (y-x)" by (intro add_left_mono) auto
  also have "... = f (x \<union> (y-x))" using addf
    by (auto simp add: additive_def) (metis Diff_disjoint Un_Diff_cancel Diff xy(1,2))
  also have "... = f y"
    by (metis Un_Diff_cancel Un_absorb1 xy(3))
  finally show "f x \<le> f y" by simp
qed

lemma (in ring_of_sets) countably_additive_additive:
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
  fixes A:: "nat \<Rightarrow> 'a set" and  f :: "'a set \<Rightarrow> ereal"
  assumes f: "positive M f" and ad: "additive M f"
      and inc: "increasing M f"
      and A: "range A \<subseteq> M"
      and disj: "disjoint_family A"
  shows  "(\<Sum>i. f (A i)) \<le> f \<Omega>"
proof (safe intro!: suminf_bound)
  fix N
  note disj_N = disjoint_family_on_mono[OF _ disj, of "{..<N}"]
  have "(\<Sum>i<N. f (A i)) = f (\<Union>i\<in>{..<N}. A i)"
    using A by (intro additive_sum [OF f ad _ _]) (auto simp: disj_N)
  also have "... \<le> f \<Omega>" using space_closed A
    by (intro increasingD[OF inc] finite_UN) auto
  finally show "(\<Sum>i<N. f (A i)) \<le> f \<Omega>" by simp
qed (insert f A, auto simp: positive_def)

lemma (in ring_of_sets) countably_additiveI_finite:
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
    by (auto simp: positiveD_empty[OF `positive M \<mu>`])
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
    by (rule suminf_eq_setsum)
  also have "\<dots> = (\<Sum>i | F i \<noteq> {}. \<mu> (F i))"
    using fin_not_empty F_subset by (rule setsum_mono_zero_left) auto
  also have "\<dots> = \<mu> (\<Union>i\<in>{i. F i \<noteq> {}}. F i)"
    using `positive M \<mu>` `additive M \<mu>` fin_not_empty disj_not_empty F by (intro additive_sum) auto
  also have "\<dots> = \<mu> (\<Union>i. F i)"
    by (rule arg_cong[where f=\<mu>]) auto
  finally show "(\<Sum>i. \<mu> (F i)) = \<mu> (\<Union>i. F i)" .
qed

section {* Properties of @{const emeasure} *}

lemma emeasure_positive: "positive (sets M) (emeasure M)"
  by (cases M) (auto simp: sets_def emeasure_def Abs_measure_inverse measure_space_def)

lemma emeasure_empty[simp, intro]: "emeasure M {} = 0"
  using emeasure_positive[of M] by (simp add: positive_def)

lemma emeasure_nonneg[intro!]: "0 \<le> emeasure M A"
  using emeasure_notin_sets[of A M] emeasure_positive[of M]
  by (cases "A \<in> sets M") (auto simp: positive_def)

lemma emeasure_not_MInf[simp]: "emeasure M A \<noteq> - \<infinity>"
  using emeasure_nonneg[of M A] by auto
  
lemma emeasure_countably_additive: "countably_additive (sets M) (emeasure M)"
  by (cases M) (auto simp: sets_def emeasure_def Abs_measure_inverse measure_space_def)

lemma suminf_emeasure:
  "range A \<subseteq> sets M \<Longrightarrow> disjoint_family A \<Longrightarrow> (\<Sum>i. emeasure M (A i)) = emeasure M (\<Union>i. A i)"
  using countable_UN[of A UNIV M] emeasure_countably_additive[of M]
  by (simp add: countably_additive_def)

lemma emeasure_additive: "additive (sets M) (emeasure M)"
  by (metis countably_additive_additive emeasure_positive emeasure_countably_additive)

lemma plus_emeasure:
  "a \<in> sets M \<Longrightarrow> b \<in> sets M \<Longrightarrow> a \<inter> b = {} \<Longrightarrow> emeasure M a + emeasure M b = emeasure M (a \<union> b)"
  using additiveD[OF emeasure_additive] ..

lemma setsum_emeasure:
  "F`I \<subseteq> sets M \<Longrightarrow> disjoint_family_on F I \<Longrightarrow> finite I \<Longrightarrow>
    (\<Sum>i\<in>I. emeasure M (F i)) = emeasure M (\<Union>i\<in>I. F i)"
  by (metis additive_sum emeasure_positive emeasure_additive)

lemma emeasure_mono:
  "a \<subseteq> b \<Longrightarrow> b \<in> sets M \<Longrightarrow> emeasure M a \<le> emeasure M b"
  by (metis additive_increasing emeasure_additive emeasure_nonneg emeasure_notin_sets
            emeasure_positive increasingD)

lemma emeasure_space:
  "emeasure M A \<le> emeasure M (space M)"
  by (metis emeasure_mono emeasure_nonneg emeasure_notin_sets sets_into_space top)

lemma emeasure_compl:
  assumes s: "s \<in> sets M" and fin: "emeasure M s \<noteq> \<infinity>"
  shows "emeasure M (space M - s) = emeasure M (space M) - emeasure M s"
proof -
  from s have "0 \<le> emeasure M s" by auto
  have "emeasure M (space M) = emeasure M (s \<union> (space M - s))" using s
    by (metis Un_Diff_cancel Un_absorb1 s sets_into_space)
  also have "... = emeasure M s + emeasure M (space M - s)"
    by (rule plus_emeasure[symmetric]) (auto simp add: s)
  finally have "emeasure M (space M) = emeasure M s + emeasure M (space M - s)" .
  then show ?thesis
    using fin `0 \<le> emeasure M s`
    unfolding ereal_eq_minus_iff by (auto simp: ac_simps)
qed

lemma emeasure_Diff:
  assumes finite: "emeasure M B \<noteq> \<infinity>"
  and measurable: "A \<in> sets M" "B \<in> sets M" "B \<subseteq> A"
  shows "emeasure M (A - B) = emeasure M A - emeasure M B"
proof -
  have "0 \<le> emeasure M B" using assms by auto
  have "(A - B) \<union> B = A" using `B \<subseteq> A` by auto
  then have "emeasure M A = emeasure M ((A - B) \<union> B)" by simp
  also have "\<dots> = emeasure M (A - B) + emeasure M B"
    using measurable by (subst plus_emeasure[symmetric]) auto
  finally show "emeasure M (A - B) = emeasure M A - emeasure M B"
    unfolding ereal_eq_minus_iff
    using finite `0 \<le> emeasure M B` by auto
qed

lemma emeasure_countable_increasing:
  assumes A: "range A \<subseteq> sets M"
      and A0: "A 0 = {}"
      and ASuc: "\<And>n. A n \<subseteq> A (Suc n)"
  shows "(SUP n. emeasure M (A n)) = emeasure M (\<Union>i. A i)"
proof -
  { fix n
    have "emeasure M (A n) = (\<Sum>i<n. emeasure M (A (Suc i) - A i))"
      proof (induct n)
        case 0 thus ?case by (auto simp add: A0)
      next
        case (Suc m)
        have "A (Suc m) = A m \<union> (A (Suc m) - A m)"
          by (metis ASuc Un_Diff_cancel Un_absorb1)
        hence "emeasure M (A (Suc m)) =
               emeasure M (A m) + emeasure M (A (Suc m) - A m)"
          by (subst plus_emeasure)
             (auto simp add: emeasure_additive range_subsetD [OF A])
        with Suc show ?case
          by simp
      qed }
  note Meq = this
  have Aeq: "(\<Union>i. A (Suc i) - A i) = (\<Union>i. A i)"
    proof (rule UN_finite2_eq [where k=1], simp)
      fix i
      show "(\<Union>i\<in>{0..<i}. A (Suc i) - A i) = (\<Union>i\<in>{0..<Suc i}. A i)"
        proof (induct i)
          case 0 thus ?case by (simp add: A0)
        next
          case (Suc i)
          thus ?case
            by (auto simp add: atLeastLessThanSuc intro: subsetD [OF ASuc])
        qed
    qed
  have A1: "\<And>i. A (Suc i) - A i \<in> sets M"
    by (metis A Diff range_subsetD)
  have A2: "(\<Union>i. A (Suc i) - A i) \<in> sets M"
    by (blast intro: range_subsetD [OF A])
  have "(SUP n. \<Sum>i<n. emeasure M (A (Suc i) - A i)) = (\<Sum>i. emeasure M (A (Suc i) - A i))"
    using A by (auto intro!: suminf_ereal_eq_SUPR[symmetric])
  also have "\<dots> = emeasure M (\<Union>i. A (Suc i) - A i)"
    by (rule suminf_emeasure)
       (auto simp add: disjoint_family_Suc ASuc A1 A2)
  also have "... =  emeasure M (\<Union>i. A i)"
    by (simp add: Aeq)
  finally have "(SUP n. \<Sum>i<n. emeasure M (A (Suc i) - A i)) = emeasure M (\<Union>i. A i)" .
  then show ?thesis by (auto simp add: Meq)
qed

lemma SUP_emeasure_incseq:
  assumes A: "range A \<subseteq> sets M" and "incseq A"
  shows "(SUP n. emeasure M (A n)) = emeasure M (\<Union>i. A i)"
proof -
  have *: "(SUP n. emeasure M (nat_case {} A (Suc n))) = (SUP n. emeasure M (nat_case {} A n))"
    using A by (auto intro!: SUPR_eq exI split: nat.split)
  have ueq: "(\<Union>i. nat_case {} A i) = (\<Union>i. A i)"
    by (auto simp add: split: nat.splits)
  have meq: "\<And>n. emeasure M (A n) = (emeasure M \<circ> nat_case {} A) (Suc n)"
    by simp
  have "(SUP n. emeasure M (nat_case {} A n)) = emeasure M (\<Union>i. nat_case {} A i)"
    using range_subsetD[OF A] incseq_SucD[OF `incseq A`]
    by (force split: nat.splits intro!: emeasure_countable_increasing)
  also have "emeasure M (\<Union>i. nat_case {} A i) = emeasure M (\<Union>i. A i)"
    by (simp add: ueq)
  finally have "(SUP n. emeasure M (nat_case {} A n)) = emeasure M (\<Union>i. A i)" .
  thus ?thesis unfolding meq * comp_def .
qed

lemma incseq_emeasure:
  assumes "range B \<subseteq> sets M" "incseq B"
  shows "incseq (\<lambda>i. emeasure M (B i))"
  using assms by (auto simp: incseq_def intro!: emeasure_mono)

lemma Lim_emeasure_incseq:
  assumes A: "range A \<subseteq> sets M" "incseq A"
  shows "(\<lambda>i. (emeasure M (A i))) ----> emeasure M (\<Union>i. A i)"
  using LIMSEQ_ereal_SUPR[OF incseq_emeasure, OF A]
    SUP_emeasure_incseq[OF A] by simp

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
  hence *: "emeasure M (\<Inter>i. A i) \<noteq> \<infinity>" using finite[of 0] by auto

  have A0: "0 \<le> emeasure M (A 0)" using A by auto

  have "emeasure M (A 0) - (INF n. emeasure M (A n)) = emeasure M (A 0) + (SUP n. - emeasure M (A n))"
    by (simp add: ereal_SUPR_uminus minus_ereal_def)
  also have "\<dots> = (SUP n. emeasure M (A 0) - emeasure M (A n))"
    unfolding minus_ereal_def using A0 assms
    by (subst SUPR_ereal_add) (auto simp add: decseq_emeasure)
  also have "\<dots> = (SUP n. emeasure M (A 0 - A n))"
    using A finite `decseq A`[unfolded decseq_def] by (subst emeasure_Diff) auto
  also have "\<dots> = emeasure M (\<Union>i. A 0 - A i)"
  proof (rule SUP_emeasure_incseq)
    show "range (\<lambda>n. A 0 - A n) \<subseteq> sets M"
      using A by auto
    show "incseq (\<lambda>n. A 0 - A n)"
      using `decseq A` by (auto simp add: incseq_def decseq_def)
  qed
  also have "\<dots> = emeasure M (A 0) - emeasure M (\<Inter>i. A i)"
    using A finite * by (simp, subst emeasure_Diff) auto
  finally show ?thesis
    unfolding ereal_minus_eq_minus_iff using finite A0 by auto
qed

lemma Lim_emeasure_decseq:
  assumes A: "range A \<subseteq> sets M" "decseq A" and fin: "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
  shows "(\<lambda>i. emeasure M (A i)) ----> emeasure M (\<Inter>i. A i)"
  using LIMSEQ_ereal_INFI[OF decseq_emeasure, OF A]
  using INF_emeasure_decseq[OF A fin] by simp

lemma emeasure_subadditive:
  assumes measurable: "A \<in> sets M" "B \<in> sets M"
  shows "emeasure M (A \<union> B) \<le> emeasure M A + emeasure M B"
proof -
  from plus_emeasure[of A M "B - A"]
  have "emeasure M (A \<union> B) = emeasure M A + emeasure M (B - A)"
    using assms by (simp add: Diff)
  also have "\<dots> \<le> emeasure M A + emeasure M B"
    using assms by (auto intro!: add_left_mono emeasure_mono)
  finally show ?thesis .
qed

lemma emeasure_subadditive_finite:
  assumes "finite I" "A ` I \<subseteq> sets M"
  shows "emeasure M (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. emeasure M (A i))"
using assms proof induct
  case (insert i I)
  then have "emeasure M (\<Union>i\<in>insert i I. A i) = emeasure M (A i \<union> (\<Union>i\<in>I. A i))"
    by simp
  also have "\<dots> \<le> emeasure M (A i) + emeasure M (\<Union>i\<in>I. A i)"
    using insert by (intro emeasure_subadditive finite_UN) auto
  also have "\<dots> \<le> emeasure M (A i) + (\<Sum>i\<in>I. emeasure M (A i))"
    using insert by (intro add_mono) auto
  also have "\<dots> = (\<Sum>i\<in>insert i I. emeasure M (A i))"
    using insert by auto
  finally show ?case .
qed simp

lemma emeasure_subadditive_countably:
  assumes "range f \<subseteq> sets M"
  shows "emeasure M (\<Union>i. f i) \<le> (\<Sum>i. emeasure M (f i))"
proof -
  have "emeasure M (\<Union>i. f i) = emeasure M (\<Union>i. disjointed f i)"
    unfolding UN_disjointed_eq ..
  also have "\<dots> = (\<Sum>i. emeasure M (disjointed f i))"
    using range_disjointed_sets[OF assms] suminf_emeasure[of "disjointed f"]
    by (simp add:  disjoint_family_disjointed comp_def)
  also have "\<dots> \<le> (\<Sum>i. emeasure M (f i))"
    using range_disjointed_sets[OF assms] assms
    by (auto intro!: suminf_le_pos emeasure_mono disjointed_subset)
  finally show ?thesis .
qed

lemma emeasure_insert:
  assumes sets: "{x} \<in> sets M" "A \<in> sets M" and "x \<notin> A"
  shows "emeasure M (insert x A) = emeasure M {x} + emeasure M A"
proof -
  have "{x} \<inter> A = {}" using `x \<notin> A` by auto
  from plus_emeasure[OF sets this] show ?thesis by simp
qed

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
      using `disjoint_family_on B S`
      unfolding disjoint_family_on_def by auto
  qed (insert assms, auto)
  also have "(\<Union>i\<in>S. A \<inter> (B i)) = A"
    using A by auto
  finally show ?thesis by simp
qed

lemma emeasure_eq_0:
  "N \<in> sets M \<Longrightarrow> emeasure M N = 0 \<Longrightarrow> K \<subseteq> N \<Longrightarrow> emeasure M K = 0"
  by (metis emeasure_mono emeasure_nonneg order_eq_iff)

lemma emeasure_UN_eq_0:
  assumes "\<And>i::nat. emeasure M (N i) = 0" and "range N \<subseteq> sets M"
  shows "emeasure M (\<Union> i. N i) = 0"
proof -
  have "0 \<le> emeasure M (\<Union> i. N i)" using assms by auto
  moreover have "emeasure M (\<Union> i. N i) \<le> 0"
    using emeasure_subadditive_countably[OF assms(2)] assms(1) by simp
  ultimately show ?thesis by simp
qed

lemma measure_eqI_finite:
  assumes [simp]: "sets M = Pow A" "sets N = Pow A" and "finite A"
  assumes eq: "\<And>a. a \<in> A \<Longrightarrow> emeasure M {a} = emeasure N {a}"
  shows "M = N"
proof (rule measure_eqI)
  fix X assume "X \<in> sets M"
  then have X: "X \<subseteq> A" by auto
  then have "emeasure M X = (\<Sum>a\<in>X. emeasure M {a})"
    using `finite A` by (subst emeasure_eq_setsum_singleton) (auto dest: finite_subset)
  also have "\<dots> = (\<Sum>a\<in>X. emeasure N {a})"
    using X eq by (auto intro!: setsum_cong)
  also have "\<dots> = emeasure N X"
    using X `finite A` by (subst emeasure_eq_setsum_singleton) (auto dest: finite_subset)
  finally show "emeasure M X = emeasure N X" .
qed simp

lemma measure_eqI_generator_eq:
  fixes M N :: "'a measure" and E :: "'a set set" and A :: "nat \<Rightarrow> 'a set"
  assumes "Int_stable E" "E \<subseteq> Pow \<Omega>"
  and eq: "\<And>X. X \<in> E \<Longrightarrow> emeasure M X = emeasure N X"
  and M: "sets M = sigma_sets \<Omega> E"
  and N: "sets N = sigma_sets \<Omega> E"
  and A: "range A \<subseteq> E" "incseq A" "(\<Union>i. A i) = \<Omega>" "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
  shows "M = N"
proof -
  let ?D = "\<lambda>F. {D. D \<in> sigma_sets \<Omega> E \<and> emeasure M (F \<inter> D) = emeasure N (F \<inter> D)}"
  interpret S: sigma_algebra \<Omega> "sigma_sets \<Omega> E" by (rule sigma_algebra_sigma_sets) fact
  { fix F assume "F \<in> E" and "emeasure M F \<noteq> \<infinity>"
    then have [intro]: "F \<in> sigma_sets \<Omega> E" by auto
    have "emeasure N F \<noteq> \<infinity>" using `emeasure M F \<noteq> \<infinity>` `F \<in> E` eq by simp
    interpret D: dynkin_system \<Omega> "?D F"
    proof (rule dynkin_systemI, simp_all)
      fix A assume "A \<in> sigma_sets \<Omega> E \<and> emeasure M (F \<inter> A) = emeasure N (F \<inter> A)"
      then show "A \<subseteq> \<Omega>" using S.sets_into_space by auto
    next
      have "F \<inter> \<Omega> = F" using `F \<in> E` `E \<subseteq> Pow \<Omega>` by auto
      then show "emeasure M (F \<inter> \<Omega>) = emeasure N (F \<inter> \<Omega>)"
        using `F \<in> E` eq by (auto intro: sigma_sets_top)
    next
      fix A assume *: "A \<in> sigma_sets \<Omega> E \<and> emeasure M (F \<inter> A) = emeasure N (F \<inter> A)"
      then have **: "F \<inter> (\<Omega> - A) = F - (F \<inter> A)"
        and [intro]: "F \<inter> A \<in> sigma_sets \<Omega> E"
        using `F \<in> E` S.sets_into_space by auto
      have "emeasure N (F \<inter> A) \<le> emeasure N F" by (auto intro!: emeasure_mono simp: M N)
      then have "emeasure N (F \<inter> A) \<noteq> \<infinity>" using `emeasure N F \<noteq> \<infinity>` by auto
      have "emeasure M (F \<inter> A) \<le> emeasure M F" by (auto intro!: emeasure_mono simp: M N)
      then have "emeasure M (F \<inter> A) \<noteq> \<infinity>" using `emeasure M F \<noteq> \<infinity>` by auto
      then have "emeasure M (F \<inter> (\<Omega> - A)) = emeasure M F - emeasure M (F \<inter> A)" unfolding **
        using `F \<inter> A \<in> sigma_sets \<Omega> E` by (auto intro!: emeasure_Diff simp: M N)
      also have "\<dots> = emeasure N F - emeasure N (F \<inter> A)" using eq `F \<in> E` * by simp
      also have "\<dots> = emeasure N (F \<inter> (\<Omega> - A))" unfolding **
        using `F \<inter> A \<in> sigma_sets \<Omega> E` `emeasure N (F \<inter> A) \<noteq> \<infinity>`
        by (auto intro!: emeasure_Diff[symmetric] simp: M N)
      finally show "\<Omega> - A \<in> sigma_sets \<Omega> E \<and> emeasure M (F \<inter> (\<Omega> - A)) = emeasure N (F \<inter> (\<Omega> - A))"
        using * by auto
    next
      fix A :: "nat \<Rightarrow> 'a set"
      assume "disjoint_family A" "range A \<subseteq> {X \<in> sigma_sets \<Omega> E. emeasure M (F \<inter> X) = emeasure N (F \<inter> X)}"
      then have A: "range (\<lambda>i. F \<inter> A i) \<subseteq> sigma_sets \<Omega> E" "F \<inter> (\<Union>x. A x) = (\<Union>x. F \<inter> A x)"
        "disjoint_family (\<lambda>i. F \<inter> A i)" "\<And>i. emeasure M (F \<inter> A i) = emeasure N (F \<inter> A i)" "range A \<subseteq> sigma_sets \<Omega> E"
        by (auto simp: disjoint_family_on_def subset_eq)
      then show "(\<Union>x. A x) \<in> sigma_sets \<Omega> E \<and> emeasure M (F \<inter> (\<Union>x. A x)) = emeasure N (F \<inter> (\<Union>x. A x))"
        by (auto simp: M N suminf_emeasure[symmetric] simp del: UN_simps)
    qed
    have *: "sigma_sets \<Omega> E = ?D F"
      using `F \<in> E` `Int_stable E`
      by (intro D.dynkin_lemma) (auto simp add: Int_stable_def eq)
    have "\<And>D. D \<in> sigma_sets \<Omega> E \<Longrightarrow> emeasure M (F \<inter> D) = emeasure N (F \<inter> D)"
      by (subst (asm) *) auto }
  note * = this
  show "M = N"
  proof (rule measure_eqI)
    show "sets M = sets N"
      using M N by simp
    fix X assume "X \<in> sets M"
    then have "X \<in> sigma_sets \<Omega> E"
      using M by simp
    let ?A = "\<lambda>i. A i \<inter> X"
    have "range ?A \<subseteq> sigma_sets \<Omega> E" "incseq ?A"
      using A(1,2) `X \<in> sigma_sets \<Omega> E` by (auto simp: incseq_def)
    moreover
    { fix i have "emeasure M (?A i) = emeasure N (?A i)"
        using *[of "A i" X] `X \<in> sigma_sets \<Omega> E` A finite by auto }
    ultimately show "emeasure M X = emeasure N X"
      using SUP_emeasure_incseq[of ?A M] SUP_emeasure_incseq[of ?A N] A(3) `X \<in> sigma_sets \<Omega> E`
      by (auto simp: M N SUP_emeasure_incseq)
  qed
qed

lemma measure_of_of_measure: "measure_of (space M) (sets M) (emeasure M) = M"
proof (intro measure_eqI emeasure_measure_of_sigma)
  show "sigma_algebra (space M) (sets M)" ..
  show "positive (sets M) (emeasure M)"
    by (simp add: positive_def emeasure_nonneg)
  show "countably_additive (sets M) (emeasure M)"
    by (simp add: emeasure_countably_additive)
qed simp_all

section "@{text \<mu>}-null sets"

definition null_sets :: "'a measure \<Rightarrow> 'a set set" where
  "null_sets M = {N\<in>sets M. emeasure M N = 0}"

lemma null_setsD1[dest]: "A \<in> null_sets M \<Longrightarrow> emeasure M A = 0"
  by (simp add: null_sets_def)

lemma null_setsD2[dest]: "A \<in> null_sets M \<Longrightarrow> A \<in> sets M"
  unfolding null_sets_def by simp

lemma null_setsI[intro]: "emeasure M A = 0 \<Longrightarrow> A \<in> sets M \<Longrightarrow> A \<in> null_sets M"
  unfolding null_sets_def by simp

interpretation null_sets: ring_of_sets "space M" "null_sets M" for M
proof
  show "null_sets M \<subseteq> Pow (space M)"
    using sets_into_space by auto
  show "{} \<in> null_sets M"
    by auto
  fix A B assume sets: "A \<in> null_sets M" "B \<in> null_sets M"
  then have "A \<in> sets M" "B \<in> sets M"
    by auto
  moreover then have "emeasure M (A \<union> B) \<le> emeasure M A + emeasure M B"
    "emeasure M (A - B) \<le> emeasure M A"
    by (auto intro!: emeasure_subadditive emeasure_mono)
  moreover have "emeasure M B = 0" "emeasure M A = 0"
    using sets by auto
  ultimately show "A - B \<in> null_sets M" "A \<union> B \<in> null_sets M"
    by (auto intro!: antisym)
qed

lemma UN_from_nat: "(\<Union>i. N i) = (\<Union>i. N (Countable.from_nat i))"
proof -
  have "(\<Union>i. N i) = (\<Union>i. (N \<circ> Countable.from_nat) i)"
    unfolding SUP_def image_compose
    unfolding surj_from_nat ..
  then show ?thesis by simp
qed

lemma null_sets_UN[intro]:
  assumes "\<And>i::'i::countable. N i \<in> null_sets M"
  shows "(\<Union>i. N i) \<in> null_sets M"
proof (intro conjI CollectI null_setsI)
  show "(\<Union>i. N i) \<in> sets M" using assms by auto
  have "0 \<le> emeasure M (\<Union>i. N i)" by (rule emeasure_nonneg)
  moreover have "emeasure M (\<Union>i. N i) \<le> (\<Sum>n. emeasure M (N (Countable.from_nat n)))"
    unfolding UN_from_nat[of N]
    using assms by (intro emeasure_subadditive_countably) auto
  ultimately show "emeasure M (\<Union>i. N i) = 0"
    using assms by (auto simp: null_setsD1)
qed

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

section "Formalize almost everywhere"

definition ae_filter :: "'a measure \<Rightarrow> 'a filter" where
  "ae_filter M = Abs_filter (\<lambda>P. \<exists>N\<in>null_sets M. {x \<in> space M. \<not> P x} \<subseteq> N)"

abbreviation
  almost_everywhere :: "'a measure \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "almost_everywhere M P \<equiv> eventually P (ae_filter M)"

syntax
  "_almost_everywhere" :: "pttrn \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool" ("AE _ in _. _" [0,0,10] 10)

translations
  "AE x in M. P" == "CONST almost_everywhere M (%x. P)"

lemma eventually_ae_filter:
  fixes M P
  defines [simp]: "F \<equiv> \<lambda>P. \<exists>N\<in>null_sets M. {x \<in> space M. \<not> P x} \<subseteq> N" 
  shows "eventually P (ae_filter M) \<longleftrightarrow> F P"
  unfolding ae_filter_def F_def[symmetric]
proof (rule eventually_Abs_filter)
  show "is_filter F"
  proof
    fix P Q assume "F P" "F Q"
    then obtain N L where N: "N \<in> null_sets M" "{x \<in> space M. \<not> P x} \<subseteq> N"
      and L: "L \<in> null_sets M" "{x \<in> space M. \<not> Q x} \<subseteq> L"
      by auto
    then have "L \<union> N \<in> null_sets M" "{x \<in> space M. \<not> (P x \<and> Q x)} \<subseteq> L \<union> N" by auto
    then show "F (\<lambda>x. P x \<and> Q x)" by auto
  next
    fix P Q assume "F P"
    then obtain N where N: "N \<in> null_sets M" "{x \<in> space M. \<not> P x} \<subseteq> N" by auto
    moreover assume "\<forall>x. P x \<longrightarrow> Q x"
    ultimately have "N \<in> null_sets M" "{x \<in> space M. \<not> Q x} \<subseteq> N" by auto
    then show "F Q" by auto
  qed auto
qed

lemma AE_I':
  "N \<in> null_sets M \<Longrightarrow> {x\<in>space M. \<not> P x} \<subseteq> N \<Longrightarrow> (AE x in M. P x)"
  unfolding eventually_ae_filter by auto

lemma AE_iff_null:
  assumes "{x\<in>space M. \<not> P x} \<in> sets M" (is "?P \<in> sets M")
  shows "(AE x in M. P x) \<longleftrightarrow> {x\<in>space M. \<not> P x} \<in> null_sets M"
proof
  assume "AE x in M. P x" then obtain N where N: "N \<in> sets M" "?P \<subseteq> N" "emeasure M N = 0"
    unfolding eventually_ae_filter by auto
  have "0 \<le> emeasure M ?P" by auto
  moreover have "emeasure M ?P \<le> emeasure M N"
    using assms N(1,2) by (auto intro: emeasure_mono)
  ultimately have "emeasure M ?P = 0" unfolding `emeasure M N = 0` by auto
  then show "?P \<in> null_sets M" using assms by auto
next
  assume "?P \<in> null_sets M" with assms show "AE x in M. P x" by (auto intro: AE_I')
qed

lemma AE_iff_null_sets:
  "N \<in> sets M \<Longrightarrow> N \<in> null_sets M \<longleftrightarrow> (AE x in M. x \<notin> N)"
  using Int_absorb1[OF sets_into_space, of N M]
  by (subst AE_iff_null) (auto simp: Int_def[symmetric])

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
    have "0 \<le> emeasure M (A \<union> B)" using A B by auto
    moreover have "emeasure M (A \<union> B) \<le> 0"
      using emeasure_subadditive[of A M B] A B by auto
    ultimately show "A \<union> B \<in> sets M" "emeasure M (A \<union> B) = 0" using A B by auto
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

lemma AE_finite_all:
  assumes f: "finite S" shows "(AE x in M. \<forall>i\<in>S. P i x) \<longleftrightarrow> (\<forall>i\<in>S. AE x in M. P i x)"
  using f by induct auto

lemma AE_finite_allI:
  assumes "finite S"
  shows "(\<And>s. s \<in> S \<Longrightarrow> AE x in M. Q s x) \<Longrightarrow> AE x in M. \<forall>s\<in>S. Q s x"
  using AE_finite_all[OF `finite S`] by auto

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
    using N A B sets_into_space by (auto intro!: emeasure_mono)
  also have "emeasure M (B - N) = emeasure M B"
    using N B by (subst emeasure_Diff_null_set) auto
  finally show ?thesis .
qed (simp add: emeasure_nonneg emeasure_notin_sets)

lemma emeasure_eq_AE:
  assumes iff: "AE x in M. x \<in> A \<longleftrightarrow> x \<in> B"
  assumes A: "A \<in> sets M" and B: "B \<in> sets M"
  shows "emeasure M A = emeasure M B"
  using assms by (safe intro!: antisym emeasure_mono_AE) auto

section {* @{text \<sigma>}-finite Measures *}

locale sigma_finite_measure =
  fixes M :: "'a measure"
  assumes sigma_finite: "\<exists>A::nat \<Rightarrow> 'a set.
    range A \<subseteq> sets M \<and> (\<Union>i. A i) = space M \<and> (\<forall>i. emeasure M (A i) \<noteq> \<infinity>)"

lemma (in sigma_finite_measure) sigma_finite_disjoint:
  obtains A :: "nat \<Rightarrow> 'a set"
  where "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" "\<And>i. emeasure M (A i) \<noteq> \<infinity>" "disjoint_family A"
proof atomize_elim
  case goal1
  obtain A :: "nat \<Rightarrow> 'a set" where
    range: "range A \<subseteq> sets M" and
    space: "(\<Union>i. A i) = space M" and
    measure: "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
    using sigma_finite by auto
  note range' = range_disjointed_sets[OF range] range
  { fix i
    have "emeasure M (disjointed A i) \<le> emeasure M (A i)"
      using range' disjointed_subset[of A i] by (auto intro!: emeasure_mono)
    then have "emeasure M (disjointed A i) \<noteq> \<infinity>"
      using measure[of i] by auto }
  with disjoint_family_disjointed UN_disjointed_eq[of A] space range'
  show ?case by (auto intro!: exI[of _ "disjointed A"])
qed

lemma (in sigma_finite_measure) sigma_finite_incseq:
  obtains A :: "nat \<Rightarrow> 'a set"
  where "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" "\<And>i. emeasure M (A i) \<noteq> \<infinity>" "incseq A"
proof atomize_elim
  case goal1
  obtain F :: "nat \<Rightarrow> 'a set" where
    F: "range F \<subseteq> sets M" "(\<Union>i. F i) = space M" "\<And>i. emeasure M (F i) \<noteq> \<infinity>"
    using sigma_finite by auto
  then show ?case
  proof (intro exI[of _ "\<lambda>n. \<Union>i\<le>n. F i"] conjI allI)
    from F have "\<And>x. x \<in> space M \<Longrightarrow> \<exists>i. x \<in> F i" by auto
    then show "(\<Union>n. \<Union> i\<le>n. F i) = space M"
      using F by fastforce
  next
    fix n
    have "emeasure M (\<Union> i\<le>n. F i) \<le> (\<Sum>i\<le>n. emeasure M (F i))" using F
      by (auto intro!: emeasure_subadditive_finite)
    also have "\<dots> < \<infinity>"
      using F by (auto simp: setsum_Pinfty)
    finally show "emeasure M (\<Union> i\<le>n. F i) \<noteq> \<infinity>" by simp
  qed (force simp: incseq_def)+
qed

section {* Measure space induced by distribution of @{const measurable}-functions *}

definition distr :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b measure" where
  "distr M N f = measure_of (space N) (sets N) (\<lambda>A. emeasure M (f -` A \<inter> space M))"

lemma
  shows sets_distr[simp]: "sets (distr M N f) = sets N"
    and space_distr[simp]: "space (distr M N f) = space N"
  by (auto simp: distr_def)

lemma
  shows measurable_distr_eq1[simp]: "measurable (distr Mf Nf f) Mf' = measurable Nf Mf'"
    and measurable_distr_eq2[simp]: "measurable Mg' (distr Mg Ng g) = measurable Mg' Ng"
  by (auto simp: measurable_def)

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
      using `disjoint_family A` by (auto simp: disjoint_family_on_def)
    ultimately show "(\<Sum>i. ?\<mu> (A i)) = ?\<mu> (\<Union>i. A i)"
      using suminf_emeasure[OF _ **] A f
      by (auto simp: comp_def vimage_UN)
  qed
  show "sigma_algebra (space N) (sets N)" ..
qed fact

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

lemma null_sets_distr_iff:
  "f \<in> measurable M N \<Longrightarrow> A \<in> null_sets (distr M N f) \<longleftrightarrow> f -` A \<inter> space M \<in> null_sets M \<and> A \<in> sets N"
  by (auto simp add: null_sets_def emeasure_distr measurable_sets)

lemma distr_distr:
  assumes f: "g \<in> measurable N L" and g: "f \<in> measurable M N"
  shows "distr (distr M N f) L g = distr M L (g \<circ> f)" (is "?L = ?R")
  using measurable_comp[OF g f] f g
  by (auto simp add: emeasure_distr measurable_sets measurable_space
           intro!: arg_cong[where f="emeasure M"] measure_eqI)

section {* Real measure values *}

lemma measure_nonneg: "0 \<le> measure M A"
  using emeasure_nonneg[of M A] unfolding measure_def by (auto intro: real_of_ereal_pos)

lemma measure_empty[simp]: "measure M {} = 0"
  unfolding measure_def by simp

lemma emeasure_eq_ereal_measure:
  "emeasure M A \<noteq> \<infinity> \<Longrightarrow> emeasure M A = ereal (measure M A)"
  using emeasure_nonneg[of M A]
  by (cases "emeasure M A") (auto simp: measure_def)

lemma measure_Union:
  assumes finite: "emeasure M A \<noteq> \<infinity>" "emeasure M B \<noteq> \<infinity>"
  and measurable: "A \<in> sets M" "B \<in> sets M" "A \<inter> B = {}"
  shows "measure M (A \<union> B) = measure M A + measure M B"
  unfolding measure_def
  using plus_emeasure[OF measurable, symmetric] finite
  by (simp add: emeasure_eq_ereal_measure)

lemma measure_finite_Union:
  assumes measurable: "A`S \<subseteq> sets M" "disjoint_family_on A S" "finite S"
  assumes finite: "\<And>i. i \<in> S \<Longrightarrow> emeasure M (A i) \<noteq> \<infinity>"
  shows "measure M (\<Union>i\<in>S. A i) = (\<Sum>i\<in>S. measure M (A i))"
  unfolding measure_def
  using setsum_emeasure[OF measurable, symmetric] finite
  by (simp add: emeasure_eq_ereal_measure)

lemma measure_Diff:
  assumes finite: "emeasure M A \<noteq> \<infinity>"
  and measurable: "A \<in> sets M" "B \<in> sets M" "B \<subseteq> A"
  shows "measure M (A - B) = measure M A - measure M B"
proof -
  have "emeasure M (A - B) \<le> emeasure M A" "emeasure M B \<le> emeasure M A"
    using measurable by (auto intro!: emeasure_mono)
  hence "measure M ((A - B) \<union> B) = measure M (A - B) + measure M B"
    using measurable finite by (rule_tac measure_Union) auto
  thus ?thesis using `B \<subseteq> A` by (auto simp: Un_absorb2)
qed

lemma measure_UNION:
  assumes measurable: "range A \<subseteq> sets M" "disjoint_family A"
  assumes finite: "emeasure M (\<Union>i. A i) \<noteq> \<infinity>"
  shows "(\<lambda>i. measure M (A i)) sums (measure M (\<Union>i. A i))"
proof -
  from summable_sums[OF summable_ereal_pos, of "\<lambda>i. emeasure M (A i)"]
       suminf_emeasure[OF measurable] emeasure_nonneg[of M]
  have "(\<lambda>i. emeasure M (A i)) sums (emeasure M (\<Union>i. A i))" by simp
  moreover
  { fix i
    have "emeasure M (A i) \<le> emeasure M (\<Union>i. A i)"
      using measurable by (auto intro!: emeasure_mono)
    then have "emeasure M (A i) = ereal ((measure M (A i)))"
      using finite by (intro emeasure_eq_ereal_measure) auto }
  ultimately show ?thesis using finite
    unfolding sums_ereal[symmetric] by (simp add: emeasure_eq_ereal_measure)
qed

lemma measure_subadditive:
  assumes measurable: "A \<in> sets M" "B \<in> sets M"
  and fin: "emeasure M A \<noteq> \<infinity>" "emeasure M B \<noteq> \<infinity>"
  shows "(measure M (A \<union> B)) \<le> (measure M A) + (measure M B)"
proof -
  have "emeasure M (A \<union> B) \<noteq> \<infinity>"
    using emeasure_subadditive[OF measurable] fin by auto
  then show "(measure M (A \<union> B)) \<le> (measure M A) + (measure M B)"
    using emeasure_subadditive[OF measurable] fin
    by (auto simp: emeasure_eq_ereal_measure)
qed

lemma measure_subadditive_finite:
  assumes A: "finite I" "A`I \<subseteq> sets M" and fin: "\<And>i. i \<in> I \<Longrightarrow> emeasure M (A i) \<noteq> \<infinity>"
  shows "measure M (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. measure M (A i))"
proof -
  { have "emeasure M (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. emeasure M (A i))"
      using emeasure_subadditive_finite[OF A] .
    also have "\<dots> < \<infinity>"
      using fin by (simp add: setsum_Pinfty)
    finally have "emeasure M (\<Union>i\<in>I. A i) \<noteq> \<infinity>" by simp }
  then show ?thesis
    using emeasure_subadditive_finite[OF A] fin
    unfolding measure_def by (simp add: emeasure_eq_ereal_measure suminf_ereal measure_nonneg)
qed

lemma measure_subadditive_countably:
  assumes A: "range A \<subseteq> sets M" and fin: "(\<Sum>i. emeasure M (A i)) \<noteq> \<infinity>"
  shows "measure M (\<Union>i. A i) \<le> (\<Sum>i. measure M (A i))"
proof -
  from emeasure_nonneg fin have "\<And>i. emeasure M (A i) \<noteq> \<infinity>" by (rule suminf_PInfty)
  moreover
  { have "emeasure M (\<Union>i. A i) \<le> (\<Sum>i. emeasure M (A i))"
      using emeasure_subadditive_countably[OF A] .
    also have "\<dots> < \<infinity>"
      using fin by simp
    finally have "emeasure M (\<Union>i. A i) \<noteq> \<infinity>" by simp }
  ultimately  show ?thesis
    using emeasure_subadditive_countably[OF A] fin
    unfolding measure_def by (simp add: emeasure_eq_ereal_measure suminf_ereal measure_nonneg)
qed

lemma measure_eq_setsum_singleton:
  assumes S: "finite S" "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  and fin: "\<And>x. x \<in> S \<Longrightarrow> emeasure M {x} \<noteq> \<infinity>"
  shows "(measure M S) = (\<Sum>x\<in>S. (measure M {x}))"
  unfolding measure_def
  using emeasure_eq_setsum_singleton[OF S] fin
  by simp (simp add: emeasure_eq_ereal_measure)

lemma Lim_measure_incseq:
  assumes A: "range A \<subseteq> sets M" "incseq A" and fin: "emeasure M (\<Union>i. A i) \<noteq> \<infinity>"
  shows "(\<lambda>i. (measure M (A i))) ----> (measure M (\<Union>i. A i))"
proof -
  have "ereal ((measure M (\<Union>i. A i))) = emeasure M (\<Union>i. A i)"
    using fin by (auto simp: emeasure_eq_ereal_measure)
  then show ?thesis
    using Lim_emeasure_incseq[OF A]
    unfolding measure_def
    by (intro lim_real_of_ereal) simp
qed

lemma Lim_measure_decseq:
  assumes A: "range A \<subseteq> sets M" "decseq A" and fin: "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
  shows "(\<lambda>n. measure M (A n)) ----> measure M (\<Inter>i. A i)"
proof -
  have "emeasure M (\<Inter>i. A i) \<le> emeasure M (A 0)"
    using A by (auto intro!: emeasure_mono)
  also have "\<dots> < \<infinity>"
    using fin[of 0] by auto
  finally have "ereal ((measure M (\<Inter>i. A i))) = emeasure M (\<Inter>i. A i)"
    by (auto simp: emeasure_eq_ereal_measure)
  then show ?thesis
    unfolding measure_def
    using Lim_emeasure_decseq[OF A fin]
    by (intro lim_real_of_ereal) simp
qed

section {* Measure spaces with @{term "emeasure M (space M) < \<infinity>"} *}

locale finite_measure = sigma_finite_measure M for M +
  assumes finite_emeasure_space: "emeasure M (space M) \<noteq> \<infinity>"

lemma finite_measureI[Pure.intro!]:
  assumes *: "emeasure M (space M) \<noteq> \<infinity>"
  shows "finite_measure M"
proof
  show "\<exists>A. range A \<subseteq> sets M \<and> (\<Union>i. A i) = space M \<and> (\<forall>i. emeasure M (A i) \<noteq> \<infinity>)"
    using * by (auto intro!: exI[of _ "\<lambda>_. space M"])
qed fact

lemma (in finite_measure) emeasure_finite[simp, intro]: "emeasure M A \<noteq> \<infinity>"
  using finite_emeasure_space emeasure_space[of M A] by auto

lemma (in finite_measure) emeasure_eq_measure: "emeasure M A = ereal (measure M A)"
  unfolding measure_def by (simp add: emeasure_eq_ereal_measure)

lemma (in finite_measure) emeasure_real: "\<exists>r. 0 \<le> r \<and> emeasure M A = ereal r"
  using emeasure_finite[of A] emeasure_nonneg[of M A] by (cases "emeasure M A") auto

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
  assumes measurable: "A`S \<subseteq> sets M" "disjoint_family_on A S" "finite S"
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
  assumes A: "range A \<subseteq> sets M" and sum: "summable (\<lambda>i. measure M (A i))"
  shows "measure M (\<Union>i. A i) \<le> (\<Sum>i. measure M (A i))"
proof -
  from `summable (\<lambda>i. measure M (A i))`
  have "(\<lambda>i. ereal (measure M (A i))) sums ereal (\<Sum>i. measure M (A i))"
    by (simp add: sums_ereal) (rule summable_sums)
  from sums_unique[OF this, symmetric]
       measure_subadditive_countably[OF A]
  show ?thesis by (simp add: emeasure_eq_measure)
qed

lemma (in finite_measure) finite_measure_eq_setsum_singleton:
  assumes "finite S" and *: "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  shows "measure M S = (\<Sum>x\<in>S. measure M {x})"
  using measure_eq_setsum_singleton[OF assms] by simp

lemma (in finite_measure) finite_Lim_measure_incseq:
  assumes A: "range A \<subseteq> sets M" "incseq A"
  shows "(\<lambda>i. measure M (A i)) ----> measure M (\<Union>i. A i)"
  using Lim_measure_incseq[OF A] by simp

lemma (in finite_measure) finite_Lim_measure_decseq:
  assumes A: "range A \<subseteq> sets M" "decseq A"
  shows "(\<lambda>n. measure M (A n)) ----> measure M (\<Inter>i. A i)"
  using Lim_measure_decseq[OF A] by simp

lemma (in finite_measure) finite_measure_compl:
  assumes S: "S \<in> sets M"
  shows "measure M (space M - S) = measure M (space M) - measure M S"
  using measure_Diff[OF _ top S sets_into_space] S by simp

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

section {* Counting space *}

definition count_space :: "'a set \<Rightarrow> 'a measure" where
  "count_space \<Omega> = measure_of \<Omega> (Pow \<Omega>) (\<lambda>A. if finite A then ereal (card A) else \<infinity>)"

lemma 
  shows space_count_space[simp]: "space (count_space \<Omega>) = \<Omega>"
    and sets_count_space[simp]: "sets (count_space \<Omega>) = Pow \<Omega>"
  using sigma_sets_into_sp[of "Pow \<Omega>" \<Omega>]
  by (auto simp: count_space_def)

lemma measurable_count_space_eq1[simp]:
  "f \<in> measurable (count_space A) M \<longleftrightarrow> f \<in> A \<rightarrow> space M"
 unfolding measurable_def by simp

lemma measurable_count_space_eq2[simp]:
  assumes "finite A"
  shows "f \<in> measurable M (count_space A) \<longleftrightarrow> (f \<in> space M \<rightarrow> A \<and> (\<forall>a\<in>A. f -` {a} \<inter> space M \<in> sets M))"
proof -
  { fix X assume "X \<subseteq> A" "f \<in> space M \<rightarrow> A"
    with `finite A` have "f -` X \<inter> space M = (\<Union>a\<in>X. f -` {a} \<inter> space M)" "finite X"
      by (auto dest: finite_subset)
    moreover assume "\<forall>a\<in>A. f -` {a} \<inter> space M \<in> sets M"
    ultimately have "f -` X \<inter> space M \<in> sets M"
      using `X \<subseteq> A` by (auto intro!: finite_UN simp del: UN_simps) }
  then show ?thesis
    unfolding measurable_def by auto
qed

lemma emeasure_count_space:
  assumes "X \<subseteq> A" shows "emeasure (count_space A) X = (if finite X then ereal (card X) else \<infinity>)"
    (is "_ = ?M X")
  unfolding count_space_def
proof (rule emeasure_measure_of_sigma)
  show "sigma_algebra A (Pow A)" by (rule sigma_algebra_Pow)

  show "positive (Pow A) ?M"
    by (auto simp: positive_def)

  show "countably_additive (Pow A) ?M"
  proof (unfold countably_additive_def, safe)
      fix F :: "nat \<Rightarrow> 'a set" assume disj: "disjoint_family F"
      show "(\<Sum>i. ?M (F i)) = ?M (\<Union>i. F i)"
      proof cases
        assume "\<forall>i. finite (F i)"
        then have finite_F: "\<And>i. finite (F i)" by auto
        have "\<forall>i\<in>{i. F i \<noteq> {}}. \<exists>x. x \<in> F i" by auto
        from bchoice[OF this] obtain f where f: "\<And>i. F i \<noteq> {} \<Longrightarrow> f i \<in> F i" by auto

        have inj_f: "inj_on f {i. F i \<noteq> {}}"
        proof (rule inj_onI, simp)
          fix i j a b assume *: "f i = f j" "F i \<noteq> {}" "F j \<noteq> {}"
          then have "f i \<in> F i" "f j \<in> F j" using f by force+
          with disj * show "i = j" by (auto simp: disjoint_family_on_def)
        qed
        have fin_eq: "finite (\<Union>i. F i) \<longleftrightarrow> finite {i. F i \<noteq> {}}"
        proof
          assume "finite (\<Union>i. F i)"
          show "finite {i. F i \<noteq> {}}"
          proof (rule finite_imageD)
            from f have "f`{i. F i \<noteq> {}} \<subseteq> (\<Union>i. F i)" by auto
            then show "finite (f`{i. F i \<noteq> {}})"
              by (rule finite_subset) fact
          qed fact
        next
          assume "finite {i. F i \<noteq> {}}"
          with finite_F have "finite (\<Union>i\<in>{i. F i \<noteq> {}}. F i)"
            by auto
          also have "(\<Union>i\<in>{i. F i \<noteq> {}}. F i) = (\<Union>i. F i)"
            by auto
          finally show "finite (\<Union>i. F i)" .
        qed
        
        show ?thesis
        proof cases
          assume *: "finite (\<Union>i. F i)"
          with finite_F have "finite {i. ?M (F i) \<noteq> 0} "
            by (simp add: fin_eq)
          then have "(\<Sum>i. ?M (F i)) = (\<Sum>i | ?M (F i) \<noteq> 0. ?M (F i))"
            by (rule suminf_eq_setsum)
          also have "\<dots> = ereal (\<Sum>i | F i \<noteq> {}. card (F i))"
            using finite_F by simp
          also have "\<dots> = ereal (card (\<Union>i \<in> {i. F i \<noteq> {}}. F i))"
            using * finite_F disj
            by (subst card_UN_disjoint) (auto simp: disjoint_family_on_def fin_eq)
          also have "\<dots> = ?M (\<Union>i. F i)"
            using * by (auto intro!: arg_cong[where f=card])
          finally show ?thesis .
        next
          assume inf: "infinite (\<Union>i. F i)"
          { fix i
            have "\<exists>N. i \<le> (\<Sum>i<N. card (F i))"
            proof (induct i)
              case (Suc j)
              from Suc obtain N where N: "j \<le> (\<Sum>i<N. card (F i))" by auto
              have "infinite ({i. F i \<noteq> {}} - {..< N})"
                using inf by (auto simp: fin_eq)
              then have "{i. F i \<noteq> {}} - {..< N} \<noteq> {}"
                by (metis finite.emptyI)
              then obtain i where i: "F i \<noteq> {}" "N \<le> i"
                by (auto simp: not_less[symmetric])

              note N
              also have "(\<Sum>i<N. card (F i)) \<le> (\<Sum>i<i. card (F i))"
                by (rule setsum_mono2) (auto simp: i)
              also have "\<dots> < (\<Sum>i<i. card (F i)) + card (F i)"
                using finite_F `F i \<noteq> {}` by (simp add: card_gt_0_iff)
              finally have "j < (\<Sum>i<Suc i. card (F i))"
                by simp
              then show ?case unfolding Suc_le_eq by blast
            qed simp }
          with finite_F inf show ?thesis
            by (auto simp del: real_of_nat_setsum intro!: SUP_PInfty
                     simp add: suminf_ereal_eq_SUPR real_of_nat_setsum[symmetric])
        qed
      next
        assume "\<not> (\<forall>i. finite (F i))"
        then obtain j where j: "infinite (F j)" by auto
        then have "infinite (\<Union>i. F i)"
          using finite_subset[of "F j" "\<Union>i. F i"] by auto
        moreover have "\<And>i. 0 \<le> ?M (F i)" by auto
        ultimately show ?thesis
          using suminf_PInfty[of "\<lambda>i. ?M (F i)" j] j by auto
      qed
  qed
  show "X \<in> Pow A" using `X \<subseteq> A` by simp
qed

lemma emeasure_count_space_finite[simp]:
  "X \<subseteq> A \<Longrightarrow> finite X \<Longrightarrow> emeasure (count_space A) X = ereal (card X)"
  using emeasure_count_space[of X A] by simp

lemma emeasure_count_space_infinite[simp]:
  "X \<subseteq> A \<Longrightarrow> infinite X \<Longrightarrow> emeasure (count_space A) X = \<infinity>"
  using emeasure_count_space[of X A] by simp

lemma emeasure_count_space_eq_0:
  "emeasure (count_space A) X = 0 \<longleftrightarrow> (X \<subseteq> A \<longrightarrow> X = {})"
proof cases
  assume X: "X \<subseteq> A"
  then show ?thesis
  proof (intro iffI impI)
    assume "emeasure (count_space A) X = 0"
    with X show "X = {}"
      by (subst (asm) emeasure_count_space) (auto split: split_if_asm)
  qed simp
qed (simp add: emeasure_notin_sets)

lemma null_sets_count_space: "null_sets (count_space A) = { {} }"
  unfolding null_sets_def by (auto simp add: emeasure_count_space_eq_0)

lemma AE_count_space: "(AE x in count_space A. P x) \<longleftrightarrow> (\<forall>x\<in>A. P x)"
  unfolding eventually_ae_filter by (auto simp add: null_sets_count_space)

lemma sigma_finite_measure_count_space:
  fixes A :: "'a::countable set"
  shows "sigma_finite_measure (count_space A)"
proof
  show "\<exists>F::nat \<Rightarrow> 'a set. range F \<subseteq> sets (count_space A) \<and> (\<Union>i. F i) = space (count_space A) \<and>
     (\<forall>i. emeasure (count_space A) (F i) \<noteq> \<infinity>)"
     using surj_from_nat by (intro exI[of _ "\<lambda>i. {from_nat i} \<inter> A"]) (auto simp del: surj_from_nat)
qed

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

end

