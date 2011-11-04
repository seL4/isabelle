(*  Title:      HOL/Probability/Measure.thy
    Author:     Lawrence C Paulson
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

header {* Properties about measure spaces *}

theory Measure
  imports Caratheodory
begin

lemma measure_algebra_more[simp]:
  "\<lparr> space = A, sets = B, \<dots> = algebra.more M \<rparr> \<lparr> measure := m \<rparr> =
   \<lparr> space = A, sets = B, \<dots> = algebra.more (M \<lparr> measure := m \<rparr>) \<rparr>"
  by (cases M) simp

lemma measure_algebra_more_eq[simp]:
  "\<And>X. measure \<lparr> space = T, sets = A, \<dots> = algebra.more X \<rparr> = measure X"
  unfolding measure_space.splits by simp

lemma measure_sigma[simp]: "measure (sigma A) = measure A"
  unfolding sigma_def by simp

lemma algebra_measure_update[simp]:
  "algebra (M'\<lparr>measure := m\<rparr>) \<longleftrightarrow> algebra M'"
  unfolding algebra_iff_Un by simp

lemma sigma_algebra_measure_update[simp]:
  "sigma_algebra (M'\<lparr>measure := m\<rparr>) \<longleftrightarrow> sigma_algebra M'"
  unfolding sigma_algebra_def sigma_algebra_axioms_def by simp

lemma finite_sigma_algebra_measure_update[simp]:
  "finite_sigma_algebra (M'\<lparr>measure := m\<rparr>) \<longleftrightarrow> finite_sigma_algebra M'"
  unfolding finite_sigma_algebra_def finite_sigma_algebra_axioms_def by simp

lemma measurable_cancel_measure[simp]:
  "measurable M1 (M2\<lparr>measure := m2\<rparr>) = measurable M1 M2"
  "measurable (M2\<lparr>measure := m1\<rparr>) M1 = measurable M2 M1"
  unfolding measurable_def by auto

lemma inj_on_image_eq_iff:
  assumes "inj_on f S"
  assumes "A \<subseteq> S" "B \<subseteq> S"
  shows "(f ` A = f ` B) \<longleftrightarrow> (A = B)"
proof -
  have "inj_on f (A \<union> B)"
    using assms by (auto intro: subset_inj_on)
  from inj_on_Un_image_eq_iff[OF this]
  show ?thesis .
qed

lemma image_vimage_inter_eq:
  assumes "f ` S = T" "X \<subseteq> T"
  shows "f ` (f -` X \<inter> S) = X"
proof (intro antisym)
  have "f ` (f -` X \<inter> S) \<subseteq> f ` (f -` X)" by auto
  also have "\<dots> = X \<inter> range f" by simp
  also have "\<dots> = X" using assms by auto
  finally show "f ` (f -` X \<inter> S) \<subseteq> X" by auto
next
  show "X \<subseteq> f ` (f -` X \<inter> S)"
  proof
    fix x assume "x \<in> X"
    then have "x \<in> T" using `X \<subseteq> T` by auto
    then obtain y where "x = f y" "y \<in> S"
      using assms by auto
    then have "{y} \<subseteq> f -` X \<inter> S" using `x \<in> X` by auto
    moreover have "x \<in> f ` {y}" using `x = f y` by auto
    ultimately show "x \<in> f ` (f -` X \<inter> S)" by auto
  qed
qed

text {*
  This formalisation of measure theory is based on the work of Hurd/Coble wand
  was later translated by Lawrence Paulson to Isabelle/HOL. Later it was
  modified to use the positive infinite reals and to prove the uniqueness of
  cut stable measures.
*}

section {* Equations for the measure function @{text \<mu>} *}

lemma (in measure_space) measure_countably_additive:
  assumes "range A \<subseteq> sets M" "disjoint_family A"
  shows "(\<Sum>i. \<mu> (A i)) = \<mu> (\<Union>i. A i)"
proof -
  have "(\<Union> i. A i) \<in> sets M" using assms(1) by (rule countable_UN)
  with ca assms show ?thesis by (simp add: countably_additive_def)
qed

lemma (in sigma_algebra) sigma_algebra_cong:
  assumes "space N = space M" "sets N = sets M"
  shows "sigma_algebra N"
  by default (insert sets_into_space, auto simp: assms)

lemma (in measure_space) measure_space_cong:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> measure N A = \<mu> A" "space N = space M" "sets N = sets M"
  shows "measure_space N"
proof -
  interpret N: sigma_algebra N by (intro sigma_algebra_cong assms)
  show ?thesis
  proof
    show "positive N (measure N)" using assms by (auto simp: positive_def)
    show "countably_additive N (measure N)" unfolding countably_additive_def
    proof safe
      fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> sets N" "disjoint_family A"
      then have "\<And>i. A i \<in> sets M" "(UNION UNIV A) \<in> sets M" unfolding assms by auto
      from measure_countably_additive[of A] A this[THEN assms(1)]
      show "(\<Sum>n. measure N (A n)) = measure N (UNION UNIV A)"
        unfolding assms by simp
    qed
  qed
qed

lemma (in measure_space) additive: "additive M \<mu>"
  using ca by (auto intro!: countably_additive_additive simp: positive_def)

lemma (in measure_space) measure_additive:
     "a \<in> sets M \<Longrightarrow> b \<in> sets M \<Longrightarrow> a \<inter> b = {}
      \<Longrightarrow> \<mu> a + \<mu> b = \<mu> (a \<union> b)"
  by (metis additiveD additive)

lemma (in measure_space) measure_mono:
  assumes "a \<subseteq> b" "a \<in> sets M" "b \<in> sets M"
  shows "\<mu> a \<le> \<mu> b"
proof -
  have "b = a \<union> (b - a)" using assms by auto
  moreover have "{} = a \<inter> (b - a)" by auto
  ultimately have "\<mu> b = \<mu> a + \<mu> (b - a)"
    using measure_additive[of a "b - a"] Diff[of b a] assms by auto
  moreover have "\<mu> a + 0 \<le> \<mu> a + \<mu> (b - a)" using assms by (intro add_mono) auto
  ultimately show "\<mu> a \<le> \<mu> b" by auto
qed

lemma (in measure_space) measure_top:
  "A \<in> sets M \<Longrightarrow> \<mu> A \<le> \<mu> (space M)"
  using sets_into_space[of A] by (auto intro!: measure_mono)

lemma (in measure_space) measure_compl:
  assumes s: "s \<in> sets M" and fin: "\<mu> s \<noteq> \<infinity>"
  shows "\<mu> (space M - s) = \<mu> (space M) - \<mu> s"
proof -
  have s_less_space: "\<mu> s \<le> \<mu> (space M)"
    using s by (auto intro!: measure_mono sets_into_space)
  from s have "0 \<le> \<mu> s" by auto
  have "\<mu> (space M) = \<mu> (s \<union> (space M - s))" using s
    by (metis Un_Diff_cancel Un_absorb1 s sets_into_space)
  also have "... = \<mu> s + \<mu> (space M - s)"
    by (rule additiveD [OF additive]) (auto simp add: s)
  finally have "\<mu> (space M) = \<mu> s + \<mu> (space M - s)" .
  then show ?thesis
    using fin `0 \<le> \<mu> s`
    unfolding ereal_eq_minus_iff by (auto simp: ac_simps)
qed

lemma (in measure_space) measure_Diff:
  assumes finite: "\<mu> B \<noteq> \<infinity>"
  and measurable: "A \<in> sets M" "B \<in> sets M" "B \<subseteq> A"
  shows "\<mu> (A - B) = \<mu> A - \<mu> B"
proof -
  have "0 \<le> \<mu> B" using assms by auto
  have "(A - B) \<union> B = A" using `B \<subseteq> A` by auto
  then have "\<mu> A = \<mu> ((A - B) \<union> B)" by simp
  also have "\<dots> = \<mu> (A - B) + \<mu> B"
    using measurable by (subst measure_additive[symmetric]) auto
  finally show "\<mu> (A - B) = \<mu> A - \<mu> B"
    unfolding ereal_eq_minus_iff
    using finite `0 \<le> \<mu> B` by auto
qed

lemma (in measure_space) measure_countable_increasing:
  assumes A: "range A \<subseteq> sets M"
      and A0: "A 0 = {}"
      and ASuc: "\<And>n. A n \<subseteq> A (Suc n)"
  shows "(SUP n. \<mu> (A n)) = \<mu> (\<Union>i. A i)"
proof -
  { fix n
    have "\<mu> (A n) = (\<Sum>i<n. \<mu> (A (Suc i) - A i))"
      proof (induct n)
        case 0 thus ?case by (auto simp add: A0)
      next
        case (Suc m)
        have "A (Suc m) = A m \<union> (A (Suc m) - A m)"
          by (metis ASuc Un_Diff_cancel Un_absorb1)
        hence "\<mu> (A (Suc m)) =
               \<mu> (A m) + \<mu> (A (Suc m) - A m)"
          by (subst measure_additive)
             (auto simp add: measure_additive range_subsetD [OF A])
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
  have "(SUP n. \<Sum>i<n. \<mu> (A (Suc i) - A i)) = (\<Sum>i. \<mu> (A (Suc i) - A i))"
    using A by (auto intro!: suminf_ereal_eq_SUPR[symmetric])
  also have "\<dots> = \<mu> (\<Union>i. A (Suc i) - A i)"
    by (rule measure_countably_additive)
       (auto simp add: disjoint_family_Suc ASuc A1 A2)
  also have "... =  \<mu> (\<Union>i. A i)"
    by (simp add: Aeq)
  finally have "(SUP n. \<Sum>i<n. \<mu> (A (Suc i) - A i)) = \<mu> (\<Union>i. A i)" .
  then show ?thesis by (auto simp add: Meq)
qed

lemma (in measure_space) continuity_from_below:
  assumes A: "range A \<subseteq> sets M" and "incseq A"
  shows "(SUP n. \<mu> (A n)) = \<mu> (\<Union>i. A i)"
proof -
  have *: "(SUP n. \<mu> (nat_case {} A (Suc n))) = (SUP n. \<mu> (nat_case {} A n))"
    using A by (auto intro!: SUPR_eq exI split: nat.split)
  have ueq: "(\<Union>i. nat_case {} A i) = (\<Union>i. A i)"
    by (auto simp add: split: nat.splits)
  have meq: "\<And>n. \<mu> (A n) = (\<mu> \<circ> nat_case {} A) (Suc n)"
    by simp
  have "(SUP n. \<mu> (nat_case {} A n)) = \<mu> (\<Union>i. nat_case {} A i)"
    using range_subsetD[OF A] incseq_SucD[OF `incseq A`]
    by (force split: nat.splits intro!: measure_countable_increasing)
  also have "\<mu> (\<Union>i. nat_case {} A i) = \<mu> (\<Union>i. A i)"
    by (simp add: ueq)
  finally have "(SUP n. \<mu> (nat_case {} A n)) = \<mu> (\<Union>i. A i)" .
  thus ?thesis unfolding meq * comp_def .
qed

lemma (in measure_space) measure_incseq:
  assumes "range B \<subseteq> sets M" "incseq B"
  shows "incseq (\<lambda>i. \<mu> (B i))"
  using assms by (auto simp: incseq_def intro!: measure_mono)

lemma (in measure_space) continuity_from_below_Lim:
  assumes A: "range A \<subseteq> sets M" "incseq A"
  shows "(\<lambda>i. (\<mu> (A i))) ----> \<mu> (\<Union>i. A i)"
  using LIMSEQ_ereal_SUPR[OF measure_incseq, OF A]
    continuity_from_below[OF A] by simp

lemma (in measure_space) measure_decseq:
  assumes "range B \<subseteq> sets M" "decseq B"
  shows "decseq (\<lambda>i. \<mu> (B i))"
  using assms by (auto simp: decseq_def intro!: measure_mono)

lemma (in measure_space) continuity_from_above:
  assumes A: "range A \<subseteq> sets M" and "decseq A"
  and finite: "\<And>i. \<mu> (A i) \<noteq> \<infinity>"
  shows "(INF n. \<mu> (A n)) = \<mu> (\<Inter>i. A i)"
proof -
  have le_MI: "\<mu> (\<Inter>i. A i) \<le> \<mu> (A 0)"
    using A by (auto intro!: measure_mono)
  hence *: "\<mu> (\<Inter>i. A i) \<noteq> \<infinity>" using finite[of 0] by auto

  have A0: "0 \<le> \<mu> (A 0)" using A by auto

  have "\<mu> (A 0) - (INF n. \<mu> (A n)) = \<mu> (A 0) + (SUP n. - \<mu> (A n))"
    by (simp add: ereal_SUPR_uminus minus_ereal_def)
  also have "\<dots> = (SUP n. \<mu> (A 0) - \<mu> (A n))"
    unfolding minus_ereal_def using A0 assms
    by (subst SUPR_ereal_add) (auto simp add: measure_decseq)
  also have "\<dots> = (SUP n. \<mu> (A 0 - A n))"
    using A finite `decseq A`[unfolded decseq_def] by (subst measure_Diff) auto
  also have "\<dots> = \<mu> (\<Union>i. A 0 - A i)"
  proof (rule continuity_from_below)
    show "range (\<lambda>n. A 0 - A n) \<subseteq> sets M"
      using A by auto
    show "incseq (\<lambda>n. A 0 - A n)"
      using `decseq A` by (auto simp add: incseq_def decseq_def)
  qed
  also have "\<dots> = \<mu> (A 0) - \<mu> (\<Inter>i. A i)"
    using A finite * by (simp, subst measure_Diff) auto
  finally show ?thesis
    unfolding ereal_minus_eq_minus_iff using finite A0 by auto
qed

lemma (in measure_space) measure_insert:
  assumes sets: "{x} \<in> sets M" "A \<in> sets M" and "x \<notin> A"
  shows "\<mu> (insert x A) = \<mu> {x} + \<mu> A"
proof -
  have "{x} \<inter> A = {}" using `x \<notin> A` by auto
  from measure_additive[OF sets this] show ?thesis by simp
qed

lemma (in measure_space) measure_setsum:
  assumes "finite S" and "\<And>i. i \<in> S \<Longrightarrow> A i \<in> sets M"
  assumes disj: "disjoint_family_on A S"
  shows "(\<Sum>i\<in>S. \<mu> (A i)) = \<mu> (\<Union>i\<in>S. A i)"
using assms proof induct
  case (insert i S)
  then have "(\<Sum>i\<in>S. \<mu> (A i)) = \<mu> (\<Union>a\<in>S. A a)"
    by (auto intro: disjoint_family_on_mono)
  moreover have "A i \<inter> (\<Union>a\<in>S. A a) = {}"
    using `disjoint_family_on A (insert i S)` `i \<notin> S`
    by (auto simp: disjoint_family_on_def)
  ultimately show ?case using insert
    by (auto simp: measure_additive finite_UN)
qed simp

lemma (in measure_space) measure_finite_singleton:
  assumes "finite S" "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  shows "\<mu> S = (\<Sum>x\<in>S. \<mu> {x})"
  using measure_setsum[of S "\<lambda>x. {x}", OF assms]
  by (auto simp: disjoint_family_on_def)

lemma finite_additivity_sufficient:
  assumes "sigma_algebra M"
  assumes fin: "finite (space M)" and pos: "positive M (measure M)" and add: "additive M (measure M)"
  shows "measure_space M"
proof -
  interpret sigma_algebra M by fact
  show ?thesis
  proof
    show [simp]: "positive M (measure M)" using pos by (simp add: positive_def)
    show "countably_additive M (measure M)"
    proof (auto simp add: countably_additive_def)
      fix A :: "nat \<Rightarrow> 'a set"
      assume A: "range A \<subseteq> sets M"
         and disj: "disjoint_family A"
         and UnA: "(\<Union>i. A i) \<in> sets M"
      def I \<equiv> "{i. A i \<noteq> {}}"
      have "Union (A ` I) \<subseteq> space M" using A
        by auto (metis range_subsetD subsetD sets_into_space)
      hence "finite (A ` I)"
        by (metis finite_UnionD finite_subset fin)
      moreover have "inj_on A I" using disj
        by (auto simp add: I_def disjoint_family_on_def inj_on_def)
      ultimately have finI: "finite I"
        by (metis finite_imageD)
      hence "\<exists>N. \<forall>m\<ge>N. A m = {}"
        proof (cases "I = {}")
          case True thus ?thesis by (simp add: I_def)
        next
          case False
          hence "\<forall>i\<in>I. i < Suc(Max I)"
            by (simp add: Max_less_iff [symmetric] finI)
          hence "\<forall>m \<ge> Suc(Max I). A m = {}"
            by (simp add: I_def) (metis less_le_not_le)
          thus ?thesis
            by blast
        qed
      then obtain N where N: "\<forall>m\<ge>N. A m = {}" by blast
      then have "\<forall>m\<ge>N. measure M (A m) = 0" using pos[unfolded positive_def] by simp
      then have "(\<Sum>n. measure M (A n)) = (\<Sum>m<N. measure M (A m))"
        by (simp add: suminf_finite)
      also have "... = measure M (\<Union>i<N. A i)"
        proof (induct N)
          case 0 thus ?case using pos[unfolded positive_def] by simp
        next
          case (Suc n)
          have "measure M (A n \<union> (\<Union> x<n. A x)) = measure M (A n) + measure M (\<Union> i<n. A i)"
            proof (rule Caratheodory.additiveD [OF add])
              show "A n \<inter> (\<Union> x<n. A x) = {}" using disj
                by (auto simp add: disjoint_family_on_def nat_less_le) blast
              show "A n \<in> sets M" using A
                by force
              show "(\<Union>i<n. A i) \<in> sets M"
                proof (induct n)
                  case 0 thus ?case by simp
                next
                  case (Suc n) thus ?case using A
                    by (simp add: lessThan_Suc Un range_subsetD)
                qed
            qed
          thus ?case using Suc
            by (simp add: lessThan_Suc)
        qed
      also have "... = measure M (\<Union>i. A i)"
        proof -
          have "(\<Union> i<N. A i) = (\<Union>i. A i)" using N
            by auto (metis Int_absorb N disjoint_iff_not_equal lessThan_iff not_leE)
          thus ?thesis by simp
        qed
      finally show "(\<Sum>n. measure M (A n)) = measure M (\<Union>i. A i)" .
    qed
  qed
qed

lemma (in measure_space) measure_setsum_split:
  assumes "finite S" and "A \<in> sets M" and br_in_M: "B ` S \<subseteq> sets M"
  assumes "(\<Union>i\<in>S. B i) = space M"
  assumes "disjoint_family_on B S"
  shows "\<mu> A = (\<Sum>i\<in>S. \<mu> (A \<inter> (B i)))"
proof -
  have *: "\<mu> A = \<mu> (\<Union>i\<in>S. A \<inter> B i)"
    using assms by auto
  show ?thesis unfolding *
  proof (rule measure_setsum[symmetric])
    show "disjoint_family_on (\<lambda>i. A \<inter> B i) S"
      using `disjoint_family_on B S`
      unfolding disjoint_family_on_def by auto
  qed (insert assms, auto)
qed

lemma (in measure_space) measure_subadditive:
  assumes measurable: "A \<in> sets M" "B \<in> sets M"
  shows "\<mu> (A \<union> B) \<le> \<mu> A + \<mu> B"
proof -
  from measure_additive[of A "B - A"]
  have "\<mu> (A \<union> B) = \<mu> A + \<mu> (B - A)"
    using assms by (simp add: Diff)
  also have "\<dots> \<le> \<mu> A + \<mu> B"
    using assms by (auto intro!: add_left_mono measure_mono)
  finally show ?thesis .
qed

lemma (in measure_space) measure_subadditive_finite:
  assumes "finite I" "\<And>i. i\<in>I \<Longrightarrow> A i \<in> sets M"
  shows "\<mu> (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. \<mu> (A i))"
using assms proof induct
  case (insert i I)
  then have "\<mu> (\<Union>i\<in>insert i I. A i) = \<mu> (A i \<union> (\<Union>i\<in>I. A i))"
    by simp
  also have "\<dots> \<le> \<mu> (A i) + \<mu> (\<Union>i\<in>I. A i)"
    using insert by (intro measure_subadditive finite_UN) auto
  also have "\<dots> \<le> \<mu> (A i) + (\<Sum>i\<in>I. \<mu> (A i))"
    using insert by (intro add_mono) auto
  also have "\<dots> = (\<Sum>i\<in>insert i I. \<mu> (A i))"
    using insert by auto
  finally show ?case .
qed simp

lemma (in measure_space) measure_eq_0:
  assumes "N \<in> sets M" and "\<mu> N = 0" and "K \<subseteq> N" and "K \<in> sets M"
  shows "\<mu> K = 0"
  using measure_mono[OF assms(3,4,1)] assms(2) positive_measure[OF assms(4)] by auto

lemma (in measure_space) measure_finitely_subadditive:
  assumes "finite I" "A ` I \<subseteq> sets M"
  shows "\<mu> (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. \<mu> (A i))"
using assms proof induct
  case (insert i I)
  then have "(\<Union>i\<in>I. A i) \<in> sets M" by (auto intro: finite_UN)
  then have "\<mu> (\<Union>i\<in>insert i I. A i) \<le> \<mu> (A i) + \<mu> (\<Union>i\<in>I. A i)"
    using insert by (simp add: measure_subadditive)
  also have "\<dots> \<le> (\<Sum>i\<in>insert i I. \<mu> (A i))"
    using insert by (auto intro!: add_left_mono)
  finally show ?case .
qed simp

lemma (in measure_space) measure_countably_subadditive:
  assumes "range f \<subseteq> sets M"
  shows "\<mu> (\<Union>i. f i) \<le> (\<Sum>i. \<mu> (f i))"
proof -
  have "\<mu> (\<Union>i. f i) = \<mu> (\<Union>i. disjointed f i)"
    unfolding UN_disjointed_eq ..
  also have "\<dots> = (\<Sum>i. \<mu> (disjointed f i))"
    using range_disjointed_sets[OF assms] measure_countably_additive
    by (simp add:  disjoint_family_disjointed comp_def)
  also have "\<dots> \<le> (\<Sum>i. \<mu> (f i))"
    using range_disjointed_sets[OF assms] assms
    by (auto intro!: suminf_le_pos measure_mono positive_measure disjointed_subset)
  finally show ?thesis .
qed

lemma (in measure_space) measure_UN_eq_0:
  assumes "\<And>i::nat. \<mu> (N i) = 0" and "range N \<subseteq> sets M"
  shows "\<mu> (\<Union> i. N i) = 0"
proof -
  have "0 \<le> \<mu> (\<Union> i. N i)" using assms by auto
  moreover have "\<mu> (\<Union> i. N i) \<le> 0"
    using measure_countably_subadditive[OF assms(2)] assms(1) by simp
  ultimately show ?thesis by simp
qed

lemma (in measure_space) measure_inter_full_set:
  assumes "S \<in> sets M" "T \<in> sets M" and fin: "\<mu> (T - S) \<noteq> \<infinity>"
  assumes T: "\<mu> T = \<mu> (space M)"
  shows "\<mu> (S \<inter> T) = \<mu> S"
proof (rule antisym)
  show " \<mu> (S \<inter> T) \<le> \<mu> S"
    using assms by (auto intro!: measure_mono)

  have pos: "0 \<le> \<mu> (T - S)" using assms by auto
  show "\<mu> S \<le> \<mu> (S \<inter> T)"
  proof (rule ccontr)
    assume contr: "\<not> ?thesis"
    have "\<mu> (space M) = \<mu> ((T - S) \<union> (S \<inter> T))"
      unfolding T[symmetric] by (auto intro!: arg_cong[where f="\<mu>"])
    also have "\<dots> \<le> \<mu> (T - S) + \<mu> (S \<inter> T)"
      using assms by (auto intro!: measure_subadditive)
    also have "\<dots> < \<mu> (T - S) + \<mu> S"
      using fin contr pos by (intro ereal_less_add) auto
    also have "\<dots> = \<mu> (T \<union> S)"
      using assms by (subst measure_additive) auto
    also have "\<dots> \<le> \<mu> (space M)"
      using assms sets_into_space by (auto intro!: measure_mono)
    finally show False ..
  qed
qed

lemma measure_unique_Int_stable:
  fixes E :: "('a, 'b) algebra_scheme" and A :: "nat \<Rightarrow> 'a set"
  assumes "Int_stable E"
  and A: "range A \<subseteq> sets E" "incseq A" "(\<Union>i. A i) = space E"
  and M: "measure_space \<lparr>space = space E, sets = sets (sigma E), measure = \<mu>\<rparr>" (is "measure_space ?M")
  and N: "measure_space \<lparr>space = space E, sets = sets (sigma E), measure = \<nu>\<rparr>" (is "measure_space ?N")
  and eq: "\<And>X. X \<in> sets E \<Longrightarrow> \<mu> X = \<nu> X"
  and finite: "\<And>i. \<mu> (A i) \<noteq> \<infinity>"
  assumes "X \<in> sets (sigma E)"
  shows "\<mu> X = \<nu> X"
proof -
  let "?D F" = "{D. D \<in> sets (sigma E) \<and> \<mu> (F \<inter> D) = \<nu> (F \<inter> D)}"
  interpret M: measure_space ?M
    where "space ?M = space E" and "sets ?M = sets (sigma E)" and "measure ?M = \<mu>" by (simp_all add: M)
  interpret N: measure_space ?N
    where "space ?N = space E" and "sets ?N = sets (sigma E)" and "measure ?N = \<nu>" by (simp_all add: N)
  { fix F assume "F \<in> sets E" and "\<mu> F \<noteq> \<infinity>"
    then have [intro]: "F \<in> sets (sigma E)" by auto
    have "\<nu> F \<noteq> \<infinity>" using `\<mu> F \<noteq> \<infinity>` `F \<in> sets E` eq by simp
    interpret D: dynkin_system "\<lparr>space=space E, sets=?D F\<rparr>"
    proof (rule dynkin_systemI, simp_all)
      fix A assume "A \<in> sets (sigma E) \<and> \<mu> (F \<inter> A) = \<nu> (F \<inter> A)"
      then show "A \<subseteq> space E" using M.sets_into_space by auto
    next
      have "F \<inter> space E = F" using `F \<in> sets E` by auto
      then show "\<mu> (F \<inter> space E) = \<nu> (F \<inter> space E)"
        using `F \<in> sets E` eq by auto
    next
      fix A assume *: "A \<in> sets (sigma E) \<and> \<mu> (F \<inter> A) = \<nu> (F \<inter> A)"
      then have **: "F \<inter> (space (sigma E) - A) = F - (F \<inter> A)"
        and [intro]: "F \<inter> A \<in> sets (sigma E)"
        using `F \<in> sets E` M.sets_into_space by auto
      have "\<nu> (F \<inter> A) \<le> \<nu> F" by (auto intro!: N.measure_mono)
      then have "\<nu> (F \<inter> A) \<noteq> \<infinity>" using `\<nu> F \<noteq> \<infinity>` by auto
      have "\<mu> (F \<inter> A) \<le> \<mu> F" by (auto intro!: M.measure_mono)
      then have "\<mu> (F \<inter> A) \<noteq> \<infinity>" using `\<mu> F \<noteq> \<infinity>` by auto
      then have "\<mu> (F \<inter> (space (sigma E) - A)) = \<mu> F - \<mu> (F \<inter> A)" unfolding **
        using `F \<inter> A \<in> sets (sigma E)` by (auto intro!: M.measure_Diff)
      also have "\<dots> = \<nu> F - \<nu> (F \<inter> A)" using eq `F \<in> sets E` * by simp
      also have "\<dots> = \<nu> (F \<inter> (space (sigma E) - A))" unfolding **
        using `F \<inter> A \<in> sets (sigma E)` `\<nu> (F \<inter> A) \<noteq> \<infinity>` by (auto intro!: N.measure_Diff[symmetric])
      finally show "space E - A \<in> sets (sigma E) \<and> \<mu> (F \<inter> (space E - A)) = \<nu> (F \<inter> (space E - A))"
        using * by auto
    next
      fix A :: "nat \<Rightarrow> 'a set"
      assume "disjoint_family A" "range A \<subseteq> {X \<in> sets (sigma E). \<mu> (F \<inter> X) = \<nu> (F \<inter> X)}"
      then have A: "range (\<lambda>i. F \<inter> A i) \<subseteq> sets (sigma E)" "F \<inter> (\<Union>x. A x) = (\<Union>x. F \<inter> A x)"
        "disjoint_family (\<lambda>i. F \<inter> A i)" "\<And>i. \<mu> (F \<inter> A i) = \<nu> (F \<inter> A i)" "range A \<subseteq> sets (sigma E)"
        by (auto simp: disjoint_family_on_def subset_eq)
      then show "(\<Union>x. A x) \<in> sets (sigma E) \<and> \<mu> (F \<inter> (\<Union>x. A x)) = \<nu> (F \<inter> (\<Union>x. A x))"
        by (auto simp: M.measure_countably_additive[symmetric]
                       N.measure_countably_additive[symmetric]
            simp del: UN_simps)
    qed
    have *: "sets (sigma E) = sets \<lparr>space = space E, sets = ?D F\<rparr>"
      using `F \<in> sets E` `Int_stable E`
      by (intro D.dynkin_lemma)
         (auto simp add: sets_sigma Int_stable_def eq intro: sigma_sets.Basic)
    have "\<And>D. D \<in> sets (sigma E) \<Longrightarrow> \<mu> (F \<inter> D) = \<nu> (F \<inter> D)"
      by (subst (asm) *) auto }
  note * = this
  let "?A i" = "A i \<inter> X"
  have A': "range ?A \<subseteq> sets (sigma E)" "incseq ?A"
    using A(1,2) `X \<in> sets (sigma E)` by (auto simp: incseq_def)
  { fix i have "\<mu> (?A i) = \<nu> (?A i)"
      using *[of "A i" X] `X \<in> sets (sigma E)` A finite by auto }
  with M.continuity_from_below[OF A'] N.continuity_from_below[OF A']
  show ?thesis using A(3) `X \<in> sets (sigma E)` by auto
qed

section "@{text \<mu>}-null sets"

abbreviation (in measure_space) "null_sets \<equiv> {N\<in>sets M. \<mu> N = 0}"

sublocale measure_space \<subseteq> nullsets!: ring_of_sets "\<lparr> space = space M, sets = null_sets \<rparr>"
  where "space \<lparr> space = space M, sets = null_sets \<rparr> = space M"
  and "sets \<lparr> space = space M, sets = null_sets \<rparr> = null_sets"
proof -
  { fix A B assume sets: "A \<in> sets M" "B \<in> sets M"
    moreover then have "\<mu> (A \<union> B) \<le> \<mu> A + \<mu> B" "\<mu> (A - B) \<le> \<mu> A"
      by (auto intro!: measure_subadditive measure_mono)
    moreover assume "\<mu> B = 0" "\<mu> A = 0"
    ultimately have "\<mu> (A - B) = 0" "\<mu> (A \<union> B) = 0"
      by (auto intro!: antisym) }
  note null = this
  show "ring_of_sets \<lparr> space = space M, sets = null_sets \<rparr>"
    by default (insert sets_into_space null, auto)
qed simp_all

lemma UN_from_nat: "(\<Union>i. N i) = (\<Union>i. N (Countable.from_nat i))"
proof -
  have "(\<Union>i. N i) = (\<Union>i. (N \<circ> Countable.from_nat) i)"
    unfolding SUP_def image_compose
    unfolding surj_from_nat ..
  then show ?thesis by simp
qed

lemma (in measure_space) null_sets_UN[intro]:
  assumes "\<And>i::'i::countable. N i \<in> null_sets"
  shows "(\<Union>i. N i) \<in> null_sets"
proof (intro conjI CollectI)
  show "(\<Union>i. N i) \<in> sets M" using assms by auto
  then have "0 \<le> \<mu> (\<Union>i. N i)" by simp
  moreover have "\<mu> (\<Union>i. N i) \<le> (\<Sum>n. \<mu> (N (Countable.from_nat n)))"
    unfolding UN_from_nat[of N]
    using assms by (intro measure_countably_subadditive) auto
  ultimately show "\<mu> (\<Union>i. N i) = 0" using assms by auto
qed

lemma (in measure_space) null_set_Int1:
  assumes "B \<in> null_sets" "A \<in> sets M" shows "A \<inter> B \<in> null_sets"
using assms proof (intro CollectI conjI)
  show "\<mu> (A \<inter> B) = 0" using assms by (intro measure_eq_0[of B "A \<inter> B"]) auto
qed auto

lemma (in measure_space) null_set_Int2:
  assumes "B \<in> null_sets" "A \<in> sets M" shows "B \<inter> A \<in> null_sets"
  using assms by (subst Int_commute) (rule null_set_Int1)

lemma (in measure_space) measure_Diff_null_set:
  assumes "B \<in> null_sets" "A \<in> sets M"
  shows "\<mu> (A - B) = \<mu> A"
proof -
  have *: "A - B = (A - (A \<inter> B))" by auto
  have "A \<inter> B \<in> null_sets" using assms by (rule null_set_Int1)
  then show ?thesis
    unfolding * using assms
    by (subst measure_Diff) auto
qed

lemma (in measure_space) null_set_Diff:
  assumes "B \<in> null_sets" "A \<in> sets M" shows "B - A \<in> null_sets"
using assms proof (intro CollectI conjI)
  show "\<mu> (B - A) = 0" using assms by (intro measure_eq_0[of B "B - A"]) auto
qed auto

lemma (in measure_space) measure_Un_null_set:
  assumes "A \<in> sets M" "B \<in> null_sets"
  shows "\<mu> (A \<union> B) = \<mu> A"
proof -
  have *: "A \<union> B = A \<union> (B - A)" by auto
  have "B - A \<in> null_sets" using assms(2,1) by (rule null_set_Diff)
  then show ?thesis
    unfolding * using assms
    by (subst measure_additive[symmetric]) auto
qed

section "Formalise almost everywhere"

definition (in measure_space)
  almost_everywhere :: "('a \<Rightarrow> bool) \<Rightarrow> bool" (binder "AE " 10) where
  "almost_everywhere P \<longleftrightarrow> (\<exists>N\<in>null_sets. { x \<in> space M. \<not> P x } \<subseteq> N)"

syntax
  "_almost_everywhere" :: "pttrn \<Rightarrow> ('a, 'b) measure_space_scheme \<Rightarrow> bool \<Rightarrow> bool" ("AE _ in _. _" [0,0,10] 10)

translations
  "AE x in M. P" == "CONST measure_space.almost_everywhere M (%x. P)"

lemma (in measure_space) AE_cong_measure:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> measure N A = \<mu> A" "sets N = sets M" "space N = space M"
  shows "(AE x in N. P x) \<longleftrightarrow> (AE x. P x)"
proof -
  interpret N: measure_space N
    by (rule measure_space_cong) fact+
  show ?thesis
    unfolding N.almost_everywhere_def almost_everywhere_def
    by (auto simp: assms)
qed

lemma (in measure_space) AE_I':
  "N \<in> null_sets \<Longrightarrow> {x\<in>space M. \<not> P x} \<subseteq> N \<Longrightarrow> (AE x. P x)"
  unfolding almost_everywhere_def by auto

lemma (in measure_space) AE_iff_null_set:
  assumes "{x\<in>space M. \<not> P x} \<in> sets M" (is "?P \<in> sets M")
  shows "(AE x. P x) \<longleftrightarrow> {x\<in>space M. \<not> P x} \<in> null_sets"
proof
  assume "AE x. P x" then obtain N where N: "N \<in> sets M" "?P \<subseteq> N" "\<mu> N = 0"
    unfolding almost_everywhere_def by auto
  have "0 \<le> \<mu> ?P" using assms by simp
  moreover have "\<mu> ?P \<le> \<mu> N"
    using assms N(1,2) by (auto intro: measure_mono)
  ultimately have "\<mu> ?P = 0" unfolding `\<mu> N = 0` by auto
  then show "?P \<in> null_sets" using assms by simp
next
  assume "?P \<in> null_sets" with assms show "AE x. P x" by (auto intro: AE_I')
qed

lemma (in measure_space) AE_iff_measurable:
  "N \<in> sets M \<Longrightarrow> {x\<in>space M. \<not> P x} = N \<Longrightarrow> (AE x. P x) \<longleftrightarrow> \<mu> N = 0"
  using AE_iff_null_set[of P] by simp

lemma (in measure_space) AE_True[intro, simp]: "AE x. True"
  unfolding almost_everywhere_def by auto

lemma (in measure_space) AE_E[consumes 1]:
  assumes "AE x. P x"
  obtains N where "{x \<in> space M. \<not> P x} \<subseteq> N" "\<mu> N = 0" "N \<in> sets M"
  using assms unfolding almost_everywhere_def by auto

lemma (in measure_space) AE_E2:
  assumes "AE x. P x" "{x\<in>space M. P x} \<in> sets M"
  shows "\<mu> {x\<in>space M. \<not> P x} = 0" (is "\<mu> ?P = 0")
proof -
  have "{x\<in>space M. \<not> P x} = space M - {x\<in>space M. P x}"
    by auto
  with AE_iff_null_set[of P] assms show ?thesis by auto
qed

lemma (in measure_space) AE_I:
  assumes "{x \<in> space M. \<not> P x} \<subseteq> N" "\<mu> N = 0" "N \<in> sets M"
  shows "AE x. P x"
  using assms unfolding almost_everywhere_def by auto

lemma (in measure_space) AE_mp[elim!]:
  assumes AE_P: "AE x. P x" and AE_imp: "AE x. P x \<longrightarrow> Q x"
  shows "AE x. Q x"
proof -
  from AE_P obtain A where P: "{x\<in>space M. \<not> P x} \<subseteq> A"
    and A: "A \<in> sets M" "\<mu> A = 0"
    by (auto elim!: AE_E)

  from AE_imp obtain B where imp: "{x\<in>space M. P x \<and> \<not> Q x} \<subseteq> B"
    and B: "B \<in> sets M" "\<mu> B = 0"
    by (auto elim!: AE_E)

  show ?thesis
  proof (intro AE_I)
    have "0 \<le> \<mu> (A \<union> B)" using A B by auto
    moreover have "\<mu> (A \<union> B) \<le> 0"
      using measure_subadditive[of A B] A B by auto
    ultimately show "A \<union> B \<in> sets M" "\<mu> (A \<union> B) = 0" using A B by auto
    show "{x\<in>space M. \<not> Q x} \<subseteq> A \<union> B"
      using P imp by auto
  qed
qed

lemma (in measure_space)
  shows AE_iffI: "AE x. P x \<Longrightarrow> AE x. P x \<longleftrightarrow> Q x \<Longrightarrow> AE x. Q x"
    and AE_disjI1: "AE x. P x \<Longrightarrow> AE x. P x \<or> Q x"
    and AE_disjI2: "AE x. Q x \<Longrightarrow> AE x. P x \<or> Q x"
    and AE_conjI: "AE x. P x \<Longrightarrow> AE x. Q x \<Longrightarrow> AE x. P x \<and> Q x"
    and AE_conj_iff[simp]: "(AE x. P x \<and> Q x) \<longleftrightarrow> (AE x. P x) \<and> (AE x. Q x)"
  by auto

lemma (in measure_space) AE_measure:
  assumes AE: "AE x. P x" and sets: "{x\<in>space M. P x} \<in> sets M"
  shows "\<mu> {x\<in>space M. P x} = \<mu> (space M)"
proof -
  from AE_E[OF AE] guess N . note N = this
  with sets have "\<mu> (space M) \<le> \<mu> ({x\<in>space M. P x} \<union> N)"
    by (intro measure_mono) auto
  also have "\<dots> \<le> \<mu> {x\<in>space M. P x} + \<mu> N"
    using sets N by (intro measure_subadditive) auto
  also have "\<dots> = \<mu> {x\<in>space M. P x}" using N by simp
  finally show "\<mu> {x\<in>space M. P x} = \<mu> (space M)"
    using measure_top[OF sets] by auto
qed

lemma (in measure_space) AE_space: "AE x. x \<in> space M"
  by (rule AE_I[where N="{}"]) auto

lemma (in measure_space) AE_I2[simp, intro]:
  "(\<And>x. x \<in> space M \<Longrightarrow> P x) \<Longrightarrow> AE x. P x"
  using AE_space by auto

lemma (in measure_space) AE_Ball_mp:
  "\<forall>x\<in>space M. P x \<Longrightarrow> AE x. P x \<longrightarrow> Q x \<Longrightarrow> AE x. Q x"
  by auto

lemma (in measure_space) AE_cong[cong]:
  "(\<And>x. x \<in> space M \<Longrightarrow> P x \<longleftrightarrow> Q x) \<Longrightarrow> (AE x. P x) \<longleftrightarrow> (AE x. Q x)"
  by auto

lemma (in measure_space) AE_all_countable:
  "(AE x. \<forall>i. P i x) \<longleftrightarrow> (\<forall>i::'i::countable. AE x. P i x)"
proof
  assume "\<forall>i. AE x. P i x"
  from this[unfolded almost_everywhere_def Bex_def, THEN choice]
  obtain N where N: "\<And>i. N i \<in> null_sets" "\<And>i. {x\<in>space M. \<not> P i x} \<subseteq> N i" by auto
  have "{x\<in>space M. \<not> (\<forall>i. P i x)} \<subseteq> (\<Union>i. {x\<in>space M. \<not> P i x})" by auto
  also have "\<dots> \<subseteq> (\<Union>i. N i)" using N by auto
  finally have "{x\<in>space M. \<not> (\<forall>i. P i x)} \<subseteq> (\<Union>i. N i)" .
  moreover from N have "(\<Union>i. N i) \<in> null_sets"
    by (intro null_sets_UN) auto
  ultimately show "AE x. \<forall>i. P i x"
    unfolding almost_everywhere_def by auto
qed auto

lemma (in measure_space) AE_finite_all:
  assumes f: "finite S" shows "(AE x. \<forall>i\<in>S. P i x) \<longleftrightarrow> (\<forall>i\<in>S. AE x. P i x)"
  using f by induct auto

lemma (in measure_space) restricted_measure_space:
  assumes "S \<in> sets M"
  shows "measure_space (restricted_space S)"
    (is "measure_space ?r")
  unfolding measure_space_def measure_space_axioms_def
proof safe
  show "sigma_algebra ?r" using restricted_sigma_algebra[OF assms] .
  show "positive ?r (measure ?r)" using `S \<in> sets M` by (auto simp: positive_def)

  show "countably_additive ?r (measure ?r)"
    unfolding countably_additive_def
  proof safe
    fix A :: "nat \<Rightarrow> 'a set"
    assume *: "range A \<subseteq> sets ?r" and **: "disjoint_family A"
    from restriction_in_sets[OF assms *[simplified]] **
    show "(\<Sum>n. measure ?r (A n)) = measure ?r (\<Union>i. A i)"
      using measure_countably_additive by simp
  qed
qed

lemma (in measure_space) AE_restricted:
  assumes "A \<in> sets M"
  shows "(AE x in restricted_space A. P x) \<longleftrightarrow> (AE x. x \<in> A \<longrightarrow> P x)"
proof -
  interpret R: measure_space "restricted_space A"
    by (rule restricted_measure_space[OF `A \<in> sets M`])
  show ?thesis
  proof
    assume "AE x in restricted_space A. P x"
    from this[THEN R.AE_E] guess N' .
    then obtain N where "{x \<in> A. \<not> P x} \<subseteq> A \<inter> N" "\<mu> (A \<inter> N) = 0" "N \<in> sets M"
      by auto
    moreover then have "{x \<in> space M. \<not> (x \<in> A \<longrightarrow> P x)} \<subseteq> A \<inter> N"
      using `A \<in> sets M` sets_into_space by auto
    ultimately show "AE x. x \<in> A \<longrightarrow> P x"
      using `A \<in> sets M` by (auto intro!: AE_I[where N="A \<inter> N"])
  next
    assume "AE x. x \<in> A \<longrightarrow> P x"
    from this[THEN AE_E] guess N .
    then show "AE x in restricted_space A. P x"
      using null_set_Int1[OF _ `A \<in> sets M`] `A \<in> sets M`[THEN sets_into_space]
      by (auto intro!: R.AE_I[where N="A \<inter> N"] simp: subset_eq)
  qed
qed

lemma (in measure_space) measure_space_subalgebra:
  assumes "sigma_algebra N" and "sets N \<subseteq> sets M" "space N = space M"
  and measure[simp]: "\<And>X. X \<in> sets N \<Longrightarrow> measure N X = measure M X"
  shows "measure_space N"
proof -
  interpret N: sigma_algebra N by fact
  show ?thesis
  proof
    from `sets N \<subseteq> sets M` have "\<And>A. range A \<subseteq> sets N \<Longrightarrow> range A \<subseteq> sets M" by blast
    then show "countably_additive N (measure N)"
      by (auto intro!: measure_countably_additive simp: countably_additive_def subset_eq)
    show "positive N (measure_space.measure N)"
      using assms(2) by (auto simp add: positive_def)
  qed
qed

lemma (in measure_space) AE_subalgebra:
  assumes ae: "AE x in N. P x"
  and N: "sets N \<subseteq> sets M" "space N = space M" "\<And>A. A \<in> sets N \<Longrightarrow> measure N A = \<mu> A"
  and sa: "sigma_algebra N"
  shows "AE x. P x"
proof -
  interpret N: measure_space N using measure_space_subalgebra[OF sa N] .
  from ae[THEN N.AE_E] guess N .
  with N show ?thesis unfolding almost_everywhere_def by auto
qed

section "@{text \<sigma>}-finite Measures"

locale sigma_finite_measure = measure_space +
  assumes sigma_finite: "\<exists>A::nat \<Rightarrow> 'a set. range A \<subseteq> sets M \<and> (\<Union>i. A i) = space M \<and> (\<forall>i. \<mu> (A i) \<noteq> \<infinity>)"

lemma (in sigma_finite_measure) restricted_sigma_finite_measure:
  assumes "S \<in> sets M"
  shows "sigma_finite_measure (restricted_space S)"
    (is "sigma_finite_measure ?r")
  unfolding sigma_finite_measure_def sigma_finite_measure_axioms_def
proof safe
  show "measure_space ?r" using restricted_measure_space[OF assms] .
next
  obtain A :: "nat \<Rightarrow> 'a set" where
      "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" "\<And>i. \<mu> (A i) \<noteq> \<infinity>"
    using sigma_finite by auto
  show "\<exists>A::nat \<Rightarrow> 'a set. range A \<subseteq> sets ?r \<and> (\<Union>i. A i) = space ?r \<and> (\<forall>i. measure ?r (A i) \<noteq> \<infinity>)"
  proof (safe intro!: exI[of _ "\<lambda>i. A i \<inter> S"] del: notI)
    fix i
    show "A i \<inter> S \<in> sets ?r"
      using `range A \<subseteq> sets M` `S \<in> sets M` by auto
  next
    fix x i assume "x \<in> S" thus "x \<in> space ?r" by simp
  next
    fix x assume "x \<in> space ?r" thus "x \<in> (\<Union>i. A i \<inter> S)"
      using `(\<Union>i. A i) = space M` `S \<in> sets M` by auto
  next
    fix i
    have "\<mu> (A i \<inter> S) \<le> \<mu> (A i)"
      using `range A \<subseteq> sets M` `S \<in> sets M` by (auto intro!: measure_mono)
    then show "measure ?r (A i \<inter> S) \<noteq> \<infinity>" using `\<mu> (A i) \<noteq> \<infinity>` by auto
  qed
qed

lemma (in sigma_finite_measure) sigma_finite_measure_cong:
  assumes cong: "\<And>A. A \<in> sets M \<Longrightarrow> measure M' A = \<mu> A" "sets M' = sets M" "space M' = space M"
  shows "sigma_finite_measure M'"
proof -
  interpret M': measure_space M' by (intro measure_space_cong cong)
  from sigma_finite guess A .. note A = this
  then have "\<And>i. A i \<in> sets M" by auto
  with A have fin: "\<forall>i. measure M' (A i) \<noteq> \<infinity>" using cong by auto
  show ?thesis
    apply default
    using A fin cong by auto
qed

lemma (in sigma_finite_measure) disjoint_sigma_finite:
  "\<exists>A::nat\<Rightarrow>'a set. range A \<subseteq> sets M \<and> (\<Union>i. A i) = space M \<and>
    (\<forall>i. \<mu> (A i) \<noteq> \<infinity>) \<and> disjoint_family A"
proof -
  obtain A :: "nat \<Rightarrow> 'a set" where
    range: "range A \<subseteq> sets M" and
    space: "(\<Union>i. A i) = space M" and
    measure: "\<And>i. \<mu> (A i) \<noteq> \<infinity>"
    using sigma_finite by auto
  note range' = range_disjointed_sets[OF range] range
  { fix i
    have "\<mu> (disjointed A i) \<le> \<mu> (A i)"
      using range' disjointed_subset[of A i] by (auto intro!: measure_mono)
    then have "\<mu> (disjointed A i) \<noteq> \<infinity>"
      using measure[of i] by auto }
  with disjoint_family_disjointed UN_disjointed_eq[of A] space range'
  show ?thesis by (auto intro!: exI[of _ "disjointed A"])
qed

lemma (in sigma_finite_measure) sigma_finite_up:
  "\<exists>F. range F \<subseteq> sets M \<and> incseq F \<and> (\<Union>i. F i) = space M \<and> (\<forall>i. \<mu> (F i) \<noteq> \<infinity>)"
proof -
  obtain F :: "nat \<Rightarrow> 'a set" where
    F: "range F \<subseteq> sets M" "(\<Union>i. F i) = space M" "\<And>i. \<mu> (F i) \<noteq> \<infinity>"
    using sigma_finite by auto
  then show ?thesis
  proof (intro exI[of _ "\<lambda>n. \<Union>i\<le>n. F i"] conjI allI)
    from F have "\<And>x. x \<in> space M \<Longrightarrow> \<exists>i. x \<in> F i" by auto
    then show "(\<Union>n. \<Union> i\<le>n. F i) = space M"
      using F by fastforce
  next
    fix n
    have "\<mu> (\<Union> i\<le>n. F i) \<le> (\<Sum>i\<le>n. \<mu> (F i))" using F
      by (auto intro!: measure_finitely_subadditive)
    also have "\<dots> < \<infinity>"
      using F by (auto simp: setsum_Pinfty)
    finally show "\<mu> (\<Union> i\<le>n. F i) \<noteq> \<infinity>" by simp
  qed (force simp: incseq_def)+
qed

section {* Measure preserving *}

definition "measure_preserving A B =
    {f \<in> measurable A B. (\<forall>y \<in> sets B. measure B y = measure A (f -` y \<inter> space A))}"

lemma measure_preservingI[intro?]:
  assumes "f \<in> measurable A B"
    and "\<And>y. y \<in> sets B \<Longrightarrow> measure A (f -` y \<inter> space A) = measure B y"
  shows "f \<in> measure_preserving A B"
  unfolding measure_preserving_def using assms by auto

lemma (in measure_space) measure_space_vimage:
  fixes M' :: "('c, 'd) measure_space_scheme"
  assumes T: "sigma_algebra M'" "T \<in> measure_preserving M M'"
  shows "measure_space M'"
proof -
  interpret M': sigma_algebra M' by fact
  show ?thesis
  proof
    show "positive M' (measure M')" using T
      by (auto simp: measure_preserving_def positive_def measurable_sets)

    show "countably_additive M' (measure M')"
    proof (intro countably_additiveI)
      fix A :: "nat \<Rightarrow> 'c set" assume "range A \<subseteq> sets M'" "disjoint_family A"
      then have A: "\<And>i. A i \<in> sets M'" "(\<Union>i. A i) \<in> sets M'" by auto
      then have *: "range (\<lambda>i. T -` (A i) \<inter> space M) \<subseteq> sets M"
        using T by (auto simp: measurable_def measure_preserving_def)
      moreover have "(\<Union>i. T -`  A i \<inter> space M) \<in> sets M"
        using * by blast
      moreover have **: "disjoint_family (\<lambda>i. T -` A i \<inter> space M)"
        using `disjoint_family A` by (auto simp: disjoint_family_on_def)
      ultimately show "(\<Sum>i. measure M' (A i)) = measure M' (\<Union>i. A i)"
        using measure_countably_additive[OF _ **] A T
        by (auto simp: comp_def vimage_UN measure_preserving_def)
    qed
  qed
qed

lemma (in measure_space) almost_everywhere_vimage:
  assumes T: "sigma_algebra M'" "T \<in> measure_preserving M M'"
    and AE: "measure_space.almost_everywhere M' P"
  shows "AE x. P (T x)"
proof -
  interpret M': measure_space M' using T by (rule measure_space_vimage)
  from AE[THEN M'.AE_E] guess N .
  then show ?thesis
    unfolding almost_everywhere_def M'.almost_everywhere_def
    using T(2) unfolding measurable_def measure_preserving_def
    by (intro bexI[of _ "T -` N \<inter> space M"]) auto
qed

lemma measure_unique_Int_stable_vimage:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes E: "Int_stable E"
  and A: "range A \<subseteq> sets E" "incseq A" "(\<Union>i. A i) = space E" "\<And>i. measure M (A i) \<noteq> \<infinity>"
  and N: "measure_space N" "T \<in> measurable N M"
  and M: "measure_space M" "sets (sigma E) = sets M" "space E = space M"
  and eq: "\<And>X. X \<in> sets E \<Longrightarrow> measure M X = measure N (T -` X \<inter> space N)"
  assumes X: "X \<in> sets (sigma E)"
  shows "measure M X = measure N (T -` X \<inter> space N)"
proof (rule measure_unique_Int_stable[OF E A(1,2,3) _ _ eq _ X])
  interpret M: measure_space M by fact
  interpret N: measure_space N by fact
  let "?T X" = "T -` X \<inter> space N"
  show "measure_space \<lparr>space = space E, sets = sets (sigma E), measure = measure M\<rparr>"
    by (rule M.measure_space_cong) (auto simp: M)
  show "measure_space \<lparr>space = space E, sets = sets (sigma E), measure = \<lambda>X. measure N (?T X)\<rparr>" (is "measure_space ?E")
  proof (rule N.measure_space_vimage)
    show "sigma_algebra ?E"
      by (rule M.sigma_algebra_cong) (auto simp: M)
    show "T \<in> measure_preserving N ?E"
      using `T \<in> measurable N M` by (auto simp: M measurable_def measure_preserving_def)
  qed
  show "\<And>i. M.\<mu> (A i) \<noteq> \<infinity>" by fact
qed

lemma (in measure_space) measure_preserving_Int_stable:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes E: "Int_stable E" "range A \<subseteq> sets E" "incseq A" "(\<Union>i. A i) = space E" "\<And>i. measure E (A i) \<noteq> \<infinity>"
  and N: "measure_space (sigma E)"
  and T: "T \<in> measure_preserving M E"
  shows "T \<in> measure_preserving M (sigma E)"
proof
  interpret E: measure_space "sigma E" by fact
  show "T \<in> measurable M (sigma E)"
    using T E.sets_into_space
    by (intro measurable_sigma) (auto simp: measure_preserving_def measurable_def)
  fix X assume "X \<in> sets (sigma E)"
  show "\<mu> (T -` X \<inter> space M) = E.\<mu> X"
  proof (rule measure_unique_Int_stable_vimage[symmetric])
    show "sets (sigma E) = sets (sigma E)" "space E = space (sigma E)"
      "\<And>i. E.\<mu> (A i) \<noteq> \<infinity>" using E by auto
    show "measure_space M" by default
  next
    fix X assume "X \<in> sets E" then show "E.\<mu> X = \<mu> (T -` X \<inter> space M)"
      using T unfolding measure_preserving_def by auto
  qed fact+
qed

section "Real measure values"

lemma (in measure_space) real_measure_Union:
  assumes finite: "\<mu> A \<noteq> \<infinity>" "\<mu> B \<noteq> \<infinity>"
  and measurable: "A \<in> sets M" "B \<in> sets M" "A \<inter> B = {}"
  shows "real (\<mu> (A \<union> B)) = real (\<mu> A) + real (\<mu> B)"
  unfolding measure_additive[symmetric, OF measurable]
  using measurable(1,2)[THEN positive_measure]
  using finite by (cases rule: ereal2_cases[of "\<mu> A" "\<mu> B"]) auto

lemma (in measure_space) real_measure_finite_Union:
  assumes measurable:
    "finite S" "\<And>i. i \<in> S \<Longrightarrow> A i \<in> sets M" "disjoint_family_on A S"
  assumes finite: "\<And>i. i \<in> S \<Longrightarrow> \<mu> (A i) \<noteq> \<infinity>"
  shows "real (\<mu> (\<Union>i\<in>S. A i)) = (\<Sum>i\<in>S. real (\<mu> (A i)))"
  using finite measurable(2)[THEN positive_measure]
  by (force intro!: setsum_real_of_ereal[symmetric]
            simp: measure_setsum[OF measurable, symmetric])

lemma (in measure_space) real_measure_Diff:
  assumes finite: "\<mu> A \<noteq> \<infinity>"
  and measurable: "A \<in> sets M" "B \<in> sets M" "B \<subseteq> A"
  shows "real (\<mu> (A - B)) = real (\<mu> A) - real (\<mu> B)"
proof -
  have "\<mu> (A - B) \<le> \<mu> A" "\<mu> B \<le> \<mu> A"
    using measurable by (auto intro!: measure_mono)
  hence "real (\<mu> ((A - B) \<union> B)) = real (\<mu> (A - B)) + real (\<mu> B)"
    using measurable finite by (rule_tac real_measure_Union) auto
  thus ?thesis using `B \<subseteq> A` by (auto simp: Un_absorb2)
qed

lemma (in measure_space) real_measure_UNION:
  assumes measurable: "range A \<subseteq> sets M" "disjoint_family A"
  assumes finite: "\<mu> (\<Union>i. A i) \<noteq> \<infinity>"
  shows "(\<lambda>i. real (\<mu> (A i))) sums (real (\<mu> (\<Union>i. A i)))"
proof -
  have "\<And>i. 0 \<le> \<mu> (A i)" using measurable by auto
  with summable_sums[OF summable_ereal_pos, of "\<lambda>i. \<mu> (A i)"]
     measure_countably_additive[OF measurable]
  have "(\<lambda>i. \<mu> (A i)) sums (\<mu> (\<Union>i. A i))" by simp
  moreover
  { fix i
    have "\<mu> (A i) \<le> \<mu> (\<Union>i. A i)"
      using measurable by (auto intro!: measure_mono)
    moreover have "0 \<le> \<mu> (A i)" using measurable by auto
    ultimately have "\<mu> (A i) = ereal (real (\<mu> (A i)))"
      using finite by (cases "\<mu> (A i)") auto }
  moreover
  have "0 \<le> \<mu> (\<Union>i. A i)" using measurable by auto
  then have "\<mu> (\<Union>i. A i) = ereal (real (\<mu> (\<Union>i. A i)))"
    using finite by (cases "\<mu> (\<Union>i. A i)") auto
  ultimately show ?thesis
    unfolding sums_ereal[symmetric] by simp
qed

lemma (in measure_space) real_measure_subadditive:
  assumes measurable: "A \<in> sets M" "B \<in> sets M"
  and fin: "\<mu> A \<noteq> \<infinity>" "\<mu> B \<noteq> \<infinity>"
  shows "real (\<mu> (A \<union> B)) \<le> real (\<mu> A) + real (\<mu> B)"
proof -
  have "0 \<le> \<mu> (A \<union> B)" using measurable by auto
  then show "real (\<mu> (A \<union> B)) \<le> real (\<mu> A) + real (\<mu> B)"
    using measure_subadditive[OF measurable] fin
    by (cases rule: ereal3_cases[of "\<mu> (A \<union> B)" "\<mu> A" "\<mu> B"]) auto
qed

lemma (in measure_space) real_measure_setsum_singleton:
  assumes S: "finite S" "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  and fin: "\<And>x. x \<in> S \<Longrightarrow> \<mu> {x} \<noteq> \<infinity>"
  shows "real (\<mu> S) = (\<Sum>x\<in>S. real (\<mu> {x}))"
  using measure_finite_singleton[OF S] fin
  using positive_measure[OF S(2)]
  by (force intro!: setsum_real_of_ereal[symmetric])

lemma (in measure_space) real_continuity_from_below:
  assumes A: "range A \<subseteq> sets M" "incseq A" and fin: "\<mu> (\<Union>i. A i) \<noteq> \<infinity>"
  shows "(\<lambda>i. real (\<mu> (A i))) ----> real (\<mu> (\<Union>i. A i))"
proof -
  have "0 \<le> \<mu> (\<Union>i. A i)" using A by auto
  then have "ereal (real (\<mu> (\<Union>i. A i))) = \<mu> (\<Union>i. A i)"
    using fin by (auto intro: ereal_real')
  then show ?thesis
    using continuity_from_below_Lim[OF A]
    by (intro lim_real_of_ereal) simp
qed

lemma (in measure_space) continuity_from_above_Lim:
  assumes A: "range A \<subseteq> sets M" "decseq A" and fin: "\<And>i. \<mu> (A i) \<noteq> \<infinity>"
  shows "(\<lambda>i. (\<mu> (A i))) ----> \<mu> (\<Inter>i. A i)"
  using LIMSEQ_ereal_INFI[OF measure_decseq, OF A]
  using continuity_from_above[OF A fin] by simp

lemma (in measure_space) real_continuity_from_above:
  assumes A: "range A \<subseteq> sets M" "decseq A" and fin: "\<And>i. \<mu> (A i) \<noteq> \<infinity>"
  shows "(\<lambda>n. real (\<mu> (A n))) ----> real (\<mu> (\<Inter>i. A i))"
proof -
  have "0 \<le> \<mu> (\<Inter>i. A i)" using A by auto
  moreover
  have "\<mu> (\<Inter>i. A i) \<le> \<mu> (A 0)"
    using A by (auto intro!: measure_mono)
  ultimately have "ereal (real (\<mu> (\<Inter>i. A i))) = \<mu> (\<Inter>i. A i)"
    using fin by (auto intro: ereal_real')
  then show ?thesis
    using continuity_from_above_Lim[OF A fin]
    by (intro lim_real_of_ereal) simp
qed

lemma (in measure_space) real_measure_countably_subadditive:
  assumes A: "range A \<subseteq> sets M" and fin: "(\<Sum>i. \<mu> (A i)) \<noteq> \<infinity>"
  shows "real (\<mu> (\<Union>i. A i)) \<le> (\<Sum>i. real (\<mu> (A i)))"
proof -
  { fix i
    have "0 \<le> \<mu> (A i)" using A by auto
    moreover have "\<mu> (A i) \<noteq> \<infinity>" using A by (intro suminf_PInfty[OF _ fin]) auto
    ultimately have "\<bar>\<mu> (A i)\<bar> \<noteq> \<infinity>" by auto }
  moreover have "0 \<le> \<mu> (\<Union>i. A i)" using A by auto
  ultimately have "ereal (real (\<mu> (\<Union>i. A i))) \<le> (\<Sum>i. ereal (real (\<mu> (A i))))"
    using measure_countably_subadditive[OF A] by (auto simp: ereal_real)
  also have "\<dots> = ereal (\<Sum>i. real (\<mu> (A i)))"
    using A
    by (auto intro!: sums_unique[symmetric] sums_ereal[THEN iffD2] summable_sums summable_real_of_ereal fin)
  finally show ?thesis by simp
qed

locale finite_measure = measure_space +
  assumes finite_measure_of_space: "\<mu> (space M) \<noteq> \<infinity>"

sublocale finite_measure < sigma_finite_measure
proof
  show "\<exists>A. range A \<subseteq> sets M \<and> (\<Union>i. A i) = space M \<and> (\<forall>i. \<mu> (A i) \<noteq> \<infinity>)"
    using finite_measure_of_space by (auto intro!: exI[of _ "\<lambda>x. space M"])
qed

lemma (in finite_measure) finite_measure[simp, intro]:
  assumes "A \<in> sets M"
  shows "\<mu> A \<noteq> \<infinity>"
proof -
  from `A \<in> sets M` have "A \<subseteq> space M"
    using sets_into_space by blast
  then have "\<mu> A \<le> \<mu> (space M)"
    using assms top by (rule measure_mono)
  then show ?thesis
    using finite_measure_of_space by auto
qed

definition (in finite_measure)
  "\<mu>' A = (if A \<in> sets M then real (\<mu> A) else 0)"

lemma (in finite_measure) finite_measure_eq: "A \<in> sets M \<Longrightarrow> \<mu> A = ereal (\<mu>' A)"
  by (auto simp: \<mu>'_def ereal_real)

lemma (in finite_measure) positive_measure'[simp, intro]: "0 \<le> \<mu>' A"
  unfolding \<mu>'_def by (auto simp: real_of_ereal_pos)

lemma (in finite_measure) real_measure:
  assumes A: "A \<in> sets M" shows "\<exists>r. 0 \<le> r \<and> \<mu> A = ereal r"
  using finite_measure[OF A] positive_measure[OF A] by (cases "\<mu> A") auto

lemma (in finite_measure) bounded_measure: "\<mu>' A \<le> \<mu>' (space M)"
proof cases
  assume "A \<in> sets M"
  moreover then have "\<mu> A \<le> \<mu> (space M)"
    using sets_into_space by (auto intro!: measure_mono)
  ultimately show ?thesis
    by (auto simp: \<mu>'_def intro!: real_of_ereal_positive_mono)
qed (simp add: \<mu>'_def real_of_ereal_pos)

lemma (in finite_measure) restricted_finite_measure:
  assumes "S \<in> sets M"
  shows "finite_measure (restricted_space S)"
    (is "finite_measure ?r")
  unfolding finite_measure_def finite_measure_axioms_def
proof (intro conjI)
  show "measure_space ?r" using restricted_measure_space[OF assms] .
next
  show "measure ?r (space ?r) \<noteq> \<infinity>" using finite_measure[OF `S \<in> sets M`] by auto
qed

lemma (in measure_space) restricted_to_finite_measure:
  assumes "S \<in> sets M" "\<mu> S \<noteq> \<infinity>"
  shows "finite_measure (restricted_space S)"
proof -
  have "measure_space (restricted_space S)"
    using `S \<in> sets M` by (rule restricted_measure_space)
  then show ?thesis
    unfolding finite_measure_def finite_measure_axioms_def
    using assms by auto
qed

lemma (in finite_measure) finite_measure_Diff:
  assumes sets: "A \<in> sets M" "B \<in> sets M" and "B \<subseteq> A"
  shows "\<mu>' (A - B) = \<mu>' A - \<mu>' B"
  using sets[THEN finite_measure_eq]
  using Diff[OF sets, THEN finite_measure_eq]
  using measure_Diff[OF _ assms] by simp

lemma (in finite_measure) finite_measure_Union:
  assumes sets: "A \<in> sets M" "B \<in> sets M" and "A \<inter> B = {}"
  shows "\<mu>' (A \<union> B) = \<mu>' A + \<mu>' B"
  using measure_additive[OF assms]
  using sets[THEN finite_measure_eq]
  using Un[OF sets, THEN finite_measure_eq]
  by simp

lemma (in finite_measure) finite_measure_finite_Union:
  assumes S: "finite S" "\<And>i. i \<in> S \<Longrightarrow> A i \<in> sets M"
  and dis: "disjoint_family_on A S"
  shows "\<mu>' (\<Union>i\<in>S. A i) = (\<Sum>i\<in>S. \<mu>' (A i))"
  using measure_setsum[OF assms]
  using finite_UN[of S A, OF S, THEN finite_measure_eq]
  using S(2)[THEN finite_measure_eq]
  by simp

lemma (in finite_measure) finite_measure_UNION:
  assumes A: "range A \<subseteq> sets M" "disjoint_family A"
  shows "(\<lambda>i. \<mu>' (A i)) sums (\<mu>' (\<Union>i. A i))"
  using real_measure_UNION[OF A]
  using countable_UN[OF A(1), THEN finite_measure_eq]
  using A(1)[THEN subsetD, THEN finite_measure_eq]
  by auto

lemma (in finite_measure) finite_measure_mono:
  assumes B: "B \<in> sets M" and "A \<subseteq> B" shows "\<mu>' A \<le> \<mu>' B"
proof cases
  assume "A \<in> sets M"
  from this[THEN finite_measure_eq] B[THEN finite_measure_eq]
  show ?thesis using measure_mono[OF `A \<subseteq> B` `A \<in> sets M` `B \<in> sets M`] by simp
next
  assume "A \<notin> sets M" then show ?thesis
    using positive_measure'[of B] unfolding \<mu>'_def by auto
qed

lemma (in finite_measure) finite_measure_subadditive:
  assumes m: "A \<in> sets M" "B \<in> sets M"
  shows "\<mu>' (A \<union> B) \<le> \<mu>' A + \<mu>' B"
  using measure_subadditive[OF m]
  using m[THEN finite_measure_eq] Un[OF m, THEN finite_measure_eq] by simp

lemma (in finite_measure) finite_measure_subadditive_finite:
  assumes "finite I" "\<And>i. i\<in>I \<Longrightarrow> A i \<in> sets M"
  shows "\<mu>' (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. \<mu>' (A i))"
  using measure_subadditive_finite[OF assms] assms
  by (simp add: finite_measure_eq finite_UN)

lemma (in finite_measure) finite_measure_countably_subadditive:
  assumes A: "range A \<subseteq> sets M" and sum: "summable (\<lambda>i. \<mu>' (A i))"
  shows "\<mu>' (\<Union>i. A i) \<le> (\<Sum>i. \<mu>' (A i))"
proof -
  note A[THEN subsetD, THEN finite_measure_eq, simp]
  note countable_UN[OF A, THEN finite_measure_eq, simp]
  from `summable (\<lambda>i. \<mu>' (A i))`
  have "(\<lambda>i. ereal (\<mu>' (A i))) sums ereal (\<Sum>i. \<mu>' (A i))"
    by (simp add: sums_ereal) (rule summable_sums)
  from sums_unique[OF this, symmetric]
       measure_countably_subadditive[OF A]
  show ?thesis by simp
qed

lemma (in finite_measure) finite_measure_finite_singleton:
  assumes "finite S" and *: "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  shows "\<mu>' S = (\<Sum>x\<in>S. \<mu>' {x})"
  using real_measure_setsum_singleton[OF assms]
  using *[THEN finite_measure_eq]
  using finite_UN[of S "\<lambda>x. {x}", OF assms, THEN finite_measure_eq]
  by simp

lemma (in finite_measure) finite_continuity_from_below:
  assumes A: "range A \<subseteq> sets M" and "incseq A"
  shows "(\<lambda>i. \<mu>' (A i)) ----> \<mu>' (\<Union>i. A i)"
  using real_continuity_from_below[OF A, OF `incseq A` finite_measure] assms
  using A[THEN subsetD, THEN finite_measure_eq]
  using countable_UN[OF A, THEN finite_measure_eq]
  by auto

lemma (in finite_measure) finite_continuity_from_above:
  assumes A: "range A \<subseteq> sets M" and "decseq A"
  shows "(\<lambda>n. \<mu>' (A n)) ----> \<mu>' (\<Inter>i. A i)"
  using real_continuity_from_above[OF A, OF `decseq A` finite_measure] assms
  using A[THEN subsetD, THEN finite_measure_eq]
  using countable_INT[OF A, THEN finite_measure_eq]
  by auto

lemma (in finite_measure) finite_measure_compl:
  assumes S: "S \<in> sets M"
  shows "\<mu>' (space M - S) = \<mu>' (space M) - \<mu>' S"
  using measure_compl[OF S, OF finite_measure, OF S]
  using S[THEN finite_measure_eq]
  using compl_sets[OF S, THEN finite_measure_eq]
  using top[THEN finite_measure_eq]
  by simp

lemma (in finite_measure) finite_measure_inter_full_set:
  assumes S: "S \<in> sets M" "T \<in> sets M"
  assumes T: "\<mu>' T = \<mu>' (space M)"
  shows "\<mu>' (S \<inter> T) = \<mu>' S"
  using measure_inter_full_set[OF S finite_measure]
  using T Diff[OF S(2,1)] Diff[OF S, THEN finite_measure_eq]
  using Int[OF S, THEN finite_measure_eq]
  using S[THEN finite_measure_eq] top[THEN finite_measure_eq]
  by simp

lemma (in finite_measure) empty_measure'[simp]: "\<mu>' {} = 0"
  unfolding \<mu>'_def by simp

section "Finite spaces"

locale finite_measure_space = measure_space + finite_sigma_algebra +
  assumes finite_single_measure[simp]: "\<And>x. x \<in> space M \<Longrightarrow> \<mu> {x} \<noteq> \<infinity>"

lemma (in finite_measure_space) sum_over_space: "(\<Sum>x\<in>space M. \<mu> {x}) = \<mu> (space M)"
  using measure_setsum[of "space M" "\<lambda>i. {i}"]
  by (simp add: sets_eq_Pow disjoint_family_on_def finite_space)

lemma finite_measure_spaceI:
  assumes "finite (space M)" "sets M = Pow(space M)" and space: "measure M (space M) \<noteq> \<infinity>"
    and add: "\<And>A B. A\<subseteq>space M \<Longrightarrow> B\<subseteq>space M \<Longrightarrow> A \<inter> B = {} \<Longrightarrow> measure M (A \<union> B) = measure M A + measure M B"
    and "measure M {} = 0" "\<And>A. A \<subseteq> space M \<Longrightarrow> 0 \<le> measure M A"
  shows "finite_measure_space M"
    unfolding finite_measure_space_def finite_measure_space_axioms_def
proof (intro allI impI conjI)
  show "measure_space M"
  proof (rule finite_additivity_sufficient)
    have *: "\<lparr>space = space M, sets = Pow (space M), \<dots> = algebra.more M\<rparr> = M"
      unfolding assms(2)[symmetric] by (auto intro!: algebra.equality)
    show "sigma_algebra M"
      using sigma_algebra_Pow[of "space M" "algebra.more M"]
      unfolding * .
    show "finite (space M)" by fact
    show "positive M (measure M)" unfolding positive_def using assms by auto
    show "additive M (measure M)" unfolding additive_def using assms by simp
  qed
  then interpret measure_space M .
  show "finite_sigma_algebra M"
  proof
    show "finite (space M)" by fact
    show "sets M = Pow (space M)" using assms by auto
  qed
  { fix x assume *: "x \<in> space M"
    with add[of "{x}" "space M - {x}"] space
    show "\<mu> {x} \<noteq> \<infinity>" by (auto simp: insert_absorb[OF *] Diff_subset) }
qed

sublocale finite_measure_space \<subseteq> finite_measure
proof
  show "\<mu> (space M) \<noteq> \<infinity>"
    unfolding sum_over_space[symmetric] setsum_Pinfty
    using finite_space finite_single_measure by auto
qed

lemma finite_measure_space_iff:
  "finite_measure_space M \<longleftrightarrow>
    finite (space M) \<and> sets M = Pow(space M) \<and> measure M (space M) \<noteq> \<infinity> \<and>
    measure M {} = 0 \<and> (\<forall>A\<subseteq>space M. 0 \<le> measure M A) \<and>
    (\<forall>A\<subseteq>space M. \<forall>B\<subseteq>space M. A \<inter> B = {} \<longrightarrow> measure M (A \<union> B) = measure M A + measure M B)"
    (is "_ = ?rhs")
proof (intro iffI)
  assume "finite_measure_space M"
  then interpret finite_measure_space M .
  show ?rhs
    using finite_space sets_eq_Pow measure_additive empty_measure finite_measure
    by auto
next
  assume ?rhs then show "finite_measure_space M"
    by (auto intro!: finite_measure_spaceI)
qed

lemma (in finite_measure_space) finite_measure_singleton:
  assumes A: "A \<subseteq> space M" shows "\<mu>' A = (\<Sum>x\<in>A. \<mu>' {x})"
  using A finite_subset[OF A finite_space]
  by (intro finite_measure_finite_singleton) auto

lemma (in finite_measure_space) finite_measure_subadditive_setsum:
  assumes "finite I"
  shows "\<mu>' (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. \<mu>' (A i))"
proof cases
  assume "(\<Union>i\<in>I. A i) \<subseteq> space M"
  then have "\<And>i. i\<in>I \<Longrightarrow> A i \<in> sets M" by auto
  from finite_measure_subadditive_finite[OF `finite I` this]
  show ?thesis by auto
next
  assume "\<not> (\<Union>i\<in>I. A i) \<subseteq> space M"
  then have "\<mu>' (\<Union>i\<in>I. A i) = 0"
    by (simp add: \<mu>'_def)
  also have "0 \<le> (\<Sum>i\<in>I. \<mu>' (A i))"
    by (auto intro!: setsum_nonneg)
  finally show ?thesis .
qed

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

end