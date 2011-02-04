(* Author: Lawrence C Paulson; Armin Heller, Johannes Hoelzl, TU Muenchen *)

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
  shows "psuminf (\<lambda>i. \<mu> (A i)) = \<mu> (\<Union>i. A i)"
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
    show "measure N {} = 0" using assms by auto
    show "countably_additive N (measure N)" unfolding countably_additive_def
    proof safe
      fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> sets N" "disjoint_family A"
      then have "\<And>i. A i \<in> sets M" "(UNION UNIV A) \<in> sets M" unfolding assms by auto
      from measure_countably_additive[of A] A this[THEN assms(1)]
      show "(\<Sum>\<^isub>\<infinity>n. measure N (A n)) = measure N (UNION UNIV A)"
        unfolding assms by simp
    qed
  qed
qed

lemma (in measure_space) additive: "additive M \<mu>"
proof (rule algebra.countably_additive_additive [OF _ _ ca])
  show "algebra M" by default
  show "positive M \<mu>" by (simp add: positive_def)
qed

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
    using measure_additive[of a "b - a"] local.Diff[of b a] assms by auto
  moreover have "\<mu> (b - a) \<ge> 0" using assms by auto
  ultimately show "\<mu> a \<le> \<mu> b" by auto
qed

lemma (in measure_space) measure_compl:
  assumes s: "s \<in> sets M" and fin: "\<mu> s \<noteq> \<omega>"
  shows "\<mu> (space M - s) = \<mu> (space M) - \<mu> s"
proof -
  have s_less_space: "\<mu> s \<le> \<mu> (space M)"
    using s by (auto intro!: measure_mono sets_into_space)

  have "\<mu> (space M) = \<mu> (s \<union> (space M - s))" using s
    by (metis Un_Diff_cancel Un_absorb1 s sets_into_space)
  also have "... = \<mu> s + \<mu> (space M - s)"
    by (rule additiveD [OF additive]) (auto simp add: s)
  finally have "\<mu> (space M) = \<mu> s + \<mu> (space M - s)" .
  thus ?thesis
    unfolding minus_pextreal_eq2[OF s_less_space fin]
    by (simp add: ac_simps)
qed

lemma (in measure_space) measure_Diff:
  assumes finite: "\<mu> B \<noteq> \<omega>"
  and measurable: "A \<in> sets M" "B \<in> sets M" "B \<subseteq> A"
  shows "\<mu> (A - B) = \<mu> A - \<mu> B"
proof -
  have *: "(A - B) \<union> B = A" using `B \<subseteq> A` by auto

  have "\<mu> ((A - B) \<union> B) = \<mu> (A - B) + \<mu> B"
    using measurable by (rule_tac measure_additive[symmetric]) auto
  thus ?thesis unfolding * using `\<mu> B \<noteq> \<omega>`
    by (simp add: pextreal_cancel_plus_minus)
qed

lemma (in measure_space) measure_countable_increasing:
  assumes A: "range A \<subseteq> sets M"
      and A0: "A 0 = {}"
      and ASuc: "\<And>n.  A n \<subseteq> A (Suc n)"
  shows "(SUP n. \<mu> (A n)) = \<mu> (\<Union>i. A i)"
proof -
  {
    fix n
    have "\<mu> (A n) =
          setsum (\<mu> \<circ> (\<lambda>i. A (Suc i) - A i)) {..<n}"
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
  have "psuminf ( (\<lambda>i. \<mu> (A (Suc i) - A i))) = \<mu> (\<Union>i. A (Suc i) - A i)"
    by (rule measure_countably_additive)
       (auto simp add: disjoint_family_Suc ASuc A1 A2)
  also have "... =  \<mu> (\<Union>i. A i)"
    by (simp add: Aeq)
  finally have "psuminf (\<lambda>i. \<mu> (A (Suc i) - A i)) = \<mu> (\<Union>i. A i)" .
  thus ?thesis
    by (auto simp add: Meq psuminf_def)
qed

lemma (in measure_space) continuity_from_below:
  assumes A: "range A \<subseteq> sets M"
      and ASuc: "!!n.  A n \<subseteq> A (Suc n)"
  shows "(SUP n. \<mu> (A n)) = \<mu> (\<Union>i. A i)"
proof -
  have *: "(SUP n. \<mu> (nat_case {} A (Suc n))) = (SUP n. \<mu> (nat_case {} A n))"
    apply (rule Sup_mono_offset_Suc)
    apply (rule measure_mono)
    using assms by (auto split: nat.split)

  have ueq: "(\<Union>i. nat_case {} A i) = (\<Union>i. A i)"
    by (auto simp add: split: nat.splits)
  have meq: "\<And>n. \<mu> (A n) = (\<mu> \<circ> nat_case {} A) (Suc n)"
    by simp
  have "(SUP n. \<mu> (nat_case {} A n)) = \<mu> (\<Union>i. nat_case {} A i)"
    by (rule measure_countable_increasing)
       (auto simp add: range_subsetD [OF A] subsetD [OF ASuc] split: nat.splits)
  also have "\<mu> (\<Union>i. nat_case {} A i) = \<mu> (\<Union>i. A i)"
    by (simp add: ueq)
  finally have "(SUP n. \<mu> (nat_case {} A n)) = \<mu> (\<Union>i. A i)" .
  thus ?thesis unfolding meq * comp_def .
qed

lemma (in measure_space) measure_up:
  assumes "\<And>i. B i \<in> sets M" "B \<up> P"
  shows "(\<lambda>i. \<mu> (B i)) \<up> \<mu> P"
  using assms unfolding isoton_def
  by (auto intro!: measure_mono continuity_from_below)

lemma (in measure_space) continuity_from_below':
  assumes A: "range A \<subseteq> sets M" "\<And>i. A i \<subseteq> A (Suc i)"
  shows "(\<lambda>i. (\<mu> (A i))) ----> (\<mu> (\<Union>i. A i))"
proof- let ?A = "\<Union>i. A i"
  have " (\<lambda>i. \<mu> (A i)) \<up> \<mu> ?A" apply(rule measure_up)
    using assms unfolding complete_lattice_class.isoton_def by auto
  thus ?thesis by(rule isotone_Lim(1))
qed

lemma (in measure_space) continuity_from_above:
  assumes A: "range A \<subseteq> sets M"
  and mono_Suc: "\<And>n.  A (Suc n) \<subseteq> A n"
  and finite: "\<And>i. \<mu> (A i) \<noteq> \<omega>"
  shows "(INF n. \<mu> (A n)) = \<mu> (\<Inter>i. A i)"
proof -
  { fix n have "A n \<subseteq> A 0" using mono_Suc by (induct n) auto }
  note mono = this

  have le_MI: "\<mu> (\<Inter>i. A i) \<le> \<mu> (A 0)"
    using A by (auto intro!: measure_mono)
  hence *: "\<mu> (\<Inter>i. A i) \<noteq> \<omega>" using finite[of 0] by auto

  have le_IM: "(INF n. \<mu> (A n)) \<le> \<mu> (A 0)"
    by (rule INF_leI) simp

  have "\<mu> (A 0) - (INF n. \<mu> (A n)) = (SUP n. \<mu> (A 0 - A n))"
    unfolding pextreal_SUP_minus[symmetric]
    using mono A finite by (subst measure_Diff) auto
  also have "\<dots> = \<mu> (\<Union>i. A 0 - A i)"
  proof (rule continuity_from_below)
    show "range (\<lambda>n. A 0 - A n) \<subseteq> sets M"
      using A by auto
    show "\<And>n. A 0 - A n \<subseteq> A 0 - A (Suc n)"
      using mono_Suc by auto
  qed
  also have "\<dots> = \<mu> (A 0) - \<mu> (\<Inter>i. A i)"
    using mono A finite * by (simp, subst measure_Diff) auto
  finally show ?thesis
    by (rule pextreal_diff_eq_diff_imp_eq[OF finite[of 0] le_IM le_MI])
qed

lemma (in measure_space) measure_down:
  assumes "\<And>i. B i \<in> sets M" "B \<down> P"
  and finite: "\<And>i. \<mu> (B i) \<noteq> \<omega>"
  shows "(\<lambda>i. \<mu> (B i)) \<down> \<mu> P"
  using assms unfolding antiton_def
  by (auto intro!: measure_mono continuity_from_above)
lemma (in measure_space) measure_insert:
  assumes sets: "{x} \<in> sets M" "A \<in> sets M" and "x \<notin> A"
  shows "\<mu> (insert x A) = \<mu> {x} + \<mu> A"
proof -
  have "{x} \<inter> A = {}" using `x \<notin> A` by auto
  from measure_additive[OF sets this] show ?thesis by simp
qed

lemma (in measure_space) measure_finite_singleton:
  assumes fin: "finite S"
  and ssets: "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  shows "\<mu> S = (\<Sum>x\<in>S. \<mu> {x})"
using assms proof induct
  case (insert x S)
  have *: "\<mu> S = (\<Sum>x\<in>S. \<mu> {x})" "{x} \<in> sets M"
    using insert.prems by (blast intro!: insert.hyps(3))+

  have "(\<Union>x\<in>S. {x}) \<in> sets M"
    using  insert.prems `finite S` by (blast intro!: finite_UN)
  hence "S \<in> sets M" by auto
  from measure_insert[OF `{x} \<in> sets M` this `x \<notin> S`]
  show ?case using `x \<notin> S` `finite S` * by simp
qed simp

lemma (in measure_space) measure_finitely_additive':
  assumes "f \<in> ({..< n :: nat} \<rightarrow> sets M)"
  assumes "\<And> a b. \<lbrakk>a < n ; b < n ; a \<noteq> b\<rbrakk> \<Longrightarrow> f a \<inter> f b = {}"
  assumes "s = \<Union> (f ` {..< n})"
  shows "(\<Sum>i<n. (\<mu> \<circ> f) i) = \<mu> s"
proof -
  def f' == "\<lambda> i. (if i < n then f i else {})"
  have rf: "range f' \<subseteq> sets M" unfolding f'_def
    using assms empty_sets by auto
  have df: "disjoint_family f'" unfolding f'_def disjoint_family_on_def
    using assms by simp
  have "\<Union> range f' = (\<Union> i \<in> {..< n}. f i)"
    unfolding f'_def by auto
  then have "\<mu> s = \<mu> (\<Union> range f')"
    using assms by simp
  then have part1: "(\<Sum>\<^isub>\<infinity> i. \<mu> (f' i)) = \<mu> s"
    using df rf ca[unfolded countably_additive_def, rule_format, of f']
    by auto

  have "(\<Sum>\<^isub>\<infinity> i. \<mu> (f' i)) = (\<Sum> i< n. \<mu> (f' i))"
    by (rule psuminf_finite) (simp add: f'_def)
  also have "\<dots> = (\<Sum>i<n. \<mu> (f i))"
    unfolding f'_def by auto
  finally have part2: "(\<Sum>\<^isub>\<infinity> i. \<mu> (f' i)) = (\<Sum>i<n. \<mu> (f i))" by simp
  show ?thesis using part1 part2 by auto
qed


lemma (in measure_space) measure_finitely_additive:
  assumes "finite r"
  assumes "r \<subseteq> sets M"
  assumes d: "\<And> a b. \<lbrakk>a \<in> r ; b \<in> r ; a \<noteq> b\<rbrakk> \<Longrightarrow> a \<inter> b = {}"
  shows "(\<Sum> i \<in> r. \<mu> i) = \<mu> (\<Union> r)"
using assms
proof -
  (* counting the elements in r is enough *)
  let ?R = "{..<card r}"
  obtain f where f: "f ` ?R = r" "inj_on f ?R"
    using ex_bij_betw_nat_finite[unfolded bij_betw_def, OF `finite r`]
    unfolding atLeast0LessThan by auto
  hence f_into_sets: "f \<in> ?R \<rightarrow> sets M" using assms by auto
  have disj: "\<And> a b. \<lbrakk>a \<in> ?R ; b \<in> ?R ; a \<noteq> b\<rbrakk> \<Longrightarrow> f a \<inter> f b = {}"
  proof -
    fix a b assume asm: "a \<in> ?R" "b \<in> ?R" "a \<noteq> b"
    hence neq: "f a \<noteq> f b" using f[unfolded inj_on_def, rule_format] by blast
    from asm have "f a \<in> r" "f b \<in> r" using f by auto
    thus "f a \<inter> f b = {}" using d[of "f a" "f b"] f using neq by auto
  qed
  have "(\<Union> r) = (\<Union> i \<in> ?R. f i)"
    using f by auto
  hence "\<mu> (\<Union> r)= \<mu> (\<Union> i \<in> ?R. f i)" by simp
  also have "\<dots> = (\<Sum> i \<in> ?R. \<mu> (f i))"
    using measure_finitely_additive'[OF f_into_sets disj] by simp
  also have "\<dots> = (\<Sum> a \<in> r. \<mu> a)"
    using f[rule_format] setsum_reindex[of f ?R "\<lambda> a. \<mu> a"] by auto
  finally show ?thesis by simp
qed

lemma (in measure_space) measure_finitely_additive'':
  assumes "finite s"
  assumes "\<And> i. i \<in> s \<Longrightarrow> a i \<in> sets M"
  assumes d: "disjoint_family_on a s"
  shows "(\<Sum> i \<in> s. \<mu> (a i)) = \<mu> (\<Union> i \<in> s. a i)"
using assms
proof -
  (* counting the elements in s is enough *)
  let ?R = "{..< card s}"
  obtain f where f: "f ` ?R = s" "inj_on f ?R"
    using ex_bij_betw_nat_finite[unfolded bij_betw_def, OF `finite s`]
    unfolding atLeast0LessThan by auto
  hence f_into_sets: "a \<circ> f \<in> ?R \<rightarrow> sets M" using assms unfolding o_def by auto
  have disj: "\<And> i j. \<lbrakk>i \<in> ?R ; j \<in> ?R ; i \<noteq> j\<rbrakk> \<Longrightarrow> (a \<circ> f) i \<inter> (a \<circ> f) j = {}"
  proof -
    fix i j assume asm: "i \<in> ?R" "j \<in> ?R" "i \<noteq> j"
    hence neq: "f i \<noteq> f j" using f[unfolded inj_on_def, rule_format] by blast
    from asm have "f i \<in> s" "f j \<in> s" using f by auto
    thus "(a \<circ> f) i \<inter> (a \<circ> f) j = {}"
      using d f neq unfolding disjoint_family_on_def by auto
  qed
  have "(\<Union> i \<in> s. a i) = (\<Union> i \<in> f ` ?R. a i)" using f by auto
  hence "(\<Union> i \<in> s. a i) = (\<Union> i \<in> ?R. a (f i))" by auto
  hence "\<mu> (\<Union> i \<in> s. a i) = (\<Sum> i \<in> ?R. \<mu> (a (f i)))"
    using measure_finitely_additive'[OF f_into_sets disj] by simp
  also have "\<dots> = (\<Sum> i \<in> s. \<mu> (a i))"
    using f[rule_format] setsum_reindex[of f ?R "\<lambda> i. \<mu> (a i)"] by auto
  finally show ?thesis by simp
qed

lemma finite_additivity_sufficient:
  assumes "sigma_algebra M"
  assumes fin: "finite (space M)" and pos: "positive M (measure M)" and add: "additive M (measure M)"
  shows "measure_space M"
proof -
  interpret sigma_algebra M by fact
  show ?thesis
  proof
    show [simp]: "measure M {} = 0" using pos by (simp add: positive_def)
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
      then have "\<forall>m\<ge>N. measure M (A m) = 0" by simp
      then have "(\<Sum>\<^isub>\<infinity> n. measure M (A n)) = setsum (\<lambda>m. measure M (A m)) {..<N}"
        by (simp add: psuminf_finite)
      also have "... = measure M (\<Union>i<N. A i)"
        proof (induct N)
          case 0 thus ?case by simp
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
      finally show "(\<Sum>\<^isub>\<infinity> n. measure M (A n)) = measure M (\<Union>i. A i)" .
    qed
  qed
qed

lemma (in measure_space) measure_setsum_split:
  assumes "finite r" and "a \<in> sets M" and br_in_M: "b ` r \<subseteq> sets M"
  assumes "(\<Union>i \<in> r. b i) = space M"
  assumes "disjoint_family_on b r"
  shows "\<mu> a = (\<Sum> i \<in> r. \<mu> (a \<inter> (b i)))"
proof -
  have *: "\<mu> a = \<mu> (\<Union>i \<in> r. a \<inter> b i)"
    using assms by auto
  show ?thesis unfolding *
  proof (rule measure_finitely_additive''[symmetric])
    show "finite r" using `finite r` by auto
    { fix i assume "i \<in> r"
      hence "b i \<in> sets M" using br_in_M by auto
      thus "a \<inter> b i \<in> sets M" using `a \<in> sets M` by auto
    }
    show "disjoint_family_on (\<lambda>i. a \<inter> b i) r"
      using `disjoint_family_on b r`
      unfolding disjoint_family_on_def by auto
  qed
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

lemma (in measure_space) measure_eq_0:
  assumes "N \<in> sets M" and "\<mu> N = 0" and "K \<subseteq> N" and "K \<in> sets M"
  shows "\<mu> K = 0"
using measure_mono[OF assms(3,4,1)] assms(2) by auto

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
  shows "\<mu> (\<Union>i. f i) \<le> (\<Sum>\<^isub>\<infinity> i. \<mu> (f i))"
proof -
  have "\<mu> (\<Union>i. f i) = \<mu> (\<Union>i. disjointed f i)"
    unfolding UN_disjointed_eq ..
  also have "\<dots> = (\<Sum>\<^isub>\<infinity> i. \<mu> (disjointed f i))"
    using range_disjointed_sets[OF assms] measure_countably_additive
    by (simp add:  disjoint_family_disjointed comp_def)
  also have "\<dots> \<le> (\<Sum>\<^isub>\<infinity> i. \<mu> (f i))"
  proof (rule psuminf_le, rule measure_mono)
    fix i show "disjointed f i \<subseteq> f i" by (rule disjointed_subset)
    show "f i \<in> sets M" "disjointed f i \<in> sets M"
      using assms range_disjointed_sets[OF assms] by auto
  qed
  finally show ?thesis .
qed

lemma (in measure_space) measure_UN_eq_0:
  assumes "\<And> i :: nat. \<mu> (N i) = 0" and "range N \<subseteq> sets M"
  shows "\<mu> (\<Union> i. N i) = 0"
using measure_countably_subadditive[OF assms(2)] assms(1) by auto

lemma (in measure_space) measure_inter_full_set:
  assumes "S \<in> sets M" "T \<in> sets M" and not_\<omega>: "\<mu> (T - S) \<noteq> \<omega>"
  assumes T: "\<mu> T = \<mu> (space M)"
  shows "\<mu> (S \<inter> T) = \<mu> S"
proof (rule antisym)
  show " \<mu> (S \<inter> T) \<le> \<mu> S"
    using assms by (auto intro!: measure_mono)

  show "\<mu> S \<le> \<mu> (S \<inter> T)"
  proof (rule ccontr)
    assume contr: "\<not> ?thesis"
    have "\<mu> (space M) = \<mu> ((T - S) \<union> (S \<inter> T))"
      unfolding T[symmetric] by (auto intro!: arg_cong[where f="\<mu>"])
    also have "\<dots> \<le> \<mu> (T - S) + \<mu> (S \<inter> T)"
      using assms by (auto intro!: measure_subadditive)
    also have "\<dots> < \<mu> (T - S) + \<mu> S"
      by (rule pextreal_less_add[OF not_\<omega>]) (insert contr, auto)
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
  and A: "range A \<subseteq> sets E" "A \<up> space E"
  and M: "measure_space \<lparr>space = space E, sets = sets (sigma E), measure = \<mu>\<rparr>" (is "measure_space ?M")
  and N: "measure_space \<lparr>space = space E, sets = sets (sigma E), measure = \<nu>\<rparr>" (is "measure_space ?N")
  and eq: "\<And>X. X \<in> sets E \<Longrightarrow> \<mu> X = \<nu> X"
  and finite: "\<And>i. \<mu> (A i) \<noteq> \<omega>"
  assumes "X \<in> sets (sigma E)"
  shows "\<mu> X = \<nu> X"
proof -
  let "?D F" = "{D. D \<in> sets (sigma E) \<and> \<mu> (F \<inter> D) = \<nu> (F \<inter> D)}"
  interpret M: measure_space ?M
    where "space ?M = space E" and "sets ?M = sets (sigma E)" and "measure ?M = \<mu>" by (simp_all add: M)
  interpret N: measure_space ?N
    where "space ?N = space E" and "sets ?N = sets (sigma E)" and "measure ?N = \<nu>" by (simp_all add: N)
  { fix F assume "F \<in> sets E" and "\<mu> F \<noteq> \<omega>"
    then have [intro]: "F \<in> sets (sigma E)" by auto
    have "\<nu> F \<noteq> \<omega>" using `\<mu> F \<noteq> \<omega>` `F \<in> sets E` eq by simp
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
      then have "\<nu> (F \<inter> A) \<noteq> \<omega>" using `\<nu> F \<noteq> \<omega>` by auto
      have "\<mu> (F \<inter> A) \<le> \<mu> F" by (auto intro!: M.measure_mono)
      then have "\<mu> (F \<inter> A) \<noteq> \<omega>" using `\<mu> F \<noteq> \<omega>` by auto
      then have "\<mu> (F \<inter> (space (sigma E) - A)) = \<mu> F - \<mu> (F \<inter> A)" unfolding **
        using `F \<inter> A \<in> sets (sigma E)` by (auto intro!: M.measure_Diff)
      also have "\<dots> = \<nu> F - \<nu> (F \<inter> A)" using eq `F \<in> sets E` * by simp
      also have "\<dots> = \<nu> (F \<inter> (space (sigma E) - A))" unfolding **
        using `F \<inter> A \<in> sets (sigma E)` `\<nu> (F \<inter> A) \<noteq> \<omega>` by (auto intro!: N.measure_Diff[symmetric])
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
  { fix i have "\<mu> (A i \<inter> X) = \<nu> (A i \<inter> X)"
      using *[of "A i" X] `X \<in> sets (sigma E)` A finite by auto }
  moreover
  have "(\<lambda>i. A i \<inter> X) \<up> X"
    using `X \<in> sets (sigma E)` M.sets_into_space A
    by (auto simp: isoton_def)
  then have "(\<lambda>i. \<mu> (A i \<inter> X)) \<up> \<mu> X" "(\<lambda>i. \<nu> (A i \<inter> X)) \<up> \<nu> X"
    using `X \<in> sets (sigma E)` A by (auto intro!: M.measure_up N.measure_up M.Int simp: subset_eq)
  ultimately show ?thesis by (simp add: isoton_def)
qed

section "@{text \<mu>}-null sets"

abbreviation (in measure_space) "null_sets \<equiv> {N\<in>sets M. \<mu> N = 0}"

lemma (in measure_space) null_sets_Un[intro]:
  assumes "N \<in> null_sets" "N' \<in> null_sets"
  shows "N \<union> N' \<in> null_sets"
proof (intro conjI CollectI)
  show "N \<union> N' \<in> sets M" using assms by auto
  have "\<mu> (N \<union> N') \<le> \<mu> N + \<mu> N'"
    using assms by (intro measure_subadditive) auto
  then show "\<mu> (N \<union> N') = 0"
    using assms by auto
qed

lemma UN_from_nat: "(\<Union>i. N i) = (\<Union>i. N (Countable.from_nat i))"
proof -
  have "(\<Union>i. N i) = (\<Union>i. (N \<circ> Countable.from_nat) i)"
    unfolding SUPR_def image_compose
    unfolding surj_from_nat ..
  then show ?thesis by simp
qed

lemma (in measure_space) null_sets_UN[intro]:
  assumes "\<And>i::'i::countable. N i \<in> null_sets"
  shows "(\<Union>i. N i) \<in> null_sets"
proof (intro conjI CollectI)
  show "(\<Union>i. N i) \<in> sets M" using assms by auto
  have "\<mu> (\<Union>i. N i) \<le> (\<Sum>\<^isub>\<infinity> n. \<mu> (N (Countable.from_nat n)))"
    unfolding UN_from_nat[of N]
    using assms by (intro measure_countably_subadditive) auto
  then show "\<mu> (\<Union>i. N i) = 0"
    using assms by auto
qed

lemma (in measure_space) null_sets_finite_UN:
  assumes "finite S" "\<And>i. i \<in> S \<Longrightarrow> A i \<in> null_sets"
  shows "(\<Union>i\<in>S. A i) \<in> null_sets"
proof (intro CollectI conjI)
  show "(\<Union>i\<in>S. A i) \<in> sets M" using assms by (intro finite_UN) auto
  have "\<mu> (\<Union>i\<in>S. A i) \<le> (\<Sum>i\<in>S. \<mu> (A i))"
    using assms by (intro measure_finitely_subadditive) auto
  then show "\<mu> (\<Union>i\<in>S. A i) = 0"
    using assms by auto
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

lemma (in measure_space) AE_I':
  "N \<in> null_sets \<Longrightarrow> {x\<in>space M. \<not> P x} \<subseteq> N \<Longrightarrow> (AE x. P x)"
  unfolding almost_everywhere_def by auto

lemma (in measure_space) AE_iff_null_set:
  assumes "{x\<in>space M. \<not> P x} \<in> sets M" (is "?P \<in> sets M")
  shows "(AE x. P x) \<longleftrightarrow> {x\<in>space M. \<not> P x} \<in> null_sets"
proof
  assume "AE x. P x" then obtain N where N: "N \<in> sets M" "?P \<subseteq> N" "\<mu> N = 0"
    unfolding almost_everywhere_def by auto
  moreover have "\<mu> ?P \<le> \<mu> N"
    using assms N(1,2) by (auto intro: measure_mono)
  ultimately show "?P \<in> null_sets" using assms by auto
next
  assume "?P \<in> null_sets" with assms show "AE x. P x" by (auto intro: AE_I')
qed

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
  obtain A where A: "?P \<subseteq> A" "A \<in> sets M" "\<mu> A = 0"
    using assms by (auto elim!: AE_E)
  have "?P = space M - {x\<in>space M. P x}" by auto
  then have "?P \<in> sets M" using assms by auto
  with assms `?P \<subseteq> A` `A \<in> sets M` have "\<mu> ?P \<le> \<mu> A"
    by (auto intro!: measure_mono)
  then show "\<mu> ?P = 0" using A by simp
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
    show "A \<union> B \<in> sets M" "\<mu> (A \<union> B) = 0" using A B
      using measure_subadditive[of A B] by auto
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

lemma (in measure_space) all_AE_countable:
  "(\<forall>i::'i::countable. AE x. P i x) \<longleftrightarrow> (AE x. \<forall>i. P i x)"
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

lemma (in measure_space) restricted_measure_space:
  assumes "S \<in> sets M"
  shows "measure_space (restricted_space S)"
    (is "measure_space ?r")
  unfolding measure_space_def measure_space_axioms_def
proof safe
  show "sigma_algebra ?r" using restricted_sigma_algebra[OF assms] .
  show "measure ?r {} = 0" by simp

  show "countably_additive ?r (measure ?r)"
    unfolding countably_additive_def
  proof safe
    fix A :: "nat \<Rightarrow> 'a set"
    assume *: "range A \<subseteq> sets ?r" and **: "disjoint_family A"
    from restriction_in_sets[OF assms *[simplified]] **
    show "(\<Sum>\<^isub>\<infinity> n. measure ?r (A n)) = measure ?r (\<Union>i. A i)"
      using measure_countably_additive by simp
  qed
qed

lemma (in measure_space) measure_space_vimage:
  fixes M' :: "('c, 'd) measure_space_scheme"
  assumes T: "sigma_algebra M'" "T \<in> measurable M M'"
    and \<nu>: "\<And>A. A \<in> sets M' \<Longrightarrow> measure M' A = \<mu> (T -` A \<inter> space M)"
  shows "measure_space M'"
proof -
  interpret M': sigma_algebra M' by fact
  show ?thesis
  proof
    show "measure M' {} = 0" using \<nu>[of "{}"] by simp

    show "countably_additive M' (measure M')"
    proof (intro countably_additiveI)
      fix A :: "nat \<Rightarrow> 'c set" assume "range A \<subseteq> sets M'" "disjoint_family A"
      then have A: "\<And>i. A i \<in> sets M'" "(\<Union>i. A i) \<in> sets M'" by auto
      then have *: "range (\<lambda>i. T -` (A i) \<inter> space M) \<subseteq> sets M"
        using `T \<in> measurable M M'` by (auto simp: measurable_def)
      moreover have "(\<Union>i. T -`  A i \<inter> space M) \<in> sets M"
        using * by blast
      moreover have **: "disjoint_family (\<lambda>i. T -` A i \<inter> space M)"
        using `disjoint_family A` by (auto simp: disjoint_family_on_def)
      ultimately show "(\<Sum>\<^isub>\<infinity> i. measure M' (A i)) = measure M' (\<Union>i. A i)"
        using measure_countably_additive[OF _ **] A
        by (auto simp: comp_def vimage_UN \<nu>)
    qed
  qed
qed

lemma (in measure_space) measure_space_subalgebra:
  assumes "sigma_algebra N" and [simp]: "sets N \<subseteq> sets M" "space N = space M"
  and measure[simp]: "\<And>X. X \<in> sets N \<Longrightarrow> measure N X = measure M X"
  shows "measure_space N"
proof -
  interpret N: sigma_algebra N by fact
  show ?thesis
  proof
    from `sets N \<subseteq> sets M` have "\<And>A. range A \<subseteq> sets N \<Longrightarrow> range A \<subseteq> sets M" by blast
    then show "countably_additive N (measure N)"
      by (auto intro!: measure_countably_additive simp: countably_additive_def subset_eq)
  qed simp
qed

section "@{text \<sigma>}-finite Measures"

locale sigma_finite_measure = measure_space +
  assumes sigma_finite: "\<exists>A::nat \<Rightarrow> 'a set. range A \<subseteq> sets M \<and> (\<Union>i. A i) = space M \<and> (\<forall>i. \<mu> (A i) \<noteq> \<omega>)"

lemma (in sigma_finite_measure) restricted_sigma_finite_measure:
  assumes "S \<in> sets M"
  shows "sigma_finite_measure (restricted_space S)"
    (is "sigma_finite_measure ?r")
  unfolding sigma_finite_measure_def sigma_finite_measure_axioms_def
proof safe
  show "measure_space ?r" using restricted_measure_space[OF assms] .
next
  obtain A :: "nat \<Rightarrow> 'a set" where
      "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" "\<And>i. \<mu> (A i) \<noteq> \<omega>"
    using sigma_finite by auto
  show "\<exists>A::nat \<Rightarrow> 'a set. range A \<subseteq> sets ?r \<and> (\<Union>i. A i) = space ?r \<and> (\<forall>i. measure ?r (A i) \<noteq> \<omega>)"
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
    also have "\<dots> < \<omega>" using `\<mu> (A i) \<noteq> \<omega>` by (auto simp: pextreal_less_\<omega>)
    finally show "measure ?r (A i \<inter> S) \<noteq> \<omega>" by (auto simp: pextreal_less_\<omega>)
  qed
qed

lemma (in sigma_finite_measure) sigma_finite_measure_cong:
  assumes cong: "\<And>A. A \<in> sets M \<Longrightarrow> measure M' A = \<mu> A" "sets M' = sets M" "space M' = space M"
  shows "sigma_finite_measure M'"
proof -
  interpret M': measure_space M' by (intro measure_space_cong cong)
  from sigma_finite guess A .. note A = this
  then have "\<And>i. A i \<in> sets M" by auto
  with A have fin: "(\<forall>i. measure M' (A i) \<noteq> \<omega>)" using cong by auto
  show ?thesis
    apply default
    using A fin cong by auto
qed

lemma (in sigma_finite_measure) disjoint_sigma_finite:
  "\<exists>A::nat\<Rightarrow>'a set. range A \<subseteq> sets M \<and> (\<Union>i. A i) = space M \<and>
    (\<forall>i. \<mu> (A i) \<noteq> \<omega>) \<and> disjoint_family A"
proof -
  obtain A :: "nat \<Rightarrow> 'a set" where
    range: "range A \<subseteq> sets M" and
    space: "(\<Union>i. A i) = space M" and
    measure: "\<And>i. \<mu> (A i) \<noteq> \<omega>"
    using sigma_finite by auto
  note range' = range_disjointed_sets[OF range] range
  { fix i
    have "\<mu> (disjointed A i) \<le> \<mu> (A i)"
      using range' disjointed_subset[of A i] by (auto intro!: measure_mono)
    then have "\<mu> (disjointed A i) \<noteq> \<omega>"
      using measure[of i] by auto }
  with disjoint_family_disjointed UN_disjointed_eq[of A] space range'
  show ?thesis by (auto intro!: exI[of _ "disjointed A"])
qed

lemma (in sigma_finite_measure) sigma_finite_up:
  "\<exists>F. range F \<subseteq> sets M \<and> F \<up> space M \<and> (\<forall>i. \<mu> (F i) \<noteq> \<omega>)"
proof -
  obtain F :: "nat \<Rightarrow> 'a set" where
    F: "range F \<subseteq> sets M" "(\<Union>i. F i) = space M" "\<And>i. \<mu> (F i) \<noteq> \<omega>"
    using sigma_finite by auto
  then show ?thesis unfolding isoton_def
  proof (intro exI[of _ "\<lambda>n. \<Union>i\<le>n. F i"] conjI allI)
    from F have "\<And>x. x \<in> space M \<Longrightarrow> \<exists>i. x \<in> F i" by auto
    then show "(\<Union>n. \<Union> i\<le>n. F i) = space M"
      using F by fastsimp
  next
    fix n
    have "\<mu> (\<Union> i\<le>n. F i) \<le> (\<Sum>i\<le>n. \<mu> (F i))" using F
      by (auto intro!: measure_finitely_subadditive)
    also have "\<dots> < \<omega>"
      using F by (auto simp: setsum_\<omega>)
    finally show "\<mu> (\<Union> i\<le>n. F i) \<noteq> \<omega>" by simp
  qed force+
qed

section "Real measure values"

lemma (in measure_space) real_measure_Union:
  assumes finite: "\<mu> A \<noteq> \<omega>" "\<mu> B \<noteq> \<omega>"
  and measurable: "A \<in> sets M" "B \<in> sets M" "A \<inter> B = {}"
  shows "real (\<mu> (A \<union> B)) = real (\<mu> A) + real (\<mu> B)"
  unfolding measure_additive[symmetric, OF measurable]
  using finite by (auto simp: real_of_pextreal_add)

lemma (in measure_space) real_measure_finite_Union:
  assumes measurable:
    "finite S" "\<And>i. i \<in> S \<Longrightarrow> A i \<in> sets M" "disjoint_family_on A S"
  assumes finite: "\<And>i. i \<in> S \<Longrightarrow> \<mu> (A i) \<noteq> \<omega>"
  shows "real (\<mu> (\<Union>i\<in>S. A i)) = (\<Sum>i\<in>S. real (\<mu> (A i)))"
  using real_of_pextreal_setsum[of S, OF finite]
        measure_finitely_additive''[symmetric, OF measurable]
  by simp

lemma (in measure_space) real_measure_Diff:
  assumes finite: "\<mu> A \<noteq> \<omega>"
  and measurable: "A \<in> sets M" "B \<in> sets M" "B \<subseteq> A"
  shows "real (\<mu> (A - B)) = real (\<mu> A) - real (\<mu> B)"
proof -
  have "\<mu> (A - B) \<le> \<mu> A"
    "\<mu> B \<le> \<mu> A"
    using measurable by (auto intro!: measure_mono)
  hence "real (\<mu> ((A - B) \<union> B)) = real (\<mu> (A - B)) + real (\<mu> B)"
    using measurable finite by (rule_tac real_measure_Union) auto
  thus ?thesis using `B \<subseteq> A` by (auto simp: Un_absorb2)
qed

lemma (in measure_space) real_measure_UNION:
  assumes measurable: "range A \<subseteq> sets M" "disjoint_family A"
  assumes finite: "\<mu> (\<Union>i. A i) \<noteq> \<omega>"
  shows "(\<lambda>i. real (\<mu> (A i))) sums (real (\<mu> (\<Union>i. A i)))"
proof -
  have *: "(\<Sum>\<^isub>\<infinity> i. \<mu> (A i)) = \<mu> (\<Union>i. A i)"
    using measure_countably_additive[OF measurable] by (simp add: comp_def)
  hence "(\<Sum>\<^isub>\<infinity> i. \<mu> (A i)) \<noteq> \<omega>" using finite by simp
  from psuminf_imp_suminf[OF this]
  show ?thesis using * by simp
qed

lemma (in measure_space) real_measure_subadditive:
  assumes measurable: "A \<in> sets M" "B \<in> sets M"
  and fin: "\<mu> A \<noteq> \<omega>" "\<mu> B \<noteq> \<omega>"
  shows "real (\<mu> (A \<union> B)) \<le> real (\<mu> A) + real (\<mu> B)"
proof -
  have "real (\<mu> (A \<union> B)) \<le> real (\<mu> A + \<mu> B)"
    using measure_subadditive[OF measurable] fin by (auto intro!: real_of_pextreal_mono)
  also have "\<dots> = real (\<mu> A) + real (\<mu> B)"
    using fin by (simp add: real_of_pextreal_add)
  finally show ?thesis .
qed

lemma (in measure_space) real_measure_countably_subadditive:
  assumes "range f \<subseteq> sets M" and "(\<Sum>\<^isub>\<infinity> i. \<mu> (f i)) \<noteq> \<omega>"
  shows "real (\<mu> (\<Union>i. f i)) \<le> (\<Sum> i. real (\<mu> (f i)))"
proof -
  have "real (\<mu> (\<Union>i. f i)) \<le> real (\<Sum>\<^isub>\<infinity> i. \<mu> (f i))"
    using assms by (auto intro!: real_of_pextreal_mono measure_countably_subadditive)
  also have "\<dots> = (\<Sum> i. real (\<mu> (f i)))"
    using assms by (auto intro!: sums_unique psuminf_imp_suminf)
  finally show ?thesis .
qed

lemma (in measure_space) real_measure_setsum_singleton:
  assumes S: "finite S" "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  and fin: "\<And>x. x \<in> S \<Longrightarrow> \<mu> {x} \<noteq> \<omega>"
  shows "real (\<mu> S) = (\<Sum>x\<in>S. real (\<mu> {x}))"
  using measure_finite_singleton[OF S] fin by (simp add: real_of_pextreal_setsum)

lemma (in measure_space) real_continuity_from_below:
  assumes A: "range A \<subseteq> sets M" "\<And>i. A i \<subseteq> A (Suc i)" and "\<mu> (\<Union>i. A i) \<noteq> \<omega>"
  shows "(\<lambda>i. real (\<mu> (A i))) ----> real (\<mu> (\<Union>i. A i))"
proof (rule SUP_eq_LIMSEQ[THEN iffD1])
  { fix n have "\<mu> (A n) \<le> \<mu> (\<Union>i. A i)"
      using A by (auto intro!: measure_mono)
    hence "\<mu> (A n) \<noteq> \<omega>" using assms by auto }
  note this[simp]

  show "mono (\<lambda>i. real (\<mu> (A i)))" unfolding mono_iff_le_Suc using A
    by (auto intro!: real_of_pextreal_mono measure_mono)

  show "(SUP n. Real (real (\<mu> (A n)))) = Real (real (\<mu> (\<Union>i. A i)))"
    using continuity_from_below[OF A(1), OF A(2)]
    using assms by (simp add: Real_real)
qed simp_all

lemma (in measure_space) real_continuity_from_above:
  assumes A: "range A \<subseteq> sets M"
  and mono_Suc: "\<And>n.  A (Suc n) \<subseteq> A n"
  and finite: "\<And>i. \<mu> (A i) \<noteq> \<omega>"
  shows "(\<lambda>n. real (\<mu> (A n))) ----> real (\<mu> (\<Inter>i. A i))"
proof (rule INF_eq_LIMSEQ[THEN iffD1])
  { fix n have "\<mu> (\<Inter>i. A i) \<le> \<mu> (A n)"
      using A by (auto intro!: measure_mono)
    hence "\<mu> (\<Inter>i. A i) \<noteq> \<omega>" using assms by auto }
  note this[simp]

  show "mono (\<lambda>i. - real (\<mu> (A i)))" unfolding mono_iff_le_Suc using assms
    by (auto intro!: real_of_pextreal_mono measure_mono)

  show "(INF n. Real (real (\<mu> (A n)))) =
    Real (real (\<mu> (\<Inter>i. A i)))"
    using continuity_from_above[OF A, OF mono_Suc finite]
    using assms by (simp add: Real_real)
qed simp_all

locale finite_measure = measure_space +
  assumes finite_measure_of_space: "\<mu> (space M) \<noteq> \<omega>"

sublocale finite_measure < sigma_finite_measure
proof
  show "\<exists>A. range A \<subseteq> sets M \<and> (\<Union>i. A i) = space M \<and> (\<forall>i. \<mu> (A i) \<noteq> \<omega>)"
    using finite_measure_of_space by (auto intro!: exI[of _ "\<lambda>x. space M"])
qed

lemma (in finite_measure) finite_measure[simp, intro]:
  assumes "A \<in> sets M"
  shows "\<mu> A \<noteq> \<omega>"
proof -
  from `A \<in> sets M` have "A \<subseteq> space M"
    using sets_into_space by blast
  hence "\<mu> A \<le> \<mu> (space M)"
    using assms top by (rule measure_mono)
  also have "\<dots> < \<omega>"
    using finite_measure_of_space unfolding pextreal_less_\<omega> .
  finally show ?thesis unfolding pextreal_less_\<omega> .
qed

lemma (in finite_measure) restricted_finite_measure:
  assumes "S \<in> sets M"
  shows "finite_measure (restricted_space S)"
    (is "finite_measure ?r")
  unfolding finite_measure_def finite_measure_axioms_def
proof (safe del: notI)
  show "measure_space ?r" using restricted_measure_space[OF assms] .
next
  show "measure ?r (space ?r) \<noteq> \<omega>" using finite_measure[OF `S \<in> sets M`] by auto
qed

lemma (in measure_space) restricted_to_finite_measure:
  assumes "S \<in> sets M" "\<mu> S \<noteq> \<omega>"
  shows "finite_measure (restricted_space S)"
proof -
  have "measure_space (restricted_space S)"
    using `S \<in> sets M` by (rule restricted_measure_space)
  then show ?thesis
    unfolding finite_measure_def finite_measure_axioms_def
    using assms by auto
qed

lemma (in finite_measure) real_finite_measure_Diff:
  assumes "A \<in> sets M" "B \<in> sets M" "B \<subseteq> A"
  shows "real (\<mu> (A - B)) = real (\<mu> A) - real (\<mu> B)"
  using finite_measure[OF `A \<in> sets M`] by (rule real_measure_Diff[OF _ assms])

lemma (in finite_measure) real_finite_measure_Union:
  assumes sets: "A \<in> sets M" "B \<in> sets M" and "A \<inter> B = {}"
  shows "real (\<mu> (A \<union> B)) = real (\<mu> A) + real (\<mu> B)"
  using sets by (auto intro!: real_measure_Union[OF _ _ assms] finite_measure)

lemma (in finite_measure) real_finite_measure_finite_Union:
  assumes "finite S" and dis: "disjoint_family_on A S"
  and *: "\<And>i. i \<in> S \<Longrightarrow> A i \<in> sets M"
  shows "real (\<mu> (\<Union>i\<in>S. A i)) = (\<Sum>i\<in>S. real (\<mu> (A i)))"
proof (rule real_measure_finite_Union[OF `finite S` _ dis])
  fix i assume "i \<in> S" from *[OF this] show "A i \<in> sets M" .
  from finite_measure[OF this] show "\<mu> (A i) \<noteq> \<omega>" .
qed

lemma (in finite_measure) real_finite_measure_UNION:
  assumes measurable: "range A \<subseteq> sets M" "disjoint_family A"
  shows "(\<lambda>i. real (\<mu> (A i))) sums (real (\<mu> (\<Union>i. A i)))"
proof (rule real_measure_UNION[OF assms])
  have "(\<Union>i. A i) \<in> sets M" using measurable(1) by (rule countable_UN)
  thus "\<mu> (\<Union>i. A i) \<noteq> \<omega>" by (rule finite_measure)
qed

lemma (in finite_measure) real_measure_mono:
  "A \<in> sets M \<Longrightarrow> B \<in> sets M \<Longrightarrow> A \<subseteq> B \<Longrightarrow> real (\<mu> A) \<le> real (\<mu> B)"
  by (auto intro!: measure_mono real_of_pextreal_mono finite_measure)

lemma (in finite_measure) real_finite_measure_subadditive:
  assumes measurable: "A \<in> sets M" "B \<in> sets M"
  shows "real (\<mu> (A \<union> B)) \<le> real (\<mu> A) + real (\<mu> B)"
  using measurable measurable[THEN finite_measure] by (rule real_measure_subadditive)

lemma (in finite_measure) real_finite_measure_countably_subadditive:
  assumes "range f \<subseteq> sets M" and "summable (\<lambda>i. real (\<mu> (f i)))"
  shows "real (\<mu> (\<Union>i. f i)) \<le> (\<Sum> i. real (\<mu> (f i)))"
proof (rule real_measure_countably_subadditive[OF assms(1)])
  have *: "\<And>i. f i \<in> sets M" using assms by auto
  have "(\<lambda>i. real (\<mu> (f i))) sums (\<Sum>i. real (\<mu> (f i)))"
    using assms(2) by (rule summable_sums)
  from suminf_imp_psuminf[OF this]
  have "(\<Sum>\<^isub>\<infinity>i. \<mu> (f i)) = Real (\<Sum>i. real (\<mu> (f i)))"
    using * by (simp add: Real_real finite_measure)
  thus "(\<Sum>\<^isub>\<infinity>i. \<mu> (f i)) \<noteq> \<omega>" by simp
qed

lemma (in finite_measure) real_finite_measure_finite_singelton:
  assumes "finite S" and *: "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  shows "real (\<mu> S) = (\<Sum>x\<in>S. real (\<mu> {x}))"
proof (rule real_measure_setsum_singleton[OF `finite S`])
  fix x assume "x \<in> S" thus "{x} \<in> sets M" by (rule *)
  with finite_measure show "\<mu> {x} \<noteq> \<omega>" .
qed

lemma (in finite_measure) real_finite_continuity_from_below:
  assumes "range A \<subseteq> sets M" "\<And>i. A i \<subseteq> A (Suc i)"
  shows "(\<lambda>i. real (\<mu> (A i))) ----> real (\<mu> (\<Union>i. A i))"
  using real_continuity_from_below[OF assms(1), OF assms(2) finite_measure] assms by auto

lemma (in finite_measure) real_finite_continuity_from_above:
  assumes A: "range A \<subseteq> sets M"
  and mono_Suc: "\<And>n.  A (Suc n) \<subseteq> A n"
  shows "(\<lambda>n. real (\<mu> (A n))) ----> real (\<mu> (\<Inter>i. A i))"
  using real_continuity_from_above[OF A, OF mono_Suc finite_measure] A
  by auto

lemma (in finite_measure) real_finite_measure_finite_Union':
  assumes "finite S" "A`S \<subseteq> sets M" "disjoint_family_on A S"
  shows "real (\<mu> (\<Union>i\<in>S. A i)) = (\<Sum>i\<in>S. real (\<mu> (A i)))"
  using assms real_finite_measure_finite_Union[of S A] by auto

lemma (in finite_measure) finite_measure_compl:
  assumes s: "s \<in> sets M"
  shows "\<mu> (space M - s) = \<mu> (space M) - \<mu> s"
  using measure_compl[OF s, OF finite_measure, OF s] .

lemma (in finite_measure) finite_measure_inter_full_set:
  assumes "S \<in> sets M" "T \<in> sets M"
  assumes T: "\<mu> T = \<mu> (space M)"
  shows "\<mu> (S \<inter> T) = \<mu> S"
  using measure_inter_full_set[OF assms(1,2) finite_measure assms(3)] assms
  by auto

section {* Measure preserving *}

definition "measure_preserving A B =
    {f \<in> measurable A B. (\<forall>y \<in> sets B. measure A (f -` y \<inter> space A) = measure B y)}"

lemma (in finite_measure) measure_preserving_lift:
  fixes f :: "'a \<Rightarrow> 'c" and A :: "('c, 'd) measure_space_scheme"
  assumes "algebra A" "finite_measure (sigma A)" (is "finite_measure ?sA")
  assumes fmp: "f \<in> measure_preserving M A"
  shows "f \<in> measure_preserving M (sigma A)"
proof -
  interpret sA: finite_measure ?sA by fact
  interpret A: algebra A by fact
  show ?thesis using fmp
  proof (clarsimp simp add: measure_preserving_def)
    assume fm: "f \<in> measurable M A"
       and "\<forall>y\<in>sets A. \<mu> (f -` y \<inter> space M) = measure A y"
    then have meq: "\<forall>y\<in>sets A. \<mu> (f -` y \<inter> space M) = sA.\<mu> y"
      by simp
    have f12: "f \<in> measurable M ?sA"
      using measurable_subset[OF A.sets_into_space] fm by auto
    hence ffn: "f \<in> space M \<rightarrow> space A"
      by (simp add: measurable_def)
    have "space M \<subseteq> f -` (space A)"
      by auto (metis PiE ffn)
    hence fveq [simp]: "(f -` (space A)) \<inter> space M = space M"
      by blast
    {
      fix y
      assume y: "y \<in> sets ?sA"
      have "sets ?sA = sigma_sets (space A) (sets A)" (is "_ = ?A") by (auto simp: sigma_def)
      also have "\<dots> \<subseteq> {s . \<mu> ((f -` s) \<inter> space M) = sA.\<mu> s}"
      proof (rule A.sigma_property_disjoint, safe)
        fix x assume "x \<in> sets A" then show "\<mu> (f -` x \<inter> space M) = sA.\<mu> x" by (simp add: meq)
      next
        fix s
        assume eq: "\<mu> (f -` s \<inter> space M) = sA.\<mu> s" and s: "s \<in> ?A"
        then have s': "s \<in> sets ?sA" by (simp add: sigma_def)
        show "\<mu> (f -` (space A - s) \<inter> space M) = measure ?sA (space A - s)"
          using sA.finite_measure_compl[OF s']
          using measurable_sets[OF f12 s'] meq[THEN bspec, OF A.top]
          by (simp add: vimage_Diff Diff_Int_distrib2 finite_measure_compl eq)
      next
        fix S
        assume S0: "S 0 = {}"
           and SSuc: "\<And>n.  S n \<subseteq> S (Suc n)"
           and rS1: "range S \<subseteq> {s. \<mu> (f -` s \<inter> space M) = sA.\<mu> s} \<inter> ?A"
        hence rS2: "range S \<subseteq> sets ?sA" by (simp add: sigma_def)
        have eq1: "\<And>i. \<mu> (f -` S i \<inter> space M) = sA.\<mu> (S i)"
          using rS1 by blast
        have *: "(\<lambda>n. sA.\<mu> (S n)) = (\<lambda>n. \<mu> (f -` S n \<inter> space M))"
          by (simp add: eq1)
        have "(SUP n. ... n) = \<mu> (\<Union>i. f -` S i \<inter> space M)"
        proof (rule measure_countable_increasing)
          show "range (\<lambda>i. f -` S i \<inter> space M) \<subseteq> sets M"
            using f12 rS2 by (auto simp add: measurable_def)
          show "f -` S 0 \<inter> space M = {}" using S0
            by blast
          show "\<And>n. f -` S n \<inter> space M \<subseteq> f -` S (Suc n) \<inter> space M"
            using SSuc by auto
        qed
        also have "\<mu> (\<Union>i. f -` S i \<inter> space M) = \<mu> (f -` (\<Union>i. S i) \<inter> space M)"
          by (simp add: vimage_UN)
        finally have "(SUP n. sA.\<mu> (S n)) = \<mu> (f -` (\<Union>i. S i) \<inter> space M)" unfolding * .
        moreover
        have "(SUP n. sA.\<mu> (S n)) = sA.\<mu> (\<Union>i. S i)"
          by (rule sA.measure_countable_increasing[OF rS2, OF S0 SSuc])
        ultimately
        show "\<mu> (f -` (\<Union>i. S i) \<inter> space M) = sA.\<mu> (\<Union>i. S i)" by simp
      next
        fix S :: "nat \<Rightarrow> 'c set"
        assume dS: "disjoint_family S"
           and rS1: "range S \<subseteq> {s. \<mu> (f -` s \<inter> space M) = sA.\<mu> s} \<inter> ?A"
        hence rS2: "range S \<subseteq> sets ?sA" by (simp add: sigma_def)
        have "\<And>i. \<mu> (f -` S i \<inter> space M) = sA.\<mu> (S i)"
          using rS1 by blast
        hence *: "(\<lambda>i. sA.\<mu> (S i)) = (\<lambda>n. \<mu> (f -` S n \<inter> space M))"
          by simp
        have "psuminf ... = \<mu> (\<Union>i. f -` S i \<inter> space M)"
          proof (rule measure_countably_additive)
            show "range (\<lambda>i. f -` S i \<inter> space M) \<subseteq> sets M"
              using f12 rS2 by (auto simp add: measurable_def)
            show "disjoint_family (\<lambda>i. f -` S i \<inter> space M)" using dS
              by (auto simp add: disjoint_family_on_def)
          qed
        hence "(\<Sum>\<^isub>\<infinity> i. sA.\<mu> (S i)) = \<mu> (\<Union>i. f -` S i \<inter> space M)" unfolding * .
        with sA.measure_countably_additive [OF rS2 dS]
        have "\<mu> (\<Union>i. f -` S i \<inter> space M) = sA.\<mu> (\<Union>i. S i)"
          by simp
        moreover have "\<mu> (f -` (\<Union>i. S i) \<inter> space M) = \<mu> (\<Union>i. f -` S i \<inter> space M)"
          by (simp add: vimage_UN)
        ultimately show "\<mu> (f -` (\<Union>i. S i) \<inter> space M) = sA.\<mu> (\<Union>i. S i)"
          by metis
      qed
      finally have "sets ?sA \<subseteq> {s . \<mu> ((f -` s) \<inter> space M) = sA.\<mu> s}" .
      hence "\<mu> (f -` y \<inter> space M) = sA.\<mu> y" using y by force
    }
    thus "f \<in> measurable M ?sA \<and> (\<forall>y\<in>sets ?sA. \<mu> (f -` y \<inter> space M) = measure A y)"
      by simp_all (blast intro: f12)
  qed
qed

section "Finite spaces"

locale finite_measure_space = measure_space + finite_sigma_algebra +
  assumes finite_single_measure[simp]: "\<And>x. x \<in> space M \<Longrightarrow> \<mu> {x} \<noteq> \<omega>"

lemma (in finite_measure_space) sum_over_space: "(\<Sum>x\<in>space M. \<mu> {x}) = \<mu> (space M)"
  using measure_finitely_additive''[of "space M" "\<lambda>i. {i}"]
  by (simp add: sets_eq_Pow disjoint_family_on_def finite_space)

lemma finite_measure_spaceI:
  assumes "finite (space M)" "sets M = Pow(space M)" and space: "measure M (space M) \<noteq> \<omega>"
    and add: "\<And>A B. A\<subseteq>space M \<Longrightarrow> B\<subseteq>space M \<Longrightarrow> A \<inter> B = {} \<Longrightarrow> measure M (A \<union> B) = measure M A + measure M B"
    and "measure M {} = 0"
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
    show "positive M (measure M)" unfolding positive_def by fact
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
    show "\<mu> {x} \<noteq> \<omega>" by (auto simp: insert_absorb[OF *] Diff_subset) }
qed

sublocale finite_measure_space \<subseteq> finite_measure
proof
  show "\<mu> (space M) \<noteq> \<omega>"
    unfolding sum_over_space[symmetric] setsum_\<omega>
    using finite_space finite_single_measure by auto
qed

lemma finite_measure_space_iff:
  "finite_measure_space M \<longleftrightarrow>
    finite (space M) \<and> sets M = Pow(space M) \<and> measure M (space M) \<noteq> \<omega> \<and> measure M {} = 0 \<and>
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

lemma psuminf_cmult_indicator:
  assumes "disjoint_family A" "x \<in> A i"
  shows "(\<Sum>\<^isub>\<infinity> n. f n * indicator (A n) x) = f i"
proof -
  have **: "\<And>n. f n * indicator (A n) x = (if n = i then f n else 0 :: pextreal)"
    using `x \<in> A i` assms unfolding disjoint_family_on_def indicator_def by auto
  then have "\<And>n. (\<Sum>j<n. f j * indicator (A j) x) = (if i < n then f i else 0 :: pextreal)"
    by (auto simp: setsum_cases)
  moreover have "(SUP n. if i < n then f i else 0) = (f i :: pextreal)"
  proof (rule pextreal_SUPI)
    fix y :: pextreal assume "\<And>n. n \<in> UNIV \<Longrightarrow> (if i < n then f i else 0) \<le> y"
    from this[of "Suc i"] show "f i \<le> y" by auto
  qed simp
  ultimately show ?thesis using `x \<in> A i` unfolding psuminf_def by auto
qed

lemma psuminf_indicator:
  assumes "disjoint_family A"
  shows "(\<Sum>\<^isub>\<infinity> n. indicator (A n) x) = indicator (\<Union>i. A i) x"
proof cases
  assume *: "x \<in> (\<Union>i. A i)"
  then obtain i where "x \<in> A i" by auto
  from psuminf_cmult_indicator[OF assms, OF this, of "\<lambda>i. 1"]
  show ?thesis using * by simp
qed simp

end