header {*Measures*}

theory Measure
  imports Caratheodory
begin

text{*From the Hurd/Coble measure theory development, translated by Lawrence Paulson.*}

section {* Equations for the measure function @{text \<mu>} *}

lemma (in measure_space) measure_countably_additive:
  assumes "range A \<subseteq> sets M" "disjoint_family A"
  shows "psuminf (\<lambda>i. \<mu> (A i)) = \<mu> (\<Union>i. A i)"
proof -
  have "(\<Union> i. A i) \<in> sets M" using assms(1) by (rule countable_UN)
  with ca assms show ?thesis by (simp add: countably_additive_def)
qed

lemma (in measure_space) measure_space_cong:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> \<nu> A = \<mu> A"
  shows "measure_space M \<nu>"
proof
  show "\<nu> {} = 0" using assms by auto
  show "countably_additive M \<nu>" unfolding countably_additive_def
  proof safe
    fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> sets M" "disjoint_family A"
    then have "\<And>i. A i \<in> sets M" "(UNION UNIV A) \<in> sets M" by auto
    from this[THEN assms] measure_countably_additive[OF A]
    show "(\<Sum>\<^isub>\<infinity>n. \<nu> (A n)) = \<nu> (UNION UNIV A)" by simp
  qed
qed

lemma (in measure_space) additive: "additive M \<mu>"
proof (rule algebra.countably_additive_additive [OF _ _ ca])
  show "algebra M" by default
  show "positive \<mu>" by (simp add: positive_def)
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
    unfolding minus_pinfreal_eq2[OF s_less_space fin]
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
    by (simp add: pinfreal_cancel_plus_minus)
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
  assumes "P \<in> sets M" "\<And>i. B i \<in> sets M" "B \<up> P"
  shows "(\<lambda>i. \<mu> (B i)) \<up> \<mu> P"
  using assms unfolding isoton_def
  by (auto intro!: measure_mono continuity_from_below)


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
    unfolding pinfreal_SUP_minus[symmetric]
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
    by (rule pinfreal_diff_eq_diff_imp_eq[OF finite[of 0] le_IM le_MI])
qed

lemma (in measure_space) measure_down:
  assumes "P \<in> sets M" "\<And>i. B i \<in> sets M" "B \<down> P"
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

lemma (in sigma_algebra) finite_additivity_sufficient:
  assumes fin: "finite (space M)" and pos: "positive \<mu>" and add: "additive M \<mu>"
  shows "measure_space M \<mu>"
proof
  show [simp]: "\<mu> {} = 0" using pos by (simp add: positive_def)
  show "countably_additive M \<mu>"
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
      then have "\<forall>m\<ge>N. \<mu> (A m) = 0" by simp
      then have "(\<Sum>\<^isub>\<infinity> n. \<mu> (A n)) = setsum (\<lambda>m. \<mu> (A m)) {..<N}"
        by (simp add: psuminf_finite)
      also have "... = \<mu> (\<Union>i<N. A i)"
        proof (induct N)
          case 0 thus ?case by simp
        next
          case (Suc n)
          have "\<mu> (A n \<union> (\<Union> x<n. A x)) = \<mu> (A n) + \<mu> (\<Union> i<n. A i)"
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
      also have "... = \<mu> (\<Union>i. A i)"
        proof -
          have "(\<Union> i<N. A i) = (\<Union>i. A i)" using N
            by auto (metis Int_absorb N disjoint_iff_not_equal lessThan_iff not_leE)
          thus ?thesis by simp
        qed
      finally show "(\<Sum>\<^isub>\<infinity> n. \<mu> (A n)) = \<mu> (\<Union>i. A i)" .
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

lemma (in measure_space) measurable_countably_subadditive:
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
      by (rule pinfreal_less_add[OF not_\<omega>]) (insert contr, auto)
    also have "\<dots> = \<mu> (T \<union> S)"
      using assms by (subst measure_additive) auto
    also have "\<dots> \<le> \<mu> (space M)"
      using assms sets_into_space by (auto intro!: measure_mono)
    finally show False ..
  qed
qed

lemma (in measure_space) restricted_measure_space:
  assumes "S \<in> sets M"
  shows "measure_space (restricted_space S) \<mu>"
    (is "measure_space ?r \<mu>")
  unfolding measure_space_def measure_space_axioms_def
proof safe
  show "sigma_algebra ?r" using restricted_sigma_algebra[OF assms] .
  show "\<mu> {} = 0" by simp
  show "countably_additive ?r \<mu>"
    unfolding countably_additive_def
  proof safe
    fix A :: "nat \<Rightarrow> 'a set"
    assume *: "range A \<subseteq> sets ?r" and **: "disjoint_family A"
    from restriction_in_sets[OF assms *[simplified]] **
    show "(\<Sum>\<^isub>\<infinity> n. \<mu> (A n)) = \<mu> (\<Union>i. A i)"
      using measure_countably_additive by simp
  qed
qed

lemma (in measure_space) measure_space_vimage:
  assumes "f \<in> measurable M M'"
  and "sigma_algebra M'"
  shows "measure_space M' (\<lambda>A. \<mu> (f -` A \<inter> space M))" (is "measure_space M' ?T")
proof -
  interpret M': sigma_algebra M' by fact

  show ?thesis
  proof
    show "?T {} = 0" by simp

    show "countably_additive M' ?T"
    proof (unfold countably_additive_def, safe)
      fix A :: "nat \<Rightarrow> 'c set" assume "range A \<subseteq> sets M'" "disjoint_family A"
      hence *: "\<And>i. f -` (A i) \<inter> space M \<in> sets M"
        using `f \<in> measurable M M'` by (auto simp: measurable_def)
      moreover have "(\<Union>i. f -`  A i \<inter> space M) \<in> sets M"
        using * by blast
      moreover have **: "disjoint_family (\<lambda>i. f -` A i \<inter> space M)"
        using `disjoint_family A` by (auto simp: disjoint_family_on_def)
      ultimately show "(\<Sum>\<^isub>\<infinity> i. ?T (A i)) = ?T (\<Union>i. A i)"
        using measure_countably_additive[OF _ **] by (auto simp: comp_def vimage_UN)
    qed
  qed
qed

lemma (in measure_space) measure_space_subalgebra:
  assumes "N \<subseteq> sets M" "sigma_algebra (M\<lparr> sets := N \<rparr>)"
  shows "measure_space (M\<lparr> sets := N \<rparr>) \<mu>"
proof -
  interpret N: sigma_algebra "M\<lparr> sets := N \<rparr>" by fact
  show ?thesis
  proof
    show "countably_additive (M\<lparr>sets := N\<rparr>) \<mu>"
      using `N \<subseteq> sets M`
      by (auto simp add: countably_additive_def
               intro!: measure_countably_additive)
  qed simp
qed

section "@{text \<sigma>}-finite Measures"

locale sigma_finite_measure = measure_space +
  assumes sigma_finite: "\<exists>A::nat \<Rightarrow> 'a set. range A \<subseteq> sets M \<and> (\<Union>i. A i) = space M \<and> (\<forall>i. \<mu> (A i) \<noteq> \<omega>)"

lemma (in sigma_finite_measure) restricted_sigma_finite_measure:
  assumes "S \<in> sets M"
  shows "sigma_finite_measure (restricted_space S) \<mu>"
    (is "sigma_finite_measure ?r _")
  unfolding sigma_finite_measure_def sigma_finite_measure_axioms_def
proof safe
  show "measure_space ?r \<mu>" using restricted_measure_space[OF assms] .
next
  obtain A :: "nat \<Rightarrow> 'a set" where
      "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" "\<And>i. \<mu> (A i) \<noteq> \<omega>"
    using sigma_finite by auto
  show "\<exists>A::nat \<Rightarrow> 'a set. range A \<subseteq> sets ?r \<and> (\<Union>i. A i) = space ?r \<and> (\<forall>i. \<mu> (A i) \<noteq> \<omega>)"
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
    also have "\<dots> < \<omega>" using `\<mu> (A i) \<noteq> \<omega>` by (auto simp: pinfreal_less_\<omega>)
    finally show "\<mu> (A i \<inter> S) \<noteq> \<omega>" by (auto simp: pinfreal_less_\<omega>)
  qed
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

section "Real measure values"

lemma (in measure_space) real_measure_Union:
  assumes finite: "\<mu> A \<noteq> \<omega>" "\<mu> B \<noteq> \<omega>"
  and measurable: "A \<in> sets M" "B \<in> sets M" "A \<inter> B = {}"
  shows "real (\<mu> (A \<union> B)) = real (\<mu> A) + real (\<mu> B)"
  unfolding measure_additive[symmetric, OF measurable]
  using finite by (auto simp: real_of_pinfreal_add)

lemma (in measure_space) real_measure_finite_Union:
  assumes measurable:
    "finite S" "\<And>i. i \<in> S \<Longrightarrow> A i \<in> sets M" "disjoint_family_on A S"
  assumes finite: "\<And>i. i \<in> S \<Longrightarrow> \<mu> (A i) \<noteq> \<omega>"
  shows "real (\<mu> (\<Union>i\<in>S. A i)) = (\<Sum>i\<in>S. real (\<mu> (A i)))"
  using real_of_pinfreal_setsum[of S, OF finite]
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
    using measure_subadditive[OF measurable] fin by (auto intro!: real_of_pinfreal_mono)
  also have "\<dots> = real (\<mu> A) + real (\<mu> B)"
    using fin by (simp add: real_of_pinfreal_add)
  finally show ?thesis .
qed

lemma (in measure_space) real_measurable_countably_subadditive:
  assumes "range f \<subseteq> sets M" and "(\<Sum>\<^isub>\<infinity> i. \<mu> (f i)) \<noteq> \<omega>"
  shows "real (\<mu> (\<Union>i. f i)) \<le> (\<Sum> i. real (\<mu> (f i)))"
proof -
  have "real (\<mu> (\<Union>i. f i)) \<le> real (\<Sum>\<^isub>\<infinity> i. \<mu> (f i))"
    using assms by (auto intro!: real_of_pinfreal_mono measurable_countably_subadditive)
  also have "\<dots> = (\<Sum> i. real (\<mu> (f i)))"
    using assms by (auto intro!: sums_unique psuminf_imp_suminf)
  finally show ?thesis .
qed

lemma (in measure_space) real_measure_setsum_singleton:
  assumes S: "finite S" "\<And>x. x \<in> S \<Longrightarrow> {x} \<in> sets M"
  and fin: "\<And>x. x \<in> S \<Longrightarrow> \<mu> {x} \<noteq> \<omega>"
  shows "real (\<mu> S) = (\<Sum>x\<in>S. real (\<mu> {x}))"
  using measure_finite_singleton[OF S] fin by (simp add: real_of_pinfreal_setsum)

lemma (in measure_space) real_continuity_from_below:
  assumes A: "range A \<subseteq> sets M" "\<And>i. A i \<subseteq> A (Suc i)" and "\<mu> (\<Union>i. A i) \<noteq> \<omega>"
  shows "(\<lambda>i. real (\<mu> (A i))) ----> real (\<mu> (\<Union>i. A i))"
proof (rule SUP_eq_LIMSEQ[THEN iffD1])
  { fix n have "\<mu> (A n) \<le> \<mu> (\<Union>i. A i)"
      using A by (auto intro!: measure_mono)
    hence "\<mu> (A n) \<noteq> \<omega>" using assms by auto }
  note this[simp]

  show "mono (\<lambda>i. real (\<mu> (A i)))" unfolding mono_iff_le_Suc using A
    by (auto intro!: real_of_pinfreal_mono measure_mono)

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
    by (auto intro!: real_of_pinfreal_mono measure_mono)

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
    using finite_measure_of_space unfolding pinfreal_less_\<omega> .
  finally show ?thesis unfolding pinfreal_less_\<omega> .
qed

lemma (in finite_measure) restricted_finite_measure:
  assumes "S \<in> sets M"
  shows "finite_measure (restricted_space S) \<mu>"
    (is "finite_measure ?r _")
  unfolding finite_measure_def finite_measure_axioms_def
proof (safe del: notI)
  show "measure_space ?r \<mu>" using restricted_measure_space[OF assms] .
next
  show "\<mu> (space ?r) \<noteq> \<omega>" using finite_measure[OF `S \<in> sets M`] by auto
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
  by (auto intro!: measure_mono real_of_pinfreal_mono finite_measure)

lemma (in finite_measure) real_finite_measure_subadditive:
  assumes measurable: "A \<in> sets M" "B \<in> sets M"
  shows "real (\<mu> (A \<union> B)) \<le> real (\<mu> A) + real (\<mu> B)"
  using measurable measurable[THEN finite_measure] by (rule real_measure_subadditive)

lemma (in finite_measure) real_finite_measurable_countably_subadditive:
  assumes "range f \<subseteq> sets M" and "summable (\<lambda>i. real (\<mu> (f i)))"
  shows "real (\<mu> (\<Union>i. f i)) \<le> (\<Sum> i. real (\<mu> (f i)))"
proof (rule real_measurable_countably_subadditive[OF assms(1)])
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

definition "measure_preserving A \<mu> B \<nu> =
    {f \<in> measurable A B. (\<forall>y \<in> sets B. \<mu> (f -` y \<inter> space A) = \<nu> y)}"

lemma (in finite_measure) measure_preserving_lift:
  fixes f :: "'a \<Rightarrow> 'a2" and A :: "('a2, 'b2) algebra_scheme"
  assumes "algebra A"
  assumes "finite_measure (sigma (space A) (sets A)) \<nu>" (is "finite_measure ?sA _")
  assumes fmp: "f \<in> measure_preserving M \<mu> A \<nu>"
  shows "f \<in> measure_preserving M \<mu> (sigma (space A) (sets A)) \<nu>"
proof -
  interpret sA: finite_measure ?sA \<nu> by fact
  interpret A: algebra A by fact
  show ?thesis using fmp
    proof (clarsimp simp add: measure_preserving_def)
      assume fm: "f \<in> measurable M A"
         and meq: "\<forall>y\<in>sets A. \<mu> (f -` y \<inter> space M) = \<nu> y"
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
        also have "\<dots> \<subseteq> {s . \<mu> ((f -` s) \<inter> space M) = \<nu> s}"
          proof (rule A.sigma_property_disjoint, auto)
            fix x assume "x \<in> sets A" then show "\<mu> (f -` x \<inter> space M) = \<nu> x" by (simp add: meq)
          next
            fix s
            assume eq: "\<mu> (f -` s \<inter> space M) = \<nu> s" and s: "s \<in> ?A"
            then have s': "s \<in> sets ?sA" by (simp add: sigma_def)
            show "\<mu> (f -` (space A - s) \<inter> space M) = \<nu> (space A - s)"
              using sA.finite_measure_compl[OF s']
              using measurable_sets[OF f12 s'] meq[THEN bspec, OF A.top]
              by (simp add: vimage_Diff Diff_Int_distrib2 finite_measure_compl eq)
          next
            fix S
            assume S0: "S 0 = {}"
               and SSuc: "\<And>n.  S n \<subseteq> S (Suc n)"
               and rS1: "range S \<subseteq> {s. \<mu> (f -` s \<inter> space M) = \<nu> s}"
               and "range S \<subseteq> ?A"
            hence rS2: "range S \<subseteq> sets ?sA" by (simp add: sigma_def)
            have eq1: "\<And>i. \<mu> (f -` S i \<inter> space M) = \<nu> (S i)"
              using rS1 by blast
            have *: "(\<lambda>n. \<nu> (S n)) = (\<lambda>n. \<mu> (f -` S n \<inter> space M))"
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
            finally have "(SUP n. \<nu> (S n)) = \<mu> (f -` (\<Union>i. S i) \<inter> space M)" unfolding * .
            moreover
            have "(SUP n. \<nu> (S n)) = \<nu> (\<Union>i. S i)"
              by (rule sA.measure_countable_increasing[OF rS2, OF S0 SSuc])
            ultimately
            show "\<mu> (f -` (\<Union>i. S i) \<inter> space M) = \<nu> (\<Union>i. S i)" by simp
          next
            fix S :: "nat => 'a2 set"
              assume dS: "disjoint_family S"
                 and rS1: "range S \<subseteq> {s. \<mu> (f -` s \<inter> space M) = \<nu> s}"
                 and "range S \<subseteq> ?A"
              hence rS2: "range S \<subseteq> sets ?sA" by (simp add: sigma_def)
              have "\<And>i. \<mu> (f -` S i \<inter> space M) = \<nu> (S i)"
                using rS1 by blast
              hence *: "(\<lambda>i. \<nu> (S i)) = (\<lambda>n. \<mu> (f -` S n \<inter> space M))"
                by simp
              have "psuminf ... = \<mu> (\<Union>i. f -` S i \<inter> space M)"
                proof (rule measure_countably_additive)
                  show "range (\<lambda>i. f -` S i \<inter> space M) \<subseteq> sets M"
                    using f12 rS2 by (auto simp add: measurable_def)
                  show "disjoint_family (\<lambda>i. f -` S i \<inter> space M)" using dS
                    by (auto simp add: disjoint_family_on_def)
                qed
              hence "(\<Sum>\<^isub>\<infinity> i. \<nu> (S i)) = \<mu> (\<Union>i. f -` S i \<inter> space M)" unfolding * .
              with sA.measure_countably_additive [OF rS2 dS]
              have "\<mu> (\<Union>i. f -` S i \<inter> space M) = \<nu> (\<Union>i. S i)"
                by simp
              moreover have "\<mu> (f -` (\<Union>i. S i) \<inter> space M) = \<mu> (\<Union>i. f -` S i \<inter> space M)"
                by (simp add: vimage_UN)
              ultimately show "\<mu> (f -` (\<Union>i. S i) \<inter> space M) = \<nu> (\<Union>i. S i)"
                by metis
          qed
        finally have "sets ?sA \<subseteq> {s . \<mu> ((f -` s) \<inter> space M) = \<nu> s}" .
        hence "\<mu> (f -` y \<inter> space M) = \<nu> y" using y by force
      }
      thus "f \<in> measurable M ?sA \<and> (\<forall>y\<in>sets ?sA. \<mu> (f -` y \<inter> space M) = \<nu> y)"
        by (blast intro: f12)
    qed
qed

section "Finite spaces"

locale finite_measure_space = measure_space +
  assumes finite_space: "finite (space M)"
  and sets_eq_Pow: "sets M = Pow (space M)"
  and finite_single_measure: "\<And>x. x \<in> space M \<Longrightarrow> \<mu> {x} \<noteq> \<omega>"

lemma (in finite_measure_space) sets_image_space_eq_Pow:
  "sets (image_space X) = Pow (space (image_space X))"
proof safe
  fix x S assume "S \<in> sets (image_space X)" "x \<in> S"
  then show "x \<in> space (image_space X)"
    using sets_into_space by (auto intro!: imageI simp: image_space_def)
next
  fix S assume "S \<subseteq> space (image_space X)"
  then obtain S' where "S = X`S'" "S'\<in>sets M"
    by (auto simp: subset_image_iff sets_eq_Pow image_space_def)
  then show "S \<in> sets (image_space X)"
    by (auto simp: image_space_def)
qed

lemma (in finite_measure_space) sum_over_space: "(\<Sum>x\<in>space M. \<mu> {x}) = \<mu> (space M)"
  using measure_finitely_additive''[of "space M" "\<lambda>i. {i}"]
  by (simp add: sets_eq_Pow disjoint_family_on_def finite_space)

lemma finite_measure_spaceI:
  assumes "finite (space M)" "sets M = Pow(space M)" and space: "\<mu> (space M) \<noteq> \<omega>"
    and add: "\<And>A B. A\<subseteq>space M \<Longrightarrow> B\<subseteq>space M \<Longrightarrow> A \<inter> B = {} \<Longrightarrow> \<mu> (A \<union> B) = \<mu> A + \<mu> B"
    and "\<mu> {} = 0"
  shows "finite_measure_space M \<mu>"
    unfolding finite_measure_space_def finite_measure_space_axioms_def
proof (safe del: notI)
  show "measure_space M \<mu>"
  proof (rule sigma_algebra.finite_additivity_sufficient)
    show "sigma_algebra M"
      apply (rule sigma_algebra_cong)
      apply (rule sigma_algebra_Pow[of "space M"])
      using assms by simp_all
    show "finite (space M)" by fact
    show "positive \<mu>" unfolding positive_def by fact
    show "additive M \<mu>" unfolding additive_def using assms by simp
  qed
  show "finite (space M)" by fact
  { fix A x assume "A \<in> sets M" "x \<in> A" then show "x \<in> space M"
      using assms by auto }
  { fix A assume "A \<subseteq> space M" then show "A \<in> sets M"
      using assms by auto }
  { fix x assume *: "x \<in> space M"
    with add[of "{x}" "space M - {x}"] space
    show "\<mu> {x} \<noteq> \<omega>" by (auto simp: insert_absorb[OF *] Diff_subset) }
qed

sublocale finite_measure_space < finite_measure
proof
  show "\<mu> (space M) \<noteq> \<omega>"
    unfolding sum_over_space[symmetric] setsum_\<omega>
    using finite_space finite_single_measure by auto
qed

lemma finite_measure_space_iff:
  "finite_measure_space M \<mu> \<longleftrightarrow>
    finite (space M) \<and> sets M = Pow(space M) \<and> \<mu> (space M) \<noteq> \<omega> \<and> \<mu> {} = 0 \<and>
    (\<forall>A\<subseteq>space M. \<forall>B\<subseteq>space M. A \<inter> B = {} \<longrightarrow> \<mu> (A \<union> B) = \<mu> A + \<mu> B)"
    (is "_ = ?rhs")
proof (intro iffI)
  assume "finite_measure_space M \<mu>"
  then interpret finite_measure_space M \<mu> .
  show ?rhs
    using finite_space sets_eq_Pow measure_additive empty_measure finite_measure
    by auto
next
  assume ?rhs then show "finite_measure_space M \<mu>"
    by (auto intro!: finite_measure_spaceI)
qed

lemma psuminf_cmult_indicator:
  assumes "disjoint_family A" "x \<in> A i"
  shows "(\<Sum>\<^isub>\<infinity> n. f n * indicator (A n) x) = f i"
proof -
  have **: "\<And>n. f n * indicator (A n) x = (if n = i then f n else 0 :: pinfreal)"
    using `x \<in> A i` assms unfolding disjoint_family_on_def indicator_def by auto
  then have "\<And>n. (\<Sum>j<n. f j * indicator (A j) x) = (if i < n then f i else 0 :: pinfreal)"
    by (auto simp: setsum_cases)
  moreover have "(SUP n. if i < n then f i else 0) = (f i :: pinfreal)"
  proof (rule pinfreal_SUPI)
    fix y :: pinfreal assume "\<And>n. n \<in> UNIV \<Longrightarrow> (if i < n then f i else 0) \<le> y"
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