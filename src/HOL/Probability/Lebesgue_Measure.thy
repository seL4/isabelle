(*  Title:      HOL/Probability/Lebesgue_Measure.thy
    Author:     Johannes Hölzl, TU München
    Author:     Robert Himmelmann, TU München
*)

header {* Lebsegue measure *}

theory Lebesgue_Measure
  imports Finite_Product_Measure
begin

lemma borel_measurable_indicator':
  "A \<in> sets borel \<Longrightarrow> f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. indicator A (f x)) \<in> borel_measurable M"
  using measurable_comp[OF _ borel_measurable_indicator, of f M borel A] by (auto simp add: comp_def)

lemma borel_measurable_sets:
  assumes "f \<in> measurable borel M" "A \<in> sets M"
  shows "f -` A \<in> sets borel"
  using measurable_sets[OF assms] by simp

subsection {* Standard Cubes *}

definition cube :: "nat \<Rightarrow> 'a::ordered_euclidean_space set" where
  "cube n \<equiv> {\<chi>\<chi> i. - real n .. \<chi>\<chi> i. real n}"

lemma borel_cube[intro]: "cube n \<in> sets borel"
  unfolding cube_def by auto

lemma cube_closed[intro]: "closed (cube n)"
  unfolding cube_def by auto

lemma cube_subset[intro]: "n \<le> N \<Longrightarrow> cube n \<subseteq> cube N"
  by (fastforce simp: eucl_le[where 'a='a] cube_def)

lemma cube_subset_iff:
  "cube n \<subseteq> cube N \<longleftrightarrow> n \<le> N"
proof
  assume subset: "cube n \<subseteq> (cube N::'a set)"
  then have "((\<chi>\<chi> i. real n)::'a) \<in> cube N"
    using DIM_positive[where 'a='a]
    by (fastforce simp: cube_def eucl_le[where 'a='a])
  then show "n \<le> N"
    by (fastforce simp: cube_def eucl_le[where 'a='a])
next
  assume "n \<le> N" then show "cube n \<subseteq> (cube N::'a set)" by (rule cube_subset)
qed

lemma ball_subset_cube:"ball (0::'a::ordered_euclidean_space) (real n) \<subseteq> cube n"
  unfolding cube_def subset_eq mem_interval apply safe unfolding euclidean_lambda_beta'
proof- fix x::'a and i assume as:"x\<in>ball 0 (real n)" "i<DIM('a)"
  thus "- real n \<le> x $$ i" "real n \<ge> x $$ i"
    using component_le_norm[of x i] by(auto simp: dist_norm)
qed

lemma mem_big_cube: obtains n where "x \<in> cube n"
proof- from reals_Archimedean2[of "norm x"] guess n ..
  thus ?thesis apply-apply(rule that[where n=n])
    apply(rule ball_subset_cube[unfolded subset_eq,rule_format])
    by (auto simp add:dist_norm)
qed

lemma cube_subset_Suc[intro]: "cube n \<subseteq> cube (Suc n)"
  unfolding cube_def subset_eq apply safe unfolding mem_interval apply auto done

subsection {* Lebesgue measure *}

definition lebesgue :: "'a::ordered_euclidean_space measure" where
  "lebesgue = measure_of UNIV {A. \<forall>n. (indicator A :: 'a \<Rightarrow> real) integrable_on cube n}
    (\<lambda>A. SUP n. ereal (integral (cube n) (indicator A)))"

lemma space_lebesgue[simp]: "space lebesgue = UNIV"
  unfolding lebesgue_def by simp

lemma lebesgueI: "(\<And>n. (indicator A :: _ \<Rightarrow> real) integrable_on cube n) \<Longrightarrow> A \<in> sets lebesgue"
  unfolding lebesgue_def by simp

lemma absolutely_integrable_on_indicator[simp]:
  fixes A :: "'a::ordered_euclidean_space set"
  shows "((indicator A :: _ \<Rightarrow> real) absolutely_integrable_on X) \<longleftrightarrow>
    (indicator A :: _ \<Rightarrow> real) integrable_on X"
  unfolding absolutely_integrable_on_def by simp

lemma LIMSEQ_indicator_UN:
  "(\<lambda>k. indicator (\<Union> i<k. A i) x) ----> (indicator (\<Union>i. A i) x :: real)"
proof cases
  assume "\<exists>i. x \<in> A i" then guess i .. note i = this
  then have *: "\<And>n. (indicator (\<Union> i<n + Suc i. A i) x :: real) = 1"
    "(indicator (\<Union> i. A i) x :: real) = 1" by (auto simp: indicator_def)
  show ?thesis
    apply (rule LIMSEQ_offset[of _ "Suc i"]) unfolding * by auto
qed (auto simp: indicator_def)

lemma indicator_add:
  "A \<inter> B = {} \<Longrightarrow> (indicator A x::_::monoid_add) + indicator B x = indicator (A \<union> B) x"
  unfolding indicator_def by auto

lemma sigma_algebra_lebesgue:
  defines "leb \<equiv> {A. \<forall>n. (indicator A :: 'a::ordered_euclidean_space \<Rightarrow> real) integrable_on cube n}"
  shows "sigma_algebra UNIV leb"
proof (safe intro!: sigma_algebra_iff2[THEN iffD2])
  fix A assume A: "A \<in> leb"
  moreover have "indicator (UNIV - A) = (\<lambda>x. 1 - indicator A x :: real)"
    by (auto simp: fun_eq_iff indicator_def)
  ultimately show "UNIV - A \<in> leb"
    using A by (auto intro!: integrable_sub simp: cube_def leb_def)
next
  fix n show "{} \<in> leb"
    by (auto simp: cube_def indicator_def[abs_def] leb_def)
next
  fix A :: "nat \<Rightarrow> _" assume A: "range A \<subseteq> leb"
  have "\<forall>n. (indicator (\<Union>i. A i) :: _ \<Rightarrow> real) integrable_on cube n" (is "\<forall>n. ?g integrable_on _")
  proof (intro dominated_convergence[where g="?g"] ballI allI)
    fix k n show "(indicator (\<Union>i<k. A i) :: _ \<Rightarrow> real) integrable_on cube n"
    proof (induct k)
      case (Suc k)
      have *: "(\<Union> i<Suc k. A i) = (\<Union> i<k. A i) \<union> A k"
        unfolding lessThan_Suc UN_insert by auto
      have *: "(\<lambda>x. max (indicator (\<Union> i<k. A i) x) (indicator (A k) x) :: real) =
          indicator (\<Union> i<Suc k. A i)" (is "(\<lambda>x. max (?f x) (?g x)) = _")
        by (auto simp: fun_eq_iff * indicator_def)
      show ?case
        using absolutely_integrable_max[of ?f "cube n" ?g] A Suc
        by (simp add: * leb_def subset_eq)
    qed auto
  qed (auto intro: LIMSEQ_indicator_UN simp: cube_def)
  then show "(\<Union>i. A i) \<in> leb" by (auto simp: leb_def)
qed simp

lemma sets_lebesgue: "sets lebesgue = {A. \<forall>n. (indicator A :: _ \<Rightarrow> real) integrable_on cube n}"
  unfolding lebesgue_def sigma_algebra.sets_measure_of_eq[OF sigma_algebra_lebesgue] ..

lemma lebesgueD: "A \<in> sets lebesgue \<Longrightarrow> (indicator A :: _ \<Rightarrow> real) integrable_on cube n"
  unfolding sets_lebesgue by simp

lemma emeasure_lebesgue:
  assumes "A \<in> sets lebesgue"
  shows "emeasure lebesgue A = (SUP n. ereal (integral (cube n) (indicator A)))"
    (is "_ = ?\<mu> A")
proof (rule emeasure_measure_of[OF lebesgue_def])
  have *: "indicator {} = (\<lambda>x. 0 :: real)" by (simp add: fun_eq_iff)
  show "positive (sets lebesgue) ?\<mu>"
  proof (unfold positive_def, intro conjI ballI)
    show "?\<mu> {} = 0" by (simp add: integral_0 *)
    fix A :: "'a set" assume "A \<in> sets lebesgue" then show "0 \<le> ?\<mu> A"
      by (auto intro!: SUP_upper2 Integration.integral_nonneg simp: sets_lebesgue)
  qed
next
  show "countably_additive (sets lebesgue) ?\<mu>"
  proof (intro countably_additive_def[THEN iffD2] allI impI)
    fix A :: "nat \<Rightarrow> 'a set" assume rA: "range A \<subseteq> sets lebesgue" "disjoint_family A"
    then have A[simp, intro]: "\<And>i n. (indicator (A i) :: _ \<Rightarrow> real) integrable_on cube n"
      by (auto dest: lebesgueD)
    let ?m = "\<lambda>n i. integral (cube n) (indicator (A i) :: _\<Rightarrow>real)"
    let ?M = "\<lambda>n I. integral (cube n) (indicator (\<Union>i\<in>I. A i) :: _\<Rightarrow>real)"
    have nn[simp, intro]: "\<And>i n. 0 \<le> ?m n i" by (auto intro!: Integration.integral_nonneg)
    assume "(\<Union>i. A i) \<in> sets lebesgue"
    then have UN_A[simp, intro]: "\<And>i n. (indicator (\<Union>i. A i) :: _ \<Rightarrow> real) integrable_on cube n"
      by (auto simp: sets_lebesgue)
    show "(\<Sum>n. ?\<mu> (A n)) = ?\<mu> (\<Union>i. A i)"
    proof (subst suminf_SUP_eq, safe intro!: incseq_SucI) 
      fix i n show "ereal (?m n i) \<le> ereal (?m (Suc n) i)"
        using cube_subset[of n "Suc n"] by (auto intro!: integral_subset_le incseq_SucI)
    next
      fix i n show "0 \<le> ereal (?m n i)"
        using rA unfolding lebesgue_def
        by (auto intro!: SUP_upper2 integral_nonneg)
    next
      show "(SUP n. \<Sum>i. ereal (?m n i)) = (SUP n. ereal (?M n UNIV))"
      proof (intro arg_cong[where f="SUPR UNIV"] ext sums_unique[symmetric] sums_ereal[THEN iffD2] sums_def[THEN iffD2])
        fix n
        have "\<And>m. (UNION {..<m} A) \<in> sets lebesgue" using rA by auto
        from lebesgueD[OF this]
        have "(\<lambda>m. ?M n {..< m}) ----> ?M n UNIV"
          (is "(\<lambda>m. integral _ (?A m)) ----> ?I")
          by (intro dominated_convergence(2)[where f="?A" and h="\<lambda>x. 1::real"])
             (auto intro: LIMSEQ_indicator_UN simp: cube_def)
        moreover
        { fix m have *: "(\<Sum>x<m. ?m n x) = ?M n {..< m}"
          proof (induct m)
            case (Suc m)
            have "(\<Union>i<m. A i) \<in> sets lebesgue" using rA by auto
            then have "(indicator (\<Union>i<m. A i) :: _\<Rightarrow>real) integrable_on (cube n)"
              by (auto dest!: lebesgueD)
            moreover
            have "(\<Union>i<m. A i) \<inter> A m = {}"
              using rA(2)[unfolded disjoint_family_on_def, THEN bspec, of m]
              by auto
            then have "\<And>x. indicator (\<Union>i<Suc m. A i) x =
              indicator (\<Union>i<m. A i) x + (indicator (A m) x :: real)"
              by (auto simp: indicator_add lessThan_Suc ac_simps)
            ultimately show ?case
              using Suc A by (simp add: Integration.integral_add[symmetric])
          qed auto }
        ultimately show "(\<lambda>m. \<Sum>x = 0..<m. ?m n x) ----> ?M n UNIV"
          by (simp add: atLeast0LessThan)
      qed
    qed
  qed
qed (auto, fact)

lemma has_integral_interval_cube:
  fixes a b :: "'a::ordered_euclidean_space"
  shows "(indicator {a .. b} has_integral
    content ({\<chi>\<chi> i. max (- real n) (a $$ i) .. \<chi>\<chi> i. min (real n) (b $$ i)} :: 'a set)) (cube n)"
    (is "(?I has_integral content ?R) (cube n)")
proof -
  let "{?N .. ?P}" = ?R
  have [simp]: "(\<lambda>x. if x \<in> cube n then ?I x else 0) = indicator ?R"
    by (auto simp: indicator_def cube_def fun_eq_iff eucl_le[where 'a='a])
  have "(?I has_integral content ?R) (cube n) \<longleftrightarrow> (indicator ?R has_integral content ?R) UNIV"
    unfolding has_integral_restrict_univ[where s="cube n", symmetric] by simp
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. 1) has_integral content ?R) ?R"
    unfolding indicator_def [abs_def] has_integral_restrict_univ ..
  finally show ?thesis
    using has_integral_const[of "1::real" "?N" "?P"] by simp
qed

lemma lebesgueI_borel[intro, simp]:
  fixes s::"'a::ordered_euclidean_space set"
  assumes "s \<in> sets borel" shows "s \<in> sets lebesgue"
proof -
  have "s \<in> sigma_sets (space lebesgue) (range (\<lambda>(a, b). {a .. (b :: 'a\<Colon>ordered_euclidean_space)}))"
    using assms by (simp add: borel_eq_atLeastAtMost)
  also have "\<dots> \<subseteq> sets lebesgue"
  proof (safe intro!: sigma_sets_subset lebesgueI)
    fix n :: nat and a b :: 'a
    let ?N = "\<chi>\<chi> i. max (- real n) (a $$ i)"
    let ?P = "\<chi>\<chi> i. min (real n) (b $$ i)"
    show "(indicator {a..b} :: 'a\<Rightarrow>real) integrable_on cube n"
      unfolding integrable_on_def
      using has_integral_interval_cube[of a b] by auto
  qed
  finally show ?thesis .
qed

lemma borel_measurable_lebesgueI:
  "f \<in> borel_measurable borel \<Longrightarrow> f \<in> borel_measurable lebesgue"
  unfolding measurable_def by simp

lemma lebesgueI_negligible[dest]: fixes s::"'a::ordered_euclidean_space set"
  assumes "negligible s" shows "s \<in> sets lebesgue"
  using assms by (force simp: cube_def integrable_on_def negligible_def intro!: lebesgueI)

lemma lmeasure_eq_0:
  fixes S :: "'a::ordered_euclidean_space set"
  assumes "negligible S" shows "emeasure lebesgue S = 0"
proof -
  have "\<And>n. integral (cube n) (indicator S :: 'a\<Rightarrow>real) = 0"
    unfolding lebesgue_integral_def using assms
    by (intro integral_unique some1_equality ex_ex1I)
       (auto simp: cube_def negligible_def)
  then show ?thesis
    using assms by (simp add: emeasure_lebesgue lebesgueI_negligible)
qed

lemma lmeasure_iff_LIMSEQ:
  assumes A: "A \<in> sets lebesgue" and "0 \<le> m"
  shows "emeasure lebesgue A = ereal m \<longleftrightarrow> (\<lambda>n. integral (cube n) (indicator A :: _ \<Rightarrow> real)) ----> m"
proof (subst emeasure_lebesgue[OF A], intro SUP_eq_LIMSEQ)
  show "mono (\<lambda>n. integral (cube n) (indicator A::_=>real))"
    using cube_subset assms by (intro monoI integral_subset_le) (auto dest!: lebesgueD)
qed

lemma has_integral_indicator_UNIV:
  fixes s A :: "'a::ordered_euclidean_space set" and x :: real
  shows "((indicator (s \<inter> A) :: 'a\<Rightarrow>real) has_integral x) UNIV = ((indicator s :: _\<Rightarrow>real) has_integral x) A"
proof -
  have "(\<lambda>x. if x \<in> A then indicator s x else 0) = (indicator (s \<inter> A) :: _\<Rightarrow>real)"
    by (auto simp: fun_eq_iff indicator_def)
  then show ?thesis
    unfolding has_integral_restrict_univ[where s=A, symmetric] by simp
qed

lemma
  fixes s a :: "'a::ordered_euclidean_space set"
  shows integral_indicator_UNIV:
    "integral UNIV (indicator (s \<inter> A) :: 'a\<Rightarrow>real) = integral A (indicator s :: _\<Rightarrow>real)"
  and integrable_indicator_UNIV:
    "(indicator (s \<inter> A) :: 'a\<Rightarrow>real) integrable_on UNIV \<longleftrightarrow> (indicator s :: 'a\<Rightarrow>real) integrable_on A"
  unfolding integral_def integrable_on_def has_integral_indicator_UNIV by auto

lemma lmeasure_finite_has_integral:
  fixes s :: "'a::ordered_euclidean_space set"
  assumes "s \<in> sets lebesgue" "emeasure lebesgue s = ereal m"
  shows "(indicator s has_integral m) UNIV"
proof -
  let ?I = "indicator :: 'a set \<Rightarrow> 'a \<Rightarrow> real"
  have "0 \<le> m"
    using emeasure_nonneg[of lebesgue s] `emeasure lebesgue s = ereal m` by simp
  have **: "(?I s) integrable_on UNIV \<and> (\<lambda>k. integral UNIV (?I (s \<inter> cube k))) ----> integral UNIV (?I s)"
  proof (intro monotone_convergence_increasing allI ballI)
    have LIMSEQ: "(\<lambda>n. integral (cube n) (?I s)) ----> m"
      using assms(2) unfolding lmeasure_iff_LIMSEQ[OF assms(1) `0 \<le> m`] .
    { fix n have "integral (cube n) (?I s) \<le> m"
        using cube_subset assms
        by (intro incseq_le[where L=m] LIMSEQ incseq_def[THEN iffD2] integral_subset_le allI impI)
           (auto dest!: lebesgueD) }
    moreover
    { fix n have "0 \<le> integral (cube n) (?I s)"
      using assms by (auto dest!: lebesgueD intro!: Integration.integral_nonneg) }
    ultimately
    show "bounded {integral UNIV (?I (s \<inter> cube k)) |k. True}"
      unfolding bounded_def
      apply (rule_tac exI[of _ 0])
      apply (rule_tac exI[of _ m])
      by (auto simp: dist_real_def integral_indicator_UNIV)
    fix k show "?I (s \<inter> cube k) integrable_on UNIV"
      unfolding integrable_indicator_UNIV using assms by (auto dest!: lebesgueD)
    fix x show "?I (s \<inter> cube k) x \<le> ?I (s \<inter> cube (Suc k)) x"
      using cube_subset[of k "Suc k"] by (auto simp: indicator_def)
  next
    fix x :: 'a
    from mem_big_cube obtain k where k: "x \<in> cube k" .
    { fix n have "?I (s \<inter> cube (n + k)) x = ?I s x"
      using k cube_subset[of k "n + k"] by (auto simp: indicator_def) }
    note * = this
    show "(\<lambda>k. ?I (s \<inter> cube k) x) ----> ?I s x"
      by (rule LIMSEQ_offset[where k=k]) (auto simp: *)
  qed
  note ** = conjunctD2[OF this]
  have m: "m = integral UNIV (?I s)"
    apply (intro LIMSEQ_unique[OF _ **(2)])
    using assms(2) unfolding lmeasure_iff_LIMSEQ[OF assms(1) `0 \<le> m`] integral_indicator_UNIV .
  show ?thesis
    unfolding m by (intro integrable_integral **)
qed

lemma lmeasure_finite_integrable: assumes s: "s \<in> sets lebesgue" and "emeasure lebesgue s \<noteq> \<infinity>"
  shows "(indicator s :: _ \<Rightarrow> real) integrable_on UNIV"
proof (cases "emeasure lebesgue s")
  case (real m)
  with lmeasure_finite_has_integral[OF `s \<in> sets lebesgue` this] emeasure_nonneg[of lebesgue s]
  show ?thesis unfolding integrable_on_def by auto
qed (insert assms emeasure_nonneg[of lebesgue s], auto)

lemma has_integral_lebesgue: assumes "((indicator s :: _\<Rightarrow>real) has_integral m) UNIV"
  shows "s \<in> sets lebesgue"
proof (intro lebesgueI)
  let ?I = "indicator :: 'a set \<Rightarrow> 'a \<Rightarrow> real"
  fix n show "(?I s) integrable_on cube n" unfolding cube_def
  proof (intro integrable_on_subinterval)
    show "(?I s) integrable_on UNIV"
      unfolding integrable_on_def using assms by auto
  qed auto
qed

lemma has_integral_lmeasure: assumes "((indicator s :: _\<Rightarrow>real) has_integral m) UNIV"
  shows "emeasure lebesgue s = ereal m"
proof (intro lmeasure_iff_LIMSEQ[THEN iffD2])
  let ?I = "indicator :: 'a set \<Rightarrow> 'a \<Rightarrow> real"
  show "s \<in> sets lebesgue" using has_integral_lebesgue[OF assms] .
  show "0 \<le> m" using assms by (rule has_integral_nonneg) auto
  have "(\<lambda>n. integral UNIV (?I (s \<inter> cube n))) ----> integral UNIV (?I s)"
  proof (intro dominated_convergence(2) ballI)
    show "(?I s) integrable_on UNIV" unfolding integrable_on_def using assms by auto
    fix n show "?I (s \<inter> cube n) integrable_on UNIV"
      unfolding integrable_indicator_UNIV using `s \<in> sets lebesgue` by (auto dest: lebesgueD)
    fix x show "norm (?I (s \<inter> cube n) x) \<le> ?I s x" by (auto simp: indicator_def)
  next
    fix x :: 'a
    from mem_big_cube obtain k where k: "x \<in> cube k" .
    { fix n have "?I (s \<inter> cube (n + k)) x = ?I s x"
      using k cube_subset[of k "n + k"] by (auto simp: indicator_def) }
    note * = this
    show "(\<lambda>k. ?I (s \<inter> cube k) x) ----> ?I s x"
      by (rule LIMSEQ_offset[where k=k]) (auto simp: *)
  qed
  then show "(\<lambda>n. integral (cube n) (?I s)) ----> m"
    unfolding integral_unique[OF assms] integral_indicator_UNIV by simp
qed

lemma has_integral_iff_lmeasure:
  "(indicator A has_integral m) UNIV \<longleftrightarrow> (A \<in> sets lebesgue \<and> emeasure lebesgue A = ereal m)"
proof
  assume "(indicator A has_integral m) UNIV"
  with has_integral_lmeasure[OF this] has_integral_lebesgue[OF this]
  show "A \<in> sets lebesgue \<and> emeasure lebesgue A = ereal m"
    by (auto intro: has_integral_nonneg)
next
  assume "A \<in> sets lebesgue \<and> emeasure lebesgue A = ereal m"
  then show "(indicator A has_integral m) UNIV" by (intro lmeasure_finite_has_integral) auto
qed

lemma lmeasure_eq_integral: assumes "(indicator s::_\<Rightarrow>real) integrable_on UNIV"
  shows "emeasure lebesgue s = ereal (integral UNIV (indicator s))"
  using assms unfolding integrable_on_def
proof safe
  fix y :: real assume "(indicator s has_integral y) UNIV"
  from this[unfolded has_integral_iff_lmeasure] integral_unique[OF this]
  show "emeasure lebesgue s = ereal (integral UNIV (indicator s))" by simp
qed

lemma lebesgue_simple_function_indicator:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> ereal"
  assumes f:"simple_function lebesgue f"
  shows "f = (\<lambda>x. (\<Sum>y \<in> f ` UNIV. y * indicator (f -` {y}) x))"
  by (rule, subst simple_function_indicator_representation[OF f]) auto

lemma integral_eq_lmeasure:
  "(indicator s::_\<Rightarrow>real) integrable_on UNIV \<Longrightarrow> integral UNIV (indicator s) = real (emeasure lebesgue s)"
  by (subst lmeasure_eq_integral) (auto intro!: integral_nonneg)

lemma lmeasure_finite: assumes "(indicator s::_\<Rightarrow>real) integrable_on UNIV" shows "emeasure lebesgue s \<noteq> \<infinity>"
  using lmeasure_eq_integral[OF assms] by auto

lemma negligible_iff_lebesgue_null_sets:
  "negligible A \<longleftrightarrow> A \<in> null_sets lebesgue"
proof
  assume "negligible A"
  from this[THEN lebesgueI_negligible] this[THEN lmeasure_eq_0]
  show "A \<in> null_sets lebesgue" by auto
next
  assume A: "A \<in> null_sets lebesgue"
  then have *:"((indicator A) has_integral (0::real)) UNIV" using lmeasure_finite_has_integral[of A]
    by (auto simp: null_sets_def)
  show "negligible A" unfolding negligible_def
  proof (intro allI)
    fix a b :: 'a
    have integrable: "(indicator A :: _\<Rightarrow>real) integrable_on {a..b}"
      by (intro integrable_on_subinterval has_integral_integrable) (auto intro: *)
    then have "integral {a..b} (indicator A) \<le> (integral UNIV (indicator A) :: real)"
      using * by (auto intro!: integral_subset_le)
    moreover have "(0::real) \<le> integral {a..b} (indicator A)"
      using integrable by (auto intro!: integral_nonneg)
    ultimately have "integral {a..b} (indicator A) = (0::real)"
      using integral_unique[OF *] by auto
    then show "(indicator A has_integral (0::real)) {a..b}"
      using integrable_integral[OF integrable] by simp
  qed
qed

lemma integral_const[simp]:
  fixes a b :: "'a::ordered_euclidean_space"
  shows "integral {a .. b} (\<lambda>x. c) = content {a .. b} *\<^sub>R c"
  by (rule integral_unique) (rule has_integral_const)

lemma lmeasure_UNIV[intro]: "emeasure lebesgue (UNIV::'a::ordered_euclidean_space set) = \<infinity>"
proof (simp add: emeasure_lebesgue, intro SUP_PInfty bexI)
  fix n :: nat
  have "indicator UNIV = (\<lambda>x::'a. 1 :: real)" by auto
  moreover
  { have "real n \<le> (2 * real n) ^ DIM('a)"
    proof (cases n)
      case 0 then show ?thesis by auto
    next
      case (Suc n')
      have "real n \<le> (2 * real n)^1" by auto
      also have "(2 * real n)^1 \<le> (2 * real n) ^ DIM('a)"
        using Suc DIM_positive[where 'a='a] by (intro power_increasing) (auto simp: real_of_nat_Suc)
      finally show ?thesis .
    qed }
  ultimately show "ereal (real n) \<le> ereal (integral (cube n) (indicator UNIV::'a\<Rightarrow>real))"
    using integral_const DIM_positive[where 'a='a]
    by (auto simp: cube_def content_closed_interval_cases setprod_constant)
qed simp

lemma lmeasure_complete: "A \<subseteq> B \<Longrightarrow> B \<in> null_sets lebesgue \<Longrightarrow> A \<in> null_sets lebesgue"
  unfolding negligible_iff_lebesgue_null_sets[symmetric] by (auto simp: negligible_subset)

lemma
  fixes a b ::"'a::ordered_euclidean_space"
  shows lmeasure_atLeastAtMost[simp]: "emeasure lebesgue {a..b} = ereal (content {a..b})"
proof -
  have "(indicator (UNIV \<inter> {a..b})::_\<Rightarrow>real) integrable_on UNIV"
    unfolding integrable_indicator_UNIV by (simp add: integrable_const indicator_def [abs_def])
  from lmeasure_eq_integral[OF this] show ?thesis unfolding integral_indicator_UNIV
    by (simp add: indicator_def [abs_def])
qed

lemma atLeastAtMost_singleton_euclidean[simp]:
  fixes a :: "'a::ordered_euclidean_space" shows "{a .. a} = {a}"
  by (force simp: eucl_le[where 'a='a] euclidean_eq[where 'a='a])

lemma content_singleton[simp]: "content {a} = 0"
proof -
  have "content {a .. a} = 0"
    by (subst content_closed_interval) auto
  then show ?thesis by simp
qed

lemma lmeasure_singleton[simp]:
  fixes a :: "'a::ordered_euclidean_space" shows "emeasure lebesgue {a} = 0"
  using lmeasure_atLeastAtMost[of a a] by simp

lemma AE_lebesgue_singleton:
  fixes a :: "'a::ordered_euclidean_space" shows "AE x in lebesgue. x \<noteq> a"
  by (rule AE_I[where N="{a}"]) auto

declare content_real[simp]

lemma
  fixes a b :: real
  shows lmeasure_real_greaterThanAtMost[simp]:
    "emeasure lebesgue {a <.. b} = ereal (if a \<le> b then b - a else 0)"
proof -
  have "emeasure lebesgue {a <.. b} = emeasure lebesgue {a .. b}"
    using AE_lebesgue_singleton[of a]
    by (intro emeasure_eq_AE) auto
  then show ?thesis by auto
qed

lemma
  fixes a b :: real
  shows lmeasure_real_atLeastLessThan[simp]:
    "emeasure lebesgue {a ..< b} = ereal (if a \<le> b then b - a else 0)"
proof -
  have "emeasure lebesgue {a ..< b} = emeasure lebesgue {a .. b}"
    using AE_lebesgue_singleton[of b]
    by (intro emeasure_eq_AE) auto
  then show ?thesis by auto
qed

lemma
  fixes a b :: real
  shows lmeasure_real_greaterThanLessThan[simp]:
    "emeasure lebesgue {a <..< b} = ereal (if a \<le> b then b - a else 0)"
proof -
  have "emeasure lebesgue {a <..< b} = emeasure lebesgue {a .. b}"
    using AE_lebesgue_singleton[of a] AE_lebesgue_singleton[of b]
    by (intro emeasure_eq_AE) auto
  then show ?thesis by auto
qed

subsection {* Lebesgue-Borel measure *}

definition "lborel = measure_of UNIV (sets borel) (emeasure lebesgue)"

lemma
  shows space_lborel[simp]: "space lborel = UNIV"
  and sets_lborel[simp]: "sets lborel = sets borel"
  and measurable_lborel1[simp]: "measurable lborel = measurable borel"
  and measurable_lborel2[simp]: "measurable A lborel = measurable A borel"
  using sigma_sets_eq[of borel]
  by (auto simp add: lborel_def measurable_def[abs_def])

lemma emeasure_lborel[simp]: "A \<in> sets borel \<Longrightarrow> emeasure lborel A = emeasure lebesgue A"
  by (rule emeasure_measure_of[OF lborel_def])
     (auto simp: positive_def emeasure_nonneg countably_additive_def intro!: suminf_emeasure)

interpretation lborel: sigma_finite_measure lborel
proof (default, intro conjI exI[of _ "\<lambda>n. cube n"])
  show "range cube \<subseteq> sets lborel" by (auto intro: borel_closed)
  { fix x :: 'a have "\<exists>n. x\<in>cube n" using mem_big_cube by auto }
  then show "(\<Union>i. cube i) = (space lborel :: 'a set)" using mem_big_cube by auto
  show "\<forall>i. emeasure lborel (cube i) \<noteq> \<infinity>" by (simp add: cube_def)
qed

interpretation lebesgue: sigma_finite_measure lebesgue
proof
  from lborel.sigma_finite guess A :: "nat \<Rightarrow> 'a set" ..
  then show "\<exists>A::nat \<Rightarrow> 'a set. range A \<subseteq> sets lebesgue \<and> (\<Union>i. A i) = space lebesgue \<and> (\<forall>i. emeasure lebesgue (A i) \<noteq> \<infinity>)"
    by (intro exI[of _ A]) (auto simp: subset_eq)
qed

lemma Int_stable_atLeastAtMost:
  fixes x::"'a::ordered_euclidean_space"
  shows "Int_stable (range (\<lambda>(a, b::'a). {a..b}))"
  by (auto simp: inter_interval Int_stable_def)

lemma lborel_eqI:
  fixes M :: "'a::ordered_euclidean_space measure"
  assumes emeasure_eq: "\<And>a b. emeasure M {a .. b} = content {a .. b}"
  assumes sets_eq: "sets M = sets borel"
  shows "lborel = M"
proof (rule measure_eqI_generator_eq[OF Int_stable_atLeastAtMost])
  let ?P = "\<Pi>\<^isub>M i\<in>{..<DIM('a::ordered_euclidean_space)}. lborel"
  let ?E = "range (\<lambda>(a, b). {a..b} :: 'a set)"
  show "?E \<subseteq> Pow UNIV" "sets lborel = sigma_sets UNIV ?E" "sets M = sigma_sets UNIV ?E"
    by (simp_all add: borel_eq_atLeastAtMost sets_eq)

  show "range cube \<subseteq> ?E" unfolding cube_def [abs_def] by auto
  show "incseq cube" using cube_subset_Suc by (auto intro!: incseq_SucI)
  { fix x :: 'a have "\<exists>n. x \<in> cube n" using mem_big_cube[of x] by fastforce }
  then show "(\<Union>i. cube i :: 'a set) = UNIV" by auto

  { fix i show "emeasure lborel (cube i) \<noteq> \<infinity>" unfolding cube_def by auto }
  { fix X assume "X \<in> ?E" then show "emeasure lborel X = emeasure M X"
      by (auto simp: emeasure_eq) }
qed

lemma lebesgue_real_affine:
  fixes c :: real assumes "c \<noteq> 0"
  shows "lborel = density (distr lborel borel (\<lambda>x. t + c * x)) (\<lambda>_. \<bar>c\<bar>)" (is "_ = ?D")
proof (rule lborel_eqI)
  fix a b show "emeasure ?D {a..b} = content {a .. b}"
  proof cases
    assume "0 < c"
    then have "(\<lambda>x. t + c * x) -` {a..b} = {(a - t) / c .. (b - t) / c}"
      by (auto simp: field_simps)
    with `0 < c` show ?thesis
      by (cases "a \<le> b")
         (auto simp: field_simps emeasure_density positive_integral_distr positive_integral_cmult
                     borel_measurable_indicator' emeasure_distr)
  next
    assume "\<not> 0 < c" with `c \<noteq> 0` have "c < 0" by auto
    then have *: "(\<lambda>x. t + c * x) -` {a..b} = {(b - t) / c .. (a - t) / c}"
      by (auto simp: field_simps)
    with `c < 0` show ?thesis
      by (cases "a \<le> b")
         (auto simp: field_simps emeasure_density positive_integral_distr
                     positive_integral_cmult borel_measurable_indicator' emeasure_distr)
  qed
qed simp

lemma lebesgue_integral_real_affine:
  fixes c :: real assumes c: "c \<noteq> 0" and f: "f \<in> borel_measurable borel"
  shows "(\<integral> x. f x \<partial> lborel) = \<bar>c\<bar> * (\<integral> x. f (t + c * x) \<partial>lborel)"
  by (subst lebesgue_real_affine[OF c, of t])
     (simp add: f integral_density integral_distr lebesgue_integral_cmult)

subsection {* Lebesgue integrable implies Gauge integrable *}

lemma has_integral_cmult_real:
  fixes c :: real
  assumes "c \<noteq> 0 \<Longrightarrow> (f has_integral x) A"
  shows "((\<lambda>x. c * f x) has_integral c * x) A"
proof cases
  assume "c \<noteq> 0"
  from has_integral_cmul[OF assms[OF this], of c] show ?thesis
    unfolding real_scaleR_def .
qed simp

lemma simple_function_has_integral:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> ereal"
  assumes f:"simple_function lebesgue f"
  and f':"range f \<subseteq> {0..<\<infinity>}"
  and om:"\<And>x. x \<in> range f \<Longrightarrow> emeasure lebesgue (f -` {x} \<inter> UNIV) = \<infinity> \<Longrightarrow> x = 0"
  shows "((\<lambda>x. real (f x)) has_integral (real (integral\<^isup>S lebesgue f))) UNIV"
  unfolding simple_integral_def space_lebesgue
proof (subst lebesgue_simple_function_indicator)
  let ?M = "\<lambda>x. emeasure lebesgue (f -` {x} \<inter> UNIV)"
  let ?F = "\<lambda>x. indicator (f -` {x})"
  { fix x y assume "y \<in> range f"
    from subsetD[OF f' this] have "y * ?F y x = ereal (real y * ?F y x)"
      by (cases rule: ereal2_cases[of y "?F y x"])
         (auto simp: indicator_def one_ereal_def split: split_if_asm) }
  moreover
  { fix x assume x: "x\<in>range f"
    have "x * ?M x = real x * real (?M x)"
    proof cases
      assume "x \<noteq> 0" with om[OF x] have "?M x \<noteq> \<infinity>" by auto
      with subsetD[OF f' x] f[THEN simple_functionD(2)] show ?thesis
        by (cases rule: ereal2_cases[of x "?M x"]) auto
    qed simp }
  ultimately
  have "((\<lambda>x. real (\<Sum>y\<in>range f. y * ?F y x)) has_integral real (\<Sum>x\<in>range f. x * ?M x)) UNIV \<longleftrightarrow>
    ((\<lambda>x. \<Sum>y\<in>range f. real y * ?F y x) has_integral (\<Sum>x\<in>range f. real x * real (?M x))) UNIV"
    by simp
  also have \<dots>
  proof (intro has_integral_setsum has_integral_cmult_real lmeasure_finite_has_integral
               real_of_ereal_pos emeasure_nonneg ballI)
    show *: "finite (range f)" "\<And>y. f -` {y} \<in> sets lebesgue"
      using simple_functionD[OF f] by auto
    fix y assume "real y \<noteq> 0" "y \<in> range f"
    with * om[OF this(2)] show "emeasure lebesgue (f -` {y}) = ereal (real (?M y))"
      by (auto simp: ereal_real)
  qed
  finally show "((\<lambda>x. real (\<Sum>y\<in>range f. y * ?F y x)) has_integral real (\<Sum>x\<in>range f. x * ?M x)) UNIV" .
qed fact

lemma bounded_realI: assumes "\<forall>x\<in>s. abs (x::real) \<le> B" shows "bounded s"
  unfolding bounded_def dist_real_def apply(rule_tac x=0 in exI)
  using assms by auto

lemma simple_function_has_integral':
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> ereal"
  assumes f: "simple_function lebesgue f" "\<And>x. 0 \<le> f x"
  and i: "integral\<^isup>S lebesgue f \<noteq> \<infinity>"
  shows "((\<lambda>x. real (f x)) has_integral (real (integral\<^isup>S lebesgue f))) UNIV"
proof -
  let ?f = "\<lambda>x. if x \<in> f -` {\<infinity>} then 0 else f x"
  note f(1)[THEN simple_functionD(2)]
  then have [simp, intro]: "\<And>X. f -` X \<in> sets lebesgue" by auto
  have f': "simple_function lebesgue ?f"
    using f by (intro simple_function_If_set) auto
  have rng: "range ?f \<subseteq> {0..<\<infinity>}" using f by auto
  have "AE x in lebesgue. f x = ?f x"
    using simple_integral_PInf[OF f i]
    by (intro AE_I[where N="f -` {\<infinity>} \<inter> space lebesgue"]) auto
  from f(1) f' this have eq: "integral\<^isup>S lebesgue f = integral\<^isup>S lebesgue ?f"
    by (rule simple_integral_cong_AE)
  have real_eq: "\<And>x. real (f x) = real (?f x)" by auto

  show ?thesis
    unfolding eq real_eq
  proof (rule simple_function_has_integral[OF f' rng])
    fix x assume x: "x \<in> range ?f" and inf: "emeasure lebesgue (?f -` {x} \<inter> UNIV) = \<infinity>"
    have "x * emeasure lebesgue (?f -` {x} \<inter> UNIV) = (\<integral>\<^isup>S y. x * indicator (?f -` {x}) y \<partial>lebesgue)"
      using f'[THEN simple_functionD(2)]
      by (simp add: simple_integral_cmult_indicator)
    also have "\<dots> \<le> integral\<^isup>S lebesgue f"
      using f'[THEN simple_functionD(2)] f
      by (intro simple_integral_mono simple_function_mult simple_function_indicator)
         (auto split: split_indicator)
    finally show "x = 0" unfolding inf using i subsetD[OF rng x] by (auto split: split_if_asm)
  qed
qed

lemma positive_integral_has_integral:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> ereal"
  assumes f: "f \<in> borel_measurable lebesgue" "range f \<subseteq> {0..<\<infinity>}" "integral\<^isup>P lebesgue f \<noteq> \<infinity>"
  shows "((\<lambda>x. real (f x)) has_integral (real (integral\<^isup>P lebesgue f))) UNIV"
proof -
  from borel_measurable_implies_simple_function_sequence'[OF f(1)]
  guess u . note u = this
  have SUP_eq: "\<And>x. (SUP i. u i x) = f x"
    using u(4) f(2)[THEN subsetD] by (auto split: split_max)
  let ?u = "\<lambda>i x. real (u i x)"
  note u_eq = positive_integral_eq_simple_integral[OF u(1,5), symmetric]
  { fix i
    note u_eq
    also have "integral\<^isup>P lebesgue (u i) \<le> (\<integral>\<^isup>+x. max 0 (f x) \<partial>lebesgue)"
      by (intro positive_integral_mono) (auto intro: SUP_upper simp: u(4)[symmetric])
    finally have "integral\<^isup>S lebesgue (u i) \<noteq> \<infinity>"
      unfolding positive_integral_max_0 using f by auto }
  note u_fin = this
  then have u_int: "\<And>i. (?u i has_integral real (integral\<^isup>S lebesgue (u i))) UNIV"
    by (rule simple_function_has_integral'[OF u(1,5)])
  have "\<forall>x. \<exists>r\<ge>0. f x = ereal r"
  proof
    fix x from f(2) have "0 \<le> f x" "f x \<noteq> \<infinity>" by (auto simp: subset_eq)
    then show "\<exists>r\<ge>0. f x = ereal r" by (cases "f x") auto
  qed
  from choice[OF this] obtain f' where f': "f = (\<lambda>x. ereal (f' x))" "\<And>x. 0 \<le> f' x" by auto

  have "\<forall>i. \<exists>r. \<forall>x. 0 \<le> r x \<and> u i x = ereal (r x)"
  proof
    fix i show "\<exists>r. \<forall>x. 0 \<le> r x \<and> u i x = ereal (r x)"
    proof (intro choice allI)
      fix i x have "u i x \<noteq> \<infinity>" using u(3)[of i] by (auto simp: image_iff) metis
      then show "\<exists>r\<ge>0. u i x = ereal r" using u(5)[of i x] by (cases "u i x") auto
    qed
  qed
  from choice[OF this] obtain u' where
      u': "u = (\<lambda>i x. ereal (u' i x))" "\<And>i x. 0 \<le> u' i x" by (auto simp: fun_eq_iff)

  have convergent: "f' integrable_on UNIV \<and>
    (\<lambda>k. integral UNIV (u' k)) ----> integral UNIV f'"
  proof (intro monotone_convergence_increasing allI ballI)
    show int: "\<And>k. (u' k) integrable_on UNIV"
      using u_int unfolding integrable_on_def u' by auto
    show "\<And>k x. u' k x \<le> u' (Suc k) x" using u(2,3,5)
      by (auto simp: incseq_Suc_iff le_fun_def image_iff u' intro!: real_of_ereal_positive_mono)
    show "\<And>x. (\<lambda>k. u' k x) ----> f' x"
      using SUP_eq u(2)
      by (intro SUP_eq_LIMSEQ[THEN iffD1]) (auto simp: u' f' incseq_mono incseq_Suc_iff le_fun_def)
    show "bounded {integral UNIV (u' k)|k. True}"
    proof (safe intro!: bounded_realI)
      fix k
      have "\<bar>integral UNIV (u' k)\<bar> = integral UNIV (u' k)"
        by (intro abs_of_nonneg integral_nonneg int ballI u')
      also have "\<dots> = real (integral\<^isup>S lebesgue (u k))"
        using u_int[THEN integral_unique] by (simp add: u')
      also have "\<dots> = real (integral\<^isup>P lebesgue (u k))"
        using positive_integral_eq_simple_integral[OF u(1,5)] by simp
      also have "\<dots> \<le> real (integral\<^isup>P lebesgue f)" using f
        by (auto intro!: real_of_ereal_positive_mono positive_integral_positive
             positive_integral_mono SUP_upper simp: SUP_eq[symmetric])
      finally show "\<bar>integral UNIV (u' k)\<bar> \<le> real (integral\<^isup>P lebesgue f)" .
    qed
  qed

  have "integral\<^isup>P lebesgue f = ereal (integral UNIV f')"
  proof (rule tendsto_unique[OF trivial_limit_sequentially])
    have "(\<lambda>i. integral\<^isup>S lebesgue (u i)) ----> (SUP i. integral\<^isup>P lebesgue (u i))"
      unfolding u_eq by (intro LIMSEQ_ereal_SUPR incseq_positive_integral u)
    also note positive_integral_monotone_convergence_SUP
      [OF u(2)  borel_measurable_simple_function[OF u(1)] u(5), symmetric]
    finally show "(\<lambda>k. integral\<^isup>S lebesgue (u k)) ----> integral\<^isup>P lebesgue f"
      unfolding SUP_eq .

    { fix k
      have "0 \<le> integral\<^isup>S lebesgue (u k)"
        using u by (auto intro!: simple_integral_positive)
      then have "integral\<^isup>S lebesgue (u k) = ereal (real (integral\<^isup>S lebesgue (u k)))"
        using u_fin by (auto simp: ereal_real) }
    note * = this
    show "(\<lambda>k. integral\<^isup>S lebesgue (u k)) ----> ereal (integral UNIV f')"
      using convergent using u_int[THEN integral_unique, symmetric]
      by (subst *) (simp add: u')
  qed
  then show ?thesis using convergent by (simp add: f' integrable_integral)
qed

lemma lebesgue_integral_has_integral:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> real"
  assumes f: "integrable lebesgue f"
  shows "(f has_integral (integral\<^isup>L lebesgue f)) UNIV"
proof -
  let ?n = "\<lambda>x. real (ereal (max 0 (- f x)))" and ?p = "\<lambda>x. real (ereal (max 0 (f x)))"
  have *: "f = (\<lambda>x. ?p x - ?n x)" by (auto simp del: ereal_max)
  { fix f :: "'a \<Rightarrow> real" have "(\<integral>\<^isup>+ x. ereal (f x) \<partial>lebesgue) = (\<integral>\<^isup>+ x. ereal (max 0 (f x)) \<partial>lebesgue)"
      by (intro positive_integral_cong_pos) (auto split: split_max) }
  note eq = this
  show ?thesis
    unfolding lebesgue_integral_def
    apply (subst *)
    apply (rule has_integral_sub)
    unfolding eq[of f] eq[of "\<lambda>x. - f x"]
    apply (safe intro!: positive_integral_has_integral)
    using integrableD[OF f]
    by (auto simp: zero_ereal_def[symmetric] positive_integral_max_0  split: split_max
             intro!: measurable_If)
qed

lemma lebesgue_simple_integral_eq_borel:
  assumes f: "f \<in> borel_measurable borel"
  shows "integral\<^isup>S lebesgue f = integral\<^isup>S lborel f"
  using f[THEN measurable_sets]
  by (auto intro!: setsum_cong arg_cong2[where f="op *"] emeasure_lborel[symmetric]
           simp: simple_integral_def)

lemma lebesgue_positive_integral_eq_borel:
  assumes f: "f \<in> borel_measurable borel"
  shows "integral\<^isup>P lebesgue f = integral\<^isup>P lborel f"
proof -
  from f have "integral\<^isup>P lebesgue (\<lambda>x. max 0 (f x)) = integral\<^isup>P lborel (\<lambda>x. max 0 (f x))"
    by (auto intro!: positive_integral_subalgebra[symmetric])
  then show ?thesis unfolding positive_integral_max_0 .
qed

lemma lebesgue_integral_eq_borel:
  assumes "f \<in> borel_measurable borel"
  shows "integrable lebesgue f \<longleftrightarrow> integrable lborel f" (is ?P)
    and "integral\<^isup>L lebesgue f = integral\<^isup>L lborel f" (is ?I)
proof -
  have "sets lborel \<subseteq> sets lebesgue" by auto
  from integral_subalgebra[of f lborel, OF _ this _ _] assms
  show ?P ?I by auto
qed

lemma borel_integral_has_integral:
  fixes f::"'a::ordered_euclidean_space => real"
  assumes f:"integrable lborel f"
  shows "(f has_integral (integral\<^isup>L lborel f)) UNIV"
proof -
  have borel: "f \<in> borel_measurable borel"
    using f unfolding integrable_def by auto
  from f show ?thesis
    using lebesgue_integral_has_integral[of f]
    unfolding lebesgue_integral_eq_borel[OF borel] by simp
qed

lemma integrable_on_cmult_iff:
  fixes c :: real assumes "c \<noteq> 0"
  shows "(\<lambda>x. c * f x) integrable_on s \<longleftrightarrow> f integrable_on s"
  using integrable_cmul[of "\<lambda>x. c * f x" s "1 / c"] integrable_cmul[of f s c] `c \<noteq> 0`
  by auto

lemma positive_integral_lebesgue_has_integral:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> real"
  assumes f_borel: "f \<in> borel_measurable lebesgue" and nonneg: "\<And>x. 0 \<le> f x"
  assumes I: "(f has_integral I) UNIV"
  shows "(\<integral>\<^isup>+x. f x \<partial>lebesgue) = I"
proof -
  from f_borel have "(\<lambda>x. ereal (f x)) \<in> borel_measurable lebesgue" by auto
  from borel_measurable_implies_simple_function_sequence'[OF this] guess F . note F = this

  have "(\<integral>\<^isup>+ x. ereal (f x) \<partial>lebesgue) = (SUP i. integral\<^isup>S lebesgue (F i))"
    using F
    by (subst positive_integral_monotone_convergence_simple)
       (simp_all add: positive_integral_max_0 simple_function_def)
  also have "\<dots> \<le> ereal I"
  proof (rule SUP_least)
    fix i :: nat

    { fix z
      from F(4)[of z] have "F i z \<le> ereal (f z)"
        by (metis SUP_upper UNIV_I ereal_max_0 min_max.sup_absorb2 nonneg)
      with F(5)[of i z] have "real (F i z) \<le> f z"
        by (cases "F i z") simp_all }
    note F_bound = this

    { fix x :: ereal assume x: "x \<noteq> 0" "x \<in> range (F i)"
      with F(3,5)[of i] have [simp]: "real x \<noteq> 0"
        by (metis image_iff order_eq_iff real_of_ereal_le_0)
      let ?s = "(\<lambda>n z. real x * indicator (F i -` {x} \<inter> cube n) z) :: nat \<Rightarrow> 'a \<Rightarrow> real"
      have "(\<lambda>z::'a. real x * indicator (F i -` {x}) z) integrable_on UNIV"
      proof (rule dominated_convergence(1))
        fix n :: nat
        have "(\<lambda>z. indicator (F i -` {x} \<inter> cube n) z :: real) integrable_on cube n"
          using x F(1)[of i]
          by (intro lebesgueD) (auto simp: simple_function_def)
        then have cube: "?s n integrable_on cube n"
          by (simp add: integrable_on_cmult_iff)
        show "?s n integrable_on UNIV"
          by (rule integrable_on_superset[OF _ _ cube]) auto
      next
        show "f integrable_on UNIV"
          unfolding integrable_on_def using I by auto
      next
        fix n from F_bound show "\<forall>x\<in>UNIV. norm (?s n x) \<le> f x"
          using nonneg F(5) by (auto split: split_indicator)
      next
        show "\<forall>z\<in>UNIV. (\<lambda>n. ?s n z) ----> real x * indicator (F i -` {x}) z"
        proof
          fix z :: 'a
          from mem_big_cube[of z] guess j .
          then have x: "eventually (\<lambda>n. ?s n z = real x * indicator (F i -` {x}) z) sequentially"
            by (auto intro!: eventually_sequentiallyI[where c=j] dest!: cube_subset split: split_indicator)
          then show "(\<lambda>n. ?s n z) ----> real x * indicator (F i -` {x}) z"
            by (rule Lim_eventually)
        qed
      qed
      then have "(indicator (F i -` {x}) :: 'a \<Rightarrow> real) integrable_on UNIV"
        by (simp add: integrable_on_cmult_iff) }
    note F_finite = lmeasure_finite[OF this]

    have "((\<lambda>x. real (F i x)) has_integral real (integral\<^isup>S lebesgue (F i))) UNIV"
    proof (rule simple_function_has_integral[of "F i"])
      show "simple_function lebesgue (F i)"
        using F(1) by (simp add: simple_function_def)
      show "range (F i) \<subseteq> {0..<\<infinity>}"
        using F(3,5)[of i] by (auto simp: image_iff) metis
    next
      fix x assume "x \<in> range (F i)" "emeasure lebesgue (F i -` {x} \<inter> UNIV) = \<infinity>"
      with F_finite[of x] show "x = 0" by auto
    qed
    from this I have "real (integral\<^isup>S lebesgue (F i)) \<le> I"
      by (rule has_integral_le) (intro ballI F_bound)
    moreover
    { fix x assume x: "x \<in> range (F i)"
      with F(3,5)[of i] have "x = 0 \<or> (0 < x \<and> x \<noteq> \<infinity>)"
        by (auto  simp: image_iff le_less) metis
      with F_finite[OF _ x] x have "x * emeasure lebesgue (F i -` {x} \<inter> UNIV) \<noteq> \<infinity>"
        by auto }
    then have "integral\<^isup>S lebesgue (F i) \<noteq> \<infinity>"
      unfolding simple_integral_def setsum_Pinfty space_lebesgue by blast
    moreover have "0 \<le> integral\<^isup>S lebesgue (F i)"
      using F(1,5) by (intro simple_integral_positive) (auto simp: simple_function_def)
    ultimately show "integral\<^isup>S lebesgue (F i) \<le> ereal I"
      by (cases "integral\<^isup>S lebesgue (F i)") auto
  qed
  also have "\<dots> < \<infinity>" by simp
  finally have finite: "(\<integral>\<^isup>+ x. ereal (f x) \<partial>lebesgue) \<noteq> \<infinity>" by simp
  have borel: "(\<lambda>x. ereal (f x)) \<in> borel_measurable lebesgue"
    using f_borel by (auto intro: borel_measurable_lebesgueI)
  from positive_integral_has_integral[OF borel _ finite]
  have "(f has_integral real (\<integral>\<^isup>+ x. ereal (f x) \<partial>lebesgue)) UNIV"
    using nonneg by (simp add: subset_eq)
  with I have "I = real (\<integral>\<^isup>+ x. ereal (f x) \<partial>lebesgue)"
    by (rule has_integral_unique)
  with finite positive_integral_positive[of _ "\<lambda>x. ereal (f x)"] show ?thesis
    by (cases "\<integral>\<^isup>+ x. ereal (f x) \<partial>lebesgue") auto
qed

lemma has_integral_iff_positive_integral_lebesgue:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable lebesgue" "\<And>x. 0 \<le> f x"
  shows "(f has_integral I) UNIV \<longleftrightarrow> integral\<^isup>P lebesgue f = I"
  using f positive_integral_lebesgue_has_integral[of f I] positive_integral_has_integral[of f]
  by (auto simp: subset_eq)

lemma has_integral_iff_positive_integral_lborel:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel" "\<And>x. 0 \<le> f x"
  shows "(f has_integral I) UNIV \<longleftrightarrow> integral\<^isup>P lborel f = I"
  using assms
  by (subst has_integral_iff_positive_integral_lebesgue)
     (auto simp: borel_measurable_lebesgueI lebesgue_positive_integral_eq_borel)

subsection {* Equivalence between product spaces and euclidean spaces *}

definition e2p :: "'a::ordered_euclidean_space \<Rightarrow> (nat \<Rightarrow> real)" where
  "e2p x = (\<lambda>i\<in>{..<DIM('a)}. x$$i)"

definition p2e :: "(nat \<Rightarrow> real) \<Rightarrow> 'a::ordered_euclidean_space" where
  "p2e x = (\<chi>\<chi> i. x i)"

lemma e2p_p2e[simp]:
  "x \<in> extensional {..<DIM('a)} \<Longrightarrow> e2p (p2e x::'a::ordered_euclidean_space) = x"
  by (auto simp: fun_eq_iff extensional_def p2e_def e2p_def)

lemma p2e_e2p[simp]:
  "p2e (e2p x) = (x::'a::ordered_euclidean_space)"
  by (auto simp: euclidean_eq[where 'a='a] p2e_def e2p_def)

interpretation lborel_product: product_sigma_finite "\<lambda>x. lborel::real measure"
  by default

interpretation lborel_space: finite_product_sigma_finite "\<lambda>x. lborel::real measure" "{..<n}" for n :: nat
  by default auto

lemma bchoice_iff: "(\<forall>x\<in>A. \<exists>y. P x y) \<longleftrightarrow> (\<exists>f. \<forall>x\<in>A. P x (f x))"
  by metis

lemma sets_product_borel:
  assumes I: "finite I"
  shows "sets (\<Pi>\<^isub>M i\<in>I. lborel) = sigma_sets (\<Pi>\<^isub>E i\<in>I. UNIV) { \<Pi>\<^isub>E i\<in>I. {..< x i :: real} | x. True}" (is "_ = ?G")
proof (subst sigma_prod_algebra_sigma_eq[where S="\<lambda>_ i::nat. {..<real i}" and E="\<lambda>_. range lessThan", OF I])
  show "sigma_sets (space (Pi\<^isub>M I (\<lambda>i. lborel))) {Pi\<^isub>E I F |F. \<forall>i\<in>I. F i \<in> range lessThan} = ?G"
    by (intro arg_cong2[where f=sigma_sets]) (auto simp: space_PiM image_iff bchoice_iff)
qed (auto simp: borel_eq_lessThan incseq_def reals_Archimedean2 image_iff intro: real_natceiling_ge)

lemma measurable_e2p:
  "e2p \<in> measurable (borel::'a::ordered_euclidean_space measure) (\<Pi>\<^isub>M i\<in>{..<DIM('a)}. (lborel :: real measure))"
proof (rule measurable_sigma_sets[OF sets_product_borel])
  fix A :: "(nat \<Rightarrow> real) set" assume "A \<in> {\<Pi>\<^isub>E i\<in>{..<DIM('a)}. {..<x i} |x. True} "
  then obtain x where  "A = (\<Pi>\<^isub>E i\<in>{..<DIM('a)}. {..<x i})" by auto
  then have "e2p -` A = {..< (\<chi>\<chi> i. x i) :: 'a}"
    using DIM_positive by (auto simp add: Pi_iff set_eq_iff e2p_def
      euclidean_eq[where 'a='a] eucl_less[where 'a='a])
  then show "e2p -` A \<inter> space (borel::'a measure) \<in> sets borel" by simp
qed (auto simp: e2p_def)

lemma measurable_p2e:
  "p2e \<in> measurable (\<Pi>\<^isub>M i\<in>{..<DIM('a)}. (lborel :: real measure))
    (borel :: 'a::ordered_euclidean_space measure)"
  (is "p2e \<in> measurable ?P _")
proof (safe intro!: borel_measurable_iff_halfspace_le[THEN iffD2])
  fix x i
  let ?A = "{w \<in> space ?P. (p2e w :: 'a) $$ i \<le> x}"
  assume "i < DIM('a)"
  then have "?A = (\<Pi>\<^isub>E j\<in>{..<DIM('a)}. if i = j then {.. x} else UNIV)"
    using DIM_positive by (auto simp: space_PiM p2e_def split: split_if_asm)
  then show "?A \<in> sets ?P"
    by auto
qed

lemma lborel_eq_lborel_space:
  "(lborel :: 'a measure) = distr (\<Pi>\<^isub>M i\<in>{..<DIM('a::ordered_euclidean_space)}. lborel) borel p2e"
  (is "?B = ?D")
proof (rule lborel_eqI)
  show "sets ?D = sets borel" by simp
  let ?P = "(\<Pi>\<^isub>M i\<in>{..<DIM('a::ordered_euclidean_space)}. lborel)"
  fix a b :: 'a
  have *: "p2e -` {a .. b} \<inter> space ?P = (\<Pi>\<^isub>E i\<in>{..<DIM('a)}. {a $$ i .. b $$ i})"
    by (auto simp: Pi_iff eucl_le[where 'a='a] p2e_def space_PiM)
  have "emeasure ?P (p2e -` {a..b} \<inter> space ?P) = content {a..b}"
  proof cases
    assume "{a..b} \<noteq> {}"
    then have "a \<le> b"
      by (simp add: interval_ne_empty eucl_le[where 'a='a])
    then have "emeasure lborel {a..b} = (\<Prod>x<DIM('a). emeasure lborel {a $$ x .. b $$ x})"
      by (auto simp: content_closed_interval eucl_le[where 'a='a]
               intro!: setprod_ereal[symmetric])
    also have "\<dots> = emeasure ?P (p2e -` {a..b} \<inter> space ?P)"
      unfolding * by (subst lborel_space.measure_times) auto
    finally show ?thesis by simp
  qed simp
  then show "emeasure ?D {a .. b} = content {a .. b}"
    by (simp add: emeasure_distr measurable_p2e)
qed

lemma borel_fubini_positiv_integral:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> ereal"
  assumes f: "f \<in> borel_measurable borel"
  shows "integral\<^isup>P lborel f = \<integral>\<^isup>+x. f (p2e x) \<partial>(\<Pi>\<^isub>M i\<in>{..<DIM('a)}. lborel)"
  by (subst lborel_eq_lborel_space) (simp add: positive_integral_distr measurable_p2e f)

lemma borel_fubini_integrable:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> real"
  shows "integrable lborel f \<longleftrightarrow>
    integrable (\<Pi>\<^isub>M i\<in>{..<DIM('a)}. lborel) (\<lambda>x. f (p2e x))"
    (is "_ \<longleftrightarrow> integrable ?B ?f")
proof
  assume "integrable lborel f"
  moreover then have f: "f \<in> borel_measurable borel"
    by auto
  moreover with measurable_p2e
  have "f \<circ> p2e \<in> borel_measurable ?B"
    by (rule measurable_comp)
  ultimately show "integrable ?B ?f"
    by (simp add: comp_def borel_fubini_positiv_integral integrable_def)
next
  assume "integrable ?B ?f"
  moreover
  then have "?f \<circ> e2p \<in> borel_measurable (borel::'a measure)"
    by (auto intro!: measurable_e2p)
  then have "f \<in> borel_measurable borel"
    by (simp cong: measurable_cong)
  ultimately show "integrable lborel f"
    by (simp add: borel_fubini_positiv_integral integrable_def)
qed

lemma borel_fubini:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel"
  shows "integral\<^isup>L lborel f = \<integral>x. f (p2e x) \<partial>((\<Pi>\<^isub>M i\<in>{..<DIM('a)}. lborel))"
  using f by (simp add: borel_fubini_positiv_integral lebesgue_integral_def)

end
