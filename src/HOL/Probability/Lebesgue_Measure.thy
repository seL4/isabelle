(*  Title:      HOL/Probability/Lebesgue_Measure.thy
    Author:     Johannes Hölzl, TU München
    Author:     Robert Himmelmann, TU München
*)

header {* Lebsegue measure *}

theory Lebesgue_Measure
  imports Finite_Product_Measure
begin

subsection {* Standard Cubes *}

definition cube :: "nat \<Rightarrow> 'a::ordered_euclidean_space set" where
  "cube n \<equiv> {\<chi>\<chi> i. - real n .. \<chi>\<chi> i. real n}"

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
  unfolding cube_def_raw subset_eq apply safe unfolding mem_interval by auto

subsection {* Lebesgue measure *} 

definition lebesgue :: "'a::ordered_euclidean_space measure_space" where
  "lebesgue = \<lparr> space = UNIV,
    sets = {A. \<forall>n. (indicator A :: 'a \<Rightarrow> real) integrable_on cube n},
    measure = \<lambda>A. SUP n. ereal (integral (cube n) (indicator A)) \<rparr>"

lemma space_lebesgue[simp]: "space lebesgue = UNIV"
  unfolding lebesgue_def by simp

lemma lebesgueD: "A \<in> sets lebesgue \<Longrightarrow> (indicator A :: _ \<Rightarrow> real) integrable_on cube n"
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

interpretation lebesgue: sigma_algebra lebesgue
proof (intro sigma_algebra_iff2[THEN iffD2] conjI allI ballI impI lebesgueI)
  fix A n assume A: "A \<in> sets lebesgue"
  have "indicator (space lebesgue - A) = (\<lambda>x. 1 - indicator A x :: real)"
    by (auto simp: fun_eq_iff indicator_def)
  then show "(indicator (space lebesgue - A) :: _ \<Rightarrow> real) integrable_on cube n"
    using A by (auto intro!: integrable_sub dest: lebesgueD simp: cube_def)
next
  fix n show "(indicator {} :: _\<Rightarrow>real) integrable_on cube n"
    by (auto simp: cube_def indicator_def_raw)
next
  fix A :: "nat \<Rightarrow> 'a set" and n ::nat assume "range A \<subseteq> sets lebesgue"
  then have A: "\<And>i. (indicator (A i) :: _ \<Rightarrow> real) integrable_on cube n"
    by (auto dest: lebesgueD)
  show "(indicator (\<Union>i. A i) :: _ \<Rightarrow> real) integrable_on cube n" (is "?g integrable_on _")
  proof (intro dominated_convergence[where g="?g"] ballI)
    fix k show "(indicator (\<Union>i<k. A i) :: _ \<Rightarrow> real) integrable_on cube n"
    proof (induct k)
      case (Suc k)
      have *: "(\<Union> i<Suc k. A i) = (\<Union> i<k. A i) \<union> A k"
        unfolding lessThan_Suc UN_insert by auto
      have *: "(\<lambda>x. max (indicator (\<Union> i<k. A i) x) (indicator (A k) x) :: real) =
          indicator (\<Union> i<Suc k. A i)" (is "(\<lambda>x. max (?f x) (?g x)) = _")
        by (auto simp: fun_eq_iff * indicator_def)
      show ?case
        using absolutely_integrable_max[of ?f "cube n" ?g] A Suc by (simp add: *)
    qed auto
  qed (auto intro: LIMSEQ_indicator_UN simp: cube_def)
qed simp

interpretation lebesgue: measure_space lebesgue
proof
  have *: "indicator {} = (\<lambda>x. 0 :: real)" by (simp add: fun_eq_iff)
  show "positive lebesgue (measure lebesgue)"
  proof (unfold positive_def, safe)
    show "measure lebesgue {} = 0" by (simp add: integral_0 * lebesgue_def)
    fix A assume "A \<in> sets lebesgue"
    then show "0 \<le> measure lebesgue A"
      unfolding lebesgue_def
      by (auto intro!: SUP_upper2 integral_nonneg)
  qed
next
  show "countably_additive lebesgue (measure lebesgue)"
  proof (intro countably_additive_def[THEN iffD2] allI impI)
    fix A :: "nat \<Rightarrow> 'b set" assume rA: "range A \<subseteq> sets lebesgue" "disjoint_family A"
    then have A[simp, intro]: "\<And>i n. (indicator (A i) :: _ \<Rightarrow> real) integrable_on cube n"
      by (auto dest: lebesgueD)
    let ?m = "\<lambda>n i. integral (cube n) (indicator (A i) :: _\<Rightarrow>real)"
    let ?M = "\<lambda>n I. integral (cube n) (indicator (\<Union>i\<in>I. A i) :: _\<Rightarrow>real)"
    have nn[simp, intro]: "\<And>i n. 0 \<le> ?m n i" by (auto intro!: integral_nonneg)
    assume "(\<Union>i. A i) \<in> sets lebesgue"
    then have UN_A[simp, intro]: "\<And>i n. (indicator (\<Union>i. A i) :: _ \<Rightarrow> real) integrable_on cube n"
      by (auto dest: lebesgueD)
    show "(\<Sum>n. measure lebesgue (A n)) = measure lebesgue (\<Union>i. A i)"
    proof (simp add: lebesgue_def, subst suminf_SUP_eq, safe intro!: incseq_SucI)
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
              using Suc A by (simp add: integral_add[symmetric])
          qed auto }
        ultimately show "(\<lambda>m. \<Sum>x = 0..<m. ?m n x) ----> ?M n UNIV"
          by (simp add: atLeast0LessThan)
      qed
    qed
  qed
qed

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
    unfolding indicator_def_raw has_integral_restrict_univ ..
  finally show ?thesis
    using has_integral_const[of "1::real" "?N" "?P"] by simp
qed

lemma lebesgueI_borel[intro, simp]:
  fixes s::"'a::ordered_euclidean_space set"
  assumes "s \<in> sets borel" shows "s \<in> sets lebesgue"
proof -
  let ?S = "range (\<lambda>(a, b). {a .. (b :: 'a\<Colon>ordered_euclidean_space)})"
  have *:"?S \<subseteq> sets lebesgue"
  proof (safe intro!: lebesgueI)
    fix n :: nat and a b :: 'a
    let ?N = "\<chi>\<chi> i. max (- real n) (a $$ i)"
    let ?P = "\<chi>\<chi> i. min (real n) (b $$ i)"
    show "(indicator {a..b} :: 'a\<Rightarrow>real) integrable_on cube n"
      unfolding integrable_on_def
      using has_integral_interval_cube[of a b] by auto
  qed
  have "s \<in> sigma_sets UNIV ?S" using assms
    unfolding borel_eq_atLeastAtMost by (simp add: sigma_def)
  thus ?thesis
    using lebesgue.sigma_subset[of "\<lparr> space = UNIV, sets = ?S\<rparr>", simplified, OF *]
    by (auto simp: sigma_def)
qed

lemma lebesgueI_negligible[dest]: fixes s::"'a::ordered_euclidean_space set"
  assumes "negligible s" shows "s \<in> sets lebesgue"
  using assms by (force simp: cube_def integrable_on_def negligible_def intro!: lebesgueI)

lemma lmeasure_eq_0:
  fixes S :: "'a::ordered_euclidean_space set" assumes "negligible S" shows "lebesgue.\<mu> S = 0"
proof -
  have "\<And>n. integral (cube n) (indicator S :: 'a\<Rightarrow>real) = 0"
    unfolding lebesgue_integral_def using assms
    by (intro integral_unique some1_equality ex_ex1I)
       (auto simp: cube_def negligible_def)
  then show ?thesis by (auto simp: lebesgue_def)
qed

lemma lmeasure_iff_LIMSEQ:
  assumes "A \<in> sets lebesgue" "0 \<le> m"
  shows "lebesgue.\<mu> A = ereal m \<longleftrightarrow> (\<lambda>n. integral (cube n) (indicator A :: _ \<Rightarrow> real)) ----> m"
proof (simp add: lebesgue_def, intro SUP_eq_LIMSEQ)
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
  assumes "s \<in> sets lebesgue" "lebesgue.\<mu> s = ereal m" "0 \<le> m"
  shows "(indicator s has_integral m) UNIV"
proof -
  let ?I = "indicator :: 'a set \<Rightarrow> 'a \<Rightarrow> real"
  have **: "(?I s) integrable_on UNIV \<and> (\<lambda>k. integral UNIV (?I (s \<inter> cube k))) ----> integral UNIV (?I s)"
  proof (intro monotone_convergence_increasing allI ballI)
    have LIMSEQ: "(\<lambda>n. integral (cube n) (?I s)) ----> m"
      using assms(2) unfolding lmeasure_iff_LIMSEQ[OF assms(1, 3)] .
    { fix n have "integral (cube n) (?I s) \<le> m"
        using cube_subset assms
        by (intro incseq_le[where L=m] LIMSEQ incseq_def[THEN iffD2] integral_subset_le allI impI)
           (auto dest!: lebesgueD) }
    moreover
    { fix n have "0 \<le> integral (cube n) (?I s)"
      using assms by (auto dest!: lebesgueD intro!: integral_nonneg) }
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
    using assms(2) unfolding lmeasure_iff_LIMSEQ[OF assms(1,3)] integral_indicator_UNIV .
  show ?thesis
    unfolding m by (intro integrable_integral **)
qed

lemma lmeasure_finite_integrable: assumes s: "s \<in> sets lebesgue" and "lebesgue.\<mu> s \<noteq> \<infinity>"
  shows "(indicator s :: _ \<Rightarrow> real) integrable_on UNIV"
proof (cases "lebesgue.\<mu> s")
  case (real m)
  with lmeasure_finite_has_integral[OF `s \<in> sets lebesgue` this]
    lebesgue.positive_measure[OF s]
  show ?thesis unfolding integrable_on_def by auto
qed (insert assms lebesgue.positive_measure[OF s], auto)

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
  shows "lebesgue.\<mu> s = ereal m"
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
  "(indicator A has_integral m) UNIV \<longleftrightarrow> (A \<in> sets lebesgue \<and> 0 \<le> m \<and> lebesgue.\<mu> A = ereal m)"
proof
  assume "(indicator A has_integral m) UNIV"
  with has_integral_lmeasure[OF this] has_integral_lebesgue[OF this]
  show "A \<in> sets lebesgue \<and> 0 \<le> m \<and> lebesgue.\<mu> A = ereal m"
    by (auto intro: has_integral_nonneg)
next
  assume "A \<in> sets lebesgue \<and> 0 \<le> m \<and> lebesgue.\<mu> A = ereal m"
  then show "(indicator A has_integral m) UNIV" by (intro lmeasure_finite_has_integral) auto
qed

lemma lmeasure_eq_integral: assumes "(indicator s::_\<Rightarrow>real) integrable_on UNIV"
  shows "lebesgue.\<mu> s = ereal (integral UNIV (indicator s))"
  using assms unfolding integrable_on_def
proof safe
  fix y :: real assume "(indicator s has_integral y) UNIV"
  from this[unfolded has_integral_iff_lmeasure] integral_unique[OF this]
  show "lebesgue.\<mu> s = ereal (integral UNIV (indicator s))" by simp
qed

lemma lebesgue_simple_function_indicator:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> ereal"
  assumes f:"simple_function lebesgue f"
  shows "f = (\<lambda>x. (\<Sum>y \<in> f ` UNIV. y * indicator (f -` {y}) x))"
  by (rule, subst lebesgue.simple_function_indicator_representation[OF f]) auto

lemma integral_eq_lmeasure:
  "(indicator s::_\<Rightarrow>real) integrable_on UNIV \<Longrightarrow> integral UNIV (indicator s) = real (lebesgue.\<mu> s)"
  by (subst lmeasure_eq_integral) (auto intro!: integral_nonneg)

lemma lmeasure_finite: assumes "(indicator s::_\<Rightarrow>real) integrable_on UNIV" shows "lebesgue.\<mu> s \<noteq> \<infinity>"
  using lmeasure_eq_integral[OF assms] by auto

lemma negligible_iff_lebesgue_null_sets:
  "negligible A \<longleftrightarrow> A \<in> lebesgue.null_sets"
proof
  assume "negligible A"
  from this[THEN lebesgueI_negligible] this[THEN lmeasure_eq_0]
  show "A \<in> lebesgue.null_sets" by auto
next
  assume A: "A \<in> lebesgue.null_sets"
  then have *:"((indicator A) has_integral (0::real)) UNIV" using lmeasure_finite_has_integral[of A] by auto
  show "negligible A" unfolding negligible_def
  proof (intro allI)
    fix a b :: 'a
    have integrable: "(indicator A :: _\<Rightarrow>real) integrable_on {a..b}"
      by (intro integrable_on_subinterval has_integral_integrable) (auto intro: *)
    then have "integral {a..b} (indicator A) \<le> (integral UNIV (indicator A) :: real)"
      using * by (auto intro!: integral_subset_le has_integral_integrable)
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

lemma lmeasure_UNIV[intro]: "lebesgue.\<mu> (UNIV::'a::ordered_euclidean_space set) = \<infinity>"
proof (simp add: lebesgue_def, intro SUP_PInfty bexI)
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

lemma
  fixes a b ::"'a::ordered_euclidean_space"
  shows lmeasure_atLeastAtMost[simp]: "lebesgue.\<mu> {a..b} = ereal (content {a..b})"
proof -
  have "(indicator (UNIV \<inter> {a..b})::_\<Rightarrow>real) integrable_on UNIV"
    unfolding integrable_indicator_UNIV by (simp add: integrable_const indicator_def_raw)
  from lmeasure_eq_integral[OF this] show ?thesis unfolding integral_indicator_UNIV
    by (simp add: indicator_def_raw)
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
  fixes a :: "'a::ordered_euclidean_space" shows "lebesgue.\<mu> {a} = 0"
  using lmeasure_atLeastAtMost[of a a] by simp

declare content_real[simp]

lemma
  fixes a b :: real
  shows lmeasure_real_greaterThanAtMost[simp]:
    "lebesgue.\<mu> {a <.. b} = ereal (if a \<le> b then b - a else 0)"
proof cases
  assume "a < b"
  then have "lebesgue.\<mu> {a <.. b} = lebesgue.\<mu> {a .. b} - lebesgue.\<mu> {a}"
    by (subst lebesgue.measure_Diff[symmetric])
       (auto intro!: arg_cong[where f=lebesgue.\<mu>])
  then show ?thesis by auto
qed auto

lemma
  fixes a b :: real
  shows lmeasure_real_atLeastLessThan[simp]:
    "lebesgue.\<mu> {a ..< b} = ereal (if a \<le> b then b - a else 0)"
proof cases
  assume "a < b"
  then have "lebesgue.\<mu> {a ..< b} = lebesgue.\<mu> {a .. b} - lebesgue.\<mu> {b}"
    by (subst lebesgue.measure_Diff[symmetric])
       (auto intro!: arg_cong[where f=lebesgue.\<mu>])
  then show ?thesis by auto
qed auto

lemma
  fixes a b :: real
  shows lmeasure_real_greaterThanLessThan[simp]:
    "lebesgue.\<mu> {a <..< b} = ereal (if a \<le> b then b - a else 0)"
proof cases
  assume "a < b"
  then have "lebesgue.\<mu> {a <..< b} = lebesgue.\<mu> {a <.. b} - lebesgue.\<mu> {b}"
    by (subst lebesgue.measure_Diff[symmetric])
       (auto intro!: arg_cong[where f=lebesgue.\<mu>])
  then show ?thesis by auto
qed auto

subsection {* Lebesgue-Borel measure *}

definition "lborel = lebesgue \<lparr> sets := sets borel \<rparr>"

lemma
  shows space_lborel[simp]: "space lborel = UNIV"
  and sets_lborel[simp]: "sets lborel = sets borel"
  and measure_lborel[simp]: "measure lborel = lebesgue.\<mu>"
  and measurable_lborel[simp]: "measurable lborel = measurable borel"
  by (simp_all add: measurable_def_raw lborel_def)

interpretation lborel: measure_space "lborel :: ('a::ordered_euclidean_space) measure_space"
  where "space lborel = UNIV"
  and "sets lborel = sets borel"
  and "measure lborel = lebesgue.\<mu>"
  and "measurable lborel = measurable borel"
proof (rule lebesgue.measure_space_subalgebra)
  have "sigma_algebra (lborel::'a measure_space) \<longleftrightarrow> sigma_algebra (borel::'a algebra)"
    unfolding sigma_algebra_iff2 lborel_def by simp
  then show "sigma_algebra (lborel::'a measure_space)" by simp default
qed auto

interpretation lborel: sigma_finite_measure lborel
  where "space lborel = UNIV"
  and "sets lborel = sets borel"
  and "measure lborel = lebesgue.\<mu>"
  and "measurable lborel = measurable borel"
proof -
  show "sigma_finite_measure lborel"
  proof (default, intro conjI exI[of _ "\<lambda>n. cube n"])
    show "range cube \<subseteq> sets lborel" by (auto intro: borel_closed)
    { fix x have "\<exists>n. x\<in>cube n" using mem_big_cube by auto }
    thus "(\<Union>i. cube i) = space lborel" by auto
    show "\<forall>i. measure lborel (cube i) \<noteq> \<infinity>" by (simp add: cube_def)
  qed
qed simp_all

interpretation lebesgue: sigma_finite_measure lebesgue
proof
  from lborel.sigma_finite guess A ..
  moreover then have "range A \<subseteq> sets lebesgue" using lebesgueI_borel by blast
  ultimately show "\<exists>A::nat \<Rightarrow> 'b set. range A \<subseteq> sets lebesgue \<and> (\<Union>i. A i) = space lebesgue \<and> (\<forall>i. lebesgue.\<mu> (A i) \<noteq> \<infinity>)"
    by auto
qed

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
  and om:"\<And>x. x \<in> range f \<Longrightarrow> lebesgue.\<mu> (f -` {x} \<inter> UNIV) = \<infinity> \<Longrightarrow> x = 0"
  shows "((\<lambda>x. real (f x)) has_integral (real (integral\<^isup>S lebesgue f))) UNIV"
  unfolding simple_integral_def space_lebesgue
proof (subst lebesgue_simple_function_indicator)
  let ?M = "\<lambda>x. lebesgue.\<mu> (f -` {x} \<inter> UNIV)"
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
      with subsetD[OF f' x] f[THEN lebesgue.simple_functionD(2)] show ?thesis
        by (cases rule: ereal2_cases[of x "?M x"]) auto
    qed simp }
  ultimately
  have "((\<lambda>x. real (\<Sum>y\<in>range f. y * ?F y x)) has_integral real (\<Sum>x\<in>range f. x * ?M x)) UNIV \<longleftrightarrow>
    ((\<lambda>x. \<Sum>y\<in>range f. real y * ?F y x) has_integral (\<Sum>x\<in>range f. real x * real (?M x))) UNIV"
    by simp
  also have \<dots>
  proof (intro has_integral_setsum has_integral_cmult_real lmeasure_finite_has_integral
               real_of_ereal_pos lebesgue.positive_measure ballI)
    show *: "finite (range f)" "\<And>y. f -` {y} \<in> sets lebesgue" "\<And>y. f -` {y} \<inter> UNIV \<in> sets lebesgue"
      using lebesgue.simple_functionD[OF f] by auto
    fix y assume "real y \<noteq> 0" "y \<in> range f"
    with * om[OF this(2)] show "lebesgue.\<mu> (f -` {y}) = ereal (real (?M y))"
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
  note f(1)[THEN lebesgue.simple_functionD(2)]
  then have [simp, intro]: "\<And>X. f -` X \<in> sets lebesgue" by auto
  have f': "simple_function lebesgue ?f"
    using f by (intro lebesgue.simple_function_If_set) auto
  have rng: "range ?f \<subseteq> {0..<\<infinity>}" using f by auto
  have "AE x in lebesgue. f x = ?f x"
    using lebesgue.simple_integral_PInf[OF f i]
    by (intro lebesgue.AE_I[where N="f -` {\<infinity>} \<inter> space lebesgue"]) auto
  from f(1) f' this have eq: "integral\<^isup>S lebesgue f = integral\<^isup>S lebesgue ?f"
    by (rule lebesgue.simple_integral_cong_AE)
  have real_eq: "\<And>x. real (f x) = real (?f x)" by auto

  show ?thesis
    unfolding eq real_eq
  proof (rule simple_function_has_integral[OF f' rng])
    fix x assume x: "x \<in> range ?f" and inf: "lebesgue.\<mu> (?f -` {x} \<inter> UNIV) = \<infinity>"
    have "x * lebesgue.\<mu> (?f -` {x} \<inter> UNIV) = (\<integral>\<^isup>S y. x * indicator (?f -` {x}) y \<partial>lebesgue)"
      using f'[THEN lebesgue.simple_functionD(2)]
      by (simp add: lebesgue.simple_integral_cmult_indicator)
    also have "\<dots> \<le> integral\<^isup>S lebesgue f"
      using f'[THEN lebesgue.simple_functionD(2)] f
      by (intro lebesgue.simple_integral_mono lebesgue.simple_function_mult lebesgue.simple_function_indicator)
         (auto split: split_indicator)
    finally show "x = 0" unfolding inf using i subsetD[OF rng x] by (auto split: split_if_asm)
  qed
qed

lemma positive_integral_has_integral:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> ereal"
  assumes f: "f \<in> borel_measurable lebesgue" "range f \<subseteq> {0..<\<infinity>}" "integral\<^isup>P lebesgue f \<noteq> \<infinity>"
  shows "((\<lambda>x. real (f x)) has_integral (real (integral\<^isup>P lebesgue f))) UNIV"
proof -
  from lebesgue.borel_measurable_implies_simple_function_sequence'[OF f(1)]
  guess u . note u = this
  have SUP_eq: "\<And>x. (SUP i. u i x) = f x"
    using u(4) f(2)[THEN subsetD] by (auto split: split_max)
  let ?u = "\<lambda>i x. real (u i x)"
  note u_eq = lebesgue.positive_integral_eq_simple_integral[OF u(1,5), symmetric]
  { fix i
    note u_eq
    also have "integral\<^isup>P lebesgue (u i) \<le> (\<integral>\<^isup>+x. max 0 (f x) \<partial>lebesgue)"
      by (intro lebesgue.positive_integral_mono) (auto intro: SUP_upper simp: u(4)[symmetric])
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
        using lebesgue.positive_integral_eq_simple_integral[OF u(1,5)] by simp
      also have "\<dots> \<le> real (integral\<^isup>P lebesgue f)" using f
        by (auto intro!: real_of_ereal_positive_mono lebesgue.positive_integral_positive
             lebesgue.positive_integral_mono SUP_upper simp: SUP_eq[symmetric])
      finally show "\<bar>integral UNIV (u' k)\<bar> \<le> real (integral\<^isup>P lebesgue f)" .
    qed
  qed

  have "integral\<^isup>P lebesgue f = ereal (integral UNIV f')"
  proof (rule tendsto_unique[OF trivial_limit_sequentially])
    have "(\<lambda>i. integral\<^isup>S lebesgue (u i)) ----> (SUP i. integral\<^isup>P lebesgue (u i))"
      unfolding u_eq by (intro LIMSEQ_ereal_SUPR lebesgue.incseq_positive_integral u)
    also note lebesgue.positive_integral_monotone_convergence_SUP
      [OF u(2)  lebesgue.borel_measurable_simple_function[OF u(1)] u(5), symmetric]
    finally show "(\<lambda>k. integral\<^isup>S lebesgue (u k)) ----> integral\<^isup>P lebesgue f"
      unfolding SUP_eq .

    { fix k
      have "0 \<le> integral\<^isup>S lebesgue (u k)"
        using u by (auto intro!: lebesgue.simple_integral_positive)
      then have "integral\<^isup>S lebesgue (u k) = ereal (real (integral\<^isup>S lebesgue (u k)))"
        using u_fin by (auto simp: ereal_real) }
    note * = this
    show "(\<lambda>k. integral\<^isup>S lebesgue (u k)) ----> ereal (integral UNIV f')"
      using convergent using u_int[THEN integral_unique, symmetric]
      by (subst *) (simp add: lim_ereal u')
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
  { fix f have "(\<integral>\<^isup>+ x. ereal (f x) \<partial>lebesgue) = (\<integral>\<^isup>+ x. ereal (max 0 (f x)) \<partial>lebesgue)"
      by (intro lebesgue.positive_integral_cong_pos) (auto split: split_max) }
  note eq = this
  show ?thesis
    unfolding lebesgue_integral_def
    apply (subst *)
    apply (rule has_integral_sub)
    unfolding eq[of f] eq[of "\<lambda>x. - f x"]
    apply (safe intro!: positive_integral_has_integral)
    using integrableD[OF f]
    by (auto simp: zero_ereal_def[symmetric] positive_integral_max_0  split: split_max
             intro!: lebesgue.measurable_If lebesgue.borel_measurable_ereal)
qed

lemma lebesgue_positive_integral_eq_borel:
  assumes f: "f \<in> borel_measurable borel"
  shows "integral\<^isup>P lebesgue f = integral\<^isup>P lborel f"
proof -
  from f have "integral\<^isup>P lebesgue (\<lambda>x. max 0 (f x)) = integral\<^isup>P lborel (\<lambda>x. max 0 (f x))"
    by (auto intro!: lebesgue.positive_integral_subalgebra[symmetric]) default
  then show ?thesis unfolding positive_integral_max_0 .
qed

lemma lebesgue_integral_eq_borel:
  assumes "f \<in> borel_measurable borel"
  shows "integrable lebesgue f \<longleftrightarrow> integrable lborel f" (is ?P)
    and "integral\<^isup>L lebesgue f = integral\<^isup>L lborel f" (is ?I)
proof -
  have *: "sigma_algebra lborel" by default
  have "sets lborel \<subseteq> sets lebesgue" by auto
  from lebesgue.integral_subalgebra[of f lborel, OF _ this _ _ *] assms
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

interpretation lborel_product: product_sigma_finite "\<lambda>x. lborel::real measure_space"
  by default

interpretation lborel_space: finite_product_sigma_finite "\<lambda>x. lborel::real measure_space" "{..<n}" for n :: nat
  where "space lborel = UNIV"
  and "sets lborel = sets borel"
  and "measure lborel = lebesgue.\<mu>"
  and "measurable lborel = measurable borel"
proof -
  show "finite_product_sigma_finite (\<lambda>x. lborel::real measure_space) {..<n}"
    by default simp
qed simp_all

lemma sets_product_borel:
  assumes [intro]: "finite I"
  shows "sets (\<Pi>\<^isub>M i\<in>I.
     \<lparr> space = UNIV::real set, sets = range lessThan, measure = lebesgue.\<mu> \<rparr>) =
   sets (\<Pi>\<^isub>M i\<in>I. lborel)" (is "sets ?G = _")
proof -
  have "sets ?G = sets (\<Pi>\<^isub>M i\<in>I.
       sigma \<lparr> space = UNIV::real set, sets = range lessThan, measure = lebesgue.\<mu> \<rparr>)"
    by (subst sigma_product_algebra_sigma_eq[of I "\<lambda>_ i. {..<real i}" ])
       (auto intro!: measurable_sigma_sigma incseq_SucI reals_Archimedean2
             simp: product_algebra_def)
  then show ?thesis
    unfolding lborel_def borel_eq_lessThan lebesgue_def sigma_def by simp
qed

lemma measurable_e2p:
  "e2p \<in> measurable (borel::'a::ordered_euclidean_space algebra)
                    (\<Pi>\<^isub>M i\<in>{..<DIM('a)}. (lborel :: real measure_space))"
    (is "_ \<in> measurable ?E ?P")
proof -
  let ?B = "\<lparr> space = UNIV::real set, sets = range lessThan, measure = lebesgue.\<mu> \<rparr>"
  let ?G = "product_algebra_generator {..<DIM('a)} (\<lambda>_. ?B)"
  have "e2p \<in> measurable ?E (sigma ?G)"
  proof (rule borel.measurable_sigma)
    show "e2p \<in> space ?E \<rightarrow> space ?G" by (auto simp: e2p_def)
    fix A assume "A \<in> sets ?G"
    then obtain E where A: "A = (\<Pi>\<^isub>E i\<in>{..<DIM('a)}. E i)"
      and "E \<in> {..<DIM('a)} \<rightarrow> (range lessThan)"
      by (auto elim!: product_algebraE simp: )
    then have "\<forall>i\<in>{..<DIM('a)}. \<exists>xs. E i = {..< xs}" by auto
    from this[THEN bchoice] guess xs ..
    then have A_eq: "A = (\<Pi>\<^isub>E i\<in>{..<DIM('a)}. {..< xs i})"
      using A by auto
    have "e2p -` A = {..< (\<chi>\<chi> i. xs i) :: 'a}"
      using DIM_positive by (auto simp add: Pi_iff set_eq_iff e2p_def A_eq
        euclidean_eq[where 'a='a] eucl_less[where 'a='a])
    then show "e2p -` A \<inter> space ?E \<in> sets ?E" by simp
  qed (auto simp: product_algebra_generator_def)
  with sets_product_borel[of "{..<DIM('a)}"] show ?thesis
    unfolding measurable_def product_algebra_def by simp
qed

lemma measurable_p2e:
  "p2e \<in> measurable (\<Pi>\<^isub>M i\<in>{..<DIM('a)}. (lborel :: real measure_space))
    (borel :: 'a::ordered_euclidean_space algebra)"
  (is "p2e \<in> measurable ?P _")
  unfolding borel_eq_lessThan
proof (intro lborel_space.measurable_sigma)
  let ?E = "\<lparr> space = UNIV :: 'a set, sets = range lessThan \<rparr>"
  show "p2e \<in> space ?P \<rightarrow> space ?E" by simp
  fix A assume "A \<in> sets ?E"
  then obtain x where "A = {..<x}" by auto
  then have "p2e -` A \<inter> space ?P = (\<Pi>\<^isub>E i\<in>{..<DIM('a)}. {..< x $$ i})"
    using DIM_positive
    by (auto simp: Pi_iff set_eq_iff p2e_def
                   euclidean_eq[where 'a='a] eucl_less[where 'a='a])
  then show "p2e -` A \<inter> space ?P \<in> sets ?P" by auto
qed simp

lemma Int_stable_cuboids:
  fixes x::"'a::ordered_euclidean_space"
  shows "Int_stable \<lparr>space = UNIV, sets = range (\<lambda>(a, b::'a). {a..b})\<rparr>"
  by (auto simp: inter_interval Int_stable_def)

lemma lborel_eq_lborel_space:
  fixes A :: "('a::ordered_euclidean_space) set"
  assumes "A \<in> sets borel"
  shows "lborel.\<mu> A = lborel_space.\<mu> DIM('a) (p2e -` A \<inter> (space (lborel_space.P DIM('a))))"
    (is "_ = measure ?P (?T A)")
proof (rule measure_unique_Int_stable_vimage)
  show "measure_space ?P" by default
  show "measure_space lborel" by default

  let ?E = "\<lparr> space = UNIV :: 'a set, sets = range (\<lambda>(a,b). {a..b}) \<rparr>"
  show "Int_stable ?E" using Int_stable_cuboids .
  show "range cube \<subseteq> sets ?E" unfolding cube_def_raw by auto
  show "incseq cube" using cube_subset_Suc by (auto intro!: incseq_SucI)
  { fix x have "\<exists>n. x \<in> cube n" using mem_big_cube[of x] by fastforce }
  then show "(\<Union>i. cube i) = space ?E" by auto
  { fix i show "lborel.\<mu> (cube i) \<noteq> \<infinity>" unfolding cube_def by auto }
  show "A \<in> sets (sigma ?E)" "sets (sigma ?E) = sets lborel" "space ?E = space lborel"
    using assms by (simp_all add: borel_eq_atLeastAtMost)

  show "p2e \<in> measurable ?P (lborel :: 'a measure_space)"
    using measurable_p2e unfolding measurable_def by simp
  { fix X assume "X \<in> sets ?E"
    then obtain a b where X[simp]: "X = {a .. b}" by auto
    have *: "?T X = (\<Pi>\<^isub>E i\<in>{..<DIM('a)}. {a $$ i .. b $$ i})"
      by (auto simp: Pi_iff eucl_le[where 'a='a] p2e_def)
    show "lborel.\<mu> X = measure ?P (?T X)"
    proof cases
      assume "X \<noteq> {}"
      then have "a \<le> b"
        by (simp add: interval_ne_empty eucl_le[where 'a='a])
      then have "lborel.\<mu> X = (\<Prod>x<DIM('a). lborel.\<mu> {a $$ x .. b $$ x})"
        by (auto simp: content_closed_interval eucl_le[where 'a='a]
                 intro!: setprod_ereal[symmetric])
      also have "\<dots> = measure ?P (?T X)"
        unfolding * by (subst lborel_space.measure_times) auto
      finally show ?thesis .
    qed simp }
qed

lemma measure_preserving_p2e:
  "p2e \<in> measure_preserving (\<Pi>\<^isub>M i\<in>{..<DIM('a)}. (lborel :: real measure_space))
    (lborel::'a::ordered_euclidean_space measure_space)" (is "_ \<in> measure_preserving ?P ?E")
proof
  show "p2e \<in> measurable ?P ?E"
    using measurable_p2e by (simp add: measurable_def)
  fix A :: "'a set" assume "A \<in> sets lborel"
  then show "lborel_space.\<mu> DIM('a) (p2e -` A \<inter> (space (lborel_space.P DIM('a)))) = lborel.\<mu> A"
    by (intro lborel_eq_lborel_space[symmetric]) simp
qed

lemma lebesgue_eq_lborel_space_in_borel:
  fixes A :: "('a::ordered_euclidean_space) set"
  assumes A: "A \<in> sets borel"
  shows "lebesgue.\<mu> A = lborel_space.\<mu> DIM('a) (p2e -` A \<inter> (space (lborel_space.P DIM('a))))"
  using lborel_eq_lborel_space[OF A] by simp

lemma borel_fubini_positiv_integral:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> ereal"
  assumes f: "f \<in> borel_measurable borel"
  shows "integral\<^isup>P lborel f = \<integral>\<^isup>+x. f (p2e x) \<partial>(lborel_space.P DIM('a))"
proof (rule lborel_space.positive_integral_vimage[OF _ measure_preserving_p2e _])
  show "f \<in> borel_measurable lborel"
    using f by (simp_all add: measurable_def)
qed default

lemma borel_fubini_integrable:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> real"
  shows "integrable lborel f \<longleftrightarrow>
    integrable (lborel_space.P DIM('a)) (\<lambda>x. f (p2e x))"
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
  moreover then
  have "?f \<circ> e2p \<in> borel_measurable (borel::'a algebra)"
    by (auto intro!: measurable_e2p measurable_comp)
  then have "f \<in> borel_measurable borel"
    by (simp cong: measurable_cong)
  ultimately show "integrable lborel f"
    by (simp add: borel_fubini_positiv_integral integrable_def)
qed

lemma borel_fubini:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel"
  shows "integral\<^isup>L lborel f = \<integral>x. f (p2e x) \<partial>(lborel_space.P DIM('a))"
  using f by (simp add: borel_fubini_positiv_integral lebesgue_integral_def)


lemma Int_stable_atLeastAtMost:
  "Int_stable \<lparr>space = UNIV, sets = range (\<lambda>(a,b). {a::'a::ordered_euclidean_space .. b}) \<rparr>"
proof (simp add: Int_stable_def image_iff, intro allI)
  fix a1 b1 a2 b2 :: 'a
  have "\<forall>i<DIM('a). \<exists>a b. {a1$$i..b1$$i} \<inter> {a2$$i..b2$$i} = {a..b}" by auto
  then have "\<exists>a b. \<forall>i<DIM('a). {a1$$i..b1$$i} \<inter> {a2$$i..b2$$i} = {a i..b i}"
    unfolding choice_iff' .
  then guess a b by safe
  then have "{a1..b1} \<inter> {a2..b2} = {(\<chi>\<chi> i. a i) .. (\<chi>\<chi> i. b i)}"
    by (simp add: set_eq_iff eucl_le[where 'a='a] all_conj_distrib[symmetric]) blast
  then show "\<exists>a' b'. {a1..b1} \<inter> {a2..b2} = {a'..b'}" by blast
qed

lemma (in sigma_algebra) borel_measurable_sets:
  assumes "f \<in> measurable borel M" "A \<in> sets M"
  shows "f -` A \<in> sets borel"
  using measurable_sets[OF assms] by simp

lemma (in sigma_algebra) measurable_identity[intro,simp]:
  "(\<lambda>x. x) \<in> measurable M M"
  unfolding measurable_def by auto

lemma lebesgue_real_affine:
  fixes X :: "real set"
  assumes "X \<in> sets borel" and "c \<noteq> 0"
  shows "measure lebesgue X = ereal \<bar>c\<bar> * measure lebesgue ((\<lambda>x. t + c * x) -` X)"
    (is "_ = ?\<nu> X")
proof -
  let ?E = "\<lparr>space = UNIV, sets = range (\<lambda>(a,b). {a::real .. b})\<rparr> :: real algebra"
  let ?M = "\<lambda>\<nu>. \<lparr>space = space ?E, sets = sets (sigma ?E), measure = \<nu>\<rparr> :: real measure_space"
  have *: "?M (measure lebesgue) = lborel"
    unfolding borel_eq_atLeastAtMost[symmetric]
    by (simp add: lborel_def lebesgue_def)
  have **: "?M ?\<nu> = lborel \<lparr> measure := ?\<nu> \<rparr>"
    unfolding borel_eq_atLeastAtMost[symmetric]
    by (simp add: lborel_def lebesgue_def)
  show ?thesis
  proof (rule measure_unique_Int_stable[where X=X, OF Int_stable_atLeastAtMost], unfold * **)
    show "X \<in> sets (sigma ?E)"
      unfolding borel_eq_atLeastAtMost[symmetric] by fact
    have "\<And>x. \<exists>xa. x \<in> cube xa" apply(rule_tac x=x in mem_big_cube) by fastforce
    then show "(\<Union>i. cube i) = space ?E" by auto
    show "incseq cube" by (intro incseq_SucI cube_subset_Suc)
    show "range cube \<subseteq> sets ?E"
      unfolding cube_def_raw by auto
    show "\<And>i. measure lebesgue (cube i) \<noteq> \<infinity>"
      by (simp add: cube_def)
    show "measure_space lborel" by default
    then interpret sigma_algebra "lborel\<lparr>measure := ?\<nu>\<rparr>"
      by (auto simp add: measure_space_def)
    show "measure_space (lborel\<lparr>measure := ?\<nu>\<rparr>)"
    proof
      show "positive (lborel\<lparr>measure := ?\<nu>\<rparr>) (measure (lborel\<lparr>measure := ?\<nu>\<rparr>))"
        by (auto simp: positive_def intro!: ereal_0_le_mult borel.borel_measurable_sets)
      show "countably_additive (lborel\<lparr>measure := ?\<nu>\<rparr>) (measure (lborel\<lparr>measure := ?\<nu>\<rparr>))"
      proof (simp add: countably_additive_def, safe)
        fix A :: "nat \<Rightarrow> real set" assume A: "range A \<subseteq> sets borel" "disjoint_family A"
        then have Ai: "\<And>i. A i \<in> sets borel" by auto
        have "(\<Sum>n. measure lebesgue ((\<lambda>x. t + c * x) -` A n)) = measure lebesgue (\<Union>n. (\<lambda>x. t + c * x) -` A n)"
        proof (intro lborel.measure_countably_additive)
          { fix n have "(\<lambda>x. t + c * x) -` A n \<inter> space borel \<in> sets borel"
              using A borel.measurable_ident unfolding id_def
              by (intro measurable_sets[where A=borel] borel.borel_measurable_add[OF _ borel.borel_measurable_times]) auto }
          then show "range (\<lambda>i. (\<lambda>x. t + c * x) -` A i) \<subseteq> sets borel" by auto
          from `disjoint_family A`
          show "disjoint_family (\<lambda>i. (\<lambda>x. t + c * x) -` A i)"
            by (rule disjoint_family_on_bisimulation) auto
        qed
        with Ai show "(\<Sum>n. ?\<nu> (A n)) = ?\<nu> (UNION UNIV A)"
          by (subst suminf_cmult_ereal)
             (auto simp: vimage_UN borel.borel_measurable_sets)
      qed
    qed
    fix X assume "X \<in> sets ?E"
    then obtain a b where [simp]: "X = {a .. b}" by auto
    show "measure lebesgue X = ?\<nu> X"
    proof cases
      assume "0 < c"
      then have "(\<lambda>x. t + c * x) -` {a..b} = {(a - t) / c .. (b - t) / c}"
        by (auto simp: field_simps)
      with `0 < c` show ?thesis
        by (cases "a \<le> b") (auto simp: field_simps)
    next
      assume "\<not> 0 < c" with `c \<noteq> 0` have "c < 0" by auto
      then have *: "(\<lambda>x. t + c * x) -` {a..b} = {(b - t) / c .. (a - t) / c}"
        by (auto simp: field_simps)
      with `c < 0` show ?thesis
        by (cases "a \<le> b") (auto simp: field_simps)
    qed
  qed
qed

end
