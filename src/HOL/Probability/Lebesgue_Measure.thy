(*  Author: Robert Himmelmann, TU Muenchen *)
header {* Lebsegue measure *}
theory Lebesgue_Measure
  imports Product_Measure
begin

subsection {* Standard Cubes *}

definition cube :: "nat \<Rightarrow> 'a::ordered_euclidean_space set" where
  "cube n \<equiv> {\<chi>\<chi> i. - real n .. \<chi>\<chi> i. real n}"

lemma cube_closed[intro]: "closed (cube n)"
  unfolding cube_def by auto

lemma cube_subset[intro]: "n \<le> N \<Longrightarrow> cube n \<subseteq> cube N"
  by (fastsimp simp: eucl_le[where 'a='a] cube_def)

lemma cube_subset_iff:
  "cube n \<subseteq> cube N \<longleftrightarrow> n \<le> N"
proof
  assume subset: "cube n \<subseteq> (cube N::'a set)"
  then have "((\<chi>\<chi> i. real n)::'a) \<in> cube N"
    using DIM_positive[where 'a='a]
    by (fastsimp simp: cube_def eucl_le[where 'a='a])
  then show "n \<le> N"
    by (fastsimp simp: cube_def eucl_le[where 'a='a])
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
proof- from real_arch_lt[of "norm x"] guess n ..
  thus ?thesis apply-apply(rule that[where n=n])
    apply(rule ball_subset_cube[unfolded subset_eq,rule_format])
    by (auto simp add:dist_norm)
qed

lemma cube_subset_Suc[intro]: "cube n \<subseteq> cube (Suc n)"
  unfolding cube_def_raw subset_eq apply safe unfolding mem_interval by auto

lemma Pi_iff: "f \<in> Pi I X \<longleftrightarrow> (\<forall>i\<in>I. f i \<in> X i)"
  unfolding Pi_def by auto

subsection {* Lebesgue measure *}

definition lebesgue :: "'a::ordered_euclidean_space measure_space" where
  "lebesgue = \<lparr> space = UNIV,
    sets = {A. \<forall>n. (indicator A :: 'a \<Rightarrow> real) integrable_on cube n},
    measure = \<lambda>A. SUP n. Real (integral (cube n) (indicator A)) \<rparr>"

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
  show "measure lebesgue {} = 0" by (simp add: integral_0 * lebesgue_def)
next
  show "countably_additive lebesgue (measure lebesgue)"
  proof (intro countably_additive_def[THEN iffD2] allI impI)
    fix A :: "nat \<Rightarrow> 'b set" assume rA: "range A \<subseteq> sets lebesgue" "disjoint_family A"
    then have A[simp, intro]: "\<And>i n. (indicator (A i) :: _ \<Rightarrow> real) integrable_on cube n"
      by (auto dest: lebesgueD)
    let "?m n i" = "integral (cube n) (indicator (A i) :: _\<Rightarrow>real)"
    let "?M n I" = "integral (cube n) (indicator (\<Union>i\<in>I. A i) :: _\<Rightarrow>real)"
    have nn[simp, intro]: "\<And>i n. 0 \<le> ?m n i" by (auto intro!: integral_nonneg)
    assume "(\<Union>i. A i) \<in> sets lebesgue"
    then have UN_A[simp, intro]: "\<And>i n. (indicator (\<Union>i. A i) :: _ \<Rightarrow> real) integrable_on cube n"
      by (auto dest: lebesgueD)
    show "(\<Sum>\<^isub>\<infinity>n. measure lebesgue (A n)) = measure lebesgue (\<Union>i. A i)"
    proof (simp add: lebesgue_def, subst psuminf_SUP_eq)
      fix n i show "Real (?m n i) \<le> Real (?m (Suc n) i)"
        using cube_subset[of n "Suc n"] by (auto intro!: integral_subset_le)
    next
      show "(SUP n. \<Sum>\<^isub>\<infinity>i. Real (?m n i)) = (SUP n. Real (?M n UNIV))"
        unfolding psuminf_def
      proof (subst setsum_Real, (intro arg_cong[where f="SUPR UNIV"] ext ballI nn SUP_eq_LIMSEQ[THEN iffD2])+)
        fix n :: nat show "mono (\<lambda>m. \<Sum>x<m. ?m n x)"
        proof (intro mono_iff_le_Suc[THEN iffD2] allI)
          fix m show "(\<Sum>x<m. ?m n x) \<le> (\<Sum>x<Suc m. ?m n x)"
            using nn[of n m] by auto
        qed
        show "0 \<le> ?M n UNIV"
          using UN_A by (auto intro!: integral_nonneg)
        fix m show "0 \<le> (\<Sum>x<m. ?m n x)" by (auto intro!: setsum_nonneg)
      next
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
        ultimately show "(\<lambda>m. \<Sum>x<m. ?m n x) ----> ?M n UNIV"
          by simp
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
  shows "lebesgue.\<mu> A = Real m \<longleftrightarrow> (\<lambda>n. integral (cube n) (indicator A :: _ \<Rightarrow> real)) ----> m"
proof (simp add: lebesgue_def, intro SUP_eq_LIMSEQ)
  show "mono (\<lambda>n. integral (cube n) (indicator A::_=>real))"
    using cube_subset assms by (intro monoI integral_subset_le) (auto dest!: lebesgueD)
  fix n show "0 \<le> integral (cube n) (indicator A::_=>real)"
    using assms by (auto dest!: lebesgueD intro!: integral_nonneg)
qed fact

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
  assumes "s \<in> sets lebesgue" "lebesgue.\<mu> s = Real m" "0 \<le> m"
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

lemma lmeasure_finite_integrable: assumes "s \<in> sets lebesgue" "lebesgue.\<mu> s \<noteq> \<omega>"
  shows "(indicator s :: _ \<Rightarrow> real) integrable_on UNIV"
proof (cases "lebesgue.\<mu> s")
  case (preal m) from lmeasure_finite_has_integral[OF `s \<in> sets lebesgue` this]
  show ?thesis unfolding integrable_on_def by auto
qed (insert assms, auto)

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
  shows "lebesgue.\<mu> s = Real m"
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
  "(indicator A has_integral m) UNIV \<longleftrightarrow> (A \<in> sets lebesgue \<and> 0 \<le> m \<and> lebesgue.\<mu> A = Real m)"
proof
  assume "(indicator A has_integral m) UNIV"
  with has_integral_lmeasure[OF this] has_integral_lebesgue[OF this]
  show "A \<in> sets lebesgue \<and> 0 \<le> m \<and> lebesgue.\<mu> A = Real m"
    by (auto intro: has_integral_nonneg)
next
  assume "A \<in> sets lebesgue \<and> 0 \<le> m \<and> lebesgue.\<mu> A = Real m"
  then show "(indicator A has_integral m) UNIV" by (intro lmeasure_finite_has_integral) auto
qed

lemma lmeasure_eq_integral: assumes "(indicator s::_\<Rightarrow>real) integrable_on UNIV"
  shows "lebesgue.\<mu> s = Real (integral UNIV (indicator s))"
  using assms unfolding integrable_on_def
proof safe
  fix y :: real assume "(indicator s has_integral y) UNIV"
  from this[unfolded has_integral_iff_lmeasure] integral_unique[OF this]
  show "lebesgue.\<mu> s = Real (integral UNIV (indicator s))" by simp
qed

lemma lebesgue_simple_function_indicator:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> pextreal"
  assumes f:"simple_function lebesgue f"
  shows "f = (\<lambda>x. (\<Sum>y \<in> f ` UNIV. y * indicator (f -` {y}) x))"
  by (rule, subst lebesgue.simple_function_indicator_representation[OF f]) auto

lemma integral_eq_lmeasure:
  "(indicator s::_\<Rightarrow>real) integrable_on UNIV \<Longrightarrow> integral UNIV (indicator s) = real (lebesgue.\<mu> s)"
  by (subst lmeasure_eq_integral) (auto intro!: integral_nonneg)

lemma lmeasure_finite: assumes "(indicator s::_\<Rightarrow>real) integrable_on UNIV" shows "lebesgue.\<mu> s \<noteq> \<omega>"
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

lemma lmeasure_UNIV[intro]: "lebesgue.\<mu> (UNIV::'a::ordered_euclidean_space set) = \<omega>"
proof (simp add: lebesgue_def SUP_\<omega>, intro allI impI)
  fix x assume "x < \<omega>"
  then obtain r where r: "x = Real r" "0 \<le> r" by (cases x) auto
  then obtain n where n: "r < of_nat n" using ex_less_of_nat by auto
  show "\<exists>i. x < Real (integral (cube i) (indicator UNIV::'a\<Rightarrow>real))"
  proof (intro exI[of _ n])
    have [simp]: "indicator UNIV = (\<lambda>x. 1)" by (auto simp: fun_eq_iff)
    { fix m :: nat assume "0 < m" then have "real n \<le> (\<Prod>x<m. 2 * real n)"
      proof (induct m)
        case (Suc m)
        show ?case
        proof cases
          assume "m = 0" then show ?thesis by (simp add: lessThan_Suc)
        next
          assume "m \<noteq> 0" then have "real n \<le> (\<Prod>x<m. 2 * real n)" using Suc by auto
          then show ?thesis
            by (auto simp: lessThan_Suc field_simps mult_le_cancel_left1)
        qed
      qed auto } note this[OF DIM_positive[where 'a='a], simp]
    then have [simp]: "0 \<le> (\<Prod>x<DIM('a). 2 * real n)" using real_of_nat_ge_zero by arith
    have "x < Real (of_nat n)" using n r by auto
    also have "Real (of_nat n) \<le> Real (integral (cube n) (indicator UNIV::'a\<Rightarrow>real))"
      by (auto simp: real_eq_of_nat[symmetric] cube_def content_closed_interval_cases)
    finally show "x < Real (integral (cube n) (indicator UNIV::'a\<Rightarrow>real))" .
  qed
qed

lemma
  fixes a b ::"'a::ordered_euclidean_space"
  shows lmeasure_atLeastAtMost[simp]: "lebesgue.\<mu> {a..b} = Real (content {a..b})"
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
    "lebesgue.\<mu> {a <.. b} = Real (if a \<le> b then b - a else 0)"
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
    "lebesgue.\<mu> {a ..< b} = Real (if a \<le> b then b - a else 0)"
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
    "lebesgue.\<mu> {a <..< b} = Real (if a \<le> b then b - a else 0)"
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

interpretation lborel: measure_space lborel
  where "space lborel = UNIV"
  and "sets lborel = sets borel"
  and "measure lborel = lebesgue.\<mu>"
  and "measurable lborel = measurable borel"
proof -
  show "measure_space lborel"
  proof
    show "countably_additive lborel (measure lborel)"
      using lebesgue.ca unfolding countably_additive_def lborel_def
      apply safe apply (erule_tac x=A in allE) by auto
  qed (auto simp: lborel_def)
qed simp_all

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
    show "\<forall>i. measure lborel (cube i) \<noteq> \<omega>" by (simp add: cube_def)
  qed
qed simp_all

interpretation lebesgue: sigma_finite_measure lebesgue
proof
  from lborel.sigma_finite guess A ..
  moreover then have "range A \<subseteq> sets lebesgue" using lebesgueI_borel by blast
  ultimately show "\<exists>A::nat \<Rightarrow> 'b set. range A \<subseteq> sets lebesgue \<and> (\<Union>i. A i) = space lebesgue \<and> (\<forall>i. lebesgue.\<mu> (A i) \<noteq> \<omega>)"
    by auto
qed

subsection {* Lebesgue integrable implies Gauge integrable *}

lemma simple_function_has_integral:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> pextreal"
  assumes f:"simple_function lebesgue f"
  and f':"\<forall>x. f x \<noteq> \<omega>"
  and om:"\<forall>x\<in>range f. lebesgue.\<mu> (f -` {x} \<inter> UNIV) = \<omega> \<longrightarrow> x = 0"
  shows "((\<lambda>x. real (f x)) has_integral (real (integral\<^isup>S lebesgue f))) UNIV"
  unfolding simple_integral_def
  apply(subst lebesgue_simple_function_indicator[OF f])
proof -
  case goal1
  have *:"\<And>x. \<forall>y\<in>range f. y * indicator (f -` {y}) x \<noteq> \<omega>"
    "\<forall>x\<in>range f. x * lebesgue.\<mu> (f -` {x} \<inter> UNIV) \<noteq> \<omega>"
    using f' om unfolding indicator_def by auto
  show ?case unfolding space_lebesgue real_of_pextreal_setsum'[OF *(1),THEN sym]
    unfolding real_of_pextreal_setsum'[OF *(2),THEN sym]
    unfolding real_of_pextreal_setsum space_lebesgue
    apply(rule has_integral_setsum)
  proof safe show "finite (range f)" using f by (auto dest: lebesgue.simple_functionD)
    fix y::'a show "((\<lambda>x. real (f y * indicator (f -` {f y}) x)) has_integral
      real (f y * lebesgue.\<mu> (f -` {f y} \<inter> UNIV))) UNIV"
    proof(cases "f y = 0") case False
      have mea:"(indicator (f -` {f y}) ::_\<Rightarrow>real) integrable_on UNIV"
        apply(rule lmeasure_finite_integrable)
        using assms unfolding simple_function_def using False by auto
      have *:"\<And>x. real (indicator (f -` {f y}) x::pextreal) = (indicator (f -` {f y}) x)"
        by (auto simp: indicator_def)
      show ?thesis unfolding real_of_pextreal_mult[THEN sym]
        apply(rule has_integral_cmul[where 'b=real, unfolded real_scaleR_def])
        unfolding Int_UNIV_right lmeasure_eq_integral[OF mea,THEN sym]
        unfolding integral_eq_lmeasure[OF mea, symmetric] *
        apply(rule integrable_integral) using mea .
    qed auto
  qed
qed

lemma bounded_realI: assumes "\<forall>x\<in>s. abs (x::real) \<le> B" shows "bounded s"
  unfolding bounded_def dist_real_def apply(rule_tac x=0 in exI)
  using assms by auto

lemma simple_function_has_integral':
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> pextreal"
  assumes f:"simple_function lebesgue f"
  and i: "integral\<^isup>S lebesgue f \<noteq> \<omega>"
  shows "((\<lambda>x. real (f x)) has_integral (real (integral\<^isup>S lebesgue f))) UNIV"
proof- let ?f = "\<lambda>x. if f x = \<omega> then 0 else f x"
  { fix x have "real (f x) = real (?f x)" by (cases "f x") auto } note * = this
  have **:"{x. f x \<noteq> ?f x} = f -` {\<omega>}" by auto
  have **:"lebesgue.\<mu> {x\<in>space lebesgue. f x \<noteq> ?f x} = 0"
    using lebesgue.simple_integral_omega[OF assms] by(auto simp add:**)
  show ?thesis apply(subst lebesgue.simple_integral_cong'[OF f _ **])
    apply(rule lebesgue.simple_function_compose1[OF f])
    unfolding * defer apply(rule simple_function_has_integral)
  proof-
    show "simple_function lebesgue ?f"
      using lebesgue.simple_function_compose1[OF f] .
    show "\<forall>x. ?f x \<noteq> \<omega>" by auto
    show "\<forall>x\<in>range ?f. lebesgue.\<mu> (?f -` {x} \<inter> UNIV) = \<omega> \<longrightarrow> x = 0"
    proof (safe, simp, safe, rule ccontr)
      fix y assume "f y \<noteq> \<omega>" "f y \<noteq> 0"
      hence "(\<lambda>x. if f x = \<omega> then 0 else f x) -` {if f y = \<omega> then 0 else f y} = f -` {f y}"
        by (auto split: split_if_asm)
      moreover assume "lebesgue.\<mu> ((\<lambda>x. if f x = \<omega> then 0 else f x) -` {if f y = \<omega> then 0 else f y}) = \<omega>"
      ultimately have "lebesgue.\<mu> (f -` {f y}) = \<omega>" by simp
      moreover
      have "f y * lebesgue.\<mu> (f -` {f y}) \<noteq> \<omega>" using i f
        unfolding simple_integral_def setsum_\<omega> simple_function_def
        by auto
      ultimately have "f y = 0" by (auto split: split_if_asm)
      then show False using `f y \<noteq> 0` by simp
    qed
  qed
qed

lemma (in measure_space) positive_integral_monotone_convergence:
  fixes f::"nat \<Rightarrow> 'a \<Rightarrow> pextreal"
  assumes i: "\<And>i. f i \<in> borel_measurable M" and mono: "\<And>x. mono (\<lambda>n. f n x)"
  and lim: "\<And>x. (\<lambda>i. f i x) ----> u x"
  shows "u \<in> borel_measurable M"
  and "(\<lambda>i. integral\<^isup>P M (f i)) ----> integral\<^isup>P M u" (is ?ilim)
proof -
  from positive_integral_isoton[unfolded isoton_fun_expand isoton_iff_Lim_mono, of f u]
  show ?ilim using mono lim i by auto
  have "\<And>x. (SUP i. f i x) = u x" using mono lim SUP_Lim_pextreal
    unfolding fun_eq_iff mono_def by auto
  moreover have "(\<lambda>x. SUP i. f i x) \<in> borel_measurable M"
    using i by auto
  ultimately show "u \<in> borel_measurable M" by simp
qed

lemma positive_integral_has_integral:
  fixes f::"'a::ordered_euclidean_space => pextreal"
  assumes f:"f \<in> borel_measurable lebesgue"
  and int_om:"integral\<^isup>P lebesgue f \<noteq> \<omega>"
  and f_om:"\<forall>x. f x \<noteq> \<omega>" (* TODO: remove this *)
  shows "((\<lambda>x. real (f x)) has_integral (real (integral\<^isup>P lebesgue f))) UNIV"
proof- let ?i = "integral\<^isup>P lebesgue f"
  from lebesgue.borel_measurable_implies_simple_function_sequence[OF f]
  guess u .. note conjunctD2[OF this,rule_format] note u = conjunctD2[OF this(1)] this(2)
  let ?u = "\<lambda>i x. real (u i x)" and ?f = "\<lambda>x. real (f x)"
  have u_simple:"\<And>k. integral\<^isup>S lebesgue (u k) = integral\<^isup>P lebesgue (u k)"
    apply(subst lebesgue.positive_integral_eq_simple_integral[THEN sym,OF u(1)]) ..
  have int_u_le:"\<And>k. integral\<^isup>S lebesgue (u k) \<le> integral\<^isup>P lebesgue f"
    unfolding u_simple apply(rule lebesgue.positive_integral_mono)
    using isoton_Sup[OF u(3)] unfolding le_fun_def by auto
  have u_int_om:"\<And>i. integral\<^isup>S lebesgue (u i) \<noteq> \<omega>"
  proof- case goal1 thus ?case using int_u_le[of i] int_om by auto qed

  note u_int = simple_function_has_integral'[OF u(1) this]
  have "(\<lambda>x. real (f x)) integrable_on UNIV \<and>
    (\<lambda>k. Integration.integral UNIV (\<lambda>x. real (u k x))) ----> Integration.integral UNIV (\<lambda>x. real (f x))"
    apply(rule monotone_convergence_increasing) apply(rule,rule,rule u_int)
  proof safe case goal1 show ?case apply(rule real_of_pextreal_mono) using u(2,3) by auto
  next case goal2 show ?case using u(3) apply(subst lim_Real[THEN sym])
      prefer 3 apply(subst Real_real') defer apply(subst Real_real')
      using isotone_Lim[OF u(3)[unfolded isoton_fun_expand, THEN spec]] using f_om u by auto
  next case goal3
    show ?case apply(rule bounded_realI[where B="real (integral\<^isup>P lebesgue f)"])
      apply safe apply(subst abs_of_nonneg) apply(rule integral_nonneg,rule) apply(rule u_int)
      unfolding integral_unique[OF u_int] defer apply(rule real_of_pextreal_mono[OF _ int_u_le])
      using u int_om by auto
  qed note int = conjunctD2[OF this]

  have "(\<lambda>i. integral\<^isup>S lebesgue (u i)) ----> ?i" unfolding u_simple
    apply(rule lebesgue.positive_integral_monotone_convergence(2))
    apply(rule lebesgue.borel_measurable_simple_function[OF u(1)])
    using isotone_Lim[OF u(3)[unfolded isoton_fun_expand, THEN spec]] by auto
  hence "(\<lambda>i. real (integral\<^isup>S lebesgue (u i))) ----> real ?i" apply-
    apply(subst lim_Real[THEN sym]) prefer 3
    apply(subst Real_real') defer apply(subst Real_real')
    using u f_om int_om u_int_om by auto
  note * = LIMSEQ_unique[OF this int(2)[unfolded integral_unique[OF u_int]]]
  show ?thesis unfolding * by(rule integrable_integral[OF int(1)])
qed

lemma lebesgue_integral_has_integral:
  fixes f::"'a::ordered_euclidean_space => real"
  assumes f:"integrable lebesgue f"
  shows "(f has_integral (integral\<^isup>L lebesgue f)) UNIV"
proof- let ?n = "\<lambda>x. - min (f x) 0" and ?p = "\<lambda>x. max (f x) 0"
  have *:"f = (\<lambda>x. ?p x - ?n x)" apply rule by auto
  note f = integrableD[OF f]
  show ?thesis unfolding lebesgue_integral_def apply(subst *)
  proof(rule has_integral_sub) case goal1
    have *:"\<forall>x. Real (f x) \<noteq> \<omega>" by auto
    note lebesgue.borel_measurable_Real[OF f(1)]
    from positive_integral_has_integral[OF this f(2) *]
    show ?case unfolding real_Real_max .
  next case goal2
    have *:"\<forall>x. Real (- f x) \<noteq> \<omega>" by auto
    note lebesgue.borel_measurable_uminus[OF f(1)]
    note lebesgue.borel_measurable_Real[OF this]
    from positive_integral_has_integral[OF this f(3) *]
    show ?case unfolding real_Real_max minus_min_eq_max by auto
  qed
qed

lemma lebesgue_positive_integral_eq_borel:
  "f \<in> borel_measurable borel \<Longrightarrow> integral\<^isup>P lebesgue f = integral\<^isup>P lborel f"
  by (auto intro!: lebesgue.positive_integral_subalgebra[symmetric]) default

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

lemma continuous_on_imp_borel_measurable:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::ordered_euclidean_space"
  assumes "continuous_on UNIV f"
  shows "f \<in> borel_measurable borel"
  apply(rule borel.borel_measurableI)
  using continuous_open_preimage[OF assms] unfolding vimage_def by auto

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

interpretation lborel_space: finite_product_sigma_finite "\<lambda>x. lborel::real measure_space" "{..<DIM('a::ordered_euclidean_space)}"
  where "space lborel = UNIV"
  and "sets lborel = sets borel"
  and "measure lborel = lebesgue.\<mu>"
  and "measurable lborel = measurable borel"
proof -
  show "finite_product_sigma_finite (\<lambda>x. lborel::real measure_space) {..<DIM('a::ordered_euclidean_space)}"
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
       (auto intro!: measurable_sigma_sigma isotoneI real_arch_lt
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
  shows "lborel.\<mu> A = lborel_space.\<mu> TYPE('a) (p2e -` A \<inter> (space (lborel_space.P TYPE('a))))"
    (is "_ = measure ?P (?T A)")
proof (rule measure_unique_Int_stable_vimage)
  show "measure_space ?P" by default
  show "measure_space lborel" by default

  let ?E = "\<lparr> space = UNIV :: 'a set, sets = range (\<lambda>(a,b). {a..b}) \<rparr>"
  show "Int_stable ?E" using Int_stable_cuboids .
  show "range cube \<subseteq> sets ?E" unfolding cube_def_raw by auto
  { fix x have "\<exists>n. x \<in> cube n" using mem_big_cube[of x] by fastsimp }
  then show "cube \<up> space ?E" by (intro isotoneI cube_subset_Suc) auto
  { fix i show "lborel.\<mu> (cube i) \<noteq> \<omega>" unfolding cube_def by auto }
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
                 intro!: Real_setprod )
      also have "\<dots> = measure ?P (?T X)"
        unfolding * by (subst lborel_space.measure_times) auto
      finally show ?thesis .
    qed simp }
qed

lemma lebesgue_eq_lborel_space_in_borel:
  fixes A :: "('a::ordered_euclidean_space) set"
  assumes A: "A \<in> sets borel"
  shows "lebesgue.\<mu> A = lborel_space.\<mu> TYPE('a) (p2e -` A \<inter> (space (lborel_space.P TYPE('a))))"
  using lborel_eq_lborel_space[OF A] by simp

lemma borel_fubini_positiv_integral:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> pextreal"
  assumes f: "f \<in> borel_measurable borel"
  shows "integral\<^isup>P lborel f = \<integral>\<^isup>+x. f (p2e x) \<partial>(lborel_space.P TYPE('a))"
proof (rule lborel_space.positive_integral_vimage[OF _ _ _ lborel_eq_lborel_space])
  show "sigma_algebra lborel" by default
  show "p2e \<in> measurable (lborel_space.P TYPE('a)) (lborel :: 'a measure_space)"
       "f \<in> borel_measurable lborel"
    using measurable_p2e f by (simp_all add: measurable_def)
qed simp

lemma borel_fubini_integrable:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> real"
  shows "integrable lborel f \<longleftrightarrow>
    integrable (lborel_space.P TYPE('a)) (\<lambda>x. f (p2e x))"
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
  shows "integral\<^isup>L lborel f = \<integral>x. f (p2e x) \<partial>(lborel_space.P TYPE('a))"
  using f by (simp add: borel_fubini_positiv_integral lebesgue_integral_def)

end
