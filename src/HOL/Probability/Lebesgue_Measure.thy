(*  Author: Robert Himmelmann, TU Muenchen *)
header {* Lebsegue measure *}
theory Lebesgue_Measure
  imports Product_Measure Complete_Measure
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

definition lebesgue :: "'a::ordered_euclidean_space algebra" where
  "lebesgue = \<lparr> space = UNIV, sets = {A. \<forall>n. (indicator A :: 'a \<Rightarrow> real) integrable_on cube n} \<rparr>"

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

definition "lmeasure A = (SUP n. Real (integral (cube n) (indicator A)))"

interpretation lebesgue: measure_space lebesgue lmeasure
proof
  have *: "indicator {} = (\<lambda>x. 0 :: real)" by (simp add: fun_eq_iff)
  show "lmeasure {} = 0" by (simp add: integral_0 * lmeasure_def)
next
  show "countably_additive lebesgue lmeasure"
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
    show "(\<Sum>\<^isub>\<infinity>n. lmeasure (A n)) = lmeasure (\<Union>i. A i)" unfolding lmeasure_def
    proof (subst psuminf_SUP_eq)
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
  fixes S :: "'a::ordered_euclidean_space set" assumes "negligible S" shows "lmeasure S = 0"
proof -
  have "\<And>n. integral (cube n) (indicator S :: 'a\<Rightarrow>real) = 0"
    unfolding integral_def using assms
    by (intro some1_equality ex_ex1I has_integral_unique)
       (auto simp: cube_def negligible_def intro: )
  then show ?thesis unfolding lmeasure_def by auto
qed

lemma lmeasure_iff_LIMSEQ:
  assumes "A \<in> sets lebesgue" "0 \<le> m"
  shows "lmeasure A = Real m \<longleftrightarrow> (\<lambda>n. integral (cube n) (indicator A :: _ \<Rightarrow> real)) ----> m"
  unfolding lmeasure_def
proof (intro SUP_eq_LIMSEQ)
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
  assumes "s \<in> sets lebesgue" "lmeasure s = Real m" "0 \<le> m"
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

lemma lmeasure_finite_integrable: assumes "s \<in> sets lebesgue" "lmeasure s \<noteq> \<omega>"
  shows "(indicator s :: _ \<Rightarrow> real) integrable_on UNIV"
proof (cases "lmeasure s")
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
  shows "lmeasure s = Real m"
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
  "(indicator A has_integral m) UNIV \<longleftrightarrow> (A \<in> sets lebesgue \<and> 0 \<le> m \<and> lmeasure A = Real m)"
proof
  assume "(indicator A has_integral m) UNIV"
  with has_integral_lmeasure[OF this] has_integral_lebesgue[OF this]
  show "A \<in> sets lebesgue \<and> 0 \<le> m \<and> lmeasure A = Real m"
    by (auto intro: has_integral_nonneg)
next
  assume "A \<in> sets lebesgue \<and> 0 \<le> m \<and> lmeasure A = Real m"
  then show "(indicator A has_integral m) UNIV" by (intro lmeasure_finite_has_integral) auto
qed

lemma lmeasure_eq_integral: assumes "(indicator s::_\<Rightarrow>real) integrable_on UNIV"
  shows "lmeasure s = Real (integral UNIV (indicator s))"
  using assms unfolding integrable_on_def
proof safe
  fix y :: real assume "(indicator s has_integral y) UNIV"
  from this[unfolded has_integral_iff_lmeasure] integral_unique[OF this]
  show "lmeasure s = Real (integral UNIV (indicator s))" by simp
qed

lemma lebesgue_simple_function_indicator:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> pextreal"
  assumes f:"lebesgue.simple_function f"
  shows "f = (\<lambda>x. (\<Sum>y \<in> f ` UNIV. y * indicator (f -` {y}) x))"
  apply(rule,subst lebesgue.simple_function_indicator_representation[OF f]) by auto

lemma integral_eq_lmeasure:
  "(indicator s::_\<Rightarrow>real) integrable_on UNIV \<Longrightarrow> integral UNIV (indicator s) = real (lmeasure s)"
  by (subst lmeasure_eq_integral) (auto intro!: integral_nonneg)

lemma lmeasure_finite: assumes "(indicator s::_\<Rightarrow>real) integrable_on UNIV" shows "lmeasure s \<noteq> \<omega>"
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

lemma lmeasure_UNIV[intro]: "lmeasure (UNIV::'a::ordered_euclidean_space set) = \<omega>"
  unfolding lmeasure_def SUP_\<omega>
proof (intro allI impI)
  fix x assume "x < \<omega>"
  then obtain r where r: "x = Real r" "0 \<le> r" by (cases x) auto
  then obtain n where n: "r < of_nat n" using ex_less_of_nat by auto
  show "\<exists>i\<in>UNIV. x < Real (integral (cube i) (indicator UNIV::'a\<Rightarrow>real))"
  proof (intro bexI[of _ n])
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
  qed auto
qed

lemma
  fixes a b ::"'a::ordered_euclidean_space"
  shows lmeasure_atLeastAtMost[simp]: "lmeasure {a..b} = Real (content {a..b})"
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
  fixes a :: "'a::ordered_euclidean_space" shows "lmeasure {a} = 0"
  using lmeasure_atLeastAtMost[of a a] by simp

declare content_real[simp]

lemma
  fixes a b :: real
  shows lmeasure_real_greaterThanAtMost[simp]:
    "lmeasure {a <.. b} = Real (if a \<le> b then b - a else 0)"
proof cases
  assume "a < b"
  then have "lmeasure {a <.. b} = lmeasure {a .. b} - lmeasure {a}"
    by (subst lebesgue.measure_Diff[symmetric])
       (auto intro!: arg_cong[where f=lmeasure])
  then show ?thesis by auto
qed auto

lemma
  fixes a b :: real
  shows lmeasure_real_atLeastLessThan[simp]:
    "lmeasure {a ..< b} = Real (if a \<le> b then b - a else 0)"
proof cases
  assume "a < b"
  then have "lmeasure {a ..< b} = lmeasure {a .. b} - lmeasure {b}"
    by (subst lebesgue.measure_Diff[symmetric])
       (auto intro!: arg_cong[where f=lmeasure])
  then show ?thesis by auto
qed auto

lemma
  fixes a b :: real
  shows lmeasure_real_greaterThanLessThan[simp]:
    "lmeasure {a <..< b} = Real (if a \<le> b then b - a else 0)"
proof cases
  assume "a < b"
  then have "lmeasure {a <..< b} = lmeasure {a <.. b} - lmeasure {b}"
    by (subst lebesgue.measure_Diff[symmetric])
       (auto intro!: arg_cong[where f=lmeasure])
  then show ?thesis by auto
qed auto

interpretation borel: measure_space borel lmeasure
proof
  show "countably_additive borel lmeasure"
    using lebesgue.ca unfolding countably_additive_def
    apply safe apply (erule_tac x=A in allE) by auto
qed auto

interpretation borel: sigma_finite_measure borel lmeasure
proof (default, intro conjI exI[of _ "\<lambda>n. cube n"])
  show "range cube \<subseteq> sets borel" by (auto intro: borel_closed)
  { fix x have "\<exists>n. x\<in>cube n" using mem_big_cube by auto }
  thus "(\<Union>i. cube i) = space borel" by auto
  show "\<forall>i. lmeasure (cube i) \<noteq> \<omega>" unfolding cube_def by auto
qed

interpretation lebesgue: sigma_finite_measure lebesgue lmeasure
proof
  from borel.sigma_finite guess A ..
  moreover then have "range A \<subseteq> sets lebesgue" using lebesgueI_borel by blast
  ultimately show "\<exists>A::nat \<Rightarrow> 'b set. range A \<subseteq> sets lebesgue \<and> (\<Union>i. A i) = space lebesgue \<and> (\<forall>i. lmeasure (A i) \<noteq> \<omega>)"
    by auto
qed

lemma simple_function_has_integral:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> pextreal"
  assumes f:"lebesgue.simple_function f"
  and f':"\<forall>x. f x \<noteq> \<omega>"
  and om:"\<forall>x\<in>range f. lmeasure (f -` {x} \<inter> UNIV) = \<omega> \<longrightarrow> x = 0"
  shows "((\<lambda>x. real (f x)) has_integral (real (lebesgue.simple_integral f))) UNIV"
  unfolding lebesgue.simple_integral_def
  apply(subst lebesgue_simple_function_indicator[OF f])
proof -
  case goal1
  have *:"\<And>x. \<forall>y\<in>range f. y * indicator (f -` {y}) x \<noteq> \<omega>"
    "\<forall>x\<in>range f. x * lmeasure (f -` {x} \<inter> UNIV) \<noteq> \<omega>"
    using f' om unfolding indicator_def by auto
  show ?case unfolding space_lebesgue real_of_pextreal_setsum'[OF *(1),THEN sym]
    unfolding real_of_pextreal_setsum'[OF *(2),THEN sym]
    unfolding real_of_pextreal_setsum space_lebesgue
    apply(rule has_integral_setsum)
  proof safe show "finite (range f)" using f by (auto dest: lebesgue.simple_functionD)
    fix y::'a show "((\<lambda>x. real (f y * indicator (f -` {f y}) x)) has_integral
      real (f y * lmeasure (f -` {f y} \<inter> UNIV))) UNIV"
    proof(cases "f y = 0") case False
      have mea:"(indicator (f -` {f y}) ::_\<Rightarrow>real) integrable_on UNIV"
        apply(rule lmeasure_finite_integrable)
        using assms unfolding lebesgue.simple_function_def using False by auto
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
  assumes f:"lebesgue.simple_function f"
  and i: "lebesgue.simple_integral f \<noteq> \<omega>"
  shows "((\<lambda>x. real (f x)) has_integral (real (lebesgue.simple_integral f))) UNIV"
proof- let ?f = "\<lambda>x. if f x = \<omega> then 0 else f x"
  { fix x have "real (f x) = real (?f x)" by (cases "f x") auto } note * = this
  have **:"{x. f x \<noteq> ?f x} = f -` {\<omega>}" by auto
  have **:"lmeasure {x\<in>space lebesgue. f x \<noteq> ?f x} = 0"
    using lebesgue.simple_integral_omega[OF assms] by(auto simp add:**)
  show ?thesis apply(subst lebesgue.simple_integral_cong'[OF f _ **])
    apply(rule lebesgue.simple_function_compose1[OF f])
    unfolding * defer apply(rule simple_function_has_integral)
  proof-
    show "lebesgue.simple_function ?f"
      using lebesgue.simple_function_compose1[OF f] .
    show "\<forall>x. ?f x \<noteq> \<omega>" by auto
    show "\<forall>x\<in>range ?f. lmeasure (?f -` {x} \<inter> UNIV) = \<omega> \<longrightarrow> x = 0"
    proof (safe, simp, safe, rule ccontr)
      fix y assume "f y \<noteq> \<omega>" "f y \<noteq> 0"
      hence "(\<lambda>x. if f x = \<omega> then 0 else f x) -` {if f y = \<omega> then 0 else f y} = f -` {f y}"
        by (auto split: split_if_asm)
      moreover assume "lmeasure ((\<lambda>x. if f x = \<omega> then 0 else f x) -` {if f y = \<omega> then 0 else f y}) = \<omega>"
      ultimately have "lmeasure (f -` {f y}) = \<omega>" by simp
      moreover
      have "f y * lmeasure (f -` {f y}) \<noteq> \<omega>" using i f
        unfolding lebesgue.simple_integral_def setsum_\<omega> lebesgue.simple_function_def
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
  and "(\<lambda>i. positive_integral (f i)) ----> positive_integral u" (is ?ilim)
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
  and int_om:"lebesgue.positive_integral f \<noteq> \<omega>"
  and f_om:"\<forall>x. f x \<noteq> \<omega>" (* TODO: remove this *)
  shows "((\<lambda>x. real (f x)) has_integral (real (lebesgue.positive_integral f))) UNIV"
proof- let ?i = "lebesgue.positive_integral f"
  from lebesgue.borel_measurable_implies_simple_function_sequence[OF f]
  guess u .. note conjunctD2[OF this,rule_format] note u = conjunctD2[OF this(1)] this(2)
  let ?u = "\<lambda>i x. real (u i x)" and ?f = "\<lambda>x. real (f x)"
  have u_simple:"\<And>k. lebesgue.simple_integral (u k) = lebesgue.positive_integral (u k)"
    apply(subst lebesgue.positive_integral_eq_simple_integral[THEN sym,OF u(1)]) ..
  have int_u_le:"\<And>k. lebesgue.simple_integral (u k) \<le> lebesgue.positive_integral f"
    unfolding u_simple apply(rule lebesgue.positive_integral_mono)
    using isoton_Sup[OF u(3)] unfolding le_fun_def by auto
  have u_int_om:"\<And>i. lebesgue.simple_integral (u i) \<noteq> \<omega>"
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
    show ?case apply(rule bounded_realI[where B="real (lebesgue.positive_integral f)"])
      apply safe apply(subst abs_of_nonneg) apply(rule integral_nonneg,rule) apply(rule u_int)
      unfolding integral_unique[OF u_int] defer apply(rule real_of_pextreal_mono[OF _ int_u_le])
      using u int_om by auto
  qed note int = conjunctD2[OF this]

  have "(\<lambda>i. lebesgue.simple_integral (u i)) ----> ?i" unfolding u_simple
    apply(rule lebesgue.positive_integral_monotone_convergence(2))
    apply(rule lebesgue.borel_measurable_simple_function[OF u(1)])
    using isotone_Lim[OF u(3)[unfolded isoton_fun_expand, THEN spec]] by auto
  hence "(\<lambda>i. real (lebesgue.simple_integral (u i))) ----> real ?i" apply-
    apply(subst lim_Real[THEN sym]) prefer 3
    apply(subst Real_real') defer apply(subst Real_real')
    using u f_om int_om u_int_om by auto
  note * = LIMSEQ_unique[OF this int(2)[unfolded integral_unique[OF u_int]]]
  show ?thesis unfolding * by(rule integrable_integral[OF int(1)])
qed

lemma lebesgue_integral_has_integral:
  fixes f::"'a::ordered_euclidean_space => real"
  assumes f:"lebesgue.integrable f"
  shows "(f has_integral (lebesgue.integral f)) UNIV"
proof- let ?n = "\<lambda>x. - min (f x) 0" and ?p = "\<lambda>x. max (f x) 0"
  have *:"f = (\<lambda>x. ?p x - ?n x)" apply rule by auto
  note f = lebesgue.integrableD[OF f]
  show ?thesis unfolding lebesgue.integral_def apply(subst *)
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
  "f \<in> borel_measurable borel \<Longrightarrow> lebesgue.positive_integral f = borel.positive_integral f "
  by (auto intro!: lebesgue.positive_integral_subalgebra[symmetric]) default

lemma lebesgue_integral_eq_borel:
  assumes "f \<in> borel_measurable borel"
  shows "lebesgue.integrable f = borel.integrable f" (is ?P)
    and "lebesgue.integral f = borel.integral f" (is ?I)
proof -
  have *: "sigma_algebra borel" by default
  have "sets borel \<subseteq> sets lebesgue" by auto
  from lebesgue.integral_subalgebra[OF assms this _ *]
  show ?P ?I by auto
qed

lemma borel_integral_has_integral:
  fixes f::"'a::ordered_euclidean_space => real"
  assumes f:"borel.integrable f"
  shows "(f has_integral (borel.integral f)) UNIV"
proof -
  have borel: "f \<in> borel_measurable borel"
    using f unfolding borel.integrable_def by auto
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

lemma (in measure_space) integral_monotone_convergence_pos':
  assumes i: "\<And>i. integrable (f i)" and mono: "\<And>x. mono (\<lambda>n. f n x)"
  and pos: "\<And>x i. 0 \<le> f i x"
  and lim: "\<And>x. (\<lambda>i. f i x) ----> u x"
  and ilim: "(\<lambda>i. integral (f i)) ----> x"
  shows "integrable u \<and> integral u = x"
  using integral_monotone_convergence_pos[OF assms] by auto

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

lemma bij_inv_p2e_e2p:
  shows "bij_inv ({..<DIM('a)} \<rightarrow>\<^isub>E UNIV) (UNIV :: 'a::ordered_euclidean_space set)
     p2e e2p" (is "bij_inv ?P ?U _ _")
proof (rule bij_invI)
  show "p2e \<in> ?P \<rightarrow> ?U" "e2p \<in> ?U \<rightarrow> ?P" by (auto simp: e2p_def)
qed auto

interpretation borel_product: product_sigma_finite "\<lambda>x. borel::real algebra" "\<lambda>x. lmeasure"
  by default

lemma cube_subset_Suc[intro]: "cube n \<subseteq> cube (Suc n)"
  unfolding cube_def_raw subset_eq apply safe unfolding mem_interval by auto

lemma Pi_iff: "f \<in> Pi I X \<longleftrightarrow> (\<forall>i\<in>I. f i \<in> X i)"
  unfolding Pi_def by auto

lemma measurable_e2p_on_generator:
  "e2p \<in> measurable \<lparr> space = UNIV::'a set, sets = range lessThan \<rparr>
  (product_algebra
    (\<lambda>x. \<lparr> space = UNIV::real set, sets = range lessThan \<rparr>)
    {..<DIM('a::ordered_euclidean_space)})"
  (is "e2p \<in> measurable ?E ?P")
proof (unfold measurable_def, intro CollectI conjI ballI)
  show "e2p \<in> space ?E \<rightarrow> space ?P" by (auto simp: e2p_def)
  fix A assume "A \<in> sets ?P"
  then obtain E where A: "A = (\<Pi>\<^isub>E i\<in>{..<DIM('a)}. E i)"
    and "E \<in> {..<DIM('a)} \<rightarrow> (range lessThan)"
    by (auto elim!: product_algebraE)
  then have "\<forall>i\<in>{..<DIM('a)}. \<exists>xs. E i = {..< xs}" by auto
  from this[THEN bchoice] guess xs ..
  then have A_eq: "A = (\<Pi>\<^isub>E i\<in>{..<DIM('a)}. {..< xs i})"
    using A by auto
  have "e2p -` A = {..< (\<chi>\<chi> i. xs i) :: 'a}"
    using DIM_positive by (auto simp add: Pi_iff set_eq_iff e2p_def A_eq
      euclidean_eq[where 'a='a] eucl_less[where 'a='a])
  then show "e2p -` A \<inter> space ?E \<in> sets ?E" by simp
qed

lemma measurable_p2e_on_generator:
  "p2e \<in> measurable
    (product_algebra
      (\<lambda>x. \<lparr> space = UNIV::real set, sets = range lessThan \<rparr>)
      {..<DIM('a::ordered_euclidean_space)})
    \<lparr> space = UNIV::'a set, sets = range lessThan \<rparr>"
  (is "p2e \<in> measurable ?P ?E")
proof (unfold measurable_def, intro CollectI conjI ballI)
  show "p2e \<in> space ?P \<rightarrow> space ?E" by simp
  fix A assume "A \<in> sets ?E"
  then obtain x where "A = {..<x}" by auto
  then have "p2e -` A \<inter> space ?P = (\<Pi>\<^isub>E i\<in>{..<DIM('a)}. {..< x $$ i})"
    using DIM_positive
    by (auto simp: Pi_iff set_eq_iff p2e_def
                   euclidean_eq[where 'a='a] eucl_less[where 'a='a])
  then show "p2e -` A \<inter> space ?P \<in> sets ?P" by auto
qed

lemma borel_vimage_algebra_eq:
  defines "F \<equiv> product_algebra (\<lambda>x. \<lparr> space = (UNIV::real set), sets = range lessThan \<rparr>) {..<DIM('a::ordered_euclidean_space)}"
  shows "sigma_algebra.vimage_algebra (borel::'a::ordered_euclidean_space algebra) (space (sigma F)) p2e = sigma F"
  unfolding borel_eq_lessThan
proof (intro vimage_algebra_sigma)
  let ?E = "\<lparr>space = (UNIV::'a set), sets = range lessThan\<rparr>"
  show "bij_inv (space (sigma F)) (space (sigma ?E)) p2e e2p"
    using bij_inv_p2e_e2p unfolding F_def by simp
  show "sets F \<subseteq> Pow (space F)" "sets ?E \<subseteq> Pow (space ?E)" unfolding F_def
    by (intro product_algebra_sets_into_space) auto
  show "p2e \<in> measurable F ?E"
    "e2p \<in> measurable ?E F"
    unfolding F_def using measurable_p2e_on_generator measurable_e2p_on_generator by auto
qed

lemma product_borel_eq_vimage:
  "sigma (product_algebra (\<lambda>x. borel) {..<DIM('a::ordered_euclidean_space)}) =
  sigma_algebra.vimage_algebra borel (extensional {..<DIM('a)})
  (p2e:: _ \<Rightarrow> 'a::ordered_euclidean_space)"
  unfolding borel_vimage_algebra_eq[simplified]
  unfolding borel_eq_lessThan
  apply(subst sigma_product_algebra_sigma_eq[where S="\<lambda>i. \<lambda>n. lessThan (real n)"])
  unfolding lessThan_iff
proof- fix i assume i:"i<DIM('a)"
  show "(\<lambda>n. {..<real n}) \<up> space \<lparr>space = UNIV, sets = range lessThan\<rparr>"
    by(auto intro!:real_arch_lt isotoneI)
qed auto

lemma e2p_Int:"e2p ` A \<inter> e2p ` B = e2p ` (A \<inter> B)" (is "?L = ?R")
  apply(rule image_Int[THEN sym])
  using bij_inv_p2e_e2p[THEN bij_inv_bij_betw(2)]
  unfolding bij_betw_def by auto

lemma Int_stable_cuboids: fixes x::"'a::ordered_euclidean_space"
  shows "Int_stable \<lparr>space = UNIV, sets = range (\<lambda>(a, b::'a). e2p ` {a..b})\<rparr>"
  unfolding Int_stable_def algebra.select_convs
proof safe fix a b x y::'a
  have *:"e2p ` {a..b} \<inter> e2p ` {x..y} =
    (\<lambda>(a, b). e2p ` {a..b}) (\<chi>\<chi> i. max (a $$ i) (x $$ i), \<chi>\<chi> i. min (b $$ i) (y $$ i)::'a)"
    unfolding e2p_Int inter_interval by auto
  show "e2p ` {a..b} \<inter> e2p ` {x..y} \<in> range (\<lambda>(a, b). e2p ` {a..b::'a})" unfolding *
    apply(rule range_eqI) ..
qed

lemma Int_stable_cuboids': fixes x::"'a::ordered_euclidean_space"
  shows "Int_stable \<lparr>space = UNIV, sets = range (\<lambda>(a, b::'a). {a..b})\<rparr>"
  unfolding Int_stable_def algebra.select_convs
  apply safe unfolding inter_interval by auto

lemma inj_on_disjoint_family_on: assumes "disjoint_family_on A S" "inj f"
  shows "disjoint_family_on (\<lambda>x. f ` A x) S"
  unfolding disjoint_family_on_def
proof(rule,rule,rule)
  fix x1 x2 assume x:"x1 \<in> S" "x2 \<in> S" "x1 \<noteq> x2"
  show "f ` A x1 \<inter> f ` A x2 = {}"
  proof(rule ccontr) case goal1
    then obtain z where z:"z \<in> f ` A x1 \<inter> f ` A x2" by auto
    then obtain z1 z2 where z12:"z1 \<in> A x1" "z2 \<in> A x2" "f z1 = z" "f z2 = z" by auto
    hence "z1 = z2" using assms(2) unfolding inj_on_def by blast
    hence "x1 = x2" using z12(1-2) using assms[unfolded disjoint_family_on_def] using x by auto
    thus False using x(3) by auto
  qed
qed

declare restrict_extensional[intro]

lemma e2p_extensional[intro]:"e2p (y::'a::ordered_euclidean_space) \<in> extensional {..<DIM('a)}"
  unfolding e2p_def by auto

lemma e2p_image_vimage: fixes A::"'a::ordered_euclidean_space set"
  shows "e2p ` A = p2e -` A \<inter> extensional {..<DIM('a)}"
proof(rule set_eqI,rule)
  fix x assume "x \<in> e2p ` A" then guess y unfolding image_iff .. note y=this
  show "x \<in> p2e -` A \<inter> extensional {..<DIM('a)}"
    apply safe apply(rule vimageI[OF _ y(1)]) unfolding y p2e_e2p by auto
next fix x assume "x \<in> p2e -` A \<inter> extensional {..<DIM('a)}"
  thus "x \<in> e2p ` A" unfolding image_iff apply(rule_tac x="p2e x" in bexI) apply(subst e2p_p2e) by auto
qed

lemma lmeasure_measure_eq_borel_prod:
  fixes A :: "('a::ordered_euclidean_space) set"
  assumes "A \<in> sets borel"
  shows "lmeasure A = borel_product.product_measure {..<DIM('a)} (e2p ` A :: (nat \<Rightarrow> real) set)"
proof (rule measure_unique_Int_stable[where X=A and A=cube])
  interpret fprod: finite_product_sigma_finite "\<lambda>x. borel" "\<lambda>x. lmeasure" "{..<DIM('a)}" by default auto
  show "Int_stable \<lparr> space = UNIV :: 'a set, sets = range (\<lambda>(a,b). {a..b}) \<rparr>"
    (is "Int_stable ?E" ) using Int_stable_cuboids' .
  show "borel = sigma ?E" using borel_eq_atLeastAtMost .
  show "\<And>i. lmeasure (cube i) \<noteq> \<omega>" unfolding cube_def by auto
  show "\<And>X. X \<in> sets ?E \<Longrightarrow>
    lmeasure X = borel_product.product_measure {..<DIM('a)} (e2p ` X :: (nat \<Rightarrow> real) set)"
  proof- case goal1 then obtain a b where X:"X = {a..b}" by auto
    { presume *:"X \<noteq> {} \<Longrightarrow> ?case"
      show ?case apply(cases,rule *,assumption) by auto }
    def XX \<equiv> "\<lambda>i. {a $$ i .. b $$ i}" assume  "X \<noteq> {}"  note X' = this[unfolded X interval_ne_empty]
    have *:"Pi\<^isub>E {..<DIM('a)} XX = e2p ` X" apply(rule set_eqI)
    proof fix x assume "x \<in> Pi\<^isub>E {..<DIM('a)} XX"
      thus "x \<in> e2p ` X" unfolding image_iff apply(rule_tac x="\<chi>\<chi> i. x i" in bexI)
        unfolding Pi_def extensional_def e2p_def restrict_def X mem_interval XX_def by rule auto
    next fix x assume "x \<in> e2p ` X" then guess y unfolding image_iff .. note y = this
      show "x \<in> Pi\<^isub>E {..<DIM('a)} XX" unfolding y using y(1)
        unfolding Pi_def extensional_def e2p_def restrict_def X mem_interval XX_def by auto
    qed
    have "lmeasure X = (\<Prod>x<DIM('a). Real (b $$ x - a $$ x))"  using X' apply- unfolding X
      unfolding lmeasure_atLeastAtMost content_closed_interval apply(subst Real_setprod) by auto
    also have "... = (\<Prod>i<DIM('a). lmeasure (XX i))" apply(rule setprod_cong2)
      unfolding XX_def lmeasure_atLeastAtMost apply(subst content_real) using X' by auto
    also have "... = borel_product.product_measure {..<DIM('a)} (e2p ` X)" unfolding *[THEN sym]
      apply(rule fprod.measure_times[THEN sym]) unfolding XX_def by auto
    finally show ?case .
  qed

  show "range cube \<subseteq> sets \<lparr>space = UNIV, sets = range (\<lambda>(a, b). {a..b})\<rparr>"
    unfolding cube_def_raw by auto
  have "\<And>x. \<exists>xa. x \<in> cube xa" apply(rule_tac x=x in mem_big_cube) by fastsimp
  thus "cube \<up> space \<lparr>space = UNIV, sets = range (\<lambda>(a, b). {a..b})\<rparr>"
    apply-apply(rule isotoneI) apply(rule cube_subset_Suc) by auto
  show "A \<in> sets borel " by fact
  show "measure_space borel lmeasure" by default
  show "measure_space borel
     (\<lambda>a::'a set. finite_product_sigma_finite.measure (\<lambda>x. borel) (\<lambda>x. lmeasure) {..<DIM('a)} (e2p ` a))"
    apply default unfolding countably_additive_def
  proof safe fix A::"nat \<Rightarrow> 'a set" assume A:"range A \<subseteq> sets borel" "disjoint_family A"
      "(\<Union>i. A i) \<in> sets borel"
    note fprod.ca[unfolded countably_additive_def,rule_format]
    note ca = this[of "\<lambda> n. e2p ` (A n)"]
    show "(\<Sum>\<^isub>\<infinity>n. finite_product_sigma_finite.measure
        (\<lambda>x. borel) (\<lambda>x. lmeasure) {..<DIM('a)} (e2p ` A n)) =
           finite_product_sigma_finite.measure (\<lambda>x. borel)
            (\<lambda>x. lmeasure) {..<DIM('a)} (e2p ` (\<Union>i. A i))" unfolding image_UN
    proof(rule ca) show "range (\<lambda>n. e2p ` A n) \<subseteq> sets
       (sigma (product_algebra (\<lambda>x. borel) {..<DIM('a)}))"
        unfolding product_borel_eq_vimage
      proof case goal1
        then guess y unfolding image_iff .. note y=this(2)
        show ?case unfolding borel.in_vimage_algebra y apply-
          apply(rule_tac x="A y" in bexI,rule e2p_image_vimage)
          using A(1) by auto
      qed

      show "disjoint_family (\<lambda>n. e2p ` A n)" apply(rule inj_on_disjoint_family_on)
        using bij_inv_p2e_e2p[THEN bij_inv_bij_betw(2)] using A(2) unfolding bij_betw_def by auto
      show "(\<Union>n. e2p ` A n) \<in> sets (sigma (product_algebra (\<lambda>x. borel) {..<DIM('a)}))"
        unfolding product_borel_eq_vimage borel.in_vimage_algebra
      proof(rule bexI[OF _ A(3)],rule set_eqI,rule)
        fix x assume x:"x \<in> (\<Union>n. e2p ` A n)" hence "p2e x \<in> (\<Union>i. A i)" by auto
        moreover have "x \<in> extensional {..<DIM('a)}"
          using x unfolding extensional_def e2p_def_raw by auto
        ultimately show "x \<in> p2e -` (\<Union>i. A i) \<inter> extensional {..<DIM('a)}" by auto
      next fix x assume x:"x \<in> p2e -` (\<Union>i. A i) \<inter> extensional {..<DIM('a)}"
        hence "p2e x \<in> (\<Union>i. A i)" by auto
        hence "\<exists>n. x \<in> e2p ` A n" apply safe apply(rule_tac x=i in exI)
          unfolding image_iff apply(rule_tac x="p2e x" in bexI)
          apply(subst e2p_p2e) using x by auto
        thus "x \<in> (\<Union>n. e2p ` A n)" by auto
      qed
    qed
  qed auto
qed

lemma e2p_p2e'[simp]: fixes x::"'a::ordered_euclidean_space"
  assumes "A \<subseteq> extensional {..<DIM('a)}"
  shows "e2p ` (p2e ` A ::'a set) = A"
  apply(rule set_eqI) unfolding image_iff Bex_def apply safe defer
  apply(rule_tac x="p2e x" in exI,safe) using assms by auto

lemma range_p2e:"range (p2e::_\<Rightarrow>'a::ordered_euclidean_space) = UNIV"
  apply safe defer unfolding image_iff apply(rule_tac x="\<lambda>i. x $$ i" in bexI)
  unfolding p2e_def by auto

lemma p2e_inv_extensional:"(A::'a::ordered_euclidean_space set)
  = p2e ` (p2e -` A \<inter> extensional {..<DIM('a)})"
  unfolding p2e_def_raw apply safe unfolding image_iff
proof- fix x assume "x\<in>A"
  let ?y = "\<lambda>i. if i<DIM('a) then x$$i else undefined"
  have *:"Chi ?y = x" apply(subst euclidean_eq) by auto
  show "\<exists>xa\<in>Chi -` A \<inter> extensional {..<DIM('a)}. x = Chi xa" apply(rule_tac x="?y" in bexI)
    apply(subst euclidean_eq) unfolding extensional_def using `x\<in>A` by(auto simp: *)
qed

lemma borel_fubini_positiv_integral:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> pextreal"
  assumes f: "f \<in> borel_measurable borel"
  shows "borel.positive_integral f =
          borel_product.product_positive_integral {..<DIM('a)} (f \<circ> p2e)"
proof- def U \<equiv> "extensional {..<DIM('a)} :: (nat \<Rightarrow> real) set"
  interpret fprod: finite_product_sigma_finite "\<lambda>x. borel" "\<lambda>x. lmeasure" "{..<DIM('a)}" by default auto
  have *:"sigma_algebra.vimage_algebra borel U (p2e:: _ \<Rightarrow> 'a)
    = sigma (product_algebra (\<lambda>x. borel) {..<DIM('a)})"
    unfolding U_def product_borel_eq_vimage[symmetric] ..
  show ?thesis
    unfolding borel.positive_integral_vimage[unfolded space_borel, OF bij_inv_p2e_e2p[THEN bij_inv_bij_betw(1)]]
    apply(subst fprod.positive_integral_cong_measure[THEN sym, of "\<lambda>A. lmeasure (p2e ` A)"])
    unfolding U_def[symmetric] *[THEN sym] o_def
  proof- fix A assume A:"A \<in> sets (sigma_algebra.vimage_algebra borel U (p2e ::_ \<Rightarrow> 'a))"
    hence *:"A \<subseteq> extensional {..<DIM('a)}" unfolding U_def by auto
    from A guess B unfolding borel.in_vimage_algebra U_def ..
    then have "(p2e ` A::'a set) \<in> sets borel"
      by (simp add: p2e_inv_extensional[of B, symmetric])
    from lmeasure_measure_eq_borel_prod[OF this] show "lmeasure (p2e ` A::'a set) =
      finite_product_sigma_finite.measure (\<lambda>x. borel) (\<lambda>x. lmeasure) {..<DIM('a)} A"
      unfolding e2p_p2e'[OF *] .
  qed auto
qed

lemma borel_fubini:
  fixes f :: "'a::ordered_euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel"
  shows "borel.integral f = borel_product.product_integral {..<DIM('a)} (f \<circ> p2e)"
proof- interpret fprod: finite_product_sigma_finite "\<lambda>x. borel" "\<lambda>x. lmeasure" "{..<DIM('a)}" by default auto
  have 1:"(\<lambda>x. Real (f x)) \<in> borel_measurable borel" using f by auto
  have 2:"(\<lambda>x. Real (- f x)) \<in> borel_measurable borel" using f by auto
  show ?thesis unfolding fprod.integral_def borel.integral_def
    unfolding borel_fubini_positiv_integral[OF 1] borel_fubini_positiv_integral[OF 2]
    unfolding o_def ..
qed

end
