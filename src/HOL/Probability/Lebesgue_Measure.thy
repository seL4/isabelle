(*  Author: Robert Himmelmann, TU Muenchen *)
header {* Lebsegue measure *}
theory Lebesgue_Measure
  imports Product_Measure Gauge_Measure Complete_Measure
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

lemma Union_inter_cube:"\<Union>{s \<inter> cube n |n. n \<in> UNIV} = s"
proof safe case goal1
  from mem_big_cube[of x] guess n . note n=this
  show ?case unfolding Union_iff apply(rule_tac x="s \<inter> cube n" in bexI)
    using n goal1 by auto
qed

lemma gmeasurable_cube[intro]:"gmeasurable (cube n)"
  unfolding cube_def by auto

lemma gmeasure_le_inter_cube[intro]: fixes s::"'a::ordered_euclidean_space set"
  assumes "gmeasurable (s \<inter> cube n)" shows "gmeasure (s \<inter> cube n) \<le> gmeasure (cube n::'a set)"
  apply(rule has_gmeasure_subset[of "s\<inter>cube n" _ "cube n"])
  unfolding has_gmeasure_measure[THEN sym] using assms by auto

lemma has_gmeasure_cube[intro]: "(cube n::('a::ordered_euclidean_space) set)
  has_gmeasure ((2 * real n) ^ (DIM('a)))"
proof-
  have "content {\<chi>\<chi> i. - real n..(\<chi>\<chi> i. real n)::'a} = (2 * real n) ^ (DIM('a))"
    apply(subst content_closed_interval) defer
    by (auto simp add:setprod_constant)
  thus ?thesis unfolding cube_def
    using has_gmeasure_interval(1)[of "(\<chi>\<chi> i. - real n)::'a" "(\<chi>\<chi> i. real n)::'a"]
    by auto
qed

lemma gmeasure_cube_eq[simp]:
  "gmeasure (cube n::('a::ordered_euclidean_space) set) = (2 * real n) ^ DIM('a)"
  by (intro measure_unique) auto

lemma gmeasure_cube_ge_n: "gmeasure (cube n::('a::ordered_euclidean_space) set) \<ge> real n"
proof cases
  assume "n = 0" then show ?thesis by simp
next
  assume "n \<noteq> 0"
  have "real n \<le> (2 * real n)^1" by simp
  also have "\<dots> \<le> (2 * real n)^DIM('a)"
    using DIM_positive[where 'a='a] `n \<noteq> 0`
    by (intro power_increasing) auto
  also have "\<dots> = gmeasure (cube n::'a set)" by simp
  finally show ?thesis .
qed

lemma gmeasure_setsum:
  assumes "finite A" and "\<And>s t. s \<in> A \<Longrightarrow> t \<in> A \<Longrightarrow> s \<noteq> t \<Longrightarrow> f s \<inter> f t = {}"
    and "\<And>i. i \<in> A \<Longrightarrow> gmeasurable (f i)"
  shows "gmeasure (\<Union>i\<in>A. f i) = (\<Sum>i\<in>A. gmeasure (f i))"
proof -
  have "gmeasure (\<Union>i\<in>A. f i) = gmeasure (\<Union>f ` A)" by auto
  also have "\<dots> = setsum gmeasure (f ` A)" using assms
  proof (intro measure_negligible_unions)
    fix X Y assume "X \<in> f`A" "Y \<in> f`A" "X \<noteq> Y"
    then have "X \<inter> Y = {}" using assms by auto
    then show "negligible (X \<inter> Y)" by auto
  qed auto
  also have "\<dots> = setsum gmeasure (f ` A - {{}})"
    using assms by (intro setsum_mono_zero_cong_right) auto
  also have "\<dots> = (\<Sum>i\<in>A - {i. f i = {}}. gmeasure (f i))"
  proof (intro setsum_reindex_cong inj_onI)
    fix s t assume *: "s \<in> A - {i. f i = {}}" "t \<in> A - {i. f i = {}}" "f s = f t"
    show "s = t"
    proof (rule ccontr)
      assume "s \<noteq> t" with assms(2)[of s t] * show False by auto
    qed
  qed auto
  also have "\<dots> = (\<Sum>i\<in>A. gmeasure (f i))"
    using assms by (intro setsum_mono_zero_cong_left) auto
  finally show ?thesis .
qed

lemma gmeasurable_finite_UNION[intro]:
  assumes "\<And>i. i \<in> S \<Longrightarrow> gmeasurable (A i)" "finite S"
  shows "gmeasurable (\<Union>i\<in>S. A i)"
  unfolding UNION_eq_Union_image using assms
  by (intro gmeasurable_finite_unions) auto

lemma gmeasurable_countable_UNION[intro]:
  fixes A :: "nat \<Rightarrow> ('a::ordered_euclidean_space) set"
  assumes measurable: "\<And>i. gmeasurable (A i)"
    and finite: "\<And>n. gmeasure (UNION {.. n} A) \<le> B"
  shows "gmeasurable (\<Union>i. A i)"
proof -
  have *: "\<And>n. \<Union>{A k |k. k \<le> n} = (\<Union>i\<le>n. A i)"
    "(\<Union>{A n |n. n \<in> UNIV}) = (\<Union>i. A i)" by auto
  show ?thesis
    by (rule gmeasurable_countable_unions_strong[of A B, unfolded *, OF assms])
qed

subsection {* Measurability *}

definition lebesgue :: "'a::ordered_euclidean_space algebra" where
  "lebesgue = \<lparr> space = UNIV, sets = {A. \<forall>n. gmeasurable (A \<inter> cube n)} \<rparr>"

lemma space_lebesgue[simp]:"space lebesgue = UNIV"
  unfolding lebesgue_def by auto

lemma lebesgueD[dest]: assumes "S \<in> sets lebesgue"
  shows "\<And>n. gmeasurable (S \<inter> cube n)"
  using assms unfolding lebesgue_def by auto

lemma lebesgueI[intro]: assumes "gmeasurable S"
  shows "S \<in> sets lebesgue" unfolding lebesgue_def cube_def
  using assms gmeasurable_interval by auto

lemma lebesgueI2: "(\<And>n. gmeasurable (S \<inter> cube n)) \<Longrightarrow> S \<in> sets lebesgue"
  using assms unfolding lebesgue_def by auto

interpretation lebesgue: sigma_algebra lebesgue
proof
  show "sets lebesgue \<subseteq> Pow (space lebesgue)"
    unfolding lebesgue_def by auto
  show "{} \<in> sets lebesgue"
    using gmeasurable_empty by auto
  { fix A B :: "'a set" assume "A \<in> sets lebesgue" "B \<in> sets lebesgue"
    then show "A \<union> B \<in> sets lebesgue"
      by (auto intro: gmeasurable_union simp: lebesgue_def Int_Un_distrib2) }
  { fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> sets lebesgue"
    show "(\<Union>i. A i) \<in> sets lebesgue"
    proof (rule lebesgueI2)
      fix n show "gmeasurable ((\<Union>i. A i) \<inter> cube n)" unfolding UN_extend_simps
        using A
        by (intro gmeasurable_countable_UNION[where B="gmeasure (cube n::'a set)"])
           (auto intro!: measure_subset gmeasure_setsum simp: UN_extend_simps simp del: gmeasure_cube_eq UN_simps)
    qed }
  { fix A assume A: "A \<in> sets lebesgue" show "space lebesgue - A \<in> sets lebesgue"
    proof (rule lebesgueI2)
      fix n
      have *: "(space lebesgue - A) \<inter> cube n = cube n - (A \<inter> cube n)"
        unfolding lebesgue_def by auto
      show "gmeasurable ((space lebesgue - A) \<inter> cube n)" unfolding *
        using A by (auto intro!: gmeasurable_diff)
    qed }
qed

lemma lebesgueI_borel[intro, simp]: fixes s::"'a::ordered_euclidean_space set"
  assumes "s \<in> sets borel" shows "s \<in> sets lebesgue"
proof- let ?S = "range (\<lambda>(a, b). {a .. (b :: 'a\<Colon>ordered_euclidean_space)})"
  have *:"?S \<subseteq> sets lebesgue" by auto
  have "s \<in> sigma_sets UNIV ?S" using assms
    unfolding borel_eq_atLeastAtMost by (simp add: sigma_def)
  thus ?thesis
    using lebesgue.sigma_subset[of "\<lparr> space = UNIV, sets = ?S\<rparr>", simplified, OF *]
    by (auto simp: sigma_def)
qed

lemma lebesgueI_negligible[dest]: fixes s::"'a::ordered_euclidean_space set"
  assumes "negligible s" shows "s \<in> sets lebesgue"
proof (rule lebesgueI2)
  fix n
  have *:"\<And>x. (if x \<in> cube n then indicator s x else 0) = (if x \<in> s \<inter> cube n then 1 else 0)"
    unfolding indicator_def_raw by auto
  note assms[unfolded negligible_def,rule_format,of "(\<chi>\<chi> i. - real n)::'a" "\<chi>\<chi> i. real n"]
  thus "gmeasurable (s \<inter> cube n)" apply-apply(rule gmeasurableI[of _ 0]) unfolding has_gmeasure_def
    apply(subst(asm) has_integral_restrict_univ[THEN sym]) unfolding cube_def[symmetric]
    apply(subst has_integral_restrict_univ[THEN sym]) unfolding * .
qed

section {* The Lebesgue Measure *}

definition "lmeasure A = (SUP n. Real (gmeasure (A \<inter> cube n)))"

lemma lmeasure_eq_0: assumes "negligible S" shows "lmeasure S = 0"
proof -
  from lebesgueI_negligible[OF assms]
  have "\<And>n. gmeasurable (S \<inter> cube n)" by auto
  from gmeasurable_measure_eq_0[OF this]
  have "\<And>n. gmeasure (S \<inter> cube n) = 0" using assms by auto
  then show ?thesis unfolding lmeasure_def by simp
qed

lemma lmeasure_iff_LIMSEQ:
  assumes "A \<in> sets lebesgue" "0 \<le> m"
  shows "lmeasure A = Real m \<longleftrightarrow> (\<lambda>n. (gmeasure (A \<inter> cube n))) ----> m"
  unfolding lmeasure_def using assms cube_subset[where 'a='a]
  by (intro SUP_eq_LIMSEQ monoI measure_subset) force+

interpretation lebesgue: measure_space lebesgue lmeasure
proof
  show "lmeasure {} = 0"
    by (auto intro!: lmeasure_eq_0)
  show "countably_additive lebesgue lmeasure"
  proof (unfold countably_additive_def, intro allI impI conjI)
    fix A :: "nat \<Rightarrow> 'b set" assume "range A \<subseteq> sets lebesgue" "disjoint_family A"
    then have A: "\<And>i. A i \<in> sets lebesgue" by auto
    show "(\<Sum>\<^isub>\<infinity>n. lmeasure (A n)) = lmeasure (\<Union>i. A i)" unfolding lmeasure_def
    proof (subst psuminf_SUP_eq)
      { fix i n
        have "gmeasure (A i \<inter> cube n) \<le> gmeasure (A i \<inter> cube (Suc n))"
          using A cube_subset[of n "Suc n"] by (auto intro!: measure_subset)
        then show "Real (gmeasure (A i \<inter> cube n)) \<le> Real (gmeasure (A i \<inter> cube (Suc n)))"
          by auto }
      show "(SUP n. \<Sum>\<^isub>\<infinity>i. Real (gmeasure (A i \<inter> cube n))) = (SUP n. Real (gmeasure ((\<Union>i. A i) \<inter> cube n)))"
      proof (intro arg_cong[where f="SUPR UNIV"] ext)
        fix n
        have sums: "(\<lambda>i. gmeasure (A i \<inter> cube n)) sums gmeasure (\<Union>{A i \<inter> cube n |i. i \<in> UNIV})"
        proof (rule has_gmeasure_countable_negligible_unions(2))
          fix i show "gmeasurable (A i \<inter> cube n)" using A by auto
        next
          fix i m :: nat assume "m \<noteq> i"
          then have "A m \<inter> cube n \<inter> (A i \<inter> cube n) = {}"
            using `disjoint_family A` unfolding disjoint_family_on_def by auto
          then show "negligible (A m \<inter> cube n \<inter> (A i \<inter> cube n))" by auto
        next
          fix i
          have "(\<Sum>k = 0..i. gmeasure (A k \<inter> cube n)) = gmeasure (\<Union>k\<le>i . A k \<inter> cube n)"
            unfolding atLeast0AtMost using A
          proof (intro gmeasure_setsum[symmetric])
            fix s t :: nat assume "s \<noteq> t" then have "A t \<inter> A s = {}"
              using `disjoint_family A` unfolding disjoint_family_on_def by auto
            then show "A s \<inter> cube n \<inter> (A t \<inter> cube n) = {}" by auto
          qed auto
          also have "\<dots> \<le> gmeasure (cube n :: 'b set)" using A
            by (intro measure_subset gmeasurable_finite_UNION) auto
          finally show "(\<Sum>k = 0..i. gmeasure (A k \<inter> cube n)) \<le> gmeasure (cube n :: 'b set)" .
        qed
        show "(\<Sum>\<^isub>\<infinity>i. Real (gmeasure (A i \<inter> cube n))) = Real (gmeasure ((\<Union>i. A i) \<inter> cube n))"
          unfolding psuminf_def
          apply (subst setsum_Real)
          apply (simp add: measure_pos_le)
        proof (rule SUP_eq_LIMSEQ[THEN iffD2])
          have "(\<Union>{A i \<inter> cube n |i. i \<in> UNIV}) = (\<Union>i. A i) \<inter> cube n" by auto
          with sums show "(\<lambda>i. \<Sum>k<i. gmeasure (A k \<inter> cube n)) ----> gmeasure ((\<Union>i. A i) \<inter> cube n)"
            unfolding sums_def atLeast0LessThan by simp
        qed (auto intro!: monoI setsum_nonneg setsum_mono2)
      qed
    qed
  qed
qed

lemma lmeasure_finite_has_gmeasure: assumes "s \<in> sets lebesgue" "lmeasure s = Real m" "0 \<le> m"
  shows "s has_gmeasure m"
proof-
  have *:"(\<lambda>n. (gmeasure (s \<inter> cube n))) ----> m"
    using `lmeasure s = Real m` unfolding lmeasure_iff_LIMSEQ[OF `s \<in> sets lebesgue` `0 \<le> m`] .
  have s: "\<And>n. gmeasurable (s \<inter> cube n)" using assms by auto
  have "(\<lambda>x. if x \<in> s then 1 else (0::real)) integrable_on UNIV \<and>
    (\<lambda>k. integral UNIV (\<lambda>x. if x \<in> s \<inter> cube k then 1 else (0::real)))
    ----> integral UNIV (\<lambda>x. if x \<in> s then 1 else 0)"
  proof(rule monotone_convergence_increasing)
    have "lmeasure s \<le> Real m" using `lmeasure s = Real m` by simp
    then have "\<forall>n. gmeasure (s \<inter> cube n) \<le> m"
      unfolding lmeasure_def complete_lattice_class.SUP_le_iff
      using `0 \<le> m` by (auto simp: measure_pos_le)
    thus *:"bounded {integral UNIV (\<lambda>x. if x \<in> s \<inter> cube k then 1 else (0::real)) |k. True}"
      unfolding integral_measure_univ[OF s] bounded_def apply-
      apply(rule_tac x=0 in exI,rule_tac x=m in exI) unfolding dist_real_def
      by (auto simp: measure_pos_le)
    show "\<forall>k. (\<lambda>x. if x \<in> s \<inter> cube k then (1::real) else 0) integrable_on UNIV"
      unfolding integrable_restrict_univ
      using s unfolding gmeasurable_def has_gmeasure_def by auto
    have *:"\<And>n. n \<le> Suc n" by auto
    show "\<forall>k. \<forall>x\<in>UNIV. (if x \<in> s \<inter> cube k then 1 else 0) \<le> (if x \<in> s \<inter> cube (Suc k) then 1 else (0::real))"
      using cube_subset[OF *] by fastsimp
    show "\<forall>x\<in>UNIV. (\<lambda>k. if x \<in> s \<inter> cube k then 1 else 0) ----> (if x \<in> s then 1 else (0::real))"
      unfolding Lim_sequentially
    proof safe case goal1 from real_arch_lt[of "norm x"] guess N .. note N = this
      show ?case apply(rule_tac x=N in exI)
      proof safe case goal1
        have "x \<in> cube n" using cube_subset[OF goal1] N
          using ball_subset_cube[of N] by(auto simp: dist_norm)
        thus ?case using `e>0` by auto
      qed
    qed
  qed note ** = conjunctD2[OF this]
  hence *:"m = integral UNIV (\<lambda>x. if x \<in> s then 1 else 0)" apply-
    apply(rule LIMSEQ_unique[OF _ **(2)]) unfolding measure_integral_univ[THEN sym,OF s] using * .
  show ?thesis unfolding has_gmeasure * apply(rule integrable_integral) using ** by auto
qed

lemma lmeasure_finite_gmeasurable: assumes "s \<in> sets lebesgue" "lmeasure s \<noteq> \<omega>"
  shows "gmeasurable s"
proof (cases "lmeasure s")
  case (preal m) from lmeasure_finite_has_gmeasure[OF `s \<in> sets lebesgue` this]
  show ?thesis unfolding gmeasurable_def by auto
qed (insert assms, auto)

lemma has_gmeasure_lmeasure: assumes "s has_gmeasure m"
  shows "lmeasure s = Real m"
proof-
  have gmea:"gmeasurable s" using assms by auto
  then have s: "s \<in> sets lebesgue" by auto
  have m:"m \<ge> 0" using assms by auto
  have *:"m = gmeasure (\<Union>{s \<inter> cube n |n. n \<in> UNIV})" unfolding Union_inter_cube
    using assms by(rule measure_unique[THEN sym])
  show ?thesis
    unfolding lmeasure_iff_LIMSEQ[OF s `0 \<le> m`] unfolding *
    apply(rule gmeasurable_nested_unions[THEN conjunct2, where B1="gmeasure s"])
  proof- fix n::nat show *:"gmeasurable (s \<inter> cube n)"
      using gmeasurable_inter[OF gmea gmeasurable_cube] .
    show "gmeasure (s \<inter> cube n) \<le> gmeasure s" apply(rule measure_subset)
      apply(rule * gmea)+ by auto
    show "s \<inter> cube n \<subseteq> s \<inter> cube (Suc n)" using cube_subset[of n "Suc n"] by auto
  qed
qed

lemma has_gmeasure_iff_lmeasure:
  "A has_gmeasure m \<longleftrightarrow> (A \<in> sets lebesgue \<and> 0 \<le> m \<and> lmeasure A = Real m)"
proof
  assume "A has_gmeasure m"
  with has_gmeasure_lmeasure[OF this]
  have "gmeasurable A" "0 \<le> m" "lmeasure A = Real m" by auto
  then show "A \<in> sets lebesgue \<and> 0 \<le> m \<and> lmeasure A = Real m" by auto
next
  assume "A \<in> sets lebesgue \<and> 0 \<le> m \<and> lmeasure A = Real m"
  then show "A has_gmeasure m" by (intro lmeasure_finite_has_gmeasure) auto
qed

lemma gmeasure_lmeasure: assumes "gmeasurable s" shows "lmeasure s = Real (gmeasure s)"
proof -
  note has_gmeasure_measureI[OF assms]
  note has_gmeasure_lmeasure[OF this]
  thus ?thesis .
qed

lemma lebesgue_simple_function_indicator:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> pextreal"
  assumes f:"lebesgue.simple_function f"
  shows "f = (\<lambda>x. (\<Sum>y \<in> f ` UNIV. y * indicator (f -` {y}) x))"
  apply(rule,subst lebesgue.simple_function_indicator_representation[OF f]) by auto

lemma lmeasure_gmeasure:
  "gmeasurable s \<Longrightarrow> gmeasure s = real (lmeasure s)"
  by (subst gmeasure_lmeasure) auto

lemma lmeasure_finite: assumes "gmeasurable s" shows "lmeasure s \<noteq> \<omega>"
  using gmeasure_lmeasure[OF assms] by auto

lemma negligible_iff_lebesgue_null_sets:
  "negligible A \<longleftrightarrow> A \<in> lebesgue.null_sets"
proof
  assume "negligible A"
  from this[THEN lebesgueI_negligible] this[THEN lmeasure_eq_0]
  show "A \<in> lebesgue.null_sets" by auto
next
  assume A: "A \<in> lebesgue.null_sets"
  then have *:"gmeasurable A" using lmeasure_finite_gmeasurable[of A] by auto
  show "negligible A"
    unfolding gmeasurable_measure_eq_0[OF *, symmetric]
    unfolding lmeasure_gmeasure[OF *] using A by auto
qed

lemma
  fixes a b ::"'a::ordered_euclidean_space"
  shows lmeasure_atLeastAtMost[simp]: "lmeasure {a..b} = Real (content {a..b})"
    and lmeasure_greaterThanLessThan[simp]: "lmeasure {a <..< b} = Real (content {a..b})"
  using has_gmeasure_interval[of a b] by (auto intro!: has_gmeasure_lmeasure)

lemma lmeasure_cube:
  "lmeasure (cube n::('a::ordered_euclidean_space) set) = (Real ((2 * real n) ^ (DIM('a))))"
  by (intro has_gmeasure_lmeasure) auto

lemma lmeasure_UNIV[intro]: "lmeasure UNIV = \<omega>"
  unfolding lmeasure_def SUP_\<omega>
proof (intro allI impI)
  fix x assume "x < \<omega>"
  then obtain r where r: "x = Real r" "0 \<le> r" by (cases x) auto
  then obtain n where n: "r < of_nat n" using ex_less_of_nat by auto
  show "\<exists>i\<in>UNIV. x < Real (gmeasure (UNIV \<inter> cube i))"
  proof (intro bexI[of _ n])
    have "x < Real (of_nat n)" using n r by auto
    also have "Real (of_nat n) \<le> Real (gmeasure (UNIV \<inter> cube n))"
      using gmeasure_cube_ge_n[of n] by (auto simp: real_eq_of_nat[symmetric])
    finally show "x < Real (gmeasure (UNIV \<inter> cube n))" .
  qed auto
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
  using has_gmeasure_interval[of a a] unfolding zero_pextreal_def
  by (intro has_gmeasure_lmeasure)
     (simp add: content_closed_interval DIM_positive)

declare content_real[simp]

lemma
  fixes a b :: real
  shows lmeasure_real_greaterThanAtMost[simp]:
    "lmeasure {a <.. b} = Real (if a \<le> b then b - a else 0)"
proof cases
  assume "a < b"
  then have "lmeasure {a <.. b} = lmeasure {a <..< b} + lmeasure {b}"
    by (subst lebesgue.measure_additive)
       (auto intro!: lebesgueI_borel arg_cong[where f=lmeasure])
  then show ?thesis by auto
qed auto

lemma
  fixes a b :: real
  shows lmeasure_real_atLeastLessThan[simp]:
    "lmeasure {a ..< b} = Real (if a \<le> b then b - a else 0)" (is ?eqlt)
proof cases
  assume "a < b"
  then have "lmeasure {a ..< b} = lmeasure {a} + lmeasure {a <..< b}"
    by (subst lebesgue.measure_additive)
       (auto intro!: lebesgueI_borel arg_cong[where f=lmeasure])
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
  show "\<forall>i. lmeasure (cube i) \<noteq> \<omega>" unfolding lmeasure_cube by auto
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
proof- case goal1
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
      have mea:"gmeasurable (f -` {f y})" apply(rule lmeasure_finite_gmeasurable)
        using assms unfolding lebesgue.simple_function_def using False by auto
      have *:"\<And>x. real (indicator (f -` {f y}) x::pextreal) = (if x \<in> f -` {f y} then 1 else 0)" by auto
      show ?thesis unfolding real_of_pextreal_mult[THEN sym]
        apply(rule has_integral_cmul[where 'b=real, unfolded real_scaleR_def])
        unfolding Int_UNIV_right lmeasure_gmeasure[OF mea,THEN sym]
        unfolding measure_integral_univ[OF mea] * apply(rule integrable_integral)
        unfolding gmeasurable_integrable[THEN sym] using mea .
    qed auto
  qed qed

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
  have "(SUP i. f i) = u" using mono lim SUP_Lim_pextreal
    unfolding fun_eq_iff SUPR_fun_expand mono_def by auto
  moreover have "(SUP i. f i) \<in> borel_measurable M"
    using i by (rule borel_measurable_SUP)
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

lemma continuous_on_imp_borel_measurable:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::ordered_euclidean_space"
  assumes "continuous_on UNIV f"
  shows "f \<in> borel_measurable lebesgue"
  apply(rule lebesgue.borel_measurableI)
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

lemma bij_euclidean_component:
  "bij_betw (e2p::'a::ordered_euclidean_space \<Rightarrow> _) (UNIV :: 'a set)
  ({..<DIM('a)} \<rightarrow>\<^isub>E (UNIV :: real set))"
  unfolding bij_betw_def e2p_def_raw
proof let ?e = "\<lambda>x.\<lambda>i\<in>{..<DIM('a::ordered_euclidean_space)}. (x::'a)$$i"
  show "inj ?e" unfolding inj_on_def restrict_def apply(subst euclidean_eq) apply safe
    apply(drule_tac x=i in fun_cong) by auto
  { fix x::"nat \<Rightarrow> real" assume x:"\<forall>i. i \<notin> {..<DIM('a)} \<longrightarrow> x i = undefined"
    hence "x = ?e (\<chi>\<chi> i. x i)" apply-apply(rule,case_tac "xa<DIM('a)") by auto
    hence "x \<in> range ?e" by fastsimp
  } thus "range ?e = ({..<DIM('a)} \<rightarrow> UNIV) \<inter> extensional {..<DIM('a)}"
    unfolding extensional_def using DIM_positive by auto
qed

lemma bij_p2e:
  "bij_betw (p2e::_ \<Rightarrow> 'a::ordered_euclidean_space) ({..<DIM('a)} \<rightarrow>\<^isub>E (UNIV :: real set))
  (UNIV :: 'a set)" (is "bij_betw ?p ?U _")
  unfolding bij_betw_def
proof show "inj_on ?p ?U" unfolding inj_on_def p2e_def
    apply(subst euclidean_eq) apply(safe,rule) unfolding extensional_def
    apply(case_tac "xa<DIM('a)") by auto
  { fix x::'a have "x \<in> ?p ` extensional {..<DIM('a)}"
      unfolding image_iff apply(rule_tac x="\<lambda>i. if i<DIM('a) then x$$i else undefined" in bexI)
      apply(subst euclidean_eq,safe) unfolding p2e_def extensional_def by auto
  } thus "?p ` ?U = UNIV" by auto
qed

lemma e2p_p2e[simp]: fixes z::"'a::ordered_euclidean_space"
  assumes "x \<in> extensional {..<DIM('a)}"
  shows "e2p (p2e x::'a) = x"
proof fix i::nat
  show "e2p (p2e x::'a) i = x i" unfolding e2p_def p2e_def restrict_def
    using assms unfolding extensional_def by auto
qed

lemma p2e_e2p[simp]: fixes x::"'a::ordered_euclidean_space"
  shows "p2e (e2p x) = x"
  apply(subst euclidean_eq) unfolding e2p_def p2e_def restrict_def by auto

interpretation borel_product: product_sigma_finite "\<lambda>x. borel::real algebra" "\<lambda>x. lmeasure"
  by default

lemma cube_subset_Suc[intro]: "cube n \<subseteq> cube (Suc n)"
  unfolding cube_def_raw subset_eq apply safe unfolding mem_interval by auto

lemma borel_vimage_algebra_eq:
  "sigma_algebra.vimage_algebra
         (borel :: ('a::ordered_euclidean_space) algebra) ({..<DIM('a)} \<rightarrow>\<^isub>E UNIV) p2e =
  sigma (product_algebra (\<lambda>x. \<lparr> space = UNIV::real set, sets = range (\<lambda>a. {..<a}) \<rparr>) {..<DIM('a)} )"
proof- note bor = borel_eq_lessThan
  def F \<equiv> "product_algebra (\<lambda>x. \<lparr> space = UNIV::real set, sets = range (\<lambda>a. {..<a}) \<rparr>) {..<DIM('a)}"
  def E \<equiv> "\<lparr>space = (UNIV::'a set), sets = range lessThan\<rparr>"
  have *:"(({..<DIM('a)} \<rightarrow> UNIV) \<inter> extensional {..<DIM('a)}) = space F" unfolding F_def by auto
  show ?thesis unfolding F_def[symmetric] * bor
  proof(rule vimage_algebra_sigma,unfold E_def[symmetric])
    show "sets E \<subseteq> Pow (space E)" "p2e \<in> space F \<rightarrow> space E" unfolding E_def by auto
  next fix A assume "A \<in> sets F"
    hence A:"A \<in> (Pi\<^isub>E {..<DIM('a)}) ` ({..<DIM('a)} \<rightarrow> range lessThan)"
      unfolding F_def product_algebra_def algebra.simps .
    then guess B unfolding image_iff .. note B=this
    hence "\<forall>x<DIM('a). B x \<in> range lessThan" by auto
    hence "\<forall>x. \<exists>xa. x<DIM('a) \<longrightarrow> B x = {..<xa}" unfolding image_iff by auto
    from choice[OF this] guess b .. note b=this
    hence b':"\<forall>i<DIM('a). Sup (B i) = b i" using Sup_lessThan by auto

    show "A \<in> (\<lambda>X. p2e -` X \<inter> space F) ` sets E" unfolding image_iff B
    proof(rule_tac x="{..< \<chi>\<chi> i. Sup (B i)}" in bexI)
      show "Pi\<^isub>E {..<DIM('a)} B = p2e -` {..<(\<chi>\<chi> i. Sup (B i))::'a} \<inter> space F"
        unfolding F_def E_def product_algebra_def algebra.simps
      proof(rule,unfold subset_eq,rule_tac[!] ballI)
        fix x assume "x \<in> Pi\<^isub>E {..<DIM('a)} B"
        hence *:"\<forall>i<DIM('a). x i < b i" "\<forall>i\<ge>DIM('a). x i = undefined"
          unfolding Pi_def extensional_def using b by auto
        have "(p2e x::'a) < (\<chi>\<chi> i. Sup (B i))" unfolding less_prod_def eucl_less[of "p2e x"]
          apply safe unfolding euclidean_lambda_beta b'[rule_format] p2e_def using * by auto
        moreover have "x \<in> extensional {..<DIM('a)}"
          using *(2) unfolding extensional_def by auto
        ultimately show "x \<in> p2e -` {..<(\<chi>\<chi> i. Sup (B i)) ::'a} \<inter>
          (({..<DIM('a)} \<rightarrow> UNIV) \<inter> extensional {..<DIM('a)})" by auto
      next fix x assume as:"x \<in> p2e -` {..<(\<chi>\<chi> i. Sup (B i))::'a} \<inter>
          (({..<DIM('a)} \<rightarrow> UNIV) \<inter> extensional {..<DIM('a)})"
        hence "p2e x < ((\<chi>\<chi> i. Sup (B i))::'a)" by auto
        hence "\<forall>i<DIM('a). x i \<in> B i" apply-apply(subst(asm) eucl_less)
          unfolding p2e_def using b b' by auto
        thus "x \<in> Pi\<^isub>E {..<DIM('a)} B" using as unfolding Pi_def extensional_def by auto
      qed
      show "{..<(\<chi>\<chi> i. Sup (B i))::'a} \<in> sets E" unfolding E_def algebra.simps by auto
    qed
  next fix A assume "A \<in> sets E"
    then guess a unfolding E_def algebra.simps image_iff .. note a = this(2)
    def B \<equiv> "\<lambda>i. {..<a $$ i}"
    show "p2e -` A \<inter> space F \<in> sets F" unfolding F_def
      unfolding product_algebra_def algebra.simps image_iff
      apply(rule_tac x=B in bexI) apply rule unfolding subset_eq apply(rule_tac[1-2] ballI)
    proof- show "B \<in> {..<DIM('a)} \<rightarrow> range lessThan" unfolding B_def by auto
      fix x assume as:"x \<in> p2e -` A \<inter> (({..<DIM('a)} \<rightarrow> UNIV) \<inter> extensional {..<DIM('a)})"
      hence "p2e x \<in> A" by auto
      hence "\<forall>i<DIM('a). x i \<in> B i" unfolding B_def a lessThan_iff
        apply-apply(subst (asm) eucl_less) unfolding p2e_def by auto
      thus "x \<in> Pi\<^isub>E {..<DIM('a)} B" using as unfolding Pi_def extensional_def by auto
    next fix x assume x:"x \<in> Pi\<^isub>E {..<DIM('a)} B"
      moreover have "p2e x \<in> A" unfolding a lessThan_iff p2e_def apply(subst eucl_less)
        using x unfolding Pi_def extensional_def B_def by auto
      ultimately show "x \<in> p2e -` A \<inter> (({..<DIM('a)} \<rightarrow> UNIV) \<inter> extensional {..<DIM('a)})" by auto
    qed
  qed
qed

lemma e2p_Int:"e2p ` A \<inter> e2p ` B = e2p ` (A \<inter> B)" (is "?L = ?R")
  apply(rule image_Int[THEN sym]) using bij_euclidean_component
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

lemma product_borel_eq_vimage:
  "sigma (product_algebra (\<lambda>x. borel) {..<DIM('a::ordered_euclidean_space)}) =
  sigma_algebra.vimage_algebra borel (({..<DIM('a)} \<rightarrow> UNIV) \<inter> extensional {..<DIM('a)})
  (p2e:: _ \<Rightarrow> 'a::ordered_euclidean_space)"
  unfolding borel_vimage_algebra_eq unfolding borel_eq_lessThan
  apply(subst sigma_product_algebra_sigma_eq[where S="\<lambda>i. \<lambda>n. lessThan (real n)"])
  unfolding lessThan_iff
proof- fix i assume i:"i<DIM('a)"
  show "(\<lambda>n. {..<real n}) \<up> space \<lparr>space = UNIV, sets = range lessThan\<rparr>"
    by(auto intro!:real_arch_lt isotoneI)
qed auto

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
  shows "e2p ` A = p2e -` A \<inter> (({..<DIM('a)} \<rightarrow> UNIV) \<inter> extensional {..<DIM('a)})"
proof(rule set_eqI,rule)
  fix x assume "x \<in> e2p ` A" then guess y unfolding image_iff .. note y=this
  show "x \<in> p2e -` A \<inter> (({..<DIM('a)} \<rightarrow> UNIV) \<inter> extensional {..<DIM('a)})"
    apply safe apply(rule vimageI[OF _ y(1)]) unfolding y p2e_e2p by auto
next fix x assume "x \<in> p2e -` A \<inter> (({..<DIM('a)} \<rightarrow> UNIV) \<inter> extensional {..<DIM('a)})"
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
  show "\<And>i. lmeasure (cube i) \<noteq> \<omega>" unfolding lmeasure_cube by auto
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
        using bij_euclidean_component using A(2) unfolding bij_betw_def by auto
      show "(\<Union>n. e2p ` A n) \<in> sets (sigma (product_algebra (\<lambda>x. borel) {..<DIM('a)}))"
        unfolding product_borel_eq_vimage borel.in_vimage_algebra
      proof(rule bexI[OF _ A(3)],rule set_eqI,rule)
        fix x assume x:"x \<in> (\<Union>n. e2p ` A n)" hence "p2e x \<in> (\<Union>i. A i)" by auto
        moreover have "x \<in> extensional {..<DIM('a)}"
          using x unfolding extensional_def e2p_def_raw by auto
        ultimately show "x \<in> p2e -` (\<Union>i. A i) \<inter> (({..<DIM('a)} \<rightarrow> UNIV) \<inter>
          extensional {..<DIM('a)})" by auto
      next fix x assume x:"x \<in> p2e -` (\<Union>i. A i) \<inter> (({..<DIM('a)} \<rightarrow> UNIV) \<inter>
          extensional {..<DIM('a)})"
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
proof- def U \<equiv> "(({..<DIM('a)} \<rightarrow> UNIV) \<inter> extensional {..<DIM('a)}):: (nat \<Rightarrow> real) set"
  interpret fprod: finite_product_sigma_finite "\<lambda>x. borel" "\<lambda>x. lmeasure" "{..<DIM('a)}" by default auto
  have "\<And>x. \<exists>i::nat. x < real i" by (metis real_arch_lt)
  hence "(\<lambda>n::nat. {..<real n}) \<up> UNIV" apply-apply(rule isotoneI) by auto
  hence *:"sigma_algebra.vimage_algebra borel U (p2e:: _ \<Rightarrow> 'a)
    = sigma (product_algebra (\<lambda>x. borel) {..<DIM('a)})"
    unfolding U_def apply-apply(subst borel_vimage_algebra_eq)
    apply(subst sigma_product_algebra_sigma_eq[where S="\<lambda>x. \<lambda>n. {..<(\<chi>\<chi> i. real n)}", THEN sym])
    unfolding borel_eq_lessThan[THEN sym] by auto
  show ?thesis unfolding borel.positive_integral_vimage[unfolded space_borel,OF bij_p2e]
    apply(subst fprod.positive_integral_cong_measure[THEN sym, of "\<lambda>A. lmeasure (p2e ` A)"])
    unfolding U_def[symmetric] *[THEN sym] o_def
  proof- fix A assume A:"A \<in> sets (sigma_algebra.vimage_algebra borel U (p2e ::_ \<Rightarrow> 'a))"
    hence *:"A \<subseteq> extensional {..<DIM('a)}" unfolding U_def by auto
    from A guess B unfolding borel.in_vimage_algebra U_def .. note B=this
    have "(p2e ` A::'a set) \<in> sets borel" unfolding B apply(subst Int_left_commute)
      apply(subst Int_absorb1) unfolding p2e_inv_extensional[of B,THEN sym] using B(1) by auto
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
