(*  Title:      HOL/Probability/Bochner_Integration.thy
    Author:     Johannes Hölzl, TU München
*)

header {* Bochner Integration for Vector-Valued Functions *}

theory Bochner_Integration
  imports Finite_Product_Measure
begin

text {*

In the following development of the Bochner integral we use second countable topologies instead
of separable spaces. A second countable topology is also separable.

*}

lemma borel_measurable_implies_sequence_metric:
  fixes f :: "'a \<Rightarrow> 'b :: {metric_space, second_countable_topology}"
  assumes [measurable]: "f \<in> borel_measurable M"
  shows "\<exists>F. (\<forall>i. simple_function M (F i)) \<and> (\<forall>x\<in>space M. (\<lambda>i. F i x) ----> f x) \<and>
    (\<forall>i. \<forall>x\<in>space M. dist (F i x) z \<le> 2 * dist (f x) z)"
proof -
  obtain D :: "'b set" where "countable D" and D: "\<And>X. open X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>d\<in>D. d \<in> X"
    by (erule countable_dense_setE)

  def e \<equiv> "from_nat_into D"
  { fix n x
    obtain d where "d \<in> D" and d: "d \<in> ball x (1 / Suc n)"
      using D[of "ball x (1 / Suc n)"] by auto
    from `d \<in> D` D[of UNIV] `countable D` obtain i where "d = e i"
      unfolding e_def by (auto dest: from_nat_into_surj)
    with d have "\<exists>i. dist x (e i) < 1 / Suc n"
      by auto }
  note e = this

  def A \<equiv> "\<lambda>m n. {x\<in>space M. dist (f x) (e n) < 1 / (Suc m) \<and> 1 / (Suc m) \<le> dist (f x) z}"
  def B \<equiv> "\<lambda>m. disjointed (A m)"
  
  def m \<equiv> "\<lambda>N x. Max {m::nat. m \<le> N \<and> x \<in> (\<Union>n\<le>N. B m n)}"
  def F \<equiv> "\<lambda>N::nat. \<lambda>x. if (\<exists>m\<le>N. x \<in> (\<Union>n\<le>N. B m n)) \<and> (\<exists>n\<le>N. x \<in> B (m N x) n) 
    then e (LEAST n. x \<in> B (m N x) n) else z"

  have B_imp_A[intro, simp]: "\<And>x m n. x \<in> B m n \<Longrightarrow> x \<in> A m n"
    using disjointed_subset[of "A m" for m] unfolding B_def by auto

  { fix m
    have "\<And>n. A m n \<in> sets M"
      by (auto simp: A_def)
    then have "\<And>n. B m n \<in> sets M"
      using sets.range_disjointed_sets[of "A m" M] by (auto simp: B_def) }
  note this[measurable]

  { fix N i x assume "\<exists>m\<le>N. x \<in> (\<Union>n\<le>N. B m n)"
    then have "m N x \<in> {m::nat. m \<le> N \<and> x \<in> (\<Union>n\<le>N. B m n)}"
      unfolding m_def by (intro Max_in) auto
    then have "m N x \<le> N" "\<exists>n\<le>N. x \<in> B (m N x) n"
      by auto }
  note m = this

  { fix j N i x assume "j \<le> N" "i \<le> N" "x \<in> B j i"
    then have "j \<le> m N x"
      unfolding m_def by (intro Max_ge) auto }
  note m_upper = this

  show ?thesis
    unfolding simple_function_def
  proof (safe intro!: exI[of _ F])
    have [measurable]: "\<And>i. F i \<in> borel_measurable M"
      unfolding F_def m_def by measurable
    show "\<And>x i. F i -` {x} \<inter> space M \<in> sets M"
      by measurable

    { fix i
      { fix n x assume "x \<in> B (m i x) n"
        then have "(LEAST n. x \<in> B (m i x) n) \<le> n"
          by (intro Least_le)
        also assume "n \<le> i" 
        finally have "(LEAST n. x \<in> B (m i x) n) \<le> i" . }
      then have "F i ` space M \<subseteq> {z} \<union> e ` {.. i}"
        by (auto simp: F_def)
      then show "finite (F i ` space M)"
        by (rule finite_subset) auto }
    
    { fix N i n x assume "i \<le> N" "n \<le> N" "x \<in> B i n"
      then have 1: "\<exists>m\<le>N. x \<in> (\<Union> n\<le>N. B m n)" by auto
      from m[OF this] obtain n where n: "m N x \<le> N" "n \<le> N" "x \<in> B (m N x) n" by auto
      moreover
      def L \<equiv> "LEAST n. x \<in> B (m N x) n"
      have "dist (f x) (e L) < 1 / Suc (m N x)"
      proof -
        have "x \<in> B (m N x) L"
          using n(3) unfolding L_def by (rule LeastI)
        then have "x \<in> A (m N x) L"
          by auto
        then show ?thesis
          unfolding A_def by simp
      qed
      ultimately have "dist (f x) (F N x) < 1 / Suc (m N x)"
        by (auto simp add: F_def L_def) }
    note * = this

    fix x assume "x \<in> space M"
    show "(\<lambda>i. F i x) ----> f x"
    proof cases
      assume "f x = z"
      then have "\<And>i n. x \<notin> A i n"
        unfolding A_def by auto
      then have "\<And>i. F i x = z"
        by (auto simp: F_def)
      then show ?thesis
        using `f x = z` by auto
    next
      assume "f x \<noteq> z"

      show ?thesis
      proof (rule tendstoI)
        fix e :: real assume "0 < e"
        with `f x \<noteq> z` obtain n where "1 / Suc n < e" "1 / Suc n < dist (f x) z"
          by (metis dist_nz order_less_trans neq_iff nat_approx_posE)
        with `x\<in>space M` `f x \<noteq> z` have "x \<in> (\<Union>i. B n i)"
          unfolding A_def B_def UN_disjointed_eq using e by auto
        then obtain i where i: "x \<in> B n i" by auto

        show "eventually (\<lambda>i. dist (F i x) (f x) < e) sequentially"
          using eventually_ge_at_top[of "max n i"]
        proof eventually_elim
          fix j assume j: "max n i \<le> j"
          with i have "dist (f x) (F j x) < 1 / Suc (m j x)"
            by (intro *[OF _ _ i]) auto
          also have "\<dots> \<le> 1 / Suc n"
            using j m_upper[OF _ _ i]
            by (auto simp: field_simps)
          also note `1 / Suc n < e`
          finally show "dist (F j x) (f x) < e"
            by (simp add: less_imp_le dist_commute)
        qed
      qed
    qed
    fix i 
    { fix n m assume "x \<in> A n m"
      then have "dist (e m) (f x) + dist (f x) z \<le> 2 * dist (f x) z"
        unfolding A_def by (auto simp: dist_commute)
      also have "dist (e m) z \<le> dist (e m) (f x) + dist (f x) z"
        by (rule dist_triangle)
      finally (xtrans) have "dist (e m) z \<le> 2 * dist (f x) z" . }
    then show "dist (F i x) z \<le> 2 * dist (f x) z"
      unfolding F_def
      apply auto
      apply (rule LeastI2)
      apply auto
      done
  qed
qed

lemma real_indicator: "real (indicator A x :: ereal) = indicator A x"
  unfolding indicator_def by auto

lemma split_indicator_asm:
  "P (indicator S x) \<longleftrightarrow> \<not> ((x \<in> S \<and> \<not> P 1) \<or> (x \<notin> S \<and> \<not> P 0))"
  unfolding indicator_def by auto

lemma
  fixes f :: "'a \<Rightarrow> 'b::semiring_1" assumes "finite A"
  shows setsum_mult_indicator[simp]: "(\<Sum>x \<in> A. f x * indicator (B x) (g x)) = (\<Sum>x\<in>{x\<in>A. g x \<in> B x}. f x)"
  and setsum_indicator_mult[simp]: "(\<Sum>x \<in> A. indicator (B x) (g x) * f x) = (\<Sum>x\<in>{x\<in>A. g x \<in> B x}. f x)"
  unfolding indicator_def
  using assms by (auto intro!: setsum_mono_zero_cong_right split: split_if_asm)

lemma borel_measurable_induct_real[consumes 2, case_names set mult add seq]:
  fixes P :: "('a \<Rightarrow> real) \<Rightarrow> bool"
  assumes u: "u \<in> borel_measurable M" "\<And>x. 0 \<le> u x"
  assumes set: "\<And>A. A \<in> sets M \<Longrightarrow> P (indicator A)"
  assumes mult: "\<And>u c. 0 \<le> c \<Longrightarrow> u \<in> borel_measurable M \<Longrightarrow> (\<And>x. 0 \<le> u x) \<Longrightarrow> P u \<Longrightarrow> P (\<lambda>x. c * u x)"
  assumes add: "\<And>u v. u \<in> borel_measurable M \<Longrightarrow> (\<And>x. 0 \<le> u x) \<Longrightarrow> P u \<Longrightarrow> v \<in> borel_measurable M \<Longrightarrow> (\<And>x. 0 \<le> v x) \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> u x = 0 \<or> v x = 0) \<Longrightarrow> P v \<Longrightarrow> P (\<lambda>x. v x + u x)"
  assumes seq: "\<And>U. (\<And>i. U i \<in> borel_measurable M) \<Longrightarrow> (\<And>i x. 0 \<le> U i x) \<Longrightarrow> (\<And>i. P (U i)) \<Longrightarrow> incseq U \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. U i x) ----> u x) \<Longrightarrow> P u"
  shows "P u"
proof -
  have "(\<lambda>x. ereal (u x)) \<in> borel_measurable M" using u by auto
  from borel_measurable_implies_simple_function_sequence'[OF this]
  obtain U where U: "\<And>i. simple_function M (U i)" "incseq U" "\<And>i. \<infinity> \<notin> range (U i)" and
    sup: "\<And>x. (SUP i. U i x) = max 0 (ereal (u x))" and nn: "\<And>i x. 0 \<le> U i x"
    by blast

  def U' \<equiv> "\<lambda>i x. indicator (space M) x * real (U i x)"
  then have U'_sf[measurable]: "\<And>i. simple_function M (U' i)"
    using U by (auto intro!: simple_function_compose1[where g=real])

  show "P u"
  proof (rule seq)
    fix i show "U' i \<in> borel_measurable M" "\<And>x. 0 \<le> U' i x"
      using U nn by (auto
          intro: borel_measurable_simple_function 
          intro!: borel_measurable_real_of_ereal real_of_ereal_pos borel_measurable_times
          simp: U'_def zero_le_mult_iff)
    show "incseq U'"
      using U(2,3) nn
      by (auto simp: incseq_def le_fun_def image_iff eq_commute U'_def indicator_def
               intro!: real_of_ereal_positive_mono)
  next
    fix x assume x: "x \<in> space M"
    have "(\<lambda>i. U i x) ----> (SUP i. U i x)"
      using U(2) by (intro LIMSEQ_SUP) (auto simp: incseq_def le_fun_def)
    moreover have "(\<lambda>i. U i x) = (\<lambda>i. ereal (U' i x))"
      using x nn U(3) by (auto simp: fun_eq_iff U'_def ereal_real image_iff eq_commute)
    moreover have "(SUP i. U i x) = ereal (u x)"
      using sup u(2) by (simp add: max_def)
    ultimately show "(\<lambda>i. U' i x) ----> u x" 
      by simp
  next
    fix i
    have "U' i ` space M \<subseteq> real ` (U i ` space M)" "finite (U i ` space M)"
      unfolding U'_def using U(1) by (auto dest: simple_functionD)
    then have fin: "finite (U' i ` space M)"
      by (metis finite_subset finite_imageI)
    moreover have "\<And>z. {y. U' i z = y \<and> y \<in> U' i ` space M \<and> z \<in> space M} = (if z \<in> space M then {U' i z} else {})"
      by auto
    ultimately have U': "(\<lambda>z. \<Sum>y\<in>U' i`space M. y * indicator {x\<in>space M. U' i x = y} z) = U' i"
      by (simp add: U'_def fun_eq_iff)
    have "\<And>x. x \<in> U' i ` space M \<Longrightarrow> 0 \<le> x"
      using nn by (auto simp: U'_def real_of_ereal_pos)
    with fin have "P (\<lambda>z. \<Sum>y\<in>U' i`space M. y * indicator {x\<in>space M. U' i x = y} z)"
    proof induct
      case empty from set[of "{}"] show ?case
        by (simp add: indicator_def[abs_def])
    next
      case (insert x F)
      then show ?case
        by (auto intro!: add mult set setsum_nonneg split: split_indicator split_indicator_asm
                 simp del: setsum_mult_indicator simp: setsum_nonneg_eq_0_iff )
    qed
    with U' show "P (U' i)" by simp
  qed
qed

lemma scaleR_cong_right:
  fixes x :: "'a :: real_vector"
  shows "(x \<noteq> 0 \<Longrightarrow> r = p) \<Longrightarrow> r *\<^sub>R x = p *\<^sub>R x"
  by (cases "x = 0") auto

inductive simple_bochner_integrable :: "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_vector) \<Rightarrow> bool" for M f where
  "simple_function M f \<Longrightarrow> emeasure M {y\<in>space M. f y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow>
    simple_bochner_integrable M f"

lemma simple_bochner_integrable_compose2:
  assumes p_0: "p 0 0 = 0"
  shows "simple_bochner_integrable M f \<Longrightarrow> simple_bochner_integrable M g \<Longrightarrow>
    simple_bochner_integrable M (\<lambda>x. p (f x) (g x))"
proof (safe intro!: simple_bochner_integrable.intros elim!: simple_bochner_integrable.cases del: notI)
  assume sf: "simple_function M f" "simple_function M g"
  then show "simple_function M (\<lambda>x. p (f x) (g x))"
    by (rule simple_function_compose2)

  from sf have [measurable]:
      "f \<in> measurable M (count_space UNIV)"
      "g \<in> measurable M (count_space UNIV)"
    by (auto intro: measurable_simple_function)

  assume fin: "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>" "emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity>"
   
  have "emeasure M {x\<in>space M. p (f x) (g x) \<noteq> 0} \<le>
      emeasure M ({x\<in>space M. f x \<noteq> 0} \<union> {x\<in>space M. g x \<noteq> 0})"
    by (intro emeasure_mono) (auto simp: p_0)
  also have "\<dots> \<le> emeasure M {x\<in>space M. f x \<noteq> 0} + emeasure M {x\<in>space M. g x \<noteq> 0}"
    by (intro emeasure_subadditive) auto
  finally show "emeasure M {y \<in> space M. p (f y) (g y) \<noteq> 0} \<noteq> \<infinity>"
    using fin by auto
qed

lemma simple_function_finite_support:
  assumes f: "simple_function M f" and fin: "(\<integral>\<^sup>+x. f x \<partial>M) < \<infinity>" and nn: "\<And>x. 0 \<le> f x"
  shows "emeasure M {x\<in>space M. f x \<noteq> 0} \<noteq> \<infinity>"
proof cases
  from f have meas[measurable]: "f \<in> borel_measurable M"
    by (rule borel_measurable_simple_function)

  assume non_empty: "\<exists>x\<in>space M. f x \<noteq> 0"

  def m \<equiv> "Min (f`space M - {0})"
  have "m \<in> f`space M - {0}"
    unfolding m_def using f non_empty by (intro Min_in) (auto simp: simple_function_def)
  then have m: "0 < m"
    using nn by (auto simp: less_le)

  from m have "m * emeasure M {x\<in>space M. 0 \<noteq> f x} = 
    (\<integral>\<^sup>+x. m * indicator {x\<in>space M. 0 \<noteq> f x} x \<partial>M)"
    using f by (intro positive_integral_cmult_indicator[symmetric]) auto
  also have "\<dots> \<le> (\<integral>\<^sup>+x. f x \<partial>M)"
    using AE_space
  proof (intro positive_integral_mono_AE, eventually_elim)
    fix x assume "x \<in> space M"
    with nn show "m * indicator {x \<in> space M. 0 \<noteq> f x} x \<le> f x"
      using f by (auto split: split_indicator simp: simple_function_def m_def)
  qed
  also note `\<dots> < \<infinity>`
  finally show ?thesis
    using m by auto 
next
  assume "\<not> (\<exists>x\<in>space M. f x \<noteq> 0)"
  with nn have *: "{x\<in>space M. f x \<noteq> 0} = {}"
    by auto
  show ?thesis unfolding * by simp
qed

lemma simple_bochner_integrableI_bounded:
  assumes f: "simple_function M f" and fin: "(\<integral>\<^sup>+x. norm (f x) \<partial>M) < \<infinity>"
  shows "simple_bochner_integrable M f"
proof
  have "emeasure M {y \<in> space M. ereal (norm (f y)) \<noteq> 0} \<noteq> \<infinity>"
  proof (rule simple_function_finite_support)
    show "simple_function M (\<lambda>x. ereal (norm (f x)))"
      using f by (rule simple_function_compose1)
    show "(\<integral>\<^sup>+ y. ereal (norm (f y)) \<partial>M) < \<infinity>" by fact
  qed simp
  then show "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>" by simp
qed fact

definition simple_bochner_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_vector) \<Rightarrow> 'b" where
  "simple_bochner_integral M f = (\<Sum>y\<in>f`space M. measure M {x\<in>space M. f x = y} *\<^sub>R y)"

lemma simple_bochner_integral_partition:
  assumes f: "simple_bochner_integrable M f" and g: "simple_function M g"
  assumes sub: "\<And>x y. x \<in> space M \<Longrightarrow> y \<in> space M \<Longrightarrow> g x = g y \<Longrightarrow> f x = f y"
  assumes v: "\<And>x. x \<in> space M \<Longrightarrow> f x = v (g x)"
  shows "simple_bochner_integral M f = (\<Sum>y\<in>g ` space M. measure M {x\<in>space M. g x = y} *\<^sub>R v y)"
    (is "_ = ?r")
proof -
  from f g have [simp]: "finite (f`space M)" "finite (g`space M)"
    by (auto simp: simple_function_def elim: simple_bochner_integrable.cases)

  from f have [measurable]: "f \<in> measurable M (count_space UNIV)"
    by (auto intro: measurable_simple_function elim: simple_bochner_integrable.cases)

  from g have [measurable]: "g \<in> measurable M (count_space UNIV)"
    by (auto intro: measurable_simple_function elim: simple_bochner_integrable.cases)

  { fix y assume "y \<in> space M"
    then have "f ` space M \<inter> {i. \<exists>x\<in>space M. i = f x \<and> g y = g x} = {v (g y)}"
      by (auto cong: sub simp: v[symmetric]) }
  note eq = this

  have "simple_bochner_integral M f =
    (\<Sum>y\<in>f`space M. (\<Sum>z\<in>g`space M. 
      if \<exists>x\<in>space M. y = f x \<and> z = g x then measure M {x\<in>space M. g x = z} else 0) *\<^sub>R y)"
    unfolding simple_bochner_integral_def
  proof (safe intro!: setsum_cong scaleR_cong_right)
    fix y assume y: "y \<in> space M" "f y \<noteq> 0"
    have [simp]: "g ` space M \<inter> {z. \<exists>x\<in>space M. f y = f x \<and> z = g x} = 
        {z. \<exists>x\<in>space M. f y = f x \<and> z = g x}"
      by auto
    have eq:"{x \<in> space M. f x = f y} =
        (\<Union>i\<in>{z. \<exists>x\<in>space M. f y = f x \<and> z = g x}. {x \<in> space M. g x = i})"
      by (auto simp: eq_commute cong: sub rev_conj_cong)
    have "finite (g`space M)" by simp
    then have "finite {z. \<exists>x\<in>space M. f y = f x \<and> z = g x}"
      by (rule rev_finite_subset) auto
    moreover
    { fix x assume "x \<in> space M" "f x = f y"
      then have "x \<in> space M" "f x \<noteq> 0"
        using y by auto
      then have "emeasure M {y \<in> space M. g y = g x} \<le> emeasure M {y \<in> space M. f y \<noteq> 0}"
        by (auto intro!: emeasure_mono cong: sub)
      then have "emeasure M {xa \<in> space M. g xa = g x} < \<infinity>"
        using f by (auto simp: simple_bochner_integrable.simps) }
    ultimately
    show "measure M {x \<in> space M. f x = f y} =
      (\<Sum>z\<in>g ` space M. if \<exists>x\<in>space M. f y = f x \<and> z = g x then measure M {x \<in> space M. g x = z} else 0)"
      apply (simp add: setsum_cases eq)
      apply (subst measure_finite_Union[symmetric])
      apply (auto simp: disjoint_family_on_def)
      done
  qed
  also have "\<dots> = (\<Sum>y\<in>f`space M. (\<Sum>z\<in>g`space M. 
      if \<exists>x\<in>space M. y = f x \<and> z = g x then measure M {x\<in>space M. g x = z} *\<^sub>R y else 0))"
    by (auto intro!: setsum_cong simp: scaleR_setsum_left)
  also have "\<dots> = ?r"
    by (subst setsum_commute)
       (auto intro!: setsum_cong simp: setsum_cases scaleR_setsum_right[symmetric] eq)
  finally show "simple_bochner_integral M f = ?r" .
qed

lemma simple_bochner_integral_add:
  assumes f: "simple_bochner_integrable M f" and g: "simple_bochner_integrable M g"
  shows "simple_bochner_integral M (\<lambda>x. f x + g x) =
    simple_bochner_integral M f + simple_bochner_integral M g"
proof -
  from f g have "simple_bochner_integral M (\<lambda>x. f x + g x) =
    (\<Sum>y\<in>(\<lambda>x. (f x, g x)) ` space M. measure M {x \<in> space M. (f x, g x) = y} *\<^sub>R (fst y + snd y))"
    by (intro simple_bochner_integral_partition)
       (auto simp: simple_bochner_integrable_compose2 elim: simple_bochner_integrable.cases)
  moreover from f g have "simple_bochner_integral M f =
    (\<Sum>y\<in>(\<lambda>x. (f x, g x)) ` space M. measure M {x \<in> space M. (f x, g x) = y} *\<^sub>R fst y)"
    by (intro simple_bochner_integral_partition)
       (auto simp: simple_bochner_integrable_compose2 elim: simple_bochner_integrable.cases)
  moreover from f g have "simple_bochner_integral M g =
    (\<Sum>y\<in>(\<lambda>x. (f x, g x)) ` space M. measure M {x \<in> space M. (f x, g x) = y} *\<^sub>R snd y)"
    by (intro simple_bochner_integral_partition)
       (auto simp: simple_bochner_integrable_compose2 elim: simple_bochner_integrable.cases)
  ultimately show ?thesis
    by (simp add: setsum_addf[symmetric] scaleR_add_right)
qed

lemma (in linear) simple_bochner_integral_linear:
  assumes g: "simple_bochner_integrable M g"
  shows "simple_bochner_integral M (\<lambda>x. f (g x)) = f (simple_bochner_integral M g)"
proof -
  from g have "simple_bochner_integral M (\<lambda>x. f (g x)) =
    (\<Sum>y\<in>g ` space M. measure M {x \<in> space M. g x = y} *\<^sub>R f y)"
    by (intro simple_bochner_integral_partition)
       (auto simp: simple_bochner_integrable_compose2[where p="\<lambda>x y. f x"] zero
             elim: simple_bochner_integrable.cases)
  also have "\<dots> = f (simple_bochner_integral M g)"
    by (simp add: simple_bochner_integral_def setsum scaleR)
  finally show ?thesis .
qed

lemma simple_bochner_integral_minus:
  assumes f: "simple_bochner_integrable M f"
  shows "simple_bochner_integral M (\<lambda>x. - f x) = - simple_bochner_integral M f"
proof -
  interpret linear uminus by unfold_locales auto
  from f show ?thesis
    by (rule simple_bochner_integral_linear)
qed

lemma simple_bochner_integral_diff:
  assumes f: "simple_bochner_integrable M f" and g: "simple_bochner_integrable M g"
  shows "simple_bochner_integral M (\<lambda>x. f x - g x) =
    simple_bochner_integral M f - simple_bochner_integral M g"
  unfolding diff_conv_add_uminus using f g
  by (subst simple_bochner_integral_add)
     (auto simp: simple_bochner_integral_minus simple_bochner_integrable_compose2[where p="\<lambda>x y. - y"])

lemma simple_bochner_integral_norm_bound:
  assumes f: "simple_bochner_integrable M f"
  shows "norm (simple_bochner_integral M f) \<le> simple_bochner_integral M (\<lambda>x. norm (f x))"
proof -
  have "norm (simple_bochner_integral M f) \<le> 
    (\<Sum>y\<in>f ` space M. norm (measure M {x \<in> space M. f x = y} *\<^sub>R y))"
    unfolding simple_bochner_integral_def by (rule norm_setsum)
  also have "\<dots> = (\<Sum>y\<in>f ` space M. measure M {x \<in> space M. f x = y} *\<^sub>R norm y)"
    by (simp add: measure_nonneg)
  also have "\<dots> = simple_bochner_integral M (\<lambda>x. norm (f x))"
    using f
    by (intro simple_bochner_integral_partition[symmetric])
       (auto intro: f simple_bochner_integrable_compose2 elim: simple_bochner_integrable.cases)
  finally show ?thesis .
qed

lemma simple_bochner_integral_eq_positive_integral:
  assumes f: "simple_bochner_integrable M f" "\<And>x. 0 \<le> f x"
  shows "simple_bochner_integral M f = (\<integral>\<^sup>+x. f x \<partial>M)"
proof -
  { fix x y z have "(x \<noteq> 0 \<Longrightarrow> y = z) \<Longrightarrow> ereal x * y = ereal x * z"
      by (cases "x = 0") (auto simp: zero_ereal_def[symmetric]) }
  note ereal_cong_mult = this

  have [measurable]: "f \<in> borel_measurable M"
    using f(1) by (auto intro: borel_measurable_simple_function elim: simple_bochner_integrable.cases)

  { fix y assume y: "y \<in> space M" "f y \<noteq> 0"
    have "ereal (measure M {x \<in> space M. f x = f y}) = emeasure M {x \<in> space M. f x = f y}"
    proof (rule emeasure_eq_ereal_measure[symmetric])
      have "emeasure M {x \<in> space M. f x = f y} \<le> emeasure M {x \<in> space M. f x \<noteq> 0}"
        using y by (intro emeasure_mono) auto
      with f show "emeasure M {x \<in> space M. f x = f y} \<noteq> \<infinity>"
        by (auto simp: simple_bochner_integrable.simps)
    qed
    moreover have "{x \<in> space M. f x = f y} = (\<lambda>x. ereal (f x)) -` {ereal (f y)} \<inter> space M"
      by auto
    ultimately have "ereal (measure M {x \<in> space M. f x = f y}) =
          emeasure M ((\<lambda>x. ereal (f x)) -` {ereal (f y)} \<inter> space M)" by simp }
  with f have "simple_bochner_integral M f = (\<integral>\<^sup>Sx. f x \<partial>M)"
    unfolding simple_integral_def
    by (subst simple_bochner_integral_partition[OF f(1), where g="\<lambda>x. ereal (f x)" and v=real])
       (auto intro: f simple_function_compose1 elim: simple_bochner_integrable.cases
             intro!: setsum_cong ereal_cong_mult
             simp: setsum_ereal[symmetric] times_ereal.simps(1)[symmetric] mult_ac
             simp del: setsum_ereal times_ereal.simps(1))
  also have "\<dots> = (\<integral>\<^sup>+x. f x \<partial>M)"
    using f
    by (intro positive_integral_eq_simple_integral[symmetric])
       (auto simp: simple_function_compose1 simple_bochner_integrable.simps)
  finally show ?thesis .
qed

lemma simple_bochner_integral_bounded:
  fixes f :: "'a \<Rightarrow> 'b::{real_normed_vector, second_countable_topology}"
  assumes f[measurable]: "f \<in> borel_measurable M"
  assumes s: "simple_bochner_integrable M s" and t: "simple_bochner_integrable M t"
  shows "ereal (norm (simple_bochner_integral M s - simple_bochner_integral M t)) \<le>
    (\<integral>\<^sup>+ x. norm (f x - s x) \<partial>M) + (\<integral>\<^sup>+ x. norm (f x - t x) \<partial>M)"
    (is "ereal (norm (?s - ?t)) \<le> ?S + ?T")
proof -
  have [measurable]: "s \<in> borel_measurable M" "t \<in> borel_measurable M"
    using s t by (auto intro: borel_measurable_simple_function elim: simple_bochner_integrable.cases)

  have "ereal (norm (?s - ?t)) = norm (simple_bochner_integral M (\<lambda>x. s x - t x))"
    using s t by (subst simple_bochner_integral_diff) auto
  also have "\<dots> \<le> simple_bochner_integral M (\<lambda>x. norm (s x - t x))"
    using simple_bochner_integrable_compose2[of "op -" M "s" "t"] s t
    by (auto intro!: simple_bochner_integral_norm_bound)
  also have "\<dots> = (\<integral>\<^sup>+x. norm (s x - t x) \<partial>M)"
    using simple_bochner_integrable_compose2[of "\<lambda>x y. norm (x - y)" M "s" "t"] s t
    by (auto intro!: simple_bochner_integral_eq_positive_integral)
  also have "\<dots> \<le> (\<integral>\<^sup>+x. ereal (norm (f x - s x)) + ereal (norm (f x - t x)) \<partial>M)"
    by (auto intro!: positive_integral_mono)
       (metis (erased, hide_lams) add_diff_cancel_left add_diff_eq diff_add_eq order_trans
              norm_minus_commute norm_triangle_ineq4 order_refl)
  also have "\<dots> = ?S + ?T"
   by (rule positive_integral_add) auto
  finally show ?thesis .
qed

inductive has_bochner_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b::{real_normed_vector, second_countable_topology} \<Rightarrow> bool"
  for M f x where
  "f \<in> borel_measurable M \<Longrightarrow>
    (\<And>i. simple_bochner_integrable M (s i)) \<Longrightarrow>
    (\<lambda>i. \<integral>\<^sup>+x. norm (f x - s i x) \<partial>M) ----> 0 \<Longrightarrow>
    (\<lambda>i. simple_bochner_integral M (s i)) ----> x \<Longrightarrow>
    has_bochner_integral M f x"

lemma has_bochner_integral_cong:
  assumes "M = N" "\<And>x. x \<in> space N \<Longrightarrow> f x = g x" "x = y"
  shows "has_bochner_integral M f x \<longleftrightarrow> has_bochner_integral N g y"
  unfolding has_bochner_integral.simps assms(1,3)
  using assms(2) by (simp cong: measurable_cong_strong positive_integral_cong_strong)

lemma has_bochner_integral_cong_AE:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (AE x in M. f x = g x) \<Longrightarrow>
    has_bochner_integral M f x \<longleftrightarrow> has_bochner_integral M g x"
  unfolding has_bochner_integral.simps
  by (intro arg_cong[where f=Ex] ext conj_cong rev_conj_cong refl arg_cong[where f="\<lambda>x. x ----> 0"]
            positive_integral_cong_AE)
     auto

lemma borel_measurable_has_bochner_integral[measurable_dest]:
  "has_bochner_integral M f x \<Longrightarrow> f \<in> borel_measurable M"
  by (auto elim: has_bochner_integral.cases)

lemma has_bochner_integral_simple_bochner_integrable:
  "simple_bochner_integrable M f \<Longrightarrow> has_bochner_integral M f (simple_bochner_integral M f)"
  by (rule has_bochner_integral.intros[where s="\<lambda>_. f"])
     (auto intro: borel_measurable_simple_function 
           elim: simple_bochner_integrable.cases
           simp: zero_ereal_def[symmetric])

lemma has_bochner_integral_real_indicator:
  assumes [measurable]: "A \<in> sets M" and A: "emeasure M A < \<infinity>"
  shows "has_bochner_integral M (indicator A) (measure M A)"
proof -
  have sbi: "simple_bochner_integrable M (indicator A::'a \<Rightarrow> real)"
  proof
    have "{y \<in> space M. (indicator A y::real) \<noteq> 0} = A"
      using sets.sets_into_space[OF `A\<in>sets M`] by (auto split: split_indicator)
    then show "emeasure M {y \<in> space M. (indicator A y::real) \<noteq> 0} \<noteq> \<infinity>"
      using A by auto
  qed (rule simple_function_indicator assms)+
  moreover have "simple_bochner_integral M (indicator A) = measure M A"
    using simple_bochner_integral_eq_positive_integral[OF sbi] A
    by (simp add: ereal_indicator emeasure_eq_ereal_measure)
  ultimately show ?thesis
    by (metis has_bochner_integral_simple_bochner_integrable)
qed

lemma has_bochner_integral_add:
  "has_bochner_integral M f x \<Longrightarrow> has_bochner_integral M g y \<Longrightarrow>
    has_bochner_integral M (\<lambda>x. f x + g x) (x + y)"
proof (safe intro!: has_bochner_integral.intros elim!: has_bochner_integral.cases)
  fix sf sg
  assume f_sf: "(\<lambda>i. \<integral>\<^sup>+ x. norm (f x - sf i x) \<partial>M) ----> 0"
  assume g_sg: "(\<lambda>i. \<integral>\<^sup>+ x. norm (g x - sg i x) \<partial>M) ----> 0"

  assume sf: "\<forall>i. simple_bochner_integrable M (sf i)"
    and sg: "\<forall>i. simple_bochner_integrable M (sg i)"
  then have [measurable]: "\<And>i. sf i \<in> borel_measurable M" "\<And>i. sg i \<in> borel_measurable M"
    by (auto intro: borel_measurable_simple_function elim: simple_bochner_integrable.cases)
  assume [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"

  show "\<And>i. simple_bochner_integrable M (\<lambda>x. sf i x + sg i x)"
    using sf sg by (simp add: simple_bochner_integrable_compose2)

  show "(\<lambda>i. \<integral>\<^sup>+ x. (norm (f x + g x - (sf i x + sg i x))) \<partial>M) ----> 0"
    (is "?f ----> 0")
  proof (rule tendsto_sandwich)
    show "eventually (\<lambda>n. 0 \<le> ?f n) sequentially" "(\<lambda>_. 0) ----> 0"
      by (auto simp: positive_integral_positive)
    show "eventually (\<lambda>i. ?f i \<le> (\<integral>\<^sup>+ x. (norm (f x - sf i x)) \<partial>M) + \<integral>\<^sup>+ x. (norm (g x - sg i x)) \<partial>M) sequentially"
      (is "eventually (\<lambda>i. ?f i \<le> ?g i) sequentially")
    proof (intro always_eventually allI)
      fix i have "?f i \<le> (\<integral>\<^sup>+ x. (norm (f x - sf i x)) + ereal (norm (g x - sg i x)) \<partial>M)"
        by (auto intro!: positive_integral_mono norm_diff_triangle_ineq)
      also have "\<dots> = ?g i"
        by (intro positive_integral_add) auto
      finally show "?f i \<le> ?g i" .
    qed
    show "?g ----> 0"
      using tendsto_add_ereal[OF _ _ f_sf g_sg] by simp
  qed
qed (auto simp: simple_bochner_integral_add tendsto_add)

lemma has_bochner_integral_bounded_linear:
  assumes "bounded_linear T"
  shows "has_bochner_integral M f x \<Longrightarrow> has_bochner_integral M (\<lambda>x. T (f x)) (T x)"
proof (safe intro!: has_bochner_integral.intros elim!: has_bochner_integral.cases)
  interpret T: bounded_linear T by fact
  have [measurable]: "T \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_on1 T.continuous_on continuous_on_id)
  assume [measurable]: "f \<in> borel_measurable M"
  then show "(\<lambda>x. T (f x)) \<in> borel_measurable M"
    by auto

  fix s assume f_s: "(\<lambda>i. \<integral>\<^sup>+ x. norm (f x - s i x) \<partial>M) ----> 0"
  assume s: "\<forall>i. simple_bochner_integrable M (s i)"
  then show "\<And>i. simple_bochner_integrable M (\<lambda>x. T (s i x))"
    by (auto intro: simple_bochner_integrable_compose2 T.zero)

  have [measurable]: "\<And>i. s i \<in> borel_measurable M"
    using s by (auto intro: borel_measurable_simple_function elim: simple_bochner_integrable.cases)

  obtain K where K: "K > 0" "\<And>x i. norm (T (f x) - T (s i x)) \<le> norm (f x - s i x) * K"
    using T.pos_bounded by (auto simp: T.diff[symmetric])

  show "(\<lambda>i. \<integral>\<^sup>+ x. norm (T (f x) - T (s i x)) \<partial>M) ----> 0"
    (is "?f ----> 0")
  proof (rule tendsto_sandwich)
    show "eventually (\<lambda>n. 0 \<le> ?f n) sequentially" "(\<lambda>_. 0) ----> 0"
      by (auto simp: positive_integral_positive)

    show "eventually (\<lambda>i. ?f i \<le> K * (\<integral>\<^sup>+ x. norm (f x - s i x) \<partial>M)) sequentially"
      (is "eventually (\<lambda>i. ?f i \<le> ?g i) sequentially")
    proof (intro always_eventually allI)
      fix i have "?f i \<le> (\<integral>\<^sup>+ x. ereal K * norm (f x - s i x) \<partial>M)"
        using K by (intro positive_integral_mono) (auto simp: mult_ac)
      also have "\<dots> = ?g i"
        using K by (intro positive_integral_cmult) auto
      finally show "?f i \<le> ?g i" .
    qed
    show "?g ----> 0"
      using ereal_lim_mult[OF f_s, of "ereal K"] by simp
  qed

  assume "(\<lambda>i. simple_bochner_integral M (s i)) ----> x"
  with s show "(\<lambda>i. simple_bochner_integral M (\<lambda>x. T (s i x))) ----> T x"
    by (auto intro!: T.tendsto simp: T.simple_bochner_integral_linear)
qed

lemma has_bochner_integral_zero[intro]: "has_bochner_integral M (\<lambda>x. 0) 0"
  by (auto intro!: has_bochner_integral.intros[where s="\<lambda>_ _. 0"]
           simp: zero_ereal_def[symmetric] simple_bochner_integrable.simps
                 simple_bochner_integral_def image_constant_conv)

lemma has_bochner_integral_scaleR_left[intro]:
  "(c \<noteq> 0 \<Longrightarrow> has_bochner_integral M f x) \<Longrightarrow> has_bochner_integral M (\<lambda>x. f x *\<^sub>R c) (x *\<^sub>R c)"
  by (cases "c = 0") (auto simp add: has_bochner_integral_bounded_linear[OF bounded_linear_scaleR_left])

lemma has_bochner_integral_scaleR_right[intro]:
  "(c \<noteq> 0 \<Longrightarrow> has_bochner_integral M f x) \<Longrightarrow> has_bochner_integral M (\<lambda>x. c *\<^sub>R f x) (c *\<^sub>R x)"
  by (cases "c = 0") (auto simp add: has_bochner_integral_bounded_linear[OF bounded_linear_scaleR_right])

lemma has_bochner_integral_mult_left[intro]:
  fixes c :: "_::{real_normed_algebra,second_countable_topology}"
  shows "(c \<noteq> 0 \<Longrightarrow> has_bochner_integral M f x) \<Longrightarrow> has_bochner_integral M (\<lambda>x. f x * c) (x * c)"
  by (cases "c = 0") (auto simp add: has_bochner_integral_bounded_linear[OF bounded_linear_mult_left])

lemma has_bochner_integral_mult_right[intro]:
  fixes c :: "_::{real_normed_algebra,second_countable_topology}"
  shows "(c \<noteq> 0 \<Longrightarrow> has_bochner_integral M f x) \<Longrightarrow> has_bochner_integral M (\<lambda>x. c * f x) (c * x)"
  by (cases "c = 0") (auto simp add: has_bochner_integral_bounded_linear[OF bounded_linear_mult_right])

lemmas has_bochner_integral_divide = 
  has_bochner_integral_bounded_linear[OF bounded_linear_divide]

lemma has_bochner_integral_divide_zero[intro]:
  fixes c :: "_::{real_normed_field, field_inverse_zero, second_countable_topology}"
  shows "(c \<noteq> 0 \<Longrightarrow> has_bochner_integral M f x) \<Longrightarrow> has_bochner_integral M (\<lambda>x. f x / c) (x / c)"
  using has_bochner_integral_divide by (cases "c = 0") auto

lemma has_bochner_integral_inner_left[intro]:
  "(c \<noteq> 0 \<Longrightarrow> has_bochner_integral M f x) \<Longrightarrow> has_bochner_integral M (\<lambda>x. f x \<bullet> c) (x \<bullet> c)"
  by (cases "c = 0") (auto simp add: has_bochner_integral_bounded_linear[OF bounded_linear_inner_left])

lemma has_bochner_integral_inner_right[intro]:
  "(c \<noteq> 0 \<Longrightarrow> has_bochner_integral M f x) \<Longrightarrow> has_bochner_integral M (\<lambda>x. c \<bullet> f x) (c \<bullet> x)"
  by (cases "c = 0") (auto simp add: has_bochner_integral_bounded_linear[OF bounded_linear_inner_right])

lemmas has_bochner_integral_minus =
  has_bochner_integral_bounded_linear[OF bounded_linear_minus[OF bounded_linear_ident]]
lemmas has_bochner_integral_Re =
  has_bochner_integral_bounded_linear[OF bounded_linear_Re]
lemmas has_bochner_integral_Im =
  has_bochner_integral_bounded_linear[OF bounded_linear_Im]
lemmas has_bochner_integral_cnj =
  has_bochner_integral_bounded_linear[OF bounded_linear_cnj]
lemmas has_bochner_integral_of_real =
  has_bochner_integral_bounded_linear[OF bounded_linear_of_real]
lemmas has_bochner_integral_fst =
  has_bochner_integral_bounded_linear[OF bounded_linear_fst]
lemmas has_bochner_integral_snd =
  has_bochner_integral_bounded_linear[OF bounded_linear_snd]

lemma has_bochner_integral_indicator:
  "A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow>
    has_bochner_integral M (\<lambda>x. indicator A x *\<^sub>R c) (measure M A *\<^sub>R c)"
  by (intro has_bochner_integral_scaleR_left has_bochner_integral_real_indicator)

lemma has_bochner_integral_diff:
  "has_bochner_integral M f x \<Longrightarrow> has_bochner_integral M g y \<Longrightarrow>
    has_bochner_integral M (\<lambda>x. f x - g x) (x - y)"
  unfolding diff_conv_add_uminus
  by (intro has_bochner_integral_add has_bochner_integral_minus)

lemma has_bochner_integral_setsum:
  "(\<And>i. i \<in> I \<Longrightarrow> has_bochner_integral M (f i) (x i)) \<Longrightarrow>
    has_bochner_integral M (\<lambda>x. \<Sum>i\<in>I. f i x) (\<Sum>i\<in>I. x i)"
  by (induct I rule: infinite_finite_induct)
     (auto intro: has_bochner_integral_zero has_bochner_integral_add)

lemma has_bochner_integral_implies_finite_norm:
  "has_bochner_integral M f x \<Longrightarrow> (\<integral>\<^sup>+x. norm (f x) \<partial>M) < \<infinity>"
proof (elim has_bochner_integral.cases)
  fix s v
  assume [measurable]: "f \<in> borel_measurable M" and s: "\<And>i. simple_bochner_integrable M (s i)" and
    lim_0: "(\<lambda>i. \<integral>\<^sup>+ x. ereal (norm (f x - s i x)) \<partial>M) ----> 0"
  from order_tendstoD[OF lim_0, of "\<infinity>"]
  obtain i where f_s_fin: "(\<integral>\<^sup>+ x. ereal (norm (f x - s i x)) \<partial>M) < \<infinity>"
    by (metis (mono_tags, lifting) eventually_False_sequentially eventually_elim1
              less_ereal.simps(4) zero_ereal_def)

  have [measurable]: "\<And>i. s i \<in> borel_measurable M"
    using s by (auto intro: borel_measurable_simple_function elim: simple_bochner_integrable.cases)

  def m \<equiv> "if space M = {} then 0 else Max ((\<lambda>x. norm (s i x))`space M)"
  have "finite (s i ` space M)"
    using s by (auto simp: simple_function_def simple_bochner_integrable.simps)
  then have "finite (norm ` s i ` space M)"
    by (rule finite_imageI)
  then have "\<And>x. x \<in> space M \<Longrightarrow> norm (s i x) \<le> m" "0 \<le> m"
    by (auto simp: m_def image_comp comp_def Max_ge_iff)
  then have "(\<integral>\<^sup>+x. norm (s i x) \<partial>M) \<le> (\<integral>\<^sup>+x. ereal m * indicator {x\<in>space M. s i x \<noteq> 0} x \<partial>M)"
    by (auto split: split_indicator intro!: Max_ge positive_integral_mono simp:)
  also have "\<dots> < \<infinity>"
    using s by (subst positive_integral_cmult_indicator) (auto simp: `0 \<le> m` simple_bochner_integrable.simps)
  finally have s_fin: "(\<integral>\<^sup>+x. norm (s i x) \<partial>M) < \<infinity>" .

  have "(\<integral>\<^sup>+ x. norm (f x) \<partial>M) \<le> (\<integral>\<^sup>+ x. ereal (norm (f x - s i x)) + ereal (norm (s i x)) \<partial>M)"
    by (auto intro!: positive_integral_mono) (metis add_commute norm_triangle_sub)
  also have "\<dots> = (\<integral>\<^sup>+x. norm (f x - s i x) \<partial>M) + (\<integral>\<^sup>+x. norm (s i x) \<partial>M)"
    by (rule positive_integral_add) auto
  also have "\<dots> < \<infinity>"
    using s_fin f_s_fin by auto
  finally show "(\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M) < \<infinity>" .
qed

lemma has_bochner_integral_norm_bound:
  assumes i: "has_bochner_integral M f x"
  shows "norm x \<le> (\<integral>\<^sup>+x. norm (f x) \<partial>M)"
using assms proof
  fix s assume
    x: "(\<lambda>i. simple_bochner_integral M (s i)) ----> x" (is "?s ----> x") and
    s[simp]: "\<And>i. simple_bochner_integrable M (s i)" and
    lim: "(\<lambda>i. \<integral>\<^sup>+ x. ereal (norm (f x - s i x)) \<partial>M) ----> 0" and
    f[measurable]: "f \<in> borel_measurable M"

  have [measurable]: "\<And>i. s i \<in> borel_measurable M"
    using s by (auto simp: simple_bochner_integrable.simps intro: borel_measurable_simple_function)

  show "norm x \<le> (\<integral>\<^sup>+x. norm (f x) \<partial>M)"
  proof (rule LIMSEQ_le)
    show "(\<lambda>i. ereal (norm (?s i))) ----> norm x"
      using x by (intro tendsto_intros lim_ereal[THEN iffD2])
    show "\<exists>N. \<forall>n\<ge>N. norm (?s n) \<le> (\<integral>\<^sup>+x. norm (f x - s n x) \<partial>M) + (\<integral>\<^sup>+x. norm (f x) \<partial>M)"
      (is "\<exists>N. \<forall>n\<ge>N. _ \<le> ?t n")
    proof (intro exI allI impI)
      fix n
      have "ereal (norm (?s n)) \<le> simple_bochner_integral M (\<lambda>x. norm (s n x))"
        by (auto intro!: simple_bochner_integral_norm_bound)
      also have "\<dots> = (\<integral>\<^sup>+x. norm (s n x) \<partial>M)"
        by (intro simple_bochner_integral_eq_positive_integral)
           (auto intro: s simple_bochner_integrable_compose2)
      also have "\<dots> \<le> (\<integral>\<^sup>+x. ereal (norm (f x - s n x)) + norm (f x) \<partial>M)"
        by (auto intro!: positive_integral_mono)
           (metis add_commute norm_minus_commute norm_triangle_sub)
      also have "\<dots> = ?t n" 
        by (rule positive_integral_add) auto
      finally show "norm (?s n) \<le> ?t n" .
    qed
    have "?t ----> 0 + (\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M)"
      using has_bochner_integral_implies_finite_norm[OF i]
      by (intro tendsto_add_ereal tendsto_const lim) auto
    then show "?t ----> \<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M"
      by simp
  qed
qed

lemma has_bochner_integral_eq:
  "has_bochner_integral M f x \<Longrightarrow> has_bochner_integral M f y \<Longrightarrow> x = y"
proof (elim has_bochner_integral.cases)
  assume f[measurable]: "f \<in> borel_measurable M"

  fix s t
  assume "(\<lambda>i. \<integral>\<^sup>+ x. norm (f x - s i x) \<partial>M) ----> 0" (is "?S ----> 0")
  assume "(\<lambda>i. \<integral>\<^sup>+ x. norm (f x - t i x) \<partial>M) ----> 0" (is "?T ----> 0")
  assume s: "\<And>i. simple_bochner_integrable M (s i)"
  assume t: "\<And>i. simple_bochner_integrable M (t i)"

  have [measurable]: "\<And>i. s i \<in> borel_measurable M" "\<And>i. t i \<in> borel_measurable M"
    using s t by (auto intro: borel_measurable_simple_function elim: simple_bochner_integrable.cases)

  let ?s = "\<lambda>i. simple_bochner_integral M (s i)"
  let ?t = "\<lambda>i. simple_bochner_integral M (t i)"
  assume "?s ----> x" "?t ----> y"
  then have "(\<lambda>i. norm (?s i - ?t i)) ----> norm (x - y)"
    by (intro tendsto_intros)
  moreover
  have "(\<lambda>i. ereal (norm (?s i - ?t i))) ----> ereal 0"
  proof (rule tendsto_sandwich)
    show "eventually (\<lambda>i. 0 \<le> ereal (norm (?s i - ?t i))) sequentially" "(\<lambda>_. 0) ----> ereal 0"
      by (auto simp: positive_integral_positive zero_ereal_def[symmetric])

    show "eventually (\<lambda>i. norm (?s i - ?t i) \<le> ?S i + ?T i) sequentially"
      by (intro always_eventually allI simple_bochner_integral_bounded s t f)
    show "(\<lambda>i. ?S i + ?T i) ----> ereal 0"
      using tendsto_add_ereal[OF _ _ `?S ----> 0` `?T ----> 0`]
      by (simp add: zero_ereal_def[symmetric])
  qed
  then have "(\<lambda>i. norm (?s i - ?t i)) ----> 0"
    by simp
  ultimately have "norm (x - y) = 0"
    by (rule LIMSEQ_unique)
  then show "x = y" by simp
qed

lemma has_bochner_integralI_AE:
  assumes f: "has_bochner_integral M f x"
    and g: "g \<in> borel_measurable M"
    and ae: "AE x in M. f x = g x"
  shows "has_bochner_integral M g x"
  using f
proof (safe intro!: has_bochner_integral.intros elim!: has_bochner_integral.cases)
  fix s assume "(\<lambda>i. \<integral>\<^sup>+ x. ereal (norm (f x - s i x)) \<partial>M) ----> 0"
  also have "(\<lambda>i. \<integral>\<^sup>+ x. ereal (norm (f x - s i x)) \<partial>M) = (\<lambda>i. \<integral>\<^sup>+ x. ereal (norm (g x - s i x)) \<partial>M)"
    using ae
    by (intro ext positive_integral_cong_AE, eventually_elim) simp
  finally show "(\<lambda>i. \<integral>\<^sup>+ x. ereal (norm (g x - s i x)) \<partial>M) ----> 0" .
qed (auto intro: g)

lemma has_bochner_integral_eq_AE:
  assumes f: "has_bochner_integral M f x"
    and g: "has_bochner_integral M g y"
    and ae: "AE x in M. f x = g x"
  shows "x = y"
proof -
  from assms have "has_bochner_integral M g x"
    by (auto intro: has_bochner_integralI_AE)
  from this g show "x = y"
    by (rule has_bochner_integral_eq)
qed

inductive integrable for M f where
  "has_bochner_integral M f x \<Longrightarrow> integrable M f"

definition lebesgue_integral ("integral\<^sup>L") where
  "integral\<^sup>L M f = (THE x. has_bochner_integral M f x)"

syntax
  "_lebesgue_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> 'a measure \<Rightarrow> real" ("\<integral> _. _ \<partial>_" [60,61] 110)

translations
  "\<integral> x. f \<partial>M" == "CONST lebesgue_integral M (\<lambda>x. f)"

lemma has_bochner_integral_integral_eq: "has_bochner_integral M f x \<Longrightarrow> integral\<^sup>L M f = x"
  by (metis the_equality has_bochner_integral_eq lebesgue_integral_def)

lemma has_bochner_integral_integrable:
  "integrable M f \<Longrightarrow> has_bochner_integral M f (integral\<^sup>L M f)"
  by (auto simp: has_bochner_integral_integral_eq integrable.simps)

lemma has_bochner_integral_iff:
  "has_bochner_integral M f x \<longleftrightarrow> integrable M f \<and> integral\<^sup>L M f = x"
  by (metis has_bochner_integral_integrable has_bochner_integral_integral_eq integrable.intros)

lemma simple_bochner_integrable_eq_integral:
  "simple_bochner_integrable M f \<Longrightarrow> simple_bochner_integral M f = integral\<^sup>L M f"
  using has_bochner_integral_simple_bochner_integrable[of M f]
  by (simp add: has_bochner_integral_integral_eq)

lemma not_integrable_integral_eq: "\<not> integrable M f \<Longrightarrow> integral\<^sup>L M f = (THE x. False)"
  unfolding integrable.simps lebesgue_integral_def by (auto intro!: arg_cong[where f=The])

lemma integral_eq_cases:
  "integrable M f \<longleftrightarrow> integrable N g \<Longrightarrow>
    (integrable M f \<Longrightarrow> integrable N g \<Longrightarrow> integral\<^sup>L M f = integral\<^sup>L N g) \<Longrightarrow>
    integral\<^sup>L M f = integral\<^sup>L N g"
  by (metis not_integrable_integral_eq)

lemma borel_measurable_integrable[measurable_dest]: "integrable M f \<Longrightarrow> f \<in> borel_measurable M"
  by (auto elim: integrable.cases has_bochner_integral.cases)

lemma integrable_cong:
  "M = N \<Longrightarrow> (\<And>x. x \<in> space N \<Longrightarrow> f x = g x) \<Longrightarrow> integrable M f \<longleftrightarrow> integrable N g"
  using assms by (simp cong: has_bochner_integral_cong add: integrable.simps)

lemma integrable_cong_AE:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> AE x in M. f x = g x \<Longrightarrow>
    integrable M f \<longleftrightarrow> integrable M g"
  unfolding integrable.simps
  by (intro has_bochner_integral_cong_AE arg_cong[where f=Ex] ext)

lemma integral_cong:
  "M = N \<Longrightarrow> (\<And>x. x \<in> space N \<Longrightarrow> f x = g x) \<Longrightarrow> integral\<^sup>L M f = integral\<^sup>L N g"
  using assms by (simp cong: has_bochner_integral_cong add: lebesgue_integral_def)

lemma integral_cong_AE:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> AE x in M. f x = g x \<Longrightarrow>
    integral\<^sup>L M f = integral\<^sup>L M g"
  unfolding lebesgue_integral_def
  by (intro has_bochner_integral_cong_AE arg_cong[where f=The] ext)

lemma integrable_add[simp, intro]: "integrable M f \<Longrightarrow> integrable M g \<Longrightarrow> integrable M (\<lambda>x. f x + g x)"
  by (auto simp: integrable.simps intro: has_bochner_integral_add)

lemma integrable_zero[simp, intro]: "integrable M (\<lambda>x. 0)"
  by (metis has_bochner_integral_zero integrable.simps) 

lemma integrable_setsum[simp, intro]: "(\<And>i. i \<in> I \<Longrightarrow> integrable M (f i)) \<Longrightarrow> integrable M (\<lambda>x. \<Sum>i\<in>I. f i x)"
  by (metis has_bochner_integral_setsum integrable.simps) 

lemma integrable_indicator[simp, intro]: "A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow>
  integrable M (\<lambda>x. indicator A x *\<^sub>R c)"
  by (metis has_bochner_integral_indicator integrable.simps) 

lemma integrable_real_indicator[simp, intro]: "A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow>
  integrable M (indicator A :: 'a \<Rightarrow> real)"
  by (metis has_bochner_integral_real_indicator integrable.simps)

lemma integrable_diff[simp, intro]: "integrable M f \<Longrightarrow> integrable M g \<Longrightarrow> integrable M (\<lambda>x. f x - g x)"
  by (auto simp: integrable.simps intro: has_bochner_integral_diff)
  
lemma integrable_bounded_linear: "bounded_linear T \<Longrightarrow> integrable M f \<Longrightarrow> integrable M (\<lambda>x. T (f x))"
  by (auto simp: integrable.simps intro: has_bochner_integral_bounded_linear)

lemma integrable_scaleR_left[simp, intro]: "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> integrable M (\<lambda>x. f x *\<^sub>R c)"
  unfolding integrable.simps by fastforce

lemma integrable_scaleR_right[simp, intro]: "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> integrable M (\<lambda>x. c *\<^sub>R f x)"
  unfolding integrable.simps by fastforce

lemma integrable_mult_left[simp, intro]:
  fixes c :: "_::{real_normed_algebra,second_countable_topology}"
  shows "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> integrable M (\<lambda>x. f x * c)"
  unfolding integrable.simps by fastforce

lemma integrable_mult_right[simp, intro]:
  fixes c :: "_::{real_normed_algebra,second_countable_topology}"
  shows "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> integrable M (\<lambda>x. c * f x)"
  unfolding integrable.simps by fastforce

lemma integrable_divide_zero[simp, intro]:
  fixes c :: "_::{real_normed_field, field_inverse_zero, second_countable_topology}"
  shows "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> integrable M (\<lambda>x. f x / c)"
  unfolding integrable.simps by fastforce

lemma integrable_inner_left[simp, intro]:
  "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> integrable M (\<lambda>x. f x \<bullet> c)"
  unfolding integrable.simps by fastforce

lemma integrable_inner_right[simp, intro]:
  "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> integrable M (\<lambda>x. c \<bullet> f x)"
  unfolding integrable.simps by fastforce

lemmas integrable_minus[simp, intro] =
  integrable_bounded_linear[OF bounded_linear_minus[OF bounded_linear_ident]]
lemmas integrable_divide[simp, intro] =
  integrable_bounded_linear[OF bounded_linear_divide]
lemmas integrable_Re[simp, intro] =
  integrable_bounded_linear[OF bounded_linear_Re]
lemmas integrable_Im[simp, intro] =
  integrable_bounded_linear[OF bounded_linear_Im]
lemmas integrable_cnj[simp, intro] =
  integrable_bounded_linear[OF bounded_linear_cnj]
lemmas integrable_of_real[simp, intro] =
  integrable_bounded_linear[OF bounded_linear_of_real]
lemmas integrable_fst[simp, intro] =
  integrable_bounded_linear[OF bounded_linear_fst]
lemmas integrable_snd[simp, intro] =
  integrable_bounded_linear[OF bounded_linear_snd]

lemma integral_zero[simp]: "integral\<^sup>L M (\<lambda>x. 0) = 0"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_zero)

lemma integral_add[simp]: "integrable M f \<Longrightarrow> integrable M g \<Longrightarrow>
    integral\<^sup>L M (\<lambda>x. f x + g x) = integral\<^sup>L M f + integral\<^sup>L M g"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_add has_bochner_integral_integrable)

lemma integral_diff[simp]: "integrable M f \<Longrightarrow> integrable M g \<Longrightarrow>
    integral\<^sup>L M (\<lambda>x. f x - g x) = integral\<^sup>L M f - integral\<^sup>L M g"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_diff has_bochner_integral_integrable)

lemma integral_setsum[simp]: "(\<And>i. i \<in> I \<Longrightarrow> integrable M (f i)) \<Longrightarrow>
  integral\<^sup>L M (\<lambda>x. \<Sum>i\<in>I. f i x) = (\<Sum>i\<in>I. integral\<^sup>L M (f i))"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_setsum has_bochner_integral_integrable)

lemma integral_bounded_linear: "bounded_linear T \<Longrightarrow> integrable M f \<Longrightarrow>
    integral\<^sup>L M (\<lambda>x. T (f x)) = T (integral\<^sup>L M f)"
  by (metis has_bochner_integral_bounded_linear has_bochner_integral_integrable has_bochner_integral_integral_eq)

lemma integral_indicator[simp]: "A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow>
  integral\<^sup>L M (\<lambda>x. indicator A x *\<^sub>R c) = measure M A *\<^sub>R c"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_indicator has_bochner_integral_integrable)

lemma integral_real_indicator[simp]: "A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow>
  integral\<^sup>L M (indicator A :: 'a \<Rightarrow> real) = measure M A"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_real_indicator has_bochner_integral_integrable)

lemma integral_scaleR_left[simp]: "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> (\<integral> x. f x *\<^sub>R c \<partial>M) = integral\<^sup>L M f *\<^sub>R c"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_integrable has_bochner_integral_scaleR_left)

lemma integral_scaleR_right[simp]: "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> (\<integral> x. c *\<^sub>R f x \<partial>M) = c *\<^sub>R integral\<^sup>L M f"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_integrable has_bochner_integral_scaleR_right)

lemma integral_mult_left[simp]:
  fixes c :: "_::{real_normed_algebra,second_countable_topology}"
  shows "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> (\<integral> x. f x * c \<partial>M) = integral\<^sup>L M f * c"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_integrable has_bochner_integral_mult_left)

lemma integral_mult_right[simp]:
  fixes c :: "_::{real_normed_algebra,second_countable_topology}"
  shows "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> (\<integral> x. c * f x \<partial>M) = c * integral\<^sup>L M f"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_integrable has_bochner_integral_mult_right)

lemma integral_inner_left[simp]: "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> (\<integral> x. f x \<bullet> c \<partial>M) = integral\<^sup>L M f \<bullet> c"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_integrable has_bochner_integral_inner_left)

lemma integral_inner_right[simp]: "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> (\<integral> x. c \<bullet> f x \<partial>M) = c \<bullet> integral\<^sup>L M f"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_integrable has_bochner_integral_inner_right)

lemma integral_divide_zero[simp]:
  fixes c :: "_::{real_normed_field, field_inverse_zero, second_countable_topology}"
  shows "(c \<noteq> 0 \<Longrightarrow> integrable M f) \<Longrightarrow> integral\<^sup>L M (\<lambda>x. f x / c) = integral\<^sup>L M f / c"
  by (intro has_bochner_integral_integral_eq has_bochner_integral_integrable has_bochner_integral_divide_zero)

lemmas integral_minus[simp] =
  integral_bounded_linear[OF bounded_linear_minus[OF bounded_linear_ident]]
lemmas integral_divide[simp] =
  integral_bounded_linear[OF bounded_linear_divide]
lemmas integral_Re[simp] =
  integral_bounded_linear[OF bounded_linear_Re]
lemmas integral_Im[simp] =
  integral_bounded_linear[OF bounded_linear_Im]
lemmas integral_cnj[simp] =
  integral_bounded_linear[OF bounded_linear_cnj]
lemmas integral_of_real[simp] =
  integral_bounded_linear[OF bounded_linear_of_real]
lemmas integral_fst[simp] =
  integral_bounded_linear[OF bounded_linear_fst]
lemmas integral_snd[simp] =
  integral_bounded_linear[OF bounded_linear_snd]

lemma integral_norm_bound_ereal:
  "integrable M f \<Longrightarrow> norm (integral\<^sup>L M f) \<le> (\<integral>\<^sup>+x. norm (f x) \<partial>M)"
  by (metis has_bochner_integral_integrable has_bochner_integral_norm_bound)

lemma integrableI_sequence:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f[measurable]: "f \<in> borel_measurable M"
  assumes s: "\<And>i. simple_bochner_integrable M (s i)"
  assumes lim: "(\<lambda>i. \<integral>\<^sup>+x. norm (f x - s i x) \<partial>M) ----> 0" (is "?S ----> 0")
  shows "integrable M f"
proof -
  let ?s = "\<lambda>n. simple_bochner_integral M (s n)"

  have "\<exists>x. ?s ----> x"
    unfolding convergent_eq_cauchy
  proof (rule metric_CauchyI)
    fix e :: real assume "0 < e"
    then have "0 < ereal (e / 2)" by auto
    from order_tendstoD(2)[OF lim this]
    obtain M where M: "\<And>n. M \<le> n \<Longrightarrow> ?S n < e / 2"
      by (auto simp: eventually_sequentially)
    show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (?s m) (?s n) < e"
    proof (intro exI allI impI)
      fix m n assume m: "M \<le> m" and n: "M \<le> n"
      have "?S n \<noteq> \<infinity>"
        using M[OF n] by auto
      have "norm (?s n - ?s m) \<le> ?S n + ?S m"
        by (intro simple_bochner_integral_bounded s f)
      also have "\<dots> < ereal (e / 2) + e / 2"
        using ereal_add_strict_mono[OF less_imp_le[OF M[OF n]] _ `?S n \<noteq> \<infinity>` M[OF m]]
        by (auto simp: positive_integral_positive)
      also have "\<dots> = e" by simp
      finally show "dist (?s n) (?s m) < e"
        by (simp add: dist_norm)
    qed
  qed
  then obtain x where "?s ----> x" ..
  show ?thesis
    by (rule, rule) fact+
qed

lemma positive_integral_dominated_convergence_norm:
  fixes u' :: "_ \<Rightarrow> _::{real_normed_vector, second_countable_topology}"
  assumes [measurable]:
       "\<And>i. u i \<in> borel_measurable M" "u' \<in> borel_measurable M" "w \<in> borel_measurable M"
    and bound: "\<And>j. AE x in M. norm (u j x) \<le> w x"
    and w: "(\<integral>\<^sup>+x. w x \<partial>M) < \<infinity>"
    and u': "AE x in M. (\<lambda>i. u i x) ----> u' x"
  shows "(\<lambda>i. (\<integral>\<^sup>+x. norm (u' x - u i x) \<partial>M)) ----> 0"
proof -
  have "AE x in M. \<forall>j. norm (u j x) \<le> w x"
    unfolding AE_all_countable by rule fact
  with u' have bnd: "AE x in M. \<forall>j. norm (u' x - u j x) \<le> 2 * w x"
  proof (eventually_elim, intro allI)
    fix i x assume "(\<lambda>i. u i x) ----> u' x" "\<forall>j. norm (u j x) \<le> w x" "\<forall>j. norm (u j x) \<le> w x"
    then have "norm (u' x) \<le> w x" "norm (u i x) \<le> w x"
      by (auto intro: LIMSEQ_le_const2 tendsto_norm)
    then have "norm (u' x) + norm (u i x) \<le> 2 * w x"
      by simp
    also have "norm (u' x - u i x) \<le> norm (u' x) + norm (u i x)"
      by (rule norm_triangle_ineq4)
    finally (xtrans) show "norm (u' x - u i x) \<le> 2 * w x" .
  qed
  
  have "(\<lambda>i. (\<integral>\<^sup>+x. norm (u' x - u i x) \<partial>M)) ----> (\<integral>\<^sup>+x. 0 \<partial>M)"
  proof (rule positive_integral_dominated_convergence)  
    show "(\<integral>\<^sup>+x. 2 * w x \<partial>M) < \<infinity>"
      by (rule positive_integral_mult_bounded_inf[OF _ w, of 2]) auto
    show "AE x in M. (\<lambda>i. ereal (norm (u' x - u i x))) ----> 0"
      using u' 
    proof eventually_elim
      fix x assume "(\<lambda>i. u i x) ----> u' x"
      from tendsto_diff[OF tendsto_const[of "u' x"] this]
      show "(\<lambda>i. ereal (norm (u' x - u i x))) ----> 0"
        by (simp add: zero_ereal_def tendsto_norm_zero_iff)
    qed
  qed (insert bnd, auto)
  then show ?thesis by simp
qed

lemma integrableI_bounded:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f[measurable]: "f \<in> borel_measurable M" and fin: "(\<integral>\<^sup>+x. norm (f x) \<partial>M) < \<infinity>"
  shows "integrable M f"
proof -
  from borel_measurable_implies_sequence_metric[OF f, of 0] obtain s where
    s: "\<And>i. simple_function M (s i)" and
    pointwise: "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) ----> f x" and
    bound: "\<And>i x. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)"
    by (simp add: norm_conv_dist) metis
  
  show ?thesis
  proof (rule integrableI_sequence)
    { fix i
      have "(\<integral>\<^sup>+x. norm (s i x) \<partial>M) \<le> (\<integral>\<^sup>+x. 2 * ereal (norm (f x)) \<partial>M)"
        by (intro positive_integral_mono) (simp add: bound)
      also have "\<dots> = 2 * (\<integral>\<^sup>+x. ereal (norm (f x)) \<partial>M)"
        by (rule positive_integral_cmult) auto
      finally have "(\<integral>\<^sup>+x. norm (s i x) \<partial>M) < \<infinity>"
        using fin by auto }
    note fin_s = this

    show "\<And>i. simple_bochner_integrable M (s i)"
      by (rule simple_bochner_integrableI_bounded) fact+

    show "(\<lambda>i. \<integral>\<^sup>+ x. ereal (norm (f x - s i x)) \<partial>M) ----> 0"
    proof (rule positive_integral_dominated_convergence_norm)
      show "\<And>j. AE x in M. norm (s j x) \<le> 2 * norm (f x)"
        using bound by auto
      show "\<And>i. s i \<in> borel_measurable M" "(\<lambda>x. 2 * norm (f x)) \<in> borel_measurable M"
        using s by (auto intro: borel_measurable_simple_function)
      show "(\<integral>\<^sup>+ x. ereal (2 * norm (f x)) \<partial>M) < \<infinity>"
        using fin unfolding times_ereal.simps(1)[symmetric] by (subst positive_integral_cmult) auto
      show "AE x in M. (\<lambda>i. s i x) ----> f x"
        using pointwise by auto
    qed fact
  qed fact
qed

lemma integrableI_nonneg:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>M) < \<infinity>"
  shows "integrable M f"
proof -
  have "(\<integral>\<^sup>+x. norm (f x) \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
    using assms by (intro positive_integral_cong_AE) auto
  then show ?thesis
    using assms by (intro integrableI_bounded) auto
qed

lemma integrable_iff_bounded:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "integrable M f \<longleftrightarrow> f \<in> borel_measurable M \<and> (\<integral>\<^sup>+x. norm (f x) \<partial>M) < \<infinity>"
  using integrableI_bounded[of f M] has_bochner_integral_implies_finite_norm[of M f]
  unfolding integrable.simps has_bochner_integral.simps[abs_def] by auto

lemma integrable_bound:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
    and g :: "'a \<Rightarrow> 'c::{banach, second_countable_topology}"
  shows "integrable M f \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (AE x in M. norm (g x) \<le> norm (f x)) \<Longrightarrow>
    integrable M g"
  unfolding integrable_iff_bounded
proof safe
  assume "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assume "AE x in M. norm (g x) \<le> norm (f x)"
  then have "(\<integral>\<^sup>+ x. ereal (norm (g x)) \<partial>M) \<le> (\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M)"
    by  (intro positive_integral_mono_AE) auto
  also assume "(\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M) < \<infinity>"
  finally show "(\<integral>\<^sup>+ x. ereal (norm (g x)) \<partial>M) < \<infinity>" .
qed 

lemma integrable_abs[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f" shows "integrable M (\<lambda>x. \<bar>f x\<bar>)"
  using assms by (rule integrable_bound) auto

lemma integrable_norm[simp, intro]:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "integrable M f" shows "integrable M (\<lambda>x. norm (f x))"
  using assms by (rule integrable_bound) auto
  
lemma integrable_norm_cancel:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "integrable M (\<lambda>x. norm (f x))" "f \<in> borel_measurable M" shows "integrable M f"
  using assms by (rule integrable_bound) auto

lemma integrable_abs_cancel:
  fixes f :: "'a \<Rightarrow> real"
  assumes [measurable]: "integrable M (\<lambda>x. \<bar>f x\<bar>)" "f \<in> borel_measurable M" shows "integrable M f"
  using assms by (rule integrable_bound) auto

lemma integrable_max[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes fg[measurable]: "integrable M f" "integrable M g"
  shows "integrable M (\<lambda>x. max (f x) (g x))"
  using integrable_add[OF integrable_norm[OF fg(1)] integrable_norm[OF fg(2)]]
  by (rule integrable_bound) auto

lemma integrable_min[simp, intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes fg[measurable]: "integrable M f" "integrable M g"
  shows "integrable M (\<lambda>x. min (f x) (g x))"
  using integrable_add[OF integrable_norm[OF fg(1)] integrable_norm[OF fg(2)]]
  by (rule integrable_bound) auto

lemma integral_minus_iff[simp]:
  "integrable M (\<lambda>x. - f x ::'a::{banach, second_countable_topology}) \<longleftrightarrow> integrable M f"
  unfolding integrable_iff_bounded
  by (auto intro: borel_measurable_uminus[of "\<lambda>x. - f x" M, simplified])

lemma integrable_indicator_iff:
  "integrable M (indicator A::_ \<Rightarrow> real) \<longleftrightarrow> A \<inter> space M \<in> sets M \<and> emeasure M (A \<inter> space M) < \<infinity>"
  by (simp add: integrable_iff_bounded borel_measurable_indicator_iff ereal_indicator positive_integral_indicator'
           cong: conj_cong)

lemma integral_dominated_convergence:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}" and w :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M" "\<And>i. s i \<in> borel_measurable M" "integrable M w"
  assumes lim: "AE x in M. (\<lambda>i. s i x) ----> f x"
  assumes bound: "\<And>i. AE x in M. norm (s i x) \<le> w x"
  shows "integrable M f"
    and "\<And>i. integrable M (s i)"
    and "(\<lambda>i. integral\<^sup>L M (s i)) ----> integral\<^sup>L M f"
proof -
  have "AE x in M. 0 \<le> w x"
    using bound[of 0] by eventually_elim (auto intro: norm_ge_zero order_trans)
  then have "(\<integral>\<^sup>+x. w x \<partial>M) = (\<integral>\<^sup>+x. norm (w x) \<partial>M)"
    by (intro positive_integral_cong_AE) auto
  with `integrable M w` have w: "w \<in> borel_measurable M" "(\<integral>\<^sup>+x. w x \<partial>M) < \<infinity>"
    unfolding integrable_iff_bounded by auto

  show int_s: "\<And>i. integrable M (s i)"
    unfolding integrable_iff_bounded
  proof
    fix i 
    have "(\<integral>\<^sup>+ x. ereal (norm (s i x)) \<partial>M) \<le> (\<integral>\<^sup>+x. w x \<partial>M)"
      using bound by (intro positive_integral_mono_AE) auto
    with w show "(\<integral>\<^sup>+ x. ereal (norm (s i x)) \<partial>M) < \<infinity>" by auto
  qed fact

  have all_bound: "AE x in M. \<forall>i. norm (s i x) \<le> w x"
    using bound unfolding AE_all_countable by auto

  show int_f: "integrable M f"
    unfolding integrable_iff_bounded
  proof
    have "(\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M) \<le> (\<integral>\<^sup>+x. w x \<partial>M)"
      using all_bound lim
    proof (intro positive_integral_mono_AE, eventually_elim)
      fix x assume "\<forall>i. norm (s i x) \<le> w x" "(\<lambda>i. s i x) ----> f x"
      then show "ereal (norm (f x)) \<le> ereal (w x)"
        by (intro LIMSEQ_le_const2[where X="\<lambda>i. ereal (norm (s i x))"] tendsto_intros lim_ereal[THEN iffD2]) auto
    qed
    with w show "(\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M) < \<infinity>" by auto
  qed fact

  have "(\<lambda>n. ereal (norm (integral\<^sup>L M (s n) - integral\<^sup>L M f))) ----> ereal 0" (is "?d ----> ereal 0")
  proof (rule tendsto_sandwich)
    show "eventually (\<lambda>n. ereal 0 \<le> ?d n) sequentially" "(\<lambda>_. ereal 0) ----> ereal 0" by auto
    show "eventually (\<lambda>n. ?d n \<le> (\<integral>\<^sup>+x. norm (s n x - f x) \<partial>M)) sequentially"
    proof (intro always_eventually allI)
      fix n
      have "?d n = norm (integral\<^sup>L M (\<lambda>x. s n x - f x))"
        using int_f int_s by simp
      also have "\<dots> \<le> (\<integral>\<^sup>+x. norm (s n x - f x) \<partial>M)"
        by (intro int_f int_s integrable_diff integral_norm_bound_ereal)
      finally show "?d n \<le> (\<integral>\<^sup>+x. norm (s n x - f x) \<partial>M)" .
    qed
    show "(\<lambda>n. \<integral>\<^sup>+x. norm (s n x - f x) \<partial>M) ----> ereal 0"
      unfolding zero_ereal_def[symmetric]
      apply (subst norm_minus_commute)
    proof (rule positive_integral_dominated_convergence_norm[where w=w])
      show "\<And>n. s n \<in> borel_measurable M"
        using int_s unfolding integrable_iff_bounded by auto
    qed fact+
  qed
  then have "(\<lambda>n. integral\<^sup>L M (s n) - integral\<^sup>L M f) ----> 0"
    unfolding lim_ereal tendsto_norm_zero_iff .
  from tendsto_add[OF this tendsto_const[of "integral\<^sup>L M f"]]
  show "(\<lambda>i. integral\<^sup>L M (s i)) ----> integral\<^sup>L M f"  by simp
qed

lemma integrable_mult_left_iff:
  fixes f :: "'a \<Rightarrow> real"
  shows "integrable M (\<lambda>x. c * f x) \<longleftrightarrow> c = 0 \<or> integrable M f"
  using integrable_mult_left[of c M f] integrable_mult_left[of "1 / c" M "\<lambda>x. c * f x"]
  by (cases "c = 0") auto

lemma positive_integral_eq_integral:
  assumes f: "integrable M f"
  assumes nonneg: "AE x in M. 0 \<le> f x" 
  shows "(\<integral>\<^sup>+ x. f x \<partial>M) = integral\<^sup>L M f"
proof -
  { fix f :: "'a \<Rightarrow> real" assume f: "f \<in> borel_measurable M" "\<And>x. 0 \<le> f x" "integrable M f"
    then have "(\<integral>\<^sup>+ x. f x \<partial>M) = integral\<^sup>L M f"
    proof (induct rule: borel_measurable_induct_real)
      case (set A) then show ?case
        by (simp add: integrable_indicator_iff ereal_indicator emeasure_eq_ereal_measure)
    next
      case (mult f c) then show ?case
        unfolding times_ereal.simps(1)[symmetric]
        by (subst positive_integral_cmult)
           (auto simp add: integrable_mult_left_iff zero_ereal_def[symmetric])
    next
      case (add g f)
      then have "integrable M f" "integrable M g"
        by (auto intro!: integrable_bound[OF add(8)])
      with add show ?case
        unfolding plus_ereal.simps(1)[symmetric]
        by (subst positive_integral_add) auto
    next
      case (seq s)
      { fix i x assume "x \<in> space M" with seq(4) have "s i x \<le> f x"
          by (intro LIMSEQ_le_const[OF seq(5)] exI[of _ i]) (auto simp: incseq_def le_fun_def) }
      note s_le_f = this

      show ?case
      proof (rule LIMSEQ_unique)
        show "(\<lambda>i. ereal (integral\<^sup>L M (s i))) ----> ereal (integral\<^sup>L M f)"
          unfolding lim_ereal
        proof (rule integral_dominated_convergence[where w=f])
          show "integrable M f" by fact
          from s_le_f seq show "\<And>i. AE x in M. norm (s i x) \<le> f x"
            by auto
        qed (insert seq, auto)
        have int_s: "\<And>i. integrable M (s i)"
          using seq f s_le_f by (intro integrable_bound[OF f(3)]) auto
        have "(\<lambda>i. \<integral>\<^sup>+ x. s i x \<partial>M) ----> \<integral>\<^sup>+ x. f x \<partial>M"
          using seq s_le_f f
          by (intro positive_integral_dominated_convergence[where w=f])
             (auto simp: integrable_iff_bounded)
        also have "(\<lambda>i. \<integral>\<^sup>+x. s i x \<partial>M) = (\<lambda>i. \<integral>x. s i x \<partial>M)"
          using seq int_s by simp
        finally show "(\<lambda>i. \<integral>x. s i x \<partial>M) ----> \<integral>\<^sup>+x. f x \<partial>M"
          by simp
      qed
    qed }
  from this[of "\<lambda>x. max 0 (f x)"] assms have "(\<integral>\<^sup>+ x. max 0 (f x) \<partial>M) = integral\<^sup>L M (\<lambda>x. max 0 (f x))"
    by simp
  also have "\<dots> = integral\<^sup>L M f"
    using assms by (auto intro!: integral_cong_AE)
  also have "(\<integral>\<^sup>+ x. max 0 (f x) \<partial>M) = (\<integral>\<^sup>+ x. f x \<partial>M)"
    using assms by (auto intro!: positive_integral_cong_AE simp: max_def)
  finally show ?thesis .
qed

lemma integral_norm_bound:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  shows "integrable M f \<Longrightarrow> norm (integral\<^sup>L M f) \<le> (\<integral>x. norm (f x) \<partial>M)"
  using positive_integral_eq_integral[of M "\<lambda>x. norm (f x)"]
  using integral_norm_bound_ereal[of M f] by simp
  
lemma integral_eq_positive_integral:
  "integrable M f \<Longrightarrow> (\<And>x. 0 \<le> f x) \<Longrightarrow> integral\<^sup>L M f = real (\<integral>\<^sup>+ x. ereal (f x) \<partial>M)"
  by (subst positive_integral_eq_integral) auto
  
lemma integrableI_simple_bochner_integrable:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "simple_bochner_integrable M f \<Longrightarrow> integrable M f"
  by (intro integrableI_sequence[where s="\<lambda>_. f"] borel_measurable_simple_function)
     (auto simp: zero_ereal_def[symmetric] simple_bochner_integrable.simps)

lemma integrable_induct[consumes 1, case_names base add lim, induct pred: integrable]:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable M f"
  assumes base: "\<And>A c. A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> P (\<lambda>x. indicator A x *\<^sub>R c)"
  assumes add: "\<And>f g. integrable M f \<Longrightarrow> P f \<Longrightarrow> integrable M g \<Longrightarrow> P g \<Longrightarrow> P (\<lambda>x. f x + g x)"
  assumes lim: "\<And>f s. (\<And>i. integrable M (s i)) \<Longrightarrow> (\<And>i. P (s i)) \<Longrightarrow>
   (\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) ----> f x) \<Longrightarrow>
   (\<And>i x. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)) \<Longrightarrow> integrable M f \<Longrightarrow> P f"
  shows "P f"
proof -
  from `integrable M f` have f: "f \<in> borel_measurable M" "(\<integral>\<^sup>+x. norm (f x) \<partial>M) < \<infinity>"
    unfolding integrable_iff_bounded by auto
  from borel_measurable_implies_sequence_metric[OF f(1)]
  obtain s where s: "\<And>i. simple_function M (s i)" "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) ----> f x"
    "\<And>i x. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)"
    unfolding norm_conv_dist by metis

  { fix f A 
    have [simp]: "P (\<lambda>x. 0)"
      using base[of "{}" undefined] by simp
    have "(\<And>i::'b. i \<in> A \<Longrightarrow> integrable M (f i::'a \<Rightarrow> 'b)) \<Longrightarrow>
    (\<And>i. i \<in> A \<Longrightarrow> P (f i)) \<Longrightarrow> P (\<lambda>x. \<Sum>i\<in>A. f i x)"
    by (induct A rule: infinite_finite_induct) (auto intro!: add) }
  note setsum = this

  def s' \<equiv> "\<lambda>i z. indicator (space M) z *\<^sub>R s i z"
  then have s'_eq_s: "\<And>i x. x \<in> space M \<Longrightarrow> s' i x = s i x"
    by simp

  have sf[measurable]: "\<And>i. simple_function M (s' i)"
    unfolding s'_def using s(1)
    by (intro simple_function_compose2[where h="op *\<^sub>R"] simple_function_indicator) auto

  { fix i 
    have "\<And>z. {y. s' i z = y \<and> y \<in> s' i ` space M \<and> y \<noteq> 0 \<and> z \<in> space M} =
        (if z \<in> space M \<and> s' i z \<noteq> 0 then {s' i z} else {})"
      by (auto simp add: s'_def split: split_indicator)
    then have "\<And>z. s' i = (\<lambda>z. \<Sum>y\<in>s' i`space M - {0}. indicator {x\<in>space M. s' i x = y} z *\<^sub>R y)"
      using sf by (auto simp: fun_eq_iff simple_function_def s'_def) }
  note s'_eq = this

  show "P f"
  proof (rule lim)
    fix i

    have "(\<integral>\<^sup>+x. norm (s' i x) \<partial>M) \<le> (\<integral>\<^sup>+x. 2 * ereal (norm (f x)) \<partial>M)"
      using s by (intro positive_integral_mono) (auto simp: s'_eq_s)
    also have "\<dots> < \<infinity>"
      using f by (subst positive_integral_cmult) auto
    finally have sbi: "simple_bochner_integrable M (s' i)"
      using sf by (intro simple_bochner_integrableI_bounded) auto
    then show "integrable M (s' i)"
      by (rule integrableI_simple_bochner_integrable)

    { fix x assume"x \<in> space M" "s' i x \<noteq> 0"
      then have "emeasure M {y \<in> space M. s' i y = s' i x} \<le> emeasure M {y \<in> space M. s' i y \<noteq> 0}"
        by (intro emeasure_mono) auto
      also have "\<dots> < \<infinity>"
        using sbi by (auto elim: simple_bochner_integrable.cases)
      finally have "emeasure M {y \<in> space M. s' i y = s' i x} \<noteq> \<infinity>" by simp }
    then show "P (s' i)"
      by (subst s'_eq) (auto intro!: setsum base)

    fix x assume "x \<in> space M" with s show "(\<lambda>i. s' i x) ----> f x"
      by (simp add: s'_eq_s)
    show "norm (s' i x) \<le> 2 * norm (f x)"
      using `x \<in> space M` s by (simp add: s'_eq_s)
  qed fact
qed

lemma integral_nonneg_AE:
  fixes f :: "'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f" "AE x in M. 0 \<le> f x"
  shows "0 \<le> integral\<^sup>L M f"
proof -
  have "0 \<le> ereal (integral\<^sup>L M (\<lambda>x. max 0 (f x)))"
    by (subst integral_eq_positive_integral)
       (auto intro: real_of_ereal_pos positive_integral_positive integrable_max assms)
  also have "integral\<^sup>L M (\<lambda>x. max 0 (f x)) = integral\<^sup>L M f"
    using assms(2) by (intro integral_cong_AE assms integrable_max) auto
  finally show ?thesis
    by simp
qed

lemma integral_eq_zero_AE:
  "f \<in> borel_measurable M \<Longrightarrow> (AE x in M. f x = 0) \<Longrightarrow> integral\<^sup>L M f = 0"
  using integral_cong_AE[of f M "\<lambda>_. 0"] by simp

lemma integral_nonneg_eq_0_iff_AE:
  fixes f :: "_ \<Rightarrow> real"
  assumes f[measurable]: "integrable M f" and nonneg: "AE x in M. 0 \<le> f x"
  shows "integral\<^sup>L M f = 0 \<longleftrightarrow> (AE x in M. f x = 0)"
proof
  assume "integral\<^sup>L M f = 0"
  then have "integral\<^sup>P M f = 0"
    using positive_integral_eq_integral[OF f nonneg] by simp
  then have "AE x in M. ereal (f x) \<le> 0"
    by (simp add: positive_integral_0_iff_AE)
  with nonneg show "AE x in M. f x = 0"
    by auto
qed (auto simp add: integral_eq_zero_AE)

lemma integral_mono_AE:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f" "integrable M g" "AE x in M. f x \<le> g x"
  shows "integral\<^sup>L M f \<le> integral\<^sup>L M g"
proof -
  have "0 \<le> integral\<^sup>L M (\<lambda>x. g x - f x)"
    using assms by (intro integral_nonneg_AE integrable_diff assms) auto
  also have "\<dots> = integral\<^sup>L M g - integral\<^sup>L M f"
    by (intro integral_diff assms)
  finally show ?thesis by simp
qed

lemma integral_mono:
  fixes f :: "'a \<Rightarrow> real"
  shows "integrable M f \<Longrightarrow> integrable M g \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x \<le> g x) \<Longrightarrow> 
    integral\<^sup>L M f \<le> integral\<^sup>L M g"
  by (intro integral_mono_AE) auto

subsection {* Measure spaces with an associated density *}

lemma integrable_density:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}" and g :: "'a \<Rightarrow> real"
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
    and nn: "AE x in M. 0 \<le> g x"
  shows "integrable (density M g) f \<longleftrightarrow> integrable M (\<lambda>x. g x *\<^sub>R f x)"
  unfolding integrable_iff_bounded using nn
  apply (simp add: positive_integral_density )
  apply (intro arg_cong2[where f="op ="] refl positive_integral_cong_AE)
  apply auto
  done

lemma integral_density:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}" and g :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
    and g[measurable]: "g \<in> borel_measurable M" "AE x in M. 0 \<le> g x"
  shows "integral\<^sup>L (density M g) f = integral\<^sup>L M (\<lambda>x. g x *\<^sub>R f x)"
proof (rule integral_eq_cases)
  assume "integrable (density M g) f"
  then show ?thesis
  proof induct
    case (base A c)
    then have [measurable]: "A \<in> sets M" by auto
  
    have int: "integrable M (\<lambda>x. g x * indicator A x)"
      using g base integrable_density[of "indicator A :: 'a \<Rightarrow> real" M g] by simp
    then have "integral\<^sup>L M (\<lambda>x. g x * indicator A x) = (\<integral>\<^sup>+ x. ereal (g x * indicator A x) \<partial>M)"
      using g by (subst positive_integral_eq_integral) auto
    also have "\<dots> = (\<integral>\<^sup>+ x. ereal (g x) * indicator A x \<partial>M)"
      by (intro positive_integral_cong) (auto split: split_indicator)
    also have "\<dots> = emeasure (density M g) A"
      by (rule emeasure_density[symmetric]) auto
    also have "\<dots> = ereal (measure (density M g) A)"
      using base by (auto intro: emeasure_eq_ereal_measure)
    also have "\<dots> = integral\<^sup>L (density M g) (indicator A)"
      using base by simp
    finally show ?case
      using base by (simp add: int)
  next
    case (add f h)
    then have [measurable]: "f \<in> borel_measurable M" "h \<in> borel_measurable M"
      by (auto dest!: borel_measurable_integrable)
    from add g show ?case
      by (simp add: scaleR_add_right integrable_density)
  next
    case (lim f s)
    have [measurable]: "f \<in> borel_measurable M" "\<And>i. s i \<in> borel_measurable M"
      using lim(1,5)[THEN borel_measurable_integrable] by auto
  
    show ?case
    proof (rule LIMSEQ_unique)
      show "(\<lambda>i. integral\<^sup>L M (\<lambda>x. g x *\<^sub>R s i x)) ----> integral\<^sup>L M (\<lambda>x. g x *\<^sub>R f x)"
      proof (rule integral_dominated_convergence(3))
        show "integrable M (\<lambda>x. 2 * norm (g x *\<^sub>R f x))"
          by (intro integrable_mult_right integrable_norm integrable_density[THEN iffD1] lim g) auto
        show "AE x in M. (\<lambda>i. g x *\<^sub>R s i x) ----> g x *\<^sub>R f x"
          using lim(3) by (auto intro!: tendsto_scaleR AE_I2[of M])
        show "\<And>i. AE x in M. norm (g x *\<^sub>R s i x) \<le> 2 * norm (g x *\<^sub>R f x)"
          using lim(4) g by (auto intro!: AE_I2[of M] mult_left_mono simp: field_simps)
      qed auto
      show "(\<lambda>i. integral\<^sup>L M (\<lambda>x. g x *\<^sub>R s i x)) ----> integral\<^sup>L (density M g) f"
        unfolding lim(2)[symmetric]
        by (rule integral_dominated_convergence(3)[where w="\<lambda>x. 2 * norm (f x)"])
           (insert lim(3-5), auto intro: integrable_norm)
    qed
  qed
qed (simp add: f g integrable_density)

lemma
  fixes g :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x" "g \<in> borel_measurable M"
  shows integral_real_density: "integral\<^sup>L (density M f) g = (\<integral> x. f x * g x \<partial>M)"
    and integrable_real_density: "integrable (density M f) g \<longleftrightarrow> integrable M (\<lambda>x. f x * g x)"
  using assms integral_density[of g M f] integrable_density[of g M f] by auto

lemma has_bochner_integral_density:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}" and g :: "'a \<Rightarrow> real"
  shows "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (AE x in M. 0 \<le> g x) \<Longrightarrow>
    has_bochner_integral M (\<lambda>x. g x *\<^sub>R f x) x \<Longrightarrow> has_bochner_integral (density M g) f x"
  by (simp add: has_bochner_integral_iff integrable_density integral_density)

subsection {* Distributions *}

lemma integrable_distr_eq:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "g \<in> measurable M N" "f \<in> borel_measurable N"
  shows "integrable (distr M N g) f \<longleftrightarrow> integrable M (\<lambda>x. f (g x))"
  unfolding integrable_iff_bounded by (simp_all add: positive_integral_distr)

lemma integrable_distr:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "T \<in> measurable M M' \<Longrightarrow> integrable (distr M M' T) f \<Longrightarrow> integrable M (\<lambda>x. f (T x))"
  by (subst integrable_distr_eq[symmetric, where g=T])
     (auto dest: borel_measurable_integrable)

lemma integral_distr:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes g[measurable]: "g \<in> measurable M N" and f: "f \<in> borel_measurable N"
  shows "integral\<^sup>L (distr M N g) f = integral\<^sup>L M (\<lambda>x. f (g x))"
proof (rule integral_eq_cases)
  assume "integrable (distr M N g) f"
  then show ?thesis
  proof induct
    case (base A c)
    then have [measurable]: "A \<in> sets N" by auto
    from base have int: "integrable (distr M N g) (\<lambda>a. indicator A a *\<^sub>R c)"
      by (intro integrable_indicator)
  
    have "integral\<^sup>L (distr M N g) (\<lambda>a. indicator A a *\<^sub>R c) = measure (distr M N g) A *\<^sub>R c"
      using base by (subst integral_indicator) auto
    also have "\<dots> = measure M (g -` A \<inter> space M) *\<^sub>R c"
      by (subst measure_distr) auto
    also have "\<dots> = integral\<^sup>L M (\<lambda>a. indicator (g -` A \<inter> space M) a *\<^sub>R c)"
      using base by (subst integral_indicator) (auto simp: emeasure_distr)
    also have "\<dots> = integral\<^sup>L M (\<lambda>a. indicator A (g a) *\<^sub>R c)"
      using int base by (intro integral_cong_AE) (auto simp: emeasure_distr split: split_indicator)
    finally show ?case .
  next
    case (add f h)
    then have [measurable]: "f \<in> borel_measurable N" "h \<in> borel_measurable N"
      by (auto dest!: borel_measurable_integrable)
    from add g show ?case
      by (simp add: scaleR_add_right integrable_distr_eq)
  next
    case (lim f s)
    have [measurable]: "f \<in> borel_measurable N" "\<And>i. s i \<in> borel_measurable N"
      using lim(1,5)[THEN borel_measurable_integrable] by auto
  
    show ?case
    proof (rule LIMSEQ_unique)
      show "(\<lambda>i. integral\<^sup>L M (\<lambda>x. s i (g x))) ----> integral\<^sup>L M (\<lambda>x. f (g x))"
      proof (rule integral_dominated_convergence(3))
        show "integrable M (\<lambda>x. 2 * norm (f (g x)))"
          using lim by (auto intro!: integrable_norm simp: integrable_distr_eq) 
        show "AE x in M. (\<lambda>i. s i (g x)) ----> f (g x)"
          using lim(3) g[THEN measurable_space] by auto
        show "\<And>i. AE x in M. norm (s i (g x)) \<le> 2 * norm (f (g x))"
          using lim(4) g[THEN measurable_space] by auto
      qed auto
      show "(\<lambda>i. integral\<^sup>L M (\<lambda>x. s i (g x))) ----> integral\<^sup>L (distr M N g) f"
        unfolding lim(2)[symmetric]
        by (rule integral_dominated_convergence(3)[where w="\<lambda>x. 2 * norm (f x)"])
           (insert lim(3-5), auto intro: integrable_norm)
    qed
  qed
qed (simp add: f g integrable_distr_eq)

lemma has_bochner_integral_distr:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "f \<in> borel_measurable N \<Longrightarrow> g \<in> measurable M N \<Longrightarrow>
    has_bochner_integral M (\<lambda>x. f (g x)) x \<Longrightarrow> has_bochner_integral (distr M N g) f x"
  by (simp add: has_bochner_integral_iff integrable_distr_eq integral_distr)

subsection {* Lebesgue integration on @{const count_space} *}

lemma integrable_count_space:
  fixes f :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  shows "finite X \<Longrightarrow> integrable (count_space X) f"
  by (auto simp: positive_integral_count_space integrable_iff_bounded)

lemma measure_count_space[simp]:
  "B \<subseteq> A \<Longrightarrow> finite B \<Longrightarrow> measure (count_space A) B = card B"
  unfolding measure_def by (subst emeasure_count_space ) auto

lemma lebesgue_integral_count_space_finite_support:
  assumes f: "finite {a\<in>A. f a \<noteq> 0}"
  shows "(\<integral>x. f x \<partial>count_space A) = (\<Sum>a | a \<in> A \<and> f a \<noteq> 0. f a)"
proof -
  have eq: "\<And>x. x \<in> A \<Longrightarrow> (\<Sum>a | x = a \<and> a \<in> A \<and> f a \<noteq> 0. f a) = (\<Sum>x\<in>{x}. f x)"
    by (intro setsum_mono_zero_cong_left) auto
    
  have "(\<integral>x. f x \<partial>count_space A) = (\<integral>x. (\<Sum>a | a \<in> A \<and> f a \<noteq> 0. indicator {a} x *\<^sub>R f a) \<partial>count_space A)"
    by (intro integral_cong refl) (simp add: f eq)
  also have "\<dots> = (\<Sum>a | a \<in> A \<and> f a \<noteq> 0. measure (count_space A) {a} *\<^sub>R f a)"
    by (subst integral_setsum) (auto intro!: setsum_cong)
  finally show ?thesis
    by auto
qed

lemma lebesgue_integral_count_space_finite: "finite A \<Longrightarrow> (\<integral>x. f x \<partial>count_space A) = (\<Sum>a\<in>A. f a)"
  by (subst lebesgue_integral_count_space_finite_support)
     (auto intro!: setsum_mono_zero_cong_left)

subsection {* Point measure *}

lemma lebesgue_integral_point_measure_finite:
  fixes g :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> 0 \<le> f a) \<Longrightarrow>
    integral\<^sup>L (point_measure A f) g = (\<Sum>a\<in>A. f a *\<^sub>R g a)"
  by (simp add: lebesgue_integral_count_space_finite AE_count_space integral_density point_measure_def)

lemma integrable_point_measure_finite:
  fixes g :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}" and f :: "'a \<Rightarrow> real"
  shows "finite A \<Longrightarrow> integrable (point_measure A f) g"
  unfolding point_measure_def
  apply (subst density_ereal_max_0)
  apply (subst integrable_density)
  apply (auto simp: AE_count_space integrable_count_space)
  done

subsection {* Legacy lemmas for the real-valued Lebesgue integral *}

lemma real_lebesgue_integral_def:
  assumes f: "integrable M f"
  shows "integral\<^sup>L M f = real (\<integral>\<^sup>+x. f x \<partial>M) - real (\<integral>\<^sup>+x. - f x \<partial>M)"
proof -
  have "integral\<^sup>L M f = integral\<^sup>L M (\<lambda>x. max 0 (f x) - max 0 (- f x))"
    by (auto intro!: arg_cong[where f="integral\<^sup>L M"])
  also have "\<dots> = integral\<^sup>L M (\<lambda>x. max 0 (f x)) - integral\<^sup>L M (\<lambda>x. max 0 (- f x))"
    by (intro integral_diff integrable_max integrable_minus integrable_zero f)
  also have "integral\<^sup>L M (\<lambda>x. max 0 (f x)) = real (\<integral>\<^sup>+x. max 0 (f x) \<partial>M)"
    by (subst integral_eq_positive_integral[symmetric]) (auto intro!: integrable_max f)
  also have "integral\<^sup>L M (\<lambda>x. max 0 (- f x)) = real (\<integral>\<^sup>+x. max 0 (- f x) \<partial>M)"
    by (subst integral_eq_positive_integral[symmetric]) (auto intro!: integrable_max f)
  also have "(\<lambda>x. ereal (max 0 (f x))) = (\<lambda>x. max 0 (ereal (f x)))"
    by (auto simp: max_def)
  also have "(\<lambda>x. ereal (max 0 (- f x))) = (\<lambda>x. max 0 (- ereal (f x)))"
    by (auto simp: max_def)
  finally show ?thesis
    unfolding positive_integral_max_0 .
qed

lemma real_integrable_def:
  "integrable M f \<longleftrightarrow> f \<in> borel_measurable M \<and>
    (\<integral>\<^sup>+ x. ereal (f x) \<partial>M) \<noteq> \<infinity> \<and> (\<integral>\<^sup>+ x. ereal (- f x) \<partial>M) \<noteq> \<infinity>"
  unfolding integrable_iff_bounded
proof (safe del: notI)
  assume *: "(\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M) < \<infinity>"
  have "(\<integral>\<^sup>+ x. ereal (f x) \<partial>M) \<le> (\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M)"
    by (intro positive_integral_mono) auto
  also note *
  finally show "(\<integral>\<^sup>+ x. ereal (f x) \<partial>M) \<noteq> \<infinity>"
    by simp
  have "(\<integral>\<^sup>+ x. ereal (- f x) \<partial>M) \<le> (\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M)"
    by (intro positive_integral_mono) auto
  also note *
  finally show "(\<integral>\<^sup>+ x. ereal (- f x) \<partial>M) \<noteq> \<infinity>"
    by simp
next
  assume [measurable]: "f \<in> borel_measurable M"
  assume fin: "(\<integral>\<^sup>+ x. ereal (f x) \<partial>M) \<noteq> \<infinity>" "(\<integral>\<^sup>+ x. ereal (- f x) \<partial>M) \<noteq> \<infinity>"
  have "(\<integral>\<^sup>+ x. norm (f x) \<partial>M) = (\<integral>\<^sup>+ x. max 0 (ereal (f x)) + max 0 (ereal (- f x)) \<partial>M)"
    by (intro positive_integral_cong) (auto simp: max_def)
  also have"\<dots> = (\<integral>\<^sup>+ x. max 0 (ereal (f x)) \<partial>M) + (\<integral>\<^sup>+ x. max 0 (ereal (- f x)) \<partial>M)"
    by (intro positive_integral_add) auto
  also have "\<dots> < \<infinity>"
    using fin by (auto simp: positive_integral_max_0)
  finally show "(\<integral>\<^sup>+ x. norm (f x) \<partial>M) < \<infinity>" .
qed

lemma integrableD[dest]:
  assumes "integrable M f"
  shows "f \<in> borel_measurable M" "(\<integral>\<^sup>+ x. ereal (f x) \<partial>M) \<noteq> \<infinity>" "(\<integral>\<^sup>+ x. ereal (- f x) \<partial>M) \<noteq> \<infinity>"
  using assms unfolding real_integrable_def by auto

lemma integrableE:
  assumes "integrable M f"
  obtains r q where
    "(\<integral>\<^sup>+x. ereal (f x)\<partial>M) = ereal r"
    "(\<integral>\<^sup>+x. ereal (-f x)\<partial>M) = ereal q"
    "f \<in> borel_measurable M" "integral\<^sup>L M f = r - q"
  using assms unfolding real_integrable_def real_lebesgue_integral_def[OF assms]
  using positive_integral_positive[of M "\<lambda>x. ereal (f x)"]
  using positive_integral_positive[of M "\<lambda>x. ereal (-f x)"]
  by (cases rule: ereal2_cases[of "(\<integral>\<^sup>+x. ereal (-f x)\<partial>M)" "(\<integral>\<^sup>+x. ereal (f x)\<partial>M)"]) auto

lemma integral_monotone_convergence_nonneg:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes i: "\<And>i. integrable M (f i)" and mono: "AE x in M. mono (\<lambda>n. f n x)"
    and pos: "\<And>i. AE x in M. 0 \<le> f i x"
    and lim: "AE x in M. (\<lambda>i. f i x) ----> u x"
    and ilim: "(\<lambda>i. integral\<^sup>L M (f i)) ----> x"
    and u: "u \<in> borel_measurable M"
  shows "integrable M u"
  and "integral\<^sup>L M u = x"
proof -
  have "(\<integral>\<^sup>+ x. ereal (u x) \<partial>M) = (SUP n. (\<integral>\<^sup>+ x. ereal (f n x) \<partial>M))"
  proof (subst positive_integral_monotone_convergence_SUP_AE[symmetric])
    fix i
    from mono pos show "AE x in M. ereal (f i x) \<le> ereal (f (Suc i) x) \<and> 0 \<le> ereal (f i x)"
      by eventually_elim (auto simp: mono_def)
    show "(\<lambda>x. ereal (f i x)) \<in> borel_measurable M"
      using i by auto
  next
    show "(\<integral>\<^sup>+ x. ereal (u x) \<partial>M) = \<integral>\<^sup>+ x. (SUP i. ereal (f i x)) \<partial>M"
      apply (rule positive_integral_cong_AE)
      using lim mono
      by eventually_elim (simp add: SUP_eq_LIMSEQ[THEN iffD2])
  qed
  also have "\<dots> = ereal x"
    using mono i unfolding positive_integral_eq_integral[OF i pos]
    by (subst SUP_eq_LIMSEQ) (auto simp: mono_def intro!: integral_mono_AE ilim)
  finally have "(\<integral>\<^sup>+ x. ereal (u x) \<partial>M) = ereal x" .
  moreover have "(\<integral>\<^sup>+ x. ereal (- u x) \<partial>M) = 0"
  proof (subst positive_integral_0_iff_AE)
    show "(\<lambda>x. ereal (- u x)) \<in> borel_measurable M"
      using u by auto
    from mono pos[of 0] lim show "AE x in M. ereal (- u x) \<le> 0"
    proof eventually_elim
      fix x assume "mono (\<lambda>n. f n x)" "0 \<le> f 0 x" "(\<lambda>i. f i x) ----> u x"
      then show "ereal (- u x) \<le> 0"
        using incseq_le[of "\<lambda>n. f n x" "u x" 0] by (simp add: mono_def incseq_def)
    qed
  qed
  ultimately show "integrable M u" "integral\<^sup>L M u = x"
    by (auto simp: real_integrable_def real_lebesgue_integral_def u)
qed

lemma
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes f: "\<And>i. integrable M (f i)" and mono: "AE x in M. mono (\<lambda>n. f n x)"
  and lim: "AE x in M. (\<lambda>i. f i x) ----> u x"
  and ilim: "(\<lambda>i. integral\<^sup>L M (f i)) ----> x"
  and u: "u \<in> borel_measurable M"
  shows integrable_monotone_convergence: "integrable M u"
    and integral_monotone_convergence: "integral\<^sup>L M u = x"
    and has_bochner_integral_monotone_convergence: "has_bochner_integral M u x"
proof -
  have 1: "\<And>i. integrable M (\<lambda>x. f i x - f 0 x)"
    using f by auto
  have 2: "AE x in M. mono (\<lambda>n. f n x - f 0 x)"
    using mono by (auto simp: mono_def le_fun_def)
  have 3: "\<And>n. AE x in M. 0 \<le> f n x - f 0 x"
    using mono by (auto simp: field_simps mono_def le_fun_def)
  have 4: "AE x in M. (\<lambda>i. f i x - f 0 x) ----> u x - f 0 x"
    using lim by (auto intro!: tendsto_diff)
  have 5: "(\<lambda>i. (\<integral>x. f i x - f 0 x \<partial>M)) ----> x - integral\<^sup>L M (f 0)"
    using f ilim by (auto intro!: tendsto_diff)
  have 6: "(\<lambda>x. u x - f 0 x) \<in> borel_measurable M"
    using f[of 0] u by auto
  note diff = integral_monotone_convergence_nonneg[OF 1 2 3 4 5 6]
  have "integrable M (\<lambda>x. (u x - f 0 x) + f 0 x)"
    using diff(1) f by (rule integrable_add)
  with diff(2) f show "integrable M u" "integral\<^sup>L M u = x"
    by auto
  then show "has_bochner_integral M u x"
    by (metis has_bochner_integral_integrable)
qed

lemma integral_norm_eq_0_iff:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f[measurable]: "integrable M f"
  shows "(\<integral>x. norm (f x) \<partial>M) = 0 \<longleftrightarrow> emeasure M {x\<in>space M. f x \<noteq> 0} = 0"
proof -
  have "(\<integral>\<^sup>+x. norm (f x) \<partial>M) = (\<integral>x. norm (f x) \<partial>M)"
    using f by (intro positive_integral_eq_integral integrable_norm) auto
  then have "(\<integral>x. norm (f x) \<partial>M) = 0 \<longleftrightarrow> (\<integral>\<^sup>+x. norm (f x) \<partial>M) = 0"
    by simp
  also have "\<dots> \<longleftrightarrow> emeasure M {x\<in>space M. ereal (norm (f x)) \<noteq> 0} = 0"
    by (intro positive_integral_0_iff) auto
  finally show ?thesis
    by simp
qed

lemma integral_0_iff:
  fixes f :: "'a \<Rightarrow> real"
  shows "integrable M f \<Longrightarrow> (\<integral>x. abs (f x) \<partial>M) = 0 \<longleftrightarrow> emeasure M {x\<in>space M. f x \<noteq> 0} = 0"
  using integral_norm_eq_0_iff[of M f] by simp

lemma (in finite_measure) lebesgue_integral_const[simp]:
  "(\<integral>x. a \<partial>M) = measure M (space M) *\<^sub>R a"
  using integral_indicator[of "space M" M a]
  by (simp del: integral_indicator integral_scaleR_left cong: integral_cong)

lemma (in finite_measure) integrable_const[intro!, simp]: "integrable M (\<lambda>x. a)"
  using integrable_indicator[of "space M" M a] by (simp cong: integrable_cong)

lemma (in finite_measure) integrable_const_bound:
  fixes f :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  shows "AE x in M. norm (f x) \<le> B \<Longrightarrow> f \<in> borel_measurable M \<Longrightarrow> integrable M f"
  apply (rule integrable_bound[OF integrable_const[of B], of f])
  apply assumption
  apply (cases "0 \<le> B")
  apply auto
  done

lemma (in finite_measure) integral_less_AE:
  fixes X Y :: "'a \<Rightarrow> real"
  assumes int: "integrable M X" "integrable M Y"
  assumes A: "(emeasure M) A \<noteq> 0" "A \<in> sets M" "AE x in M. x \<in> A \<longrightarrow> X x \<noteq> Y x"
  assumes gt: "AE x in M. X x \<le> Y x"
  shows "integral\<^sup>L M X < integral\<^sup>L M Y"
proof -
  have "integral\<^sup>L M X \<le> integral\<^sup>L M Y"
    using gt int by (intro integral_mono_AE) auto
  moreover
  have "integral\<^sup>L M X \<noteq> integral\<^sup>L M Y"
  proof
    assume eq: "integral\<^sup>L M X = integral\<^sup>L M Y"
    have "integral\<^sup>L M (\<lambda>x. \<bar>Y x - X x\<bar>) = integral\<^sup>L M (\<lambda>x. Y x - X x)"
      using gt int by (intro integral_cong_AE) auto
    also have "\<dots> = 0"
      using eq int by simp
    finally have "(emeasure M) {x \<in> space M. Y x - X x \<noteq> 0} = 0"
      using int by (simp add: integral_0_iff)
    moreover
    have "(\<integral>\<^sup>+x. indicator A x \<partial>M) \<le> (\<integral>\<^sup>+x. indicator {x \<in> space M. Y x - X x \<noteq> 0} x \<partial>M)"
      using A by (intro positive_integral_mono_AE) auto
    then have "(emeasure M) A \<le> (emeasure M) {x \<in> space M. Y x - X x \<noteq> 0}"
      using int A by (simp add: integrable_def)
    ultimately have "emeasure M A = 0"
      using emeasure_nonneg[of M A] by simp
    with `(emeasure M) A \<noteq> 0` show False by auto
  qed
  ultimately show ?thesis by auto
qed

lemma (in finite_measure) integral_less_AE_space:
  fixes X Y :: "'a \<Rightarrow> real"
  assumes int: "integrable M X" "integrable M Y"
  assumes gt: "AE x in M. X x < Y x" "emeasure M (space M) \<noteq> 0"
  shows "integral\<^sup>L M X < integral\<^sup>L M Y"
  using gt by (intro integral_less_AE[OF int, where A="space M"]) auto

(* GENERALIZE to banach, sct *)
lemma integral_sums:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes integrable[measurable]: "\<And>i. integrable M (f i)"
  and summable: "\<And>x. x \<in> space M \<Longrightarrow> summable (\<lambda>i. \<bar>f i x\<bar>)"
  and sums: "summable (\<lambda>i. (\<integral>x. \<bar>f i x\<bar> \<partial>M))"
  shows "integrable M (\<lambda>x. (\<Sum>i. f i x))" (is "integrable M ?S")
  and "(\<lambda>i. integral\<^sup>L M (f i)) sums (\<integral>x. (\<Sum>i. f i x) \<partial>M)" (is ?integral)
proof -
  have "\<forall>x\<in>space M. \<exists>w. (\<lambda>i. \<bar>f i x\<bar>) sums w"
    using summable unfolding summable_def by auto
  from bchoice[OF this]
  obtain w where w: "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. \<bar>f i x\<bar>) sums w x" by auto
  then have w_borel: "w \<in> borel_measurable M" unfolding sums_def
    by (rule borel_measurable_LIMSEQ) auto

  let ?w = "\<lambda>y. if y \<in> space M then w y else 0"

  obtain x where abs_sum: "(\<lambda>i. (\<integral>x. \<bar>f i x\<bar> \<partial>M)) sums x"
    using sums unfolding summable_def ..

  have 1: "\<And>n. integrable M (\<lambda>x. \<Sum>i<n. f i x)"
    using integrable by auto

  have 2: "\<And>j. AE x in M. norm (\<Sum>i<j. f i x) \<le> ?w x"
    using AE_space
  proof eventually_elim
    fix j x assume [simp]: "x \<in> space M"
    have "\<bar>\<Sum>i<j. f i x\<bar> \<le> (\<Sum>i<j. \<bar>f i x\<bar>)" by (rule setsum_abs)
    also have "\<dots> \<le> w x" using w[of x] setsum_le_suminf[of "\<lambda>i. \<bar>f i x\<bar>"] unfolding sums_iff by auto
    finally show "norm (\<Sum>i<j. f i x) \<le> ?w x" by simp
  qed

  have 3: "integrable M ?w"
  proof (rule integrable_monotone_convergence(1))
    let ?F = "\<lambda>n y. (\<Sum>i<n. \<bar>f i y\<bar>)"
    let ?w' = "\<lambda>n y. if y \<in> space M then ?F n y else 0"
    have "\<And>n. integrable M (?F n)"
      using integrable by (auto intro!: integrable_abs)
    thus "\<And>n. integrable M (?w' n)" by (simp cong: integrable_cong)
    show "AE x in M. mono (\<lambda>n. ?w' n x)"
      by (auto simp: mono_def le_fun_def intro!: setsum_mono2)
    show "AE x in M. (\<lambda>n. ?w' n x) ----> ?w x"
        using w by (simp_all add: tendsto_const sums_def)
    have *: "\<And>n. integral\<^sup>L M (?w' n) = (\<Sum>i< n. (\<integral>x. \<bar>f i x\<bar> \<partial>M))"
      using integrable by (simp add: integrable_abs cong: integral_cong)
    from abs_sum
    show "(\<lambda>i. integral\<^sup>L M (?w' i)) ----> x" unfolding * sums_def .
  qed (simp add: w_borel measurable_If_set)

  from summable[THEN summable_rabs_cancel]
  have 4: "AE x in M. (\<lambda>n. \<Sum>i<n. f i x) ----> (\<Sum>i. f i x)"
    by (auto intro: summable_LIMSEQ)

  note int = integral_dominated_convergence(1,3)[OF _ _ 3 4 2]

  from int show "integrable M ?S" by simp

  show ?integral unfolding sums_def integral_setsum(1)[symmetric, OF integrable]
    using int(2) by simp
qed

lemma integrable_mult_indicator:
  fixes f :: "'a \<Rightarrow> real"
  shows "A \<in> sets M \<Longrightarrow> integrable M f \<Longrightarrow> integrable M (\<lambda>x. f x * indicator A x)"
  by (rule integrable_bound[where f="\<lambda>x. \<bar>f x\<bar>"])
     (auto intro: integrable_abs split: split_indicator)

lemma tendsto_integral_at_top:
  fixes f :: "real \<Rightarrow> real"
  assumes M: "sets M = sets borel" and f[measurable]: "integrable M f"
  shows "((\<lambda>y. \<integral> x. f x * indicator {.. y} x \<partial>M) ---> \<integral> x. f x \<partial>M) at_top"
proof -
  have M_measure[simp]: "borel_measurable M = borel_measurable borel"
    using M by (simp add: sets_eq_imp_space_eq measurable_def)
  { fix f :: "real \<Rightarrow> real" assume f: "integrable M f" "\<And>x. 0 \<le> f x"
    then have [measurable]: "f \<in> borel_measurable borel"
      by (simp add: real_integrable_def)
    have "((\<lambda>y. \<integral> x. f x * indicator {.. y} x \<partial>M) ---> \<integral> x. f x \<partial>M) at_top"
    proof (rule tendsto_at_topI_sequentially)
      have int: "\<And>n. integrable M (\<lambda>x. f x * indicator {.. n} x)"
        by (rule integrable_mult_indicator) (auto simp: M f)
      show "(\<lambda>n. \<integral> x. f x * indicator {..real n} x \<partial>M) ----> integral\<^sup>L M f"
      proof (rule integral_dominated_convergence)
        { fix x have "eventually (\<lambda>n. f x * indicator {..real n} x = f x) sequentially"
            by (rule eventually_sequentiallyI[of "natceiling x"])
               (auto split: split_indicator simp: natceiling_le_eq) }
        from filterlim_cong[OF refl refl this]
        show "AE x in M. (\<lambda>n. f x * indicator {..real n} x) ----> f x"
          by (simp add: tendsto_const)
        show "\<And>j. AE x in M. norm (f x * indicator {.. j} x) \<le> f x"
          using f(2) by (intro AE_I2) (auto split: split_indicator)
      qed (simp | fact)+
      show "mono (\<lambda>y. \<integral> x. f x * indicator {..y} x \<partial>M)"
        by (intro monoI integral_mono int) (auto split: split_indicator intro: f)
    qed }
  note nonneg = this
  let ?P = "\<lambda>y. \<integral> x. max 0 (f x) * indicator {..y} x \<partial>M"
  let ?N = "\<lambda>y. \<integral> x. max 0 (- f x) * indicator {..y} x \<partial>M"
  let ?p = "integral\<^sup>L M (\<lambda>x. max 0 (f x))"
  let ?n = "integral\<^sup>L M (\<lambda>x. max 0 (- f x))"
  have "(?P ---> ?p) at_top" "(?N ---> ?n) at_top"
    by (auto intro!: nonneg integrable_max f)
  note tendsto_diff[OF this]
  also have "(\<lambda>y. ?P y - ?N y) = (\<lambda>y. \<integral> x. f x * indicator {..y} x \<partial>M)"
    by (subst integral_diff[symmetric])
       (auto intro!: integrable_mult_indicator integrable_max f integral_cong
             simp: M split: split_max)
  also have "?p - ?n = integral\<^sup>L M f"
    by (subst integral_diff[symmetric])
       (auto intro!: integrable_max f integral_cong simp: M split: split_max)
  finally show ?thesis .
qed

lemma
  fixes f :: "real \<Rightarrow> real"
  assumes M: "sets M = sets borel"
  assumes nonneg: "AE x in M. 0 \<le> f x"
  assumes borel: "f \<in> borel_measurable borel"
  assumes int: "\<And>y. integrable M (\<lambda>x. f x * indicator {.. y} x)"
  assumes conv: "((\<lambda>y. \<integral> x. f x * indicator {.. y} x \<partial>M) ---> x) at_top"
  shows has_bochner_integral_monotone_convergence_at_top: "has_bochner_integral M f x"
    and integrable_monotone_convergence_at_top: "integrable M f"
    and integral_monotone_convergence_at_top:"integral\<^sup>L M f = x"
proof -
  from nonneg have "AE x in M. mono (\<lambda>n::nat. f x * indicator {..real n} x)"
    by (auto split: split_indicator intro!: monoI)
  { fix x have "eventually (\<lambda>n. f x * indicator {..real n} x = f x) sequentially"
      by (rule eventually_sequentiallyI[of "natceiling x"])
         (auto split: split_indicator simp: natceiling_le_eq) }
  from filterlim_cong[OF refl refl this]
  have "AE x in M. (\<lambda>i. f x * indicator {..real i} x) ----> f x"
    by (simp add: tendsto_const)
  have "(\<lambda>i. \<integral> x. f x * indicator {..real i} x \<partial>M) ----> x"
    using conv filterlim_real_sequentially by (rule filterlim_compose)
  have M_measure[simp]: "borel_measurable M = borel_measurable borel"
    using M by (simp add: sets_eq_imp_space_eq measurable_def)
  have "f \<in> borel_measurable M"
    using borel by simp
  show "has_bochner_integral M f x"
    by (rule has_bochner_integral_monotone_convergence) fact+
  then show "integrable M f" "integral\<^sup>L M f = x"
    by (auto simp: _has_bochner_integral_iff)
qed


subsection {* Lebesgue integration on countable spaces *}

lemma integral_on_countable:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  and bij: "bij_betw enum S (f ` space M)"
  and enum_zero: "enum ` (-S) \<subseteq> {0}"
  and fin: "\<And>x. x \<noteq> 0 \<Longrightarrow> (emeasure M) (f -` {x} \<inter> space M) \<noteq> \<infinity>"
  and abs_summable: "summable (\<lambda>r. \<bar>enum r * real ((emeasure M) (f -` {enum r} \<inter> space M))\<bar>)"
  shows "integrable M f"
  and "(\<lambda>r. enum r * real ((emeasure M) (f -` {enum r} \<inter> space M))) sums integral\<^sup>L M f" (is ?sums)
proof -
  let ?A = "\<lambda>r. f -` {enum r} \<inter> space M"
  let ?F = "\<lambda>r x. enum r * indicator (?A r) x"
  have enum_eq: "\<And>r. enum r * real ((emeasure M) (?A r)) = integral\<^sup>L M (?F r)"
    using f fin by (simp add: measure_def cong: disj_cong)

  { fix x assume "x \<in> space M"
    hence "f x \<in> enum ` S" using bij unfolding bij_betw_def by auto
    then obtain i where "i\<in>S" "enum i = f x" by auto
    have F: "\<And>j. ?F j x = (if j = i then f x else 0)"
    proof cases
      fix j assume "j = i"
      thus "?thesis j" using `x \<in> space M` `enum i = f x` by (simp add: indicator_def)
    next
      fix j assume "j \<noteq> i"
      show "?thesis j" using bij `i \<in> S` `j \<noteq> i` `enum i = f x` enum_zero
        by (cases "j \<in> S") (auto simp add: indicator_def bij_betw_def inj_on_def)
    qed
    hence F_abs: "\<And>j. \<bar>if j = i then f x else 0\<bar> = (if j = i then \<bar>f x\<bar> else 0)" by auto
    have "(\<lambda>i. ?F i x) sums f x"
         "(\<lambda>i. \<bar>?F i x\<bar>) sums \<bar>f x\<bar>"
      by (auto intro!: sums_single simp: F F_abs) }
  note F_sums_f = this(1) and F_abs_sums_f = this(2)

  have int_f: "integral\<^sup>L M f = (\<integral>x. (\<Sum>r. ?F r x) \<partial>M)" "integrable M f = integrable M (\<lambda>x. \<Sum>r. ?F r x)"
    using F_sums_f by (auto intro!: integral_cong integrable_cong simp: sums_iff)

  { fix r
    have "(\<integral>x. \<bar>?F r x\<bar> \<partial>M) = (\<integral>x. \<bar>enum r\<bar> * indicator (?A r) x \<partial>M)"
      by (auto simp: indicator_def intro!: integral_cong)
    also have "\<dots> = \<bar>enum r\<bar> * real ((emeasure M) (?A r))"
      using f fin by (simp add: measure_def cong: disj_cong)
    finally have "(\<integral>x. \<bar>?F r x\<bar> \<partial>M) = \<bar>enum r * real ((emeasure M) (?A r))\<bar>"
      using f by (subst (2) abs_mult_pos[symmetric]) (auto intro!: real_of_ereal_pos measurable_sets) }
  note int_abs_F = this

  have 1: "\<And>i. integrable M (\<lambda>x. ?F i x)"
    using f fin by auto

  have 2: "\<And>x. x \<in> space M \<Longrightarrow> summable (\<lambda>i. \<bar>?F i x\<bar>)"
    using F_abs_sums_f unfolding sums_iff by auto

  from integral_sums(2)[OF 1 2, unfolded int_abs_F, OF _ abs_summable]
  show ?sums unfolding enum_eq int_f by simp

  from integral_sums(1)[OF 1 2, unfolded int_abs_F, OF _ abs_summable]
  show "integrable M f" unfolding int_f by simp
qed

subsection {* Product measure *}

lemma (in sigma_finite_measure) borel_measurable_lebesgue_integrable[measurable (raw)]:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes [measurable]: "split f \<in> borel_measurable (N \<Otimes>\<^sub>M M)"
  shows "Measurable.pred N (\<lambda>x. integrable M (f x))"
proof -
  have [simp]: "\<And>x. x \<in> space N \<Longrightarrow> integrable M (f x) \<longleftrightarrow> (\<integral>\<^sup>+y. norm (f x y) \<partial>M) < \<infinity>"
    unfolding integrable_iff_bounded by simp
  show ?thesis
    by (simp cong: measurable_cong)
qed

lemma (in sigma_finite_measure) measurable_measure[measurable (raw)]:
  "(\<And>x. x \<in> space N \<Longrightarrow> A x \<subseteq> space M) \<Longrightarrow>
    {x \<in> space (N \<Otimes>\<^sub>M M). snd x \<in> A (fst x)} \<in> sets (N \<Otimes>\<^sub>M M) \<Longrightarrow>
    (\<lambda>x. measure M (A x)) \<in> borel_measurable N"
  unfolding measure_def by (intro measurable_emeasure borel_measurable_real_of_ereal)

lemma Collect_subset [simp]: "{x\<in>A. P x} \<subseteq> A" by auto

lemma (in sigma_finite_measure) borel_measurable_lebesgue_integral[measurable (raw)]:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f[measurable]: "split f \<in> borel_measurable (N \<Otimes>\<^sub>M M)"
  shows "(\<lambda>x. \<integral>y. f x y \<partial>M) \<in> borel_measurable N"
proof -
  from borel_measurable_implies_sequence_metric[OF f, of 0] guess s ..
  then have s: "\<And>i. simple_function (N \<Otimes>\<^sub>M M) (s i)"
    "\<And>x y. x \<in> space N \<Longrightarrow> y \<in> space M \<Longrightarrow> (\<lambda>i. s i (x, y)) ----> f x y"
    "\<And>i x y. x \<in> space N \<Longrightarrow> y \<in> space M \<Longrightarrow> norm (s i (x, y)) \<le> 2 * norm (f x y)"
    by (auto simp: space_pair_measure norm_conv_dist)

  have [measurable]: "\<And>i. s i \<in> borel_measurable (N \<Otimes>\<^sub>M M)"
    by (rule borel_measurable_simple_function) fact

  have "\<And>i. s i \<in> measurable (N \<Otimes>\<^sub>M M) (count_space UNIV)"
    by (rule measurable_simple_function) fact

  def f' \<equiv> "\<lambda>i x. if integrable M (f x)
    then simple_bochner_integral M (\<lambda>y. s i (x, y))
    else (THE x. False)"

  { fix i x assume "x \<in> space N"
    then have "simple_bochner_integral M (\<lambda>y. s i (x, y)) =
      (\<Sum>z\<in>s i ` (space N \<times> space M). measure M {y \<in> space M. s i (x, y) = z} *\<^sub>R z)"
      using s(1)[THEN simple_functionD(1)]
      unfolding simple_bochner_integral_def
      by (intro setsum_mono_zero_cong_left)
         (auto simp: eq_commute space_pair_measure image_iff cong: conj_cong) }
  note eq = this

  show ?thesis
  proof (rule borel_measurable_LIMSEQ_metric)
    fix i show "f' i \<in> borel_measurable N"
      unfolding f'_def by (simp_all add: eq cong: measurable_cong if_cong)
  next
    fix x assume x: "x \<in> space N"
    { assume int_f: "integrable M (f x)"
      have int_2f: "integrable M (\<lambda>y. 2 * norm (f x y))"
        by (intro integrable_norm integrable_mult_right int_f)
      have "(\<lambda>i. integral\<^sup>L M (\<lambda>y. s i (x, y))) ----> integral\<^sup>L M (f x)"
      proof (rule integral_dominated_convergence)
        from int_f show "f x \<in> borel_measurable M" by auto
        show "\<And>i. (\<lambda>y. s i (x, y)) \<in> borel_measurable M"
          using x by simp
        show "AE xa in M. (\<lambda>i. s i (x, xa)) ----> f x xa"
          using x s(2) by auto
        show "\<And>i. AE xa in M. norm (s i (x, xa)) \<le> 2 * norm (f x xa)"
          using x s(3) by auto
      qed fact
      moreover
      { fix i
        have "simple_bochner_integrable M (\<lambda>y. s i (x, y))"
        proof (rule simple_bochner_integrableI_bounded)
          have "(\<lambda>y. s i (x, y)) ` space M \<subseteq> s i ` (space N \<times> space M)"
            using x by auto
          then show "simple_function M (\<lambda>y. s i (x, y))"
            using simple_functionD(1)[OF s(1), of i] x
            by (intro simple_function_borel_measurable)
               (auto simp: space_pair_measure dest: finite_subset)
          have "(\<integral>\<^sup>+ y. ereal (norm (s i (x, y))) \<partial>M) \<le> (\<integral>\<^sup>+ y. 2 * norm (f x y) \<partial>M)"
            using x s by (intro positive_integral_mono) auto
          also have "(\<integral>\<^sup>+ y. 2 * norm (f x y) \<partial>M) < \<infinity>"
            using int_2f by (simp add: integrable_iff_bounded)
          finally show "(\<integral>\<^sup>+ xa. ereal (norm (s i (x, xa))) \<partial>M) < \<infinity>" .
        qed
        then have "integral\<^sup>L M (\<lambda>y. s i (x, y)) = simple_bochner_integral M (\<lambda>y. s i (x, y))"
          by (rule simple_bochner_integrable_eq_integral[symmetric]) }
      ultimately have "(\<lambda>i. simple_bochner_integral M (\<lambda>y. s i (x, y))) ----> integral\<^sup>L M (f x)"
        by simp }
    then 
    show "(\<lambda>i. f' i x) ----> integral\<^sup>L M (f x)"
      unfolding f'_def
      by (cases "integrable M (f x)") (simp_all add: not_integrable_integral_eq tendsto_const)
  qed
qed

lemma (in pair_sigma_finite) integrable_product_swap:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes "integrable (M1 \<Otimes>\<^sub>M M2) f"
  shows "integrable (M2 \<Otimes>\<^sub>M M1) (\<lambda>(x,y). f (y,x))"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  have *: "(\<lambda>(x,y). f (y,x)) = (\<lambda>x. f (case x of (x,y)\<Rightarrow>(y,x)))" by (auto simp: fun_eq_iff)
  show ?thesis unfolding *
    by (rule integrable_distr[OF measurable_pair_swap'])
       (simp add: distr_pair_swap[symmetric] assms)
qed

lemma (in pair_sigma_finite) integrable_product_swap_iff:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  shows "integrable (M2 \<Otimes>\<^sub>M M1) (\<lambda>(x,y). f (y,x)) \<longleftrightarrow> integrable (M1 \<Otimes>\<^sub>M M2) f"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  from Q.integrable_product_swap[of "\<lambda>(x,y). f (y,x)"] integrable_product_swap[of f]
  show ?thesis by auto
qed

lemma (in pair_sigma_finite) integral_product_swap:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
  shows "(\<integral>(x,y). f (y,x) \<partial>(M2 \<Otimes>\<^sub>M M1)) = integral\<^sup>L (M1 \<Otimes>\<^sub>M M2) f"
proof -
  have *: "(\<lambda>(x,y). f (y,x)) = (\<lambda>x. f (case x of (x,y)\<Rightarrow>(y,x)))" by (auto simp: fun_eq_iff)
  show ?thesis unfolding *
    by (simp add: integral_distr[symmetric, OF measurable_pair_swap' f] distr_pair_swap[symmetric])
qed

lemma (in pair_sigma_finite) emeasure_pair_measure_finite:
  assumes A: "A \<in> sets (M1 \<Otimes>\<^sub>M M2)" and finite: "emeasure (M1 \<Otimes>\<^sub>M M2) A < \<infinity>"
  shows "AE x in M1. emeasure M2 {y\<in>space M2. (x, y) \<in> A} < \<infinity>"
proof -
  from M2.emeasure_pair_measure_alt[OF A] finite
  have "(\<integral>\<^sup>+ x. emeasure M2 (Pair x -` A) \<partial>M1) \<noteq> \<infinity>"
    by simp
  then have "AE x in M1. emeasure M2 (Pair x -` A) \<noteq> \<infinity>"
    by (rule positive_integral_PInf_AE[rotated]) (intro M2.measurable_emeasure_Pair A)
  moreover have "\<And>x. x \<in> space M1 \<Longrightarrow> Pair x -` A = {y\<in>space M2. (x, y) \<in> A}"
    using sets.sets_into_space[OF A] by (auto simp: space_pair_measure)
  ultimately show ?thesis by auto
qed

lemma (in pair_sigma_finite) AE_integrable_fst':
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f[measurable]: "integrable (M1 \<Otimes>\<^sub>M M2) f"
  shows "AE x in M1. integrable M2 (\<lambda>y. f (x, y))"
proof -
  have "(\<integral>\<^sup>+x. (\<integral>\<^sup>+y. norm (f (x, y)) \<partial>M2) \<partial>M1) = (\<integral>\<^sup>+x. norm (f x) \<partial>(M1 \<Otimes>\<^sub>M M2))"
    by (rule M2.positive_integral_fst) simp
  also have "(\<integral>\<^sup>+x. norm (f x) \<partial>(M1 \<Otimes>\<^sub>M M2)) \<noteq> \<infinity>"
    using f unfolding integrable_iff_bounded by simp
  finally have "AE x in M1. (\<integral>\<^sup>+y. norm (f (x, y)) \<partial>M2) \<noteq> \<infinity>"
    by (intro positive_integral_PInf_AE M2.borel_measurable_positive_integral )
       (auto simp: measurable_split_conv)
  with AE_space show ?thesis
    by eventually_elim
       (auto simp: integrable_iff_bounded measurable_compose[OF _ borel_measurable_integrable[OF f]])
qed

lemma (in pair_sigma_finite) integrable_fst':
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f[measurable]: "integrable (M1 \<Otimes>\<^sub>M M2) f"
  shows "integrable M1 (\<lambda>x. \<integral>y. f (x, y) \<partial>M2)"
  unfolding integrable_iff_bounded
proof
  show "(\<lambda>x. \<integral> y. f (x, y) \<partial>M2) \<in> borel_measurable M1"
    by (rule M2.borel_measurable_lebesgue_integral) simp
  have "(\<integral>\<^sup>+ x. ereal (norm (\<integral> y. f (x, y) \<partial>M2)) \<partial>M1) \<le> (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. norm (f (x, y)) \<partial>M2) \<partial>M1)"
    using AE_integrable_fst'[OF f] by (auto intro!: positive_integral_mono_AE integral_norm_bound_ereal)
  also have "(\<integral>\<^sup>+x. (\<integral>\<^sup>+y. norm (f (x, y)) \<partial>M2) \<partial>M1) = (\<integral>\<^sup>+x. norm (f x) \<partial>(M1 \<Otimes>\<^sub>M M2))"
    by (rule M2.positive_integral_fst) simp
  also have "(\<integral>\<^sup>+x. norm (f x) \<partial>(M1 \<Otimes>\<^sub>M M2)) < \<infinity>"
    using f unfolding integrable_iff_bounded by simp
  finally show "(\<integral>\<^sup>+ x. ereal (norm (\<integral> y. f (x, y) \<partial>M2)) \<partial>M1) < \<infinity>" .
qed

lemma (in pair_sigma_finite) integral_fst':
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f: "integrable (M1 \<Otimes>\<^sub>M M2) f"
  shows "(\<integral>x. (\<integral>y. f (x, y) \<partial>M2) \<partial>M1) = integral\<^sup>L (M1 \<Otimes>\<^sub>M M2) f"
using f proof induct
  case (base A c)
  have A[measurable]: "A \<in> sets (M1 \<Otimes>\<^sub>M M2)" by fact

  have eq: "\<And>x y. x \<in> space M1 \<Longrightarrow> indicator A (x, y) = indicator {y\<in>space M2. (x, y) \<in> A} y"
    using sets.sets_into_space[OF A] by (auto split: split_indicator simp: space_pair_measure)

  have int_A: "integrable (M1 \<Otimes>\<^sub>M M2) (indicator A :: _ \<Rightarrow> real)"
    using base by (rule integrable_real_indicator)

  have "(\<integral> x. \<integral> y. indicator A (x, y) *\<^sub>R c \<partial>M2 \<partial>M1) = (\<integral>x. measure M2 {y\<in>space M2. (x, y) \<in> A} *\<^sub>R c \<partial>M1)"
  proof (intro integral_cong_AE, simp, simp)
    from AE_integrable_fst'[OF int_A] AE_space
    show "AE x in M1. (\<integral>y. indicator A (x, y) *\<^sub>R c \<partial>M2) = measure M2 {y\<in>space M2. (x, y) \<in> A} *\<^sub>R c"
      by eventually_elim (simp add: eq integrable_indicator_iff)
  qed
  also have "\<dots> = measure (M1 \<Otimes>\<^sub>M M2) A *\<^sub>R c"
  proof (subst integral_scaleR_left)
    have "(\<integral>\<^sup>+x. ereal (measure M2 {y \<in> space M2. (x, y) \<in> A}) \<partial>M1) =
      (\<integral>\<^sup>+x. emeasure M2 {y \<in> space M2. (x, y) \<in> A} \<partial>M1)"
      using emeasure_pair_measure_finite[OF base]
      by (intro positive_integral_cong_AE, eventually_elim) (simp add: emeasure_eq_ereal_measure)
    also have "\<dots> = emeasure (M1 \<Otimes>\<^sub>M M2) A"
      using sets.sets_into_space[OF A]
      by (subst M2.emeasure_pair_measure_alt)
         (auto intro!: positive_integral_cong arg_cong[where f="emeasure M2"] simp: space_pair_measure)
    finally have *: "(\<integral>\<^sup>+x. ereal (measure M2 {y \<in> space M2. (x, y) \<in> A}) \<partial>M1) = emeasure (M1 \<Otimes>\<^sub>M M2) A" .

    from base * show "integrable M1 (\<lambda>x. measure M2 {y \<in> space M2. (x, y) \<in> A})"
      by (simp add: measure_nonneg integrable_iff_bounded)
    then have "(\<integral>x. measure M2 {y \<in> space M2. (x, y) \<in> A} \<partial>M1) = 
      (\<integral>\<^sup>+x. ereal (measure M2 {y \<in> space M2. (x, y) \<in> A}) \<partial>M1)"
      by (rule positive_integral_eq_integral[symmetric]) (simp add: measure_nonneg)
    also note *
    finally show "(\<integral>x. measure M2 {y \<in> space M2. (x, y) \<in> A} \<partial>M1) *\<^sub>R c = measure (M1 \<Otimes>\<^sub>M M2) A *\<^sub>R c"
      using base by (simp add: emeasure_eq_ereal_measure)
  qed
  also have "\<dots> = (\<integral> a. indicator A a *\<^sub>R c \<partial>(M1 \<Otimes>\<^sub>M M2))"
    using base by simp
  finally show ?case .
next
  case (add f g)
  then have [measurable]: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)" "g \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
    by auto
  have "(\<integral> x. \<integral> y. f (x, y) + g (x, y) \<partial>M2 \<partial>M1) = 
    (\<integral> x. (\<integral> y. f (x, y) \<partial>M2) + (\<integral> y. g (x, y) \<partial>M2) \<partial>M1)"
    apply (rule integral_cong_AE)
    apply simp_all
    using AE_integrable_fst'[OF add(1)] AE_integrable_fst'[OF add(3)]
    apply eventually_elim
    apply simp
    done 
  also have "\<dots> = (\<integral> x. f x \<partial>(M1 \<Otimes>\<^sub>M M2)) + (\<integral> x. g x \<partial>(M1 \<Otimes>\<^sub>M M2))"
    using integrable_fst'[OF add(1)] integrable_fst'[OF add(3)] add(2,4) by simp
  finally show ?case
    using add by simp
next
  case (lim f s)
  then have [measurable]: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)" "\<And>i. s i \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
    by auto
  
  show ?case
  proof (rule LIMSEQ_unique)
    show "(\<lambda>i. integral\<^sup>L (M1 \<Otimes>\<^sub>M M2) (s i)) ----> integral\<^sup>L (M1 \<Otimes>\<^sub>M M2) f"
    proof (rule integral_dominated_convergence)
      show "integrable (M1 \<Otimes>\<^sub>M M2) (\<lambda>x. 2 * norm (f x))"
        using lim(5) by (auto intro: integrable_norm)
    qed (insert lim, auto)
    have "(\<lambda>i. \<integral> x. \<integral> y. s i (x, y) \<partial>M2 \<partial>M1) ----> \<integral> x. \<integral> y. f (x, y) \<partial>M2 \<partial>M1"
    proof (rule integral_dominated_convergence)
      have "AE x in M1. \<forall>i. integrable M2 (\<lambda>y. s i (x, y))"
        unfolding AE_all_countable using AE_integrable_fst'[OF lim(1)] ..
      with AE_space AE_integrable_fst'[OF lim(5)]
      show "AE x in M1. (\<lambda>i. \<integral> y. s i (x, y) \<partial>M2) ----> \<integral> y. f (x, y) \<partial>M2"
      proof eventually_elim
        fix x assume x: "x \<in> space M1" and
          s: "\<forall>i. integrable M2 (\<lambda>y. s i (x, y))" and f: "integrable M2 (\<lambda>y. f (x, y))"
        show "(\<lambda>i. \<integral> y. s i (x, y) \<partial>M2) ----> \<integral> y. f (x, y) \<partial>M2"
        proof (rule integral_dominated_convergence)
          show "integrable M2 (\<lambda>y. 2 * norm (f (x, y)))"
             using f by (auto intro: integrable_norm)
          show "AE xa in M2. (\<lambda>i. s i (x, xa)) ----> f (x, xa)"
            using x lim(3) by (auto simp: space_pair_measure)
          show "\<And>i. AE xa in M2. norm (s i (x, xa)) \<le> 2 * norm (f (x, xa))"
            using x lim(4) by (auto simp: space_pair_measure)
        qed (insert x, measurable)
      qed
      show "integrable M1 (\<lambda>x. (\<integral> y. 2 * norm (f (x, y)) \<partial>M2))"
        by (intro integrable_mult_right integrable_norm integrable_fst' lim)
      fix i show "AE x in M1. norm (\<integral> y. s i (x, y) \<partial>M2) \<le> (\<integral> y. 2 * norm (f (x, y)) \<partial>M2)"
        using AE_space AE_integrable_fst'[OF lim(1), of i] AE_integrable_fst'[OF lim(5)]
      proof eventually_elim 
        fix x assume x: "x \<in> space M1"
          and s: "integrable M2 (\<lambda>y. s i (x, y))" and f: "integrable M2 (\<lambda>y. f (x, y))"
        from s have "norm (\<integral> y. s i (x, y) \<partial>M2) \<le> (\<integral>\<^sup>+y. norm (s i (x, y)) \<partial>M2)"
          by (rule integral_norm_bound_ereal)
        also have "\<dots> \<le> (\<integral>\<^sup>+y. 2 * norm (f (x, y)) \<partial>M2)"
          using x lim by (auto intro!: positive_integral_mono simp: space_pair_measure)
        also have "\<dots> = (\<integral>y. 2 * norm (f (x, y)) \<partial>M2)"
          using f by (intro positive_integral_eq_integral) auto
        finally show "norm (\<integral> y. s i (x, y) \<partial>M2) \<le> (\<integral> y. 2 * norm (f (x, y)) \<partial>M2)"
          by simp
      qed
    qed simp_all
    then show "(\<lambda>i. integral\<^sup>L (M1 \<Otimes>\<^sub>M M2) (s i)) ----> \<integral> x. \<integral> y. f (x, y) \<partial>M2 \<partial>M1"
      using lim by simp
  qed
qed

lemma (in pair_sigma_finite)
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f: "integrable (M1 \<Otimes>\<^sub>M M2) (split f)"
  shows AE_integrable_fst: "AE x in M1. integrable M2 (\<lambda>y. f x y)" (is "?AE")
    and integrable_fst: "integrable M1 (\<lambda>x. \<integral>y. f x y \<partial>M2)" (is "?INT")
    and integral_fst: "(\<integral>x. (\<integral>y. f x y \<partial>M2) \<partial>M1) = integral\<^sup>L (M1 \<Otimes>\<^sub>M M2) (\<lambda>(x, y). f x y)" (is "?EQ")
  using AE_integrable_fst'[OF f] integrable_fst'[OF f] integral_fst'[OF f] by auto

lemma (in pair_sigma_finite)
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f[measurable]: "integrable (M1 \<Otimes>\<^sub>M M2) (split f)"
  shows AE_integrable_snd: "AE y in M2. integrable M1 (\<lambda>x. f x y)" (is "?AE")
    and integrable_snd: "integrable M2 (\<lambda>y. \<integral>x. f x y \<partial>M1)" (is "?INT")
    and integral_snd: "(\<integral>y. (\<integral>x. f x y \<partial>M1) \<partial>M2) = integral\<^sup>L (M1 \<Otimes>\<^sub>M M2) (split f)" (is "?EQ")
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  have Q_int: "integrable (M2 \<Otimes>\<^sub>M M1) (\<lambda>(x, y). f y x)"
    using f unfolding integrable_product_swap_iff[symmetric] by simp
  show ?AE  using Q.AE_integrable_fst'[OF Q_int] by simp
  show ?INT using Q.integrable_fst'[OF Q_int] by simp
  show ?EQ using Q.integral_fst'[OF Q_int]
    using integral_product_swap[of "split f"] by simp
qed

lemma (in pair_sigma_finite) Fubini_integral:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes f: "integrable (M1 \<Otimes>\<^sub>M M2) (split f)"
  shows "(\<integral>y. (\<integral>x. f x y \<partial>M1) \<partial>M2) = (\<integral>x. (\<integral>y. f x y \<partial>M2) \<partial>M1)"
  unfolding integral_snd[OF assms] integral_fst[OF assms] ..

lemma (in product_sigma_finite) product_integral_singleton:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  shows "f \<in> borel_measurable (M i) \<Longrightarrow> (\<integral>x. f (x i) \<partial>Pi\<^sub>M {i} M) = integral\<^sup>L (M i) f"
  apply (subst distr_singleton[symmetric])
  apply (subst integral_distr)
  apply simp_all
  done

lemma (in product_sigma_finite) product_integral_fold:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes IJ[simp]: "I \<inter> J = {}" and fin: "finite I" "finite J"
  and f: "integrable (Pi\<^sub>M (I \<union> J) M) f"
  shows "integral\<^sup>L (Pi\<^sub>M (I \<union> J) M) f = (\<integral>x. (\<integral>y. f (merge I J (x, y)) \<partial>Pi\<^sub>M J M) \<partial>Pi\<^sub>M I M)"
proof -
  interpret I: finite_product_sigma_finite M I by default fact
  interpret J: finite_product_sigma_finite M J by default fact
  have "finite (I \<union> J)" using fin by auto
  interpret IJ: finite_product_sigma_finite M "I \<union> J" by default fact
  interpret P: pair_sigma_finite "Pi\<^sub>M I M" "Pi\<^sub>M J M" by default
  let ?M = "merge I J"
  let ?f = "\<lambda>x. f (?M x)"
  from f have f_borel: "f \<in> borel_measurable (Pi\<^sub>M (I \<union> J) M)"
    by auto
  have P_borel: "(\<lambda>x. f (merge I J x)) \<in> borel_measurable (Pi\<^sub>M I M \<Otimes>\<^sub>M Pi\<^sub>M J M)"
    using measurable_comp[OF measurable_merge f_borel] by (simp add: comp_def)
  have f_int: "integrable (Pi\<^sub>M I M \<Otimes>\<^sub>M Pi\<^sub>M J M) ?f"
    by (rule integrable_distr[OF measurable_merge]) (simp add: distr_merge[OF IJ fin] f)
  show ?thesis
    apply (subst distr_merge[symmetric, OF IJ fin])
    apply (subst integral_distr[OF measurable_merge f_borel])
    apply (subst P.integral_fst'[symmetric, OF f_int])
    apply simp
    done
qed

lemma (in product_sigma_finite) product_integral_insert:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes I: "finite I" "i \<notin> I"
    and f: "integrable (Pi\<^sub>M (insert i I) M) f"
  shows "integral\<^sup>L (Pi\<^sub>M (insert i I) M) f = (\<integral>x. (\<integral>y. f (x(i:=y)) \<partial>M i) \<partial>Pi\<^sub>M I M)"
proof -
  have "integral\<^sup>L (Pi\<^sub>M (insert i I) M) f = integral\<^sup>L (Pi\<^sub>M (I \<union> {i}) M) f"
    by simp
  also have "\<dots> = (\<integral>x. (\<integral>y. f (merge I {i} (x,y)) \<partial>Pi\<^sub>M {i} M) \<partial>Pi\<^sub>M I M)"
    using f I by (intro product_integral_fold) auto
  also have "\<dots> = (\<integral>x. (\<integral>y. f (x(i := y)) \<partial>M i) \<partial>Pi\<^sub>M I M)"
  proof (rule integral_cong[OF refl], subst product_integral_singleton[symmetric])
    fix x assume x: "x \<in> space (Pi\<^sub>M I M)"
    have f_borel: "f \<in> borel_measurable (Pi\<^sub>M (insert i I) M)"
      using f by auto
    show "(\<lambda>y. f (x(i := y))) \<in> borel_measurable (M i)"
      using measurable_comp[OF measurable_component_update f_borel, OF x `i \<notin> I`]
      unfolding comp_def .
    from x I show "(\<integral> y. f (merge I {i} (x,y)) \<partial>Pi\<^sub>M {i} M) = (\<integral> xa. f (x(i := xa i)) \<partial>Pi\<^sub>M {i} M)"
      by (auto intro!: integral_cong arg_cong[where f=f] simp: merge_def space_PiM extensional_def PiE_def)
  qed
  finally show ?thesis .
qed

lemma (in product_sigma_finite) product_integrable_setprod:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> _::{real_normed_field,banach,second_countable_topology}"
  assumes [simp]: "finite I" and integrable: "\<And>i. i \<in> I \<Longrightarrow> integrable (M i) (f i)"
  shows "integrable (Pi\<^sub>M I M) (\<lambda>x. (\<Prod>i\<in>I. f i (x i)))" (is "integrable _ ?f")
proof (unfold integrable_iff_bounded, intro conjI)
  interpret finite_product_sigma_finite M I by default fact
  show "?f \<in> borel_measurable (Pi\<^sub>M I M)"
    using assms by simp
  have "(\<integral>\<^sup>+ x. ereal (norm (\<Prod>i\<in>I. f i (x i))) \<partial>Pi\<^sub>M I M) = 
      (\<integral>\<^sup>+ x. (\<Prod>i\<in>I. ereal (norm (f i (x i)))) \<partial>Pi\<^sub>M I M)"
    by (simp add: setprod_norm setprod_ereal)
  also have "\<dots> = (\<Prod>i\<in>I. \<integral>\<^sup>+ x. ereal (norm (f i x)) \<partial>M i)"
    using assms by (intro product_positive_integral_setprod) auto
  also have "\<dots> < \<infinity>"
    using integrable by (simp add: setprod_PInf positive_integral_positive integrable_iff_bounded)
  finally show "(\<integral>\<^sup>+ x. ereal (norm (\<Prod>i\<in>I. f i (x i))) \<partial>Pi\<^sub>M I M) < \<infinity>" .
qed

lemma (in product_sigma_finite) product_integral_setprod:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> _::{real_normed_field,banach,second_countable_topology}"
  assumes "finite I" and integrable: "\<And>i. i \<in> I \<Longrightarrow> integrable (M i) (f i)"
  shows "(\<integral>x. (\<Prod>i\<in>I. f i (x i)) \<partial>Pi\<^sub>M I M) = (\<Prod>i\<in>I. integral\<^sup>L (M i) (f i))"
using assms proof induct
  case empty
  interpret finite_measure "Pi\<^sub>M {} M"
    by rule (simp add: space_PiM)
  show ?case by (simp add: space_PiM measure_def)
next
  case (insert i I)
  then have iI: "finite (insert i I)" by auto
  then have prod: "\<And>J. J \<subseteq> insert i I \<Longrightarrow>
    integrable (Pi\<^sub>M J M) (\<lambda>x. (\<Prod>i\<in>J. f i (x i)))"
    by (intro product_integrable_setprod insert(4)) (auto intro: finite_subset)
  interpret I: finite_product_sigma_finite M I by default fact
  have *: "\<And>x y. (\<Prod>j\<in>I. f j (if j = i then y else x j)) = (\<Prod>j\<in>I. f j (x j))"
    using `i \<notin> I` by (auto intro!: setprod_cong)
  show ?case
    unfolding product_integral_insert[OF insert(1,2) prod[OF subset_refl]]
    by (simp add: * insert prod subset_insertI)
qed

lemma integrable_subalgebra:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes borel: "f \<in> borel_measurable N"
  and N: "sets N \<subseteq> sets M" "space N = space M" "\<And>A. A \<in> sets N \<Longrightarrow> emeasure N A = emeasure M A"
  shows "integrable N f \<longleftrightarrow> integrable M f" (is ?P)
proof -
  have "f \<in> borel_measurable M"
    using assms by (auto simp: measurable_def)
  with assms show ?thesis
    using assms by (auto simp: integrable_iff_bounded positive_integral_subalgebra)
qed

lemma integral_subalgebra:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes borel: "f \<in> borel_measurable N"
  and N: "sets N \<subseteq> sets M" "space N = space M" "\<And>A. A \<in> sets N \<Longrightarrow> emeasure N A = emeasure M A"
  shows "integral\<^sup>L N f = integral\<^sup>L M f"
proof cases
  assume "integrable N f"
  then show ?thesis
  proof induct
    case base with assms show ?case by (auto simp: subset_eq measure_def)
  next
    case (add f g)
    then have "(\<integral> a. f a + g a \<partial>N) = integral\<^sup>L M f + integral\<^sup>L M g"
      by simp
    also have "\<dots> = (\<integral> a. f a + g a \<partial>M)"
      using add integrable_subalgebra[OF _ N, of f] integrable_subalgebra[OF _ N, of g] by simp
    finally show ?case .
  next
    case (lim f s)
    then have M: "\<And>i. integrable M (s i)" "integrable M f"
      using integrable_subalgebra[OF _ N, of f] integrable_subalgebra[OF _ N, of "s i" for i] by simp_all
    show ?case
    proof (intro LIMSEQ_unique)
      show "(\<lambda>i. integral\<^sup>L N (s i)) ----> integral\<^sup>L N f"
        apply (rule integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f x)"])
        using lim
        apply auto
        done
      show "(\<lambda>i. integral\<^sup>L N (s i)) ----> integral\<^sup>L M f"
        unfolding lim
        apply (rule integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f x)"])
        using lim M N(2)
        apply auto
        done
    qed
  qed
qed (simp add: not_integrable_integral_eq integrable_subalgebra[OF assms])

hide_const simple_bochner_integral
hide_const simple_bochner_integrable

end
