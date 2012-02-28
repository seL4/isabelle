(*  Title:      HOL/Probability/Conditional_Probability.thy
    Author:     Johannes Hölzl, TU München
*)

header {*Conditional probability*}

theory Conditional_Probability
imports Probability_Measure Radon_Nikodym
begin

section "Conditional Expectation and Probability"

definition (in prob_space)
  "conditional_expectation N X = (SOME Y. Y\<in>borel_measurable N \<and> (\<forall>x. 0 \<le> Y x)
    \<and> (\<forall>C\<in>sets N. (\<integral>\<^isup>+x. Y x * indicator C x\<partial>M) = (\<integral>\<^isup>+x. X x * indicator C x\<partial>M)))"

lemma (in prob_space) conditional_expectation_exists:
  fixes X :: "'a \<Rightarrow> ereal" and N :: "('a, 'b) measure_space_scheme"
  assumes borel: "X \<in> borel_measurable M" "AE x. 0 \<le> X x"
  and N: "sigma_algebra N" "sets N \<subseteq> sets M" "space N = space M" "\<And>A. measure N A = \<mu> A"
  shows "\<exists>Y\<in>borel_measurable N. (\<forall>x. 0 \<le> Y x) \<and> (\<forall>C\<in>sets N.
      (\<integral>\<^isup>+x. Y x * indicator C x \<partial>M) = (\<integral>\<^isup>+x. X x * indicator C x \<partial>M))"
proof -
  note N(4)[simp]
  interpret P: prob_space N
    using prob_space_subalgebra[OF N] .

  let ?f = "\<lambda>A x. X x * indicator A x"
  let ?Q = "\<lambda>A. integral\<^isup>P M (?f A)"

  from measure_space_density[OF borel]
  have Q: "measure_space (N\<lparr> measure := ?Q \<rparr>)"
    apply (rule measure_space.measure_space_subalgebra[of "M\<lparr> measure := ?Q \<rparr>"])
    using N by (auto intro!: P.sigma_algebra_cong)
  then interpret Q: measure_space "N\<lparr> measure := ?Q \<rparr>" .

  have "P.absolutely_continuous ?Q"
    unfolding P.absolutely_continuous_def
  proof safe
    fix A assume "A \<in> sets N" "P.\<mu> A = 0"
    then have f_borel: "?f A \<in> borel_measurable M" "AE x. x \<notin> A"
      using borel N by (auto intro!: borel_measurable_indicator AE_not_in)
    then show "?Q A = 0"
      by (auto simp add: positive_integral_0_iff_AE)
  qed
  from P.Radon_Nikodym[OF Q this]
  obtain Y where Y: "Y \<in> borel_measurable N" "\<And>x. 0 \<le> Y x"
    "\<And>A. A \<in> sets N \<Longrightarrow> ?Q A =(\<integral>\<^isup>+x. Y x * indicator A x \<partial>N)"
    by blast
  with N(2) show ?thesis
    by (auto intro!: bexI[OF _ Y(1)] simp: positive_integral_subalgebra[OF _ _ N(2,3,4,1)])
qed

lemma (in prob_space)
  fixes X :: "'a \<Rightarrow> ereal" and N :: "('a, 'b) measure_space_scheme"
  assumes borel: "X \<in> borel_measurable M" "AE x. 0 \<le> X x"
  and N: "sigma_algebra N" "sets N \<subseteq> sets M" "space N = space M" "\<And>A. measure N A = \<mu> A"
  shows borel_measurable_conditional_expectation:
    "conditional_expectation N X \<in> borel_measurable N"
  and conditional_expectation: "\<And>C. C \<in> sets N \<Longrightarrow>
      (\<integral>\<^isup>+x. conditional_expectation N X x * indicator C x \<partial>M) =
      (\<integral>\<^isup>+x. X x * indicator C x \<partial>M)"
   (is "\<And>C. C \<in> sets N \<Longrightarrow> ?eq C")
proof -
  note CE = conditional_expectation_exists[OF assms, unfolded Bex_def]
  then show "conditional_expectation N X \<in> borel_measurable N"
    unfolding conditional_expectation_def by (rule someI2_ex) blast

  from CE show "\<And>C. C \<in> sets N \<Longrightarrow> ?eq C"
    unfolding conditional_expectation_def by (rule someI2_ex) blast
qed

lemma (in sigma_algebra) factorize_measurable_function_pos:
  fixes Z :: "'a \<Rightarrow> ereal" and Y :: "'a \<Rightarrow> 'c"
  assumes "sigma_algebra M'" and "Y \<in> measurable M M'" "Z \<in> borel_measurable M"
  assumes Z: "Z \<in> borel_measurable (sigma_algebra.vimage_algebra M' (space M) Y)"
  shows "\<exists>g\<in>borel_measurable M'. \<forall>x\<in>space M. max 0 (Z x) = g (Y x)"
proof -
  interpret M': sigma_algebra M' by fact
  have Y: "Y \<in> space M \<rightarrow> space M'" using assms unfolding measurable_def by auto
  from M'.sigma_algebra_vimage[OF this]
  interpret va: sigma_algebra "M'.vimage_algebra (space M) Y" .

  from va.borel_measurable_implies_simple_function_sequence'[OF Z] guess f . note f = this

  have "\<forall>i. \<exists>g. simple_function M' g \<and> (\<forall>x\<in>space M. f i x = g (Y x))"
  proof
    fix i
    from f(1)[of i] have "finite (f i`space M)" and B_ex:
      "\<forall>z\<in>(f i)`space M. \<exists>B. B \<in> sets M' \<and> (f i) -` {z} \<inter> space M = Y -` B \<inter> space M"
      unfolding simple_function_def by auto
    from B_ex[THEN bchoice] guess B .. note B = this

    let ?g = "\<lambda>x. \<Sum>z\<in>f i`space M. z * indicator (B z) x"

    show "\<exists>g. simple_function M' g \<and> (\<forall>x\<in>space M. f i x = g (Y x))"
    proof (intro exI[of _ ?g] conjI ballI)
      show "simple_function M' ?g" using B by auto

      fix x assume "x \<in> space M"
      then have "\<And>z. z \<in> f i`space M \<Longrightarrow> indicator (B z) (Y x) = (indicator (f i -` {z} \<inter> space M) x::ereal)"
        unfolding indicator_def using B by auto
      then show "f i x = ?g (Y x)" using `x \<in> space M` f(1)[of i]
        by (subst va.simple_function_indicator_representation) auto
    qed
  qed
  from choice[OF this] guess g .. note g = this

  show ?thesis
  proof (intro ballI bexI)
    show "(\<lambda>x. SUP i. g i x) \<in> borel_measurable M'"
      using g by (auto intro: M'.borel_measurable_simple_function)
    fix x assume "x \<in> space M"
    have "max 0 (Z x) = (SUP i. f i x)" using f by simp
    also have "\<dots> = (SUP i. g i (Y x))"
      using g `x \<in> space M` by simp
    finally show "max 0 (Z x) = (SUP i. g i (Y x))" .
  qed
qed

lemma (in sigma_algebra) factorize_measurable_function:
  fixes Z :: "'a \<Rightarrow> ereal" and Y :: "'a \<Rightarrow> 'c"
  assumes "sigma_algebra M'" and "Y \<in> measurable M M'" "Z \<in> borel_measurable M"
  shows "Z \<in> borel_measurable (sigma_algebra.vimage_algebra M' (space M) Y)
    \<longleftrightarrow> (\<exists>g\<in>borel_measurable M'. \<forall>x\<in>space M. Z x = g (Y x))"
proof safe
  interpret M': sigma_algebra M' by fact
  have Y: "Y \<in> space M \<rightarrow> space M'" using assms unfolding measurable_def by auto
  from M'.sigma_algebra_vimage[OF this]
  interpret va: sigma_algebra "M'.vimage_algebra (space M) Y" .

  { fix g :: "'c \<Rightarrow> ereal" assume "g \<in> borel_measurable M'"
    with M'.measurable_vimage_algebra[OF Y]
    have "g \<circ> Y \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
      by (rule measurable_comp)
    moreover assume "\<forall>x\<in>space M. Z x = g (Y x)"
    then have "Z \<in> borel_measurable (M'.vimage_algebra (space M) Y) \<longleftrightarrow>
       g \<circ> Y \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
       by (auto intro!: measurable_cong)
    ultimately show "Z \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
      by simp }

  assume Z: "Z \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
  with assms have "(\<lambda>x. - Z x) \<in> borel_measurable M"
    "(\<lambda>x. - Z x) \<in> borel_measurable (M'.vimage_algebra (space M) Y)"
    by auto
  from factorize_measurable_function_pos[OF assms(1,2) this] guess n .. note n = this
  from factorize_measurable_function_pos[OF assms Z] guess p .. note p = this
  let ?g = "\<lambda>x. p x - n x"
  show "\<exists>g\<in>borel_measurable M'. \<forall>x\<in>space M. Z x = g (Y x)"
  proof (intro bexI ballI)
    show "?g \<in> borel_measurable M'" using p n by auto
    fix x assume "x \<in> space M"
    then have "p (Y x) = max 0 (Z x)" "n (Y x) = max 0 (- Z x)"
      using p n by auto
    then show "Z x = ?g (Y x)"
      by (auto split: split_max)
  qed
qed

end