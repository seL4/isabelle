theory Euclidean_Lebesgue
  imports Lebesgue_Integration Lebesgue_Measure
begin

lemma simple_function_has_integral:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> pinfreal"
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
  show ?case unfolding space_lebesgue_space real_of_pinfreal_setsum'[OF *(1),THEN sym]
    unfolding real_of_pinfreal_setsum'[OF *(2),THEN sym]
    unfolding real_of_pinfreal_setsum space_lebesgue_space
    apply(rule has_integral_setsum)
  proof safe show "finite (range f)" using f by (auto dest: lebesgue.simple_functionD)
    fix y::'a show "((\<lambda>x. real (f y * indicator (f -` {f y}) x)) has_integral
      real (f y * lmeasure (f -` {f y} \<inter> UNIV))) UNIV"
    proof(cases "f y = 0") case False
      have mea:"gmeasurable (f -` {f y})" apply(rule glmeasurable_finite)
        using assms unfolding lebesgue.simple_function_def using False by auto
      have *:"\<And>x. real (indicator (f -` {f y}) x::pinfreal) = (if x \<in> f -` {f y} then 1 else 0)" by auto
      show ?thesis unfolding real_of_pinfreal_mult[THEN sym]
        apply(rule has_integral_cmul[where 'b=real, unfolded real_scaleR_def])
        unfolding Int_UNIV_right lmeasure_gmeasure[OF mea,THEN sym]
        unfolding measure_integral_univ[OF mea] * apply(rule integrable_integral)
        unfolding gmeasurable_integrable[THEN sym] using mea .
    qed auto
  qed qed

lemma (in measure_space) positive_integral_omega:
  assumes "f \<in> borel_measurable M"
  and "positive_integral f \<noteq> \<omega>"
  shows "\<mu> (f -` {\<omega>} \<inter> space M) = 0"
proof -
  have "\<omega> * \<mu> (f -` {\<omega>} \<inter> space M) = positive_integral (\<lambda>x. \<omega> * indicator (f -` {\<omega>} \<inter> space M) x)"
    using positive_integral_cmult_indicator[OF borel_measurable_vimage, OF assms(1), of \<omega> \<omega>] by simp
  also have "\<dots> \<le> positive_integral f"
    by (auto intro!: positive_integral_mono simp: indicator_def)
  finally show ?thesis
    using assms(2) by (cases ?thesis) auto
qed

lemma (in measure_space) simple_integral_omega:
  assumes "simple_function f"
  and "simple_integral f \<noteq> \<omega>"
  shows "\<mu> (f -` {\<omega>} \<inter> space M) = 0"
proof (rule positive_integral_omega)
  show "f \<in> borel_measurable M" using assms by (auto intro: borel_measurable_simple_function)
  show "positive_integral f \<noteq> \<omega>"
    using assms by (simp add: positive_integral_eq_simple_integral)
qed

lemma bounded_realI: assumes "\<forall>x\<in>s. abs (x::real) \<le> B" shows "bounded s"
  unfolding bounded_def dist_real_def apply(rule_tac x=0 in exI)
  using assms by auto

lemma simple_function_has_integral':
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> pinfreal"
  assumes f:"lebesgue.simple_function f"
  and i: "lebesgue.simple_integral f \<noteq> \<omega>"
  shows "((\<lambda>x. real (f x)) has_integral (real (lebesgue.simple_integral f))) UNIV"
proof- let ?f = "\<lambda>x. if f x = \<omega> then 0 else f x"
  { fix x have "real (f x) = real (?f x)" by (cases "f x") auto } note * = this
  have **:"{x. f x \<noteq> ?f x} = f -` {\<omega>}" by auto
  have **:"lmeasure {x\<in>space lebesgue_space. f x \<noteq> ?f x} = 0"
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
  fixes f::"nat \<Rightarrow> 'a \<Rightarrow> pinfreal"
  assumes i: "\<And>i. f i \<in> borel_measurable M" and mono: "\<And>x. mono (\<lambda>n. f n x)"
  and lim: "\<And>x. (\<lambda>i. f i x) ----> u x"
  shows "u \<in> borel_measurable M"
  and "(\<lambda>i. positive_integral (f i)) ----> positive_integral u" (is ?ilim)
proof -
  from positive_integral_isoton[unfolded isoton_fun_expand isoton_iff_Lim_mono, of f u]
  show ?ilim using mono lim i by auto
  have "(SUP i. f i) = u" using mono lim SUP_Lim_pinfreal
    unfolding fun_eq_iff SUPR_fun_expand mono_def by auto
  moreover have "(SUP i. f i) \<in> borel_measurable M"
    using i by (rule borel_measurable_SUP)
  ultimately show "u \<in> borel_measurable M" by simp
qed

lemma positive_integral_has_integral:
  fixes f::"'a::ordered_euclidean_space => pinfreal"
  assumes f:"f \<in> borel_measurable lebesgue_space"
  and int_om:"lebesgue.positive_integral f \<noteq> \<omega>"
  and f_om:"\<forall>x. f x \<noteq> \<omega>" (* TODO: remove this *)
  shows "((\<lambda>x. real (f x)) has_integral (real (lebesgue.positive_integral f))) UNIV"
proof- let ?i = "lebesgue.positive_integral f"
  from lebesgue.borel_measurable_implies_simple_function_sequence[OF f]
  guess u .. note conjunctD2[OF this,rule_format] note u = conjunctD2[OF this(1)] this(2)
  let ?u = "\<lambda>i x. real (u i x)" and ?f = "\<lambda>x. real (f x)"
  have u_simple:"\<And>k. lebesgue.simple_integral (u k) = lebesgue.positive_integral (u k)"
    apply(subst lebesgue.positive_integral_eq_simple_integral[THEN sym,OF u(1)]) ..
    (*unfolding image_iff defer apply(rule) using u(2) by smt*)
  have int_u_le:"\<And>k. lebesgue.simple_integral (u k) \<le> lebesgue.positive_integral f"
    unfolding u_simple apply(rule lebesgue.positive_integral_mono)
    using isoton_Sup[OF u(3)] unfolding le_fun_def by auto
  have u_int_om:"\<And>i. lebesgue.simple_integral (u i) \<noteq> \<omega>"
  proof- case goal1 thus ?case using int_u_le[of i] int_om by auto qed

  note u_int = simple_function_has_integral'[OF u(1) this]
  have "(\<lambda>x. real (f x)) integrable_on UNIV \<and>
    (\<lambda>k. gintegral UNIV (\<lambda>x. real (u k x))) ----> gintegral UNIV (\<lambda>x. real (f x))"
    apply(rule monotone_convergence_increasing) apply(rule,rule,rule u_int)
  proof safe case goal1 show ?case apply(rule real_of_pinfreal_mono) using u(2,3) by auto
  next case goal2 show ?case using u(3) apply(subst lim_Real[THEN sym])
      prefer 3 apply(subst Real_real') defer apply(subst Real_real')
      using isotone_Lim[OF u(3)[unfolded isoton_fun_expand, THEN spec]] using f_om u by auto
  next case goal3
    show ?case apply(rule bounded_realI[where B="real (lebesgue.positive_integral f)"])
      apply safe apply(subst abs_of_nonneg) apply(rule integral_nonneg,rule) apply(rule u_int)
      unfolding integral_unique[OF u_int] defer apply(rule real_of_pinfreal_mono[OF _ int_u_le])
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

lemma lmeasurable_imp_borel[dest]: fixes s::"'a::ordered_euclidean_space set"
  assumes "s \<in> sets borel_space" shows "lmeasurable s"
proof- let ?S = "range (\<lambda>(a, b). {a .. (b :: 'a\<Colon>ordered_euclidean_space)})"
  have *:"?S \<subseteq> sets lebesgue_space" by auto
  have "s \<in> sigma_sets UNIV ?S" using assms
    unfolding borel_space_eq_atLeastAtMost by (simp add: sigma_def)
  thus ?thesis using lebesgue.sigma_subset[of ?S,unfolded sets_sigma,OF *]
    by auto
qed

lemma lmeasurable_open[dest]:
  assumes "open s" shows "lmeasurable s"
proof- have "s \<in> sets borel_space" using assms by auto
  thus ?thesis by auto qed

lemma continuous_on_imp_borel_measurable:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::ordered_euclidean_space"
  assumes "continuous_on UNIV f"
  shows "f \<in> borel_measurable lebesgue_space"
  apply(rule lebesgue.borel_measurableI)
  unfolding lebesgue_measurable apply(rule lmeasurable_open)
  using continuous_open_preimage[OF assms] unfolding vimage_def by auto


lemma (in measure_space) integral_monotone_convergence_pos':
  assumes i: "\<And>i. integrable (f i)" and mono: "\<And>x. mono (\<lambda>n. f n x)"
  and pos: "\<And>x i. 0 \<le> f i x"
  and lim: "\<And>x. (\<lambda>i. f i x) ----> u x"
  and ilim: "(\<lambda>i. integral (f i)) ----> x"
  shows "integrable u \<and> integral u = x"
  using integral_monotone_convergence_pos[OF assms] by auto

end
