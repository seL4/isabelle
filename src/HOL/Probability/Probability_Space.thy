theory Probability_Space
imports Lebesgue
begin

locale prob_space = measure_space +
  assumes prob_space: "measure M (space M) = 1"
begin

abbreviation "events \<equiv> sets M"
abbreviation "prob \<equiv> measure M"
abbreviation "prob_preserving \<equiv> measure_preserving"
abbreviation "random_variable \<equiv> \<lambda> s X. X \<in> measurable M s"
abbreviation "expectation \<equiv> integral"

definition
  "indep A B \<longleftrightarrow> A \<in> events \<and> B \<in> events \<and> prob (A \<inter> B) = prob A * prob B"

definition
  "indep_families F G \<longleftrightarrow> (\<forall> A \<in> F. \<forall> B \<in> G. indep A B)"

definition
  "distribution X = (\<lambda>s. prob ((X -` s) \<inter> (space M)))"

definition
  "probably e \<longleftrightarrow> e \<in> events \<and> prob e = 1"

definition
  "possibly e \<longleftrightarrow> e \<in> events \<and> prob e \<noteq> 0"

definition
  "joint_distribution X Y \<equiv> (\<lambda>a. prob ((\<lambda>x. (X x, Y x)) -` a \<inter> space M))"

definition
  "conditional_expectation X s \<equiv> THE f. random_variable borel_space f \<and>
    (\<forall> g \<in> s. integral (\<lambda>x. f x * indicator_fn g x) =
              integral (\<lambda>x. X x * indicator_fn g x))"

definition
  "conditional_prob e1 e2 \<equiv> conditional_expectation (indicator_fn e1) e2"

lemma positive: "positive M prob"
  unfolding positive_def using positive empty_measure by blast

lemma prob_compl:
  assumes "s \<in> events"
  shows "prob (space M - s) = 1 - prob s"
using assms
proof -
  have "prob ((space M - s) \<union> s) = prob (space M - s) + prob s"
    using assms additive[unfolded additive_def] by blast
  thus ?thesis by (simp add:Un_absorb2[OF sets_into_space[OF assms]] prob_space)
qed

lemma indep_space:
  assumes "s \<in> events"
  shows "indep (space M) s"
using assms prob_space
unfolding indep_def by auto


lemma prob_space_increasing:
  "increasing M prob"
by (rule additive_increasing[OF positive additive])

lemma prob_subadditive:
  assumes "s \<in> events" "t \<in> events"
  shows "prob (s \<union> t) \<le> prob s + prob t"
using assms
proof -
  have "prob (s \<union> t) = prob ((s - t) \<union> t)" by simp
  also have "\<dots> = prob (s - t) + prob t"
    using additive[unfolded additive_def, rule_format, of "s-t" "t"] 
      assms by blast
  also have "\<dots> \<le> prob s + prob t"
    using prob_space_increasing[unfolded increasing_def, rule_format] assms
    by auto
  finally show ?thesis by simp
qed

lemma prob_zero_union:
  assumes "s \<in> events" "t \<in> events" "prob t = 0"
  shows "prob (s \<union> t) = prob s"
using assms 
proof -
  have "prob (s \<union> t) \<le> prob s"
    using prob_subadditive[of s t] assms by auto
  moreover have "prob (s \<union> t) \<ge> prob s"
    using prob_space_increasing[unfolded increasing_def, rule_format] 
      assms by auto
  ultimately show ?thesis by simp
qed

lemma prob_eq_compl:
  assumes "s \<in> events" "t \<in> events"
  assumes "prob (space M - s) = prob (space M - t)"
  shows "prob s = prob t"
using assms prob_compl by auto

lemma prob_one_inter:
  assumes events:"s \<in> events" "t \<in> events"
  assumes "prob t = 1"
  shows "prob (s \<inter> t) = prob s"
using assms
proof -
  have "prob ((space M - s) \<union> (space M - t)) = prob (space M - s)" 
    using prob_compl[of "t"] prob_zero_union assms by auto
  then show "prob (s \<inter> t) = prob s" 
    using prob_eq_compl[of "s \<inter> t"] events by (simp only: Diff_Int) auto
qed

lemma prob_eq_bigunion_image:
  assumes "range f \<subseteq> events" "range g \<subseteq> events"
  assumes "disjoint_family f" "disjoint_family g"
  assumes "\<And> n :: nat. prob (f n) = prob (g n)"
  shows "(prob (\<Union> i. f i) = prob (\<Union> i. g i))"
using assms 
proof -
  have a: "(\<lambda> i. prob (f i)) sums (prob (\<Union> i. f i))" 
    using ca[unfolded countably_additive_def] assms by blast
  have b: "(\<lambda> i. prob (g i)) sums (prob (\<Union> i. g i))"
    using ca[unfolded countably_additive_def] assms by blast
  show ?thesis using sums_unique[OF b] sums_unique[OF a] assms by simp
qed

lemma prob_countably_subadditive: 
  assumes "range f \<subseteq> events" 
  assumes "summable (prob \<circ> f)"
  shows "prob (\<Union>i. f i) \<le> (\<Sum> i. prob (f i))"
using assms
proof -
  def f' == "\<lambda> i. f i - (\<Union> j \<in> {0 ..< i}. f j)"
  have "(\<Union> i. f' i) \<subseteq> (\<Union> i. f i)" unfolding f'_def by auto
  moreover have "(\<Union> i. f' i) \<supseteq> (\<Union> i. f i)"
  proof (rule subsetI)
    fix x assume "x \<in> (\<Union> i. f i)"
    then obtain k where "x \<in> f k" by blast
    hence k: "k \<in> {m. x \<in> f m}" by simp
    have "\<exists> l. x \<in> f l \<and> (\<forall> l' < l. x \<notin> f l')"
      using wfE_min[of "{(x, y). x < y}" "k" "{m. x \<in> f m}", 
        OF wf_less k] by auto
    thus "x \<in> (\<Union> i. f' i)" unfolding f'_def by auto
  qed
  ultimately have uf'f: "(\<Union> i. f' i) = (\<Union> i. f i)" by (rule equalityI)

  have df': "\<And> i j. i < j \<Longrightarrow> f' i \<inter> f' j = {}"
    unfolding f'_def by auto
  have "\<And> i j. i \<noteq> j \<Longrightarrow> f' i \<inter> f' j = {}"
    apply (drule iffD1[OF nat_neq_iff])
    using df' by auto
  hence df: "disjoint_family f'" unfolding disjoint_family_on_def by simp

  have rf': "\<And> i. f' i \<in> events"
  proof -
    fix i :: nat
    have "(\<Union> {f j | j. j \<in> {0 ..< i}}) = (\<Union> j \<in> {0 ..< i}. f j)" by blast
    hence "(\<Union> {f j | j. j \<in> {0 ..< i}}) \<in> events 
      \<Longrightarrow> (\<Union> j \<in> {0 ..< i}. f j) \<in> events" by auto
    thus "f' i \<in> events" 
      unfolding f'_def 
      using assms finite_union[of "{f j | j. j \<in> {0 ..< i}}"]
        Diff[of "f i" "\<Union> j \<in> {0 ..< i}. f j"] by auto
  qed
  hence uf': "(\<Union> range f') \<in> events" by auto
  
  have "\<And> i. prob (f' i) \<le> prob (f i)"
    using prob_space_increasing[unfolded increasing_def, rule_format, OF rf']
      assms rf' unfolding f'_def by blast

  hence absinc: "\<And> i. \<bar> prob (f' i) \<bar> \<le> prob (f i)"
    using abs_of_nonneg positive[unfolded positive_def]
      assms rf' by auto

  have "prob (\<Union> i. f i) = prob (\<Union> i. f' i)" using uf'f by simp

  also have "\<dots> = (\<Sum> i. prob (f' i))"
    using ca[unfolded countably_additive_def, rule_format]
    sums_unique rf' uf' df
    by auto
  
  also have "\<dots> \<le> (\<Sum> i. prob (f i))"
    using summable_le2[of "\<lambda> i. prob (f' i)" "\<lambda> i. prob (f i)", 
      rule_format, OF absinc]
      assms[unfolded o_def] by auto

  finally show ?thesis by auto
qed

lemma prob_countably_zero:
  assumes "range c \<subseteq> events"
  assumes "\<And> i. prob (c i) = 0"
  shows "(prob (\<Union> i :: nat. c i) = 0)"
  using assms
proof -
  have leq0: "0 \<le> prob (\<Union> i. c i)"
    using assms positive[unfolded positive_def, rule_format] 
    by auto

  have "prob (\<Union> i. c i) \<le> (\<Sum> i. prob (c i))"
    using prob_countably_subadditive[of c, unfolded o_def]
      assms sums_zero sums_summable by auto

  also have "\<dots> = 0"
    using assms sums_zero 
      sums_unique[of "\<lambda> i. prob (c i)" "0"] by auto

  finally show "prob (\<Union> i. c i) = 0"
    using leq0 by auto
qed

lemma indep_sym:
   "indep a b \<Longrightarrow> indep b a"
unfolding indep_def using Int_commute[of a b] by auto

lemma indep_refl:
  assumes "a \<in> events"
  shows "indep a a = (prob a = 0) \<or> (prob a = 1)"
using assms unfolding indep_def by auto

lemma prob_equiprobable_finite_unions:
  assumes "s \<in> events" 
  assumes "\<And>x. x \<in> s \<Longrightarrow> {x} \<in> events"
  assumes "finite s"
  assumes "\<And> x y. \<lbrakk>x \<in> s; y \<in> s\<rbrakk> \<Longrightarrow> (prob {x} = prob {y})"
  shows "prob s = of_nat (card s) * prob {SOME x. x \<in> s}"
using assms
proof (cases "s = {}")
  case True thus ?thesis by simp
next
  case False hence " \<exists> x. x \<in> s" by blast
  from someI_ex[OF this] assms
  have prob_some: "\<And> x. x \<in> s \<Longrightarrow> prob {x} = prob {SOME y. y \<in> s}" by blast
  have "prob s = (\<Sum> x \<in> s. prob {x})"
    using assms measure_real_sum_image by blast
  also have "\<dots> = (\<Sum> x \<in> s. prob {SOME y. y \<in> s})" using prob_some by auto
  also have "\<dots> = of_nat (card s) * prob {(SOME x. x \<in> s)}"
    using setsum_constant assms by auto
  finally show ?thesis by simp
qed

lemma prob_real_sum_image_fn:
  assumes "e \<in> events"
  assumes "\<And> x. x \<in> s \<Longrightarrow> e \<inter> f x \<in> events"
  assumes "finite s"
  assumes "\<And> x y. \<lbrakk>x \<in> s ; y \<in> s ; x \<noteq> y\<rbrakk> \<Longrightarrow> f x \<inter> f y = {}"
  assumes "space M \<subseteq> (\<Union> i \<in> s. f i)"
  shows "prob e = (\<Sum> x \<in> s. prob (e \<inter> f x))"
using assms
proof -
  let ?S = "{0 ..< card s}"
  obtain g where "g ` ?S = s \<and> inj_on g ?S"
    using ex_bij_betw_nat_finite[unfolded bij_betw_def, of s] assms by auto
  moreover hence gs: "g ` ?S = s" by simp
  ultimately have ginj: "inj_on g ?S" by simp
  let ?f' = "\<lambda> i. e \<inter> f (g i)"
  have f': "?f' \<in> ?S \<rightarrow> events"
    using gs assms by blast
  hence "\<And> i j. \<lbrakk>i \<in> ?S ; j \<in> ?S ; i \<noteq> j\<rbrakk> 
    \<Longrightarrow> ?f' i \<inter> ?f' j = {}" using assms ginj[unfolded inj_on_def] gs f' by blast
  hence df': "\<And> i j. \<lbrakk>i < card s ; j < card s ; i \<noteq> j\<rbrakk> 
    \<Longrightarrow> ?f' i \<inter> ?f' j = {}" by simp

  have "e = e \<inter> space M" using assms sets_into_space by simp
  also hence "\<dots> = e \<inter> (\<Union> x \<in> s. f x)" using assms by blast
  also have "\<dots> = (\<Union> x \<in> g ` ?S. e \<inter> f x)" using gs by simp
  also have "\<dots> = (\<Union> i \<in> ?S. ?f' i)" by simp
  finally have "prob e = prob (\<Union> i \<in> ?S. ?f' i)" by simp
  also have "\<dots> = (\<Sum> i \<in> ?S. prob (?f' i))"
    apply (subst measure_finitely_additive'')
    using f' df' assms by (auto simp: disjoint_family_on_def)
  also have "\<dots> = (\<Sum> x \<in> g ` ?S. prob (e \<inter> f x))" 
    using setsum_reindex[of g "?S" "\<lambda> x. prob (e \<inter> f x)"]
      ginj by simp
  also have "\<dots> = (\<Sum> x \<in> s. prob (e \<inter> f x))" using gs by simp
  finally show ?thesis by simp
qed

lemma distribution_prob_space:
  assumes "random_variable s X"
  shows "prob_space \<lparr>space = space s, sets = sets s, measure = distribution X\<rparr>"
using assms
proof -
  let ?N = "\<lparr>space = space s, sets = sets s, measure = distribution X\<rparr>"
  interpret s: sigma_algebra "s" using assms[unfolded measurable_def] by auto
  hence sigN: "sigma_algebra ?N" using s.sigma_algebra_extend by auto

  have pos: "\<And> e. e \<in> sets s \<Longrightarrow> distribution X e \<ge> 0"
    unfolding distribution_def
    using positive[unfolded positive_def]
    assms[unfolded measurable_def] by auto

  have cas: "countably_additive ?N (distribution X)"
  proof -
    {
      fix f :: "nat \<Rightarrow> 'c \<Rightarrow> bool"
      let ?g = "\<lambda> n. X -` f n \<inter> space M"
      assume asm: "range f \<subseteq> sets s" "UNION UNIV f \<in> sets s" "disjoint_family f"
      hence "range ?g \<subseteq> events" 
        using assms unfolding measurable_def by blast
      from ca[unfolded countably_additive_def, 
        rule_format, of ?g, OF this] countable_UN[OF this] asm
      have "(\<lambda> n. prob (?g n)) sums prob (UNION UNIV ?g)"
        unfolding disjoint_family_on_def by blast
      moreover have "(X -` (\<Union> n. f n)) = (\<Union> n. X -` f n)" by blast
      ultimately have "(\<lambda> n. distribution X (f n)) sums distribution X (UNION UNIV f)"
        unfolding distribution_def by simp
    } thus ?thesis unfolding countably_additive_def by simp
  qed

  have ds0: "distribution X {} = 0"
    unfolding distribution_def by simp

  have "X -` space s \<inter> space M = space M"
    using assms[unfolded measurable_def] by auto
  hence ds1: "distribution X (space s) = 1"
    unfolding measurable_def distribution_def using prob_space by simp

  from ds0 ds1 cas pos sigN
  show "prob_space ?N"
    unfolding prob_space_def prob_space_axioms_def
    measure_space_def measure_space_axioms_def by simp
qed

lemma distribution_lebesgue_thm1:
  assumes "random_variable s X"
  assumes "A \<in> sets s"
  shows "distribution X A = expectation (indicator_fn (X -` A \<inter> space M))"
unfolding distribution_def
using assms unfolding measurable_def
using integral_indicator_fn by auto

lemma distribution_lebesgue_thm2:
  assumes "random_variable s X" "A \<in> sets s"
  shows "distribution X A = measure_space.integral \<lparr>space = space s, sets = sets s, measure = distribution X\<rparr> (indicator_fn A)"
  (is "_ = measure_space.integral ?M _")
proof -
  interpret S: prob_space ?M using assms(1) by (rule distribution_prob_space)

  show ?thesis
    using S.integral_indicator_fn(1)
    using assms unfolding distribution_def by auto
qed

lemma finite_expectation1:
  assumes "finite (space M)" "random_variable borel_space X"
  shows "expectation X = (\<Sum> r \<in> X ` space M. r * prob (X -` {r} \<inter> space M))"
  using assms integral_finite measurable_def
  unfolding borel_measurable_def by auto

lemma finite_expectation:
  assumes "finite (space M) \<and> random_variable borel_space X"
  shows "expectation X = (\<Sum> r \<in> X ` (space M). r * distribution X {r})"
using assms unfolding distribution_def using finite_expectation1 by auto

lemma finite_marginal_product_space_POW:
  assumes "Pow (space M) = events"
  assumes "random_variable \<lparr> space = X ` (space M), sets = Pow (X ` (space M))\<rparr> X"
  assumes "random_variable \<lparr> space = Y ` (space M), sets = Pow (Y ` (space M))\<rparr> Y"
  assumes "finite (space M)"
  shows "measure_space \<lparr> space = ((X ` (space M)) \<times> (Y ` (space M))),
  sets = Pow ((X ` (space M)) \<times> (Y ` (space M))),
  measure = (\<lambda>a. prob ((\<lambda>x. (X x,Y x)) -` a \<inter> space M))\<rparr>"
  using assms
proof -
  let "?S" = "\<lparr> space = ((X ` (space M)) \<times> (Y ` (space M))), 
    sets = Pow ((X ` (space M)) \<times> (Y ` (space M)))\<rparr>"
  let "?M" = "\<lparr> space = ((X ` (space M)) \<times> (Y ` (space M))), 
    sets = Pow ((X ` (space M)) \<times> (Y ` (space M)))\<rparr>"
  have pos: "positive ?S (\<lambda>a. prob ((\<lambda>x. (X x,Y x)) -` a \<inter> space M))"
    unfolding positive_def using positive[unfolded positive_def] assms by auto
  { fix x y
    have A: "((\<lambda>x. (X x, Y x)) -` x) \<inter> space M \<in> sets M" using assms by auto
    have B: "((\<lambda>x. (X x, Y x)) -` y) \<inter> space M \<in> sets M" using assms by auto
    assume "x \<inter> y = {}"
    from additive[unfolded additive_def, rule_format, OF A B] this
    have "prob (((\<lambda>x. (X x, Y x)) -` x \<union>
      (\<lambda>x. (X x, Y x)) -` y) \<inter> space M) =
      prob ((\<lambda>x. (X x, Y x)) -` x \<inter> space M) +
      prob ((\<lambda>x. (X x, Y x)) -` y \<inter> space M)" 
      apply (subst Int_Un_distrib2)
      by auto }
  hence add: "additive ?S (\<lambda>a. prob ((\<lambda>x. (X x,Y x)) -` a \<inter> space M))"
    unfolding additive_def by auto
  interpret S: sigma_algebra "?S" 
    unfolding sigma_algebra_def algebra_def
      sigma_algebra_axioms_def by auto
  show ?thesis
     using add pos S.finite_additivity_sufficient assms by auto
qed

lemma finite_marginal_product_space_POW2:
  assumes "Pow (space M) = events"
  assumes "random_variable \<lparr>space = s1, sets = Pow s1\<rparr> X"
  assumes "random_variable \<lparr>space = s2, sets = Pow s2\<rparr> Y"
  assumes "finite (space M)"
  assumes "finite s1" "finite s2"
  shows "measure_space \<lparr> space = s1 \<times> s2, sets = Pow (s1 \<times> s2), measure = joint_distribution X Y\<rparr>"
proof -
  let "?S" = "\<lparr> space = s1 \<times> s2, sets = Pow (s1 \<times> s2) \<rparr>"
  let "?M" = "\<lparr> space = s1 \<times> s2, sets = Pow (s1 \<times> s2), measure = joint_distribution X Y \<rparr>"
  have pos: "positive ?S (joint_distribution X Y)" using positive
    unfolding positive_def joint_distribution_def using assms by auto
  { fix x y
    have A: "((\<lambda>x. (X x, Y x)) -` x) \<inter> space M \<in> sets M" using assms by auto
    have B: "((\<lambda>x. (X x, Y x)) -` y) \<inter> space M \<in> sets M" using assms by auto
    assume "x \<inter> y = {}"
    from additive[unfolded additive_def, rule_format, OF A B] this
    have "prob (((\<lambda>x. (X x, Y x)) -` x \<union>
      (\<lambda>x. (X x, Y x)) -` y) \<inter> space M) =
      prob ((\<lambda>x. (X x, Y x)) -` x \<inter> space M) +
      prob ((\<lambda>x. (X x, Y x)) -` y \<inter> space M)" 
      apply (subst Int_Un_distrib2)
      by auto }
  hence add: "additive ?S (joint_distribution X Y)"
    unfolding additive_def joint_distribution_def by auto
  interpret S: sigma_algebra "?S" 
    unfolding sigma_algebra_def algebra_def
      sigma_algebra_axioms_def by auto
  show ?thesis
     using add pos S.finite_additivity_sufficient assms by auto
qed

lemma prob_x_eq_1_imp_prob_y_eq_0:
  assumes "{x} \<in> events"
  assumes "(prob {x} = 1)"
  assumes "{y} \<in> events"
  assumes "y \<noteq> x"
  shows "prob {y} = 0"
  using prob_one_inter[of "{y}" "{x}"] assms by auto

lemma distribution_x_eq_1_imp_distribution_y_eq_0:
  assumes X: "random_variable \<lparr>space = X ` (space M), sets = Pow (X ` (space M))\<rparr> X"
  assumes "(distribution X {x} = 1)"
  assumes "y \<noteq> x"
  shows "distribution X {y} = 0"
proof -
  let ?S = "\<lparr>space = X ` (space M), sets = Pow (X ` (space M))\<rparr>"
  let ?M = "\<lparr>space = X ` (space M), sets = Pow (X ` (space M)), measure = distribution X\<rparr>"
  interpret S: prob_space ?M
    using distribution_prob_space[OF X] by auto
  { assume "{x} \<notin> sets ?M"
    hence "x \<notin> X ` space M" by auto
    hence "X -` {x} \<inter> space M = {}" by auto
    hence "distribution X {x} = 0" unfolding distribution_def by auto
    hence "False" using assms by auto }
  hence x: "{x} \<in> sets ?M" by auto
  { assume "{y} \<notin> sets ?M"
    hence "y \<notin> X ` space M" by auto
    hence "X -` {y} \<inter> space M = {}" by auto
    hence "distribution X {y} = 0" unfolding distribution_def by auto }
  moreover
  { assume "{y} \<in> sets ?M"
    hence "distribution X {y} = 0" using assms S.prob_x_eq_1_imp_prob_y_eq_0[OF x] by auto }
  ultimately show ?thesis by auto
qed

end

end
