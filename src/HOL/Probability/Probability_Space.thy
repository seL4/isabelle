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

abbreviation
  "joint_distribution X Y \<equiv> distribution (\<lambda>x. (X x, Y x))"

(*
definition probably :: "('a \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<forall>\<^sup>*" 10) where
  "probably P \<longleftrightarrow> { x. P x } \<in> events \<and> prob { x. P x } = 1"
definition possibly :: "('a \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<exists>\<^sup>*" 10) where
  "possibly P \<longleftrightarrow> { x. P x } \<in> events \<and> prob { x. P x } \<noteq> 0"
*)

definition
  "conditional_expectation X M' \<equiv> SOME f. f \<in> measurable M' borel_space \<and>
    (\<forall> g \<in> sets M'. measure_space.integral M' (\<lambda>x. f x * indicator_fn g x) =
                    measure_space.integral M' (\<lambda>x. X x * indicator_fn g x))"

definition
  "conditional_prob E M' \<equiv> conditional_expectation (indicator_fn E) M'"

lemma positive': "positive M prob"
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
by (rule additive_increasing[OF positive' additive])

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
    using abs_of_nonneg positive'[unfolded positive_def]
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
    using assms positive'[unfolded positive_def, rule_format] 
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
    using positive'[unfolded positive_def]
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

locale finite_prob_space = prob_space + finite_measure_space

lemma finite_prob_space_eq:
  "finite_prob_space M \<longleftrightarrow> finite_measure_space M \<and> measure M (space M) = 1"
  unfolding finite_prob_space_def finite_measure_space_def prob_space_def prob_space_axioms_def
  by auto

lemma (in prob_space) not_empty: "space M \<noteq> {}"
  using prob_space empty_measure by auto

lemma (in finite_prob_space) sum_over_space_eq_1: "(\<Sum>x\<in>space M. measure M {x}) = 1"
  using prob_space sum_over_space by simp

lemma (in finite_prob_space) positive_distribution: "0 \<le> distribution X x"
  unfolding distribution_def using positive sets_eq_Pow by simp

lemma (in finite_prob_space) joint_distribution_restriction_fst:
  "joint_distribution X Y A \<le> distribution X (fst ` A)"
  unfolding distribution_def
proof (safe intro!: measure_mono)
  fix x assume "x \<in> space M" and *: "(X x, Y x) \<in> A"
  show "x \<in> X -` fst ` A"
    by (auto intro!: image_eqI[OF _ *])
qed (simp_all add: sets_eq_Pow)

lemma (in finite_prob_space) joint_distribution_restriction_snd:
  "joint_distribution X Y A \<le> distribution Y (snd ` A)"
  unfolding distribution_def
proof (safe intro!: measure_mono)
  fix x assume "x \<in> space M" and *: "(X x, Y x) \<in> A"
  show "x \<in> Y -` snd ` A"
    by (auto intro!: image_eqI[OF _ *])
qed (simp_all add: sets_eq_Pow)

lemma (in finite_prob_space) distribution_order:
  shows "0 \<le> distribution X x'"
  and "(distribution X x' \<noteq> 0) \<longleftrightarrow> (0 < distribution X x')"
  and "r \<le> joint_distribution X Y {(x, y)} \<Longrightarrow> r \<le> distribution X {x}"
  and "r \<le> joint_distribution X Y {(x, y)} \<Longrightarrow> r \<le> distribution Y {y}"
  and "r < joint_distribution X Y {(x, y)} \<Longrightarrow> r < distribution X {x}"
  and "r < joint_distribution X Y {(x, y)} \<Longrightarrow> r < distribution Y {y}"
  and "distribution X {x} = 0 \<Longrightarrow> joint_distribution X Y {(x, y)} = 0"
  and "distribution Y {y} = 0 \<Longrightarrow> joint_distribution X Y {(x, y)} = 0"
  using positive_distribution[of X x']
    positive_distribution[of "\<lambda>x. (X x, Y x)" "{(x, y)}"]
    joint_distribution_restriction_fst[of X Y "{(x, y)}"]
    joint_distribution_restriction_snd[of X Y "{(x, y)}"]
  by auto

lemma (in finite_prob_space) finite_product_measure_space:
  assumes "finite s1" "finite s2"
  shows "finite_measure_space \<lparr> space = s1 \<times> s2, sets = Pow (s1 \<times> s2), measure = joint_distribution X Y\<rparr>"
    (is "finite_measure_space ?M")
proof (rule finite_Pow_additivity_sufficient)
  show "positive ?M (measure ?M)"
    unfolding positive_def using positive'[unfolded positive_def] assms sets_eq_Pow
    by (simp add: distribution_def)

  show "additive ?M (measure ?M)" unfolding additive_def
  proof safe
    fix x y
    have A: "((\<lambda>x. (X x, Y x)) -` x) \<inter> space M \<in> sets M" using assms sets_eq_Pow by auto
    have B: "((\<lambda>x. (X x, Y x)) -` y) \<inter> space M \<in> sets M" using assms sets_eq_Pow by auto
    assume "x \<inter> y = {}"
    from additive[unfolded additive_def, rule_format, OF A B] this
    show "measure ?M (x \<union> y) = measure ?M x + measure ?M y"
      apply (simp add: distribution_def)
      apply (subst Int_Un_distrib2)
      by auto
  qed

  show "finite (space ?M)"
    using assms by auto

  show "sets ?M = Pow (space ?M)"
    by simp
qed

lemma (in finite_prob_space) finite_product_measure_space_of_images:
  shows "finite_measure_space \<lparr> space = X ` space M \<times> Y ` space M,
                                sets = Pow (X ` space M \<times> Y ` space M),
                                measure = joint_distribution X Y\<rparr>"
    (is "finite_measure_space ?M")
  using finite_space by (auto intro!: finite_product_measure_space)

lemma (in finite_prob_space) finite_measure_space:
  shows "finite_measure_space \<lparr> space = X ` space M, sets = Pow (X ` space M), measure = distribution X\<rparr>"
    (is "finite_measure_space ?S")
proof (rule finite_Pow_additivity_sufficient, simp_all)
  show "finite (X ` space M)" using finite_space by simp

  show "positive ?S (distribution X)" unfolding distribution_def
    unfolding positive_def using positive'[unfolded positive_def] sets_eq_Pow by auto

  show "additive ?S (distribution X)" unfolding additive_def distribution_def
  proof (simp, safe)
    fix x y
    have x: "(X -` x) \<inter> space M \<in> sets M"
      and y: "(X -` y) \<inter> space M \<in> sets M" using sets_eq_Pow by auto
    assume "x \<inter> y = {}"
    from additive[unfolded additive_def, rule_format, OF x y] this
    have "prob (((X -` x) \<union> (X -` y)) \<inter> space M) =
      prob ((X -` x) \<inter> space M) + prob ((X -` y) \<inter> space M)"
      apply (subst Int_Un_distrib2)
      by auto
    thus "prob ((X -` x \<union> X -` y) \<inter> space M) = prob (X -` x \<inter> space M) + prob (X -` y \<inter> space M)"
      by auto
  qed
qed

lemma (in finite_prob_space) finite_prob_space_of_images:
  "finite_prob_space \<lparr> space = X ` space M, sets = Pow (X ` space M), measure = distribution X\<rparr>"
  (is "finite_prob_space ?S")
proof (simp add: finite_prob_space_eq, safe)
  show "finite_measure_space ?S" by (rule finite_measure_space)
  have "X -` X ` space M \<inter> space M = space M" by auto
  thus "distribution X (X`space M) = 1"
    by (simp add: distribution_def prob_space)
qed

lemma (in finite_prob_space) finite_product_prob_space_of_images:
  "finite_prob_space \<lparr> space = X ` space M \<times> Y ` space M, sets = Pow (X ` space M \<times> Y ` space M), 
    measure = joint_distribution X Y\<rparr>"
  (is "finite_prob_space ?S")
proof (simp add: finite_prob_space_eq, safe)
  show "finite_measure_space ?S" by (rule finite_product_measure_space_of_images)

  have "X -` X ` space M \<inter> Y -` Y ` space M \<inter> space M = space M" by auto
  thus "joint_distribution X Y (X ` space M \<times> Y ` space M) = 1"
    by (simp add: distribution_def prob_space vimage_Times comp_def)
qed

end
