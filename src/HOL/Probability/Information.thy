theory Information
imports Probability_Space Product_Measure
begin

lemma pos_neg_part_abs:
  fixes f :: "'a \<Rightarrow> real"
  shows "pos_part f x + neg_part f x = \<bar>f x\<bar>"
unfolding real_abs_def pos_part_def neg_part_def by auto

lemma pos_part_abs:
  fixes f :: "'a \<Rightarrow> real"
  shows "pos_part (\<lambda> x. \<bar>f x\<bar>) y = \<bar>f y\<bar>"
unfolding pos_part_def real_abs_def by auto

lemma neg_part_abs:
  fixes f :: "'a \<Rightarrow> real"
  shows "neg_part (\<lambda> x. \<bar>f x\<bar>) y = 0"
unfolding neg_part_def real_abs_def by auto

lemma (in measure_space) int_abs:
  assumes "integrable f"
  shows "integrable (\<lambda> x. \<bar>f x\<bar>)"
using assms
proof -
  from assms obtain p q where pq: "p \<in> nnfis (pos_part f)" "q \<in> nnfis (neg_part f)"
    unfolding integrable_def by auto
  hence "p + q \<in> nnfis (\<lambda> x. pos_part f x + neg_part f x)"
    using nnfis_add by auto
  hence "p + q \<in> nnfis (\<lambda> x. \<bar>f x\<bar>)" using pos_neg_part_abs[of f] by simp
  thus ?thesis unfolding integrable_def
    using ext[OF pos_part_abs[of f], of "\<lambda> y. y"]
      ext[OF neg_part_abs[of f], of "\<lambda> y. y"]
    using nnfis_0 by auto
qed

lemma (in measure_space) measure_mono:
  assumes "a \<subseteq> b" "a \<in> sets M" "b \<in> sets M"
  shows "measure M a \<le> measure M b"
proof -
  have "b = a \<union> (b - a)" using assms by auto
  moreover have "{} = a \<inter> (b - a)" by auto
  ultimately have "measure M b = measure M a + measure M (b - a)"
    using measure_additive[of a "b - a"] local.Diff[of b a] assms by auto
  moreover have "measure M (b - a) \<ge> 0" using positive assms by auto
  ultimately show "measure M a \<le> measure M b" by auto
qed

lemma (in measure_space) integral_0:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable f" "integral f = 0" "nonneg f" and borel: "f \<in> borel_measurable M"
  shows "measure M ({x. f x \<noteq> 0} \<inter> space M) = 0"
proof -
  have "{x. f x \<noteq> 0} = {x. \<bar>f x\<bar> > 0}" by auto
  moreover
  { fix y assume "y \<in> {x. \<bar> f x \<bar> > 0}"
    hence "\<bar> f y \<bar> > 0" by auto
    hence "\<exists> n. \<bar>f y\<bar> \<ge> inverse (real (Suc n))"
      using ex_inverse_of_nat_Suc_less[of "\<bar>f y\<bar>"] less_imp_le unfolding real_of_nat_def by auto
    hence "y \<in> (\<Union> n. {x. \<bar>f x\<bar> \<ge> inverse (real (Suc n))})"
      by auto }
  moreover
  { fix y assume "y \<in> (\<Union> n. {x. \<bar>f x\<bar> \<ge> inverse (real (Suc n))})"
    then obtain n where n: "y \<in> {x. \<bar>f x\<bar> \<ge> inverse (real (Suc n))}" by auto
    hence "\<bar>f y\<bar> \<ge> inverse (real (Suc n))" by auto
    hence "\<bar>f y\<bar> > 0"
      using real_of_nat_Suc_gt_zero
        positive_imp_inverse_positive[of "real_of_nat (Suc n)"] by fastsimp
    hence "y \<in> {x. \<bar>f x\<bar> > 0}" by auto }
  ultimately have fneq0_UN: "{x. f x \<noteq> 0} = (\<Union> n. {x. \<bar>f x\<bar> \<ge> inverse (real (Suc n))})"
    by blast
  { fix n
    have int_one: "integrable (\<lambda> x. \<bar>f x\<bar> ^ 1)" using int_abs assms by auto
    have "measure M (f -` {inverse (real (Suc n))..} \<inter> space M)
           \<le> integral (\<lambda> x. \<bar>f x\<bar> ^ 1) / (inverse (real (Suc n)) ^ 1)"
      using markov_ineq[OF `integrable f` _ int_one] real_of_nat_Suc_gt_zero by auto
    hence le0: "measure M (f -` {inverse (real (Suc n))..} \<inter> space M) \<le> 0"
      using assms unfolding nonneg_def by auto
    have "{x. f x \<ge> inverse (real (Suc n))} \<inter> space M \<in> sets M"
      apply (subst Int_commute) unfolding Int_def
      using borel[unfolded borel_measurable_ge_iff] by simp
    hence m0: "measure M ({x. f x \<ge> inverse (real (Suc n))} \<inter> space M) = 0 \<and>
      {x. f x \<ge> inverse (real (Suc n))} \<inter> space M \<in> sets M"
      using positive le0 unfolding atLeast_def by fastsimp }
  moreover hence "range (\<lambda> n. {x. f x \<ge> inverse (real (Suc n))} \<inter> space M) \<subseteq> sets M"
    by auto
  moreover
  { fix n
    have "inverse (real (Suc n)) \<ge> inverse (real (Suc (Suc n)))"
      using less_imp_inverse_less real_of_nat_Suc_gt_zero[of n] by fastsimp
    hence "\<And> x. f x \<ge> inverse (real (Suc n)) \<Longrightarrow> f x \<ge> inverse (real (Suc (Suc n)))" by (rule order_trans)
    hence "{x. f x \<ge> inverse (real (Suc n))} \<inter> space M
         \<subseteq> {x. f x \<ge> inverse (real (Suc (Suc n)))} \<inter> space M" by auto }
  ultimately have "(\<lambda> x. 0) ----> measure M (\<Union> n. {x. f x \<ge> inverse (real (Suc n))} \<inter> space M)"
    using monotone_convergence[of "\<lambda> n. {x. f x \<ge> inverse (real (Suc n))} \<inter> space M"]
    unfolding o_def by (simp del: of_nat_Suc)
  hence "measure M (\<Union> n. {x. f x \<ge> inverse (real (Suc n))} \<inter> space M) = 0"
    using LIMSEQ_const[of 0] LIMSEQ_unique by simp
  hence "measure M ((\<Union> n. {x. \<bar>f x\<bar> \<ge> inverse (real (Suc n))}) \<inter> space M) = 0"
    using assms unfolding nonneg_def by auto
  thus "measure M ({x. f x \<noteq> 0} \<inter> space M) = 0" using fneq0_UN by simp
qed

definition
  "KL_divergence b M u v =
    measure_space.integral (M\<lparr>measure := u\<rparr>)
                           (\<lambda>x. log b ((measure_space.RN_deriv (M \<lparr>measure := v\<rparr> ) u) x))"

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

lemma (in finite_prob_space) finite_prob_space:
  "finite_prob_space \<lparr> space = X ` space M, sets = Pow (X ` space M), measure = distribution X\<rparr>"
  (is "finite_prob_space ?S")
  unfolding finite_prob_space_def prob_space_def prob_space_axioms_def
proof safe
  show "finite_measure_space ?S" by (rule finite_measure_space)
  thus "measure_space ?S" by (simp add: finite_measure_space_def)

  have "X -` X ` space M \<inter> space M = space M" by auto
  thus "measure ?S (space ?S) = 1"
    by (simp add: distribution_def prob_space)
qed

lemma (in finite_prob_space) finite_measure_space_image_prod:
  "finite_measure_space \<lparr>space = X ` space M \<times> Y ` space M,
    sets = Pow (X ` space M \<times> Y ` space M), measure_space.measure = distribution (\<lambda>x. (X x, Y x))\<rparr>"
  (is "finite_measure_space ?Z")
proof (rule finite_Pow_additivity_sufficient, simp_all)
  show "finite (X ` space M \<times> Y ` space M)" using finite_space by simp

  let ?d = "distribution (\<lambda>x. (X x, Y x))"

  show "positive ?Z ?d"
    using sets_eq_Pow by (auto simp: positive_def distribution_def intro!: positive)

  show "additive ?Z ?d" unfolding additive_def
  proof safe
    fix x y assume "x \<in> sets ?Z" and "y \<in> sets ?Z"
    assume "x \<inter> y = {}"
    thus "?d (x \<union> y) = ?d x + ?d y"
      apply (simp add: distribution_def)
      apply (subst measure_additive[unfolded sets_eq_Pow, simplified])
      by (auto simp: Un_Int_distrib Un_Int_distrib2 intro!: arg_cong[where f=prob])
  qed
qed

definition (in prob_space)
  "mutual_information b s1 s2 X Y \<equiv>
    let prod_space =
      prod_measure_space (\<lparr>space = space s1, sets = sets s1, measure = distribution X\<rparr>)
                         (\<lparr>space = space s2, sets = sets s2, measure = distribution Y\<rparr>)
    in
      KL_divergence b prod_space (joint_distribution X Y) (measure prod_space)"

abbreviation (in finite_prob_space)
  finite_mutual_information ("\<I>\<^bsub>_\<^esub>'(_ ; _')") where
  "\<I>\<^bsub>b\<^esub>(X ; Y) \<equiv> mutual_information b
    \<lparr> space = X`space M, sets = Pow (X`space M) \<rparr>
    \<lparr> space = Y`space M, sets = Pow (Y`space M) \<rparr> X Y"

abbreviation (in finite_prob_space)
  finite_mutual_information_2 :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> real" ("\<I>'(_ ; _')") where
  "\<I>(X ; Y) \<equiv> \<I>\<^bsub>2\<^esub>(X ; Y)"

lemma (in prob_space) mutual_information_cong:
  assumes [simp]: "space S1 = space S3" "sets S1 = sets S3"
    "space S2 = space S4" "sets S2 = sets S4"
  shows "mutual_information b S1 S2 X Y = mutual_information b S3 S4 X Y"
  unfolding mutual_information_def by simp

lemma (in prob_space) joint_distribution:
  "joint_distribution X Y = distribution (\<lambda>x. (X x, Y x))"
  unfolding joint_distribution_def_raw distribution_def_raw ..

lemma (in finite_prob_space) finite_mutual_information_reduce:
  "\<I>\<^bsub>b\<^esub>(X;Y) = (\<Sum> (x,y) \<in> X ` space M \<times> Y ` space M.
    distribution (\<lambda>x. (X x, Y x)) {(x,y)} * log b (distribution (\<lambda>x. (X x, Y x)) {(x,y)} /
                                                   (distribution X {x} * distribution Y {y})))"
  (is "_ = setsum ?log ?prod")
  unfolding Let_def mutual_information_def KL_divergence_def
proof (subst finite_measure_space.integral_finite_singleton, simp_all add: joint_distribution)
  let ?X = "\<lparr>space = X ` space M, sets = Pow (X ` space M), measure_space.measure = distribution X\<rparr>"
  let ?Y = "\<lparr>space = Y ` space M, sets = Pow (Y ` space M), measure_space.measure = distribution Y\<rparr>"
  let ?P = "prod_measure_space ?X ?Y"

  interpret X: finite_measure_space "?X" by (rule finite_measure_space)
  moreover interpret Y: finite_measure_space "?Y" by (rule finite_measure_space)
  ultimately have ms_X: "measure_space ?X" and ms_Y: "measure_space ?Y" by unfold_locales

  interpret P: finite_measure_space "?P" by (rule finite_measure_space_finite_prod_measure) (fact+)

  let ?P' = "measure_update (\<lambda>_. distribution (\<lambda>x. (X x, Y x))) ?P"
  from finite_measure_space_image_prod[of X Y]
    sigma_prod_sets_finite[OF X.finite_space Y.finite_space]
  show "finite_measure_space ?P'"
    by (simp add: X.sets_eq_Pow Y.sets_eq_Pow joint_distribution finite_measure_space_def prod_measure_space_def)

  show "(\<Sum>x \<in> space ?P. log b (measure_space.RN_deriv ?P (distribution (\<lambda>x. (X x, Y x))) x) * distribution (\<lambda>x. (X x, Y x)) {x})
    = setsum ?log ?prod"
  proof (rule setsum_cong)
    show "space ?P = ?prod" unfolding prod_measure_space_def by simp
  next
    fix x assume x: "x \<in> X ` space M \<times> Y ` space M"
    then obtain d e where x_Pair: "x = (d, e)"
      and d: "d \<in> X ` space M"
      and e: "e \<in> Y ` space M" by auto

    { fix x assume m_0: "measure ?P {x} = 0"
      have "distribution (\<lambda>x. (X x, Y x)) {x} = 0"
      proof (cases x)
        case (Pair a b)
        hence "(\<lambda>x. (X x, Y x)) -` {x} \<inter> space M = (X -` {a} \<inter> space M) \<inter> (Y -` {b} \<inter> space M)"
          and x_prod: "{x} = {a} \<times> {b}" by auto

        let ?PROD = "(\<lambda>x. (X x, Y x)) -` {x} \<inter> space M"

        show ?thesis
        proof (cases "{a} \<subseteq> X ` space M \<and> {b} \<subseteq> Y ` space M")
          case False
          hence "?PROD = {}"
            unfolding Pair by auto
          thus ?thesis by (auto simp: distribution_def)
        next
          have [intro]: "prob ?PROD \<le> 0 \<Longrightarrow> prob ?PROD = 0"
            using sets_eq_Pow by (auto intro!: positive real_le_antisym[of _ 0])

          case True
          with prod_measure_times[OF ms_X ms_Y, simplified, of "{a}" "{b}"]
          have "prob (X -` {a} \<inter> space M) = 0 \<or> prob (Y -` {b} \<inter> space M) = 0" (is "?X_0 \<or> ?Y_0") using m_0
            by (simp add: prod_measure_space_def distribution_def Pair)
          thus ?thesis
          proof (rule disjE)
            assume ?X_0
            have "prob ?PROD \<le> prob (X -` {a} \<inter> space M)"
              using sets_eq_Pow Pair by (auto intro!: measure_mono)
            thus ?thesis using `?X_0` by (auto simp: distribution_def)
          next
            assume ?Y_0
            have "prob ?PROD \<le> prob (Y -` {b} \<inter> space M)"
              using sets_eq_Pow Pair by (auto intro!: measure_mono)
            thus ?thesis using `?Y_0` by (auto simp: distribution_def)
          qed
        qed
      qed }
    note measure_zero_joint_distribution = this

    show "log b (measure_space.RN_deriv ?P (distribution (\<lambda>x. (X x, Y x))) x) * distribution (\<lambda>x. (X x, Y x)) {x} = ?log x"
    apply (cases "distribution (\<lambda>x. (X x, Y x)) {x} \<noteq> 0")
    apply (subst P.RN_deriv_finite_singleton)
    proof (simp_all add: x_Pair)
      from `finite_measure_space ?P'` show "measure_space ?P'" by (simp add: finite_measure_space_def)
    next
      fix x assume m_0: "measure ?P {x} = 0" thus "distribution (\<lambda>x. (X x, Y x)) {x} = 0" by fact
    next
      show "(d,e) \<in> space ?P" unfolding prod_measure_space_def using x x_Pair by simp
    next
      assume jd_0: "distribution (\<lambda>x. (X x, Y x)) {(d, e)} \<noteq> 0"
      show "measure ?P {(d,e)} \<noteq> 0"
      proof
        assume "measure ?P {(d,e)} = 0"
        from measure_zero_joint_distribution[OF this] jd_0
        show False by simp
      qed
    next
      assume jd_0: "distribution (\<lambda>x. (X x, Y x)) {(d, e)} \<noteq> 0"
      with prod_measure_times[OF ms_X ms_Y, simplified, of "{d}" "{e}"] d
      show "log b (distribution (\<lambda>x. (X x, Y x)) {(d, e)} / measure ?P {(d, e)}) =
        log b (distribution (\<lambda>x. (X x, Y x)) {(d, e)} / (distribution X {d} * distribution Y {e}))"
        by (auto intro!: arg_cong[where f="log b"] simp: prod_measure_space_def)
    qed
  qed
qed

lemma (in finite_prob_space) distribution_log_split:
  assumes "1 < b"
  shows
  "distribution (\<lambda>x. (X x, Z x)) {(X x, z)} * log b (distribution (\<lambda>x. (X x, Z x)) {(X x, z)} /
                                                     (distribution X {X x} * distribution Z {z})) =
   distribution (\<lambda>x. (X x, Z x)) {(X x, z)} * log b (distribution (\<lambda>x. (X x, Z x)) {(X x, z)} /
                                                     distribution Z {z}) -
   distribution (\<lambda>x. (X x, Z x)) {(X x, z)} * log b (distribution X {X x})"
  (is "?lhs = ?rhs")
proof (cases "distribution (\<lambda>x. (X x, Z x)) {(X x, z)} = 0")
  case True thus ?thesis by simp
next
  case False

  let ?dZ = "distribution Z"
  let ?dX = "distribution X"
  let ?dXZ = "distribution (\<lambda>x. (X x, Z x))"

  have dist_nneg: "\<And>x X. 0 \<le> distribution X x"
    unfolding distribution_def using sets_eq_Pow by (auto intro: positive)

  have "?lhs = ?dXZ {(X x, z)} * (log b (?dXZ {(X x, z)} / ?dZ {z}) - log b (?dX {X x}))"
  proof -
    have pos_dXZ: "0 < ?dXZ {(X x, z)}"
      using False dist_nneg[of "\<lambda>x. (X x, Z x)" "{(X x, z)}"] by auto
    moreover
    have "((\<lambda>x. (X x, Z x)) -` {(X x, z)}) \<inter> space M \<subseteq> (X -` {X x}) \<inter> space M" by auto
    hence "?dXZ {(X x, z)} \<le> ?dX {X x}"
      unfolding distribution_def
      by (rule measure_mono) (simp_all add: sets_eq_Pow)
    with pos_dXZ have "0 < ?dX {X x}" by (rule less_le_trans)
    moreover
    have "((\<lambda>x. (X x, Z x)) -` {(X x, z)}) \<inter> space M \<subseteq> (Z -` {z}) \<inter> space M" by auto
    hence "?dXZ {(X x, z)} \<le> ?dZ {z}"
      unfolding distribution_def
      by (rule measure_mono) (simp_all add: sets_eq_Pow)
    with pos_dXZ have "0 < ?dZ {z}" by (rule less_le_trans)
    moreover have "0 < b" by (rule less_trans[OF _ `1 < b`]) simp
    moreover have "b \<noteq> 1" by (rule ccontr) (insert `1 < b`, simp)
    ultimately show ?thesis
      using pos_dXZ
      apply (subst (2) mult_commute)
      apply (subst divide_divide_eq_left[symmetric])
      apply (subst log_divide)
      by (auto intro: divide_pos_pos)
  qed
  also have "... = ?rhs"
    by (simp add: field_simps)
  finally show ?thesis .
qed

lemma (in finite_prob_space) finite_mutual_information_reduce_prod:
  "mutual_information b
    \<lparr> space = X ` space M, sets = Pow (X ` space M) \<rparr>
    \<lparr> space = Y ` space M \<times> Z ` space M, sets = Pow (Y ` space M \<times> Z ` space M) \<rparr>
    X (\<lambda>x. (Y x,Z x)) =
    (\<Sum> (x, y, z) \<in> X`space M \<times> Y`space M \<times> Z`space M.
      distribution (\<lambda>x. (X x, Y x,Z x)) {(x, y, z)} *
      log b (distribution (\<lambda>x. (X x, Y x,Z x)) {(x, y, z)} /
              (distribution X {x} * distribution (\<lambda>x. (Y x,Z x)) {(y,z)})))" (is "_ = setsum ?log ?space")
  unfolding Let_def mutual_information_def KL_divergence_def using finite_space
proof (subst finite_measure_space.integral_finite_singleton,
       simp_all add: prod_measure_space_def sigma_prod_sets_finite joint_distribution)
  let ?sets = "Pow (X ` space M \<times> Y ` space M \<times> Z ` space M)"
    and ?measure = "distribution (\<lambda>x. (X x, Y x, Z x))"
  let ?P = "\<lparr> space = ?space, sets = ?sets, measure = ?measure\<rparr>"

  show "finite_measure_space ?P"
  proof (rule finite_Pow_additivity_sufficient, simp_all)
    show "finite ?space" using finite_space by auto

    show "positive ?P ?measure"
      using sets_eq_Pow by (auto simp: positive_def distribution_def intro!: positive)

    show "additive ?P ?measure"
    proof (simp add: additive_def distribution_def, safe)
      fix x y assume "x \<subseteq> ?space" and "y \<subseteq> ?space"
      assume "x \<inter> y = {}"
      thus "prob (((\<lambda>x. (X x, Y x, Z x)) -` x \<union> (\<lambda>x. (X x, Y x, Z x)) -` y) \<inter> space M) =
            prob ((\<lambda>x. (X x, Y x, Z x)) -` x \<inter> space M) + prob ((\<lambda>x. (X x, Y x, Z x)) -` y \<inter> space M)"
        apply (subst measure_additive[unfolded sets_eq_Pow, simplified])
        by (auto simp: Un_Int_distrib Un_Int_distrib2 intro!: arg_cong[where f=prob])
    qed
  qed

  let ?X = "\<lparr>space = X ` space M, sets = Pow (X ` space M), measure = distribution X\<rparr>"
  and ?YZ = "\<lparr>space = Y ` space M \<times> Z ` space M, sets = Pow (Y ` space M \<times> Z ` space M), measure = distribution (\<lambda>x. (Y x, Z x))\<rparr>"
  let ?u = "prod_measure ?X ?YZ"

  from finite_measure_space[of X] finite_measure_space_image_prod[of Y Z]
  have ms_X: "measure_space ?X" and ms_YZ: "measure_space ?YZ"
    by (simp_all add: finite_measure_space_def)

  show "(\<Sum>x \<in> ?space. log b (measure_space.RN_deriv \<lparr>space=?space, sets=?sets, measure=?u\<rparr>
    (distribution (\<lambda>x. (X x, Y x, Z x))) x) * distribution (\<lambda>x. (X x, Y x, Z x)) {x})
    = setsum ?log ?space"
  proof (rule setsum_cong)
    fix x assume x: "x \<in> ?space"
    then obtain d e f where x_Pair: "x = (d, e, f)"
      and d: "d \<in> X ` space M"
      and e: "e \<in> Y ` space M"
      and f: "f \<in> Z ` space M" by auto

    { fix x assume m_0: "?u {x} = 0"

      let ?PROD = "(\<lambda>x. (X x, Y x, Z x)) -` {x} \<inter> space M"
      obtain a b c where Pair: "x = (a, b, c)" by (cases x)
      hence "?PROD = (X -` {a} \<inter> space M) \<inter> ((\<lambda>x. (Y x, Z x)) -` {(b, c)} \<inter> space M)"
        and x_prod: "{x} = {a} \<times> {(b, c)}" by auto

      have "distribution (\<lambda>x. (X x, Y x, Z x)) {x} = 0"
      proof (cases "{a} \<subseteq> X ` space M")
        case False
        hence "?PROD = {}"
          unfolding Pair by auto
        thus ?thesis by (auto simp: distribution_def)
      next
        have [intro]: "prob ?PROD \<le> 0 \<Longrightarrow> prob ?PROD = 0"
          using sets_eq_Pow by (auto intro!: positive real_le_antisym[of _ 0])

        case True
        with prod_measure_times[OF ms_X ms_YZ, simplified, of "{a}" "{(b,c)}"]
        have "prob (X -` {a} \<inter> space M) = 0 \<or> prob ((\<lambda>x. (Y x, Z x)) -` {(b, c)} \<inter> space M) = 0"
          (is "prob ?X = 0 \<or> prob ?Y = 0") using m_0
          by (simp add: prod_measure_space_def distribution_def Pair)
        thus ?thesis
        proof (rule disjE)
          assume "prob ?X = 0"
          have "prob ?PROD \<le> prob ?X"
            using sets_eq_Pow Pair by (auto intro!: measure_mono)
          thus ?thesis using `prob ?X = 0` by (auto simp: distribution_def)
        next
          assume "prob ?Y = 0"
          have "prob ?PROD \<le> prob ?Y"
            using sets_eq_Pow Pair by (auto intro!: measure_mono)
          thus ?thesis using `prob ?Y = 0` by (auto simp: distribution_def)
        qed
      qed }
    note measure_zero_joint_distribution = this

    from x_Pair d e f finite_space
    show "log b (measure_space.RN_deriv \<lparr>space=?space, sets=?sets, measure=?u\<rparr>
      (distribution (\<lambda>x. (X x, Y x, Z x))) x) * distribution (\<lambda>x. (X x, Y x, Z x)) {x} = ?log x"
    apply (cases "distribution (\<lambda>x. (X x, Y x, Z x)) {x} \<noteq> 0")
    apply (subst finite_measure_space.RN_deriv_finite_singleton)
    proof simp_all
      show "measure_space ?P" using `finite_measure_space ?P` by (simp add: finite_measure_space_def)

      from finite_measure_space_finite_prod_measure[OF finite_measure_space[of X]
        finite_measure_space_image_prod[of Y Z]] finite_space
      show "finite_measure_space \<lparr>space=?space, sets=?sets, measure=?u\<rparr>"
        by (simp add: prod_measure_space_def sigma_prod_sets_finite)
    next
      fix x assume "?u {x} = 0" thus "distribution (\<lambda>x. (X x, Y x, Z x)) {x} = 0" by fact
    next
      assume jd_0: "distribution (\<lambda>x. (X x, Y x, Z x)) {(d, e, f)} \<noteq> 0"
      show "?u {(d,e,f)} \<noteq> 0"
      proof
        assume "?u {(d, e, f)} = 0"
        from measure_zero_joint_distribution[OF this] jd_0
        show False by simp
      qed
    next
      assume jd_0: "distribution (\<lambda>x. (X x, Y x, Z x)) {(d, e, f)} \<noteq> 0"
      with prod_measure_times[OF ms_X ms_YZ, simplified, of "{d}" "{(e,f)}"] d
      show "log b (distribution (\<lambda>x. (X x, Y x, Z x)) {(d, e, f)} / ?u {(d, e, f)}) =
        log b (distribution (\<lambda>x. (X x, Y x, Z x)) {(d, e, f)} / (distribution X {d} * distribution (\<lambda>x. (Y x, Z x)) {(e,f)}))"
        by (auto intro!: arg_cong[where f="log b"] simp: prod_measure_space_def)
    qed
  qed simp
qed

definition (in prob_space)
  "entropy b s X = mutual_information b s s X X"

abbreviation (in finite_prob_space)
  finite_entropy ("\<H>\<^bsub>_\<^esub>'(_')") where
  "\<H>\<^bsub>b\<^esub>(X) \<equiv> entropy b \<lparr> space = X`space M, sets = Pow (X`space M) \<rparr> X"

abbreviation (in finite_prob_space)
  finite_entropy_2 ("\<H>'(_')") where
  "\<H>(X) \<equiv> \<H>\<^bsub>2\<^esub>(X)"

lemma (in finite_prob_space) finite_entropy_reduce:
  assumes "1 < b"
  shows "\<H>\<^bsub>b\<^esub>(X) = -(\<Sum> x \<in> X ` space M. distribution X {x} * log b (distribution X {x}))"
proof -
  have fin: "finite (X ` space M)" using finite_space by simp

  have If_mult_distr: "\<And>A B C D. If A B C * D = If A (B * D) (C * D)" by auto

  { fix x y
    have "(\<lambda>x. (X x, X x)) -` {(x, y)} = (if x = y then X -` {x} else {})" by auto
    hence "distribution (\<lambda>x. (X x, X x))  {(x,y)} = (if x = y then distribution X {x} else 0)"
      unfolding distribution_def by auto }
  moreover
  have "\<And>x. 0 \<le> distribution X x"
    unfolding distribution_def using finite_space sets_eq_Pow by (auto intro: positive)
  hence "\<And>x. distribution X x \<noteq> 0 \<Longrightarrow> 0 < distribution X x" by (auto simp: le_less)
  ultimately
  show ?thesis using `1 < b`
    by (auto intro!: setsum_cong
      simp: log_inverse If_mult_distr setsum_cases[OF fin] inverse_eq_divide[symmetric]
        entropy_def setsum_negf[symmetric] joint_distribution finite_mutual_information_reduce
        setsum_cartesian_product[symmetric])
qed

lemma log_inj: assumes "1 < b" shows "inj_on (log b) {0 <..}"
proof (rule inj_onI, simp)
  fix x y assume pos: "0 < x" "0 < y" and *: "log b x = log b y"
  show "x = y"
  proof (cases rule: linorder_cases)
    assume "x < y" hence "log b x < log b y"
      using log_less_cancel_iff[OF `1 < b`] pos by simp
    thus ?thesis using * by simp
  next
    assume "y < x" hence "log b y < log b x"
      using log_less_cancel_iff[OF `1 < b`] pos by simp
    thus ?thesis using * by simp
  qed simp
qed

definition (in prob_space)
  "conditional_mutual_information b s1 s2 s3 X Y Z \<equiv>
    let prod_space =
      prod_measure_space \<lparr>space = space s2, sets = sets s2, measure = distribution Y\<rparr>
                         \<lparr>space = space s3, sets = sets s3, measure = distribution Z\<rparr>
    in
      mutual_information b s1 prod_space X (\<lambda>x. (Y x, Z x)) -
      mutual_information b s1 s3 X Z"

abbreviation (in finite_prob_space)
  finite_conditional_mutual_information ("\<I>\<^bsub>_\<^esub>'( _ ; _ | _ ')") where
  "\<I>\<^bsub>b\<^esub>(X ; Y | Z) \<equiv> conditional_mutual_information b
    \<lparr> space = X`space M, sets = Pow (X`space M) \<rparr>
    \<lparr> space = Y`space M, sets = Pow (Y`space M) \<rparr>
    \<lparr> space = Z`space M, sets = Pow (Z`space M) \<rparr>
    X Y Z"

abbreviation (in finite_prob_space)
  finite_conditional_mutual_information_2 ("\<I>'( _ ; _ | _ ')") where
  "\<I>(X ; Y | Z) \<equiv> \<I>\<^bsub>2\<^esub>(X ; Y | Z)"

lemma image_pair_eq_Sigma:
  "(\<lambda>x. (f x, g x)) ` A = Sigma (f ` A) (\<lambda>x. g ` (f -` {x} \<inter> A))"
proof (safe intro!: imageI vimageI, simp_all)
  fix a b assume *: "a \<in> A" "b \<in> A" and eq: "f a = f b"
  show "(f b, g a) \<in> (\<lambda>x. (f x, g x)) ` A" unfolding eq[symmetric]
    using * by auto
qed

lemma inj_on_swap: "inj_on (\<lambda>(x,y). (y,x)) A" by (auto intro!: inj_onI)

lemma (in finite_prob_space) finite_conditional_mutual_information_reduce:
  assumes "1 < b"
  shows "\<I>\<^bsub>b\<^esub>(X ; Y | Z) =
	- (\<Sum> (x, z) \<in> (X ` space M \<times> Z ` space M).
             distribution (\<lambda>x. (X x, Z x)) {(x,z)} * log b (distribution (\<lambda>x. (X x, Z x)) {(x,z)} / distribution Z {z}))
	+ (\<Sum> (x, y, z) \<in> (X ` space M \<times> (\<lambda>x. (Y x, Z x)) ` space M).
             distribution (\<lambda>x. (X x, Y x, Z x)) {(x, y, z)} *
             log b (distribution (\<lambda>x. (X x, Y x, Z x)) {(x, y, z)}/
             distribution (\<lambda>x. (Y x, Z x)) {(y, z)}))" (is "_ = ?rhs")
unfolding conditional_mutual_information_def Let_def using finite_space
apply (simp add: prod_measure_space_def sigma_prod_sets_finite)
apply (subst mutual_information_cong[of _ "\<lparr>space = X ` space M, sets = Pow (X ` space M)\<rparr>"
  _ "\<lparr>space = Y ` space M \<times> Z ` space M, sets = Pow (Y ` space M \<times> Z ` space M)\<rparr>"], simp_all)
apply (subst finite_mutual_information_reduce_prod, simp_all)
apply (subst finite_mutual_information_reduce, simp_all)
proof -
  let ?dXYZ = "distribution (\<lambda>x. (X x, Y x, Z x))"
  let ?dXZ = "distribution (\<lambda>x. (X x, Z x))"
  let ?dYZ = "distribution (\<lambda>x. (Y x, Z x))"
  let ?dX = "distribution X"
  let ?dY = "distribution Y"
  let ?dZ = "distribution Z"

  have If_mult_distr: "\<And>A B C D. If A B C * D = If A (B * D) (C * D)" by auto
  { fix x y
    have "(\<lambda>x. (X x, Y x, Z x)) -` {(X x, y)} \<inter> space M =
      (if y \<in> (\<lambda>x. (Y x, Z x)) ` space M then (\<lambda>x. (X x, Y x, Z x)) -` {(X x, y)} \<inter> space M else {})" by auto
    hence "?dXYZ {(X x, y)} = (if y \<in> (\<lambda>x. (Y x, Z x)) ` space M then ?dXYZ {(X x, y)} else 0)"
      unfolding distribution_def by auto }
  note split_measure = this

  have sets: "Y ` space M \<times> Z ` space M \<inter> (\<lambda>x. (Y x, Z x)) ` space M = (\<lambda>x. (Y x, Z x)) ` space M" by auto

  have cong: "\<And>A B C D. \<lbrakk> A = C ; B = D \<rbrakk> \<Longrightarrow> A + B = C + D" by auto

  { fix A f have "setsum f A = setsum (\<lambda>(x, y). f (y, x)) ((\<lambda>(x, y). (y, x)) ` A)"
    using setsum_reindex[OF inj_on_swap, of "\<lambda>(x, y). f (y, x)" A] by (simp add: split_twice) }
  note setsum_reindex_swap = this

  { fix A B f assume *: "finite A" "\<forall>x\<in>A. finite (B x)"
    have "(\<Sum>x\<in>Sigma A B. f x) = (\<Sum>x\<in>A. setsum (\<lambda>y. f (x, y)) (B x))"
      unfolding setsum_Sigma[OF *] by simp }
  note setsum_Sigma = this

  { fix x
    have "(\<Sum>z\<in>Z ` space M. ?dXZ {(X x, z)}) = (\<Sum>yz\<in>(\<lambda>x. (Y x, Z x)) ` space M. ?dXYZ {(X x, yz)})"
      apply (subst setsum_reindex_swap)
      apply (simp add: image_image distribution_def)
      unfolding image_pair_eq_Sigma
      apply (subst setsum_Sigma)
      using finite_space apply simp_all
      apply (rule setsum_cong[OF refl])
      apply (subst measure_finitely_additive'')
      by (auto simp add: disjoint_family_on_def sets_eq_Pow intro!: arg_cong[where f=prob]) }

  thus "(\<Sum>(x, y, z)\<in>X ` space M \<times> Y ` space M \<times> Z ` space M.
      ?dXYZ {(x, y, z)} * log b (?dXYZ {(x, y, z)} / (?dX {x} * ?dYZ {(y, z)}))) -
    (\<Sum>(x, y)\<in>X ` space M \<times> Z ` space M.
      ?dXZ {(x, y)} * log b (?dXZ {(x, y)} / (?dX {x} * ?dZ {y}))) =
  - (\<Sum> (x, z) \<in> (X ` space M \<times> Z ` space M).
      ?dXZ {(x,z)} * log b (?dXZ {(x,z)} / ?dZ {z})) +
    (\<Sum> (x, y, z) \<in> (X ` space M \<times> (\<lambda>x. (Y x, Z x)) ` space M).
      ?dXYZ {(x, y, z)} * log b (?dXYZ {(x, y, z)} / ?dYZ {(y, z)}))"
    using finite_space
    apply (auto simp: setsum_cartesian_product[symmetric] setsum_negf[symmetric]
                      setsum_addf[symmetric] diff_minus
      intro!: setsum_cong[OF refl])
    apply (subst split_measure)
    apply (simp add: If_mult_distr setsum_cases sets distribution_log_split[OF assms, of X])
    apply (subst add_commute)
    by (simp add: setsum_subtractf setsum_negf field_simps setsum_right_distrib[symmetric] sets_eq_Pow)
qed

definition (in prob_space)
  "conditional_entropy b S T X Y = conditional_mutual_information b S S T X X Y"

abbreviation (in finite_prob_space)
  finite_conditional_entropy ("\<H>\<^bsub>_\<^esub>'(_ | _')") where
  "\<H>\<^bsub>b\<^esub>(X | Y) \<equiv> conditional_entropy b
    \<lparr> space = X`space M, sets = Pow (X`space M) \<rparr>
    \<lparr> space = Y`space M, sets = Pow (Y`space M) \<rparr> X Y"

abbreviation (in finite_prob_space)
  finite_conditional_entropy_2 ("\<H>'(_ | _')") where
  "\<H>(X | Y) \<equiv> \<H>\<^bsub>2\<^esub>(X | Y)"

lemma (in finite_prob_space) finite_conditional_entropy_reduce:
  assumes "1 < b"
  shows "\<H>\<^bsub>b\<^esub>(X | Z) =
     - (\<Sum>(x, z)\<in>X ` space M \<times> Z ` space M.
         joint_distribution X Z {(x, z)} *
         log b (joint_distribution X Z {(x, z)} / distribution Z {z}))"
proof -
  have *: "\<And>x y z. (\<lambda>x. (X x, X x, Z x)) -` {(x, y, z)} = (if x = y then (\<lambda>x. (X x, Z x)) -` {(x, z)} else {})" by auto
  show ?thesis
    unfolding finite_conditional_mutual_information_reduce[OF assms]
      conditional_entropy_def joint_distribution_def distribution_def *
    by (auto intro!: setsum_0')
qed

lemma (in finite_prob_space) finite_mutual_information_eq_entropy_conditional_entropy:
  assumes "1 < b" shows "\<I>\<^bsub>b\<^esub>(X ; Z) = \<H>\<^bsub>b\<^esub>(X) - \<H>\<^bsub>b\<^esub>(X | Z)" (is "mutual_information b ?X ?Z X Z = _")
  unfolding finite_mutual_information_reduce
    finite_entropy_reduce[OF assms]
    finite_conditional_entropy_reduce[OF assms]
    joint_distribution diff_minus_eq_add
  using finite_space
  apply (auto simp add: setsum_addf[symmetric] setsum_subtractf
      setsum_Sigma[symmetric] distribution_log_split[OF assms] setsum_negf[symmetric]
    intro!: setsum_cong[OF refl])
  apply (simp add: setsum_negf setsum_left_distrib[symmetric])
proof (rule disjI2)
  let ?dX = "distribution X"
  and ?dXZ = "distribution (\<lambda>x. (X x, Z x))"

  fix x assume "x \<in> space M"
  have "\<And>z. (\<lambda>x. (X x, Z x)) -` {(X x, z)} \<inter> space M = (X -` {X x} \<inter> space M) \<inter> (Z -` {z} \<inter> space M)" by auto
  thus "(\<Sum>z\<in>Z ` space M. distribution (\<lambda>x. (X x, Z x)) {(X x, z)}) = distribution X {X x}"
    unfolding distribution_def
    apply (subst prob_real_sum_image_fn[where e="X -` {X x} \<inter> space M" and s = "Z`space M" and f="\<lambda>z. Z -` {z} \<inter> space M"])
    using finite_space sets_eq_Pow by auto
qed

(* -------------Entropy of a RV with a certain event is zero---------------- *)

lemma (in finite_prob_space) finite_entropy_certainty_eq_0:
  assumes "x \<in> X ` space M" and "distribution X {x} = 1" and "b > 1"
  shows "\<H>\<^bsub>b\<^esub>(X) = 0"
proof -
  interpret X: finite_prob_space "\<lparr> space = X ` space M,
    sets = Pow (X ` space M),
    measure = distribution X\<rparr>" by (rule finite_prob_space)

  have "distribution X (X ` space M - {x}) = distribution X (X ` space M) - distribution X {x}"
    using X.measure_compl[of "{x}"] assms by auto
  also have "\<dots> = 0" using X.prob_space assms by auto
  finally have X0: "distribution X (X ` space M - {x}) = 0" by auto

  { fix y assume asm: "y \<noteq> x" "y \<in> X ` space M"
    hence "{y} \<subseteq> X ` space M - {x}" by auto
    from X.measure_mono[OF this] X0 X.positive[of "{y}"] asm
    have "distribution X {y} = 0" by auto }

  hence fi: "\<And> y. y \<in> X ` space M \<Longrightarrow> distribution X {y} = (if x = y then 1 else 0)"
    using assms by auto

  have y: "\<And>y. (if x = y then 1 else 0) * log b (if x = y then 1 else 0) = 0" by simp

  show ?thesis
    unfolding finite_entropy_reduce[OF `b > 1`] by (auto simp: y fi)
qed
(* --------------- upper bound on entropy for a rv ------------------------- *)

definition convex_set :: "real set \<Rightarrow> bool"
where
  "convex_set C \<equiv> (\<forall> x y \<mu>. x \<in> C \<and> y \<in> C \<and> 0 \<le> \<mu> \<and> \<mu> \<le> 1 \<longrightarrow> \<mu> * x + (1 - \<mu>) * y \<in> C)"

lemma pos_is_convex:
  shows "convex_set {0 <..}"
unfolding convex_set_def
proof safe
  fix x y \<mu> :: real
  assume asms: "\<mu> \<ge> 0" "\<mu> \<le> 1" "x > 0" "y > 0"
  { assume "\<mu> = 0"
    hence "\<mu> * x + (1 - \<mu>) * y = y" by simp
    hence "\<mu> * x + (1 - \<mu>) * y > 0" using asms by simp }
  moreover
  { assume "\<mu> = 1"
    hence "\<mu> * x + (1 - \<mu>) * y > 0" using asms by simp }
  moreover
  { assume "\<mu> \<noteq> 1" "\<mu> \<noteq> 0"
    hence "\<mu> > 0" "(1 - \<mu>) > 0" using asms by auto
    hence "\<mu> * x + (1 - \<mu>) * y > 0" using asms
      apply (subst add_nonneg_pos[of "\<mu> * x" "(1 - \<mu>) * y"])
      using real_mult_order by auto fastsimp }
  ultimately show "\<mu> * x + (1 - \<mu>) * y > 0" using assms by blast
qed

definition convex_fun :: "(real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool"
where
  "convex_fun f C \<equiv> (\<forall> x y \<mu>. convex_set C \<and> (x \<in> C \<and> y \<in> C \<and> 0 \<le> \<mu> \<and> \<mu> \<le> 1 
                   \<longrightarrow> f (\<mu> * x + (1 - \<mu>) * y) \<le> \<mu> * f x + (1 - \<mu>) * f y))"

lemma pos_convex_function:
  fixes f :: "real \<Rightarrow> real"
  assumes "convex_set C"
  assumes leq: "\<And> x y. \<lbrakk>x \<in> C ; y \<in> C\<rbrakk> \<Longrightarrow> f' x * (y - x) \<le> f y - f x"
  shows "convex_fun f C"
unfolding convex_fun_def
using assms
proof safe
  fix x y \<mu> :: real
  let ?x = "\<mu> * x + (1 - \<mu>) * y"
  assume asm: "convex_set C" "x \<in> C" "y \<in> C" "\<mu> \<ge> 0" "\<mu> \<le> 1"
  hence "1 - \<mu> \<ge> 0" by auto
  hence xpos: "?x \<in> C" using asm unfolding convex_set_def by auto
  have geq: "\<mu> * (f x - f ?x) + (1 - \<mu>) * (f y - f ?x) 
            \<ge> \<mu> * f' ?x * (x - ?x) + (1 - \<mu>) * f' ?x * (y - ?x)"
    using add_mono[OF mult_mono1[OF leq[OF xpos asm(2)] `\<mu> \<ge> 0`]
      mult_mono1[OF leq[OF xpos asm(3)] `1 - \<mu> \<ge> 0`]] by auto
  hence "\<mu> * f x + (1 - \<mu>) * f y - f ?x \<ge> 0"
    by (auto simp add:field_simps)
  thus "\<mu> * f x + (1 - \<mu>) * f y \<ge> f ?x" by simp
qed

lemma atMostAtLeast_subset_convex:
  assumes "convex_set C"
  assumes "x \<in> C" "y \<in> C" "x < y"
  shows "{x .. y} \<subseteq> C"
proof safe
  fix z assume zasm: "z \<in> {x .. y}"
  { assume asm: "x < z" "z < y"
    let "?\<mu>" = "(y - z) / (y - x)"
    have "0 \<le> ?\<mu>" "?\<mu> \<le> 1" using assms asm by (auto simp add:field_simps)
    hence comb: "?\<mu> * x + (1 - ?\<mu>) * y \<in> C" 
      using assms[unfolded convex_set_def] by blast
    have "?\<mu> * x + (1 - ?\<mu>) * y = (y - z) * x / (y - x) + (1 - (y - z) / (y - x)) * y"
      by (auto simp add:field_simps)
    also have "\<dots> = ((y - z) * x + (y - x - (y - z)) * y) / (y - x)"
      using assms unfolding add_divide_distrib by (auto simp:field_simps)
    also have "\<dots> = z" 
      using assms by (auto simp:field_simps)
    finally have "z \<in> C"
      using comb by auto } note less = this
  show "z \<in> C" using zasm less assms
    unfolding atLeastAtMost_iff le_less by auto
qed

lemma f''_imp_f':
  fixes f :: "real \<Rightarrow> real"
  assumes "convex_set C"
  assumes f': "\<And> x. x \<in> C \<Longrightarrow> DERIV f x :> (f' x)"
  assumes f'': "\<And> x. x \<in> C \<Longrightarrow> DERIV f' x :> (f'' x)"
  assumes pos: "\<And> x. x \<in> C \<Longrightarrow> f'' x \<ge> 0"
  assumes "x \<in> C" "y \<in> C"
  shows "f' x * (y - x) \<le> f y - f x"
using assms
proof -
  { fix x y :: real assume asm: "x \<in> C" "y \<in> C" "y > x"
    hence ge: "y - x > 0" "y - x \<ge> 0" by auto
    from asm have le: "x - y < 0" "x - y \<le> 0" by auto
    then obtain z1 where z1: "z1 > x" "z1 < y" "f y - f x = (y - x) * f' z1"
      using subsetD[OF atMostAtLeast_subset_convex[OF `convex_set C` `x \<in> C` `y \<in> C` `x < y`],
        THEN f', THEN MVT2[OF `x < y`, rule_format, unfolded atLeastAtMost_iff[symmetric]]]
      by auto
    hence "z1 \<in> C" using atMostAtLeast_subset_convex
      `convex_set C` `x \<in> C` `y \<in> C` `x < y` by fastsimp
    from z1 have z1': "f x - f y = (x - y) * f' z1"
      by (simp add:field_simps)
    obtain z2 where z2: "z2 > x" "z2 < z1" "f' z1 - f' x = (z1 - x) * f'' z2"
      using subsetD[OF atMostAtLeast_subset_convex[OF `convex_set C` `x \<in> C` `z1 \<in> C` `x < z1`],
        THEN f'', THEN MVT2[OF `x < z1`, rule_format, unfolded atLeastAtMost_iff[symmetric]]] z1
      by auto
    obtain z3 where z3: "z3 > z1" "z3 < y" "f' y - f' z1 = (y - z1) * f'' z3"
      using subsetD[OF atMostAtLeast_subset_convex[OF `convex_set C` `z1 \<in> C` `y \<in> C` `z1 < y`],
        THEN f'', THEN MVT2[OF `z1 < y`, rule_format, unfolded atLeastAtMost_iff[symmetric]]] z1
      by auto
    have "f' y - (f x - f y) / (x - y) = f' y - f' z1" 
      using asm z1' by auto
    also have "\<dots> = (y - z1) * f'' z3" using z3 by auto
    finally have cool': "f' y - (f x - f y) / (x - y) = (y - z1) * f'' z3" by simp
    have A': "y - z1 \<ge> 0" using z1 by auto
    have "z3 \<in> C" using z3 asm atMostAtLeast_subset_convex
      `convex_set C` `x \<in> C` `z1 \<in> C` `x < z1` by fastsimp
    hence B': "f'' z3 \<ge> 0" using assms by auto
    from A' B' have "(y - z1) * f'' z3 \<ge> 0" using mult_nonneg_nonneg by auto
    from cool' this have "f' y - (f x - f y) / (x - y) \<ge> 0" by auto
    from mult_right_mono_neg[OF this le(2)]
    have "f' y * (x - y) - (f x - f y) / (x - y) * (x - y) \<le> 0 * (x - y)"
      unfolding diff_def using real_add_mult_distrib by auto
    hence "f' y * (x - y) - (f x - f y) \<le> 0" using le by auto
    hence res: "f' y * (x - y) \<le> f x - f y" by auto
    have "(f y - f x) / (y - x) - f' x = f' z1 - f' x"
      using asm z1 by auto
    also have "\<dots> = (z1 - x) * f'' z2" using z2 by auto
    finally have cool: "(f y - f x) / (y - x) - f' x = (z1 - x) * f'' z2" by simp
    have A: "z1 - x \<ge> 0" using z1 by auto
    have "z2 \<in> C" using z2 z1 asm atMostAtLeast_subset_convex
      `convex_set C` `z1 \<in> C` `y \<in> C` `z1 < y` by fastsimp
    hence B: "f'' z2 \<ge> 0" using assms by auto
    from A B have "(z1 - x) * f'' z2 \<ge> 0" using mult_nonneg_nonneg by auto
    from cool this have "(f y - f x) / (y - x) - f' x \<ge> 0" by auto
    from mult_right_mono[OF this ge(2)]
    have "(f y - f x) / (y - x) * (y - x) - f' x * (y - x) \<ge> 0 * (y - x)" 
      unfolding diff_def using real_add_mult_distrib by auto
    hence "f y - f x - f' x * (y - x) \<ge> 0" using ge by auto
    hence "f y - f x \<ge> f' x * (y - x)" "f' y * (x - y) \<le> f x - f y"
      using res by auto } note less_imp = this
  { fix x y :: real assume "x \<in> C" "y \<in> C" "x \<noteq> y"
    hence"f y - f x \<ge> f' x * (y - x)"
    unfolding neq_iff apply safe
    using less_imp by auto } note neq_imp = this
  moreover
  { fix x y :: real assume asm: "x \<in> C" "y \<in> C" "x = y"
    hence "f y - f x \<ge> f' x * (y - x)" by auto }
  ultimately show ?thesis using assms by blast
qed

lemma f''_ge0_imp_convex:
  fixes f :: "real \<Rightarrow> real"
  assumes conv: "convex_set C"
  assumes f': "\<And> x. x \<in> C \<Longrightarrow> DERIV f x :> (f' x)"
  assumes f'': "\<And> x. x \<in> C \<Longrightarrow> DERIV f' x :> (f'' x)"
  assumes pos: "\<And> x. x \<in> C \<Longrightarrow> f'' x \<ge> 0"
  shows "convex_fun f C"
using f''_imp_f'[OF conv f' f'' pos] assms pos_convex_function by fastsimp

lemma minus_log_convex:
  fixes b :: real
  assumes "b > 1"
  shows "convex_fun (\<lambda> x. - log b x) {0 <..}"
proof -
  have "\<And> z. z > 0 \<Longrightarrow> DERIV (log b) z :> 1 / (ln b * z)" using DERIV_log by auto
  hence f': "\<And> z. z > 0 \<Longrightarrow> DERIV (\<lambda> z. - log b z) z :> - 1 / (ln b * z)"
    using DERIV_minus by auto
  have "\<And> z :: real. z > 0 \<Longrightarrow> DERIV inverse z :> - (inverse z ^ Suc (Suc 0))"
    using less_imp_neq[THEN not_sym, THEN DERIV_inverse] by auto
  from this[THEN DERIV_cmult, of _ "- 1 / ln b"]
  have "\<And> z :: real. z > 0 \<Longrightarrow> DERIV (\<lambda> z. (- 1 / ln b) * inverse z) z :> (- 1 / ln b) * (- (inverse z ^ Suc (Suc 0)))"
    by auto
  hence f''0: "\<And> z :: real. z > 0 \<Longrightarrow> DERIV (\<lambda> z. - 1 / (ln b * z)) z :> 1 / (ln b * z * z)"
    unfolding inverse_eq_divide by (auto simp add:real_mult_assoc)
  have f''_ge0: "\<And> z :: real. z > 0 \<Longrightarrow> 1 / (ln b * z * z) \<ge> 0"
    using `b > 1` by (auto intro!:less_imp_le simp add:divide_pos_pos[of 1] real_mult_order)
  from f''_ge0_imp_convex[OF pos_is_convex, 
    unfolded greaterThan_iff, OF f' f''0 f''_ge0]
  show ?thesis by auto
qed

lemma setsum_nonneg_0:
  fixes f :: "'a \<Rightarrow> real"
  assumes "finite s"
  assumes "\<And> i. i \<in> s \<Longrightarrow> f i \<ge> 0"
  assumes "(\<Sum> i \<in> s. f i) = 0"
  assumes "i \<in> s"
  shows "f i = 0"
proof -
  { assume asm: "f i > 0"
    from assms have "\<forall> j \<in> s - {i}. f j \<ge> 0" by auto
    from setsum_nonneg[of "s - {i}" f, OF this]
    have "(\<Sum> j \<in> s - {i}. f j) \<ge> 0" by simp
    hence "(\<Sum> j \<in> s - {i}. f j) + f i > 0" using asm by auto
    from this setsum.remove[of s i f, OF `finite s` `i \<in> s`]
    have "(\<Sum> j \<in> s. f j) > 0" by auto
    hence "False" using assms by auto }
  thus ?thesis using assms by fastsimp
qed

lemma setsum_nonneg_leq_1:
  fixes f :: "'a \<Rightarrow> real"
  assumes "finite s"
  assumes "\<And> i. i \<in> s \<Longrightarrow> f i \<ge> 0"
  assumes "(\<Sum> i \<in> s. f i) = 1"
  assumes "i \<in> s"
  shows "f i \<le> 1"
proof -
  { assume asm: "f i > 1"
    from assms have "\<forall> j \<in> s - {i}. f j \<ge> 0" by auto
    from setsum_nonneg[of "s - {i}" f, OF this]
    have "(\<Sum> j \<in> s - {i}. f j) \<ge> 0" by simp
    hence "(\<Sum> j \<in> s - {i}. f j) + f i > 1" using asm by auto
    from this setsum.remove[of s i f, OF `finite s` `i \<in> s`]
    have "(\<Sum> j \<in> s. f j) > 1" by auto
    hence "False" using assms by auto }
  thus ?thesis using assms by fastsimp
qed

lemma convex_set_setsum:
  assumes "finite s" "s \<noteq> {}"
  assumes "convex_set C"
  assumes "(\<Sum> i \<in> s. a i) = 1"
  assumes "\<And> i. i \<in> s \<Longrightarrow> a i \<ge> 0"
  assumes "\<And> i. i \<in> s \<Longrightarrow> y i \<in> C"
  shows "(\<Sum> j \<in> s. a j * y j) \<in> C"
using assms
proof (induct s arbitrary:a rule:finite_ne_induct)
  case (singleton i) note asms = this
  hence "a i = 1" by auto
  thus ?case using asms by auto
next
  case (insert i s) note asms = this
  { assume "a i = 1"
    hence "(\<Sum> j \<in> s. a j) = 0"
      using asms by auto
    hence "\<And> j. j \<in> s \<Longrightarrow> a j = 0" 
      using setsum_nonneg_0 asms by fastsimp
    hence ?case using asms by auto }
  moreover
  { assume asm: "a i \<noteq> 1"
    from asms have yai: "y i \<in> C" "a i \<ge> 0" by auto
    have fis: "finite (insert i s)" using asms by auto
    hence ai1: "a i \<le> 1" using setsum_nonneg_leq_1[of "insert i s" a] asms by simp
    hence "a i < 1" using asm by auto
    hence i0: "1 - a i > 0" by auto
    let "?a j" = "a j / (1 - a i)"
    { fix j assume "j \<in> s"
      hence "?a j \<ge> 0" 
        using i0 asms divide_nonneg_pos 
        by fastsimp } note a_nonneg = this
    have "(\<Sum> j \<in> insert i s. a j) = 1" using asms by auto
    hence "(\<Sum> j \<in> s. a j) = 1 - a i" using setsum.insert asms by fastsimp
    hence "(\<Sum> j \<in> s. a j) / (1 - a i) = 1" using i0 by auto
    hence a1: "(\<Sum> j \<in> s. ?a j) = 1" unfolding divide.setsum by simp
    from this asms
    have "(\<Sum>j\<in>s. ?a j * y j) \<in> C" using a_nonneg by fastsimp
    hence "a i * y i + (1 - a i) * (\<Sum> j \<in> s. ?a j * y j) \<in> C"
      using asms[unfolded convex_set_def, rule_format] yai ai1 by auto
    hence "a i * y i + (\<Sum> j \<in> s. (1 - a i) * (?a j * y j)) \<in> C"
      using mult_right.setsum[of "(1 - a i)" "\<lambda> j. ?a j * y j" s] by auto
    hence "a i * y i + (\<Sum> j \<in> s. a j * y j) \<in> C" using i0 by auto
    hence ?case using setsum.insert asms by auto }
  ultimately show ?case by auto
qed

lemma convex_fun_setsum:
  fixes a :: "'a \<Rightarrow> real"
  assumes "finite s" "s \<noteq> {}"
  assumes "convex_fun f C"
  assumes "(\<Sum> i \<in> s. a i) = 1"
  assumes "\<And> i. i \<in> s \<Longrightarrow> a i \<ge> 0"
  assumes "\<And> i. i \<in> s \<Longrightarrow> y i \<in> C"
  shows "f (\<Sum> i \<in> s. a i * y i) \<le> (\<Sum> i \<in> s. a i * f (y i))"
using assms
proof (induct s arbitrary:a rule:finite_ne_induct)
  case (singleton i)
  hence ai: "a i = 1" by auto
  thus ?case by auto
next
  case (insert i s) note asms = this
  hence "convex_fun f C" by simp
  from this[unfolded convex_fun_def, rule_format]
  have conv: "\<And> x y \<mu>. \<lbrakk>x \<in> C; y \<in> C; 0 \<le> \<mu>; \<mu> \<le> 1\<rbrakk>
  \<Longrightarrow> f (\<mu> * x + (1 - \<mu>) * y) \<le> \<mu> * f x + (1 - \<mu>) * f y"
    by simp
  { assume "a i = 1"
    hence "(\<Sum> j \<in> s. a j) = 0"
      using asms by auto
    hence "\<And> j. j \<in> s \<Longrightarrow> a j = 0" 
      using setsum_nonneg_0 asms by fastsimp
    hence ?case using asms by auto }
  moreover
  { assume asm: "a i \<noteq> 1"
    from asms have yai: "y i \<in> C" "a i \<ge> 0" by auto
    have fis: "finite (insert i s)" using asms by auto
    hence ai1: "a i \<le> 1" using setsum_nonneg_leq_1[of "insert i s" a] asms by simp
    hence "a i < 1" using asm by auto
    hence i0: "1 - a i > 0" by auto
    let "?a j" = "a j / (1 - a i)"
    { fix j assume "j \<in> s"
      hence "?a j \<ge> 0" 
        using i0 asms divide_nonneg_pos 
        by fastsimp } note a_nonneg = this
    have "(\<Sum> j \<in> insert i s. a j) = 1" using asms by auto
    hence "(\<Sum> j \<in> s. a j) = 1 - a i" using setsum.insert asms by fastsimp
    hence "(\<Sum> j \<in> s. a j) / (1 - a i) = 1" using i0 by auto
    hence a1: "(\<Sum> j \<in> s. ?a j) = 1" unfolding divide.setsum by simp
    have "convex_set C" using asms unfolding convex_fun_def by auto
    hence asum: "(\<Sum> j \<in> s. ?a j * y j) \<in> C"
      using asms convex_set_setsum[OF `finite s` `s \<noteq> {}` 
        `convex_set C` a1 a_nonneg] by auto
    have asum_le: "f (\<Sum> j \<in> s. ?a j * y j) \<le> (\<Sum> j \<in> s. ?a j * f (y j))"
      using a_nonneg a1 asms by blast
    have "f (\<Sum> j \<in> insert i s. a j * y j) = f ((\<Sum> j \<in> s. a j * y j) + a i * y i)"
      using setsum.insert[of s i "\<lambda> j. a j * y j", OF `finite s` `i \<notin> s`] asms 
      by (auto simp only:add_commute)
    also have "\<dots> = f ((1 - a i) * (\<Sum> j \<in> s. a j * y j) / (1 - a i) + a i * y i)"
      using i0 by auto
    also have "\<dots> = f ((1 - a i) * (\<Sum> j \<in> s. a j * y j / (1 - a i)) + a i * y i)"
      unfolding divide.setsum[of "\<lambda> j. a j * y j" s "1 - a i", symmetric] by auto
    also have "\<dots> = f ((1 - a i) * (\<Sum> j \<in> s. ?a j * y j) + a i * y i)" by auto
    also have "\<dots> \<le> (1 - a i) * f ((\<Sum> j \<in> s. ?a j * y j)) + a i * f (y i)"
      using conv[of "y i" "(\<Sum> j \<in> s. ?a j * y j)" "a i", OF yai(1) asum yai(2) ai1]
      by (auto simp only:add_commute)
    also have "\<dots> \<le> (1 - a i) * (\<Sum> j \<in> s. ?a j * f (y j)) + a i * f (y i)"
      using add_right_mono[OF mult_left_mono[of _ _ "1 - a i", 
        OF asum_le less_imp_le[OF i0]], of "a i * f (y i)"] by simp
    also have "\<dots> = (\<Sum> j \<in> s. (1 - a i) * ?a j * f (y j)) + a i * f (y i)"
      unfolding mult_right.setsum[of "1 - a i" "\<lambda> j. ?a j * f (y j)"] using i0 by auto
    also have "\<dots> = (\<Sum> j \<in> s. a j * f (y j)) + a i * f (y i)" using i0 by auto
    also have "\<dots> = (\<Sum> j \<in> insert i s. a j * f (y j))" using asms by auto
    finally have "f (\<Sum> j \<in> insert i s. a j * y j) \<le> (\<Sum> j \<in> insert i s. a j * f (y j))"
      by simp }
  ultimately show ?case by auto
qed

lemma log_setsum:
  assumes "finite s" "s \<noteq> {}"
  assumes "b > 1"
  assumes "(\<Sum> i \<in> s. a i) = 1"
  assumes "\<And> i. i \<in> s \<Longrightarrow> a i \<ge> 0"
  assumes "\<And> i. i \<in> s \<Longrightarrow> y i \<in> {0 <..}"
  shows "log b (\<Sum> i \<in> s. a i * y i) \<ge> (\<Sum> i \<in> s. a i * log b (y i))"
proof -
  have "convex_fun (\<lambda> x. - log b x) {0 <..}"
    by (rule minus_log_convex[OF `b > 1`])
  hence "- log b (\<Sum> i \<in> s. a i * y i) \<le> (\<Sum> i \<in> s. a i * - log b (y i))"
    using convex_fun_setsum assms by blast
  thus ?thesis by (auto simp add:setsum_negf le_imp_neg_le)
qed

lemma (in finite_prob_space) finite_entropy_le_card:
  assumes "1 < b"
  shows "\<H>\<^bsub>b\<^esub>(X) \<le> log b (real (card (X ` space M \<inter> {x . distribution X {x} \<noteq> 0})))"
proof -
  interpret X: finite_prob_space "\<lparr>space = X ` space M,
                                    sets = Pow (X ` space M),
                                 measure = distribution X\<rparr>"
    using finite_prob_space by auto
  have triv: "\<And> x. (if distribution X {x} \<noteq> 0 then distribution X {x} else 0) = distribution X {x}"
    by auto
  hence sum1: "(\<Sum> x \<in> X ` space M \<inter> {y. distribution X {y} \<noteq> 0}. distribution X {x}) = 1"
    using X.measure_finitely_additive''[of "X ` space M" "\<lambda> x. {x}", simplified]
      sets_eq_Pow inj_singleton[unfolded inj_on_def, rule_format]
    unfolding disjoint_family_on_def  X.prob_space[symmetric]
    using finite_imageI[OF finite_space, of X] by (auto simp add:triv setsum_restrict_set)
  have pos: "\<And> x. x \<in> X ` space M \<inter> {y. distribution X {y} \<noteq> 0} \<Longrightarrow> inverse (distribution X {x}) > 0"
    using X.positive sets_eq_Pow unfolding inverse_positive_iff_positive less_le by auto
  { assume asm: "X ` space M \<inter> {y. distribution X {y} \<noteq> 0} = {}" 
    { fix x assume "x \<in> X ` space M"
      hence "distribution X {x} = 0" using asm by blast }
    hence A: "(\<Sum> x \<in> X ` space M. distribution X {x}) = 0" by auto
    have B: "(\<Sum> x \<in> X ` space M. distribution X {x})
      \<ge> (\<Sum> x \<in> X ` space M \<inter> {y. distribution X {y} \<noteq> 0}. distribution X {x})"
      using finite_imageI[OF finite_space, of X]
      by (subst setsum_mono2) auto
    from A B have "False" using sum1 by auto } note not_empty = this
  { fix x assume asm: "x \<in> X ` space M"
    have "- distribution X {x} * log b (distribution X {x})
       = - (if distribution X {x} \<noteq> 0 
            then distribution X {x} * log b (distribution X {x})
            else 0)"
      by auto
    also have "\<dots> = (if distribution X {x} \<noteq> 0 
          then distribution X {x} * - log b (distribution X {x})
          else 0)"
      by auto
    also have "\<dots> = (if distribution X {x} \<noteq> 0
                    then distribution X {x} * log b (inverse (distribution X {x}))
                    else 0)"
      using log_inverse `1 < b` X.positive[of "{x}"] asm by auto
    finally have "- distribution X {x} * log b (distribution X {x})
                 = (if distribution X {x} \<noteq> 0 
                    then distribution X {x} * log b (inverse (distribution X {x}))
                    else 0)"
      by auto } note log_inv = this
  have "- (\<Sum> x \<in> X ` space M. distribution X {x} * log b (distribution X {x}))
       = (\<Sum> x \<in> X ` space M. (if distribution X {x} \<noteq> 0 
          then distribution X {x} * log b (inverse (distribution X {x}))
          else 0))"
    unfolding setsum_negf[symmetric] using log_inv by auto
  also have "\<dots> = (\<Sum> x \<in> X ` space M \<inter> {y. distribution X {y} \<noteq> 0}.
                          distribution X {x} * log b (inverse (distribution X {x})))"
    unfolding setsum_restrict_set[OF finite_imageI[OF finite_space, of X]] by auto
  also have "\<dots> \<le> log b (\<Sum> x \<in> X ` space M \<inter> {y. distribution X {y} \<noteq> 0}.
                          distribution X {x} * (inverse (distribution X {x})))"
    apply (subst log_setsum[OF _ _ `b > 1` sum1, 
     unfolded greaterThan_iff, OF _ _ _]) using pos sets_eq_Pow
      X.finite_space assms X.positive not_empty by auto
  also have "\<dots> = log b (\<Sum> x \<in> X ` space M \<inter> {y. distribution X {y} \<noteq> 0}. 1)"
    by auto
  also have "\<dots> \<le> log b (real_of_nat (card (X ` space M \<inter> {y. distribution X {y} \<noteq> 0})))"
    by auto
  finally have "- (\<Sum>x\<in>X ` space M. distribution X {x} * log b (distribution X {x}))
               \<le> log b (real_of_nat (card (X ` space M \<inter> {y. distribution X {y} \<noteq> 0})))" by simp
  thus ?thesis unfolding finite_entropy_reduce[OF assms] real_eq_of_nat by auto
qed

(* --------------- entropy is maximal for a uniform rv --------------------- *)

lemma (in finite_prob_space) uniform_prob:
  assumes "x \<in> space M"
  assumes "\<And> x y. \<lbrakk>x \<in> space M ; y \<in> space M\<rbrakk> \<Longrightarrow> prob {x} = prob {y}"
  shows "prob {x} = 1 / real (card (space M))"
proof -
  have prob_x: "\<And> y. y \<in> space M \<Longrightarrow> prob {y} = prob {x}"
    using assms(2)[OF _ `x \<in> space M`] by blast
  have "1 = prob (space M)"
    using prob_space by auto
  also have "\<dots> = (\<Sum> x \<in> space M. prob {x})"
    using measure_finitely_additive''[of "space M" "\<lambda> x. {x}", simplified]
      sets_eq_Pow inj_singleton[unfolded inj_on_def, rule_format]
      finite_space unfolding disjoint_family_on_def  prob_space[symmetric]
    by (auto simp add:setsum_restrict_set)
  also have "\<dots> = (\<Sum> y \<in> space M. prob {x})"
    using prob_x by auto
  also have "\<dots> = real_of_nat (card (space M)) * prob {x}" by simp
  finally have one: "1 = real (card (space M)) * prob {x}"
    using real_eq_of_nat by auto
  hence two: "real (card (space M)) \<noteq> 0" by fastsimp 
  from one have three: "prob {x} \<noteq> 0" by fastsimp
  thus ?thesis using one two three divide_cancel_right
    by (auto simp:field_simps)
qed

lemma (in finite_prob_space) finite_entropy_uniform_max:
  assumes "b > 1"
  assumes "\<And>x y. \<lbrakk> x \<in> X ` space M ; y \<in> X ` space M \<rbrakk> \<Longrightarrow> distribution X {x} = distribution X {y}"
  shows "\<H>\<^bsub>b\<^esub>(X) = log b (real (card (X ` space M)))"
proof -
  interpret X: finite_prob_space "\<lparr>space = X ` space M,
                                    sets = Pow (X ` space M),
                                 measure = distribution X\<rparr>"
    using finite_prob_space by auto
  { fix x assume xasm: "x \<in> X ` space M"
    hence card_gt0: "real (card (X ` space M)) > 0"
      using card_gt_0_iff X.finite_space by auto
    from xasm have "\<And> y. y \<in> X ` space M \<Longrightarrow> distribution X {y} = distribution X {x}"
      using assms by blast
    hence "- (\<Sum>x\<in>X ` space M. distribution X {x} * log b (distribution X {x}))
         = - (\<Sum> y \<in> X ` space M. distribution X {x} * log b (distribution X {x}))"
      by auto
    also have "\<dots> = - real_of_nat (card (X ` space M)) * distribution X {x} * log b (distribution X {x})"
      by auto
    also have "\<dots> = - real (card (X ` space M)) * (1 / real (card (X ` space M))) * log b (1 / real (card (X ` space M)))"
      unfolding real_eq_of_nat[symmetric]
      by (auto simp: X.uniform_prob[simplified, OF xasm assms(2)])
    also have "\<dots> = log b (real (card (X ` space M)))"
      unfolding inverse_eq_divide[symmetric]
      using card_gt0 log_inverse `b > 1` 
      by (auto simp add:field_simps card_gt0)
    finally have ?thesis
      unfolding finite_entropy_reduce[OF `b > 1`] by auto }
  moreover
  { assume "X ` space M = {}"
    hence "distribution X (X ` space M) = 0"
      using X.empty_measure by simp
    hence "False" using X.prob_space by auto }
  ultimately show ?thesis by auto
qed

end
