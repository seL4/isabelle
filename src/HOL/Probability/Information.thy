theory Information
imports Probability_Space Product_Measure Convex
begin

section "Convex theory"

lemma log_setsum:
  assumes "finite s" "s \<noteq> {}"
  assumes "b > 1"
  assumes "(\<Sum> i \<in> s. a i) = 1"
  assumes "\<And> i. i \<in> s \<Longrightarrow> a i \<ge> 0"
  assumes "\<And> i. i \<in> s \<Longrightarrow> y i \<in> {0 <..}"
  shows "log b (\<Sum> i \<in> s. a i * y i) \<ge> (\<Sum> i \<in> s. a i * log b (y i))"
proof -
  have "convex_on {0 <..} (\<lambda> x. - log b x)"
    by (rule minus_log_convex[OF `b > 1`])
  hence "- log b (\<Sum> i \<in> s. a i * y i) \<le> (\<Sum> i \<in> s. a i * - log b (y i))"
    using convex_on_setsum[of _ _ "\<lambda> x. - log b x"] assms pos_is_convex by fastsimp
  thus ?thesis by (auto simp add:setsum_negf le_imp_neg_le)
qed

lemma log_setsum':
  assumes "finite s" "s \<noteq> {}"
  assumes "b > 1"
  assumes "(\<Sum> i \<in> s. a i) = 1"
  assumes pos: "\<And> i. i \<in> s \<Longrightarrow> 0 \<le> a i"
          "\<And> i. \<lbrakk> i \<in> s ; 0 < a i \<rbrakk> \<Longrightarrow> 0 < y i"
  shows "log b (\<Sum> i \<in> s. a i * y i) \<ge> (\<Sum> i \<in> s. a i * log b (y i))"
proof -
  have "\<And>y. (\<Sum> i \<in> s - {i. a i = 0}. a i * y i) = (\<Sum> i \<in> s. a i * y i)"
    using assms by (auto intro!: setsum_mono_zero_cong_left)
  moreover have "log b (\<Sum> i \<in> s - {i. a i = 0}. a i * y i) \<ge> (\<Sum> i \<in> s - {i. a i = 0}. a i * log b (y i))"
  proof (rule log_setsum)
    have "setsum a (s - {i. a i = 0}) = setsum a s"
      using assms(1) by (rule setsum_mono_zero_cong_left) auto
    thus sum_1: "setsum a (s - {i. a i = 0}) = 1"
      "finite (s - {i. a i = 0})" using assms by simp_all

    show "s - {i. a i = 0} \<noteq> {}"
    proof
      assume *: "s - {i. a i = 0} = {}"
      hence "setsum a (s - {i. a i = 0}) = 0" by (simp add: * setsum_empty)
      with sum_1 show False by simp
qed

    fix i assume "i \<in> s - {i. a i = 0}"
    hence "i \<in> s" "a i \<noteq> 0" by simp_all
    thus "0 \<le> a i" "y i \<in> {0<..}" using pos[of i] by auto
  qed fact+
  ultimately show ?thesis by simp
qed

section "Information theory"

lemma (in finite_prob_space) sum_over_space_distrib:
  "(\<Sum>x\<in>X`space M. distribution X {x}) = 1"
  unfolding distribution_def prob_space[symmetric] using finite_space
  by (subst measure_finitely_additive'')
     (auto simp add: disjoint_family_on_def sets_eq_Pow intro!: arg_cong[where f=prob])

locale finite_information_space = finite_prob_space +
  fixes b :: real assumes b_gt_1: "1 < b"

definition
  "KL_divergence b M X Y =
    measure_space.integral (M\<lparr>measure := X\<rparr>)
                           (\<lambda>x. log b ((measure_space.RN_deriv (M \<lparr>measure := Y\<rparr> ) X) x))"

lemma (in finite_prob_space) distribution_mono:
  assumes "\<And>t. \<lbrakk> t \<in> space M ; X t \<in> x \<rbrakk> \<Longrightarrow> Y t \<in> y"
  shows "distribution X x \<le> distribution Y y"
  unfolding distribution_def
  using assms by (auto simp: sets_eq_Pow intro!: measure_mono)

lemma (in prob_space) distribution_remove_const:
  shows "joint_distribution X (\<lambda>x. ()) {(x, ())} = distribution X {x}"
  and "joint_distribution (\<lambda>x. ()) X {((), x)} = distribution X {x}"
  and "joint_distribution X (\<lambda>x. (Y x, ())) {(x, y, ())} = joint_distribution X Y {(x, y)}"
  and "joint_distribution X (\<lambda>x. ((), Y x)) {(x, (), y)} = joint_distribution X Y {(x, y)}"
  and "distribution (\<lambda>x. ()) {()} = 1"
  unfolding prob_space[symmetric]
  by (auto intro!: arg_cong[where f=prob] simp: distribution_def)


context finite_information_space
begin

lemma distribution_mono_gt_0:
  assumes gt_0: "0 < distribution X x"
  assumes *: "\<And>t. \<lbrakk> t \<in> space M ; X t \<in> x \<rbrakk> \<Longrightarrow> Y t \<in> y"
  shows "0 < distribution Y y"
  by (rule less_le_trans[OF gt_0 distribution_mono]) (rule *)

lemma
  assumes "0 \<le> A" and pos: "0 < A \<Longrightarrow> 0 < B" "0 < A \<Longrightarrow> 0 < C"
  shows mult_log_mult: "A * log b (B * C) = A * log b B + A * log b C" (is "?mult")
  and mult_log_divide: "A * log b (B / C) = A * log b B - A * log b C" (is "?div")
proof -
  have "?mult \<and> ?div"
proof (cases "A = 0")
  case False
  hence "0 < A" using `0 \<le> A` by auto
    with pos[OF this] show "?mult \<and> ?div" using b_gt_1
      by (auto simp: log_divide log_mult field_simps)
qed simp
  thus ?mult and ?div by auto
qed

lemma split_pairs:
  shows
    "((A, B) = X) \<longleftrightarrow> (fst X = A \<and> snd X = B)" and
    "(X = (A, B)) \<longleftrightarrow> (fst X = A \<and> snd X = B)" by auto

ML {*

  (* tactic to solve equations of the form @{term "W * log b (X / (Y * Z)) = W * log b X - W * log b (Y * Z)"}
     where @{term W} is a joint distribution of @{term X}, @{term Y}, and @{term Z}. *)

  val mult_log_intros = [@{thm mult_log_divide}, @{thm mult_log_mult}]
  val intros = [@{thm divide_pos_pos}, @{thm mult_pos_pos}, @{thm positive_distribution}]

  val distribution_gt_0_tac = (rtac @{thm distribution_mono_gt_0}
    THEN' assume_tac
    THEN' clarsimp_tac (clasimpset_of @{context} addsimps2 @{thms split_pairs}))

  val distr_mult_log_eq_tac = REPEAT_ALL_NEW (CHANGED o TRY o
    (resolve_tac (mult_log_intros @ intros)
      ORELSE' distribution_gt_0_tac
      ORELSE' clarsimp_tac (clasimpset_of @{context})))

  fun instanciate_term thy redex intro =
    let
      val intro_concl = Thm.concl_of intro

      val lhs = intro_concl |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst

      val m = SOME (Pattern.match thy (lhs, redex) (Vartab.empty, Vartab.empty))
        handle Pattern.MATCH => NONE

    in
      Option.map (fn m => Envir.subst_term m intro_concl) m
    end

  fun mult_log_simproc simpset redex =
  let
    val ctxt = Simplifier.the_context simpset
    val thy = ProofContext.theory_of ctxt
    fun prove (SOME thm) = (SOME
          (Goal.prove ctxt [] [] thm (K (distr_mult_log_eq_tac 1))
           |> mk_meta_eq)
            handle THM _ => NONE)
      | prove NONE = NONE
  in
    get_first (instanciate_term thy (term_of redex) #> prove) mult_log_intros
  end
*}

simproc_setup mult_log ("distribution X x * log b (A * B)" |
                        "distribution X x * log b (A / B)") = {* K mult_log_simproc *}

end

lemma KL_divergence_eq_finite:
  assumes u: "finite_measure_space (M\<lparr>measure := u\<rparr>)"
  assumes v: "finite_measure_space (M\<lparr>measure := v\<rparr>)"
  assumes u_0: "\<And>x. \<lbrakk> x \<in> space M ; v {x} = 0 \<rbrakk> \<Longrightarrow> u {x} = 0"
  shows "KL_divergence b M u v = (\<Sum>x\<in>space M. u {x} * log b (u {x} / v {x}))" (is "_ = ?sum")
proof (simp add: KL_divergence_def, subst finite_measure_space.integral_finite_singleton, simp_all add: u)
  have ms_u: "measure_space (M\<lparr>measure := u\<rparr>)"
    using u unfolding finite_measure_space_def by simp

  show "(\<Sum>x \<in> space M. log b (measure_space.RN_deriv (M\<lparr>measure := v\<rparr>) u x) * u {x}) = ?sum"
    apply (rule setsum_cong[OF refl])
    apply simp
    apply (safe intro!: arg_cong[where f="log b"] )
    apply (subst finite_measure_space.RN_deriv_finite_singleton)
    using assms ms_u by auto
qed

lemma log_setsum_divide:
  assumes "finite S" and "S \<noteq> {}" and "1 < b"
  assumes "(\<Sum>x\<in>S. g x) = 1"
  assumes pos: "\<And>x. x \<in> S \<Longrightarrow> g x \<ge> 0" "\<And>x. x \<in> S \<Longrightarrow> f x \<ge> 0"
  assumes g_pos: "\<And>x. \<lbrakk> x \<in> S ; 0 < g x \<rbrakk> \<Longrightarrow> 0 < f x"
  shows "- (\<Sum>x\<in>S. g x * log b (g x / f x)) \<le> log b (\<Sum>x\<in>S. f x)"
proof -
  have log_mono: "\<And>x y. 0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> log b x \<le> log b y"
    using `1 < b` by (subst log_le_cancel_iff) auto

  have "- (\<Sum>x\<in>S. g x * log b (g x / f x)) = (\<Sum>x\<in>S. g x * log b (f x / g x))"
  proof (unfold setsum_negf[symmetric], rule setsum_cong)
    fix x assume x: "x \<in> S"
    show "- (g x * log b (g x / f x)) = g x * log b (f x / g x)"
    proof (cases "g x = 0")
      case False
      with pos[OF x] g_pos[OF x] have "0 < f x" "0 < g x" by simp_all
      thus ?thesis using `1 < b` by (simp add: log_divide field_simps)
    qed simp
  qed rule
  also have "... \<le> log b (\<Sum>x\<in>S. g x * (f x / g x))"
  proof (rule log_setsum')
    fix x assume x: "x \<in> S" "0 < g x"
    with g_pos[OF x] show "0 < f x / g x" by (safe intro!: divide_pos_pos)
  qed fact+
  also have "... = log b (\<Sum>x\<in>S - {x. g x = 0}. f x)" using `finite S`
    by (auto intro!: setsum_mono_zero_cong_right arg_cong[where f="log b"]
        split: split_if_asm)
  also have "... \<le> log b (\<Sum>x\<in>S. f x)"
  proof (rule log_mono)
    have "0 = (\<Sum>x\<in>S - {x. g x = 0}. 0)" by simp
    also have "... < (\<Sum>x\<in>S - {x. g x = 0}. f x)" (is "_ < ?sum")
    proof (rule setsum_strict_mono)
      show "finite (S - {x. g x = 0})" using `finite S` by simp
      show "S - {x. g x = 0} \<noteq> {}"
      proof
        assume "S - {x. g x = 0} = {}"
        hence "(\<Sum>x\<in>S. g x) = 0" by (subst setsum_0') auto
        with `(\<Sum>x\<in>S. g x) = 1` show False by simp
      qed
      fix x assume "x \<in> S - {x. g x = 0}"
      thus "0 < f x" using g_pos[of x] pos(1)[of x] by auto
    qed
    finally show "0 < ?sum" .
    show "(\<Sum>x\<in>S - {x. g x = 0}. f x) \<le> (\<Sum>x\<in>S. f x)"
      using `finite S` pos by (auto intro!: setsum_mono2)
  qed
  finally show ?thesis .
qed

lemma KL_divergence_positive_finite:
  assumes u: "finite_prob_space (M\<lparr>measure := u\<rparr>)"
  assumes v: "finite_prob_space (M\<lparr>measure := v\<rparr>)"
  assumes u_0: "\<And>x. \<lbrakk> x \<in> space M ; v {x} = 0 \<rbrakk> \<Longrightarrow> u {x} = 0"
  and "1 < b"
  shows "0 \<le> KL_divergence b M u v"
proof -
  interpret u: finite_prob_space "M\<lparr>measure := u\<rparr>" using u .
  interpret v: finite_prob_space "M\<lparr>measure := v\<rparr>" using v .

  have *: "space M \<noteq> {}" using u.not_empty by simp

  have "- (KL_divergence b M u v) \<le> log b (\<Sum>x\<in>space M. v {x})"
  proof (subst KL_divergence_eq_finite, safe intro!: log_setsum_divide *)
    show "finite_measure_space (M\<lparr>measure := u\<rparr>)"
      "finite_measure_space (M\<lparr>measure := v\<rparr>)"
       using u v unfolding finite_prob_space_eq by simp_all

     show "finite (space M)" using u.finite_space by simp
     show "1 < b" by fact
     show "(\<Sum>x\<in>space M. u {x}) = 1" using u.sum_over_space_eq_1 by simp

     fix x assume x: "x \<in> space M"
     thus pos: "0 \<le> u {x}" "0 \<le> v {x}"
       using u.positive u.sets_eq_Pow v.positive v.sets_eq_Pow by simp_all

     { assume "v {x} = 0" from u_0[OF x this] show "u {x} = 0" . }
     { assume "0 < u {x}"
       hence "v {x} \<noteq> 0" using u_0[OF x] by auto
       with pos show "0 < v {x}" by simp }
  qed
  thus "0 \<le> KL_divergence b M u v" using v.sum_over_space_eq_1 by simp
qed

definition (in prob_space)
  "mutual_information b s1 s2 X Y \<equiv>
    let prod_space =
      prod_measure_space (\<lparr>space = space s1, sets = sets s1, measure = distribution X\<rparr>)
                         (\<lparr>space = space s2, sets = sets s2, measure = distribution Y\<rparr>)
    in
      KL_divergence b prod_space (joint_distribution X Y) (measure prod_space)"

abbreviation (in finite_information_space)
  finite_mutual_information ("\<I>'(_ ; _')") where
  "\<I>(X ; Y) \<equiv> mutual_information b
    \<lparr> space = X`space M, sets = Pow (X`space M) \<rparr>
    \<lparr> space = Y`space M, sets = Pow (Y`space M) \<rparr> X Y"

lemma (in finite_measure_space) measure_spaceI: "measure_space M"
  by unfold_locales

lemma prod_measure_times_finite:
  assumes fms: "finite_measure_space M" "finite_measure_space M'" and a: "a \<in> space M \<times> space M'"
  shows "prod_measure M M' {a} = measure M {fst a} * measure M' {snd a}"
proof (cases a)
  case (Pair b c)
  hence a_eq: "{a} = {b} \<times> {c}" by simp

  with fms[THEN finite_measure_space.measure_spaceI]
    fms[THEN finite_measure_space.sets_eq_Pow] a Pair
  show ?thesis unfolding a_eq
    by (subst prod_measure_times) simp_all
qed

lemma setsum_cartesian_product':
  "(\<Sum>x\<in>A \<times> B. f x) = (\<Sum>x\<in>A. setsum (\<lambda>y. f (x, y)) B)"
  unfolding setsum_cartesian_product by simp

lemma (in finite_information_space)
  assumes MX: "finite_prob_space \<lparr> space = space MX, sets = sets MX, measure = distribution X\<rparr>"
    (is "finite_prob_space ?MX")
  assumes MY: "finite_prob_space \<lparr> space = space MY, sets = sets MY, measure = distribution Y\<rparr>"
    (is "finite_prob_space ?MY")
  and X_space: "X ` space M \<subseteq> space MX" and Y_space: "Y ` space M \<subseteq> space MY"
  shows mutual_information_eq_generic:
    "mutual_information b MX MY X Y = (\<Sum> (x,y) \<in> space MX \<times> space MY.
      joint_distribution X Y {(x,y)} *
      log b (joint_distribution X Y {(x,y)} /
      (distribution X {x} * distribution Y {y})))"
    (is "?equality")
  and mutual_information_positive_generic:
    "0 \<le> mutual_information b MX MY X Y" (is "?positive")
proof -
  let ?P = "prod_measure_space ?MX ?MY"
  let ?measure = "joint_distribution X Y"
  let ?P' = "measure_update (\<lambda>_. ?measure) ?P"

  interpret X: finite_prob_space "?MX" using MX .
  moreover interpret Y: finite_prob_space "?MY" using MY .
  ultimately have ms_X: "measure_space ?MX"
    and ms_Y: "measure_space ?MY" by unfold_locales

  have fms_P: "finite_measure_space ?P"
      by (rule finite_measure_space_finite_prod_measure) fact+

  have fms_P': "finite_measure_space ?P'"
      using finite_product_measure_space[of "space MX" "space MY"]
        X.finite_space Y.finite_space sigma_prod_sets_finite[OF X.finite_space Y.finite_space]
        X.sets_eq_Pow Y.sets_eq_Pow
      by (simp add: prod_measure_space_def)

  { fix x assume "x \<in> space ?P"
    hence x_in_MX: "{fst x} \<in> sets MX" using X.sets_eq_Pow
      by (auto simp: prod_measure_space_def)

    assume "measure ?P {x} = 0"
    with prod_measure_times[OF ms_X ms_Y, of "{fst x}" "{snd x}"] x_in_MX
    have "distribution X {fst x} = 0 \<or> distribution Y {snd x} = 0"
      by (simp add: prod_measure_space_def)

    hence "joint_distribution X Y {x} = 0"
      by (cases x) (auto simp: distribution_order) }
  note measure_0 = this

  show ?equality
    unfolding Let_def mutual_information_def using fms_P fms_P' measure_0 MX MY
    by (subst KL_divergence_eq_finite)
       (simp_all add: prod_measure_space_def prod_measure_times_finite
         finite_prob_space_eq setsum_cartesian_product')

  show ?positive
    unfolding Let_def mutual_information_def using measure_0 b_gt_1
  proof (safe intro!: KL_divergence_positive_finite, simp_all)
    from ms_X ms_Y X.top Y.top X.prob_space Y.prob_space
    have "measure ?P (space ?P) = 1"
      by (simp add: prod_measure_space_def, subst prod_measure_times, simp_all)
    with fms_P show "finite_prob_space ?P"
      by (simp add: finite_prob_space_eq)

    from ms_X ms_Y X.top Y.top X.prob_space Y.prob_space Y.not_empty X_space Y_space
    have "measure ?P' (space ?P') = 1" unfolding prob_space[symmetric]
      by (auto simp add: prod_measure_space_def distribution_def vimage_Times comp_def
        intro!: arg_cong[where f=prob])
    with fms_P' show "finite_prob_space ?P'"
      by (simp add: finite_prob_space_eq)
  qed
qed

lemma (in finite_information_space) mutual_information_eq:
  "\<I>(X;Y) = (\<Sum> (x,y) \<in> X ` space M \<times> Y ` space M.
    distribution (\<lambda>x. (X x, Y x)) {(x,y)} * log b (distribution (\<lambda>x. (X x, Y x)) {(x,y)} /
                                                   (distribution X {x} * distribution Y {y})))"
  by (subst mutual_information_eq_generic) (simp_all add: finite_prob_space_of_images)

lemma (in finite_information_space) mutual_information_positive: "0 \<le> \<I>(X;Y)"
  by (subst mutual_information_positive_generic) (simp_all add: finite_prob_space_of_images)

definition (in prob_space)
  "entropy b s X = mutual_information b s s X X"

abbreviation (in finite_information_space)
  finite_entropy ("\<H>'(_')") where
  "\<H>(X) \<equiv> entropy b \<lparr> space = X`space M, sets = Pow (X`space M) \<rparr> X"

lemma (in finite_information_space) joint_distribution_remove[simp]:
    "joint_distribution X X {(x, x)} = distribution X {x}"
  unfolding distribution_def by (auto intro!: arg_cong[where f=prob])

lemma (in finite_information_space) entropy_eq:
  "\<H>(X) = -(\<Sum> x \<in> X ` space M. distribution X {x} * log b (distribution X {x}))"
proof -
  { fix f
  { fix x y
    have "(\<lambda>x. (X x, X x)) -` {(x, y)} = (if x = y then X -` {x} else {})" by auto
      hence "distribution (\<lambda>x. (X x, X x))  {(x,y)} * f x y = (if x = y then distribution X {x} * f x y else 0)"
      unfolding distribution_def by auto }
    hence "(\<Sum>(x, y) \<in> X ` space M \<times> X ` space M. joint_distribution X X {(x, y)} * f x y) =
      (\<Sum>x \<in> X ` space M. distribution X {x} * f x x)"
      unfolding setsum_cartesian_product' by (simp add: setsum_cases finite_space) }
  note remove_cartesian_product = this

  show ?thesis
    unfolding entropy_def mutual_information_eq setsum_negf[symmetric] remove_cartesian_product
    by (auto intro!: setsum_cong)
qed

lemma (in finite_information_space) entropy_positive: "0 \<le> \<H>(X)"
  unfolding entropy_def using mutual_information_positive .

definition (in prob_space)
  "conditional_mutual_information b s1 s2 s3 X Y Z \<equiv>
    let prod_space =
      prod_measure_space \<lparr>space = space s2, sets = sets s2, measure = distribution Y\<rparr>
                         \<lparr>space = space s3, sets = sets s3, measure = distribution Z\<rparr>
    in
      mutual_information b s1 prod_space X (\<lambda>x. (Y x, Z x)) -
      mutual_information b s1 s3 X Z"

abbreviation (in finite_information_space)
  finite_conditional_mutual_information ("\<I>'( _ ; _ | _ ')") where
  "\<I>(X ; Y | Z) \<equiv> conditional_mutual_information b
    \<lparr> space = X`space M, sets = Pow (X`space M) \<rparr>
    \<lparr> space = Y`space M, sets = Pow (Y`space M) \<rparr>
    \<lparr> space = Z`space M, sets = Pow (Z`space M) \<rparr>
    X Y Z"

lemma (in finite_information_space) setsum_distribution_gen:
  assumes "Z -` {c} \<inter> space M = (\<Union>x \<in> X`space M. Y -` {f x}) \<inter> space M"
  and "inj_on f (X`space M)"
  shows "(\<Sum>x \<in> X`space M. distribution Y {f x}) = distribution Z {c}"
  unfolding distribution_def assms
  using finite_space assms
  by (subst measure_finitely_additive'')
     (auto simp add: disjoint_family_on_def sets_eq_Pow inj_on_def
      intro!: arg_cong[where f=prob])

lemma (in finite_information_space) setsum_distribution:
  "(\<Sum>x \<in> X`space M. joint_distribution X Y {(x, y)}) = distribution Y {y}"
  "(\<Sum>y \<in> Y`space M. joint_distribution X Y {(x, y)}) = distribution X {x}"
  "(\<Sum>x \<in> X`space M. joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)}) = joint_distribution Y Z {(y, z)}"
  "(\<Sum>y \<in> Y`space M. joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)}) = joint_distribution X Z {(x, z)}"
  "(\<Sum>z \<in> Z`space M. joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)}) = joint_distribution X Y {(x, y)}"
  by (auto intro!: inj_onI setsum_distribution_gen)

lemma (in finite_information_space) conditional_mutual_information_eq_sum:
   "\<I>(X ; Y | Z) =
     (\<Sum>(x, y, z)\<in>X ` space M \<times> (\<lambda>x. (Y x, Z x)) ` space M.
             distribution (\<lambda>x. (X x, Y x, Z x)) {(x, y, z)} *
             log b (distribution (\<lambda>x. (X x, Y x, Z x)) {(x, y, z)}/
        distribution (\<lambda>x. (Y x, Z x)) {(y, z)})) -
     (\<Sum>(x, z)\<in>X ` space M \<times> Z ` space M.
        distribution (\<lambda>x. (X x, Z x)) {(x,z)} * log b (distribution (\<lambda>x. (X x, Z x)) {(x,z)} / distribution Z {z}))"
  (is "_ = ?rhs")
proof -
  have setsum_product:
    "\<And>f x. (\<Sum>v\<in>(\<lambda>x. (Y x, Z x)) ` space M. joint_distribution X (\<lambda>x. (Y x, Z x)) {(x,v)} * f v)
      = (\<Sum>v\<in>Y ` space M \<times> Z ` space M. joint_distribution X (\<lambda>x. (Y x, Z x)) {(x,v)} * f v)"
  proof (safe intro!: setsum_mono_zero_cong_left imageI)
    fix x y z f
    assume *: "(Y y, Z z) \<notin> (\<lambda>x. (Y x, Z x)) ` space M" and "y \<in> space M" "z \<in> space M"
    hence "(\<lambda>x. (X x, Y x, Z x)) -` {(x, Y y, Z z)} \<inter> space M = {}"
    proof safe
      fix x' assume x': "x' \<in> space M" and eq: "Y x' = Y y" "Z x' = Z z"
      have "(Y y, Z z) \<in> (\<lambda>x. (Y x, Z x)) ` space M" using eq[symmetric] x' by auto
      thus "x' \<in> {}" using * by auto
    qed
    thus "joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, Y y, Z z)} * f (Y y) (Z z) = 0"
      unfolding distribution_def by simp
  qed (simp add: finite_space)

  thus ?thesis
    unfolding conditional_mutual_information_def Let_def mutual_information_eq
    apply (subst mutual_information_eq_generic)
    by (auto simp add: prod_measure_space_def sigma_prod_sets_finite finite_space
        finite_prob_space_of_images finite_product_prob_space_of_images
        setsum_cartesian_product' setsum_product setsum_subtractf setsum_addf
        setsum_left_distrib[symmetric] setsum_distribution
      cong: setsum_cong)
qed

lemma (in finite_information_space) conditional_mutual_information_eq:
  "\<I>(X ; Y | Z) = (\<Sum>(x, y, z) \<in> X ` space M \<times> Y ` space M \<times> Z ` space M.
             distribution (\<lambda>x. (X x, Y x, Z x)) {(x, y, z)} *
             log b (distribution (\<lambda>x. (X x, Y x, Z x)) {(x, y, z)}/
    (joint_distribution X Z {(x, z)} * joint_distribution Y Z {(y,z)} / distribution Z {z})))"
  unfolding conditional_mutual_information_def Let_def mutual_information_eq
    apply (subst mutual_information_eq_generic)
  by (auto simp add: prod_measure_space_def sigma_prod_sets_finite finite_space
      finite_prob_space_of_images finite_product_prob_space_of_images
      setsum_cartesian_product' setsum_product setsum_subtractf setsum_addf
      setsum_left_distrib[symmetric] setsum_distribution setsum_commute[where A="Y`space M"]
    cong: setsum_cong)

lemma (in finite_information_space) conditional_mutual_information_eq_mutual_information:
  "\<I>(X ; Y) = \<I>(X ; Y | (\<lambda>x. ()))"
proof -
  have [simp]: "(\<lambda>x. ()) ` space M = {()}" using not_empty by auto

  show ?thesis
    unfolding conditional_mutual_information_eq mutual_information_eq
    by (simp add: setsum_cartesian_product' distribution_remove_const)
qed

lemma (in finite_information_space) conditional_mutual_information_positive:
  "0 \<le> \<I>(X ; Y | Z)"
proof -
  let ?dXYZ = "distribution (\<lambda>x. (X x, Y x, Z x))"
  let ?dXZ = "joint_distribution X Z"
  let ?dYZ = "joint_distribution Y Z"
  let ?dX = "distribution X"
  let ?dZ = "distribution Z"
  let ?M = "X ` space M \<times> Y ` space M \<times> Z ` space M"

  have split_beta: "\<And>f. split f = (\<lambda>x. f (fst x) (snd x))" by (simp add: expand_fun_eq)

  have "- (\<Sum>(x, y, z) \<in> ?M. ?dXYZ {(x, y, z)} *
    log b (?dXYZ {(x, y, z)} / (?dXZ {(x, z)} * ?dYZ {(y,z)} / ?dZ {z})))
    \<le> log b (\<Sum>(x, y, z) \<in> ?M. ?dXZ {(x, z)} * ?dYZ {(y,z)} / ?dZ {z})"
    unfolding split_beta
  proof (rule log_setsum_divide)
    show "?M \<noteq> {}" using not_empty by simp
    show "1 < b" using b_gt_1 .

    fix x assume "x \<in> ?M"
    show "0 \<le> ?dXYZ {(fst x, fst (snd x), snd (snd x))}" using positive_distribution .
    show "0 \<le> ?dXZ {(fst x, snd (snd x))} * ?dYZ {(fst (snd x), snd (snd x))} / ?dZ {snd (snd x)}"
      by (auto intro!: mult_nonneg_nonneg positive_distribution simp: zero_le_divide_iff)

    assume *: "0 < ?dXYZ {(fst x, fst (snd x), snd (snd x))}"
    thus "0 < ?dXZ {(fst x, snd (snd x))} * ?dYZ {(fst (snd x), snd (snd x))} / ?dZ {snd (snd x)}"
      by (auto intro!: divide_pos_pos mult_pos_pos
           intro: distribution_order(6) distribution_mono_gt_0)
  qed (simp_all add: setsum_cartesian_product' sum_over_space_distrib setsum_distribution finite_space)
  also have "(\<Sum>(x, y, z) \<in> ?M. ?dXZ {(x, z)} * ?dYZ {(y,z)} / ?dZ {z}) = (\<Sum>z\<in>Z`space M. ?dZ {z})"
    apply (simp add: setsum_cartesian_product')
    apply (subst setsum_commute)
    apply (subst (2) setsum_commute)
    by (auto simp: setsum_divide_distrib[symmetric] setsum_product[symmetric] setsum_distribution
          intro!: setsum_cong)
  finally show ?thesis
    unfolding conditional_mutual_information_eq sum_over_space_distrib by simp
qed


definition (in prob_space)
  "conditional_entropy b S T X Y = conditional_mutual_information b S S T X X Y"

abbreviation (in finite_information_space)
  finite_conditional_entropy ("\<H>'(_ | _')") where
  "\<H>(X | Y) \<equiv> conditional_entropy b
    \<lparr> space = X`space M, sets = Pow (X`space M) \<rparr>
    \<lparr> space = Y`space M, sets = Pow (Y`space M) \<rparr> X Y"

lemma (in finite_information_space) conditional_entropy_positive:
  "0 \<le> \<H>(X | Y)" unfolding conditional_entropy_def using conditional_mutual_information_positive .

lemma (in finite_information_space) conditional_entropy_eq:
  "\<H>(X | Z) =
     - (\<Sum>(x, z)\<in>X ` space M \<times> Z ` space M.
         joint_distribution X Z {(x, z)} *
         log b (joint_distribution X Z {(x, z)} / distribution Z {z}))"
proof -
  have *: "\<And>x y z. (\<lambda>x. (X x, X x, Z x)) -` {(x, y, z)} = (if x = y then (\<lambda>x. (X x, Z x)) -` {(x, z)} else {})" by auto
  show ?thesis
    unfolding conditional_mutual_information_eq_sum
      conditional_entropy_def distribution_def *
    by (auto intro!: setsum_0')
qed

lemma (in finite_information_space) mutual_information_eq_entropy_conditional_entropy:
  "\<I>(X ; Z) = \<H>(X) - \<H>(X | Z)"
  unfolding mutual_information_eq entropy_eq conditional_entropy_eq
  using finite_space
  by (auto simp add: setsum_addf setsum_subtractf setsum_cartesian_product'
      setsum_left_distrib[symmetric] setsum_addf setsum_distribution)

lemma (in finite_information_space) conditional_entropy_less_eq_entropy:
  "\<H>(X | Z) \<le> \<H>(X)"
proof -
  have "\<I>(X ; Z) = \<H>(X) - \<H>(X | Z)" using mutual_information_eq_entropy_conditional_entropy .
  with mutual_information_positive[of X Z] entropy_positive[of X]
  show ?thesis by auto
qed

(* -------------Entropy of a RV with a certain event is zero---------------- *)

lemma (in finite_information_space) finite_entropy_certainty_eq_0:
  assumes "x \<in> X ` space M" and "distribution X {x} = 1"
  shows "\<H>(X) = 0"
proof -
  interpret X: finite_prob_space "\<lparr> space = X ` space M,
    sets = Pow (X ` space M),
    measure = distribution X\<rparr>" by (rule finite_prob_space_of_images)

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

  show ?thesis unfolding entropy_eq by (auto simp: y fi)
qed
(* --------------- upper bound on entropy for a rv ------------------------- *)

lemma (in finite_information_space) finite_entropy_le_card:
  "\<H>(X) \<le> log b (real (card (X ` space M \<inter> {x . distribution X {x} \<noteq> 0})))"
proof -
  interpret X: finite_prob_space "\<lparr>space = X ` space M,
                                    sets = Pow (X ` space M),
                                 measure = distribution X\<rparr>"
    using finite_prob_space_of_images by auto

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
      using log_inverse b_gt_1 X.positive[of "{x}"] asm by auto
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
    apply (subst log_setsum[OF _ _ b_gt_1 sum1, 
     unfolded greaterThan_iff, OF _ _ _]) using pos sets_eq_Pow
      X.finite_space assms X.positive not_empty by auto
  also have "\<dots> = log b (\<Sum> x \<in> X ` space M \<inter> {y. distribution X {y} \<noteq> 0}. 1)"
    by auto
  also have "\<dots> \<le> log b (real_of_nat (card (X ` space M \<inter> {y. distribution X {y} \<noteq> 0})))"
    by auto
  finally have "- (\<Sum>x\<in>X ` space M. distribution X {x} * log b (distribution X {x}))
               \<le> log b (real_of_nat (card (X ` space M \<inter> {y. distribution X {y} \<noteq> 0})))" by simp
  thus ?thesis unfolding entropy_eq real_eq_of_nat by auto
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

lemma (in finite_information_space) finite_entropy_uniform_max:
  assumes "\<And>x y. \<lbrakk> x \<in> X ` space M ; y \<in> X ` space M \<rbrakk> \<Longrightarrow> distribution X {x} = distribution X {y}"
  shows "\<H>(X) = log b (real (card (X ` space M)))"
proof -
  interpret X: finite_prob_space "\<lparr>space = X ` space M,
                                    sets = Pow (X ` space M),
                                 measure = distribution X\<rparr>"
    using finite_prob_space_of_images by auto

  { fix x assume xasm: "x \<in> X ` space M"
    hence card_gt0: "real (card (X ` space M)) > 0"
      using card_gt_0_iff X.finite_space by auto
    from xasm have "\<And> y. y \<in> X ` space M \<Longrightarrow> distribution X {y} = distribution X {x}"
      using assms by blast
    hence "- (\<Sum>x\<in>X ` space M. distribution X {x} * log b (distribution X {x}))
         = - real (card (X ` space M)) * distribution X {x} * log b (distribution X {x})"
      unfolding real_eq_of_nat by auto
    also have "\<dots> = - real (card (X ` space M)) * (1 / real (card (X ` space M))) * log b (1 / real (card (X ` space M)))"
      by (auto simp: X.uniform_prob[simplified, OF xasm assms])
    also have "\<dots> = log b (real (card (X ` space M)))"
      unfolding inverse_eq_divide[symmetric]
      using card_gt0 log_inverse b_gt_1
      by (auto simp add:field_simps card_gt0)
    finally have ?thesis
      unfolding entropy_eq by auto }
  moreover
  { assume "X ` space M = {}"
    hence "distribution X (X ` space M) = 0"
      using X.empty_measure by simp
    hence "False" using X.prob_space by auto }
  ultimately show ?thesis by auto
qed

definition "subvimage A f g \<longleftrightarrow> (\<forall>x \<in> A. f -` {f x} \<inter> A \<subseteq> g -` {g x} \<inter> A)"

lemma subvimageI:
  assumes "\<And>x y. \<lbrakk> x \<in> A ; y \<in> A ; f x = f y \<rbrakk> \<Longrightarrow> g x = g y"
  shows "subvimage A f g"
  using assms unfolding subvimage_def by blast

lemma subvimageE[consumes 1]:
  assumes "subvimage A f g"
  obtains "\<And>x y. \<lbrakk> x \<in> A ; y \<in> A ; f x = f y \<rbrakk> \<Longrightarrow> g x = g y"
  using assms unfolding subvimage_def by blast

lemma subvimageD:
  "\<lbrakk> subvimage A f g ; x \<in> A ; y \<in> A ; f x = f y \<rbrakk> \<Longrightarrow> g x = g y"
  using assms unfolding subvimage_def by blast

lemma subvimage_subset:
  "\<lbrakk> subvimage B f g ; A \<subseteq> B \<rbrakk> \<Longrightarrow> subvimage A f g"
  unfolding subvimage_def by auto

lemma subvimage_idem[intro]: "subvimage A g g"
  by (safe intro!: subvimageI)

lemma subvimage_comp_finer[intro]:
  assumes svi: "subvimage A g h"
  shows "subvimage A g (f \<circ> h)"
proof (rule subvimageI, simp)
  fix x y assume "x \<in> A" "y \<in> A" "g x = g y"
  from svi[THEN subvimageD, OF this]
  show "f (h x) = f (h y)" by simp
qed

lemma subvimage_comp_gran:
  assumes svi: "subvimage A g h"
  assumes inj: "inj_on f (g ` A)"
  shows "subvimage A (f \<circ> g) h"
  by (rule subvimageI) (auto intro!: subvimageD[OF svi] simp: inj_on_iff[OF inj])

lemma subvimage_comp:
  assumes svi: "subvimage (f ` A) g h"
  shows "subvimage A (g \<circ> f) (h \<circ> f)"
  by (rule subvimageI) (auto intro!: svi[THEN subvimageD])

lemma subvimage_trans:
  assumes fg: "subvimage A f g"
  assumes gh: "subvimage A g h"
  shows "subvimage A f h"
  by (rule subvimageI) (auto intro!: fg[THEN subvimageD] gh[THEN subvimageD])

lemma subvimage_translator:
  assumes svi: "subvimage A f g"
  shows "\<exists>h. \<forall>x \<in> A. h (f x)  = g x"
proof (safe intro!: exI[of _ "\<lambda>x. (THE z. z \<in> (g ` (f -` {x} \<inter> A)))"])
  fix x assume "x \<in> A"
  show "(THE x'. x' \<in> (g ` (f -` {f x} \<inter> A))) = g x"
    by (rule theI2[of _ "g x"])
      (insert `x \<in> A`, auto intro!: svi[THEN subvimageD])
qed

lemma subvimage_translator_image:
  assumes svi: "subvimage A f g"
  shows "\<exists>h. h ` f ` A = g ` A"
proof -
  from subvimage_translator[OF svi]
  obtain h where "\<And>x. x \<in> A \<Longrightarrow> h (f x) = g x" by auto
  thus ?thesis
    by (auto intro!: exI[of _ h]
      simp: image_compose[symmetric] comp_def cong: image_cong)
qed

lemma subvimage_finite:
  assumes svi: "subvimage A f g" and fin: "finite (f`A)"
  shows "finite (g`A)"
proof -
  from subvimage_translator_image[OF svi]
  obtain h where "g`A = h`f`A" by fastsimp
  with fin show "finite (g`A)" by simp
qed

lemma subvimage_disj:
  assumes svi: "subvimage A f g"
  shows "f -` {x} \<inter> A \<subseteq> g -` {y} \<inter> A \<or>
      f -` {x} \<inter> g -` {y} \<inter> A = {}" (is "?sub \<or> ?dist")
proof (rule disjCI)
  assume "\<not> ?dist"
  then obtain z where "z \<in> A" and "x = f z" and "y = g z" by auto
  thus "?sub" using svi unfolding subvimage_def by auto
qed

lemma setsum_image_split:
  assumes svi: "subvimage A f g" and fin: "finite (f ` A)"
  shows "(\<Sum>x\<in>f`A. h x) = (\<Sum>y\<in>g`A. \<Sum>x\<in>f`(g -` {y} \<inter> A). h x)"
    (is "?lhs = ?rhs")
proof -
  have "f ` A =
      snd ` (SIGMA x : g ` A. f ` (g -` {x} \<inter> A))"
      (is "_ = snd ` ?SIGMA")
    unfolding image_split_eq_Sigma[symmetric]
    by (simp add: image_compose[symmetric] comp_def)
  moreover
  have snd_inj: "inj_on snd ?SIGMA"
    unfolding image_split_eq_Sigma[symmetric]
    by (auto intro!: inj_onI subvimageD[OF svi])
  ultimately
  have "(\<Sum>x\<in>f`A. h x) = (\<Sum>(x,y)\<in>?SIGMA. h y)"
    by (auto simp: setsum_reindex intro: setsum_cong)
  also have "... = ?rhs"
    using subvimage_finite[OF svi fin] fin
    apply (subst setsum_Sigma[symmetric])
    by (auto intro!: finite_subset[of _ "f`A"])
  finally show ?thesis .
qed

lemma (in finite_information_space) entropy_partition:
  assumes svi: "subvimage (space M) X P"
  shows "\<H>(X) = \<H>(P) + \<H>(X|P)"
proof -
  have "(\<Sum>x\<in>X ` space M. distribution X {x} * log b (distribution X {x})) =
    (\<Sum>y\<in>P `space M. \<Sum>x\<in>X ` space M.
    joint_distribution X P {(x, y)} * log b (joint_distribution X P {(x, y)}))"
  proof (subst setsum_image_split[OF svi],
      safe intro!: finite_imageI finite_space setsum_mono_zero_cong_left imageI)
    fix p x assume in_space: "p \<in> space M" "x \<in> space M"
    assume "joint_distribution X P {(X x, P p)} * log b (joint_distribution X P {(X x, P p)}) \<noteq> 0"
    hence "(\<lambda>x. (X x, P x)) -` {(X x, P p)} \<inter> space M \<noteq> {}" by (auto simp: distribution_def)
    with svi[unfolded subvimage_def, rule_format, OF `x \<in> space M`]
    show "x \<in> P -` {P p}" by auto
  next
    fix p x assume in_space: "p \<in> space M" "x \<in> space M"
    assume "P x = P p"
    from this[symmetric] svi[unfolded subvimage_def, rule_format, OF `x \<in> space M`]
    have "X -` {X x} \<inter> space M \<subseteq> P -` {P p} \<inter> space M"
      by auto
    hence "(\<lambda>x. (X x, P x)) -` {(X x, P p)} \<inter> space M = X -` {X x} \<inter> space M"
      by auto
    thus "distribution X {X x} * log b (distribution X {X x}) =
          joint_distribution X P {(X x, P p)} *
          log b (joint_distribution X P {(X x, P p)})"
      by (auto simp: distribution_def)
  qed
  thus ?thesis
  unfolding entropy_eq conditional_entropy_eq
    by (simp add: setsum_cartesian_product' setsum_subtractf setsum_distribution
      setsum_left_distrib[symmetric] setsum_commute[where B="P`space M"])
qed

corollary (in finite_information_space) entropy_data_processing:
  "\<H>(f \<circ> X) \<le> \<H>(X)"
  by (subst (2) entropy_partition[of _ "f \<circ> X"]) (auto intro: conditional_entropy_positive)

lemma (in prob_space) distribution_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> X x = Y x"
  shows "distribution X = distribution Y"
  unfolding distribution_def expand_fun_eq
  using assms by (auto intro!: arg_cong[where f=prob])

lemma (in prob_space) joint_distribution_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> X x = X' x"
  assumes "\<And>x. x \<in> space M \<Longrightarrow> Y x = Y' x"
  shows "joint_distribution X Y = joint_distribution X' Y'"
  unfolding distribution_def expand_fun_eq
  using assms by (auto intro!: arg_cong[where f=prob])

lemma image_cong:
  "\<lbrakk> \<And>x. x \<in> S \<Longrightarrow> X x = X' x \<rbrakk> \<Longrightarrow> X ` S = X' ` S"
  by (auto intro!: image_eqI)

lemma (in finite_information_space) mutual_information_cong:
  assumes X: "\<And>x. x \<in> space M \<Longrightarrow> X x = X' x"
  assumes Y: "\<And>x. x \<in> space M \<Longrightarrow> Y x = Y' x"
  shows "\<I>(X ; Y) = \<I>(X' ; Y')"
proof -
  have "X ` space M = X' ` space M" using X by (rule image_cong)
  moreover have "Y ` space M = Y' ` space M" using Y by (rule image_cong)
  ultimately show ?thesis
  unfolding mutual_information_eq
    using
      assms[THEN distribution_cong]
      joint_distribution_cong[OF assms]
    by (auto intro!: setsum_cong)
qed

corollary (in finite_information_space) entropy_of_inj:
  assumes "inj_on f (X`space M)"
  shows "\<H>(f \<circ> X) = \<H>(X)"
proof (rule antisym)
  show "\<H>(f \<circ> X) \<le> \<H>(X)" using entropy_data_processing .
next
  have "\<H>(X) = \<H>(the_inv_into (X`space M) f \<circ> (f \<circ> X))"
    by (auto intro!: mutual_information_cong simp: entropy_def the_inv_into_f_f[OF assms])
  also have "... \<le> \<H>(f \<circ> X)"
    using entropy_data_processing .
  finally show "\<H>(X) \<le> \<H>(f \<circ> X)" .
qed

end
