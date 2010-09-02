theory Information
imports Probability_Space Product_Measure Convex Radon_Nikodym
begin

lemma log_le: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> log a x \<le> log a y"
  by (subst log_le_cancel_iff) auto

lemma log_less: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> x < y \<Longrightarrow> log a x < log a y"
  by (subst log_less_cancel_iff) auto

lemma setsum_cartesian_product':
  "(\<Sum>x\<in>A \<times> B. f x) = (\<Sum>x\<in>A. setsum (\<lambda>y. f (x, y)) B)"
  unfolding setsum_cartesian_product by simp

lemma real_of_pinfreal_inverse[simp]:
  fixes X :: pinfreal
  shows "real (inverse X) = 1 / real X"
  by (cases X) (auto simp: inverse_eq_divide)

lemma (in finite_prob_space) finite_product_prob_space_of_images:
  "finite_prob_space \<lparr> space = X ` space M \<times> Y ` space M, sets = Pow (X ` space M \<times> Y ` space M)\<rparr>
                     (joint_distribution X Y)"
  (is "finite_prob_space ?S _")
proof (simp add: finite_prob_space_eq finite_product_measure_space_of_images)
  have "X -` X ` space M \<inter> Y -` Y ` space M \<inter> space M = space M" by auto
  thus "joint_distribution X Y (X ` space M \<times> Y ` space M) = 1"
    by (simp add: distribution_def prob_space vimage_Times comp_def measure_space_1)
qed

lemma (in finite_prob_space) finite_measure_space_prod:
  assumes X: "finite_measure_space MX (distribution X)"
  assumes Y: "finite_measure_space MY (distribution Y)"
  shows "finite_measure_space (prod_measure_space MX MY) (joint_distribution X Y)"
    (is "finite_measure_space ?M ?D")
proof (intro finite_measure_spaceI)
  interpret X: finite_measure_space MX "distribution X" by fact
  interpret Y: finite_measure_space MY "distribution Y" by fact
  note finite_measure_space.finite_prod_measure_space[OF X Y, simp]
  show "finite (space ?M)" using X.finite_space Y.finite_space by auto
  show "joint_distribution X Y {} = 0" by simp
  show "sets ?M = Pow (space ?M)" by simp
  { fix x show "?D (space ?M) \<noteq> \<omega>" by (rule distribution_finite) }
  { fix A B assume "A \<subseteq> space ?M" "B \<subseteq> space ?M" "A \<inter> B = {}"
    have *: "(\<lambda>t. (X t, Y t)) -` (A \<union> B) \<inter> space M =
             (\<lambda>t. (X t, Y t)) -` A \<inter> space M \<union> (\<lambda>t. (X t, Y t)) -` B \<inter> space M"
      by auto
    show "?D (A \<union> B) = ?D A + ?D B" unfolding distribution_def *
      apply (rule measure_additive[symmetric])
      using `A \<inter> B = {}` by (auto simp: sets_eq_Pow) }
qed

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

lemma split_pairs:
  shows
    "((A, B) = X) \<longleftrightarrow> (fst X = A \<and> snd X = B)" and
    "(X = (A, B)) \<longleftrightarrow> (fst X = A \<and> snd X = B)" by auto

section "Information theory"

locale finite_information_space = finite_prob_space +
  fixes b :: real assumes b_gt_1: "1 < b"

context finite_information_space
begin

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

ML {*

  (* tactic to solve equations of the form @{term "W * log b (X / (Y * Z)) = W * log b X - W * log b (Y * Z)"}
     where @{term W} is a joint distribution of @{term X}, @{term Y}, and @{term Z}. *)

  val mult_log_intros = [@{thm mult_log_divide}, @{thm mult_log_mult}]
  val intros = [@{thm divide_pos_pos}, @{thm mult_pos_pos}, @{thm real_pinfreal_nonneg},
    @{thm real_distribution_divide_pos_pos},
    @{thm real_distribution_mult_inverse_pos_pos},
    @{thm real_distribution_mult_pos_pos}]

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

simproc_setup mult_log ("real (distribution X x) * log b (A * B)" |
                        "real (distribution X x) * log b (A / B)") = {* K mult_log_simproc *}

end

subsection "Kullback$-$Leibler divergence"

text {* The Kullback$-$Leibler divergence is also known as relative entropy or
Kullback$-$Leibler distance. *}

definition
  "KL_divergence b M \<mu> \<nu> =
    measure_space.integral M \<mu> (\<lambda>x. log b (real (sigma_finite_measure.RN_deriv M \<nu> \<mu> x)))"

lemma (in finite_measure_space) KL_divergence_eq_finite:
  assumes v: "finite_measure_space M \<nu>"
  assumes ac: "\<forall>x\<in>space M. \<mu> {x} = 0 \<longrightarrow> \<nu> {x} = 0"
  shows "KL_divergence b M \<nu> \<mu> = (\<Sum>x\<in>space M. real (\<nu> {x}) * log b (real (\<nu> {x}) / real (\<mu> {x})))" (is "_ = ?sum")
proof (simp add: KL_divergence_def finite_measure_space.integral_finite_singleton[OF v])
  interpret v: finite_measure_space M \<nu> by fact
  have ms: "measure_space M \<nu>" by fact
  have ac: "absolutely_continuous \<nu>"
    using ac by (auto intro!: absolutely_continuousI[OF v])
  show "(\<Sum>x \<in> space M. log b (real (RN_deriv \<nu> x)) * real (\<nu> {x})) = ?sum"
    using RN_deriv_finite_measure[OF ms ac]
    by (auto intro!: setsum_cong simp: field_simps real_of_pinfreal_mult[symmetric])
qed

lemma (in finite_prob_space) KL_divergence_positive_finite:
  assumes v: "finite_prob_space M \<nu>"
  assumes ac: "\<And>x. \<lbrakk> x \<in> space M ; \<mu> {x} = 0 \<rbrakk> \<Longrightarrow> \<nu> {x} = 0"
  and "1 < b"
  shows "0 \<le> KL_divergence b M \<nu> \<mu>"
proof -
  interpret v: finite_prob_space M \<nu> using v .

  have *: "space M \<noteq> {}" using not_empty by simp

  hence "- (KL_divergence b M \<nu> \<mu>) \<le> log b (\<Sum>x\<in>space M. real (\<mu> {x}))"
  proof (subst KL_divergence_eq_finite)
    show "finite_measure_space  M \<nu>" by fact

    show "\<forall>x\<in>space M. \<mu> {x} = 0 \<longrightarrow> \<nu> {x} = 0" using ac by auto
    show "- (\<Sum>x\<in>space M. real (\<nu> {x}) * log b (real (\<nu> {x}) / real (\<mu> {x}))) \<le> log b (\<Sum>x\<in>space M. real (\<mu> {x}))"
    proof (safe intro!: log_setsum_divide *)
      show "finite (space M)" using finite_space by simp
      show "1 < b" by fact
      show "(\<Sum>x\<in>space M. real (\<nu> {x})) = 1" using v.finite_sum_over_space_eq_1 by simp

      fix x assume x: "x \<in> space M"
      { assume "0 < real (\<nu> {x})"
        hence "\<mu> {x} \<noteq> 0" using ac[OF x] by auto
        thus "0 < prob {x}" using finite_measure[of "{x}"] sets_eq_Pow x
          by (cases "\<mu> {x}") simp_all }
    qed auto
  qed
  thus "0 \<le> KL_divergence b M \<nu> \<mu>" using finite_sum_over_space_eq_1 by simp
qed

subsection {* Mutual Information *}

definition (in prob_space)
  "mutual_information b S T X Y =
    KL_divergence b (prod_measure_space S T)
      (joint_distribution X Y)
      (prod_measure S (distribution X) T (distribution Y))"

abbreviation (in finite_information_space)
  finite_mutual_information ("\<I>'(_ ; _')") where
  "\<I>(X ; Y) \<equiv> mutual_information b
    \<lparr> space = X`space M, sets = Pow (X`space M) \<rparr>
    \<lparr> space = Y`space M, sets = Pow (Y`space M) \<rparr> X Y"

lemma (in finite_information_space) mutual_information_generic_eq:
  assumes MX: "finite_measure_space MX (distribution X)"
  assumes MY: "finite_measure_space MY (distribution Y)"
  shows "mutual_information b MX MY X Y = (\<Sum> (x,y) \<in> space MX \<times> space MY.
      real (joint_distribution X Y {(x,y)}) *
      log b (real (joint_distribution X Y {(x,y)}) /
      (real (distribution X {x}) * real (distribution Y {y}))))"
proof -
  let ?P = "prod_measure_space MX MY"
  let ?\<mu> = "prod_measure MX (distribution X) MY (distribution Y)"
  let ?\<nu> = "joint_distribution X Y"
  interpret X: finite_measure_space MX "distribution X" by fact
  moreover interpret Y: finite_measure_space MY "distribution Y" by fact
  have fms: "finite_measure_space MX (distribution X)"
            "finite_measure_space MY (distribution Y)" by fact+
  have fms_P: "finite_measure_space ?P ?\<mu>"
    by (rule X.finite_measure_space_finite_prod_measure) fact
  then interpret P: finite_measure_space ?P ?\<mu> .
  have fms_P': "finite_measure_space ?P ?\<nu>"
      using finite_product_measure_space[of "space MX" "space MY"]
        X.finite_space Y.finite_space sigma_prod_sets_finite[OF X.finite_space Y.finite_space]
        X.sets_eq_Pow Y.sets_eq_Pow
      by (simp add: prod_measure_space_def sigma_def)
  then interpret P': finite_measure_space ?P ?\<nu> .
  { fix x assume "x \<in> space ?P"
    hence in_MX: "{fst x} \<in> sets MX" "{snd x} \<in> sets MY" using X.sets_eq_Pow Y.sets_eq_Pow
      by (auto simp: prod_measure_space_def)
    assume "?\<mu> {x} = 0"
    with X.finite_prod_measure_times[OF fms(2), of "{fst x}" "{snd x}"] in_MX
    have "distribution X {fst x} = 0 \<or> distribution Y {snd x} = 0"
      by (simp add: prod_measure_space_def)
    hence "joint_distribution X Y {x} = 0"
      by (cases x) (auto simp: distribution_order) }
  note measure_0 = this
  show ?thesis
    unfolding Let_def mutual_information_def
    using measure_0 fms_P fms_P' MX MY P.absolutely_continuous_def
    by (subst P.KL_divergence_eq_finite)
       (auto simp add: prod_measure_space_def prod_measure_times_finite
         finite_prob_space_eq setsum_cartesian_product' real_of_pinfreal_mult[symmetric])
qed

lemma (in finite_information_space)
  assumes MX: "finite_prob_space MX (distribution X)"
  assumes MY: "finite_prob_space MY (distribution Y)"
  and X_space: "X ` space M \<subseteq> space MX" and Y_space: "Y ` space M \<subseteq> space MY"
  shows mutual_information_eq_generic:
    "mutual_information b MX MY X Y = (\<Sum> (x,y) \<in> space MX \<times> space MY.
      real (joint_distribution X Y {(x,y)}) *
      log b (real (joint_distribution X Y {(x,y)}) /
      (real (distribution X {x}) * real (distribution Y {y}))))"
    (is "?equality")
  and mutual_information_positive_generic:
    "0 \<le> mutual_information b MX MY X Y" (is "?positive")
proof -
  let ?P = "prod_measure_space MX MY"
  let ?\<mu> = "prod_measure MX (distribution X) MY (distribution Y)"
  let ?\<nu> = "joint_distribution X Y"

  interpret X: finite_prob_space MX "distribution X" by fact
  moreover interpret Y: finite_prob_space MY "distribution Y" by fact
  have ms_X: "measure_space MX (distribution X)"
    and ms_Y: "measure_space MY (distribution Y)"
    and fms: "finite_measure_space MX (distribution X)" "finite_measure_space MY (distribution Y)" by fact+
  have fms_P: "finite_measure_space ?P ?\<mu>"
    by (rule X.finite_measure_space_finite_prod_measure) fact
  then interpret P: finite_measure_space ?P ?\<mu> .

  have fms_P': "finite_measure_space ?P ?\<nu>"
      using finite_product_measure_space[of "space MX" "space MY"]
        X.finite_space Y.finite_space sigma_prod_sets_finite[OF X.finite_space Y.finite_space]
        X.sets_eq_Pow Y.sets_eq_Pow
      by (simp add: prod_measure_space_def sigma_def)
  then interpret P': finite_measure_space ?P ?\<nu> .

  { fix x assume "x \<in> space ?P"
    hence in_MX: "{fst x} \<in> sets MX" "{snd x} \<in> sets MY" using X.sets_eq_Pow Y.sets_eq_Pow
      by (auto simp: prod_measure_space_def)

    assume "?\<mu> {x} = 0"
    with X.finite_prod_measure_times[OF fms(2), of "{fst x}" "{snd x}"] in_MX
    have "distribution X {fst x} = 0 \<or> distribution Y {snd x} = 0"
      by (simp add: prod_measure_space_def)

    hence "joint_distribution X Y {x} = 0"
      by (cases x) (auto simp: distribution_order) }
  note measure_0 = this

  show ?equality
    unfolding Let_def mutual_information_def
    using measure_0 fms_P fms_P' MX MY P.absolutely_continuous_def
    by (subst P.KL_divergence_eq_finite)
       (auto simp add: prod_measure_space_def prod_measure_times_finite
         finite_prob_space_eq setsum_cartesian_product' real_of_pinfreal_mult[symmetric])

  show ?positive
    unfolding Let_def mutual_information_def using measure_0 b_gt_1
  proof (safe intro!: finite_prob_space.KL_divergence_positive_finite, simp_all)
    have "?\<mu> (space ?P) = 1"
      using X.top Y.top X.measure_space_1 Y.measure_space_1 fms
      by (simp add: prod_measure_space_def X.finite_prod_measure_times)
    with fms_P show "finite_prob_space ?P ?\<mu>"
      by (simp add: finite_prob_space_eq)

    from ms_X ms_Y X.top Y.top X.measure_space_1 Y.measure_space_1 Y.not_empty X_space Y_space
    have "?\<nu> (space ?P) = 1" unfolding measure_space_1[symmetric]
      by (auto intro!: arg_cong[where f="\<mu>"]
               simp add: prod_measure_space_def distribution_def vimage_Times comp_def)
    with fms_P' show "finite_prob_space ?P ?\<nu>"
      by (simp add: finite_prob_space_eq)
  qed
qed

lemma (in finite_information_space) mutual_information_eq:
  "\<I>(X;Y) = (\<Sum> (x,y) \<in> X ` space M \<times> Y ` space M.
    real (distribution (\<lambda>x. (X x, Y x)) {(x,y)}) * log b (real (distribution (\<lambda>x. (X x, Y x)) {(x,y)}) /
                                                   (real (distribution X {x}) * real (distribution Y {y}))))"
  by (subst mutual_information_eq_generic) (simp_all add: finite_prob_space_of_images)

lemma (in finite_information_space) mutual_information_cong:
  assumes X: "\<And>x. x \<in> space M \<Longrightarrow> X x = X' x"
  assumes Y: "\<And>x. x \<in> space M \<Longrightarrow> Y x = Y' x"
  shows "\<I>(X ; Y) = \<I>(X' ; Y')"
proof -
  have "X ` space M = X' ` space M" using X by (auto intro!: image_eqI)
  moreover have "Y ` space M = Y' ` space M" using Y by (auto intro!: image_eqI)
  ultimately show ?thesis
  unfolding mutual_information_eq
    using
      assms[THEN distribution_cong]
      joint_distribution_cong[OF assms]
    by (auto intro!: setsum_cong)
qed

lemma (in finite_information_space) mutual_information_positive: "0 \<le> \<I>(X;Y)"
  by (subst mutual_information_positive_generic) (simp_all add: finite_prob_space_of_images)

subsection {* Entropy *}

definition (in prob_space)
  "entropy b s X = mutual_information b s s X X"

abbreviation (in finite_information_space)
  finite_entropy ("\<H>'(_')") where
  "\<H>(X) \<equiv> entropy b \<lparr> space = X`space M, sets = Pow (X`space M) \<rparr> X"

lemma (in finite_information_space) entropy_generic_eq:
  assumes MX: "finite_measure_space MX (distribution X)"
  shows "entropy b MX X = -(\<Sum> x \<in> space MX. real (distribution X {x}) * log b (real (distribution X {x})))"
proof -
  let "?X x" = "real (distribution X {x})"
  let "?XX x y" = "real (joint_distribution X X {(x, y)})"
  interpret MX: finite_measure_space MX "distribution X" by fact
  { fix x y
    have "(\<lambda>x. (X x, X x)) -` {(x, y)} = (if x = y then X -` {x} else {})" by auto
    then have "?XX x y * log b (?XX x y / (?X x * ?X y)) =
        (if x = y then - ?X y * log b (?X y) else 0)"
      unfolding distribution_def by (auto simp: mult_log_divide) }
  note remove_XX = this
  show ?thesis
    unfolding entropy_def mutual_information_generic_eq[OF MX MX]
    unfolding setsum_cartesian_product[symmetric] setsum_negf[symmetric] remove_XX
    by (auto simp: setsum_cases MX.finite_space)
qed

lemma (in finite_information_space) entropy_eq:
  "\<H>(X) = -(\<Sum> x \<in> X ` space M. real (distribution X {x}) * log b (real (distribution X {x})))"
  by (simp add: finite_measure_space entropy_generic_eq)

lemma (in finite_information_space) entropy_positive: "0 \<le> \<H>(X)"
  unfolding entropy_def using mutual_information_positive .

lemma (in finite_information_space) entropy_certainty_eq_0:
  assumes "x \<in> X ` space M" and "distribution X {x} = 1"
  shows "\<H>(X) = 0"
proof -
  interpret X: finite_prob_space "\<lparr> space = X ` space M, sets = Pow (X ` space M) \<rparr>" "distribution X"
    by (rule finite_prob_space_of_images)

  have "distribution X (X ` space M - {x}) = distribution X (X ` space M) - distribution X {x}"
    using X.measure_compl[of "{x}"] assms by auto
  also have "\<dots> = 0" using X.prob_space assms by auto
  finally have X0: "distribution X (X ` space M - {x}) = 0" by auto

  { fix y assume asm: "y \<noteq> x" "y \<in> X ` space M"
    hence "{y} \<subseteq> X ` space M - {x}" by auto
    from X.measure_mono[OF this] X0 asm
    have "distribution X {y} = 0" by auto }

  hence fi: "\<And> y. y \<in> X ` space M \<Longrightarrow> real (distribution X {y}) = (if x = y then 1 else 0)"
    using assms by auto

  have y: "\<And>y. (if x = y then 1 else 0) * log b (if x = y then 1 else 0) = 0" by simp

  show ?thesis unfolding entropy_eq by (auto simp: y fi)
qed

lemma (in finite_information_space) entropy_le_card_not_0:
  "\<H>(X) \<le> log b (real (card (X ` space M \<inter> {x . distribution X {x} \<noteq> 0})))"
proof -
  let "?d x" = "distribution X {x}"
  let "?p x" = "real (?d x)"
  have "\<H>(X) = (\<Sum>x\<in>X`space M. ?p x * log b (1 / ?p x))"
    by (auto intro!: setsum_cong simp: entropy_eq setsum_negf[symmetric])
  also have "\<dots> \<le> log b (\<Sum>x\<in>X`space M. ?p x * (1 / ?p x))"
    apply (rule log_setsum')
    using not_empty b_gt_1 finite_space sum_over_space_real_distribution
    by auto
  also have "\<dots> = log b (\<Sum>x\<in>X`space M. if ?d x \<noteq> 0 then 1 else 0)"
    apply (rule arg_cong[where f="\<lambda>f. log b (\<Sum>x\<in>X`space M. f x)"])
    using distribution_finite[of X] by (auto simp: expand_fun_eq real_of_pinfreal_eq_0)
  finally show ?thesis
    using finite_space by (auto simp: setsum_cases real_eq_of_nat)
qed

lemma (in finite_information_space) entropy_uniform_max:
  assumes "\<And>x y. \<lbrakk> x \<in> X ` space M ; y \<in> X ` space M \<rbrakk> \<Longrightarrow> distribution X {x} = distribution X {y}"
  shows "\<H>(X) = log b (real (card (X ` space M)))"
proof -
  note uniform =
    finite_prob_space_of_images[of X, THEN finite_prob_space.uniform_prob, simplified]

  have card_gt0: "0 < card (X ` space M)" unfolding card_gt_0_iff
    using finite_space not_empty by auto

  { fix x assume "x \<in> X ` space M"
    hence "real (distribution X {x}) = 1 / real (card (X ` space M))"
    proof (rule uniform)
      fix x y assume "x \<in> X`space M" "y \<in> X`space M"
      from assms[OF this] show "real (distribution X {x}) = real (distribution X {y})" by simp
    qed }
  thus ?thesis
    using not_empty finite_space b_gt_1 card_gt0
    by (simp add: entropy_eq real_eq_of_nat[symmetric] log_divide)
qed

lemma (in finite_information_space) entropy_le_card:
  "\<H>(X) \<le> log b (real (card (X ` space M)))"
proof cases
  assume "X ` space M \<inter> {x. distribution X {x} \<noteq> 0} = {}"
  then have "\<And>x. x\<in>X`space M \<Longrightarrow> distribution X {x} = 0" by auto
  moreover
  have "0 < card (X`space M)"
    using finite_space not_empty unfolding card_gt_0_iff by auto
  then have "log b 1 \<le> log b (real (card (X`space M)))"
    using b_gt_1 by (intro log_le) auto
  ultimately show ?thesis unfolding entropy_eq by simp
next
  assume False: "X ` space M \<inter> {x. distribution X {x} \<noteq> 0} \<noteq> {}"
  have "card (X ` space M \<inter> {x. distribution X {x} \<noteq> 0}) \<le> card (X ` space M)"
    (is "?A \<le> ?B") using finite_space not_empty by (auto intro!: card_mono)
  note entropy_le_card_not_0
  also have "log b (real ?A) \<le> log b (real ?B)"
    using b_gt_1 False finite_space not_empty `?A \<le> ?B`
    by (auto intro!: log_le simp: card_gt_0_iff)
  finally show ?thesis .
qed

lemma (in finite_information_space) entropy_commute:
  "\<H>(\<lambda>x. (X x, Y x)) = \<H>(\<lambda>x. (Y x, X x))"
proof -
  have *: "(\<lambda>x. (Y x, X x))`space M = (\<lambda>(a,b). (b,a))`(\<lambda>x. (X x, Y x))`space M"
    by auto
  have inj: "\<And>X. inj_on (\<lambda>(a,b). (b,a)) X"
    by (auto intro!: inj_onI)
  show ?thesis
    unfolding entropy_eq unfolding * setsum_reindex[OF inj]
    by (simp add: joint_distribution_commute[of Y X] split_beta)
qed

lemma (in finite_information_space) entropy_eq_cartesian_sum:
  "\<H>(\<lambda>x. (X x, Y x)) = -(\<Sum>x\<in>X`space M. \<Sum>y\<in>Y`space M.
    real (joint_distribution X Y {(x,y)}) *
    log b (real (joint_distribution X Y {(x,y)})))"
proof -
  { fix x assume "x\<notin>(\<lambda>x. (X x, Y x))`space M"
    then have "(\<lambda>x. (X x, Y x)) -` {x} \<inter> space M = {}" by auto
    then have "joint_distribution X Y {x} = 0"
      unfolding distribution_def by auto }
  then show ?thesis using finite_space
    unfolding entropy_eq neg_equal_iff_equal setsum_cartesian_product
    by (auto intro!: setsum_mono_zero_cong_left)
qed

subsection {* Conditional Mutual Information *}

definition (in prob_space)
  "conditional_mutual_information b M1 M2 M3 X Y Z \<equiv>
    mutual_information b M1 (prod_measure_space M2 M3) X (\<lambda>x. (Y x, Z x)) -
    mutual_information b M1 M3 X Z"

abbreviation (in finite_information_space)
  finite_conditional_mutual_information ("\<I>'( _ ; _ | _ ')") where
  "\<I>(X ; Y | Z) \<equiv> conditional_mutual_information b
    \<lparr> space = X`space M, sets = Pow (X`space M) \<rparr>
    \<lparr> space = Y`space M, sets = Pow (Y`space M) \<rparr>
    \<lparr> space = Z`space M, sets = Pow (Z`space M) \<rparr>
    X Y Z"

lemma (in finite_information_space) conditional_mutual_information_generic_eq:
  assumes MX: "finite_measure_space MX (distribution X)"
  assumes MY: "finite_measure_space MY (distribution Y)"
  assumes MZ: "finite_measure_space MZ (distribution Z)"
  shows "conditional_mutual_information b MX MY MZ X Y Z =
    (\<Sum>(x, y, z)\<in>space MX \<times> space MY \<times> space MZ.
      real (joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)}) *
      log b (real (joint_distribution X (\<lambda>x. (Y x, Z x)) {(x, y, z)}) /
                   (real (distribution X {x}) * real (joint_distribution Y Z {(y, z)})))) -
    (\<Sum>(x, y)\<in>space MX \<times> space MZ.
      real (joint_distribution X Z {(x, y)}) *
      log b (real (joint_distribution X Z {(x, y)}) / (real (distribution X {x}) * real (distribution Z {y}))))"
  using assms finite_measure_space_prod[OF MY MZ]
  unfolding conditional_mutual_information_def
  by (subst (1 2) mutual_information_generic_eq)
     (simp_all add: setsum_cartesian_product' finite_measure_space.finite_prod_measure_space)


lemma (in finite_information_space) conditional_mutual_information_eq:
  "\<I>(X ; Y | Z) = (\<Sum>(x, y, z) \<in> X ` space M \<times> Y ` space M \<times> Z ` space M.
             real (distribution (\<lambda>x. (X x, Y x, Z x)) {(x, y, z)}) *
             log b (real (distribution (\<lambda>x. (X x, Y x, Z x)) {(x, y, z)}) /
    (real (joint_distribution X Z {(x, z)}) * real (joint_distribution Y Z {(y,z)} / distribution Z {z}))))"
  by (subst conditional_mutual_information_generic_eq)
     (auto simp add: prod_measure_space_def sigma_prod_sets_finite finite_space
      finite_measure_space finite_product_prob_space_of_images sigma_def
      setsum_cartesian_product' setsum_product setsum_subtractf setsum_addf
      setsum_left_distrib[symmetric] setsum_real_distribution setsum_commute[where A="Y`space M"]
      real_of_pinfreal_mult[symmetric]
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
  let "?dXYZ A" = "real (distribution (\<lambda>x. (X x, Y x, Z x)) A)"
  let "?dXZ A" = "real (joint_distribution X Z A)"
  let "?dYZ A" = "real (joint_distribution Y Z A)"
  let "?dX A" = "real (distribution X A)"
  let "?dZ A" = "real (distribution Z A)"
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
    let ?x = "(fst x, fst (snd x), snd (snd x))"

    show "0 \<le> ?dXYZ {?x}" using real_pinfreal_nonneg .
    show "0 \<le> ?dXZ {(fst x, snd (snd x))} * ?dYZ {(fst (snd x), snd (snd x))} / ?dZ {snd (snd x)}"
     by (simp add: real_pinfreal_nonneg mult_nonneg_nonneg divide_nonneg_nonneg)

    assume *: "0 < ?dXYZ {?x}"
    thus "0 < ?dXZ {(fst x, snd (snd x))} * ?dYZ {(fst (snd x), snd (snd x))} / ?dZ {snd (snd x)}"
      apply (rule_tac divide_pos_pos mult_pos_pos)+
      by (auto simp add: real_distribution_gt_0 intro: distribution_order(6) distribution_mono_gt_0)
  qed (simp_all add: setsum_cartesian_product' sum_over_space_real_distribution setsum_real_distribution finite_space)
  also have "(\<Sum>(x, y, z) \<in> ?M. ?dXZ {(x, z)} * ?dYZ {(y,z)} / ?dZ {z}) = (\<Sum>z\<in>Z`space M. ?dZ {z})"
    apply (simp add: setsum_cartesian_product')
    apply (subst setsum_commute)
    apply (subst (2) setsum_commute)
    by (auto simp: setsum_divide_distrib[symmetric] setsum_product[symmetric] setsum_real_distribution
          intro!: setsum_cong)
  finally show ?thesis
    unfolding conditional_mutual_information_eq sum_over_space_real_distribution
    by (simp add: real_of_pinfreal_mult[symmetric])
qed

subsection {* Conditional Entropy *}

definition (in prob_space)
  "conditional_entropy b S T X Y = conditional_mutual_information b S S T X X Y"

abbreviation (in finite_information_space)
  finite_conditional_entropy ("\<H>'(_ | _')") where
  "\<H>(X | Y) \<equiv> conditional_entropy b
    \<lparr> space = X`space M, sets = Pow (X`space M) \<rparr>
    \<lparr> space = Y`space M, sets = Pow (Y`space M) \<rparr> X Y"

lemma (in finite_information_space) conditional_entropy_positive:
  "0 \<le> \<H>(X | Y)" unfolding conditional_entropy_def using conditional_mutual_information_positive .

lemma (in finite_information_space) conditional_entropy_generic_eq:
  assumes MX: "finite_measure_space MX (distribution X)"
  assumes MY: "finite_measure_space MZ (distribution Z)"
  shows "conditional_entropy b MX MZ X Z =
     - (\<Sum>(x, z)\<in>space MX \<times> space MZ.
         real (joint_distribution X Z {(x, z)}) *
         log b (real (joint_distribution X Z {(x, z)}) / real (distribution Z {z})))"
  unfolding conditional_entropy_def using assms
  apply (simp add: conditional_mutual_information_generic_eq
                   setsum_cartesian_product' setsum_commute[of _ "space MZ"]
                   setsum_negf[symmetric] setsum_subtractf[symmetric])
proof (safe intro!: setsum_cong, simp)
  fix z x assume "z \<in> space MZ" "x \<in> space MX"
  let "?XXZ x'" = "real (joint_distribution X (\<lambda>x. (X x, Z x)) {(x, x', z)})"
  let "?XZ x'" = "real (joint_distribution X Z {(x', z)})"
  let "?X" = "real (distribution X {x})"
  interpret MX: finite_measure_space MX "distribution X" by fact
  have *: "\<And>A. A = {} \<Longrightarrow> prob A = 0" by simp
  have XXZ: "\<And>x'. ?XXZ x' = (if x' = x then ?XZ x else 0)"
    by (auto simp: distribution_def intro!: arg_cong[where f=prob] *)
  have "(\<Sum>x'\<in>space MX. ?XXZ x' * log b (?XXZ x') - (?XXZ x' * log b ?X + ?XXZ x' * log b (?XZ x'))) =
    (\<Sum>x'\<in>{x}. ?XZ x' * log b (?XZ x') - (?XZ x' * log b ?X + ?XZ x' * log b (?XZ x')))"
    using `x \<in> space MX` MX.finite_space
    by (safe intro!: setsum_mono_zero_cong_right)
       (auto split: split_if_asm simp: XXZ)
  then show "(\<Sum>x'\<in>space MX. ?XXZ x' * log b (?XXZ x') - (?XXZ x' * log b ?X + ?XXZ x' * log b (?XZ x'))) +
      ?XZ x * log b ?X = 0" by simp
qed

lemma (in finite_information_space) conditional_entropy_eq:
  "\<H>(X | Z) =
     - (\<Sum>(x, z)\<in>X ` space M \<times> Z ` space M.
         real (joint_distribution X Z {(x, z)}) *
         log b (real (joint_distribution X Z {(x, z)}) / real (distribution Z {z})))"
  by (simp add: finite_measure_space conditional_entropy_generic_eq)

lemma (in finite_information_space) conditional_entropy_eq_ce_with_hypothesis:
  "\<H>(X | Y) =
    -(\<Sum>y\<in>Y`space M. real (distribution Y {y}) *
      (\<Sum>x\<in>X`space M. real (joint_distribution X Y {(x,y)}) / real (distribution Y {(y)}) *
              log b (real (joint_distribution X Y {(x,y)}) / real (distribution Y {(y)}))))"
  unfolding conditional_entropy_eq neg_equal_iff_equal
  apply (simp add: setsum_commute[of _ "Y`space M"] setsum_cartesian_product' setsum_divide_distrib[symmetric])
  apply (safe intro!: setsum_cong)
  using real_distribution_order'[of Y _ X _]
  by (auto simp add: setsum_subtractf[of _ _ "X`space M"])

lemma (in finite_information_space) conditional_entropy_eq_cartesian_sum:
  "\<H>(X | Y) = -(\<Sum>x\<in>X`space M. \<Sum>y\<in>Y`space M.
    real (joint_distribution X Y {(x,y)}) *
    log b (real (joint_distribution X Y {(x,y)}) / real (distribution Y {y})))"
proof -
  { fix x assume "x\<notin>(\<lambda>x. (X x, Y x))`space M"
    then have "(\<lambda>x. (X x, Y x)) -` {x} \<inter> space M = {}" by auto
    then have "joint_distribution X Y {x} = 0"
      unfolding distribution_def by auto }
  then show ?thesis using finite_space
    unfolding conditional_entropy_eq neg_equal_iff_equal setsum_cartesian_product
    by (auto intro!: setsum_mono_zero_cong_left)
qed

subsection {* Equalities *}

lemma (in finite_information_space) mutual_information_eq_entropy_conditional_entropy:
  "\<I>(X ; Z) = \<H>(X) - \<H>(X | Z)"
  unfolding mutual_information_eq entropy_eq conditional_entropy_eq
  using finite_space
  by (auto simp add: setsum_addf setsum_subtractf setsum_cartesian_product'
      setsum_left_distrib[symmetric] setsum_addf setsum_real_distribution)

lemma (in finite_information_space) conditional_entropy_less_eq_entropy:
  "\<H>(X | Z) \<le> \<H>(X)"
proof -
  have "\<I>(X ; Z) = \<H>(X) - \<H>(X | Z)" using mutual_information_eq_entropy_conditional_entropy .
  with mutual_information_positive[of X Z] entropy_positive[of X]
  show ?thesis by auto
qed

lemma (in finite_information_space) entropy_chain_rule:
  "\<H>(\<lambda>x. (X x, Y x)) = \<H>(X) + \<H>(Y|X)"
  unfolding entropy_eq[of X] entropy_eq_cartesian_sum conditional_entropy_eq_cartesian_sum
  unfolding setsum_commute[of _ "X`space M"] setsum_negf[symmetric] setsum_addf[symmetric]
  by (rule setsum_cong)
     (simp_all add: setsum_negf setsum_addf setsum_subtractf setsum_real_distribution
                    setsum_left_distrib[symmetric] joint_distribution_commute[of X Y])

section {* Partitioning *}

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
  have "(\<Sum>x\<in>X ` space M. real (distribution X {x}) * log b (real (distribution X {x}))) =
    (\<Sum>y\<in>P `space M. \<Sum>x\<in>X ` space M.
    real (joint_distribution X P {(x, y)}) * log b (real (joint_distribution X P {(x, y)})))"
  proof (subst setsum_image_split[OF svi],
      safe intro!: finite_imageI finite_space setsum_mono_zero_cong_left imageI)
    fix p x assume in_space: "p \<in> space M" "x \<in> space M"
    assume "real (joint_distribution X P {(X x, P p)}) * log b (real (joint_distribution X P {(X x, P p)})) \<noteq> 0"
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
    thus "real (distribution X {X x}) * log b (real (distribution X {X x})) =
          real (joint_distribution X P {(X x, P p)}) *
          log b (real (joint_distribution X P {(X x, P p)}))"
      by (auto simp: distribution_def)
  qed
  thus ?thesis
  unfolding entropy_eq conditional_entropy_eq
    by (simp add: setsum_cartesian_product' setsum_subtractf setsum_real_distribution
      setsum_left_distrib[symmetric] setsum_commute[where B="P`space M"])
qed

corollary (in finite_information_space) entropy_data_processing:
  "\<H>(f \<circ> X) \<le> \<H>(X)"
  by (subst (2) entropy_partition[of _ "f \<circ> X"]) (auto intro: conditional_entropy_positive)

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
