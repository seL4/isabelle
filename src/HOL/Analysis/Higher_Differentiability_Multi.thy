section \<open>Higher-Order Differentiability in Several Variables\<close>

text \<open>
  \<open>k\<close>-times Fréchet differentiability and \<open>C\<^sup>k\<close> smoothness for maps between real normed
  vector spaces, and gradients, Hessians and Jacobians for maps between Euclidean spaces.
  Higher derivatives are iterated as directional derivatives
  \<open>\<lambda>y. frechet_derivative f (at y) v\<close>, which keeps the codomain type fixed.  The
  one-variable notions \<open>k_times_differentiable_at\<close> and \<open>C_k_on\<close> use \<open>deriv ^^ k\<close> instead,
  as Taylor expansions and power series require; for \<open>f :: real \<Rightarrow> real\<close> the two agree
  (\<open>k_times_Fr_real_iff\<close>, \<open>Ck_on_real_iff\<close>), and for functions of one real variable
  \<open>C\<^sup>1\<close> agrees with \<open>C1_differentiable_on\<close> of HOL-Analysis.
\<close>

theory Higher_Differentiability_Multi
  imports Higher_Order_Derivatives Cartesian_Euclidean_Space
begin

subsection \<open>Multi-dimensional \<open>k\<close>-times Fréchet differentiability at a point\<close>

text \<open>
  Differentiability without continuity: \<open>f\<close> is \<open>(Suc k)\<close>-times differentiable at \<open>x\<close> if
  it is \<open>k\<close>-times differentiable near \<open>x\<close>, differentiable at \<open>x\<close>, and every directional
  derivative \<open>\<lambda>y. frechet_derivative f (at y) v\<close> is \<open>k\<close>-times differentiable at \<open>x\<close>.
\<close>

primrec k_times_Fr_differentiable_at
  :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "k_times_Fr_differentiable_at 0 f x \<longleftrightarrow> True"
| "k_times_Fr_differentiable_at (Suc k) f x \<longleftrightarrow>
     (\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. k_times_Fr_differentiable_at k f y))
   \<and> f differentiable (at x)
   \<and> (\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x)"

text \<open>\<open>1\<close>-times differentiable is Fréchet differentiable.\<close>

lemma one_times_Fr_iff:
  "k_times_Fr_differentiable_at 1 f x \<longleftrightarrow> f differentiable (at x)"
  by auto

text \<open>Monotonicity: higher differentiability implies lower.\<close>

lemma k_times_Fr_differentiable_at_mono:
  assumes "m \<le> k" and "k_times_Fr_differentiable_at k f x"
  shows   "k_times_Fr_differentiable_at m f x"
  using assms
proof (induction k arbitrary: m f x)
  case 0
  then have "m = 0" by simp
  then show ?case by simp
next
  case (Suc k)
  note IH = Suc.IH
  note asm = Suc.prems

  show ?case
  proof (cases m)
    case 0
    then show ?thesis by simp
  next
    case (Suc m')
    from asm(1) Suc have m'_le: "m' \<le> k"
      by simp

    from asm(2) obtain A where
      A: "open A"
         "x \<in> A"
         "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
      and fdiff: "f differentiable (at x)"
      and D: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
      by auto

    have A': "\<forall>y\<in>A. k_times_Fr_differentiable_at m' f y"
      using A(3) IH[OF m'_le] by blast

    have D': "\<forall>v. k_times_Fr_differentiable_at m' (\<lambda>y. frechet_derivative f (at y) v) x"
      using D IH[OF m'_le] by blast

    show ?thesis
      using Suc A fdiff D' A'
      by (metis IH asm(1,2) le_Suc_eq)
  qed
qed

text \<open>Peeling off the top layer.\<close>

lemma k_times_Fr_differentiable_at_SucD:
  assumes "k_times_Fr_differentiable_at (Suc k) f x"
  shows   "k_times_Fr_differentiable_at k f x"
    and   "f differentiable (at x)"
    and   "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
  using assms k_times_Fr_differentiable_at_mono
  by auto

text \<open>The derivative field inherits differentiability.\<close>

lemma k_times_Fr_differentiable_at_derivative:
  assumes "k_times_Fr_differentiable_at (Suc k) f x"
  shows   "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
  using assms by simp


subsection \<open>Set-wise \<open>k\<close>-times Fréchet differentiability\<close>

definition k_times_Fr_differentiable_on
  :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "k_times_Fr_differentiable_on k f S \<longleftrightarrow> (\<forall>x\<in>S. k_times_Fr_differentiable_at k f x)"

lemma k_times_Fr_differentiable_onI:
  "(\<And>x. x \<in> S \<Longrightarrow> k_times_Fr_differentiable_at k f x) \<Longrightarrow> k_times_Fr_differentiable_on k f S"
  by (simp add: k_times_Fr_differentiable_on_def)

lemma k_times_Fr_differentiable_onD:
  "k_times_Fr_differentiable_on k f S \<Longrightarrow> x \<in> S \<Longrightarrow> k_times_Fr_differentiable_at k f x"
  by (simp add: k_times_Fr_differentiable_on_def)

lemma k_times_Fr_differentiable_on_mono:
  "m \<le> k \<Longrightarrow> k_times_Fr_differentiable_on k f S \<Longrightarrow> k_times_Fr_differentiable_on m f S"
  by (simp add: k_times_Fr_differentiable_on_def k_times_Fr_differentiable_at_mono)

lemma k_times_Fr_differentiable_on_subset:
  "S \<subseteq> T \<Longrightarrow> k_times_Fr_differentiable_on k f T \<Longrightarrow> k_times_Fr_differentiable_on k f S"
  by (simp add: k_times_Fr_differentiable_on_def subset_iff)


subsection \<open>\<open>C\<^sup>k\<close> at a point (with continuity)\<close>

text \<open>
  \<open>Ck_at k f x\<close>: for \<open>k = 0\<close>, \<open>f\<close> is continuous at \<open>x\<close>; for \<open>Suc n\<close>, \<open>f\<close> is \<open>C\<^sup>n\<close>
  near \<open>x\<close>, differentiable at \<open>x\<close>, and every directional derivative is \<open>C\<^sup>n\<close> at \<open>x\<close>.
\<close>

primrec Ck_at
  :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "Ck_at 0 f x \<longleftrightarrow> continuous (at x) f"
| "Ck_at (Suc k) f x \<longleftrightarrow>
     (\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. Ck_at k f y))
   \<and> f differentiable (at x)
   \<and> (\<forall>v. Ck_at k (\<lambda>y. frechet_derivative f (at y) v) x)"


subsection \<open>\<open>C\<^sup>k\<close> on an open set\<close>

text \<open>\<open>C\<^sup>k\<close> on an open set; the multi-dimensional version of @{const C_k_on}.\<close>

definition Ck_on
  :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "Ck_on k f U \<longleftrightarrow> open U \<and> (\<forall>x\<in>U. Ck_at k f x)"


subsection \<open>Relationships between the three notions\<close>

text \<open>\<open>C\<^sup>k\<close> implies \<open>k\<close>-times differentiable (forgetting continuity).\<close>

lemma Ck_at_imp_k_times_Fr:
  "Ck_at k f x \<Longrightarrow> k_times_Fr_differentiable_at k f x"
  by (induction k arbitrary: f x) auto

corollary Ck_on_imp_k_times_Fr_on:
  "Ck_on k f U \<Longrightarrow> k_times_Fr_differentiable_on k f U"
  by (simp add: Ck_on_def k_times_Fr_differentiable_on_def Ck_at_imp_k_times_Fr)


subsection \<open>Basic properties of \<open>C\<^sup>k\<close> at a point and on an open set\<close>

lemma Ck_atI_Suc:
  assumes "open A" and "x \<in> A" and "\<And>y. y \<in> A \<Longrightarrow> Ck_at k f y"
    and "f differentiable (at x)"
    and "\<And>v. Ck_at k (\<lambda>y. frechet_derivative f (at y) v) x"
  shows "Ck_at (Suc k) f x"
  unfolding Ck_at.simps(2) using assms by blast

lemma Ck_at_SucE:
  assumes "Ck_at (Suc k) f x"
  obtains A where "open A" and "x \<in> A" and "\<forall>y\<in>A. Ck_at k f y"
    and "f differentiable (at x)"
    and "\<forall>v. Ck_at k (\<lambda>y. frechet_derivative f (at y) v) x"
  using assms unfolding Ck_at.simps(2) by blast

lemma Ck_at_imp_continuous: "Ck_at k f x \<Longrightarrow> continuous (at x) f"
  by (cases k) (auto intro: differentiable_imp_continuous_within)

lemma Ck_at_SucD:
  assumes "Ck_at (Suc k) f x"
  shows "Ck_at k f x"
  using assms
proof (induction k arbitrary: f x)
  case 0
  then show ?case
    by (auto intro: differentiable_imp_continuous_within)
next
  case (Suc k)
  from Suc.prems obtain A where A: "open A" "x \<in> A" "\<forall>y\<in>A. Ck_at (Suc k) f y"
    and d: "f differentiable (at x)"
    and D: "\<forall>v. Ck_at (Suc k) (\<lambda>y. frechet_derivative f (at y) v) x"
    by (rule Ck_at_SucE)
  show ?case
  proof (rule Ck_atI_Suc[OF A(1,2) _ d])
    show "Ck_at k f y" if "y \<in> A" for y
      using A(3) that by (blast intro: Suc.IH)
    show "Ck_at k (\<lambda>y. frechet_derivative f (at y) v) x" for v
      using D by (blast intro: Suc.IH)
  qed
qed

lemma Ck_at_mono:
  assumes "Ck_at k f x" and "m \<le> k"
  shows "Ck_at m f x"
  using assms
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case
    using Ck_at_SucD le_Suc_eq by blast
qed

text \<open>A transfer principle: \<open>Ck_at k f x\<close> only depends on the values of \<open>f\<close> on an open
  neighbourhood of \<open>x\<close>.\<close>

lemma Ck_at_transfer_open:
  assumes "open U" and "x \<in> U" and "\<And>y. y \<in> U \<Longrightarrow> f y = g y"
    and "Ck_at k f x"
  shows "Ck_at k g x"
  using assms
proof (induction k arbitrary: f g x)
  case 0
  have "\<forall>\<^sub>F y in nhds x. f y = g y"
    using "0.prems"(1-3) by (auto simp: eventually_nhds)
  then show ?case
    using "0.prems"(4) isCont_cong by auto
next
  case (Suc k)
  from Suc.prems(4) obtain A where A: "open A" "x \<in> A" "\<forall>y\<in>A. Ck_at k f y"
    and d: "f differentiable (at x)"
    and D: "\<forall>v. Ck_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    by (rule Ck_at_SucE)
  have eq_der: "frechet_derivative f (at y) = frechet_derivative g (at y)" if "y \<in> U" for y
    using Suc.prems using frechet_derivative_transform_within_open that by blast
  show ?case
  proof (rule Ck_atI_Suc)
    show "open (A \<inter> U)" and "x \<in> A \<inter> U"
      using A(1,2) Suc.prems(1,2) by auto
    show "Ck_at k g y" if "y \<in> A \<inter> U" for y
      using that A(3) Suc.IH[where f = f and g = g, OF Suc.prems(1) _ Suc.prems(3)] by blast
    show "g differentiable (at x)"
      using d Suc.prems(1-3) by (rule differentiable_transform_within_open)
    show "Ck_at k (\<lambda>y. frechet_derivative g (at y) v) x" for v
      by (rule Suc.IH[OF Suc.prems(1,2) _ D[rule_format, of v]]) (simp add: eq_der)
  qed
qed

lemma Ck_onI: "open U \<Longrightarrow> (\<And>x. x \<in> U \<Longrightarrow> Ck_at k f x) \<Longrightarrow> Ck_on k f U"
  by (simp add: Ck_on_def)

lemma Ck_on_open: "Ck_on k f U \<Longrightarrow> open U"
  by (simp add: Ck_on_def)

lemma Ck_onD: "Ck_on k f U \<Longrightarrow> x \<in> U \<Longrightarrow> Ck_at k f x"
  by (simp add: Ck_on_def)

lemma Ck_on_mono:
  assumes "Ck_on k f U" and "m \<le> k"
  shows "Ck_on m f U"
  using assms unfolding Ck_on_def by (blast intro: Ck_at_mono)

lemma Ck_on_SucD: "Ck_on (Suc k) f U \<Longrightarrow> Ck_on k f U"
  by (erule Ck_on_mono) simp

lemma Ck_on_subset:
  assumes "Ck_on k f U" and "open V" and "V \<subseteq> U"
  shows "Ck_on k f V"
  using assms unfolding Ck_on_def by blast

lemma Ck_on_imp_continuous_on: "Ck_on k f U \<Longrightarrow> continuous_on U f"
  unfolding Ck_on_def by (auto simp: continuous_on_eq_continuous_at intro: Ck_at_imp_continuous)

lemma Ck_on_cong:
  assumes "U = V" and "\<And>x. x \<in> V \<Longrightarrow> f x = g x"
  shows "Ck_on k f U \<longleftrightarrow> Ck_on k g V"
proof -
  have sym: "\<And>x. x \<in> V \<Longrightarrow> g x = f x"
    using assms(2) by simp
  have "Ck_at k f x \<longleftrightarrow> Ck_at k g x" if V: "open V" "x \<in> V" for x
    using Ck_at_transfer_open[of V x f g k, OF V assms(2)]
      Ck_at_transfer_open[of V x g f k, OF V sym] by blast
  then show ?thesis
    using assms(1) unfolding Ck_on_def by blast
qed

lemma Ck_on_congI:
  assumes "Ck_on k g U" and "\<And>x. x \<in> U \<Longrightarrow> f x = g x"
  shows "Ck_on k f U"
  using Ck_on_cong[of U U f g k, OF refl assms(2)] assms(1) by simp

text \<open>On open sets, \<open>C\<^sup>k\<close> satisfies the recursion below.  The closure properties are proved by
  induction along it, following the treatment of \<open>higher_differentiable_on\<close> in the AFP
  entry \<^emph>\<open>Smooth Manifolds\<close> by Immler and Zhan.\<close>

lemma Ck_on_0_iff: "Ck_on 0 f U \<longleftrightarrow> open U \<and> continuous_on U f"
  by (auto simp: Ck_on_def continuous_on_eq_continuous_at)

lemma Ck_on_of_derivatives:
  assumes U: "open U"
    and d: "\<And>x. x \<in> U \<Longrightarrow> f differentiable (at x)"
    and D: "\<And>v. Ck_on k (\<lambda>x. frechet_derivative f (at x) v) U"
  shows "Ck_on k f U"
  using d D
proof (induction k arbitrary: f)
  case 0
  then show ?case
    using U by (auto simp: Ck_on_def intro: differentiable_imp_continuous_within)
next
  case (Suc k)
  have Ck: "Ck_on k f U"
    by (rule Suc.IH) (use Suc.prems in \<open>auto intro: Ck_on_SucD\<close>)
  show ?case
  proof (rule Ck_onI[OF U])
    fix x assume x: "x \<in> U"
    show "Ck_at (Suc k) f x"
    proof (rule Ck_atI_Suc[OF U x])
      show "Ck_at k f y" if "y \<in> U" for y
        using Ck that by (rule Ck_onD)
      show "f differentiable (at x)"
        using x by (rule Suc.prems(1))
      show "Ck_at k (\<lambda>y. frechet_derivative f (at y) v) x" for v
        by (rule Ck_at_SucD[OF Ck_onD[OF Suc.prems(2) x]])
    qed
  qed
qed

lemma Ck_on_Suc_iff:
  "Ck_on (Suc k) f U \<longleftrightarrow>
     open U \<and> (\<forall>x\<in>U. f differentiable (at x)) \<and>
     (\<forall>v. Ck_on k (\<lambda>x. frechet_derivative f (at x) v) U)"
proof
  assume "Ck_on (Suc k) f U"
  then show "open U \<and> (\<forall>x\<in>U. f differentiable (at x)) \<and>
      (\<forall>v. Ck_on k (\<lambda>x. frechet_derivative f (at x) v) U)"
    by (auto simp: Ck_on_def)
next
  assume "open U \<and> (\<forall>x\<in>U. f differentiable (at x)) \<and>
      (\<forall>v. Ck_on k (\<lambda>x. frechet_derivative f (at x) v) U)"
  then have U: "open U" and d: "\<And>x. x \<in> U \<Longrightarrow> f differentiable (at x)"
    and D: "\<And>v. Ck_on k (\<lambda>x. frechet_derivative f (at x) v) U"
    by auto
  have Ck: "Ck_on k f U"
    using U d D by (rule Ck_on_of_derivatives)
  show "Ck_on (Suc k) f U"
  proof (rule Ck_onI[OF U])
    fix x assume x: "x \<in> U"
    show "Ck_at (Suc k) f x"
      by (rule Ck_atI_Suc[OF U x Ck_onD[OF Ck] d[OF x] Ck_onD[OF D x]])
  qed
qed


subsection \<open>Bridge to the one-dimensional theory\<close>

text \<open>For \<open>f :: real \<Rightarrow> real\<close>, the two notions of \<open>k\<close>-times differentiability agree.\<close>


text \<open>Being \<open>k\<close>-times differentiable at \<open>x\<close> only depends on the function near \<open>x\<close>.\<close>

lemma k_times_differentiable_at_transfer_open:
  fixes f g :: "real \<Rightarrow> real"
  assumes U: "open U" "x \<in> U"
    and eq: "\<And>y. y \<in> U \<Longrightarrow> f y = g y"
    and Hf: "k_times_differentiable_at k f x"
  shows "k_times_differentiable_at k g x"
  using U eq Hf
proof (induction k arbitrary: f g x U)
  case 0
  then show ?case by simp
next
  case (Suc k)

  text \<open>Unfold the definition at \<open>x\<close>.\<close>
  from Suc.prems(4) obtain \<epsilon> where \<epsilon>pos: "\<epsilon> > 0"
    and ball_f: "\<And>y. \<bar>y - x\<bar> < \<epsilon> \<Longrightarrow> k_times_differentiable_at k f y"
    and der_f: "((deriv ^^ k) f
                   has_derivative (\<lambda>h. (deriv ^^ Suc k) f x * h)) (at x)"
    by auto

  text \<open>Shrink the ball so that it sits inside \<open>U\<close>, where \<open>f = g\<close>.\<close>
  obtain \<delta> where \<delta>pos: "\<delta> > 0" and ballU: "ball x \<delta> \<subseteq> U"
    using Suc.prems(1,2) open_contains_ball by blast
  define r where "r = min \<epsilon> \<delta>"
  have rpos: "r > 0" using \<epsilon>pos \<delta>pos by (simp add: r_def)

  define B where "B = ball x r"
  have openB: "open B" and xB: "x \<in> B" using rpos by (auto simp: B_def)
  have BsubU: "B \<subseteq> U"
    using ballU by (auto simp: B_def r_def dist_real_def abs_minus_commute)
  have eqB: "\<forall>y\<in>B. f y = g y" using BsubU Suc.prems(3) by auto

  text \<open>On \<open>B\<close> the function \<open>f\<close> is \<open>k\<close>-times differentiable.\<close>
  have f_on_B: "f k-times_differentiable_on B"
    by (rule k_times_differentiable_onI)
       (auto simp: B_def r_def dist_real_def abs_minus_commute intro!: ball_f)

  text \<open>Transfer this to \<open>g\<close> and obtain agreement of the lower derivatives.\<close>
  have g_on_B: "g k-times_differentiable_on B"
   and der_agree: "\<forall>y\<in>B. \<forall>m<k. ((deriv ^^ m) g
                       has_derivative (*) ((deriv ^^ Suc m) f y)) (at y)"
    using times_differentiable_on_transfer[OF openB f_on_B eqB] by blast+

  text \<open>Part 1: the \<open>\<epsilon>\<close>-ball condition for \<open>g\<close> (radius \<open>r\<close>).\<close>
  have ball_g: "\<forall>y. \<bar>y - x\<bar> < r \<longrightarrow> k_times_differentiable_at k g y"
    using g_on_B
    by (auto simp: k_times_differentiable_on_def B_def dist_real_def abs_minus_commute)

  text \<open>Part 2: the \<open>k\<close>-th derivatives of \<open>f\<close> and \<open>g\<close> coincide on \<open>B\<close>.\<close>
  have kth_eq: "\<forall>y\<in>B. (deriv ^^ k) f y = (deriv ^^ k) g y"
  proof (cases k)
    case 0
    then show ?thesis using eqB by simp
  next
    case (Suc n)
    show ?thesis
    proof
      fix y assume yB: "y \<in> B"
      have "((deriv ^^ n) g has_derivative (*) ((deriv ^^ Suc n) f y)) (at y)"
        using der_agree yB Suc by simp
      hence "deriv ((deriv ^^ n) g) y = (deriv ^^ Suc n) f y"
        by (rule deriv_eq)
      thus "(deriv ^^ k) f y = (deriv ^^ k) g y"
        using Suc by simp
    qed
  qed

  text \<open>Transfer the derivative condition at \<open>x\<close> from \<open>f\<close> to \<open>g\<close>.\<close>
  have der_f': "((deriv ^^ k) f has_derivative (*) ((deriv ^^ Suc k) f x)) (at x)"
    using der_f by simp
  have der_g': "((deriv ^^ k) g has_derivative (*) ((deriv ^^ Suc k) f x)) (at x)"
    using has_derivative_transfer_on_open[OF openB xB _ der_f'] kth_eq by blast
  have kSuc_eq: "(deriv ^^ Suc k) g x = (deriv ^^ Suc k) f x"
    using der_g' by (simp add: deriv_eq)

  have der_g: "((deriv ^^ k) g
                  has_derivative (\<lambda>h. (deriv ^^ Suc k) g x * h)) (at x)"
    using der_g' kSuc_eq by simp

  show "k_times_differentiable_at (Suc k) g x"
    using \<epsilon>pos rpos ball_g der_g by auto
qed

lemma eq_on_open_k_times_differentiable_at:
  fixes f g :: "real \<Rightarrow> real"
  assumes U: "open U" "x \<in> U"
    and eq: "\<And>y. y \<in> U \<Longrightarrow> f y = g y"
  shows "k_times_differentiable_at k f x \<longleftrightarrow> k_times_differentiable_at k g x"
  using k_times_differentiable_at_transfer_open[OF U eq]
        k_times_differentiable_at_transfer_open[OF U(1,2), of g f k] eq
  by auto

lemma k_times_differentiable_at_cmult:
  fixes f :: "real \<Rightarrow> real"
  shows "k_times_differentiable_at k f x \<Longrightarrow>
         k_times_differentiable_at k (\<lambda>y. c * f y) x"
  by (rule kth_deriv_cmultE)



lemma k_times_Fr_real_iff:
  fixes f :: "real \<Rightarrow> real"
  shows "k_times_Fr_differentiable_at k f x \<longleftrightarrow> k_times_differentiable_at k f x"
proof (induction k arbitrary: f x)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof
    assume H: "k_times_Fr_differentiable_at (Suc k) f x"

    from H obtain A where
      A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
      and df: "f differentiable (at x)"
      and D: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
      unfolding k_times_Fr_differentiable_at.simps(2)
      by blast

    have neigh: "\<forall>y\<in>A. k_times_differentiable_at k f y"
      using A(3) Suc.IH by blast

    have dk: "k_times_differentiable_at k (deriv f) x"
    proof (cases k)
      case 0
      then show ?thesis by simp
    next
      case (Suc j)

      have H1: "k_times_Fr_differentiable_at (Suc j)
                  (\<lambda>y. frechet_derivative f (at y) 1) x"
        using D Suc by simp
      then have dk1:
        "k_times_differentiable_at (Suc j)
           (\<lambda>y. frechet_derivative f (at y) 1) x"
        using Suc.IH Suc by blast

      have eq_deriv: "\<And>y. y \<in> A \<Longrightarrow> frechet_derivative f (at y) 1 = deriv f y"
        using A(3) Suc frechet_derivative_one_eq_deriv k_times_Fr_differentiable_at.simps(2) by blast


      have "k_times_differentiable_at (Suc j)
              (\<lambda>y. frechet_derivative f (at y) 1) x \<longleftrightarrow>
            k_times_differentiable_at (Suc j) (deriv f) x"
        using A(1,2) eq_deriv eq_on_open_k_times_differentiable_at by presburger
      then show ?thesis
        using Suc dk1 by blast
    qed

    show "k_times_differentiable_at (Suc k) f x"
    proof -
      obtain \<epsilon> where \<epsilon>pos: "\<epsilon> > 0" and ballA: "ball x \<epsilon> \<subseteq> A"
        using A(1,2) open_contains_ball by blast
      have part1: "\<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at k f y"
        using ballA neigh by (auto simp: dist_real_def abs_minus_commute,
                               simp add: dist_norm subsetD)
      have diffk: "(deriv ^^ k) f differentiable (at x)"
      proof (cases k)
        case 0
        then show ?thesis using df by simp
      next
        case (Suc j)
        from dk Suc have d: "(deriv f) (Suc j)-times_differentiable_at x" by simp
        have "((deriv ^^ j) (deriv f)
                 has_real_derivative (deriv ^^ Suc j) (deriv f) x) (at x)"
          using k_times_differentiable_at_le_deriv(2)[OF d lessI] .
        then have "(deriv ^^ j) (deriv f) differentiable (at x)"
          using real_differentiable_def by blast
        then show ?thesis
          using Suc kth_deriv_shift by metis
      qed
      have part2: "((deriv ^^ k) f
                      has_derivative (\<lambda>h. (deriv ^^ Suc k) f x * h)) (at x)"
      proof -
        from diffk have "((deriv ^^ k) f
                 has_real_derivative deriv ((deriv ^^ k) f) x) (at x)"
          using DERIV_deriv_iff_real_differentiable by blast
        then show ?thesis
          by (simp add: has_field_derivative_def)
      qed
      show ?thesis
        using \<epsilon>pos part1 part2 by auto
    qed
  next
    assume H: "k_times_differentiable_at (Suc k) f x"

    from H obtain \<epsilon> where \<epsilon>pos: "\<epsilon> > 0"
      and ball_f: "\<And>y. \<bar>y - x\<bar> < \<epsilon> \<Longrightarrow> k_times_differentiable_at k f y"
      by auto
    define A where "A = ball x \<epsilon>"
    have A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_differentiable_at k f y"
      using \<epsilon>pos ball_f by (auto simp: A_def dist_real_def abs_minus_commute)
    have df: "f differentiable (at x)"
    proof -
      have "f 1-times_differentiable_at x"
        using H k_times_differentiable_at_mono[of 1 "Suc k" f x] by simp
      then show ?thesis
        by (metis one_time_differentiable_at_iff real_differentiable_def)
    qed
    have dk: "k_times_differentiable_at k (deriv f) x"
      using k_times_differentiable_at_derivative[OF H] by simp

    have neigh: "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
      using A(3) Suc.IH by blast

    have D: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    proof
      fix v
      show "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
      proof (cases k)
        case 0
        then show ?thesis by simp
      next
        case (Suc j)

        have dk': "k_times_differentiable_at (Suc j) (\<lambda>y. v * deriv f y) x"
          using dk Suc k_times_differentiable_at_cmult[of "Suc j" "deriv f" x v]
          by blast
        hence dk'': "k_times_differentiable_at (Suc j) (\<lambda>y. deriv f y * v) x"
          by (simp add: mult.commute)

        have eq_deriv: "\<And>y. y \<in> A \<Longrightarrow> frechet_derivative f (at y) v = deriv f y * v"
          using Suc frechet_derivative_to_deriv neigh by auto

        have "k_times_differentiable_at (Suc j)
                (\<lambda>y. frechet_derivative f (at y) v) x \<longleftrightarrow>
              k_times_differentiable_at (Suc j) (\<lambda>y. deriv f y * v) x"
          using A(1,2) eq_deriv eq_on_open_k_times_differentiable_at by presburger
        then have "k_times_differentiable_at (Suc j)
                     (\<lambda>y. frechet_derivative f (at y) v) x"
          using dk'' by blast
        then show ?thesis
          using Suc Suc.IH by blast
      qed
    qed

    show "k_times_Fr_differentiable_at (Suc k) f x"
      unfolding k_times_Fr_differentiable_at.simps(2)
      using A(1,2) neigh df D by blast
  qed
qed



subsection \<open>Basic closure properties\<close>

text \<open>These generalise the one-dimensional closure results for @{const C_k_on}.\<close>

lemma k_times_Fr_const:
  "k_times_Fr_differentiable_at k (\<lambda>_. c) x"
proof (induction k arbitrary: x c)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. k_times_Fr_differentiable_at k (\<lambda>_. c) y)"
    using Suc.IH by (intro exI[of _ UNIV]) auto
  moreover have "(\<lambda>_. c) differentiable (at x)"
    by simp
  moreover have "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative (\<lambda>_. c) (at y) v) x"
    by (simp add: Suc)
  ultimately show ?case
    by simp
qed

lemma k_times_Fr_id:
  "k_times_Fr_differentiable_at k (\<lambda>x. x) x"
proof (induction k arbitrary: x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have nbhd:
    "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. k_times_Fr_differentiable_at k (\<lambda>x. x) y)"
    using Suc.IH by (intro exI[of _ UNIV]) auto
  have diff: "(\<lambda>x. x) differentiable (at x)"
    by simp
  have derivs: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative (\<lambda>x. x) (at y) v) x"
    by (simp add: k_times_Fr_const)
  show ?case
    using nbhd diff derivs
    by simp
qed

lemma Ck_at_const:
  "Ck_at k (\<lambda>_. c) x"
proof (induction k arbitrary: x c)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have nbhd: "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. Ck_at k (\<lambda>_. c) y)"
    using Suc.IH by (intro exI[of _ UNIV]) auto

  have diff: "(\<lambda>_. c) differentiable (at x)"
    by simp

  have derivs: "\<forall>v. Ck_at k (\<lambda>y. frechet_derivative (\<lambda>_. c) (at y) v) x"
    by (simp add: Suc)

  show ?case
    using nbhd diff derivs
    by simp
qed

lemma Ck_on_const:
  "open U \<Longrightarrow> Ck_on k (\<lambda>_. c) U"
  by (simp add: Ck_on_def Ck_at_const)

text \<open>
  As in the one-dimensional case, the forward implication is proved by
  induction and the equivalence follows by symmetry of the hypotheses.
\<close>

lemma k_times_Fr_differentiable_at_transfer_open:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes U: "open U" "x \<in> U"
    and eq: "\<And>y. y \<in> U \<Longrightarrow> f y = g y"
    and Hf: "k_times_Fr_differentiable_at k f x"
  shows "k_times_Fr_differentiable_at k g x"
  using U eq Hf
proof (induction k arbitrary: f g x U)
  case 0
  then show ?case by simp
next
  case (Suc k)

  from Suc.prems(4) obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
    and df: "f differentiable (at x)"
    and Df: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    by blast

  let ?C = "A \<inter> U"
  have C: "open ?C" "x \<in> ?C"
    using A Suc.prems by auto

  have neigh: "\<forall>y\<in>?C. k_times_Fr_differentiable_at k g y"
    by (metis A(3) Int_iff Suc.IH Suc.prems(1,3))
  have evx: "eventually (\<lambda>y. y \<in> U) (nhds x)"
    using Suc.prems(1,2) by (simp add: eventually_nhds, auto)
  have evx_fg: "eventually (\<lambda>y. f y = g y) (nhds x)"
    by (rule eventually_mono[OF evx]) (use Suc.prems(3) in auto)


  have dg: "g differentiable (at x)"
    by (metis Suc.prems(1,2,3) df differentiable_transform_within_open)

  have Dg: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
  proof
    fix v
    show "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
    proof (cases k)
      case 0
      then show ?thesis by simp
    next
      case (Suc j)

      have eqD:
        "\<And>y. y \<in> ?C \<Longrightarrow> frechet_derivative f (at y) v = frechet_derivative g (at y) v"
      proof -
        fix y
        assume yC: "y \<in> ?C"
        hence yA: "y \<in> A" and yU: "y \<in> U"
          by auto

        have fy: "k_times_Fr_differentiable_at (Suc j) f y"
          using A(3) Suc yA by blast

        hence dfy: "f differentiable (at y)"
          using k_times_Fr_differentiable_at_mono[of 1 "Suc j" f y]
          by (simp add: one_times_Fr_iff)

        have gy: "k_times_Fr_differentiable_at (Suc j) g y"
          using Suc neigh yC by blast

        hence dgy: "g differentiable (at y)"
          using k_times_Fr_differentiable_at_mono[of 1 "Suc j" g y]
          by (simp add: one_times_Fr_iff)

        have evy: "eventually (\<lambda>z. f z = g z) (nhds y)"
          using Suc.prems(1) yU Suc.prems(3)
          by (simp add: eventually_nhds, auto)

        have "(f has_derivative frechet_derivative f (at y)) (at y)"
          by (simp add: dfy frechet_derivative_works[THEN iffD1])
        then have "(g has_derivative frechet_derivative f (at y)) (at y)"
          using Suc.prems(1,3) has_derivative_transfer_on_open yU by blast
        moreover have "(g has_derivative frechet_derivative g (at y)) (at y)"
          using dgy frechet_derivative_works[THEN iffD1] by blast
        ultimately have "frechet_derivative f (at y) = frechet_derivative g (at y)"
          by (rule has_derivative_unique)
        then show "frechet_derivative f (at y) v = frechet_derivative g (at y) v"
          by simp
      qed

      have "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
        using Df by blast
      then show ?thesis
        using Suc.IH[OF C(1,2), of
            "\<lambda>y. frechet_derivative f (at y) v"
            "\<lambda>y. frechet_derivative g (at y) v"]
          eqD
        by blast
    qed
  qed

  show "k_times_Fr_differentiable_at (Suc k) g x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    using C neigh dg Dg by blast
qed

lemma eq_on_open_k_times_Fr_differentiable_at:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes U: "open U" "x \<in> U"
    and eq: "\<And>y. y \<in> U \<Longrightarrow> f y = g y"
  shows "k_times_Fr_differentiable_at k f x \<longleftrightarrow> k_times_Fr_differentiable_at k g x"
  using k_times_Fr_differentiable_at_transfer_open[OF U eq]
        k_times_Fr_differentiable_at_transfer_open[OF U(1,2), of g f k] eq
  by auto

lemma k_times_Fr_add:
  assumes "k_times_Fr_differentiable_at k f x"
      and "k_times_Fr_differentiable_at k g x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. f y + g y) x"
  using assms
proof (induction k arbitrary: f g x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  from Suc.prems(1) obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
    and df: "f differentiable (at x)"
    and Df: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    by blast

  from Suc.prems(2) obtain B where
    B: "open B" "x \<in> B" "\<forall>y\<in>B. k_times_Fr_differentiable_at k g y"
    and dg: "g differentiable (at x)"
    and Dg: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    by blast

  let ?C = "A \<inter> B"
  have C: "open ?C" "x \<in> ?C"
    using A B by auto

  have neigh: "\<forall>y\<in>?C. k_times_Fr_differentiable_at k (\<lambda>z. f z + g z) y"
  proof
    fix y
    assume yC: "y \<in> ?C"
    then have yA: "y \<in> A" and yB: "y \<in> B"
      by auto
    show "k_times_Fr_differentiable_at k (\<lambda>z. f z + g z) y"
      using Suc.IH A(3)[rule_format, OF yA] B(3)[rule_format, OF yB] by blast
  qed

  have diff: "(\<lambda>y. f y + g y) differentiable (at x)"
    by (simp add: df dg)
  have Dsum:"\<forall>v. k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. f z + g z) (at y) v) x"
  proof
    fix v
    show "k_times_Fr_differentiable_at k
            (\<lambda>y. frechet_derivative (\<lambda>z. f z + g z) (at y) v) x"
    proof (cases k)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc j)

      have ksum:
        "k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative f (at y) v + frechet_derivative g (at y) v) x"
        using Suc.IH Df Dg by blast

      have eqD:
        "\<And>y. y \<in> ?C \<Longrightarrow>
          frechet_derivative (\<lambda>z. f z + g z) (at y) v =
          frechet_derivative f (at y) v + frechet_derivative g (at y) v"
      proof -
        fix y
        assume yC: "y \<in> ?C"
        then have yA: "y \<in> A" and yB: "y \<in> B"
          by auto

        have fy: "k_times_Fr_differentiable_at (Suc j) f y"
          using A(3) Suc yA by blast

        have gy: "k_times_Fr_differentiable_at (Suc j) g y"
          using B(3) Suc yB by blast


        have dfy: "f differentiable (at y)"
          using fy k_times_Fr_differentiable_at_mono[of 1 "Suc j" f y]
          by (simp add: one_times_Fr_iff)

        have dgy: "g differentiable (at y)"
          using gy k_times_Fr_differentiable_at_mono[of 1 "Suc j" g y]
          by (simp add: one_times_Fr_iff)

        have hder: "((\<lambda>z. f z + g z) has_derivative
             (\<lambda>h. frechet_derivative f (at y) h + frechet_derivative g (at y) h)) (at y)"
          by (simp add: dfy dgy frechet_derivative_works[THEN iffD1])

        then have "frechet_derivative (\<lambda>z. f z + g z) (at y) =
              (\<lambda>h. frechet_derivative f (at y) h + frechet_derivative g (at y) h)"
          using frechet_derivative_at[symmetric] by blast
        then show
          "frechet_derivative (\<lambda>z. f z + g z) (at y) v =
           frechet_derivative f (at y) v + frechet_derivative g (at y) v"
          by simp
      qed

      have
        "k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. f z + g z) (at y) v) x \<longleftrightarrow>
         k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative f (at y) v + frechet_derivative g (at y) v) x"
        by (smt (verit) C(1,2) eqD eq_on_open_k_times_Fr_differentiable_at)
      then show ?thesis
        using ksum by blast
    qed
  qed
  show ?case
    unfolding k_times_Fr_differentiable_at.simps(2)
    using C neigh diff Dsum by blast
qed

lemma k_times_Fr_scaleR:
  assumes "k_times_Fr_differentiable_at k f x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. c *\<^sub>R f y) x"
  using assms
proof (induction k arbitrary: f x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  from Suc.prems obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
    and df: "f differentiable (at x)"
    and Df: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    by blast

  have neigh: "\<forall>y\<in>A. k_times_Fr_differentiable_at k (\<lambda>z. c *\<^sub>R f z) y"
    using A(3) Suc.IH by blast

  have diff: "(\<lambda>y. c *\<^sub>R f y) differentiable (at x)"
    by (simp add: df)

  have Dscale: "\<forall>v. k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v) x"
  proof
    fix v
    show "k_times_Fr_differentiable_at k
            (\<lambda>y. frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v) x"
    proof (cases k)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc j)

      have kscaled:
        "k_times_Fr_differentiable_at k
           (\<lambda>y. c *\<^sub>R frechet_derivative f (at y) v) x"
        using Suc.IH Df by blast

      have eqD:
        "\<And>y. y \<in> A \<Longrightarrow>
          frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v =
          c *\<^sub>R frechet_derivative f (at y) v"
      proof -
        fix y
        assume yA: "y \<in> A"

        have fy: "k_times_Fr_differentiable_at (Suc j) f y"
          using A(3) Suc yA by blast

        hence dfy: "f differentiable (at y)"
          using k_times_Fr_differentiable_at_mono[of 1 "Suc j" f y]
          by (simp add: one_times_Fr_iff)

        have hder: "((\<lambda>z. c *\<^sub>R f z) has_derivative (\<lambda>h. c *\<^sub>R frechet_derivative f (at y) h)) (at y)"
          by (simp add: dfy frechet_derivative_works[THEN iffD1] has_derivative_scaleR_right)

        have "frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) = (\<lambda>h. c *\<^sub>R frechet_derivative f (at y) h)"
          by (metis frechet_derivative_at hder)
        then show "frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v =  c *\<^sub>R frechet_derivative f (at y) v"
          by simp
      qed

      have  "k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v) x \<longleftrightarrow>
         k_times_Fr_differentiable_at k
           (\<lambda>y. c *\<^sub>R frechet_derivative f (at y) v) x"
        by (smt (verit) A(1,2) eqD eq_on_open_k_times_Fr_differentiable_at)
      then show ?thesis
        using kscaled by blast
    qed
  qed

  show ?case
    unfolding k_times_Fr_differentiable_at.simps(2)
    using A(1,2) neigh diff Dscale by blast
qed

lemma Ck_on_add:
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. f y + g y) U"
  using assms
proof (induction k arbitrary: f g)
  case 0
  then show ?case
    by (auto simp: Ck_on_0_iff intro: continuous_intros)
next
  case (Suc k)
  from Suc.prems have U: "open U"
    and df: "\<And>x. x \<in> U \<Longrightarrow> f differentiable (at x)"
    and dg: "\<And>x. x \<in> U \<Longrightarrow> g differentiable (at x)"
    and Df: "\<And>v. Ck_on k (\<lambda>x. frechet_derivative f (at x) v) U"
    and Dg: "\<And>v. Ck_on k (\<lambda>x. frechet_derivative g (at x) v) U"
    by (auto simp: Ck_on_Suc_iff)
  show ?case
    unfolding Ck_on_Suc_iff
    using U df dg Suc.IH[OF Df Dg]
    by (auto simp: frechet_derivative_add cong: Ck_on_cong)
qed

text \<open>A bounded bilinear operation preserves \<open>C\<^sup>k\<close>; this covers products, scalar
  multiplication and inner products.\<close>

lemma Ck_on_bilinear:
  assumes P: "bounded_bilinear P" and "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. P (f y) (g y)) U"
  using assms(2,3)
proof (induction k arbitrary: f g)
  case 0
  then show ?case
    by (auto simp: Ck_on_0_iff intro: bounded_bilinear.continuous_on[OF P])
next
  case (Suc k)
  from Suc.prems have U: "open U"
    and df: "\<And>x. x \<in> U \<Longrightarrow> f differentiable (at x)"
    and dg: "\<And>x. x \<in> U \<Longrightarrow> g differentiable (at x)"
    and Df: "\<And>v. Ck_on k (\<lambda>x. frechet_derivative f (at x) v) U"
    and Dg: "\<And>v. Ck_on k (\<lambda>x. frechet_derivative g (at x) v) U"
    by (auto simp: Ck_on_Suc_iff)
  have fk: "Ck_on k f U" and gk: "Ck_on k g U"
    using Suc.prems by (auto intro: Ck_on_SucD)
  have dP: "(\<lambda>y. P (f y) (g y)) differentiable (at x)" if "x \<in> U" for x
    using bounded_bilinear.FDERIV[OF P frechet_derivative_works[THEN iffD1, OF df[OF that]]
        frechet_derivative_works[THEN iffD1, OF dg[OF that]]]
    unfolding differentiable_def by blast
  show ?case
    unfolding Ck_on_Suc_iff
    using U dP Ck_on_add[OF Suc.IH[OF fk Dg] Suc.IH[OF Df gk]]
    by (auto simp: frechet_derivative_bilinear[OF P] df dg cong: Ck_on_cong)
qed

lemma Ck_on_sum:
  fixes F :: "'i \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes fin: "finite I"
      and ne: "I \<noteq> {}"
      and Ck: "\<And>i. i \<in> I \<Longrightarrow> Ck_on k (F i) U"
  shows "Ck_on k (\<lambda>y. \<Sum>i\<in>I. F i y) U"
  using fin ne Ck
proof (induction rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert i I)
  have Ci: "Ck_on k (F i) U"
    using insert.prems by simp
  show ?case
  proof (cases "I = {}")
    case True
    then show ?thesis
      using Ci insert.hyps by simp
  next
    case False
    have CI: "Ck_on k (\<lambda>y. \<Sum>j\<in>I. F j y) U"
      using insert.IH[OF False] insert.prems by blast
    show ?thesis
      using Ck_on_add[OF Ci CI] insert.hyps by simp
  qed
qed

lemma Ck_on_scaleR:
  assumes "Ck_on k f U"
  shows "Ck_on k (\<lambda>y. c *\<^sub>R f y) U"
  using Ck_on_bilinear[OF bounded_bilinear_scaleR Ck_on_const[OF Ck_on_open[OF assms]] assms] .

lemma Ck_on_id:
  "open U \<Longrightarrow> Ck_on k (\<lambda>x. x) U"
proof (induction k)
  case 0
  then show ?case by (simp add: Ck_on_0_iff)
next
  case (Suc k)
  then show ?case by (simp add: Ck_on_Suc_iff Ck_on_const)
qed

lemma Ck_on_neg:
  assumes "Ck_on k f U"
  shows "Ck_on k (\<lambda>y. - f y) U"
proof -
  have "Ck_on k (\<lambda>y. (-1) *\<^sub>R f y) U"
    by (rule Ck_on_scaleR[OF assms])
  thus ?thesis by simp
qed

lemma Ck_on_sub:
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. f y - g y) U"
proof -
  have "Ck_on k (\<lambda>y. f y + (- g y)) U"
    by (rule Ck_on_add[OF assms(1) Ck_on_neg[OF assms(2)]])
  thus ?thesis by simp
qed

lemma Ck_on_mult:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. f y * g y) U"
  using Ck_on_bilinear[OF bounded_bilinear_mult assms] .

lemma Ck_on_pow:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "Ck_on k f U"
  shows "Ck_on k (\<lambda>y. (f y) ^ n) U"
proof (induction n)
  case 0
  have "open U" using assms by (simp add: Ck_on_def)
  then show ?case
    using Ck_on_const by simp
next
  case (Suc n)
  have "Ck_on k (\<lambda>y. f y * (f y) ^ n) U"
    by (rule Ck_on_mult[OF assms Suc])
  thus ?case by (simp add: power_Suc2)
qed

lemma Ck_on_inverse:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_field"
  assumes "Ck_on k f U" and "\<And>y. y \<in> U \<Longrightarrow> f y \<noteq> 0"
  shows "Ck_on k (\<lambda>y. inverse (f y)) U"
  using assms
proof (induction k arbitrary: f)
  case 0
  then show ?case
    by (auto simp: Ck_on_0_iff intro!: continuous_on_inverse)
next
  case (Suc k)
  from Suc.prems(1) have U: "open U"
    and df: "\<And>x. x \<in> U \<Longrightarrow> f differentiable (at x)"
    and Df: "\<And>v. Ck_on k (\<lambda>x. frechet_derivative f (at x) v) U"
    by (auto simp: Ck_on_Suc_iff)
  have inv: "Ck_on k (\<lambda>y. inverse (f y)) U"
    using Ck_on_SucD[OF Suc.prems(1)] Suc.prems(2) by (rule Suc.IH)
  have D: "Ck_on k (\<lambda>x. - (inverse (f x) * frechet_derivative f (at x) v * inverse (f x))) U"
    for v
    by (intro Ck_on_neg Ck_on_mult inv Df)
  show ?case
    unfolding Ck_on_Suc_iff
    using U df Suc.prems(2) D
    by (auto simp: frechet_derivative_inverse cong: Ck_on_cong)
qed

lemma Ck_on_divide:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "Ck_on k f U" and "Ck_on k g U" and "\<And>y. y \<in> U \<Longrightarrow> g y \<noteq> 0"
  shows "Ck_on k (\<lambda>y. f y / g y) U"
proof -
  have inv_g: "Ck_on k (\<lambda>y. inverse (g y)) U"
    by (rule Ck_on_inverse[OF assms(2,3)])
  have "Ck_on k (\<lambda>y. f y * inverse (g y)) U"
    by (rule Ck_on_mult[OF assms(1) inv_g])
  thus ?thesis by (simp add: divide_inverse)
qed

lemma Ck_on_inner:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_inner"
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. f y \<bullet> g y) U"
  using Ck_on_bilinear[OF bounded_bilinear_inner assms] .

lemma Ck_on_norm_sq:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_inner"
  assumes "Ck_on k f U"
  shows "Ck_on k (\<lambda>y. (norm (f y))\<^sup>2) U"
proof -
  have "Ck_on k (\<lambda>y. f y \<bullet> f y) U"
    by (rule Ck_on_inner[OF assms assms])
  thus ?thesis by (simp add: dot_square_norm)
qed

lemma Ck_on_compose:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
    and g :: "'b \<Rightarrow> 'c::real_normed_vector"
  assumes "Ck_on k g V" and "Ck_on k f U" and fUV: "\<And>y. y \<in> U \<Longrightarrow> f y \<in> V"
  shows "Ck_on k (\<lambda>y. g (f y)) U"
  using assms(1,2)
proof (induction k arbitrary: g)
  case 0
  then show ?case
    using fUV by (auto simp: Ck_on_0_iff intro: continuous_on_compose2)
next
  case (Suc k)
  from Suc.prems(1) have dg: "\<And>y. y \<in> V \<Longrightarrow> g differentiable (at y)"
    and Dg: "\<And>w. Ck_on k (\<lambda>y. frechet_derivative g (at y) w) V"
    by (auto simp: Ck_on_Suc_iff)
  from Suc.prems(2) have U: "open U"
    and df: "\<And>x. x \<in> U \<Longrightarrow> f differentiable (at x)"
    and Df: "\<And>v. Ck_on k (\<lambda>x. frechet_derivative f (at x) v) U"
    by (auto simp: Ck_on_Suc_iff)
  have fk: "Ck_on k f U"
    using Suc.prems(2) by (rule Ck_on_SucD)
  have D: "Ck_on k (\<lambda>x. \<Sum>i\<in>Basis. (frechet_derivative f (at x) v \<bullet> i) *\<^sub>R
      frechet_derivative g (at (f x)) i) U" for v
  proof (rule Ck_on_sum[OF finite_Basis nonempty_Basis])
    fix i :: 'b
    have "Ck_on k (\<lambda>x. frechet_derivative f (at x) v \<bullet> i) U"
      by (rule Ck_on_inner[OF Df Ck_on_const[OF U]])
    moreover have "Ck_on k (\<lambda>x. frechet_derivative g (at (f x)) i) U"
      by (rule Suc.IH[OF Dg fk])
    ultimately show "Ck_on k (\<lambda>x. (frechet_derivative f (at x) v \<bullet> i) *\<^sub>R
        frechet_derivative g (at (f x)) i) U"
      by (rule Ck_on_bilinear[OF bounded_bilinear_scaleR])
  qed
  show ?case
    unfolding Ck_on_Suc_iff
    using U df dg fUV D
    by (auto simp: frechet_derivative_compose_euclidean cong: Ck_on_cong
        intro: differentiable_chain_at[unfolded o_def])
qed

lemma Ck_on_Pair:
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. (f y, g y)) U"
  using assms
proof (induction k arbitrary: f g)
  case 0
  then show ?case
    by (auto simp: Ck_on_0_iff intro: continuous_intros)
next
  case (Suc k)
  from Suc.prems have U: "open U"
    and df: "\<And>x. x \<in> U \<Longrightarrow> f differentiable (at x)"
    and dg: "\<And>x. x \<in> U \<Longrightarrow> g differentiable (at x)"
    and Df: "\<And>v. Ck_on k (\<lambda>x. frechet_derivative f (at x) v) U"
    and Dg: "\<And>v. Ck_on k (\<lambda>x. frechet_derivative g (at x) v) U"
    by (auto simp: Ck_on_Suc_iff)
  show ?case
    unfolding Ck_on_Suc_iff
    using U df dg Suc.IH[OF Df Dg]
    by (auto simp: frechet_derivative_Pair cong: Ck_on_cong)
qed

text \<open>A bounded linear map is its own derivative, hence \<open>C\<^sup>k\<close> for every \<open>k\<close>.\<close>

lemma Ck_at_bounded_linear:
  fixes T :: "'b::real_normed_vector \<Rightarrow> 'c::real_normed_vector"
  assumes T: "bounded_linear T"
  shows "Ck_at k T x"
proof (induction k arbitrary: x)
  case 0
  have "continuous (at x) T"
    by (rule bounded_linear.continuous[OF T continuous_ident])
  thus ?case by simp
next
  case (Suc k)
  have der: "(T has_derivative T) (at y)" for y
    using bounded_linear.has_derivative[OF T has_derivative_ident] by simp
  show ?case
    unfolding Ck_at.simps(2)
  proof (intro conjI allI)
    show "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. Ck_at k T y)"
      by (intro exI[where x = UNIV] conjI) (auto simp: Suc.IH)
    show "T differentiable (at x)" using der unfolding differentiable_def by blast
    fix v
    have "frechet_derivative T (at y) v = T v" for y
      using frechet_derivative_at[OF der] by simp
    hence "(\<lambda>y. frechet_derivative T (at y) v) = (\<lambda>y. T v)" by (rule ext)
    thus "Ck_at k (\<lambda>y. frechet_derivative T (at y) v) x"
      by (simp add: Ck_at_const)
  qed
qed

lemma Ck_on_bounded_linear:
  fixes T :: "'b::real_normed_vector \<Rightarrow> 'c::real_normed_vector"
  assumes "bounded_linear T" and "open V"
  shows "Ck_on k T V"
  using assms by (simp add: Ck_on_def Ck_at_bounded_linear)

lemma Ck_on_bounded_linear_compose:
  fixes T :: "'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
    and f :: "'a::real_normed_vector \<Rightarrow> 'b"
  assumes T: "bounded_linear T" and f: "Ck_on k f U"
  shows "Ck_on k (\<lambda>y. T (f y)) U"
  by (rule Ck_on_compose[OF Ck_on_bounded_linear[OF T open_UNIV] f]) simp

text \<open>For \<open>f :: real \<Rightarrow> real\<close>, \<^const>\<open>Ck_on\<close> agrees with the one-dimensional notion
  \<^const>\<open>C_k_on\<close>.\<close>

lemma Ck_on_real_iff:
  fixes f :: "real \<Rightarrow> real"
  shows "Ck_on k f U \<longleftrightarrow> C_k_on k f U"
proof (induction k arbitrary: f)
  case 0
  show ?case
    by (simp add: Ck_on_0_iff C0_on_def)
next
  case (Suc k)
  show ?case
  proof
    assume "Ck_on (Suc k) f U"
    then have U: "open U" and d: "\<And>x. x \<in> U \<Longrightarrow> f differentiable (at x)"
      and D: "\<And>v. Ck_on k (\<lambda>x. frechet_derivative f (at x) v) U"
      by (auto simp: Ck_on_Suc_iff)
    have "Ck_on k (deriv f) U"
      using D[of 1] by (rule Ck_on_congI) (simp add: d frechet_derivative_one_eq_deriv)
    then have "C_k_on k (deriv f) U"
      by (simp add: Suc.IH)
    moreover have "f differentiable_on U"
      using U d by (simp add: differentiable_on_eq_differentiable_at)
    ultimately show "C_k_on (Suc k) f U"
      by (simp add: C_k_on_Suc_iff)
  next
    assume "C_k_on (Suc k) f U"
    then have diff: "f differentiable_on U" and "C_k_on k (deriv f) U"
      by (simp_all add: C_k_on_Suc_iff)
    then have Ck: "Ck_on k (deriv f) U"
      by (simp add: Suc.IH)
    have U: "open U"
      using Ck by (rule Ck_on_open)
    have d: "\<And>x. x \<in> U \<Longrightarrow> f differentiable (at x)"
      using diff U by (simp add: differentiable_on_eq_differentiable_at)
    have "Ck_on k (\<lambda>x. frechet_derivative f (at x) v) U" for v
    proof (rule Ck_on_congI)
      show "Ck_on k (\<lambda>x. v * deriv f x) U"
        using Ck_on_mult[OF Ck_on_const[OF U] Ck] .
      show "frechet_derivative f (at x) v = v * deriv f x" if "x \<in> U" for x
        using d[OF that] by (rule frechet_derivative_to_deriv)
    qed
    then show "Ck_on (Suc k) f U"
      using U d by (simp add: Ck_on_Suc_iff)
  qed
qed

text \<open>For functions of one real variable, \<open>C\<^sup>1\<close> agrees with @{const C1_differentiable_on}.\<close>

lemma Ck_on_1_iff_C1_differentiable_on:
  fixes f :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes "open U"
  shows "Ck_on 1 f U \<longleftrightarrow> f C1_differentiable_on U"
proof -
  have fd: "frechet_derivative f (at x) v = v *\<^sub>R vector_derivative f (at x)"
    if "f differentiable (at x)" for x v
  proof -
    have "(f has_derivative (\<lambda>h. h *\<^sub>R vector_derivative f (at x))) (at x)"
      using vector_derivative_works[THEN iffD1, OF that] by (simp only: has_vector_derivative_def)
    then have "frechet_derivative f (at x) = (\<lambda>h. h *\<^sub>R vector_derivative f (at x))"
      by (rule frechet_derivative_at[symmetric])
    then show ?thesis
      by simp
  qed
  have "Ck_on 1 f U \<longleftrightarrow> (\<forall>x\<in>U. f differentiable (at x)) \<and>
      (\<forall>v. continuous_on U (\<lambda>x. frechet_derivative f (at x) v))"
    using assms by (simp add: One_nat_def Ck_on_Suc_iff Ck_on_0_iff)
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>U. f differentiable (at x)) \<and>
      continuous_on U (\<lambda>x. vector_derivative f (at x))"
  proof (rule conj_cong[OF refl])
    assume d: "\<forall>x\<in>U. f differentiable (at x)"
    show "(\<forall>v. continuous_on U (\<lambda>x. frechet_derivative f (at x) v)) \<longleftrightarrow>
        continuous_on U (\<lambda>x. vector_derivative f (at x))"
    proof
      assume "\<forall>v. continuous_on U (\<lambda>x. frechet_derivative f (at x) v)"
      then have "continuous_on U (\<lambda>x. frechet_derivative f (at x) 1)"
        by blast
      then show "continuous_on U (\<lambda>x. vector_derivative f (at x))"
        by (rule continuous_on_eq) (simp add: d fd)
    next
      assume c: "continuous_on U (\<lambda>x. vector_derivative f (at x))"
      show "\<forall>v. continuous_on U (\<lambda>x. frechet_derivative f (at x) v)"
      proof
        fix v
        have "continuous_on U (\<lambda>x. v *\<^sub>R vector_derivative f (at x))"
          by (intro continuous_intros c)
        then show "continuous_on U (\<lambda>x. frechet_derivative f (at x) v)"
          by (rule continuous_on_eq) (simp add: d fd)
      qed
    qed
  qed
  also have "\<dots> \<longleftrightarrow> f C1_differentiable_on U"
    by (simp add: C1_differentiable_on_eq)
  finally show ?thesis .
qed


subsection \<open>Gradient for \<open>real\<^sup>n \<Rightarrow> real\<close>\<close>

definition grad_fun :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real^'n"
  ("\<nabla>")
  where "\<nabla> f x = (THE g :: real^'n. GDERIV f x :> g)"

lemma grad_fun_eq:
  assumes "GDERIV f x :> g"
  shows "\<nabla> f x = g"
  unfolding grad_fun_def using assms gradient_unique
  by (metis the_equality)

lemma grad_fun_satisfies_GDERIV:
  assumes "GDERIV f x :> g"
  shows "GDERIV f x :> \<nabla> f x"
  using assms grad_fun_eq by blast

lemma frechet_eq_inner_gradient:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "(f has_derivative L) (at x)" and "GDERIV f x :> \<nabla> f x"
  shows "L v = v \<bullet> \<nabla> f x"
  using assms has_derivative_unique gderiv_def by blast

subsection \<open>Hessian for \<open>real\<^sup>n \<Rightarrow> real\<close>\<close>

text \<open>
  The multi-dimensional Hessian: the Fréchet derivative of the gradient,
  represented as a matrix.
\<close>

definition has_hessian ::
    "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real^'n^'n \<Rightarrow> bool"
    ("(HESS (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
  where "HESS f x :> H \<longleftrightarrow> (\<nabla> f has_derivative (\<lambda>v. H *v v)) (at x)"

lemma hessian_unique:
  "HESS f x :> H \<Longrightarrow> HESS f x :> H' \<Longrightarrow> H = H'"
  unfolding has_hessian_def
  by (metis has_derivative_unique matrix_eq)

definition hess_fun :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real^'n^'n"
  ("\<nabla>\<^sup>2")
  where "\<nabla>\<^sup>2 f x = (THE H :: real^'n^'n. HESS f x :> H)"

lemma hess_fun_eq:
  assumes "HESS f x :> H"
  shows "\<nabla>\<^sup>2 f x = H"
  unfolding hess_fun_def using assms hessian_unique
  by (metis the_equality)

lemma hessian_eq_jacobian_of_gradient:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "HESS f x :> H"
  shows "H = matrix (frechet_derivative (\<nabla> f) (at x))"
  by (metis assms frechet_derivative_at[symmetric] has_hessian_def matrix_of_matrix_vector_mul)

text \<open>
  The Hessian entries are iterated partial derivatives:
  \<open>(\<nabla>\<^sup>2 f x) $ i $ j = \<partial>\<^sub>j (\<partial>\<^sub>i f) (x)\<close>.
\<close>

lemma hessian_eq_double_nabla:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "HESS f x :> \<nabla>\<^sup>2 f x"
  shows "\<forall>i j. \<nabla>\<^sup>2 f x $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
proof (intro allI)
  fix i j
  have row_grad: "GDERIV (\<lambda>y. \<nabla> f y $ i) x :> (\<nabla>\<^sup>2 f x) $ i"
  proof -
    have H: "(\<nabla> f has_derivative (*v) (\<nabla>\<^sup>2 f x)) (at x)"
      using assms unfolding has_hessian_def by simp
    have Hcomp: "((\<lambda>y. \<nabla> f y \<bullet> axis i 1) has_derivative
         (\<lambda>v. ((*v) (\<nabla>\<^sup>2 f x)) v \<bullet> axis i 1)) (at x within UNIV)"
      using H by (subst (asm) has_derivative_componentwise_within[where S = UNIV],
                  auto simp: Basis_vec_def)
    have comp_fun:  "(\<lambda>y. \<nabla> f y \<bullet> axis i 1) = (\<lambda>y. \<nabla> f y $ i)"
      by (rule ext, simp add: cart_eq_inner_axis)
    have comp_deriv: "(\<lambda>v. ((*v) (\<nabla>\<^sup>2 f x)) v \<bullet> axis i 1) = (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f x) $ i))"
      by (rule ext, simp add: inner_axis' inner_commute matrix_vector_mul_component)
    from Hcomp show ?thesis
      unfolding gderiv_def by (simp add: comp_fun comp_deriv)
  qed
  hence "\<nabla> (\<lambda>y. \<nabla> f y $ i) x = (\<nabla>\<^sup>2 f x) $ i"
    by (rule grad_fun_eq)
  then show "\<nabla>\<^sup>2 f x $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
    by simp
qed


subsection \<open>Connecting \<open>C\<^sup>k\<close> to the Hessian\<close>

text \<open>Consequences of \<open>C\<^sup>k\<close> for gradients and Hessians.\<close>

lemma Ck_2_imp_gradient_exists:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "Ck_on 2 f U" and "x \<in> U"
  shows "\<exists>g. GDERIV f x :> g"
proof -
  from assms have "Ck_at 2 f x"
    by (simp add: Ck_on_def)
  then have "f differentiable (at x)"
    by (metis Ck_at.simps(2) Suc_1)
  then show ?thesis
    by (rule Fr_diff_imp_gradient_exists)
qed

lemma Ck_2_imp_hessian_exists:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "Ck_on 2 f U" and "x \<in> U"
  shows "HESS f x :> \<nabla>\<^sup>2 f x"
proof -
  from assms have C2: "Ck_at 2 f x"
    by (simp add: Ck_on_def)

  then obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. Ck_at 1 f y"
    and diffx: "f differentiable (at x)"
    and D: "\<forall>v. Ck_at 1 (\<lambda>y. frechet_derivative f (at y) v) x"
    by (metis Ck_at.simps(2) Suc_1)

  let ?H = "(\<chi> i. \<nabla> (\<lambda>y. \<nabla> f y $ i) x)"

  have H_wit: "HESS f x :> ?H"
  proof (unfold has_hessian_def)
    have comp: "\<forall>i\<in>Basis. ((\<lambda>y. \<nabla> f y \<bullet> i) has_derivative (\<lambda>v. ((*v) ?H) v \<bullet> i)) (at x)"
    proof clarify
      fix b :: "real^'n"
      assume b: "b \<in> Basis"
      then obtain i where i: "b = axis i 1"
        by (auto simp: Basis_vec_def)

      let ?Fi = "(\<lambda>y. frechet_derivative f (at y) (axis i 1))"
      let ?Gi = "(\<lambda>y. \<nabla> f y $ i)"

      have Fi_C1: "Ck_at 1 ?Fi x"
        using D by blast
      hence Fi_diff: "?Fi differentiable (at x)"
        by simp

      have eqA: "\<And>y. y \<in> A \<Longrightarrow> ?Fi y = ?Gi y"
        by (metis (lifting) A(3) Ck_at.simps(2) Fr_diff_imp_gradient_exists Suc_eq_plus1 add_0
            frechet_derivative_at grad_fun_eq gderiv_def inner_axis' inner_real_def lambda_one)


      have ev_eq: "eventually (\<lambda>y. ?Fi y = ?Gi y) (nhds x)"
      proof -
        have "\<exists>S. open S \<and> x \<in> S \<and> (\<forall>y\<in>S. ?Fi y = ?Gi y)"
          using A eqA by blast
        then show ?thesis
          by (simp add: eventually_nhds)
      qed

      have Gi_diff: "?Gi differentiable (at x)"
        by (metis (no_types, lifting) A(1,2) Fi_diff differentiable_transform_within_open eqA)


      from Fr_diff_imp_gradient_exists[OF Gi_diff]
      obtain gi where gi: "GDERIV ?Gi x :> gi"
        by blast

      have gradGi: "GDERIV ?Gi x :> \<nabla> ?Gi x"
        using gi by (rule grad_fun_satisfies_GDERIV)

      have dGi: "(?Gi has_derivative (\<lambda>v. v \<bullet> (?H $ i))) (at x)"
        using gradGi unfolding gderiv_def by simp

      have "((\<lambda>y. \<nabla> f y \<bullet> b) has_derivative (\<lambda>v. ((*v) ?H) v \<bullet> b)) (at x)"
        by (metis (no_types, lifting) ext cart_eq_inner_axis dGi i
            inner_commute matrix_vector_mul_component)
      then show "((\<lambda>y. \<nabla> f y \<bullet> b) has_derivative (\<lambda>v. ((*v) ?H) v \<bullet> b)) (at x)".
    qed

    then show "(\<nabla> f has_derivative (*v) ?H) (at x)"
      using has_derivative_componentwise_within by blast
  qed
  show ?thesis
    using H_wit hess_fun_eq by fastforce
qed

lemma Ck_2_imp_hessian_continuous:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "Ck_on 2 f U"
  shows "continuous_on U (\<nabla>\<^sup>2 f)"
proof -
  have openU: "open U"
    using assms by (simp add: Ck_on_def)

  have comp_cont: "\<And>x i j. x \<in> U \<Longrightarrow> continuous (at x) (\<lambda>y. \<nabla>\<^sup>2 f y $ i $ j)"
  proof -
    fix x i j
    assume xU: "x \<in> U"

    from assms xU have C2x: "Ck_at 2 f x"
      by (simp add: Ck_on_def)

    from C2x obtain A where
      A: "open A" "x \<in> A" "\<forall>y\<in>A. Ck_at 1 f y"
      and diffx: "f differentiable (at x)"
      and Dx: "\<forall>v. Ck_at 1 (\<lambda>y. frechet_derivative f (at y) v) x"
      by (metis Ck_at.simps(2) Suc_1)

    let ?Fi = "(\<lambda>y. frechet_derivative f (at y) (axis i 1))"
    let ?K  = "(\<lambda>y. frechet_derivative ?Fi (at y) (axis j 1))"
    let ?Hc = "(\<lambda>y. \<nabla>\<^sup>2 f y $ i $ j)"

    have Fi_C1: "Ck_at 1 ?Fi x"
      using Dx by simp

    have K_cont: "continuous (at x) ?K"
      using Fi_C1 by simp

    have eq_on_U: "\<And>y. y \<in> U \<Longrightarrow> frechet_derivative ?Fi (at y) (axis j 1) = \<nabla>\<^sup>2 f y $ i $ j"
    proof -
      fix y
      assume yU: "y \<in> U"

      from assms yU have C2y: "Ck_at 2 f y"
        by (simp add: Ck_on_def)

      have dy: "f differentiable (at y)"
        by (metis C2y Ck_at.simps(2) Suc_1)

      have Fi_C1_y: "Ck_at 1 ?Fi y"
        using C2y by (metis Ck_at.simps(2) Suc_1)

      have Fi_diff_y: "?Fi differentiable (at y)"
        using Fi_C1_y by simp

      let ?Gi = "(\<lambda>z. \<nabla> f z $ i)"

      have FG_eq_on_U: "\<And>z. z \<in> U \<Longrightarrow> ?Fi z = ?Gi z"
      proof -
        fix z
        assume zU: "z \<in> U"

        from assms zU have C2z: "Ck_at 2 f z"
          by (simp add: Ck_on_def)

        have dz: "f differentiable (at z)"
          by (metis C2z Ck_at.simps(2) Suc_1)

        from Fr_diff_imp_gradient_exists[OF dz]
        obtain g where g: "GDERIV f z :> g"
          by blast
        have g_eq: "\<nabla> f z = g"
          using g by (rule grad_fun_eq)
        have "(f has_derivative (\<lambda>v. v \<bullet> g)) (at z)"
          using g unfolding gderiv_def by simp
        hence fd_eq: "frechet_derivative f (at z) = (\<lambda>v. v \<bullet> g)"
          by (metis frechet_derivative_at)
        show "?Fi z = ?Gi z"
          by (simp add: fd_eq g_eq inner_axis')
      qed

      have ev_FG: "eventually (\<lambda>z. ?Fi z = ?Gi z) (nhds y)"
        using FG_eq_on_U eventually_nhds openU yU by blast


      have Gi_diff_y: "?Gi differentiable (at y)"
        by (metis (no_types, lifting) FG_eq_on_U Fi_diff_y differentiable_transform_within_open openU yU)


      then have fd_Fi_Gi: "frechet_derivative ?Fi (at y) = frechet_derivative ?Gi (at y)"
        by (smt (verit, best) FG_eq_on_U frechet_derivative_transform_within_open openU yU)

      from Fr_diff_imp_gradient_exists[OF Gi_diff_y]
      obtain gi where gi: "GDERIV ?Gi y :> gi"
        by blast

      have gi_eq: "\<nabla> ?Gi y = gi"
        using gi by (rule grad_fun_eq)

      have "(?Gi has_derivative (\<lambda>v. v \<bullet> gi)) (at y)"
        using gi unfolding gderiv_def by simp
      hence fd_Gi: "frechet_derivative ?Gi (at y) = (\<lambda>v. v \<bullet> gi)"
        by (metis frechet_derivative_at)

      have fd_Gi_axis: "frechet_derivative ?Gi (at y) (axis j 1) = \<nabla> ?Gi y $ j"
        by (metis cart_eq_inner_axis fd_Gi gi_eq inner_commute)
      have Hess_y: "HESS f y :> \<nabla>\<^sup>2 f y"
        using assms yU by (rule Ck_2_imp_hessian_exists)

      have hess_eq: "\<nabla>\<^sup>2 f y $ i $ j = \<nabla> ?Gi y $ j"
        using hessian_eq_double_nabla[OF Hess_y] by simp

      show "frechet_derivative ?Fi (at y) (axis j 1) = \<nabla>\<^sup>2 f y $ i $ j"
        using fd_Fi_Gi fd_Gi_axis hess_eq by simp
    qed
    have ev_eq: "eventually (\<lambda>y. ?K y = ?Hc y) (nhds x)"
      using eq_on_U eventually_nhds openU xU by blast
    show "continuous (at x) ?Hc"
      using K_cont ev_eq isCont_cong by fastforce
  qed

  show ?thesis
    unfolding continuous_on
  proof
    fix x
    assume xU: "x \<in> U"

    have isCont_H: "isCont (\<lambda>y. \<chi> i. \<chi> j. \<nabla>\<^sup>2 f y $ i $ j) x"
      unfolding isCont_def
    proof (rule tendsto_vec_lambda)
      fix i
      show "((\<lambda>y. \<chi> j. \<nabla>\<^sup>2 f y $ i $ j) \<longlongrightarrow> (\<chi> j. \<nabla>\<^sup>2 f x $ i $ j)) (at x)"
      proof (rule tendsto_vec_lambda)
        fix j
        from comp_cont[OF xU, of i j]
        show "((\<lambda>y. \<nabla>\<^sup>2 f y $ i $ j) \<longlongrightarrow> \<nabla>\<^sup>2 f x $ i $ j) (at x)"
          unfolding isCont_def by simp
      qed
    qed
    then have "continuous (at x) (\<nabla>\<^sup>2 f)"
      by simp
    then show "(\<nabla>\<^sup>2 f \<longlongrightarrow> \<nabla>\<^sup>2 f x) (at x within U)"
      by (metis at_within_open continuous_within openU xU)
  qed
qed

text \<open>The proof evaluates the second difference of \<open>f\<close> along \<open>e\<^sub>i\<close> and \<open>e\<^sub>j\<close> by the mean
  value theorem in both orders and lets the increments tend to \<open>0\<close>.\<close>

lemma mixed_coordinate_second_derivative_eq:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes openU: "open U"
      and xU: "x \<in> U"
      and C2: "Ck_on 2 f U"
  shows "(\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ j)) x $ i"
proof -
  (* Notation *)
  let ?ei = "axis i 1 :: real^'n"
  let ?ej = "axis j 1 :: real^'n"

  (* Work inside a ball *)
  obtain r where r_pos: "r > 0" and rU: "ball x r \<subseteq> U"
    using openU xU by (meson open_contains_ball)

  define \<delta> where "\<delta> = r / 4"
  have \<delta>_pos: "\<delta> > 0" using r_pos by (simp add: \<delta>_def)

  (* Any point x + s\<sqdot>e\<^sub>i + t\<sqdot>e\<^sub>j with |s|,|t| < \<delta> lies in U. *)
  have inU: "\<lbrakk> \<bar>s\<bar> < \<delta>; \<bar>t\<bar> < \<delta> \<rbrakk> \<Longrightarrow> x + s *\<^sub>R ?ei + t *\<^sub>R ?ej \<in> U" for s t
  proof -
    assume s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>"
    have "norm (s *\<^sub>R ?ei + t *\<^sub>R ?ej) \<le> \<bar>s\<bar> + \<bar>t\<bar>"
      by (simp add: norm_triangle_le)
    also have "\<dots> < \<delta> + \<delta>" using s_bd t_bd by linarith
    also have "\<dots> = r / 2" by (simp add: \<delta>_def)
    also have "\<dots> < r" using r_pos by linarith
    finally show "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej \<in> U"
      by (metis (no_types, lifting) add.assoc basic_trans_rules(31)
          dist_0_norm dist_add_cancel group_cancel.rule0 mem_ball rU)
  qed

  (* Names for partial derivatives *)
  (* Ps(s,t) = \<partial>\<^sub>if at x + s\<sqdot>e\<^sub>i + t\<sqdot>e\<^sub>j *)
  define Ps where "Ps s t = \<nabla> f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej) $ i" for s t
  (* Qt(s,t) = \<partial>\<^sub>jf at x + s\<sqdot>e\<^sub>i + t\<sqdot>e\<^sub>j *)
  define Qt where "Qt s t = \<nabla> f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej) $ j" for s t

  (* Basic differentiability facts *)
  have diff_at: "f differentiable (at z)" if "z \<in> U" for z
    by (metis Ck_at.simps(2) Ck_on_def Suc_1 C2 that)

  have grad_exists: "GDERIV f z :> \<nabla> f z" if "z \<in> U" for z
    using Fr_diff_imp_gradient_exists[OF diff_at[OF that]]
      grad_fun_satisfies_GDERIV by blast

  have Hess_exists: "HESS f z :> \<nabla>\<^sup>2 f z" if "z \<in> U" for z
    using C2 that by (rule Ck_2_imp_hessian_exists)

  have hcont: "continuous_on U (\<nabla>\<^sup>2 f)"
    using C2 by (rule Ck_2_imp_hessian_continuous)

  (* Row-gradient lemma *)
  (* GDERIV (\<lambda>y. \<nabla> f y $ k) z :> (\<nabla>\<^sup>2f z) $ k  for z \<in> U *)
  have row_grad: "GDERIV (\<lambda>y. \<nabla> f y $ k) z :> (\<nabla>\<^sup>2 f z) $ k"
    if zU: "z \<in> U" for z k
  proof -
    have H: "(\<nabla> f has_derivative (*v) (\<nabla>\<^sup>2 f z)) (at z)"
      using Hess_exists[OF zU] unfolding has_hessian_def .
    have "((\<lambda>y. \<nabla> f y \<bullet> axis k 1) has_derivative
         (\<lambda>v. ((*v) (\<nabla>\<^sup>2 f z)) v \<bullet> axis k 1)) (at z within UNIV)"
      using H by (subst (asm) has_derivative_componentwise_within[where S = UNIV],
                  auto simp: Basis_vec_def)
    thus ?thesis
      unfolding gderiv_def
      by (simp add: inner_axis' inner_commute matrix_vector_mul_component)
  qed

  (* Derivatives of the slice maps *)
  (* \<partial>/\<partial>s [Ps(s,t)] = (\<nabla>\<^sup>2f)$i$i  and  \<partial>/\<partial>t [Ps(s,t)] = (\<nabla>\<^sup>2f)$i$j *)

  have Ps_has_deriv_t:
    "((\<lambda>t'. Ps s t') has_real_derivative (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j)
       (at t)"
    if s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>" for s t
  proof -
    let ?z = "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej"
    have zU: "?z \<in> U" using inU[OF s_bd t_bd] .
    have rg: "GDERIV (\<lambda>y. \<nabla> f y $ i) ?z :> (\<nabla>\<^sup>2 f ?z) $ i"
      by (rule row_grad[OF zU])
    have fd: "((\<lambda>y. \<nabla> f y $ i) has_derivative (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f ?z) $ i))) (at ?z)"
      using rg unfolding gderiv_def .
    have lin: "((\<lambda>t'. x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej) has_derivative (\<lambda>dt. dt *\<^sub>R ?ej)) (at t)"
      by (intro derivative_eq_intros) auto
    have chain:
      "((\<lambda>t'. \<nabla> f (x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej) $ i) has_derivative
         (\<lambda>dt. (dt *\<^sub>R ?ej) \<bullet> ((\<nabla>\<^sup>2 f ?z) $ i))) (at t)"
      using has_derivative_compose[OF lin fd] by (simp add: o_def)
    have "(\<lambda>dt. (dt *\<^sub>R ?ej) \<bullet> ((\<nabla>\<^sup>2 f ?z) $ i))
        = (\<lambda>dt. dt * ((\<nabla>\<^sup>2 f ?z) $ i $ j))"
      by (rule ext, simp add: inner_axis' mult.commute)
    thus ?thesis
      using chain unfolding Ps_def has_field_derivative_def
      by (simp add: mult_commute_abs)
  qed

  have Qt_has_deriv_s:
    "((\<lambda>s'. Qt s' t) has_real_derivative (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i)
       (at s)"
    if s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>" for s t
  proof -
    let ?z = "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej"
    have zU: "?z \<in> U" using inU[OF s_bd t_bd] .
    have rg: "GDERIV (\<lambda>y. \<nabla> f y $ j) ?z :> (\<nabla>\<^sup>2 f ?z) $ j"
      by (rule row_grad[OF zU])
    have fd: "((\<lambda>y. \<nabla> f y $ j) has_derivative (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f ?z) $ j))) (at ?z)"
      using rg unfolding gderiv_def .
    have lin: "((\<lambda>s'. x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej) has_derivative (\<lambda>ds. ds *\<^sub>R ?ei)) (at s)"
      by (intro derivative_eq_intros) auto
    have chain:
      "((\<lambda>s'. \<nabla> f (x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej) $ j) has_derivative
         (\<lambda>ds. (ds *\<^sub>R ?ei) \<bullet> ((\<nabla>\<^sup>2 f ?z) $ j))) (at s)"
      using has_derivative_compose[OF lin fd] by (simp add: o_def)
    have "(\<lambda>ds. (ds *\<^sub>R ?ei) \<bullet> ((\<nabla>\<^sup>2 f ?z) $ j))
        = (\<lambda>ds. ds * ((\<nabla>\<^sup>2 f ?z) $ j $ i))"
      by (rule ext, simp add: inner_axis' mult.commute)
    thus ?thesis
      using chain unfolding Qt_def has_field_derivative_def
      by (metis (no_types, lifting) ext mult.commute)
  qed

  (* Similarly for \<partial>/\<partial>s [\<Phi>(s,t)] and \<partial>/\<partial>t [\<Phi>(s,t)] *)
  have Phi_has_deriv_s: "((\<lambda>s'. f (x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej)) has_real_derivative Ps s t) (at s)"
    if s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>" for s t
  proof -
    let ?z = "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej"
    have zU: "?z \<in> U" using inU[OF s_bd t_bd] .
    have fd: "(f has_derivative (\<lambda>v. v \<bullet> \<nabla> f ?z)) (at ?z)"
      using grad_exists[OF zU] unfolding gderiv_def .
    have lin: "((\<lambda>s'. x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej) has_derivative (\<lambda>ds. ds *\<^sub>R ?ei)) (at s)"
      by (intro derivative_eq_intros) auto
    have chain: "((\<lambda>s'. f (x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej)) has_derivative
         (\<lambda>ds. (ds *\<^sub>R ?ei) \<bullet> \<nabla> f ?z)) (at s)"
      using has_derivative_compose[OF lin fd] by (simp add: o_def)
    have "(\<lambda>ds. (ds *\<^sub>R ?ei) \<bullet> \<nabla> f ?z) = (\<lambda>ds. ds * (\<nabla> f ?z $ i))"
      by (rule ext, simp add: inner_axis' mult.commute)
    thus ?thesis
      using chain unfolding Ps_def has_field_derivative_def
      by (metis (full_types, lifting) ext mult.commute)
  qed

  have Phi_has_deriv_t: "((\<lambda>t'. f (x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej)) has_real_derivative Qt s t) (at t)"
    if s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>" for s t
  proof -
    let ?z = "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej"
    have zU: "?z \<in> U" using inU[OF s_bd t_bd] .
    have fd: "(f has_derivative (\<lambda>v. v \<bullet> \<nabla> f ?z)) (at ?z)"
      using grad_exists[OF zU] unfolding gderiv_def .
    have lin: "((\<lambda>t'. x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej) has_derivative (\<lambda>dt. dt *\<^sub>R ?ej)) (at t)"
      by (intro derivative_eq_intros) auto
    have chain: "((\<lambda>t'. f (x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej)) has_derivative
         (\<lambda>dt. (dt *\<^sub>R ?ej) \<bullet> \<nabla> f ?z)) (at t)"
      using has_derivative_compose[OF lin fd] by (simp add: o_def)
    have "(\<lambda>dt. (dt *\<^sub>R ?ej) \<bullet> \<nabla> f ?z) = (\<lambda>dt. dt * (\<nabla> f ?z $ j))"
      by (rule ext, simp add: inner_axis' mult.commute)
    thus ?thesis
      using chain unfolding Qt_def has_field_derivative_def
      by (metis (full_types, lifting) ext mult.commute)
  qed


  (* Continuity of the relevant Hessian entries *)


  (* For the \<epsilon>-\<delta> argument we only need: *)
  have Hij_cont_at_0:
    "\<forall>\<epsilon>>0. \<exists>\<delta>'>0. \<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
       \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j - (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
  proof -
    have cont_comp: "isCont (\<lambda>p. (\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ i $ j) (0,0)"
    proof -
      have cont_hij: "continuous_on U (\<lambda>z. (\<nabla>\<^sup>2 f z) $ i $ j)"
        using hcont by (simp add: continuous_on_component)
      have isCont_hij: "isCont (\<lambda>z. (\<nabla>\<^sup>2 f z) $ i $ j) x"
        using cont_hij openU xU continuous_on_eq_continuous_at by blast
      have isCont_slice: "isCont (\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0::real, 0::real)"
        by (intro continuous_intros)
      have at_zero: "(\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0::real, 0::real) = x"
        by simp
      have "isCont (\<lambda>z. (\<nabla>\<^sup>2 f z) $ i $ j)
              ((\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0, 0))"
        using isCont_hij by (simp add: at_zero)
      thus ?thesis
        by (rule isCont_o2[OF isCont_slice])
    qed
    show ?thesis
    proof (intro allI impI)
      fix \<epsilon> :: real
      assume eps: "\<epsilon> > 0"

      (* Step 1: unfold isCont to tendsto, then to eventually_at *)
      from cont_comp
      have "((\<lambda>p. (\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ i $ j) \<longlongrightarrow>
              (\<nabla>\<^sup>2 f x) $ i $ j) (at (0,0))"
        unfolding isCont_def by simp

      (* Step 2: instantiate tendsto_iff at \<epsilon> *)
      from this[unfolded tendsto_iff] eps
      have "eventually (\<lambda>p. dist ((\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ i $ j)
                                  ((\<nabla>\<^sup>2 f x) $ i $ j) < \<epsilon>) (at (0,0))"
        by simp

      (* Step 3: unfold eventually_at to get r'' with the p \<noteq> (0,0) guard *)
      then obtain r'' where r''_pos: "r'' > 0"
        and r''_bd: "\<forall>p. p \<noteq> (0::real, 0::real) \<and> dist p (0,0) < r'' \<longrightarrow>
             dist ((\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ i $ j)
                  ((\<nabla>\<^sup>2 f x) $ i $ j) < \<epsilon>"
        unfolding eventually_at by auto

      (* Step 4: extend to ALL p by case-splitting on p = (0,0) *)
      define \<delta>' where "\<delta>' = min \<delta> (r'' / 2)"
      have "\<delta>' > 0" using \<delta>_pos r''_pos by (simp add: \<delta>'_def)
      moreover have "\<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j -
         (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
      proof (intro allI impI)
        fix s t assume st: "\<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>'"
        show "\<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j -
               (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
        proof (cases "s = 0 \<and> t = 0")
          case True
          then show ?thesis using eps by simp
        next
          case False
          then have "(s, t) \<noteq> (0::real, 0::real)" by auto
          moreover have "dist (s,t) (0::real, 0::real) < r''"
          proof -
            have "dist (s,t) (0::real, 0::real) \<le> \<bar>s\<bar> + \<bar>t\<bar>"
              using sqrt_sum_squares_le_sum_abs by (simp add: dist_Pair_Pair)
            also have "\<dots> < r''" using st by (simp add: \<delta>'_def)
            finally show ?thesis.
          qed
          ultimately have "dist ((\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j)
                                ((\<nabla>\<^sup>2 f x) $ i $ j) < \<epsilon>"
            using r''_bd by auto
          thus ?thesis by (simp add: dist_real_def)
        qed
      qed
      ultimately show "\<exists>\<delta>'>0. \<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j -
         (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
        by blast
    qed
  qed

  have Hji_cont_at_0:
  "\<forall>\<epsilon>>0. \<exists>\<delta>'>0. \<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
     \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
  proof -
    have cont_comp: "isCont (\<lambda>p. (\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ j $ i) (0,0)"
    proof -
      have cont_hji: "continuous_on U (\<lambda>z. (\<nabla>\<^sup>2 f z) $ j $ i)"
        using hcont by (simp add: continuous_on_component)
      have isCont_hji: "isCont (\<lambda>z. (\<nabla>\<^sup>2 f z) $ j $ i) x"
        using cont_hji openU xU continuous_on_eq_continuous_at by blast
      have isCont_slice: "isCont (\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0::real, 0::real)"
        by (intro continuous_intros)
      have at_zero: "(\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0::real, 0::real) = x"
        by simp
      have "isCont (\<lambda>z. (\<nabla>\<^sup>2 f z) $ j $ i)
              ((\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0, 0))"
        using isCont_hji by (simp add: at_zero)
      thus ?thesis
        by (rule isCont_o2[OF isCont_slice])
    qed
    show ?thesis
    proof (intro allI impI)
      fix \<epsilon> :: real
      assume eps: "\<epsilon> > 0"

      from cont_comp
      have "((\<lambda>p. (\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ j $ i) \<longlongrightarrow>
              (\<nabla>\<^sup>2 f x) $ j $ i) (at (0,0))"
        unfolding isCont_def by simp

      from this[unfolded tendsto_iff] eps
      have "eventually (\<lambda>p. dist ((\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ j $ i)
                                  ((\<nabla>\<^sup>2 f x) $ j $ i) < \<epsilon>) (at (0,0))"
        by simp

      then obtain r'' where r''_pos: "r'' > 0"
        and r''_bd: "\<forall>p. p \<noteq> (0::real, 0::real) \<and> dist p (0,0) < r'' \<longrightarrow>
             dist ((\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ j $ i)
                  ((\<nabla>\<^sup>2 f x) $ j $ i) < \<epsilon>"
        unfolding eventually_at by auto

      define \<delta>' where "\<delta>' = min \<delta> (r'' / 2)"
      have "\<delta>' > 0"
        using \<delta>_pos r''_pos by (simp add: \<delta>'_def)
      moreover have "\<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i -
         (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
      proof (intro allI impI)
        fix s t
        assume st: "\<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>'"
        show "\<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i -
               (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
        proof (cases "s = 0 \<and> t = 0")
          case True
          then show ?thesis
            using eps by simp
        next
          case False
          then have "(s, t) \<noteq> (0::real, 0::real)"
            by auto
          moreover have "dist (s,t) (0::real, 0::real) < r''"
          proof -
            have "dist (s,t) (0::real, 0::real) \<le> \<bar>s\<bar> + \<bar>t\<bar>"
              using sqrt_sum_squares_le_sum_abs by (simp add: dist_Pair_Pair)
            also have "\<dots> < r''"
              using st by (simp add: \<delta>'_def)
            finally show ?thesis .
          qed
          ultimately have "dist ((\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i)
                                ((\<nabla>\<^sup>2 f x) $ j $ i) < \<epsilon>"
            using r''_bd by auto
          thus ?thesis
            by (simp add: dist_real_def)
        qed
      qed
      ultimately show "\<exists>\<delta>'>0. \<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i -
         (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
        by blast
    qed
  qed


  (* The rectangle increment *)
  define \<Delta> where
    "\<Delta> h k = f (x + h *\<^sub>R ?ei + k *\<^sub>R ?ej)
           - f (x + h *\<^sub>R ?ei)
           - f (x + k *\<^sub>R ?ej)
           + f x" for h k

  (* MVT, direction 1: differentiate in s first, then t *)
  have dir1:
    "\<exists>\<xi> \<eta>. \<bar>\<xi>\<bar> \<le> \<bar>h\<bar> \<and> \<bar>\<eta>\<bar> \<le> \<bar>k\<bar> \<and>
            \<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
    if h_pos: "h > 0" and k_pos: "k > 0"
       and h_bd: "h < \<delta>" and k_bd: "k < \<delta>"
    for h k
  proof -
    (* g(s) = f(x + s\<sqdot>e\<^sub>i + k\<sqdot>e\<^sub>j) - f(x + s\<sqdot>e\<^sub>i) *)
    define g where "g s = f (x + s *\<^sub>R ?ei + k *\<^sub>R ?ej) - f (x + s *\<^sub>R ?ei)" for s

    have g_deriv: "(g has_real_derivative (Ps s k - Ps s 0)) (at s)"
      if "\<bar>s\<bar> < \<delta>" for s
    proof -
      have "((\<lambda>s'. f (x + s' *\<^sub>R ?ei + k *\<^sub>R ?ej)) has_real_derivative Ps s k) (at s)"
        using Phi_has_deriv_s[of s k] that k_bd k_pos by linarith
      moreover have "((\<lambda>s'. f (x + s' *\<^sub>R ?ei + 0 *\<^sub>R ?ej)) has_real_derivative Ps s 0) (at s)"
        using Phi_has_deriv_s[of s 0] that \<delta>_pos by auto
      ultimately show ?thesis
        unfolding g_def
        by (subst derivative_eq_intros, simp_all)
    qed

    (* Apply MVT to g on [0,h] *)
    have g_deriv_on_seg: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> h \<Longrightarrow> (g has_real_derivative (Ps x k - Ps x 0)) (at x)"
    proof -
      fix x :: real
      assume x0: "0 \<le> x"
      assume xh: "x \<le> h"
      have "\<bar>x\<bar> = x"
        using x0 by simp
      also have "... \<le> h"
        using xh by simp
      also have "... < \<delta>"
        using h_bd by simp
      finally have "\<bar>x\<bar> < \<delta>" .
      thus "(g has_real_derivative (Ps x k - Ps x 0)) (at x)"
        by (rule g_deriv)
    qed

    have g_diff: "\<exists>\<xi>. 0 < \<xi> \<and> \<xi> < h \<and> \<Delta> h k = h * (Ps \<xi> k - Ps \<xi> 0)"
    proof -
      obtain \<xi> where \<xi>:
        "0 < \<xi>" "\<xi> < h"
        "g h - g 0 = (h - 0) * (Ps \<xi> k - Ps \<xi> 0)"
        using MVT2[of 0 h g "\<lambda>x. Ps x k - Ps x 0"]
          h_pos g_deriv_on_seg
        by blast
      have "g h - g 0 = \<Delta> h k"
        by (simp add: g_def \<Delta>_def)
      with \<xi> show ?thesis
        by auto
    qed
    then obtain \<xi> where \<xi>_pos: "0 < \<xi>" and \<xi>_lt: "\<xi> < h"
      and eq1: "\<Delta> h k = h * (Ps \<xi> k - Ps \<xi> 0)" by blast

    (* Now apply MVT to p(t) = Ps(\<xi>,t) on [0,k] *)
    define p where "p t = Ps \<xi> t" for t

    have p_deriv: "(p has_real_derivative (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j) (at t)"
      if "\<bar>t\<bar> < \<delta>" for t
      using Ps_has_deriv_t[of \<xi> t] \<xi>_lt h_bd that
      unfolding p_def
      using \<xi>_pos by argo


    (* MVT application to p on [0,k] *)
    have p_deriv_on_seg: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> k \<Longrightarrow>
       (p has_real_derivative (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j) (at t)"
    proof -
      fix t :: real
      assume t0: "0 \<le> t"
      assume tk: "t \<le> k"
      have "\<bar>t\<bar> = t"
        using t0 by simp
      also have "... \<le> k"
        using tk by simp
      also have "... < \<delta>"
        using k_bd by simp
      finally have "\<bar>t\<bar> < \<delta>".
      thus "(p has_real_derivative (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j) (at t)"
        by (rule p_deriv)
    qed

    have p_diff: "\<exists>\<eta>. 0 < \<eta> \<and> \<eta> < k \<and>
        Ps \<xi> k - Ps \<xi> 0 = k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
    proof -
      obtain \<eta> where \<eta>:
        "0 < \<eta>"
        "\<eta> < k"
        "p k - p 0 = (k - 0) * ((\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j)"
        using MVT2[of 0 k p "\<lambda>t. (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j"] k_pos p_deriv_on_seg
        by blast
      have "p k - p 0 = Ps \<xi> k - Ps \<xi> 0"
        unfolding p_def by simp
      with \<eta> show ?thesis
        by auto
    qed
    then obtain \<eta> where \<eta>_pos: "0 < \<eta>" and \<eta>_lt: "\<eta> < k"
      and eq2: "Ps \<xi> k - Ps \<xi> 0 = k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
      by blast

    have "\<Delta> h k = h * (k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j)"
      using eq1 eq2 by simp
    hence "\<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
      by (simp add: mult.assoc)
    moreover have "\<bar>\<xi>\<bar> \<le> \<bar>h\<bar>" using \<xi>_pos \<xi>_lt h_pos by linarith
    moreover have "\<bar>\<eta>\<bar> \<le> \<bar>k\<bar>" using \<eta>_pos \<eta>_lt k_pos by linarith
    ultimately show ?thesis by blast
  qed

  (* MVT, direction 2: differentiate in t first, then s *)
  have dir2:
    "\<exists>\<xi>' \<eta>'. \<bar>\<xi>'\<bar> \<le> \<bar>h\<bar> \<and> \<bar>\<eta>'\<bar> \<le> \<bar>k\<bar> \<and>
              \<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
    if h_pos: "h > 0" and k_pos: "k > 0"
       and h_bd: "h < \<delta>" and k_bd: "k < \<delta>"
    for h k
  proof -
    (* g̃(t) = f(x + h\<sqdot>e\<^sub>i + t\<sqdot>e\<^sub>j) - f(x + t\<sqdot>e\<^sub>j) *)
    define g' where "g' t = f (x + h *\<^sub>R ?ei + t *\<^sub>R ?ej) - f (x + t *\<^sub>R ?ej)" for t

    have g'_deriv: "(g' has_real_derivative (Qt h t - Qt 0 t)) (at t)"
      if "\<bar>t\<bar> < \<delta>" for t
    proof -
      have "((\<lambda>t'. f (x + h *\<^sub>R ?ei + t' *\<^sub>R ?ej)) has_real_derivative Qt h t) (at t)"
        using Phi_has_deriv_t[of h t] h_bd that
        using h_pos by linarith
      moreover have "((\<lambda>t'. f (x + 0 *\<^sub>R ?ei + t' *\<^sub>R ?ej)) has_real_derivative Qt 0 t) (at t)"
        using Phi_has_deriv_t[of 0 t] \<delta>_pos that by auto
      ultimately show ?thesis
        unfolding g'_def by (subst derivative_eq_intros, simp_all)
    qed

    (* MVT on g̃ over [0,k] *)
    have g'_diff: "\<exists>\<eta>'. 0 < \<eta>' \<and> \<eta>' < k \<and> \<Delta> h k = k * (Qt h \<eta>' - Qt 0 \<eta>')"
    proof -
      have "g' k - g' 0 = \<Delta> h k"
        by (simp add: g'_def \<Delta>_def)
      moreover have g'_deriv_on_seg:
        "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> k \<Longrightarrow> (g' has_real_derivative (Qt h t - Qt 0 t)) (at t)"
      proof -
        fix t :: real
        assume t0: "0 \<le> t"
        assume tk: "t \<le> k"
        have "\<bar>t\<bar> = t"
          using t0 by simp
        also have "... \<le> k"
          using tk by simp
        also have "... < \<delta>"
          using k_bd by simp
        finally have "\<bar>t\<bar> < \<delta>".
        thus "(g' has_real_derivative (Qt h t - Qt 0 t)) (at t)"
          by (rule g'_deriv)
      qed
      moreover obtain \<eta>' where "0 < \<eta>'" "\<eta>' < k"
        and "g' k - g' 0 = k * (Qt h \<eta>' - Qt 0 \<eta>')"
        using MVT2[of 0 k g' "\<lambda>t. Qt h t - Qt 0 t"] k_pos g'_deriv_on_seg
        by auto
      ultimately show ?thesis
        by auto
    qed

    then obtain \<eta>' where \<eta>'_pos: "0 < \<eta>'" and \<eta>'_lt: "\<eta>' < k"
      and eq1': "\<Delta> h k = k * (Qt h \<eta>' - Qt 0 \<eta>')" by blast

    (* MVT on q(s) = Qt(s, \<eta>') over [0,h] *)
    define q where "q s = Qt s \<eta>'" for s

    have q_deriv_on_seg:
      "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> h \<Longrightarrow>
        (q has_real_derivative (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i) (at s)"
    proof -
      fix s :: real
      assume s0: "0 \<le> s"
      assume sh: "s \<le> h"
      have "\<bar>s\<bar> = s"
        using s0 by simp
      also have "... \<le> h"
        using sh by simp
      also have "... < \<delta>"
        using h_bd by simp
      finally have "\<bar>s\<bar> < \<delta>" .
      thus "(q has_real_derivative (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i) (at s)"
        using Qt_has_deriv_s \<eta>'_lt \<eta>'_pos \<open>q \<equiv> \<lambda>s. Qt s \<eta>'\<close> k_bd by fastforce
    qed

    have q_diff: "\<exists>\<xi>'. 0 < \<xi>' \<and> \<xi>' < h \<and>
        Qt h \<eta>' - Qt 0 \<eta>' = h * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
    proof -
      obtain \<xi>' where \<xi>':
        "0 < \<xi>'"
        "\<xi>' < h"
        "q h - q 0 = (h - 0) * ((\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i)"
        using MVT2[of 0 h q "\<lambda>s. (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"] h_pos q_deriv_on_seg
        by blast
      have "q h - q 0 = Qt h \<eta>' - Qt 0 \<eta>'"
        unfolding q_def by simp
      with \<xi>' show ?thesis
        by auto
    qed
    then obtain \<xi>' where \<xi>'_pos: "0 < \<xi>'" and \<xi>'_lt: "\<xi>' < h"
      and eq2': "Qt h \<eta>' - Qt 0 \<eta>' = h * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
      by blast

    have "\<Delta> h k = k * (h * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i)"
      using eq1' eq2' by simp
    hence "\<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
      by (simp add: mult.commute mult.assoc)
    moreover have "\<bar>\<xi>'\<bar> \<le> \<bar>h\<bar>" using \<xi>'_pos \<xi>'_lt h_pos by linarith
    moreover have "\<bar>\<eta>'\<bar> \<le> \<bar>k\<bar>" using \<eta>'_pos \<eta>'_lt k_pos by linarith
    ultimately show ?thesis by blast
  qed

  (* Combine: equality of Hessian entries *)
  have "(\<nabla>\<^sup>2 f x) $ i $ j = (\<nabla>\<^sup>2 f x) $ j $ i"
  proof (rule ccontr)
    assume neq: "(\<nabla>\<^sup>2 f x) $ i $ j \<noteq> (\<nabla>\<^sup>2 f x) $ j $ i"

    define \<epsilon> where "\<epsilon> = \<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> / 3"
    then have \<epsilon>_pos: "\<epsilon> > 0" using neq by simp

    (* By continuity, get \<delta>\<^sub>1 for the (i,j) entry and \<delta>\<^sub>2 for the (j,i) entry *)
    obtain \<delta>\<^sub>1 where \<delta>\<^sub>1_pos: "\<delta>\<^sub>1 > 0"
      and \<delta>\<^sub>1_bd: "\<forall>s t. \<bar>s\<bar> < \<delta>\<^sub>1 \<and> \<bar>t\<bar> < \<delta>\<^sub>1 \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j - (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
      using Hij_cont_at_0 \<epsilon>_pos by blast

    obtain \<delta>\<^sub>2 where \<delta>\<^sub>2_pos: "\<delta>\<^sub>2 > 0"
      and \<delta>\<^sub>2_bd: "\<forall>s t. \<bar>s\<bar> < \<delta>\<^sub>2 \<and> \<bar>t\<bar> < \<delta>\<^sub>2 \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
      using Hji_cont_at_0 \<epsilon>_pos by blast

    define \<delta>\<^sub>3 where "\<delta>\<^sub>3 = min \<delta> (min \<delta>\<^sub>1 \<delta>\<^sub>2)"
    have \<delta>\<^sub>3_pos: "\<delta>\<^sub>3 > 0" using \<delta>_pos \<delta>\<^sub>1_pos \<delta>\<^sub>2_pos by (simp add: \<delta>\<^sub>3_def)

    (* Pick concrete h, k *)
    define h where "h = \<delta>\<^sub>3 / 2"
    define k where "k = \<delta>\<^sub>3 / 2"
    have h_pos: "h > 0" and k_pos: "k > 0"
      using \<delta>\<^sub>3_pos by (simp_all add: h_def k_def)
    have h_bd: "h < \<delta>" and k_bd: "k < \<delta>"
      using \<delta>\<^sub>3_pos by (simp_all add: h_def k_def \<delta>\<^sub>3_def, auto)

    (* Apply dir1 and dir2 *)
    obtain \<xi> \<eta> where \<xi>_bd: "\<bar>\<xi>\<bar> \<le> h" and \<eta>_bd: "\<bar>\<eta>\<bar> \<le> k"
      and eq_ij: "\<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
      using dir1[OF h_pos k_pos h_bd k_bd] h_pos k_pos by auto

    obtain \<xi>' \<eta>' where \<xi>'_bd: "\<bar>\<xi>'\<bar> \<le> h" and \<eta>'_bd: "\<bar>\<eta>'\<bar> \<le> k"
      and eq_ji: "\<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
      using dir2[OF h_pos k_pos h_bd k_bd] h_pos k_pos by auto

    (* Both \<xi>,\<eta> and \<xi>',\<eta>' are within \<delta>\<^sub>1 and \<delta>\<^sub>2 bounds *)
    have "\<bar>\<xi>\<bar> < \<delta>\<^sub>1" and "\<bar>\<eta>\<bar> < \<delta>\<^sub>1"
      using \<xi>_bd \<eta>_bd \<delta>\<^sub>3_pos by (simp_all add: h_def k_def \<delta>\<^sub>3_def)
    hence close_ij:
      "\<bar>(\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j - (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
      using \<delta>\<^sub>1_bd by blast

    have "\<bar>\<xi>'\<bar> < \<delta>\<^sub>2" and "\<bar>\<eta>'\<bar> < \<delta>\<^sub>2"
      using \<xi>'_bd \<eta>'_bd \<delta>\<^sub>3_pos by (simp_all add: h_def k_def \<delta>\<^sub>3_def)
    hence close_ji:
      "\<bar>(\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
      using \<delta>\<^sub>2_bd by blast

    (* From eq_ij and eq_ji, since h*k > 0 we can cancel: *)
    have "(\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j =
          (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
      using eq_ij eq_ji h_pos k_pos by simp

    (* Triangle inequality gives contradiction *)
    hence "\<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < 2 * \<epsilon>"
      using close_ij close_ji by linarith
    hence "\<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar>
            < 2 * \<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> / 3"
      by (simp add: \<epsilon>_def)
    moreover have "\<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> > 0"
      using neq by simp
    ultimately show False
      by (simp add: field_simps)
  qed

  (* Translate to gradient notation *)
  have Hx: "HESS f x :> \<nabla>\<^sup>2 f x"
    using Hess_exists xU by blast

  have rowi: "(\<nabla>\<^sup>2 f x) $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
    using hessian_eq_double_nabla[OF Hx] by simp
  have rowj: "(\<nabla>\<^sup>2 f x) $ j $ i = (\<nabla> (\<lambda>y. \<nabla> f y $ j)) x $ i"
    using hessian_eq_double_nabla[OF Hx] by simp

  show ?thesis
    using \<open>(\<nabla>\<^sup>2 f x) $ i $ j = (\<nabla>\<^sup>2 f x) $ j $ i\<close> rowi rowj by simp
qed



theorem clairaut_hessian_symmetric:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "open U"
      and "x \<in> U"
      and "Ck_on 2 f U"
  shows "transpose (\<nabla>\<^sup>2 f x) = \<nabla>\<^sup>2 f x"
proof -
  have H: "HESS f x :> \<nabla>\<^sup>2 f x"
    using assms(2,3) by (subst Ck_2_imp_hessian_exists, simp_all)

  have sym_entries: "\<forall>i j. \<nabla>\<^sup>2 f x $ i $ j = \<nabla>\<^sup>2 f x $ j $ i"
  proof (intro allI)
    fix i j
    have ij: "\<nabla>\<^sup>2 f x $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
      using hessian_eq_double_nabla[OF H] by simp
    have ji: "\<nabla>\<^sup>2 f x $ j $ i = (\<nabla> (\<lambda>y. \<nabla> f y $ j)) x $ i"
      using hessian_eq_double_nabla[OF H] by simp
    have mix: "(\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ j)) x $ i"
      by (rule mixed_coordinate_second_derivative_eq[OF assms])
    show "\<nabla>\<^sup>2 f x $ i $ j = \<nabla>\<^sup>2 f x $ j $ i"
      using ij ji mix by simp
  qed
  then show ?thesis
    by (simp add: Finite_Cartesian_Product.transpose_def)
qed

text \<open>Equivalently, all mixed partials commute.\<close>

corollary mixed_partials_commute:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "open U" and "x \<in> U" and "Ck_on 2 f U"
  shows "\<nabla>\<^sup>2 f x $ i $ j = \<nabla>\<^sup>2 f x $ j $ i"
  using clairaut_hessian_symmetric[OF assms]
  by (metis (no_types, lifting) Finite_Cartesian_Product.transpose_def vec_lambda_beta)

subsection \<open>Basic algebra of gradients\<close>

lemma grad_fun_add:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GDERIV f x :> gf"
      and "\<exists>gg. GDERIV g x :> gg"
  shows "\<nabla> (\<lambda>y. f y + g y) x = \<nabla> f x + \<nabla> g x"
proof -
  have Gf: "GDERIV f x :> \<nabla> f x"
    using assms(1) by (blast intro: grad_fun_satisfies_GDERIV)
  have Gg: "GDERIV g x :> \<nabla> g x"
    using assms(2) by (blast intro: grad_fun_satisfies_GDERIV)
  have "GDERIV (\<lambda>y. f y + g y) x :> \<nabla> f x + \<nabla> g x"
    by (rule GDERIV_add[OF Gf Gg])
  thus ?thesis
    by (rule grad_fun_eq)
qed

lemma grad_fun_scaleR:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GDERIV f x :> gf"
  shows "\<nabla> (\<lambda>y. c * f y) x = c *\<^sub>R \<nabla> f x"
proof -
  have Gf: "GDERIV f x :> \<nabla> f x"
    using assms by (blast intro: grad_fun_satisfies_GDERIV)
  have "GDERIV (\<lambda>y. c * f y) x :> c *\<^sub>R \<nabla> f x"
    by (rule GDERIV_cmult[OF Gf])
  thus ?thesis
    by (rule grad_fun_eq)
qed

lemma grad_fun_neg:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GDERIV f x :> gf"
  shows "\<nabla> (\<lambda>y. - f y) x = - \<nabla> f x"
proof -
  have "\<nabla> (\<lambda>y. (-1) * f y) x = (-1) *\<^sub>R \<nabla> f x"
    by (rule grad_fun_scaleR[OF assms])
  thus ?thesis by simp
qed

lemma grad_fun_sub:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GDERIV f x :> gf"
      and "\<exists>gg. GDERIV g x :> gg"
  shows "\<nabla> (\<lambda>y. f y - g y) x = \<nabla> f x - \<nabla> g x"
proof -
  have "\<nabla> (\<lambda>y. f y + (- g y)) x = \<nabla> f x + \<nabla> (\<lambda>y. - g y) x"
    using assms grad_fun_add GDERIV_minus by blast
  also have "\<nabla> (\<lambda>y. - g y) x = - \<nabla> g x"
    by (rule grad_fun_neg[OF assms(2)])
  finally show ?thesis by simp
qed


subsection \<open>Constants and affine maps\<close>

lemma grad_fun_const:
  fixes c :: real
  shows "\<nabla> (\<lambda>_. c) x = 0"
  by (rule grad_fun_eq[OF GDERIV_const])

lemma grad_fun_affine:
  fixes a :: real and b :: "real^'n::finite"
  shows "\<nabla> (\<lambda>x. a + x \<bullet> b) x = b"
  by (rule grad_fun_eq[OF GDERIV_affine])

lemma grad_fun_sum:
  fixes F :: "'i \<Rightarrow> real^'n::finite \<Rightarrow> real"
  assumes exG: "\<And>i. i \<in> I \<Longrightarrow> \<exists>g. GDERIV (F i) x :> g"
  shows "\<nabla> (\<lambda>y. \<Sum>i\<in>I. F i y) x = (\<Sum>i\<in>I. \<nabla> (F i) x)"
proof -
  have G: "\<And>i. i \<in> I \<Longrightarrow> GDERIV (F i) x :> \<nabla> (F i) x"
    using exG by (blast intro: grad_fun_satisfies_GDERIV)
  have "GDERIV (\<lambda>y. \<Sum>i\<in>I. F i y) x :> (\<Sum>i\<in>I. \<nabla> (F i) x)"
    by (rule GDERIV_sum[OF G])
  thus ?thesis
    by (rule grad_fun_eq)
qed


subsection \<open>Hessian: constants and affine maps\<close>

lemma HESS_const_zero:
  fixes c :: real
  shows "HESS (\<lambda>_. c) x :> 0"
  unfolding has_hessian_def
  by (metis (no_types, lifting) ext grad_fun_const has_derivative_const matrix_vector_mult_0)

lemma HESS_affine_zero:
  fixes a :: real and b :: "real^'n::finite"
  shows "HESS (\<lambda>x. a + x \<bullet> b) x :> 0"
  unfolding has_hessian_def
  by (metis (no_types, lifting) ext grad_fun_affine has_derivative_const matrix_vector_mult_0)

lemma hessian_const_zero:
  fixes c :: real
  shows "\<nabla>\<^sup>2 (\<lambda>_. c) x = 0"
  using HESS_const_zero by (metis hess_fun_eq)

lemma hessian_affine_zero:
  fixes a :: real and b :: "real^'n::finite"
  shows "\<nabla>\<^sup>2 (\<lambda>x. a + x \<bullet> b) x = 0"
  using HESS_affine_zero by (metis hess_fun_eq)


subsection \<open>Coordinate formulas\<close>

lemma HESS_row_gradient:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes H: "HESS f x :> Hx"
  shows "GDERIV (\<lambda>y. \<nabla> f y $ i) x :> Hx $ i"
proof -
  have Hd: "(\<nabla> f has_derivative (*v) Hx) (at x)"
    using H unfolding has_hessian_def by simp
  have Hcomp:
    "((\<lambda>y. \<nabla> f y \<bullet> axis i 1) has_derivative
       (\<lambda>v. ((*v) Hx) v \<bullet> axis i 1)) (at x within UNIV)"
    using Hd
    by (subst (asm) has_derivative_componentwise_within[where S = UNIV])
       (auto simp: Basis_vec_def)
  have comp_fun:
    "(\<lambda>y. \<nabla> f y \<bullet> axis i 1) = (\<lambda>y. \<nabla> f y $ i)"
    by (rule ext) (simp add: cart_eq_inner_axis)
  have comp_deriv:
    "(\<lambda>v. ((*v) Hx) v \<bullet> axis i 1) = (\<lambda>v. v \<bullet> (Hx $ i))"
    by (metis (no_types) cart_eq_inner_axis inner_commute matrix_vector_mul_component)
  show ?thesis
    using Hcomp
    unfolding gderiv_def
    by (simp add: comp_fun comp_deriv)
qed

lemma HESS_row_eq:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes H: "HESS f x :> Hx"
  shows "\<nabla> (\<lambda>y. \<nabla> f y $ i) x = Hx $ i"
  by (rule grad_fun_eq[OF HESS_row_gradient[OF H]])

lemma HESS_component_eq:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes H: "HESS f x :> Hx"
  shows "Hx $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
  using HESS_row_eq[OF H, of i] by simp


subsection \<open>Hessian algebra at the predicate level\<close>

lemma HESS_add:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Hf: "HESS f x :> Hf'" and Hg: "HESS g x :> Hg'"
      and eq: "\<And>y. y \<in> A \<Longrightarrow> \<nabla> (\<lambda>z. f z + g z) y = \<nabla> f y + \<nabla> g y"
      and Aop: "open A" and xA: "x \<in> A"
  shows "HESS (\<lambda>y. f y + g y) x :> Hf' + Hg'"
proof -
  have dsum: "((\<lambda>y. \<nabla> f y + \<nabla> g y) has_derivative
               (\<lambda>v. Hf' *v v + Hg' *v v)) (at x)"
    using has_derivative_add
      Hf[unfolded has_hessian_def] Hg[unfolded has_hessian_def] by blast
  have dtrans: "((\<lambda>y. \<nabla> (\<lambda>z. f z + g z) y) has_derivative
                 (\<lambda>v. Hf' *v v + Hg' *v v)) (at x)"
    by (smt (verit, best) Aop dsum eq has_derivative_transfer_on_open xA)

  have "\<And>v. (Hf' + Hg') *v v = Hf' *v v + Hg' *v v"
    by (simp add: matrix_vector_mult_def vec_eq_iff sum.distrib distrib_right)
  thus ?thesis
    unfolding has_hessian_def using dtrans by presburger
qed

lemma HESS_scaleR:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes Hf: "HESS f x :> Hf'"
      and eq: "\<And>y. y \<in> A \<Longrightarrow> \<nabla> (\<lambda>z. c * f z) y = c *\<^sub>R \<nabla> f y"
      and Aop: "open A" and xA: "x \<in> A"
  shows "HESS (\<lambda>y. c * f y) x :> c *\<^sub>R Hf'"
proof -
  have dscale: "((\<lambda>y. c *\<^sub>R \<nabla> f y) has_derivative
                 (\<lambda>v. c *\<^sub>R (Hf' *v v))) (at x)"
    using Hf[unfolded has_hessian_def]
    by (intro has_derivative_scaleR_right)
  have dtrans: "((\<lambda>y. \<nabla> (\<lambda>z. c * f z) y) has_derivative
                 (\<lambda>v. c *\<^sub>R (Hf' *v v))) (at x)"
    using Aop dscale xA by (force simp: eq has_derivative_transform_within_open)
  have "\<And>v. (c *\<^sub>R Hf') *v v = c *\<^sub>R (Hf' *v v)"
    by (simp add: matrix_vector_mult_def vec_eq_iff scaleR_sum_right,
        simp add: sum_distrib_left vector_space_over_itself.scale_scale)
  thus ?thesis
    unfolding has_hessian_def using dtrans by presburger
qed


subsection \<open>Linearity of the Hessian on \<open>C\<^sup>2\<close> maps\<close>

lemma hessian_add_on_C2:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Cf: "Ck_on 2 f U"
      and Cg: "Ck_on 2 g U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. f y + g y) x = \<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x"
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix i
  have openU: "open U"
    using Cf by (simp add: Ck_on_def)
  have Hf: "HESS f x :> \<nabla>\<^sup>2 f x"
    using Cf xU by (rule Ck_2_imp_hessian_exists)
  have Hg: "HESS g x :> \<nabla>\<^sup>2 g x"
    using Cg xU by (rule Ck_2_imp_hessian_exists)
  have Hfg: "HESS (\<lambda>y. f y + g y) x :> \<nabla>\<^sup>2 (\<lambda>y. f y + g y) x"
    using Ck_on_add[OF Cf Cg] xU by (rule Ck_2_imp_hessian_exists)
  let ?\<phi> = "\<lambda>y. \<nabla> (\<lambda>z. f z + g z) y $ i"
  let ?\<psi> = "\<lambda>y. \<nabla> f y $ i + \<nabla> g y $ i"
  have eqU: "\<And>y. y \<in> U \<Longrightarrow> ?\<phi> y = ?\<psi> y"
  proof -
    fix y assume yU: "y \<in> U"
    have Gf: "GDERIV f y :> \<nabla> f y"
      using Ck_2_imp_gradient_exists[OF Cf yU]
      by (blast intro: grad_fun_satisfies_GDERIV)
    have Gg: "GDERIV g y :> \<nabla> g y"
      using Ck_2_imp_gradient_exists[OF Cg yU]
      by (blast intro: grad_fun_satisfies_GDERIV)
    have "GDERIV (\<lambda>z. f z + g z) y :> \<nabla> f y + \<nabla> g y"
      by (rule GDERIV_add[OF Gf Gg])
    hence "\<nabla> (\<lambda>z. f z + g z) y = \<nabla> f y + \<nabla> g y"
      by (rule grad_fun_eq)
    thus "?\<phi> y = ?\<psi> y" by simp
  qed
  have Grow_f: "GDERIV (\<lambda>y. \<nabla> f y $ i) x :> (\<nabla>\<^sup>2 f x) $ i"
    by (rule HESS_row_gradient[OF Hf])
  have Grow_g: "GDERIV (\<lambda>y. \<nabla> g y $ i) x :> (\<nabla>\<^sup>2 g x) $ i"
    by (rule HESS_row_gradient[OF Hg])
  have G\<psi>: "GDERIV ?\<psi> x :> ((\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i)"
    using GDERIV_add[OF Grow_f Grow_g] by simp
  have D\<psi>: "(?\<psi> has_derivative (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i))) (at x)"
    using G\<psi> unfolding gderiv_def by simp
  have D\<phi>: "(?\<phi> has_derivative (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i))) (at x)"
    by (smt (verit, best) D\<psi> eqU has_derivative_transform_within_open openU xU)
  have G\<phi>: "GDERIV ?\<phi> x :> ((\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i)"
    using D\<phi> unfolding gderiv_def by simp
  show "\<nabla>\<^sup>2 (\<lambda>y. f y + g y) x $ i = (\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i"
    using G\<phi> HESS_row_eq Hfg grad_fun_eq by fastforce
qed

lemma hessian_scaleR_on_C2:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes Cf: "Ck_on 2 f U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. c * f y) x = c *\<^sub>R \<nabla>\<^sup>2 f x"
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix i
  have openU: "open U"
    using Cf by (simp add: Ck_on_def)
  have Hf: "HESS f x :> \<nabla>\<^sup>2 f x"
    using Cf xU by (rule Ck_2_imp_hessian_exists)
  have Hcf: "HESS (\<lambda>y. c * f y) x :> \<nabla>\<^sup>2 (\<lambda>y. c * f y) x"
    using Ck_on_scaleR[OF Cf] xU by (subst Ck_2_imp_hessian_exists, auto)
  let ?\<phi> = "\<lambda>y. \<nabla> (\<lambda>z. c * f z) y $ i"
  let ?\<psi> = "\<lambda>y. c * (\<nabla> f y $ i)"
  have eqU: "\<And>y. y \<in> U \<Longrightarrow> ?\<phi> y = ?\<psi> y"
  proof -
    fix y assume yU: "y \<in> U"
    have Gf: "GDERIV f y :> \<nabla> f y"
      using Ck_2_imp_gradient_exists[OF Cf yU]
      by (blast intro: grad_fun_satisfies_GDERIV)
    have "GDERIV (\<lambda>z. c * f z) y :> c *\<^sub>R \<nabla> f y"
      by (rule GDERIV_cmult[OF Gf])
    hence "\<nabla> (\<lambda>z. c * f z) y = c *\<^sub>R \<nabla> f y"
      by (rule grad_fun_eq)
    thus "?\<phi> y = ?\<psi> y" by simp
  qed
  have Grow_f: "GDERIV (\<lambda>y. \<nabla> f y $ i) x :> (\<nabla>\<^sup>2 f x) $ i"
    by (rule HESS_row_gradient[OF Hf])
  have G\<psi>: "GDERIV ?\<psi> x :> c *\<^sub>R ((\<nabla>\<^sup>2 f x) $ i)"
    using GDERIV_cmult[OF Grow_f] by simp
  have D\<psi>: "(?\<psi> has_derivative (\<lambda>v. v \<bullet> (c *\<^sub>R ((\<nabla>\<^sup>2 f x) $ i)))) (at x)"
    using G\<psi> unfolding gderiv_def by simp
  have D\<phi>: "(?\<phi> has_derivative (\<lambda>v. v \<bullet> (c *\<^sub>R ((\<nabla>\<^sup>2 f x) $ i)))) (at x)"
    using D\<psi> openU xU by (fastforce simp: eqU has_derivative_transform_within_open)
  have G\<phi>: "GDERIV ?\<phi> x :> c *\<^sub>R ((\<nabla>\<^sup>2 f x) $ i)"
    using D\<phi> unfolding gderiv_def by simp
  show "\<nabla>\<^sup>2 (\<lambda>y. c * f y) x $ i = (c *\<^sub>R \<nabla>\<^sup>2 f x) $ i"
    using G\<phi> HESS_row_eq Hcf grad_fun_eq by fastforce
qed

lemma hessian_sub_on_C2:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Cf: "Ck_on 2 f U"
      and Cg: "Ck_on 2 g U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. f y - g y) x = \<nabla>\<^sup>2 f x - \<nabla>\<^sup>2 g x"
proof -
  have "\<nabla>\<^sup>2 (\<lambda>y. f y + (-1) * g y) x = \<nabla>\<^sup>2 f x + (-1) *\<^sub>R \<nabla>\<^sup>2 g x"
  proof (subst hessian_add_on_C2)
    show "Ck_on 2 f U"
      by (rule Cf)
    show "Ck_on 2 (\<lambda>y. (-1) * g y) U"
      using Ck_on_scaleR[OF Cg] by (metis ext real_scaleR_def)
    show "x \<in> U"
      by (rule xU)
    show "\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 (\<lambda>y. - 1 * g y) x = \<nabla>\<^sup>2 f x + - 1 *\<^sub>R \<nabla>\<^sup>2 g x"
      by (metis Cg hessian_scaleR_on_C2 xU)
  qed
  thus ?thesis by simp
qed

lemma hessian_sum_on_C2:
  fixes F :: "'i \<Rightarrow> real^'n::finite \<Rightarrow> real"
  assumes fin: "finite I"
      and C2: "\<And>i. i \<in> I \<Longrightarrow> Ck_on 2 (F i) U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. \<Sum>i\<in>I. F i y) x = (\<Sum>i\<in>I. \<nabla>\<^sup>2 (F i) x)"
  using fin C2
proof (induction rule: finite_induct)
  case empty
  show ?case by (simp add: hessian_const_zero)
next
  case (insert i I)
  have Ci: "Ck_on 2 (F i) U"
    using insert.prems by simp
  have openU: "open U"
    using Ci by (simp add: Ck_on_def)
  have C2_I: "\<And>j. j \<in> I \<Longrightarrow> Ck_on 2 (F j) U"
    using insert.prems by simp
  have CI: "Ck_on 2 (\<lambda>y. \<Sum>j\<in>I. F j y) U"
  proof (cases "I = {}")
    case True
    then show ?thesis
      using Ck_on_const[OF openU] by simp
  next
    case False
    then show ?thesis
      using Ck_on_sum[OF insert.hyps(1) False C2_I]
      by presburger
  qed
  have IH: "\<nabla>\<^sup>2 (\<lambda>y. \<Sum>j\<in>I. F j y) x = (\<Sum>j\<in>I. \<nabla>\<^sup>2 (F j) x)"
    using insert.IH C2_I by blast
  have "\<nabla>\<^sup>2 (\<lambda>y. \<Sum>j\<in>insert i I. F j y) x
        = \<nabla>\<^sup>2 (\<lambda>y. F i y + (\<Sum>j\<in>I. F j y)) x"
    by (simp add: insert.hyps(1,2))
  also have "\<dots> = \<nabla>\<^sup>2 (F i) x + \<nabla>\<^sup>2 (\<lambda>y. \<Sum>j\<in>I. F j y) x"
    by (rule hessian_add_on_C2[OF Ci CI xU])
  also have "\<dots> = \<nabla>\<^sup>2 (F i) x + (\<Sum>j\<in>I. \<nabla>\<^sup>2 (F j) x)"
    by (simp add: IH)
  also have "\<dots> = (\<Sum>j\<in>insert i I. \<nabla>\<^sup>2 (F j) x)"
    using insert.hyps by simp
  finally show ?case.
qed

lemma second_directional_derivative_eq_hessian_quadratic_form:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes C2: "Ck_on 2 f U"
      and xU: "x \<in> U"
  shows "frechet_derivative (\<lambda>y. frechet_derivative f (at y) v) (at x) v
       = v \<bullet> ((\<nabla>\<^sup>2 f x) *v v)"
proof -
  have openU: "open U"
    using C2 by (simp add: Ck_on_def)

  have H: "HESS f x :> \<nabla>\<^sup>2 f x"
    using C2 xU by (rule Ck_2_imp_hessian_exists)

  have eqU: "\<And>y. y \<in> U \<Longrightarrow> frechet_derivative f (at y) v = v \<bullet> \<nabla> f y"
  proof -
    fix y
    assume yU: "y \<in> U"

    from Ck_2_imp_gradient_exists[OF C2 yU]
    obtain g where g: "GDERIV f y :> g"
      by blast

    have Gy: "GDERIV f y :> \<nabla> f y"
      using g by (rule grad_fun_satisfies_GDERIV)

    have "(f has_derivative (\<lambda>w. w \<bullet> \<nabla> f y)) (at y)"
      using Gy unfolding gderiv_def by simp
    hence "frechet_derivative f (at y) = (\<lambda>w. w \<bullet> \<nabla> f y)"
      by (subst frechet_derivative_at, auto)

    thus "frechet_derivative f (at y) v = v \<bullet> \<nabla> f y"
      by simp
  qed
  have "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. frechet_derivative f (at y) v = v \<bullet> \<nabla> f y)"
    using openU xU eqU by blast
  then have ev_eq: "eventually (\<lambda>y. frechet_derivative f (at y) v = v \<bullet> \<nabla> f y) (nhds x)"
    by (simp add: eventually_nhds)
  have Dgrad: "(\<nabla> f has_derivative (*v) (\<nabla>\<^sup>2 f x)) (at x)"
    using H unfolding has_hessian_def by simp
  have Dcomp: "((\<lambda>y. v \<bullet> \<nabla> f y) has_derivative (\<lambda>h. v \<bullet> (((*v) (\<nabla>\<^sup>2 f x)) h))) (at x)"
    using Dgrad by (auto intro!: derivative_eq_intros)
  have Dfd: "((\<lambda>y. frechet_derivative f (at y) v) has_derivative
       (\<lambda>h. v \<bullet> (((*v) (\<nabla>\<^sup>2 f x)) h))) (at x)"
    by (metis (no_types, lifting) Dcomp eqU has_derivative_transform_within_open openU xU)
  have FD: "frechet_derivative (\<lambda>y. frechet_derivative f (at y) v) (at x)
    = (\<lambda>h. v \<bullet> (((*v) (\<nabla>\<^sup>2 f x)) h))"
    by (metis Dfd frechet_derivative_at)
  show ?thesis
    by (simp add: FD)
qed

subsection \<open>Outer product of vectors\<close>

definition outer_prod :: "real^'n \<Rightarrow> real^'n \<Rightarrow> real^'n^'n"
  where "outer_prod a b = (\<chi> i j. a $ i * b $ j)"

lemma outer_prod_component [simp]:
  "outer_prod a b $ i $ j = a $ i * b $ j"
  by (simp add: outer_prod_def)

lemma outer_prod_row:
  "outer_prod a b $ i = (a $ i) *\<^sub>R b"
  by (simp add: vec_eq_iff outer_prod_def)

lemma outer_prod_commute:
  "transpose (outer_prod a b) = outer_prod b a"
  by (simp add: vec_eq_iff transpose_def outer_prod_def mult.commute)

lemma outer_prod_add_left:
  "outer_prod (a + b) c = outer_prod a c + outer_prod b c"
  by (simp add: vec_eq_iff outer_prod_def distrib_right)

lemma outer_prod_add_right:
  "outer_prod a (b + c) = outer_prod a b + outer_prod a c"
  by (simp add: vec_eq_iff outer_prod_def distrib_left)

lemma outer_prod_scaleR_left:
  "outer_prod (c *\<^sub>R a) b = c *\<^sub>R outer_prod a b"
  by (simp add: vec_eq_iff outer_prod_def)

lemma outer_prod_scaleR_right:
  "outer_prod a (c *\<^sub>R b) = c *\<^sub>R outer_prod a b"
  by (simp add: vec_eq_iff outer_prod_def)

lemma outer_prod_zero_left [simp]:
  "outer_prod 0 b = 0"
  by (simp add: vec_eq_iff outer_prod_def)

lemma outer_prod_zero_right [simp]:
  "outer_prod a 0 = 0"
  by (simp add: vec_eq_iff outer_prod_def)

lemma outer_prod_mult_vec:
  "outer_prod a b *v v = (b \<bullet> v) *\<^sub>R a"
  by (simp add: matrix_vector_mul_component outer_prod_row vec_eq_iff)


subsection \<open>Gradient product rule\<close>

lemma grad_fun_mult:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GDERIV f x :> gf"
      and "\<exists>gg. GDERIV g x :> gg"
  shows "\<nabla> (\<lambda>y. f y * g y) x = f x *\<^sub>R \<nabla> g x + g x *\<^sub>R \<nabla> f x"
proof -
  have Gf: "GDERIV f x :> \<nabla> f x"
    using assms(1) by (blast intro: grad_fun_satisfies_GDERIV)
  have Gg: "GDERIV g x :> \<nabla> g x"
    using assms(2) by (blast intro: grad_fun_satisfies_GDERIV)
  have "GDERIV (\<lambda>y. f y * g y) x :> f x *\<^sub>R \<nabla> g x + g x *\<^sub>R \<nabla> f x"
    by (rule GDERIV_mult[OF Gf Gg])
  thus ?thesis
    by (rule grad_fun_eq)
qed


subsection \<open>Hessian product rule\<close>

text \<open>
  \<open>\<nabla>\<^sup>2(fg) = f \<nabla>\<^sup>2g + g \<nabla>\<^sup>2f + \<nabla>f \<otimes> \<nabla>g + \<nabla>g \<otimes> \<nabla>f\<close> for \<open>C\<^sup>2\<close> functions
  \<open>f, g : \<real>\<^sup>n \<rightarrow> \<real>\<close>, where \<open>\<otimes>\<close> is the outer product @{const outer_prod}.
\<close>

lemma hessian_mult_on_C2:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Cf: "Ck_on 2 f U"
      and Cg: "Ck_on 2 g U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. f y * g y) x =
           f x *\<^sub>R \<nabla>\<^sup>2 g x + g x *\<^sub>R \<nabla>\<^sup>2 f x
         + outer_prod (\<nabla> f x) (\<nabla> g x)
         + outer_prod (\<nabla> g x) (\<nabla> f x)"
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix i

  have openU: "open U"
    using Cf by (simp add: Ck_on_def)

  (* Hessians exist *)
  have Hf: "HESS f x :> \<nabla>\<^sup>2 f x"
    using Cf xU by (rule Ck_2_imp_hessian_exists)
  have Hg: "HESS g x :> \<nabla>\<^sup>2 g x"
    using Cg xU by (rule Ck_2_imp_hessian_exists)

  have Cfh: "Ck_on 2 (\<lambda>y. f y * g y) U"
    by (simp add: Cf Cg Ck_on_mult)

  have Hfg: "HESS (\<lambda>y. f y * g y) x :> \<nabla>\<^sup>2 (\<lambda>y. f y * g y) x"
    using Cfh xU by (rule Ck_2_imp_hessian_exists)

  (* Gradient existence on U *)
  have Gf_at: "\<And>y. y \<in> U \<Longrightarrow> GDERIV f y :> \<nabla> f y"
    using Ck_2_imp_gradient_exists[OF Cf]
    by (blast intro: grad_fun_satisfies_GDERIV)
  have Gg_at: "\<And>y. y \<in> U \<Longrightarrow> GDERIV g y :> \<nabla> g y"
    using Ck_2_imp_gradient_exists[OF Cg]
    by (blast intro: grad_fun_satisfies_GDERIV)

  (* Row gradients of Hessians *)
  have Hf_row: "GDERIV (\<lambda>y. \<nabla> f y $ i) x :> (\<nabla>\<^sup>2 f x) $ i"
    by (rule HESS_row_gradient[OF Hf])
  have Hg_row: "GDERIV (\<lambda>y. \<nabla> g y $ i) x :> (\<nabla>\<^sup>2 g x) $ i"
    by (rule HESS_row_gradient[OF Hg])

  (* The i-th component of \<nabla>(fg) *)
  (* On U: \<nabla>(fg)(y) $ i = f(y) * \<nabla>g(y) $ i + g(y) * \<nabla>f(y) $ i *)
  let ?\<phi> = "\<lambda>y. \<nabla> (\<lambda>z. f z * g z) y $ i"
  let ?\<psi> = "\<lambda>y. f y * (\<nabla> g y $ i) + g y * (\<nabla> f y $ i)"

  have eqU: "\<And>y. y \<in> U \<Longrightarrow> ?\<phi> y = ?\<psi> y"
  proof -
    fix y assume yU: "y \<in> U"
    have "GDERIV (\<lambda>z. f z * g z) y :> f y *\<^sub>R \<nabla> g y + g y *\<^sub>R \<nabla> f y"
      by (rule GDERIV_mult[OF Gf_at[OF yU] Gg_at[OF yU]])
    hence "\<nabla> (\<lambda>z. f z * g z) y = f y *\<^sub>R \<nabla> g y + g y *\<^sub>R \<nabla> f y"
      by (rule grad_fun_eq)
    thus "?\<phi> y = ?\<psi> y" by simp
  qed

  (* Gradient of y \<mapsto> f(y) * \<nabla>g(y)$i *)
  have Gf_x: "GDERIV f x :> \<nabla> f x"
    using Gf_at[OF xU] .
  have Gg_x: "GDERIV g x :> \<nabla> g x"
    using Gg_at[OF xU] .

  have G_term1: "GDERIV (\<lambda>y. f y * (\<nabla> g y $ i)) x :>
                   f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x"
    by (rule GDERIV_mult[OF Gf_x Hg_row])

  (* Gradient of y \<mapsto> g(y) * \<nabla>f(y)$i *)
  have G_term2: "GDERIV (\<lambda>y. g y * (\<nabla> f y $ i)) x :>
                   g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x"
    by (rule GDERIV_mult[OF Gg_x Hf_row])

  (* Gradient of \<psi> by addition *)
  have G\<psi>: "GDERIV ?\<psi> x :>
               (f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
             + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)"
    by (rule GDERIV_add[OF G_term1 G_term2])

  (* Transfer from \<psi> to \<phi> using agreement on U *)
  have D\<psi>: "(?\<psi> has_derivative
      (\<lambda>v. v \<bullet> ((f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
              + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)))) (at x)"
    using G\<psi> unfolding gderiv_def by simp

  have D\<phi>: "(?\<phi> has_derivative
      (\<lambda>v. v \<bullet> ((f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
              + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)))) (at x)"
    using D\<psi> openU xU by (fastforce simp: eqU has_derivative_transform_within_open)

  have G\<phi>: "GDERIV ?\<phi> x :>
               (f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
             + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)"
    using D\<phi> unfolding gderiv_def by simp

  (* Assemble the row *)
  have row_eq: "\<nabla> ?\<phi> x =
      (f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
    + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)"
    by (rule grad_fun_eq[OF G\<phi>])

  have lhs: "\<nabla>\<^sup>2 (\<lambda>y. f y * g y) x $ i = \<nabla> ?\<phi> x"
    using HESS_row_eq[OF Hfg] by simp

  (* Express the RHS in terms of the target matrix *)
  let ?M = "f x *\<^sub>R \<nabla>\<^sup>2 g x + g x *\<^sub>R \<nabla>\<^sup>2 f x
          + outer_prod (\<nabla> f x) (\<nabla> g x)
          + outer_prod (\<nabla> g x) (\<nabla> f x)"

  have rhs: "?M $ i =
      (f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
    + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)"
    by (simp add: vec_eq_iff outer_prod_row algebra_simps)

  show "\<nabla>\<^sup>2 (\<lambda>y. f y * g y) x $ i = ?M $ i"
    using lhs row_eq rhs by simp
qed

lemma grad_fun_compose:
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and F :: "real^'n::finite \<Rightarrow> real^'m"
  assumes "\<exists>gg. GDERIV g (F x) :> gg"
      and "F differentiable (at x)"
  shows "\<nabla> (\<lambda>y. g (F y)) x = transpose (jacobian F (at x)) *v \<nabla> g (F x)"
proof -
  have Gg: "GDERIV g (F x) :> \<nabla> g (F x)"
    using assms(1) by (blast intro: grad_fun_satisfies_GDERIV)
  have "GDERIV (\<lambda>y. g (F y)) x :> transpose (jacobian F (at x)) *v \<nabla> g (F x)"
    by (rule GDERIV_compose'[OF Gg assms(2)])
  thus ?thesis
    by (rule grad_fun_eq)
qed


subsection \<open>Component closure\<close>

lemma Ck_on_component:
  fixes F :: "'a::real_normed_vector \<Rightarrow> real^'m::finite"
  assumes "Ck_on k F U"
  shows "Ck_on k (\<lambda>x. F x $ r) U"
  by (rule Ck_on_bounded_linear_compose[OF bounded_linear_vec_nth assms])


text \<open>
  For \<open>C\<^sup>2\<close> maps \<open>g\<close> and \<open>F\<close>:
  \<open>\<nabla>\<^sup>2(g \<circ> F)(x) = J\<^sup>T ** \<nabla>\<^sup>2g(F x) ** J + \<Sigma>\<^sub>r (\<nabla>g(F x) $ r) *\<^sub>R \<nabla>\<^sup>2F\<^sub>r(x)\<close>,
  where \<open>J = jacobian F (at x)\<close> and \<open>F\<^sub>r y = F y $ r\<close>.
\<close>

lemma hessian_compose_on_C2:
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and F :: "real^'n::finite \<Rightarrow> real^'m"
  assumes Cg: "Ck_on 2 g V"
      and CF: "Ck_on 2 F U"
      and FUV: "\<And>y. y \<in> U \<Longrightarrow> F y \<in> V"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. g (F y)) x =
           transpose (jacobian F (at x)) ** \<nabla>\<^sup>2 g (F x) ** jacobian F (at x)
         + (\<Sum>r\<in>UNIV. (\<nabla> g (F x) $ r) *\<^sub>R \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x)"
         (is "?LHS = ?RHS")
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix i :: 'n

  have openU: "open U" using CF by (simp add: Ck_on_def)
  have openV: "open V" using Cg by (simp add: Ck_on_def)

  (* C\<^sup>2 closure: g \<circ> F is C\<^sup>2 on U *)
  have CgF: "Ck_on 2 (\<lambda>y. g (F y)) U"
    using Ck_on_compose[OF Cg CF FUV] .

  (* Component C\<^sup>2 *)
  have CF_r: "\<And>r. Ck_on 2 (\<lambda>y. F y $ r) U"
    using CF by (rule Ck_on_component)

  (* Hessians exist *)
  have HgF: "HESS (\<lambda>y. g (F y)) x :> \<nabla>\<^sup>2 (\<lambda>y. g (F y)) x"
    using CgF xU by (rule Ck_2_imp_hessian_exists)
  have Hg: "HESS g (F x) :> \<nabla>\<^sup>2 g (F x)"
    using Cg FUV[OF xU] by (rule Ck_2_imp_hessian_exists)
  have HF_r: "\<And>r. HESS (\<lambda>y. F y $ r) x :> \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x"
    using CF_r xU by (rule Ck_2_imp_hessian_exists)

  (* Differentiability of F on U *)
  have F_diff: "\<And>y. y \<in> U \<Longrightarrow> F differentiable (at y)"
  proof -
    fix y assume "y \<in> U"
    then have "Ck_at 2 F y"
      using CF by (simp add: Ck_on_def)
    thus "F differentiable (at y)"
      by (metis Ck_at.simps(2) Suc_1)
  qed

  (* Gradient existence *)
  have Gg_at: "\<And>z. z \<in> V \<Longrightarrow> GDERIV g z :> \<nabla> g z"
    using Ck_2_imp_gradient_exists[OF Cg]
    by (blast intro: grad_fun_satisfies_GDERIV)

  have GF_r_at: "\<And>r y. y \<in> U \<Longrightarrow> GDERIV (\<lambda>y. F y $ r) y :> \<nabla> (\<lambda>y. F y $ r) y"
    using Ck_2_imp_gradient_exists[OF CF_r]
    by (blast intro: grad_fun_satisfies_GDERIV)

  (* Row gradients of component Hessians *)
  have HF_r_row: "\<And>r. GDERIV (\<lambda>y. \<nabla> (\<lambda>z. F z $ r) y $ i) x :> (\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i"
    by (rule HESS_row_gradient[OF HF_r])

  (* Row gradient of the Hessian of g *)
  have Hg_row: "\<And>r. GDERIV (\<lambda>z. \<nabla> g z $ r) (F x) :> (\<nabla>\<^sup>2 g (F x)) $ r"
    by (rule HESS_row_gradient[OF Hg])

  (* On U, \<nabla>(g \<circ> F)(y) $ i = \<Sigma>_r (\<nabla>(F_r)(y) $ i) * (\<nabla>g(F(y)) $ r) *)
  let ?\<phi> = "\<lambda>y. \<nabla> (\<lambda>z. g (F z)) y $ i"
  let ?\<psi> = "\<lambda>y. \<Sum>r\<in>UNIV. \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r"

  have eqU: "\<And>y. y \<in> U \<Longrightarrow> ?\<phi> y = ?\<psi> y"
  proof -
    fix y :: "real^'n"
    assume yU: "y \<in> U"

    have Fy_V: "F y \<in> V" using FUV[OF yU] .
    have Gy: "GDERIV g (F y) :> \<nabla> g (F y)"
      using Gg_at[OF Fy_V] .
    have Fy_diff: "F differentiable (at y)"
      using F_diff[OF yU] .

    have grad_comp: "\<nabla> (\<lambda>z. g (F z)) y = transpose (jacobian F (at y)) *v \<nabla> g (F y)"
      by (rule grad_fun_compose[where g=g and F=F], blast intro: Gy, rule Fy_diff)

    have "?\<phi> y = (transpose (jacobian F (at y)) *v \<nabla> g (F y)) $ i"
      using grad_comp by simp
    also have "\<dots> = (\<Sum>r\<in>UNIV. transpose (jacobian F (at y)) $ i $ r * \<nabla> g (F y) $ r)"
      by (simp add: matrix_vector_mult_def)
    also have "\<dots> = (\<Sum>r\<in>UNIV. jacobian F (at y) $ r $ i * \<nabla> g (F y) $ r)"
      by (simp add: transpose_def)
    also have "\<dots> = ?\<psi> y"
    proof (rule sum.cong[OF refl])
      fix r :: 'm
      assume "r \<in> UNIV"

      have Fr_diff: "(\<lambda>z. F z $ r) differentiable (at y)"
      proof -
        have FD: "(F has_derivative frechet_derivative F (at y)) (at y)"
          using Fy_diff frechet_derivative_works[THEN iffD1] by blast

        have Hcomp:"((\<lambda>z. F z \<bullet> axis r 1) has_derivative
                     (\<lambda>h. frechet_derivative F (at y) h \<bullet> axis r 1)) (at y within UNIV)"
          using FD
          by (subst (asm) has_derivative_componentwise_within[where S = UNIV],
              auto simp: Basis_vec_def)

        have comp_fun: "(\<lambda>z. F z \<bullet> axis r 1) = (\<lambda>z. F z $ r)"
          by (rule ext) (simp add: cart_eq_inner_axis)
        have coord_D: "((\<lambda>z. F z $ r) has_derivative
                        (\<lambda>h. frechet_derivative F (at y) h $ r)) (at y)"
          using Hcomp by (simp add: inner_axis)
        then show ?thesis
          unfolding differentiable_def by blast
      qed

      show "jacobian F (at y) $ r $ i * \<nabla> g (F y) $ r =  \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r"
      proof -
        have Jcomp: "jacobian F (at y) $ r $ i = frechet_derivative (\<lambda>z. F z $ r) (at y) (axis i 1)"
          using jacobian_component[OF Fy_diff, of r i] by simp

        have GFr: "GDERIV (\<lambda>z. F z $ r) y :> \<nabla> (\<lambda>z. F z $ r) y"
          using Fr_diff_imp_gradient_exists[OF Fr_diff]
          by (blast intro: grad_fun_satisfies_GDERIV)

        have DFr: "((\<lambda>z. F z $ r) has_derivative (\<lambda>h. h \<bullet> \<nabla> (\<lambda>z. F z $ r) y)) (at y)"
          using GFr unfolding gderiv_def by simp

        have FD_eq:  "frechet_derivative (\<lambda>z. F z $ r) (at y) = (\<lambda>h. h \<bullet> \<nabla> (\<lambda>z. F z $ r) y)"
          by (subst frechet_derivative_at[OF DFr], simp)

        have "frechet_derivative (\<lambda>z. F z $ r) (at y) (axis i 1)
              = axis i 1 \<bullet> \<nabla> (\<lambda>z. F z $ r) y"
          by (simp add: FD_eq)
        also have "... = \<nabla> (\<lambda>z. F z $ r) y $ i"
          using inner_commute by (simp add: cart_eq_inner_axis, auto)
        finally show ?thesis
          using Jcomp by simp
      qed
      then have "jacobian F (at y) $ r $ i = \<nabla> (\<lambda>z. F z $ r) y $ i"
        using jacobian_component[OF Fy_diff]
        by (metis (mono_tags, lifting) Fr_diff Fr_diff_imp_gradient_exists cart_eq_inner_axis
            frechet_derivative_at grad_fun_eq gderiv_def inner_commute)
      qed
      thus "\<nabla> (\<lambda>z. g (F z)) y $ i = (\<Sum>r\<in>UNIV. \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r)"
        using calculation by presburger
  qed

  (* Differentiate \<psi> at x using GDERIV_sum, GDERIV_mult *)
  (* \<psi> y = \<Sigma>_r a_r y * b_r y, where a_r y = \<nabla>(F_r)(y) $ i and b_r y = \<nabla>g(F y) $ r *)

  have Ga_r: "\<And>r. GDERIV (\<lambda>y. \<nabla> (\<lambda>z. F z $ r) y $ i) x :> (\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i"
    using HF_r_row .

  have Gb_r: "\<And>r. GDERIV (\<lambda>y. \<nabla> g (F y) $ r) x :> transpose (jacobian F (at x)) *v ((\<nabla>\<^sup>2 g (F x)) $ r)"
  proof -
    fix r :: 'm
    have "GDERIV (\<lambda>z. \<nabla> g z $ r) (F x) :> (\<nabla>\<^sup>2 g (F x)) $ r"
      using Hg_row .
    thus "GDERIV (\<lambda>y. \<nabla> g (F y) $ r) x :> transpose (jacobian F (at x)) *v ((\<nabla>\<^sup>2 g (F x)) $ r)"
      by (rule GDERIV_compose'[OF _ F_diff[OF xU]])
  qed

  have G_term_r: "\<And>r. GDERIV (\<lambda>y. \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r) x :>
      \<nabla> (\<lambda>z. F z $ r) x $ i *\<^sub>R (transpose (jacobian F (at x)) *v ((\<nabla>\<^sup>2 g (F x)) $ r))
    + \<nabla> g (F x) $ r *\<^sub>R ((\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i)"
    by (rule GDERIV_mult[OF Ga_r Gb_r])

  define G_r where "G_r r =
      \<nabla> (\<lambda>z. F z $ r) x $ i *\<^sub>R (transpose (jacobian F (at x)) *v ((\<nabla>\<^sup>2 g (F x)) $ r))
    + \<nabla> g (F x) $ r *\<^sub>R ((\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i)" for r

  have G\<psi>: "GDERIV ?\<psi> x :> (\<Sum>r\<in>UNIV. G_r r)"
      using G_term_r by (simp add: G_r_def GDERIV_sum)

  (* Transfer from \<psi> to \<phi> *)
  have D\<psi>: "(?\<psi> has_derivative (\<lambda>v. v \<bullet> (\<Sum>r\<in>UNIV. G_r r))) (at x)"
    using G\<psi> unfolding gderiv_def .

  have D\<phi>: "(?\<phi> has_derivative (\<lambda>v. v \<bullet> (\<Sum>r\<in>UNIV. G_r r))) (at x)"
    using D\<psi> openU xU by (force simp: eqU has_derivative_transform_within_open)

  have G\<phi>: "GDERIV ?\<phi> x :> (\<Sum>r\<in>UNIV. G_r r)"
    using D\<phi> unfolding gderiv_def by simp

  have row_eq: "\<nabla> ?\<phi> x = (\<Sum>r\<in>UNIV. G_r r)"
    by (rule grad_fun_eq[OF G\<phi>])

  have lhs: "?LHS $ i = \<nabla> ?\<phi> x"
    using HESS_row_eq[OF HgF] by simp

  (* Match the RHS row *)

  have sum_second: "(\<Sum>r\<in>UNIV. \<nabla> g (F x) $ r *\<^sub>R ((\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i))
                  = (\<Sum>r\<in>UNIV. (\<nabla> g (F x) $ r) *\<^sub>R \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i"
    by simp

  (* matrix algebra: the key identity relating the sum to J^T H J *)
  have sum_first: "(\<Sum>r\<in>UNIV. \<nabla> (\<lambda>z. F z $ r) x $ i *\<^sub>R
                      (transpose (jacobian F (at x)) *v ((\<nabla>\<^sup>2 g (F x)) $ r)))
                 = (transpose (jacobian F (at x)) ** \<nabla>\<^sup>2 g (F x) ** jacobian F (at x)) $ i"
  proof -
    have grad_jac: "\<nabla> (\<lambda>z. F z $ r) x $ i = jacobian F (at x) $ r $ i" for r
    proof -
      have Fr_diff: "(\<lambda>z. F z $ r) differentiable (at x)"
        using F_diff[OF xU] by (metis CF_r Ck_at.simps(2) Ck_on_def Suc_1 xU)
      have GFr: "GDERIV (\<lambda>z. F z $ r) x :> \<nabla> (\<lambda>z. F z $ r) x"
        using Fr_diff_imp_gradient_exists[OF Fr_diff]
        by (blast intro: grad_fun_satisfies_GDERIV)
      have FD_eq: "frechet_derivative (\<lambda>z. F z $ r) (at x) = (\<lambda>h. h \<bullet> \<nabla> (\<lambda>z. F z $ r) x)"
        using GFr unfolding gderiv_def  by (metis frechet_derivative_at)
      have "jacobian F (at x) $ r $ i = frechet_derivative (\<lambda>z. F z $ r) (at x) (axis i 1)"
        using jacobian_component[OF F_diff[OF xU]].
      also have "\<dots> = \<nabla> (\<lambda>z. F z $ r) x $ i"
        by (simp add: FD_eq cart_eq_inner_axis inner_commute,
            metis (no_types, lifting) ext FD_eq cart_eq_inner_axis)
      finally show ?thesis by simp
    qed
    then have "(\<Sum>r\<in>UNIV. \<nabla> (\<lambda>z. F z $ r) x $ i *\<^sub>R  (transpose (jacobian F (at x)) *v ((\<nabla>\<^sup>2 g (F x)) $ r)))
        = (\<Sum>r\<in>UNIV. jacobian F (at x) $ r $ i *\<^sub>R   (transpose (jacobian F (at x)) *v ((\<nabla>\<^sup>2 g (F x)) $ r)))"
      by simp
    also have "\<dots> = (transpose (jacobian F (at x)) ** \<nabla>\<^sup>2 g (F x) ** jacobian F (at x)) $ i"
      by (rule row_transpose_mult_both[symmetric])
    finally show ?thesis.
  qed
  then have "(\<Sum>r\<in>UNIV. G_r r) = ?RHS $ i"
    unfolding G_r_def sum.distrib vector_add_component
    using sum_second by (rule arg_cong2[where f = "(+)"])
  then show "?LHS $ i = ?RHS $ i"
    using lhs row_eq by simp
qed


subsection \<open>Affine composition (special case)\<close>

text \<open>For affine \<open>F y = A *v y + b\<close> the chain rule becomes
  \<open>\<nabla>\<^sup>2(g \<circ> F)(x) = A\<^sup>T ** \<nabla>\<^sup>2g(A *v x + b) ** A\<close>.\<close>

lemma hessian_affine_compose_on_C2:
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and A :: "real^'n^'m"
    and b :: "real^'m"
  assumes Cg: "Ck_on 2 g V"
      and sub: "\<And>y. y \<in> U \<Longrightarrow> A *v y + b \<in> V"
      and oU: "open U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. g (A *v y + b)) x = transpose A ** \<nabla>\<^sup>2 g (A *v x + b) ** A"
proof -
  define F where "F y = A *v y + b" for y
  have bl: "bounded_linear ((*v) A)"
    by simp
  have CF: "Ck_on 2 F U"
    unfolding F_def using Ck_on_add[OF Ck_on_bounded_linear[OF bl oU] Ck_on_const[OF oU]] .
  have F_diff: "\<And>y. F differentiable (at y)"
    unfolding F_def by (simp add: bounded_linear_imp_differentiable)
  have jac_eq: "jacobian F (at y) = A" for y
    unfolding jacobian_def F_def by (metis bl bounded_linear_imp_has_derivative
              frechet_derivative_at has_derivative_add_const matrix_of_matrix_vector_mul)
  have comp_hess_zero: "\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x = 0" for r
  proof -
    have fn_eq: "(\<lambda>y. F y $ r) = (\<lambda>y. b $ r + y \<bullet> (A $ r))"
    proof (rule ext)
      fix y :: "real^'n"
      have "F y $ r = (A *v y + b) $ r"
        by (simp add: F_def)
      also have "\<dots> = (\<Sum>j\<in>UNIV. A $ r $ j * y $ j) + b $ r"
        by (simp add: matrix_vector_mult_def)
      also have "\<dots> = b $ r + y \<bullet> (A $ r)"
        by (simp add: inner_vec_def, meson mult.commute)
      finally show "F y $ r = b $ r + y \<bullet> (A $ r)".
    qed
    have "HESS (\<lambda>y. b $ r + y \<bullet> (A $ r)) x :> 0"
      by (rule HESS_affine_zero)
    hence "HESS (\<lambda>y. F y $ r) x :> 0"
      by (simp add: fn_eq)
    thus ?thesis
      by (metis hess_fun_eq)
  qed
  then have grad_zero_sum: "(\<Sum>r\<in>UNIV. \<nabla> g (F x) $ r *\<^sub>R \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) = 0"
    by simp
  have "\<nabla>\<^sup>2 (\<lambda>y. g (F y)) x =
         transpose (jacobian F (at x)) ** \<nabla>\<^sup>2 g (F x) ** jacobian F (at x)
       + (\<Sum>r\<in>UNIV. \<nabla> g (F x) $ r *\<^sub>R \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x)"
    by (rule hessian_compose_on_C2[OF Cg CF _ xU], simp add: F_def sub)
  also have "\<dots> = transpose A ** \<nabla>\<^sup>2 g (F x) ** A + 0"
    by (simp add: jac_eq grad_zero_sum)
  also have "\<dots> = transpose A ** \<nabla>\<^sup>2 g (A *v x + b) ** A"
    by (simp add: F_def)
  ultimately show ?thesis by (simp add: F_def)
qed

subsection \<open>Summary of the hierarchy\<close>

text \<open>
  \<^const>\<open>Ck_at\<close> implies \<^const>\<open>k_times_Fr_differentiable_at\<close>, and \<^const>\<open>Ck_on\<close> implies
  \<^const>\<open>k_times_Fr_differentiable_on\<close>.  For \<open>f :: real \<Rightarrow> real\<close>,
  \<^const>\<open>k_times_Fr_differentiable_at\<close> agrees with \<^const>\<open>k_times_differentiable_at\<close>,
  and \<^const>\<open>Ck_on\<close> with \<^const>\<open>C_k_on\<close>.
\<close>

end
