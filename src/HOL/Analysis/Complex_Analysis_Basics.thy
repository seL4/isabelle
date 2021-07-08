(*  Author: John Harrison, Marco Maggesi, Graziano Gentili, Gianni Ciolli, Valentina Bruno
    Ported from "hol_light/Multivariate/canal.ml" by L C Paulson (2014)
*)

section \<open>Complex Analysis Basics\<close>
text \<open>Definitions of analytic and holomorphic functions, limit theorems, complex differentiation\<close>

theory Complex_Analysis_Basics
  imports Derivative "HOL-Library.Nonpos_Ints"
begin

subsection\<^marker>\<open>tag unimportant\<close>\<open>General lemmas\<close>

lemma nonneg_Reals_cmod_eq_Re: "z \<in> \<real>\<^sub>\<ge>\<^sub>0 \<Longrightarrow> norm z = Re z"
  by (simp add: complex_nonneg_Reals_iff cmod_eq_Re)

lemma fact_cancel:
  fixes c :: "'a::real_field"
  shows "of_nat (Suc n) * c / (fact (Suc n)) = c / (fact n)"
  using of_nat_neq_0 by force

lemma vector_derivative_cnj_within:
  assumes "at x within A \<noteq> bot" and "f differentiable at x within A"
  shows   "vector_derivative (\<lambda>z. cnj (f z)) (at x within A) = 
             cnj (vector_derivative f (at x within A))" (is "_ = cnj ?D")
proof -
  let ?D = "vector_derivative f (at x within A)"
  from assms have "(f has_vector_derivative ?D) (at x within A)"
    by (subst (asm) vector_derivative_works)
  hence "((\<lambda>x. cnj (f x)) has_vector_derivative cnj ?D) (at x within A)"
    by (rule has_vector_derivative_cnj)
  thus ?thesis using assms by (auto dest: vector_derivative_within)
qed

lemma vector_derivative_cnj:
  assumes "f differentiable at x"
  shows   "vector_derivative (\<lambda>z. cnj (f z)) (at x) = cnj (vector_derivative f (at x))"
  using assms by (intro vector_derivative_cnj_within) auto

lemma
  shows open_halfspace_Re_lt: "open {z. Re(z) < b}"
    and open_halfspace_Re_gt: "open {z. Re(z) > b}"
    and closed_halfspace_Re_ge: "closed {z. Re(z) \<ge> b}"
    and closed_halfspace_Re_le: "closed {z. Re(z) \<le> b}"
    and closed_halfspace_Re_eq: "closed {z. Re(z) = b}"
    and open_halfspace_Im_lt: "open {z. Im(z) < b}"
    and open_halfspace_Im_gt: "open {z. Im(z) > b}"
    and closed_halfspace_Im_ge: "closed {z. Im(z) \<ge> b}"
    and closed_halfspace_Im_le: "closed {z. Im(z) \<le> b}"
    and closed_halfspace_Im_eq: "closed {z. Im(z) = b}"
  by (intro open_Collect_less closed_Collect_le closed_Collect_eq continuous_on_Re
            continuous_on_Im continuous_on_id continuous_on_const)+

lemma closed_complex_Reals: "closed (\<real> :: complex set)"
proof -
  have "(\<real> :: complex set) = {z. Im z = 0}"
    by (auto simp: complex_is_Real_iff)
  then show ?thesis
    by (metis closed_halfspace_Im_eq)
qed

lemma closed_Real_halfspace_Re_le: "closed (\<real> \<inter> {w. Re w \<le> x})"
  by (simp add: closed_Int closed_complex_Reals closed_halfspace_Re_le)

lemma closed_nonpos_Reals_complex [simp]: "closed (\<real>\<^sub>\<le>\<^sub>0 :: complex set)"
proof -
  have "\<real>\<^sub>\<le>\<^sub>0 = \<real> \<inter> {z. Re(z) \<le> 0}"
    using complex_nonpos_Reals_iff complex_is_Real_iff by auto
  then show ?thesis
    by (metis closed_Real_halfspace_Re_le)
qed

lemma closed_Real_halfspace_Re_ge: "closed (\<real> \<inter> {w. x \<le> Re(w)})"
  using closed_halfspace_Re_ge
  by (simp add: closed_Int closed_complex_Reals)

lemma closed_nonneg_Reals_complex [simp]: "closed (\<real>\<^sub>\<ge>\<^sub>0 :: complex set)"
proof -
  have "\<real>\<^sub>\<ge>\<^sub>0 = \<real> \<inter> {z. Re(z) \<ge> 0}"
    using complex_nonneg_Reals_iff complex_is_Real_iff by auto
  then show ?thesis
    by (metis closed_Real_halfspace_Re_ge)
qed

lemma closed_real_abs_le: "closed {w \<in> \<real>. \<bar>Re w\<bar> \<le> r}"
proof -
  have "{w \<in> \<real>. \<bar>Re w\<bar> \<le> r} = (\<real> \<inter> {w. Re w \<le> r}) \<inter> (\<real> \<inter> {w. Re w \<ge> -r})"
    by auto
  then show "closed {w \<in> \<real>. \<bar>Re w\<bar> \<le> r}"
    by (simp add: closed_Int closed_Real_halfspace_Re_ge closed_Real_halfspace_Re_le)
qed

lemma real_lim:
  fixes l::complex
  assumes "(f \<longlongrightarrow> l) F" and "\<not> trivial_limit F" and "eventually P F" and "\<And>a. P a \<Longrightarrow> f a \<in> \<real>"
  shows  "l \<in> \<real>"
proof (rule Lim_in_closed_set[OF closed_complex_Reals _ assms(2,1)])
  show "eventually (\<lambda>x. f x \<in> \<real>) F"
    using assms(3, 4) by (auto intro: eventually_mono)
qed

lemma real_lim_sequentially:
  fixes l::complex
  shows "(f \<longlongrightarrow> l) sequentially \<Longrightarrow> (\<exists>N. \<forall>n\<ge>N. f n \<in> \<real>) \<Longrightarrow> l \<in> \<real>"
by (rule real_lim [where F=sequentially]) (auto simp: eventually_sequentially)

lemma real_series:
  fixes l::complex
  shows "f sums l \<Longrightarrow> (\<And>n. f n \<in> \<real>) \<Longrightarrow> l \<in> \<real>"
unfolding sums_def
by (metis real_lim_sequentially sum_in_Reals)

lemma Lim_null_comparison_Re:
  assumes "eventually (\<lambda>x. norm(f x) \<le> Re(g x)) F" "(g \<longlongrightarrow> 0) F" shows "(f \<longlongrightarrow> 0) F"
  by (rule Lim_null_comparison[OF assms(1)] tendsto_eq_intros assms(2))+ simp

subsection\<open>Holomorphic functions\<close>

definition\<^marker>\<open>tag important\<close> holomorphic_on :: "[complex \<Rightarrow> complex, complex set] \<Rightarrow> bool"
           (infixl "(holomorphic'_on)" 50)
  where "f holomorphic_on s \<equiv> \<forall>x\<in>s. f field_differentiable (at x within s)"

named_theorems\<^marker>\<open>tag important\<close> holomorphic_intros "structural introduction rules for holomorphic_on"

lemma holomorphic_onI [intro?]: "(\<And>x. x \<in> s \<Longrightarrow> f field_differentiable (at x within s)) \<Longrightarrow> f holomorphic_on s"
  by (simp add: holomorphic_on_def)

lemma holomorphic_onD [dest?]: "\<lbrakk>f holomorphic_on s; x \<in> s\<rbrakk> \<Longrightarrow> f field_differentiable (at x within s)"
  by (simp add: holomorphic_on_def)

lemma holomorphic_on_imp_differentiable_on:
    "f holomorphic_on s \<Longrightarrow> f differentiable_on s"
  unfolding holomorphic_on_def differentiable_on_def
  by (simp add: field_differentiable_imp_differentiable)

lemma holomorphic_on_imp_differentiable_at:
   "\<lbrakk>f holomorphic_on s; open s; x \<in> s\<rbrakk> \<Longrightarrow> f field_differentiable (at x)"
using at_within_open holomorphic_on_def by fastforce

lemma holomorphic_on_empty [holomorphic_intros]: "f holomorphic_on {}"
  by (simp add: holomorphic_on_def)

lemma holomorphic_on_open:
    "open s \<Longrightarrow> f holomorphic_on s \<longleftrightarrow> (\<forall>x \<in> s. \<exists>f'. DERIV f x :> f')"
  by (auto simp: holomorphic_on_def field_differentiable_def has_field_derivative_def at_within_open [of _ s])

lemma holomorphic_on_imp_continuous_on:
    "f holomorphic_on s \<Longrightarrow> continuous_on s f"
  by (metis field_differentiable_imp_continuous_at continuous_on_eq_continuous_within holomorphic_on_def)

lemma holomorphic_closedin_preimage_constant:
  assumes "f holomorphic_on D" 
  shows "closedin (top_of_set D) {z\<in>D. f z = a}"
  by (simp add: assms continuous_closedin_preimage_constant holomorphic_on_imp_continuous_on)

lemma holomorphic_closed_preimage_constant:
  assumes "f holomorphic_on UNIV" 
  shows "closed {z. f z = a}"
  using holomorphic_closedin_preimage_constant [OF assms] by simp

lemma holomorphic_on_subset [elim]:
    "f holomorphic_on s \<Longrightarrow> t \<subseteq> s \<Longrightarrow> f holomorphic_on t"
  unfolding holomorphic_on_def
  by (metis field_differentiable_within_subset subsetD)

lemma holomorphic_transform: "\<lbrakk>f holomorphic_on s; \<And>x. x \<in> s \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> g holomorphic_on s"
  by (metis field_differentiable_transform_within linordered_field_no_ub holomorphic_on_def)

lemma holomorphic_cong: "s = t ==> (\<And>x. x \<in> s \<Longrightarrow> f x = g x) \<Longrightarrow> f holomorphic_on s \<longleftrightarrow> g holomorphic_on t"
  by (metis holomorphic_transform)

lemma holomorphic_on_linear [simp, holomorphic_intros]: "((*) c) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_linear)

lemma holomorphic_on_const [simp, holomorphic_intros]: "(\<lambda>z. c) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_const)

lemma holomorphic_on_ident [simp, holomorphic_intros]: "(\<lambda>x. x) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_ident)

lemma holomorphic_on_id [simp, holomorphic_intros]: "id holomorphic_on s"
  unfolding id_def by (rule holomorphic_on_ident)

lemma holomorphic_on_compose:
  "f holomorphic_on s \<Longrightarrow> g holomorphic_on (f ` s) \<Longrightarrow> (g o f) holomorphic_on s"
  using field_differentiable_compose_within[of f _ s g]
  by (auto simp: holomorphic_on_def)

lemma holomorphic_on_compose_gen:
  "f holomorphic_on s \<Longrightarrow> g holomorphic_on t \<Longrightarrow> f ` s \<subseteq> t \<Longrightarrow> (g o f) holomorphic_on s"
  by (metis holomorphic_on_compose holomorphic_on_subset)

lemma holomorphic_on_balls_imp_entire:
  assumes "\<not>bdd_above A" "\<And>r. r \<in> A \<Longrightarrow> f holomorphic_on ball c r"
  shows   "f holomorphic_on B"
proof (rule holomorphic_on_subset)
  show "f holomorphic_on UNIV" unfolding holomorphic_on_def
  proof
    fix z :: complex
    from \<open>\<not>bdd_above A\<close> obtain r where r: "r \<in> A" "r > norm (z - c)"
      by (meson bdd_aboveI not_le)
    with assms(2) have "f holomorphic_on ball c r" by blast
    moreover from r have "z \<in> ball c r" by (auto simp: dist_norm norm_minus_commute)
    ultimately show "f field_differentiable at z"
      by (auto simp: holomorphic_on_def at_within_open[of _ "ball c r"])
  qed
qed auto

lemma holomorphic_on_balls_imp_entire':
  assumes "\<And>r. r > 0 \<Longrightarrow> f holomorphic_on ball c r"
  shows   "f holomorphic_on B"
proof (rule holomorphic_on_balls_imp_entire)
  {
    fix M :: real
    have "\<exists>x. x > max M 0" by (intro gt_ex)
    hence "\<exists>x>0. x > M" by auto
  }
  thus "\<not>bdd_above {(0::real)<..}" unfolding bdd_above_def
    by (auto simp: not_le)
qed (insert assms, auto)

lemma holomorphic_on_minus [holomorphic_intros]: "f holomorphic_on s \<Longrightarrow> (\<lambda>z. -(f z)) holomorphic_on s"
  by (metis field_differentiable_minus holomorphic_on_def)

lemma holomorphic_on_add [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s\<rbrakk> \<Longrightarrow> (\<lambda>z. f z + g z) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_add)

lemma holomorphic_on_diff [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s\<rbrakk> \<Longrightarrow> (\<lambda>z. f z - g z) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_diff)

lemma holomorphic_on_mult [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s\<rbrakk> \<Longrightarrow> (\<lambda>z. f z * g z) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_mult)

lemma holomorphic_on_inverse [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on s; \<And>z. z \<in> s \<Longrightarrow> f z \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>z. inverse (f z)) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_inverse)

lemma holomorphic_on_divide [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s; \<And>z. z \<in> s \<Longrightarrow> g z \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>z. f z / g z) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_divide)

lemma holomorphic_on_power [holomorphic_intros]:
  "f holomorphic_on s \<Longrightarrow> (\<lambda>z. (f z)^n) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_power)

lemma holomorphic_on_sum [holomorphic_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) holomorphic_on s) \<Longrightarrow> (\<lambda>x. sum (\<lambda>i. f i x) I) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_sum)

lemma holomorphic_on_prod [holomorphic_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) holomorphic_on s) \<Longrightarrow> (\<lambda>x. prod (\<lambda>i. f i x) I) holomorphic_on s"
  by (induction I rule: infinite_finite_induct) (auto intro: holomorphic_intros)

lemma holomorphic_pochhammer [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> (\<lambda>s. pochhammer (f s) n) holomorphic_on A"
  by (induction n) (auto intro!: holomorphic_intros simp: pochhammer_Suc)

lemma holomorphic_on_scaleR [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> (\<lambda>x. c *\<^sub>R f x) holomorphic_on A"
  by (auto simp: scaleR_conv_of_real intro!: holomorphic_intros)

lemma holomorphic_on_Un [holomorphic_intros]:
  assumes "f holomorphic_on A" "f holomorphic_on B" "open A" "open B"
  shows   "f holomorphic_on (A \<union> B)"
  using assms by (auto simp: holomorphic_on_def  at_within_open[of _ A]
                             at_within_open[of _ B]  at_within_open[of _ "A \<union> B"] open_Un)

lemma holomorphic_on_If_Un [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on B" "open A" "open B"
  assumes "\<And>z. z \<in> A \<Longrightarrow> z \<in> B \<Longrightarrow> f z = g z"
  shows   "(\<lambda>z. if z \<in> A then f z else g z) holomorphic_on (A \<union> B)" (is "?h holomorphic_on _")
proof (intro holomorphic_on_Un)
  note \<open>f holomorphic_on A\<close>
  also have "f holomorphic_on A \<longleftrightarrow> ?h holomorphic_on A"
    by (intro holomorphic_cong) auto
  finally show \<dots> .
next
  note \<open>g holomorphic_on B\<close>
  also have "g holomorphic_on B \<longleftrightarrow> ?h holomorphic_on B"
    using assms by (intro holomorphic_cong) auto
  finally show \<dots> .
qed (insert assms, auto)

lemma holomorphic_derivI:
     "\<lbrakk>f holomorphic_on S; open S; x \<in> S\<rbrakk>
      \<Longrightarrow> (f has_field_derivative deriv f x) (at x within T)"
by (metis DERIV_deriv_iff_field_differentiable at_within_open  holomorphic_on_def has_field_derivative_at_within)

lemma complex_derivative_transform_within_open:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s; open s; z \<in> s; \<And>w. w \<in> s \<Longrightarrow> f w = g w\<rbrakk>
   \<Longrightarrow> deriv f z = deriv g z"
  unfolding holomorphic_on_def
  by (rule DERIV_imp_deriv)
     (metis DERIV_deriv_iff_field_differentiable has_field_derivative_transform_within_open at_within_open)

lemma holomorphic_nonconstant:
  assumes holf: "f holomorphic_on S" and "open S" "\<xi> \<in> S" "deriv f \<xi> \<noteq> 0"
    shows "\<not> f constant_on S"
  by (rule nonzero_deriv_nonconstant [of f "deriv f \<xi>" \<xi> S])
    (use assms in \<open>auto simp: holomorphic_derivI\<close>)

subsection\<open>Analyticity on a set\<close>

definition\<^marker>\<open>tag important\<close> analytic_on (infixl "(analytic'_on)" 50)
  where "f analytic_on S \<equiv> \<forall>x \<in> S. \<exists>e. 0 < e \<and> f holomorphic_on (ball x e)"

named_theorems\<^marker>\<open>tag important\<close> analytic_intros "introduction rules for proving analyticity"

lemma analytic_imp_holomorphic: "f analytic_on S \<Longrightarrow> f holomorphic_on S"
  by (simp add: at_within_open [OF _ open_ball] analytic_on_def holomorphic_on_def)
     (metis centre_in_ball field_differentiable_at_within)

lemma analytic_on_open: "open S \<Longrightarrow> f analytic_on S \<longleftrightarrow> f holomorphic_on S"
apply (auto simp: analytic_imp_holomorphic)
apply (auto simp: analytic_on_def holomorphic_on_def)
by (metis holomorphic_on_def holomorphic_on_subset open_contains_ball)

lemma analytic_on_imp_differentiable_at:
  "f analytic_on S \<Longrightarrow> x \<in> S \<Longrightarrow> f field_differentiable (at x)"
 apply (auto simp: analytic_on_def holomorphic_on_def)
by (metis open_ball centre_in_ball field_differentiable_within_open)

lemma analytic_on_subset: "f analytic_on S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> f analytic_on T"
  by (auto simp: analytic_on_def)

lemma analytic_on_Un: "f analytic_on (S \<union> T) \<longleftrightarrow> f analytic_on S \<and> f analytic_on T"
  by (auto simp: analytic_on_def)

lemma analytic_on_Union: "f analytic_on (\<Union>\<T>) \<longleftrightarrow> (\<forall>T \<in> \<T>. f analytic_on T)"
  by (auto simp: analytic_on_def)

lemma analytic_on_UN: "f analytic_on (\<Union>i\<in>I. S i) \<longleftrightarrow> (\<forall>i\<in>I. f analytic_on (S i))"
  by (auto simp: analytic_on_def)

lemma analytic_on_holomorphic:
  "f analytic_on S \<longleftrightarrow> (\<exists>T. open T \<and> S \<subseteq> T \<and> f holomorphic_on T)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs \<longleftrightarrow> (\<exists>T. open T \<and> S \<subseteq> T \<and> f analytic_on T)"
  proof safe
    assume "f analytic_on S"
    then show "\<exists>T. open T \<and> S \<subseteq> T \<and> f analytic_on T"
      apply (simp add: analytic_on_def)
      apply (rule exI [where x="\<Union>{U. open U \<and> f analytic_on U}"], auto)
      apply (metis open_ball analytic_on_open centre_in_ball)
      by (metis analytic_on_def)
  next
    fix T
    assume "open T" "S \<subseteq> T" "f analytic_on T"
    then show "f analytic_on S"
        by (metis analytic_on_subset)
  qed
  also have "... \<longleftrightarrow> ?rhs"
    by (auto simp: analytic_on_open)
  finally show ?thesis .
qed

lemma analytic_on_linear [analytic_intros,simp]: "((*) c) analytic_on S"
  by (auto simp add: analytic_on_holomorphic)

lemma analytic_on_const [analytic_intros,simp]: "(\<lambda>z. c) analytic_on S"
  by (metis analytic_on_def holomorphic_on_const zero_less_one)

lemma analytic_on_ident [analytic_intros,simp]: "(\<lambda>x. x) analytic_on S"
  by (simp add: analytic_on_def gt_ex)

lemma analytic_on_id [analytic_intros]: "id analytic_on S"
  unfolding id_def by (rule analytic_on_ident)

lemma analytic_on_compose:
  assumes f: "f analytic_on S"
      and g: "g analytic_on (f ` S)"
    shows "(g o f) analytic_on S"
unfolding analytic_on_def
proof (intro ballI)
  fix x
  assume x: "x \<in> S"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball x e" using f
    by (metis analytic_on_def)
  obtain e' where e': "0 < e'" and gh: "g holomorphic_on ball (f x) e'" using g
    by (metis analytic_on_def g image_eqI x)
  have "isCont f x"
    by (metis analytic_on_imp_differentiable_at field_differentiable_imp_continuous_at f x)
  with e' obtain d where d: "0 < d" and fd: "f ` ball x d \<subseteq> ball (f x) e'"
     by (auto simp: continuous_at_ball)
  have "g \<circ> f holomorphic_on ball x (min d e)"
    apply (rule holomorphic_on_compose)
    apply (metis fh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
    by (metis fd gh holomorphic_on_subset image_mono min.cobounded1 subset_ball)
  then show "\<exists>e>0. g \<circ> f holomorphic_on ball x e"
    by (metis d e min_less_iff_conj)
qed

lemma analytic_on_compose_gen:
  "f analytic_on S \<Longrightarrow> g analytic_on T \<Longrightarrow> (\<And>z. z \<in> S \<Longrightarrow> f z \<in> T)
             \<Longrightarrow> g o f analytic_on S"
by (metis analytic_on_compose analytic_on_subset image_subset_iff)

lemma analytic_on_neg [analytic_intros]:
  "f analytic_on S \<Longrightarrow> (\<lambda>z. -(f z)) analytic_on S"
by (metis analytic_on_holomorphic holomorphic_on_minus)

lemma analytic_on_add [analytic_intros]:
  assumes f: "f analytic_on S"
      and g: "g analytic_on S"
    shows "(\<lambda>z. f z + g z) analytic_on S"
unfolding analytic_on_def
proof (intro ballI)
  fix z
  assume z: "z \<in> S"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball z e" using f
    by (metis analytic_on_def)
  obtain e' where e': "0 < e'" and gh: "g holomorphic_on ball z e'" using g
    by (metis analytic_on_def g z)
  have "(\<lambda>z. f z + g z) holomorphic_on ball z (min e e')"
    apply (rule holomorphic_on_add)
    apply (metis fh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
    by (metis gh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
  then show "\<exists>e>0. (\<lambda>z. f z + g z) holomorphic_on ball z e"
    by (metis e e' min_less_iff_conj)
qed

lemma analytic_on_diff [analytic_intros]:
  assumes f: "f analytic_on S"
      and g: "g analytic_on S"
    shows "(\<lambda>z. f z - g z) analytic_on S"
unfolding analytic_on_def
proof (intro ballI)
  fix z
  assume z: "z \<in> S"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball z e" using f
    by (metis analytic_on_def)
  obtain e' where e': "0 < e'" and gh: "g holomorphic_on ball z e'" using g
    by (metis analytic_on_def g z)
  have "(\<lambda>z. f z - g z) holomorphic_on ball z (min e e')"
    apply (rule holomorphic_on_diff)
    apply (metis fh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
    by (metis gh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
  then show "\<exists>e>0. (\<lambda>z. f z - g z) holomorphic_on ball z e"
    by (metis e e' min_less_iff_conj)
qed

lemma analytic_on_mult [analytic_intros]:
  assumes f: "f analytic_on S"
      and g: "g analytic_on S"
    shows "(\<lambda>z. f z * g z) analytic_on S"
unfolding analytic_on_def
proof (intro ballI)
  fix z
  assume z: "z \<in> S"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball z e" using f
    by (metis analytic_on_def)
  obtain e' where e': "0 < e'" and gh: "g holomorphic_on ball z e'" using g
    by (metis analytic_on_def g z)
  have "(\<lambda>z. f z * g z) holomorphic_on ball z (min e e')"
    apply (rule holomorphic_on_mult)
    apply (metis fh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
    by (metis gh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
  then show "\<exists>e>0. (\<lambda>z. f z * g z) holomorphic_on ball z e"
    by (metis e e' min_less_iff_conj)
qed

lemma analytic_on_inverse [analytic_intros]:
  assumes f: "f analytic_on S"
      and nz: "(\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0)"
    shows "(\<lambda>z. inverse (f z)) analytic_on S"
unfolding analytic_on_def
proof (intro ballI)
  fix z
  assume z: "z \<in> S"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball z e" using f
    by (metis analytic_on_def)
  have "continuous_on (ball z e) f"
    by (metis fh holomorphic_on_imp_continuous_on)
  then obtain e' where e': "0 < e'" and nz': "\<And>y. dist z y < e' \<Longrightarrow> f y \<noteq> 0"
    by (metis open_ball centre_in_ball continuous_on_open_avoid e z nz)
  have "(\<lambda>z. inverse (f z)) holomorphic_on ball z (min e e')"
    apply (rule holomorphic_on_inverse)
    apply (metis fh holomorphic_on_subset min.cobounded2 min.commute subset_ball)
    by (metis nz' mem_ball min_less_iff_conj)
  then show "\<exists>e>0. (\<lambda>z. inverse (f z)) holomorphic_on ball z e"
    by (metis e e' min_less_iff_conj)
qed

lemma analytic_on_divide [analytic_intros]:
  assumes f: "f analytic_on S"
      and g: "g analytic_on S"
      and nz: "(\<And>z. z \<in> S \<Longrightarrow> g z \<noteq> 0)"
    shows "(\<lambda>z. f z / g z) analytic_on S"
unfolding divide_inverse
by (metis analytic_on_inverse analytic_on_mult f g nz)

lemma analytic_on_power [analytic_intros]:
  "f analytic_on S \<Longrightarrow> (\<lambda>z. (f z) ^ n) analytic_on S"
by (induct n) (auto simp: analytic_on_mult)

lemma analytic_on_sum [analytic_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) analytic_on S) \<Longrightarrow> (\<lambda>x. sum (\<lambda>i. f i x) I) analytic_on S"
  by (induct I rule: infinite_finite_induct) (auto simp: analytic_on_add)

lemma deriv_left_inverse:
  assumes "f holomorphic_on S" and "g holomorphic_on T"
      and "open S" and "open T"
      and "f ` S \<subseteq> T"
      and [simp]: "\<And>z. z \<in> S \<Longrightarrow> g (f z) = z"
      and "w \<in> S"
    shows "deriv f w * deriv g (f w) = 1"
proof -
  have "deriv f w * deriv g (f w) = deriv g (f w) * deriv f w"
    by (simp add: algebra_simps)
  also have "... = deriv (g o f) w"
    using assms
    by (metis analytic_on_imp_differentiable_at analytic_on_open deriv_chain image_subset_iff)
  also have "... = deriv id w"
  proof (rule complex_derivative_transform_within_open [where s=S])
    show "g \<circ> f holomorphic_on S"
      by (rule assms holomorphic_on_compose_gen holomorphic_intros)+
  qed (use assms in auto)
  also have "... = 1"
    by simp
  finally show ?thesis .
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>Analyticity at a point\<close>

lemma analytic_at_ball:
  "f analytic_on {z} \<longleftrightarrow> (\<exists>e. 0<e \<and> f holomorphic_on ball z e)"
by (metis analytic_on_def singleton_iff)

lemma analytic_at:
    "f analytic_on {z} \<longleftrightarrow> (\<exists>s. open s \<and> z \<in> s \<and> f holomorphic_on s)"
by (metis analytic_on_holomorphic empty_subsetI insert_subset)

lemma analytic_on_analytic_at:
    "f analytic_on s \<longleftrightarrow> (\<forall>z \<in> s. f analytic_on {z})"
by (metis analytic_at_ball analytic_on_def)

lemma analytic_at_two:
  "f analytic_on {z} \<and> g analytic_on {z} \<longleftrightarrow>
   (\<exists>s. open s \<and> z \<in> s \<and> f holomorphic_on s \<and> g holomorphic_on s)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain s t
    where st: "open s" "z \<in> s" "f holomorphic_on s"
              "open t" "z \<in> t" "g holomorphic_on t"
    by (auto simp: analytic_at)
  show ?rhs
    apply (rule_tac x="s \<inter> t" in exI)
    using st
    apply (auto simp: holomorphic_on_subset)
    done
next
  assume ?rhs
  then show ?lhs
    by (force simp add: analytic_at)
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>Combining theorems for derivative with ``analytic at'' hypotheses\<close>

lemma
  assumes "f analytic_on {z}" "g analytic_on {z}"
  shows complex_derivative_add_at: "deriv (\<lambda>w. f w + g w) z = deriv f z + deriv g z"
    and complex_derivative_diff_at: "deriv (\<lambda>w. f w - g w) z = deriv f z - deriv g z"
    and complex_derivative_mult_at: "deriv (\<lambda>w. f w * g w) z =
           f z * deriv g z + deriv f z * g z"
proof -
  obtain s where s: "open s" "z \<in> s" "f holomorphic_on s" "g holomorphic_on s"
    using assms by (metis analytic_at_two)
  show "deriv (\<lambda>w. f w + g w) z = deriv f z + deriv g z"
    apply (rule DERIV_imp_deriv [OF DERIV_add])
    using s
    apply (auto simp: holomorphic_on_open field_differentiable_def DERIV_deriv_iff_field_differentiable)
    done
  show "deriv (\<lambda>w. f w - g w) z = deriv f z - deriv g z"
    apply (rule DERIV_imp_deriv [OF DERIV_diff])
    using s
    apply (auto simp: holomorphic_on_open field_differentiable_def DERIV_deriv_iff_field_differentiable)
    done
  show "deriv (\<lambda>w. f w * g w) z = f z * deriv g z + deriv f z * g z"
    apply (rule DERIV_imp_deriv [OF DERIV_mult'])
    using s
    apply (auto simp: holomorphic_on_open field_differentiable_def DERIV_deriv_iff_field_differentiable)
    done
qed

lemma deriv_cmult_at:
  "f analytic_on {z} \<Longrightarrow>  deriv (\<lambda>w. c * f w) z = c * deriv f z"
by (auto simp: complex_derivative_mult_at)

lemma deriv_cmult_right_at:
  "f analytic_on {z} \<Longrightarrow>  deriv (\<lambda>w. f w * c) z = deriv f z * c"
by (auto simp: complex_derivative_mult_at)

subsection\<^marker>\<open>tag unimportant\<close>\<open>Complex differentiation of sequences and series\<close>

(* TODO: Could probably be simplified using Uniform_Limit *)
lemma has_complex_derivative_sequence:
  fixes S :: "complex set"
  assumes cvs: "convex S"
      and df:  "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x within S)"
      and conv: "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<longrightarrow> x \<in> S \<longrightarrow> norm (f' n x - g' x) \<le> e"
      and "\<exists>x l. x \<in> S \<and> ((\<lambda>n. f n x) \<longlongrightarrow> l) sequentially"
    shows "\<exists>g. \<forall>x \<in> S. ((\<lambda>n. f n x) \<longlongrightarrow> g x) sequentially \<and>
                       (g has_field_derivative (g' x)) (at x within S)"
proof -
  from assms obtain x l where x: "x \<in> S" and tf: "((\<lambda>n. f n x) \<longlongrightarrow> l) sequentially"
    by blast
  { fix e::real assume e: "e > 0"
    then obtain N where N: "\<forall>n\<ge>N. \<forall>x. x \<in> S \<longrightarrow> cmod (f' n x - g' x) \<le> e"
      by (metis conv)
    have "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>S. \<forall>h. cmod (f' n x * h - g' x * h) \<le> e * cmod h"
    proof (rule exI [of _ N], clarify)
      fix n y h
      assume "N \<le> n" "y \<in> S"
      then have "cmod (f' n y - g' y) \<le> e"
        by (metis N)
      then have "cmod h * cmod (f' n y - g' y) \<le> cmod h * e"
        by (auto simp: antisym_conv2 mult_le_cancel_left norm_triangle_ineq2)
      then show "cmod (f' n y * h - g' y * h) \<le> e * cmod h"
        by (simp add: norm_mult [symmetric] field_simps)
    qed
  } note ** = this
  show ?thesis
    unfolding has_field_derivative_def
  proof (rule has_derivative_sequence [OF cvs _ _ x])
    show "(\<lambda>n. f n x) \<longlonglongrightarrow> l"
      by (rule tf)
  next show "\<And>e. e > 0 \<Longrightarrow> \<forall>\<^sub>F n in sequentially. \<forall>x\<in>S. \<forall>h. cmod (f' n x * h - g' x * h) \<le> e * cmod h"
      unfolding eventually_sequentially by (blast intro: **)
  qed (metis has_field_derivative_def df)
qed

lemma has_complex_derivative_series:
  fixes S :: "complex set"
  assumes cvs: "convex S"
      and df:  "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x within S)"
      and conv: "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<longrightarrow> x \<in> S
                \<longrightarrow> cmod ((\<Sum>i<n. f' i x) - g' x) \<le> e"
      and "\<exists>x l. x \<in> S \<and> ((\<lambda>n. f n x) sums l)"
    shows "\<exists>g. \<forall>x \<in> S. ((\<lambda>n. f n x) sums g x) \<and> ((g has_field_derivative g' x) (at x within S))"
proof -
  from assms obtain x l where x: "x \<in> S" and sf: "((\<lambda>n. f n x) sums l)"
    by blast
  { fix e::real assume e: "e > 0"
    then obtain N where N: "\<forall>n x. n \<ge> N \<longrightarrow> x \<in> S
            \<longrightarrow> cmod ((\<Sum>i<n. f' i x) - g' x) \<le> e"
      by (metis conv)
    have "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>S. \<forall>h. cmod ((\<Sum>i<n. h * f' i x) - g' x * h) \<le> e * cmod h"
    proof (rule exI [of _ N], clarify)
      fix n y h
      assume "N \<le> n" "y \<in> S"
      then have "cmod ((\<Sum>i<n. f' i y) - g' y) \<le> e"
        by (metis N)
      then have "cmod h * cmod ((\<Sum>i<n. f' i y) - g' y) \<le> cmod h * e"
        by (auto simp: antisym_conv2 mult_le_cancel_left norm_triangle_ineq2)
      then show "cmod ((\<Sum>i<n. h * f' i y) - g' y * h) \<le> e * cmod h"
        by (simp add: norm_mult [symmetric] field_simps sum_distrib_left)
    qed
  } note ** = this
  show ?thesis
  unfolding has_field_derivative_def
  proof (rule has_derivative_series [OF cvs _ _ x])
    fix n x
    assume "x \<in> S"
    then show "((f n) has_derivative (\<lambda>z. z * f' n x)) (at x within S)"
      by (metis df has_field_derivative_def mult_commute_abs)
  next show " ((\<lambda>n. f n x) sums l)"
    by (rule sf)
  next show "\<And>e. e>0 \<Longrightarrow> \<forall>\<^sub>F n in sequentially. \<forall>x\<in>S. \<forall>h. cmod ((\<Sum>i<n. h * f' i x) - g' x * h) \<le> e * cmod h"
      unfolding eventually_sequentially by (blast intro: **)
  qed
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Taylor on Complex Numbers\<close>

lemma sum_Suc_reindex:
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
    shows  "sum f {0..n} = f 0 - f (Suc n) + sum (\<lambda>i. f (Suc i)) {0..n}"
by (induct n) auto

lemma field_Taylor:
  assumes S: "convex S"
      and f: "\<And>i x. x \<in> S \<Longrightarrow> i \<le> n \<Longrightarrow> (f i has_field_derivative f (Suc i) x) (at x within S)"
      and B: "\<And>x. x \<in> S \<Longrightarrow> norm (f (Suc n) x) \<le> B"
      and w: "w \<in> S"
      and z: "z \<in> S"
    shows "norm(f 0 z - (\<Sum>i\<le>n. f i w * (z-w) ^ i / (fact i)))
          \<le> B * norm(z - w)^(Suc n) / fact n"
proof -
  have wzs: "closed_segment w z \<subseteq> S" using assms
    by (metis convex_contains_segment)
  { fix u
    assume "u \<in> closed_segment w z"
    then have "u \<in> S"
      by (metis wzs subsetD)
    have "(\<Sum>i\<le>n. f i u * (- of_nat i * (z-u)^(i - 1)) / (fact i) +
                      f (Suc i) u * (z-u)^i / (fact i)) =
              f (Suc n) u * (z-u) ^ n / (fact n)"
    proof (induction n)
      case 0 show ?case by simp
    next
      case (Suc n)
      have "(\<Sum>i\<le>Suc n. f i u * (- of_nat i * (z-u) ^ (i - 1)) / (fact i) +
                             f (Suc i) u * (z-u) ^ i / (fact i)) =
           f (Suc n) u * (z-u) ^ n / (fact n) +
           f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n) / (fact (Suc n)) -
           f (Suc n) u * ((1 + of_nat n) * (z-u) ^ n) / (fact (Suc n))"
        using Suc by simp
      also have "... = f (Suc (Suc n)) u * (z-u) ^ Suc n / (fact (Suc n))"
      proof -
        have "(fact(Suc n)) *
             (f(Suc n) u *(z-u) ^ n / (fact n) +
               f(Suc(Suc n)) u *((z-u) *(z-u) ^ n) / (fact(Suc n)) -
               f(Suc n) u *((1 + of_nat n) *(z-u) ^ n) / (fact(Suc n))) =
            ((fact(Suc n)) *(f(Suc n) u *(z-u) ^ n)) / (fact n) +
            ((fact(Suc n)) *(f(Suc(Suc n)) u *((z-u) *(z-u) ^ n)) / (fact(Suc n))) -
            ((fact(Suc n)) *(f(Suc n) u *(of_nat(Suc n) *(z-u) ^ n))) / (fact(Suc n))"
          by (simp add: algebra_simps del: fact_Suc)
        also have "... = ((fact (Suc n)) * (f (Suc n) u * (z-u) ^ n)) / (fact n) +
                         (f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n)) -
                         (f (Suc n) u * ((1 + of_nat n) * (z-u) ^ n))"
          by (simp del: fact_Suc)
        also have "... = (of_nat (Suc n) * (f (Suc n) u * (z-u) ^ n)) +
                         (f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n)) -
                         (f (Suc n) u * ((1 + of_nat n) * (z-u) ^ n))"
          by (simp only: fact_Suc of_nat_mult ac_simps) simp
        also have "... = f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n)"
          by (simp add: algebra_simps)
        finally show ?thesis
        by (simp add: mult_left_cancel [where c = "(fact (Suc n))", THEN iffD1] del: fact_Suc)
      qed
      finally show ?case .
    qed
    then have "((\<lambda>v. (\<Sum>i\<le>n. f i v * (z - v)^i / (fact i)))
                has_field_derivative f (Suc n) u * (z-u) ^ n / (fact n))
               (at u within S)"
      apply (intro derivative_eq_intros)
      apply (blast intro: assms \<open>u \<in> S\<close>)
      apply (rule refl)+
      apply (auto simp: field_simps)
      done
  } note sum_deriv = this
  { fix u
    assume u: "u \<in> closed_segment w z"
    then have us: "u \<in> S"
      by (metis wzs subsetD)
    have "norm (f (Suc n) u) * norm (z - u) ^ n \<le> norm (f (Suc n) u) * norm (u - z) ^ n"
      by (metis norm_minus_commute order_refl)
    also have "... \<le> norm (f (Suc n) u) * norm (z - w) ^ n"
      by (metis mult_left_mono norm_ge_zero power_mono segment_bound [OF u])
    also have "... \<le> B * norm (z - w) ^ n"
      by (metis norm_ge_zero zero_le_power mult_right_mono  B [OF us])
    finally have "norm (f (Suc n) u) * norm (z - u) ^ n \<le> B * norm (z - w) ^ n" .
  } note cmod_bound = this
  have "(\<Sum>i\<le>n. f i z * (z - z) ^ i / (fact i)) = (\<Sum>i\<le>n. (f i z / (fact i)) * 0 ^ i)"
    by simp
  also have "\<dots> = f 0 z / (fact 0)"
    by (subst sum_zero_power) simp
  finally have "norm (f 0 z - (\<Sum>i\<le>n. f i w * (z - w) ^ i / (fact i)))
                \<le> norm ((\<Sum>i\<le>n. f i w * (z - w) ^ i / (fact i)) -
                        (\<Sum>i\<le>n. f i z * (z - z) ^ i / (fact i)))"
    by (simp add: norm_minus_commute)
  also have "... \<le> B * norm (z - w) ^ n / (fact n) * norm (w - z)"
    apply (rule field_differentiable_bound
      [where f' = "\<lambda>w. f (Suc n) w * (z - w)^n / (fact n)"
         and S = "closed_segment w z", OF convex_closed_segment])
    apply (auto simp: DERIV_subset [OF sum_deriv wzs]
                  norm_divide norm_mult norm_power divide_le_cancel cmod_bound)
    done
  also have "...  \<le> B * norm (z - w) ^ Suc n / (fact n)"
    by (simp add: algebra_simps norm_minus_commute)
  finally show ?thesis .
qed

lemma complex_Taylor:
  assumes S: "convex S"
      and f: "\<And>i x. x \<in> S \<Longrightarrow> i \<le> n \<Longrightarrow> (f i has_field_derivative f (Suc i) x) (at x within S)"
      and B: "\<And>x. x \<in> S \<Longrightarrow> cmod (f (Suc n) x) \<le> B"
      and w: "w \<in> S"
      and z: "z \<in> S"
    shows "cmod(f 0 z - (\<Sum>i\<le>n. f i w * (z-w) ^ i / (fact i)))
          \<le> B * cmod(z - w)^(Suc n) / fact n"
  using assms by (rule field_Taylor)


text\<open>Something more like the traditional MVT for real components\<close>

lemma complex_mvt_line:
  assumes "\<And>u. u \<in> closed_segment w z \<Longrightarrow> (f has_field_derivative f'(u)) (at u)"
    shows "\<exists>u. u \<in> closed_segment w z \<and> Re(f z) - Re(f w) = Re(f'(u) * (z - w))"
proof -
  have twz: "\<And>t. (1 - t) *\<^sub>R w + t *\<^sub>R z = w + t *\<^sub>R (z - w)"
    by (simp add: real_vector.scale_left_diff_distrib real_vector.scale_right_diff_distrib)
  note assms[unfolded has_field_derivative_def, derivative_intros]
  show ?thesis
    apply (cut_tac mvt_simple
                     [of 0 1 "Re o f o (\<lambda>t. (1 - t) *\<^sub>R w +  t *\<^sub>R z)"
                      "\<lambda>u. Re o (\<lambda>h. f'((1 - u) *\<^sub>R w + u *\<^sub>R z) * h) o (\<lambda>t. t *\<^sub>R (z - w))"])
    apply auto
    apply (rule_tac x="(1 - x) *\<^sub>R w + x *\<^sub>R z" in exI)
    apply (auto simp: closed_segment_def twz) []
    apply (intro derivative_eq_intros has_derivative_at_withinI, simp_all)
    apply (simp add: fun_eq_iff real_vector.scale_right_diff_distrib)
    apply (force simp: twz closed_segment_def)
    done
qed

lemma complex_Taylor_mvt:
  assumes "\<And>i x. \<lbrakk>x \<in> closed_segment w z; i \<le> n\<rbrakk> \<Longrightarrow> ((f i) has_field_derivative f (Suc i) x) (at x)"
    shows "\<exists>u. u \<in> closed_segment w z \<and>
            Re (f 0 z) =
            Re ((\<Sum>i = 0..n. f i w * (z - w) ^ i / (fact i)) +
                (f (Suc n) u * (z-u)^n / (fact n)) * (z - w))"
proof -
  { fix u
    assume u: "u \<in> closed_segment w z"
    have "(\<Sum>i = 0..n.
               (f (Suc i) u * (z-u) ^ i - of_nat i * (f i u * (z-u) ^ (i - Suc 0))) /
               (fact i)) =
          f (Suc 0) u -
             (f (Suc (Suc n)) u * ((z-u) ^ Suc n) - (of_nat (Suc n)) * (z-u) ^ n * f (Suc n) u) /
             (fact (Suc n)) +
             (\<Sum>i = 0..n.
                 (f (Suc (Suc i)) u * ((z-u) ^ Suc i) - of_nat (Suc i) * (f (Suc i) u * (z-u) ^ i)) /
                 (fact (Suc i)))"
       by (subst sum_Suc_reindex) simp
    also have "... = f (Suc 0) u -
             (f (Suc (Suc n)) u * ((z-u) ^ Suc n) - (of_nat (Suc n)) * (z-u) ^ n * f (Suc n) u) /
             (fact (Suc n)) +
             (\<Sum>i = 0..n.
                 f (Suc (Suc i)) u * ((z-u) ^ Suc i) / (fact (Suc i))  -
                 f (Suc i) u * (z-u) ^ i / (fact i))"
      by (simp only: diff_divide_distrib fact_cancel ac_simps)
    also have "... = f (Suc 0) u -
             (f (Suc (Suc n)) u * (z-u) ^ Suc n - of_nat (Suc n) * (z-u) ^ n * f (Suc n) u) /
             (fact (Suc n)) +
             f (Suc (Suc n)) u * (z-u) ^ Suc n / (fact (Suc n)) - f (Suc 0) u"
      by (subst sum_Suc_diff) auto
    also have "... = f (Suc n) u * (z-u) ^ n / (fact n)"
      by (simp only: algebra_simps diff_divide_distrib fact_cancel)
    finally have "(\<Sum>i = 0..n. (f (Suc i) u * (z - u) ^ i
                             - of_nat i * (f i u * (z-u) ^ (i - Suc 0))) / (fact i)) =
                  f (Suc n) u * (z - u) ^ n / (fact n)" .
    then have "((\<lambda>u. \<Sum>i = 0..n. f i u * (z - u) ^ i / (fact i)) has_field_derivative
                f (Suc n) u * (z - u) ^ n / (fact n))  (at u)"
      apply (intro derivative_eq_intros)+
      apply (force intro: u assms)
      apply (rule refl)+
      apply (auto simp: ac_simps)
      done
  }
  then show ?thesis
    apply (cut_tac complex_mvt_line [of w z "\<lambda>u. \<Sum>i = 0..n. f i u * (z-u) ^ i / (fact i)"
               "\<lambda>u. (f (Suc n) u * (z-u)^n / (fact n))"])
    apply (auto simp add: intro: open_closed_segment)
    done
qed


end
