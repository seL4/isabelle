(*  Title:      HOL/Analysis/Lipschitz.thy
    Author:     Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    Author:     Fabian Immler, TU München
*)
section \<open>Lipschitz Continuity\<close>

theory Lipschitz
  imports
    Derivative Abstract_Metric_Spaces
begin

definition\<^marker>\<open>tag important\<close> lipschitz_on
  where "lipschitz_on C U f \<longleftrightarrow> (0 \<le> C \<and> (\<forall>x \<in> U. \<forall>y\<in>U. dist (f x) (f y) \<le> C * dist x y))"

open_bundle lipschitz_syntax
begin
notation\<^marker>\<open>tag important\<close> lipschitz_on (\<open>_-lipschitz'_on\<close> [1000])
end

bundle no_lipschitz_syntax
begin
no_notation lipschitz_on (\<open>_-lipschitz'_on\<close> [1000])
end

lemma lipschitz_onI: "L-lipschitz_on X f"
  if "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> dist (f x) (f y) \<le> L * dist x y" "0 \<le> L"
  using that by (auto simp: lipschitz_on_def)

lemma lipschitz_onD:
  "dist (f x) (f y) \<le> L * dist x y"
  if "L-lipschitz_on X f" "x \<in> X" "y \<in> X"
  using that by (auto simp: lipschitz_on_def)

lemma lipschitz_on_nonneg:
  "0 \<le> L" if "L-lipschitz_on X f"
  using that by (auto simp: lipschitz_on_def)

lemma lipschitz_on_normD:
  "norm (f x - f y) \<le> L * norm (x - y)"
  if "lipschitz_on L X f" "x \<in> X" "y \<in> X"
  using lipschitz_onD[OF that]
  by (simp add: dist_norm)

lemma lipschitz_on_mono: "L-lipschitz_on D f" if "M-lipschitz_on E f" "D \<subseteq> E" "M \<le> L"
  using that
  by (force simp: lipschitz_on_def intro: order_trans[OF _ mult_right_mono])

lemmas lipschitz_on_subset = lipschitz_on_mono[OF _ _ order_refl]
  and lipschitz_on_le = lipschitz_on_mono[OF _ order_refl]

lemma lipschitz_on_leI:
  "L-lipschitz_on X f"
  if "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> dist (f x) (f y) \<le> L * dist x y"
    "0 \<le> L"
  for f::"'a::{linorder_topology, ordered_real_vector, metric_space} \<Rightarrow> 'b::metric_space"
proof (rule lipschitz_onI)
  fix x y assume xy: "x \<in> X" "y \<in> X"
  consider "y \<le> x" | "x \<le> y"
    by (rule le_cases)
  then show "dist (f x) (f y) \<le> L * dist x y"
  proof cases
    case 1
    then have "dist (f y) (f x) \<le> L * dist y x"
      by (auto intro!: that xy)
    then show ?thesis
      by (simp add: dist_commute)
  qed (auto intro!: that xy)
qed fact

lemma lipschitz_on_concat:
  fixes a b c::real
  assumes f: "L-lipschitz_on {a .. b} f"
  assumes g: "L-lipschitz_on {b .. c} g"
  assumes fg: "f b = g b"
  shows "lipschitz_on L {a .. c} (\<lambda>x. if x \<le> b then f x else g x)"
    (is "lipschitz_on _ _ ?f")
proof (rule lipschitz_on_leI)
  fix x y
  assume x: "x \<in> {a..c}" and y: "y \<in> {a..c}" and xy: "x \<le> y"
  consider "x \<le> b \<and> b < y" | "x \<ge> b \<or> y \<le> b" by arith
  then show "dist (?f x) (?f y) \<le> L * dist x y"
  proof cases
    case 1
    have "dist (f x) (g y) \<le> dist (f x) (f b) + dist (g b) (g y)"
      unfolding fg by (rule dist_triangle)
    also have "dist (f x) (f b) \<le> L * dist x b"
      using 1 x
      by (auto intro!: lipschitz_onD[OF f])
    also have "dist (g b) (g y) \<le> L * dist b y"
      using 1 x y
      by (auto intro!: lipschitz_onD[OF g] lipschitz_onD[OF f])
    finally have "dist (f x) (g y) \<le> L * dist x b + L * dist b y"
      by simp
    also have "\<dots> = L * (dist x b + dist b y)"
      by (simp add: algebra_simps)
    also have "dist x b + dist b y = dist x y"
      using 1 x y
      by (auto simp: dist_real_def abs_real_def)
    finally show ?thesis
      using 1 by simp
  next
    case 2
    with lipschitz_onD[OF f, of x y] lipschitz_onD[OF g, of x y] x y xy
    show ?thesis
      by (auto simp: fg)
  qed
qed (rule lipschitz_on_nonneg[OF f])

lemma lipschitz_on_concat_max:
  fixes a b c::real
  assumes f: "L-lipschitz_on {a .. b} f"
  assumes g: "M-lipschitz_on {b .. c} g"
  assumes fg: "f b = g b"
  shows "(max L M)-lipschitz_on {a .. c} (\<lambda>x. if x \<le> b then f x else g x)"
proof -
  have "lipschitz_on (max L M) {a .. b} f" "lipschitz_on (max L M) {b .. c} g"
    by (auto intro!: lipschitz_on_mono[OF f order_refl] lipschitz_on_mono[OF g order_refl])
  from lipschitz_on_concat[OF this fg] show ?thesis .
qed

text \<open>Equivalence between "abstract" and "type class" Lipschitz notions, 
for all types in the metric space class\<close>
lemma Lipschitz_map_euclidean [simp]:
  "Lipschitz_continuous_map euclidean_metric euclidean_metric f
     \<longleftrightarrow> (\<exists>B. lipschitz_on B UNIV f)"  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (force simp add: Lipschitz_continuous_map_pos lipschitz_on_def less_le_not_le)
  show "?rhs \<Longrightarrow> ?lhs"                             
    by (auto simp: Lipschitz_continuous_map_def lipschitz_on_def)
qed

subsubsection \<open>Continuity\<close>

proposition lipschitz_on_uniformly_continuous:
  assumes "L-lipschitz_on X f"
  shows "uniformly_continuous_on X f"
  unfolding uniformly_continuous_on_def
proof safe
  fix e::real
  assume "0 < e"
  from assms have l: "(L+1)-lipschitz_on X f"
    by (rule lipschitz_on_mono) auto
  show "\<exists>d>0. \<forall>x\<in>X. \<forall>x'\<in>X. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
    using lipschitz_onD[OF l] lipschitz_on_nonneg[OF assms] \<open>0 < e\<close>
    by (force intro!: exI[where x="e/(L + 1)"] simp: field_simps)
qed

proposition lipschitz_on_continuous_on:
  "continuous_on X f" if "L-lipschitz_on X f"
  by (rule uniformly_continuous_imp_continuous[OF lipschitz_on_uniformly_continuous[OF that]])

lemma lipschitz_on_continuous_within:
  "continuous (at x within X) f" if "L-lipschitz_on X f" "x \<in> X"
  using lipschitz_on_continuous_on[OF that(1)] that(2)
  by (auto simp: continuous_on_eq_continuous_within)

subsubsection \<open>Differentiable functions\<close>

proposition bounded_derivative_imp_lipschitz:
  assumes "\<And>x. x \<in> X \<Longrightarrow> (f has_derivative f' x) (at x within X)"
  assumes convex: "convex X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> onorm (f' x) \<le> C" "0 \<le> C"
  shows "C-lipschitz_on X f"
proof (rule lipschitz_onI)
  show "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> dist (f x) (f y) \<le> C * dist x y"
    by (auto intro!: assms differentiable_bound[unfolded dist_norm[symmetric], OF convex])
qed fact


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Structural introduction rules\<close>

named_theorems lipschitz_intros "structural introduction rules for Lipschitz controls"

lemma lipschitz_on_compose [lipschitz_intros]:
  "(D * C)-lipschitz_on U (g o f)"
  if f: "C-lipschitz_on U f" and g: "D-lipschitz_on (f`U) g"
proof (rule lipschitz_onI)
  show "D* C \<ge> 0" using lipschitz_on_nonneg[OF f] lipschitz_on_nonneg[OF g] by auto
  fix x y assume H: "x \<in> U" "y \<in> U"
  have "dist (g (f x)) (g (f y)) \<le> D * dist (f x) (f y)"
    apply (rule lipschitz_onD[OF g]) using H by auto
  also have "... \<le> D * C * dist x y"
    using mult_left_mono[OF lipschitz_onD(1)[OF f H] lipschitz_on_nonneg[OF g]] by auto
  finally show "dist ((g \<circ> f) x) ((g \<circ> f) y) \<le> D * C* dist x y"
    unfolding comp_def by (auto simp add: mult.commute)
qed

lemma lipschitz_on_compose2:
  "(D * C)-lipschitz_on U (\<lambda>x. g (f x))"
  if "C-lipschitz_on U f" "D-lipschitz_on (f`U) g"
  using lipschitz_on_compose[OF that] by (simp add: o_def)

lemma lipschitz_on_cong[cong]:
  "C-lipschitz_on U g \<longleftrightarrow> D-lipschitz_on V f"
  if "C = D" "U = V" "\<And>x. x \<in> V \<Longrightarrow> g x = f x"
  using that by (auto simp: lipschitz_on_def)

lemma lipschitz_on_transform:
  "C-lipschitz_on U g"
  if "C-lipschitz_on U f"
    "\<And>x. x \<in> U \<Longrightarrow> g x = f x"
  using that
  by simp

lemma lipschitz_on_empty_iff[simp]: "C-lipschitz_on {} f \<longleftrightarrow> C \<ge> 0"
  by (auto simp: lipschitz_on_def)

lemma lipschitz_on_insert_iff[simp]:
  "C-lipschitz_on (insert y X) f \<longleftrightarrow>
    C-lipschitz_on X f \<and> (\<forall>x \<in> X. dist (f x) (f y) \<le> C * dist x y)"
  by (auto simp: lipschitz_on_def dist_commute)

lemma lipschitz_on_singleton [lipschitz_intros]: "C \<ge> 0 \<Longrightarrow> C-lipschitz_on {x} f"
  and lipschitz_on_empty [lipschitz_intros]: "C \<ge> 0 \<Longrightarrow> C-lipschitz_on {} f"
  by simp_all

lemma lipschitz_on_id [lipschitz_intros]: "1-lipschitz_on U (\<lambda>x. x)"
  by (auto simp: lipschitz_on_def)

lemma lipschitz_on_constant [lipschitz_intros]: "0-lipschitz_on U (\<lambda>x. c)"
  by (auto simp: lipschitz_on_def)

lemma lipschitz_on_add [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow>'b::real_normed_vector"
  assumes "C-lipschitz_on U f"
    "D-lipschitz_on U g"
  shows "(C+D)-lipschitz_on U (\<lambda>x. f x + g x)"
proof (rule lipschitz_onI)
  show "C + D \<ge> 0"
    using lipschitz_on_nonneg[OF assms(1)] lipschitz_on_nonneg[OF assms(2)] by auto
  fix x y assume H: "x \<in> U" "y \<in> U"
  have "dist (f x + g x) (f y + g y) \<le> dist (f x) (f y) + dist (g x) (g y)"
    by (simp add: dist_triangle_add)
  also have "... \<le> C * dist x y + D * dist x y"
    using lipschitz_onD(1)[OF assms(1) H] lipschitz_onD(1)[OF assms(2) H] by auto
  finally show "dist (f x + g x) (f y + g y) \<le> (C+D) * dist x y" by (auto simp add: algebra_simps)
qed

lemma lipschitz_on_cmult [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "C-lipschitz_on U f"
  shows "(abs(a) * C)-lipschitz_on U (\<lambda>x. a *\<^sub>R f x)"
proof (rule lipschitz_onI)
  show "abs(a) * C \<ge> 0" using lipschitz_on_nonneg[OF assms(1)] by auto
  fix x y assume H: "x \<in> U" "y \<in> U"
  have "dist (a *\<^sub>R f x) (a *\<^sub>R f y) = abs(a) * dist (f x) (f y)"
    by (metis dist_norm norm_scaleR real_vector.scale_right_diff_distrib)
  also have "... \<le> abs(a) * C * dist x y"
    using lipschitz_onD(1)[OF assms(1) H] by (simp add: Groups.mult_ac(1) mult_left_mono)
  finally show "dist (a *\<^sub>R f x) (a *\<^sub>R f y) \<le> \<bar>a\<bar> * C * dist x y" by auto
qed

lemma lipschitz_on_cmult_real [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow> real"
  assumes "C-lipschitz_on U f"
  shows "(abs(a) * C)-lipschitz_on U (\<lambda>x. a * f x)"
  using lipschitz_on_cmult[OF assms] by auto

lemma lipschitz_on_cmult_nonneg [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "C-lipschitz_on U f"
    "a \<ge> 0"
  shows "(a * C)-lipschitz_on U (\<lambda>x. a *\<^sub>R f x)"
  using lipschitz_on_cmult[OF assms(1), of a] assms(2) by auto

lemma lipschitz_on_cmult_real_nonneg [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow> real"
  assumes "C-lipschitz_on U f"
    "a \<ge> 0"
  shows "(a * C)-lipschitz_on U (\<lambda>x. a * f x)"
  using lipschitz_on_cmult_nonneg[OF assms] by auto

lemma lipschitz_on_cmult_upper [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "C-lipschitz_on U f"
    "abs(a) \<le> D"
  shows "(D * C)-lipschitz_on U (\<lambda>x. a *\<^sub>R f x)"
  apply (rule lipschitz_on_mono[OF lipschitz_on_cmult[OF assms(1), of a], of _ "D * C"])
  using assms(2) lipschitz_on_nonneg[OF assms(1)] mult_right_mono by auto

lemma lipschitz_on_cmult_real_upper [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow> real"
  assumes "C-lipschitz_on U f"
    "abs(a) \<le> D"
  shows "(D * C)-lipschitz_on U (\<lambda>x. a * f x)"
  using lipschitz_on_cmult_upper[OF assms] by auto

lemma lipschitz_on_minus[lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow>'b::real_normed_vector"
  assumes "C-lipschitz_on U f"
  shows "C-lipschitz_on U (\<lambda>x. - f x)"
  by (metis (mono_tags, lifting) assms dist_minus lipschitz_on_def)

lemma lipschitz_on_minus_iff[simp]:
  "L-lipschitz_on X (\<lambda>x. - f x) \<longleftrightarrow> L-lipschitz_on X f"
  "L-lipschitz_on X (- f) \<longleftrightarrow> L-lipschitz_on X f"
  for f::"'a::metric_space \<Rightarrow>'b::real_normed_vector"
  using lipschitz_on_minus[of L X f] lipschitz_on_minus[of L X "-f"]
  by auto

lemma lipschitz_on_diff[lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow>'b::real_normed_vector"
  assumes "C-lipschitz_on U f" "D-lipschitz_on U g"
  shows "(C + D)-lipschitz_on U (\<lambda>x. f x - g x)"
  using lipschitz_on_add[OF assms(1) lipschitz_on_minus[OF assms(2)]] by auto

lemma lipschitz_on_closure [lipschitz_intros]:
  assumes "C-lipschitz_on U f" "continuous_on (closure U) f"
  shows "C-lipschitz_on (closure U) f"
proof (rule lipschitz_onI)
  show "C \<ge> 0" using lipschitz_on_nonneg[OF assms(1)] by simp
  fix x y assume "x \<in> closure U" "y \<in> closure U"
  obtain u v::"nat \<Rightarrow> 'a" where *: "\<And>n. u n \<in> U" "u \<longlonglongrightarrow> x"
                                   "\<And>n. v n \<in> U" "v \<longlonglongrightarrow> y"
    using \<open>x \<in> closure U\<close> \<open>y \<in> closure U\<close> unfolding closure_sequential by blast
  have a: "(\<lambda>n. f (u n)) \<longlonglongrightarrow> f x"
    using *(1) *(2) \<open>x \<in> closure U\<close> \<open>continuous_on (closure U) f\<close>
    unfolding comp_def continuous_on_closure_sequentially[of U f] by auto
  have b: "(\<lambda>n. f (v n)) \<longlonglongrightarrow> f y"
    using *(3) *(4) \<open>y \<in> closure U\<close> \<open>continuous_on (closure U) f\<close>
    unfolding comp_def continuous_on_closure_sequentially[of U f] by auto
  have l: "(\<lambda>n. C * dist (u n) (v n) - dist (f (u n)) (f (v n))) \<longlonglongrightarrow> C * dist x y - dist (f x) (f y)"
    by (intro tendsto_intros * a b)
  have "C * dist (u n) (v n) - dist (f (u n)) (f (v n)) \<ge> 0" for n
    using lipschitz_onD(1)[OF assms(1) \<open>u n \<in> U\<close> \<open>v n \<in> U\<close>] by simp
  then have "C * dist x y - dist (f x) (f y) \<ge> 0" using LIMSEQ_le_const[OF l, of 0] by auto
  then show "dist (f x) (f y) \<le> C * dist x y" by auto
qed

lemma lipschitz_on_Pair[lipschitz_intros]:
  assumes f: "L-lipschitz_on A f"
  assumes g: "M-lipschitz_on A g"
  shows "(sqrt (L\<^sup>2 + M\<^sup>2))-lipschitz_on A (\<lambda>a. (f a, g a))"
proof (rule lipschitz_onI, goal_cases)
  case (1 x y)
  have "dist (f x, g x) (f y, g y) = sqrt ((dist (f x) (f y))\<^sup>2 + (dist (g x) (g y))\<^sup>2)"
    by (auto simp add: dist_Pair_Pair real_le_lsqrt)
  also have "\<dots> \<le> sqrt ((L * dist x y)\<^sup>2 + (M * dist x y)\<^sup>2)"
    by (auto intro!: real_sqrt_le_mono add_mono power_mono 1 lipschitz_onD f g)
  also have "\<dots> \<le> sqrt (L\<^sup>2 + M\<^sup>2) * dist x y"
    by (auto simp: power_mult_distrib ring_distribs[symmetric] real_sqrt_mult)
  finally show ?case .
qed simp

lemma lipschitz_extend_closure:
  fixes f::"('a::metric_space) \<Rightarrow> ('b::complete_space)"
  assumes "C-lipschitz_on U f"
  shows "\<exists>g. C-lipschitz_on (closure U) g \<and> (\<forall>x\<in>U. g x = f x)"
proof -
  obtain g where g: "\<And>x. x \<in> U \<Longrightarrow> g x = f x" "uniformly_continuous_on (closure U) g"
    using uniformly_continuous_on_extension_on_closure[OF lipschitz_on_uniformly_continuous[OF assms]] by metis
  have "C-lipschitz_on (closure U) g"
    apply (rule lipschitz_on_closure, rule lipschitz_on_transform[OF assms])
    using g uniformly_continuous_imp_continuous[OF g(2)] by auto
  then show ?thesis using g(1) by auto
qed

lemma (in bounded_linear) lipschitz_boundE:
  obtains B where "B-lipschitz_on A f"
proof -
  from nonneg_bounded
  obtain B where B: "B \<ge> 0" "\<And>x. norm (f x) \<le> B * norm x"
    by (auto simp: ac_simps)
  have "B-lipschitz_on A f"
    by (auto intro!: lipschitz_onI B simp: dist_norm diff[symmetric])
  thus ?thesis ..
qed


subsection \<open>Local Lipschitz continuity\<close>

text \<open>Given a function defined on a real interval, it is Lipschitz-continuous if and only if
it is locally so, as proved in the following lemmas. It is useful especially for
piecewise-defined functions: if each piece is Lipschitz, then so is the whole function.
The same goes for functions defined on geodesic spaces, or more generally on geodesic subsets
in a metric space (for instance convex subsets in a real vector space), and this follows readily
from the real case, but we will not prove it explicitly.

We give several variations around this statement. This is essentially a connectedness argument.\<close>

lemma locally_lipschitz_imp_lipschitz_aux:
  fixes f::"real \<Rightarrow> ('a::metric_space)"
  assumes "a \<le> b"
          "continuous_on {a..b} f"
          "\<And>x. x \<in> {a..<b} \<Longrightarrow> \<exists>y \<in> {x<..b}. dist (f y) (f x) \<le> M * (y-x)"
  shows "dist (f b) (f a) \<le> M * (b-a)"
proof -
  define A where "A = {x \<in> {a..b}. dist (f x) (f a) \<le> M * (x-a)}"
  have *: "A = (\<lambda>x. M * (x-a) - dist (f x) (f a))-`{0..} \<inter> {a..b}"
    unfolding A_def by auto
  have "a \<in> A" unfolding A_def using \<open>a \<le> b\<close> by auto
  then have "A \<noteq> {}" by auto
  moreover have "bdd_above A" unfolding A_def by auto
  moreover have "closed A" unfolding * by (rule closed_vimage_Int, auto intro!: continuous_intros assms)
  ultimately have "Sup A \<in> A" by (rule closed_contains_Sup)
  have "Sup A = b"
  proof (rule ccontr)
    assume "Sup A \<noteq> b"
    define x where "x = Sup A"
    have I: "dist (f x) (f a) \<le> M * (x-a)" using \<open>Sup A \<in> A\<close> x_def A_def by auto
    have "x \<in> {a..<b}" unfolding x_def using \<open>Sup A \<in> A\<close> \<open>Sup A \<noteq> b\<close> A_def by auto
    then obtain y where J: "y \<in> {x<..b}" "dist (f y) (f x) \<le> M * (y-x)" using assms(3) by blast
    have "dist (f y) (f a) \<le> dist (f y) (f x) + dist (f x) (f a)" by (rule dist_triangle)
    also have "... \<le> M * (y-x) + M * (x-a)" using I J(2) by auto
    finally have "dist (f y) (f a) \<le> M * (y-a)" by (auto simp add: algebra_simps)
    then have "y \<in> A" unfolding A_def using \<open>y \<in> {x<..b}\<close> \<open>x \<in> {a..<b}\<close> by auto
    then have "y \<le> Sup A" by (rule cSup_upper, auto simp: A_def)
    then show False using \<open>y \<in> {x<..b}\<close> x_def by auto
  qed
  then show ?thesis using \<open>Sup A \<in> A\<close> A_def by auto
qed

lemma locally_lipschitz_imp_lipschitz:
  fixes f::"real \<Rightarrow> ('a::metric_space)"
  assumes "continuous_on {a..b} f"
          "\<And>x y. x \<in> {a..<b} \<Longrightarrow> y > x \<Longrightarrow> \<exists>z \<in> {x<..y}. dist (f z) (f x) \<le> M * (z-x)"
          "M \<ge> 0"
  shows "lipschitz_on M {a..b} f"
proof (rule lipschitz_onI[OF _ \<open>M \<ge> 0\<close>])
  have *: "dist (f t) (f s) \<le> M * (t-s)" if "s \<le> t" "s \<in> {a..b}" "t \<in> {a..b}" for s t
  proof (rule locally_lipschitz_imp_lipschitz_aux, simp add: \<open>s \<le> t\<close>)
    show "continuous_on {s..t} f" using continuous_on_subset[OF assms(1)] that by auto
    fix x assume "x \<in> {s..<t}"
    then have "x \<in> {a..<b}" using that by auto
    show "\<exists>z\<in>{x<..t}. dist (f z) (f x) \<le> M * (z - x)"
      using assms(2)[OF \<open>x \<in> {a..<b}\<close>, of t] \<open>x \<in> {s..<t}\<close> by auto
  qed
  fix x y assume "x \<in> {a..b}" "y \<in> {a..b}"
  consider "x \<le> y" | "y \<le> x" by linarith
  then show "dist (f x) (f y) \<le> M * dist x y"
    apply (cases)
    using *[OF _ \<open>x \<in> {a..b}\<close> \<open>y \<in> {a..b}\<close>] *[OF _ \<open>y \<in> {a..b}\<close> \<open>x \<in> {a..b}\<close>]
    by (auto simp add: dist_commute dist_real_def)
qed

text \<open>We deduce that if a function is Lipschitz on finitely many closed sets on the real line, then
it is Lipschitz on any interval contained in their union. The difficulty in the proof is to show
that any point \<open>z\<close> in this interval (except the maximum) has a point arbitrarily close to it on its
right which is contained in a common initial closed set. Otherwise, we show that there is a small
interval \<open>(z, T)\<close> which does not intersect any of the initial closed sets, a contradiction.\<close>

proposition lipschitz_on_closed_Union:
  assumes "\<And>i. i \<in> I \<Longrightarrow> lipschitz_on M (U i) f"
          "\<And>i. i \<in> I \<Longrightarrow> closed (U i)"
          "finite I"
          "M \<ge> 0"
          "{u..(v::real)} \<subseteq> (\<Union>i\<in>I. U i)"
  shows "lipschitz_on M {u..v} f"
proof (rule locally_lipschitz_imp_lipschitz[OF _ _ \<open>M \<ge> 0\<close>])
  have *: "continuous_on (U i) f" if "i \<in> I" for i
    by (rule lipschitz_on_continuous_on[OF assms(1)[OF \<open>i\<in> I\<close>]])
  have "continuous_on (\<Union>i\<in>I. U i) f"
    apply (rule continuous_on_closed_Union) using \<open>finite I\<close> * assms(2) by auto
  then show "continuous_on {u..v} f"
    using \<open>{u..(v::real)} \<subseteq> (\<Union>i\<in>I. U i)\<close> continuous_on_subset by auto

  fix z Z assume z: "z \<in> {u..<v}" "z < Z"
  then have "u \<le> v" by auto
  define T where "T = min Z v"
  then have T: "T > z" "T \<le> v" "T \<ge> u" "T \<le> Z" using z by auto
  define A where "A = (\<Union>i\<in> I \<inter> {i. U i \<inter> {z<..T} \<noteq> {}}. U i \<inter> {z..T})"
  have a: "closed A"
    unfolding A_def apply (rule closed_UN) using \<open>finite I\<close> \<open>\<And>i. i \<in> I \<Longrightarrow> closed (U i)\<close> by auto
  have b: "bdd_below A" unfolding A_def using \<open>finite I\<close> by auto
  have "\<exists>i \<in> I. T \<in> U i" using \<open>{u..v} \<subseteq> (\<Union>i\<in>I. U i)\<close> T by auto
  then have c: "T \<in> A" unfolding A_def using T by (auto, fastforce)
  have "Inf A \<ge> z"
    apply (rule cInf_greatest, auto) using c unfolding A_def by auto
  moreover have "Inf A \<le> z"
  proof (rule ccontr)
    assume "\<not>(Inf A \<le> z)"
    then obtain w where w: "w > z" "w < Inf A" by (meson dense not_le_imp_less)
    have "Inf A \<le> T" using a b c by (simp add: cInf_lower)
    then have "w \<le> T" using w by auto
    then have "w \<in> {u..v}" using w \<open>z \<in> {u..<v}\<close> T by auto
    then obtain j where j: "j \<in> I" "w \<in> U j" using \<open>{u..v} \<subseteq> (\<Union>i\<in>I. U i)\<close> by fastforce
    then have "w \<in> U j \<inter> {z..T}" "U j \<inter> {z<..T} \<noteq> {}" using j T w \<open>w \<le> T\<close> by auto
    then have "w \<in> A" unfolding A_def using \<open>j \<in> I\<close> by auto
    then have "Inf A \<le> w" using a b by (simp add: cInf_lower)
    then show False using w by auto
  qed
  ultimately have "Inf A = z" by simp
  moreover have "Inf A \<in> A"
    apply (rule closed_contains_Inf) using a b c by auto
  ultimately have "z \<in> A" by simp
  then obtain i where i: "i \<in> I" "U i \<inter> {z<..T} \<noteq> {}" "z \<in> U i" unfolding A_def by auto
  then obtain t where "t \<in> U i \<inter> {z<..T}" by blast
  then have "dist (f t) (f z) \<le> M * (t - z)"
    using lipschitz_onD(1)[OF assms(1)[of i], of t z] i dist_real_def by auto
  then show "\<exists>t\<in>{z<..Z}. dist (f t) (f z) \<le> M * (t - z)" using \<open>T \<le> Z\<close> \<open>t \<in> U i \<inter> {z<..T}\<close> by auto
qed


subsection \<open>Local Lipschitz continuity (uniform for a family of functions)\<close>

definition\<^marker>\<open>tag important\<close> local_lipschitz::
  "'a::metric_space set \<Rightarrow> 'b::metric_space set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c::metric_space) \<Rightarrow> bool"
  where
  "local_lipschitz T X f \<equiv> \<forall>x \<in> X. \<forall>t \<in> T.
    \<exists>u>0. \<exists>L. \<forall>t \<in> cball t u \<inter> T. L-lipschitz_on (cball x u \<inter> X) (f t)"

lemma local_lipschitzI:
  assumes "\<And>t x. t \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> \<exists>u>0. \<exists>L. \<forall>t \<in> cball t u \<inter> T. L-lipschitz_on (cball x u \<inter> X) (f t)"
  shows "local_lipschitz T X f"
  using assms
  unfolding local_lipschitz_def
  by auto

lemma local_lipschitzE:
  assumes local_lipschitz: "local_lipschitz T X f"
  assumes "t \<in> T" "x \<in> X"
  obtains u L where "u > 0" "\<And>s. s \<in> cball t u \<inter> T \<Longrightarrow> L-lipschitz_on (cball x u \<inter> X) (f s)"
  using assms local_lipschitz_def
  by metis

lemma local_lipschitz_continuous_on:
  assumes local_lipschitz: "local_lipschitz T X f"
  assumes "t \<in> T"
  shows "continuous_on X (f t)"
  unfolding continuous_on_def
proof safe
  fix x assume "x \<in> X"
  from local_lipschitzE[OF local_lipschitz \<open>t \<in> T\<close> \<open>x \<in> X\<close>] obtain u L
    where "0 < u"
    and L: "\<And>s. s \<in> cball t u \<inter> T \<Longrightarrow> L-lipschitz_on (cball x u \<inter> X) (f s)"
    by metis
  have "x \<in> ball x u" using \<open>0 < u\<close> by simp
  from lipschitz_on_continuous_on[OF L]
  have tendsto: "(f t \<longlongrightarrow> f t x) (at x within cball x u \<inter> X)"
    using \<open>0 < u\<close> \<open>x \<in> X\<close> \<open>t \<in> T\<close>
    by (auto simp: continuous_on_def)
  moreover have "\<forall>\<^sub>F xa in at x. (xa \<in> cball x u \<inter> X) = (xa \<in> X)"
    using eventually_at_ball[OF \<open>0 < u\<close>, of x UNIV]
    by eventually_elim auto
  ultimately show "(f t \<longlongrightarrow> f t x) (at x within X)"
    by (rule Lim_transform_within_set)
qed

lemma
  local_lipschitz_compose1:
  assumes ll: "local_lipschitz (g ` T) X (\<lambda>t. f t)"
  assumes g: "continuous_on T g"
  shows "local_lipschitz T X (\<lambda>t. f (g t))"
proof (rule local_lipschitzI)
  fix t x
  assume "t \<in> T" "x \<in> X"
  then have "g t \<in> g ` T" by simp
  from local_lipschitzE[OF assms(1) this \<open>x \<in> X\<close>]
  obtain u L where "0 < u" and l: "(\<And>s. s \<in> cball (g t) u \<inter> g ` T \<Longrightarrow> L-lipschitz_on (cball x u \<inter> X) (f s))"
    by auto
  from g[unfolded continuous_on_eq_continuous_within, rule_format, OF \<open>t \<in> T\<close>,
    unfolded continuous_within_eps_delta, rule_format, OF \<open>0 < u\<close>]
  obtain d where d: "d>0" "\<And>x'. x'\<in>T \<Longrightarrow> dist x' t < d \<Longrightarrow> dist (g x') (g t) < u"
    by (auto)
  show "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> T. L-lipschitz_on  (cball x u \<inter> X) (f (g t))"
    using d \<open>0 < u\<close>
    by (fastforce intro: exI[where x="(min d u)/2"] exI[where x=L]
      intro!: less_imp_le[OF d(2)] lipschitz_on_subset[OF l] simp: dist_commute)
qed

context
  fixes T::"'a::metric_space set" and X f
  assumes local_lipschitz: "local_lipschitz T X f"
begin

lemma continuous_on_TimesI:
  assumes y: "\<And>x. x \<in> X \<Longrightarrow> continuous_on T (\<lambda>t. f t x)"
  shows "continuous_on (T \<times> X) (\<lambda>(t, x). f t x)"
  unfolding continuous_on_iff
proof (safe, simp)
  fix a b and e::real
  assume H: "a \<in> T" "b \<in> X" "0 < e"
  hence "0 < e/2" by simp
  from y[unfolded continuous_on_iff, OF \<open>b \<in> X\<close>, rule_format, OF \<open>a \<in> T\<close> \<open>0 < e/2\<close>]
  obtain d where d: "d > 0" "\<And>t. t \<in> T \<Longrightarrow> dist t a < d \<Longrightarrow> dist (f t b) (f a b) < e/2"
    by auto

  from \<open>a : T\<close> \<open>b \<in> X\<close>
  obtain u L where u: "0 < u"
    and L: "\<And>t. t \<in> cball a u \<inter> T \<Longrightarrow> L-lipschitz_on  (cball b u \<inter> X) (f t)"
    by (erule local_lipschitzE[OF local_lipschitz])

  have "a \<in> cball a u \<inter> T" by (auto simp: \<open>0 < u\<close> \<open>a \<in> T\<close> less_imp_le)
  from lipschitz_on_nonneg[OF L[OF \<open>a \<in> cball _ _ \<inter> _\<close>]] have "0 \<le> L" .

  let ?d = "Min {d, u, (e/2/(L + 1))}"
  show "\<exists>d>0. \<forall>x\<in>T. \<forall>y\<in>X. dist (x, y) (a, b) < d \<longrightarrow> dist (f x y) (f a b) < e"
  proof (rule exI[where x = ?d], safe)
    show "0 < ?d"
      using \<open>0 \<le> L\<close> \<open>0 < u\<close> \<open>0 < e\<close> \<open>0 < d\<close>
      by (auto intro!: divide_pos_pos )
    fix x y
    assume "x \<in> T" "y \<in> X"
    assume dist_less: "dist (x, y) (a, b) < ?d"
    have "dist y b \<le> dist (x, y) (a, b)"
      using dist_snd_le[of "(x, y)" "(a, b)"]
      by auto
    also
    note dist_less
    also
    {
      note calculation
      also have "?d \<le> u" by simp
      finally have "dist y b < u" .
    }
    have "?d \<le> e/2/(L + 1)" by simp
    also have "(L + 1) * \<dots> \<le> e / 2"
      using \<open>0 < e\<close> \<open>L \<ge> 0\<close>
      by (auto simp: field_split_simps)
    finally have le1: "(L + 1) * dist y b < e / 2" using \<open>L \<ge> 0\<close> by simp

    have "dist x a \<le> dist (x, y) (a, b)"
      using dist_fst_le[of "(x, y)" "(a, b)"]
      by auto
    also note dist_less
    finally have "dist x a < ?d" .
    also have "?d \<le> d" by simp
    finally have "dist x a < d" .
    note \<open>dist x a < ?d\<close>
    also have "?d \<le> u" by simp
    finally have "dist x a < u" .
    then have "x \<in> cball a u \<inter> T"
      using \<open>x \<in> T\<close>
      by (auto simp: dist_commute)
    have "dist (f x y) (f a b) \<le> dist (f x y) (f x b) + dist (f x b) (f a b)"
      by (rule dist_triangle)
    also have "(L + 1)-lipschitz_on (cball b u \<inter> X) (f x)"
      using L[OF \<open>x \<in> cball a u \<inter> T\<close>]
      by (rule lipschitz_on_le) simp
    then have "dist (f x y) (f x b) \<le> (L + 1) * dist y b"
      apply (rule lipschitz_onD)
      subgoal
        using \<open>y \<in> X\<close> \<open>dist y b < u\<close>
        by (simp add: dist_commute)
      subgoal
        using \<open>0 < u\<close> \<open>b \<in> X\<close>
        by simp
      done
    also have "(L + 1) * dist y b \<le> e / 2"
      using le1 \<open>0 \<le> L\<close> by simp
    also have "dist (f x b) (f a b) < e / 2"
      by (rule d; fact)
    also have "e / 2 + e / 2 = e" by simp
    finally show "dist (f x y) (f a b) < e" by simp
  qed
qed

lemma local_lipschitz_compact_implies_lipschitz:
  assumes "compact X" "compact T"
  assumes cont: "\<And>x. x \<in> X \<Longrightarrow> continuous_on T (\<lambda>t. f t x)"
  obtains L where "\<And>t. t \<in> T \<Longrightarrow> L-lipschitz_on X (f t)"
proof -
  {
    assume *: "\<And>n::nat. \<not>(\<forall>t\<in>T. n-lipschitz_on X (f t))"
    {
      fix n::nat
      from *[of n] have "\<exists>x y t. t \<in> T \<and> x \<in> X \<and> y \<in> X \<and> dist (f t y) (f t x) > n * dist y x"
        by (force simp: lipschitz_on_def)
    } then obtain t and x y::"nat \<Rightarrow> 'b" where xy: "\<And>n. x n \<in> X" "\<And>n. y n \<in> X"
      and t: "\<And>n. t n \<in> T"
      and d: "\<And>n. dist (f (t n) (y n)) (f (t n) (x n)) > n * dist (y n) (x n)"
      by metis
    from xy assms obtain lx rx where lx': "lx \<in> X" "strict_mono (rx :: nat \<Rightarrow> nat)" "(x o rx) \<longlonglongrightarrow> lx"
      by (metis compact_def)
    with xy have "\<And>n. (y o rx) n \<in> X" by auto
    with assms obtain ly ry where ly': "ly \<in> X" "strict_mono (ry :: nat \<Rightarrow> nat)" "((y o rx) o ry) \<longlonglongrightarrow> ly"
      by (metis compact_def)
    with t have "\<And>n. ((t o rx) o ry) n \<in> T" by simp
    with assms obtain lt rt where lt': "lt \<in> T" "strict_mono (rt :: nat \<Rightarrow> nat)" "(((t o rx) o ry) o rt) \<longlonglongrightarrow> lt"
      by (metis compact_def)
    from lx' ly'
    have lx: "(x o (rx o ry o rt)) \<longlonglongrightarrow> lx" (is "?x \<longlonglongrightarrow> _")
      and ly: "(y o (rx o ry o rt)) \<longlonglongrightarrow> ly" (is "?y \<longlonglongrightarrow> _")
      and lt: "(t o (rx o ry o rt)) \<longlonglongrightarrow> lt" (is "?t \<longlonglongrightarrow> _")
      subgoal by (simp add: LIMSEQ_subseq_LIMSEQ o_assoc lt'(2))
      subgoal by (simp add: LIMSEQ_subseq_LIMSEQ ly'(3) o_assoc lt'(2))
      subgoal by (simp add: o_assoc lt'(3))
      done
    hence "(\<lambda>n. dist (?y n) (?x n)) \<longlonglongrightarrow> dist ly lx"
      by (metis tendsto_dist)
    moreover
    let ?S = "(\<lambda>(t, x). f t x) ` (T \<times> X)"
    have "eventually (\<lambda>n::nat. n > 0) sequentially"
      by (metis eventually_at_top_dense)
    hence "eventually (\<lambda>n. norm (dist (?y n) (?x n)) \<le> norm (\<bar>diameter ?S\<bar> / n) * 1) sequentially"
    proof eventually_elim
      case (elim n)
      have "0 < rx (ry (rt n))" using \<open>0 < n\<close>
        by (metis dual_order.strict_trans1 lt'(2) lx'(2) ly'(2) seq_suble)
      have compact: "compact ?S"
        by (auto intro!: compact_continuous_image continuous_on_subset[OF continuous_on_TimesI]
          compact_Times \<open>compact X\<close> \<open>compact T\<close> cont)
      have "norm (dist (?y n) (?x n)) = dist (?y n) (?x n)" by simp
      also
      from this elim d[of "rx (ry (rt n))"]
      have "\<dots> < dist (f (?t n) (?y n)) (f (?t n) (?x n)) / rx (ry (rt (n)))"
        using lx'(2) ly'(2) lt'(2) \<open>0 < rx _\<close>
        by (auto simp add: field_split_simps strict_mono_def)
      also have "\<dots> \<le> diameter ?S / n"
      proof (rule frac_le)
        show "diameter ?S \<ge> 0"
          using compact compact_imp_bounded diameter_ge_0 by blast
        show "dist (f (?t n) (?y n)) (f (?t n) (?x n)) \<le> diameter ((\<lambda>(t,x). f t x) ` (T \<times> X))"
          by (metis (no_types) compact compact_imp_bounded diameter_bounded_bound image_eqI mem_Sigma_iff o_apply split_conv t xy(1) xy(2))
        show "real n \<le> real (rx (ry (rt n)))"
          by (meson le_trans lt'(2) lx'(2) ly'(2) of_nat_mono strict_mono_imp_increasing)
      qed (use \<open>n > 0\<close> in auto)
      also have "\<dots> \<le> abs (diameter ?S) / n"
        by (auto intro!: divide_right_mono)
      finally show ?case by simp
    qed
    with _ have "(\<lambda>n. dist (?y n) (?x n)) \<longlonglongrightarrow> 0"
      by (rule tendsto_0_le)
        (metis tendsto_divide_0[OF tendsto_const] filterlim_at_top_imp_at_infinity
          filterlim_real_sequentially)
    ultimately have "lx = ly"
      using LIMSEQ_unique by fastforce
    with assms lx' have "lx \<in> X" by auto
    from \<open>lt \<in> T\<close> this obtain u L where L: "u > 0" "\<And>t. t \<in> cball lt u \<inter> T \<Longrightarrow> L-lipschitz_on (cball lx u \<inter> X) (f t)"
      by (erule local_lipschitzE[OF local_lipschitz])
    hence "L \<ge> 0" by (force intro!: lipschitz_on_nonneg \<open>lt \<in> T\<close>)

    from L lt ly lx \<open>lx = ly\<close>
    have
      "eventually (\<lambda>n. ?t n \<in> ball lt u) sequentially"
      "eventually (\<lambda>n. ?y n \<in> ball lx u) sequentially"
      "eventually (\<lambda>n. ?x n \<in> ball lx u) sequentially"
      by (auto simp: dist_commute Lim)
    moreover have "eventually (\<lambda>n. n > L) sequentially"
      by (metis filterlim_at_top_dense filterlim_real_sequentially)
    ultimately
    have "eventually (\<lambda>_. False) sequentially"
    proof eventually_elim
      case (elim n)
      hence "dist (f (?t n) (?y n)) (f (?t n) (?x n)) \<le> L * dist (?y n) (?x n)"
        using assms xy t
        unfolding dist_norm[symmetric]
        by (intro lipschitz_onD[OF L(2)]) (auto)
      also have "\<dots> \<le> n * dist (?y n) (?x n)"
        using elim by (intro mult_right_mono) auto
      also have "\<dots> \<le> rx (ry (rt n)) * dist (?y n) (?x n)"
        by (intro mult_right_mono[OF _ zero_le_dist])
           (meson lt'(2) lx'(2) ly'(2) of_nat_le_iff order_trans seq_suble)
      also have "\<dots> < dist (f (?t n) (?y n)) (f (?t n) (?x n))"
        by (auto intro!: d)
      finally show ?case by simp
    qed
    hence False
      by simp
  } then obtain L where "\<And>t. t \<in> T \<Longrightarrow> L-lipschitz_on X (f t)"
    by metis
  thus ?thesis ..
qed

lemma local_lipschitz_subset:
  assumes "S \<subseteq> T" "Y \<subseteq> X"
  shows "local_lipschitz S Y f"
proof (rule local_lipschitzI)
  fix t x assume "t \<in> S" "x \<in> Y"
  then have "t \<in> T" "x \<in> X" using assms by auto
  from local_lipschitzE[OF local_lipschitz, OF this]
  obtain u L where u: "0 < u" and L: "\<And>s. s \<in> cball t u \<inter> T \<Longrightarrow> L-lipschitz_on (cball x u \<inter> X) (f s)"
    by blast
  show "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> S. L-lipschitz_on (cball x u \<inter> Y) (f t)"
    using assms
    by (auto intro: exI[where x=u] exI[where x=L]
        intro!: u lipschitz_on_subset[OF _ Int_mono[OF order_refl \<open>Y \<subseteq> X\<close>]] L)
qed

end

lemma local_lipschitz_minus:
  fixes f::"'a::metric_space \<Rightarrow> 'b::metric_space \<Rightarrow> 'c::real_normed_vector"
  shows "local_lipschitz T X (\<lambda>t x. - f t x) = local_lipschitz T X f"
  by (auto simp: local_lipschitz_def lipschitz_on_minus)

lemma local_lipschitz_PairI:
  assumes f: "local_lipschitz A B (\<lambda>a b. f a b)"
  assumes g: "local_lipschitz A B (\<lambda>a b. g a b)"
  shows "local_lipschitz A B (\<lambda>a b. (f a b, g a b))"
proof (rule local_lipschitzI)
  fix t x assume "t \<in> A" "x \<in> B"
  from local_lipschitzE[OF f this] local_lipschitzE[OF g this]
  obtain u L v M where "0 < u" "(\<And>s. s \<in> cball t u \<inter> A \<Longrightarrow> L-lipschitz_on (cball x u \<inter> B) (f s))"
    "0 < v" "(\<And>s. s \<in> cball t v \<inter> A \<Longrightarrow> M-lipschitz_on (cball x v \<inter> B) (g s))"
    by metis
  then show "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> A. L-lipschitz_on (cball x u \<inter> B) (\<lambda>b. (f t b, g t b))"
    by (intro exI[where x="min u v"])
      (force intro: lipschitz_on_subset intro!: lipschitz_on_Pair)
qed

lemma local_lipschitz_constI: "local_lipschitz S T (\<lambda>t x. f t)"
  by (auto simp: intro!: local_lipschitzI lipschitz_on_constant intro: exI[where x=1])

lemma (in bounded_linear) local_lipschitzI:
  shows "local_lipschitz A B (\<lambda>_. f)"
proof (rule local_lipschitzI, goal_cases)
  case (1 t x)
  from lipschitz_boundE[of "(cball x 1 \<inter> B)"] obtain C where "C-lipschitz_on (cball x 1 \<inter> B) f" by auto
  then show ?case
    by (auto intro: exI[where x=1])
qed

proposition c1_implies_local_lipschitz:
  fixes T::"real set" and X::"'a::{banach,heine_borel} set"
    and f::"real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes f': "\<And>t x. t \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> (f t has_derivative blinfun_apply (f' (t, x))) (at x)"
  assumes cont_f': "continuous_on (T \<times> X) f'"
  assumes "open T"
  assumes "open X"
  shows "local_lipschitz T X f"
proof (rule local_lipschitzI)
  fix t x
  assume "t \<in> T" "x \<in> X"
  from open_contains_cball[THEN iffD1, OF \<open>open X\<close>, rule_format, OF \<open>x \<in> X\<close>]
  obtain u where u: "u > 0" "cball x u \<subseteq> X" by auto
  moreover
  from open_contains_cball[THEN iffD1, OF \<open>open T\<close>, rule_format, OF \<open>t \<in> T\<close>]
  obtain v where v: "v > 0" "cball t v \<subseteq> T" by auto
  ultimately
  have "compact (cball t v \<times> cball x u)" "cball t v \<times> cball x u \<subseteq> T \<times> X"
    by (auto intro!: compact_Times)
  then have "compact (f' ` (cball t v \<times> cball x u))"
    by (auto intro!: compact_continuous_image continuous_on_subset[OF cont_f'])
  then obtain B where B: "B > 0" "\<And>s y. s \<in> cball t v \<Longrightarrow> y \<in> cball x u \<Longrightarrow> norm (f' (s, y)) \<le> B"
    by (auto dest!: compact_imp_bounded simp: bounded_pos)

  have lipschitz: "B-lipschitz_on (cball x (min u v) \<inter> X) (f s)" if s: "s \<in> cball t v" for s
  proof -
    note s
    also note \<open>cball t v \<subseteq> T\<close>
    finally
    have deriv: "\<And>y. y \<in> cball x u \<Longrightarrow> (f s has_derivative blinfun_apply (f' (s, y))) (at y within cball x u)"
      using \<open>_ \<subseteq> X\<close>
      by (auto intro!: has_derivative_at_withinI[OF f'])
    have "norm (f s y - f s z) \<le> B * norm (y - z)"
      if "y \<in> cball x u" "z \<in> cball x u"
      for y z
      using s that
      by (intro differentiable_bound[OF convex_cball deriv])
        (auto intro!: B  simp: norm_blinfun.rep_eq[symmetric])
    then show ?thesis
      using \<open>0 < B\<close>
      by (auto intro!: lipschitz_onI simp: dist_norm)
  qed
  show "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> T. L-lipschitz_on (cball x u \<inter> X) (f t)"
    by (force intro: exI[where x="min u v"] exI[where x=B] intro!: lipschitz simp: u v)
qed

end
