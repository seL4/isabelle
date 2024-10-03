section \<open>Bounded Continuous Functions\<close>

theory Bounded_Continuous_Function
  imports
    Topology_Euclidean_Space
    Uniform_Limit
begin

subsection \<open>Definition\<close>

definition\<^marker>\<open>tag important\<close> "bcontfun = {f. continuous_on UNIV f \<and> bounded (range f)}"

typedef (overloaded) ('a, 'b) bcontfun (\<open>(\<open>notation=\<open>infix \<Rightarrow>\<^sub>C\<close>\<close>_ \<Rightarrow>\<^sub>C /_)\<close> [22, 21] 21) =
  "bcontfun::('a::topological_space \<Rightarrow> 'b::metric_space) set"
  morphisms apply_bcontfun Bcontfun
  by (auto intro: continuous_intros simp: bounded_def bcontfun_def)

declare [[coercion "apply_bcontfun :: ('a::topological_space \<Rightarrow>\<^sub>C'b::metric_space) \<Rightarrow> 'a \<Rightarrow> 'b"]]

setup_lifting type_definition_bcontfun

lemma continuous_on_apply_bcontfun[intro, simp]: "continuous_on T (apply_bcontfun x)"
  and bounded_apply_bcontfun[intro, simp]: "bounded (range (apply_bcontfun x))"
  using apply_bcontfun[of x]
  by (auto simp: bcontfun_def intro: continuous_on_subset)

lemma bcontfun_eqI: "(\<And>x. apply_bcontfun f x = apply_bcontfun g x) \<Longrightarrow> f = g"
  by transfer auto

lemma bcontfunE:
  assumes "f \<in> bcontfun"
  obtains g where "f = apply_bcontfun g"
  by (blast intro: apply_bcontfun_cases assms )

lemma const_bcontfun: "(\<lambda>x. b) \<in> bcontfun"
  by (auto simp: bcontfun_def image_def)

lift_definition const_bcontfun::"'b::metric_space \<Rightarrow> ('a::topological_space \<Rightarrow>\<^sub>C 'b)" is "\<lambda>c _. c"
  by (rule const_bcontfun)

(* TODO: Generalize to uniform spaces? *)
instantiation bcontfun :: (topological_space, metric_space) metric_space
begin

lift_definition\<^marker>\<open>tag important\<close> dist_bcontfun :: "'a \<Rightarrow>\<^sub>C 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C 'b \<Rightarrow> real"
  is "\<lambda>f g. (SUP x. dist (f x) (g x))" .

definition uniformity_bcontfun :: "('a \<Rightarrow>\<^sub>C 'b \<times> 'a \<Rightarrow>\<^sub>C 'b) filter"
  where "uniformity_bcontfun = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_bcontfun :: "('a \<Rightarrow>\<^sub>C 'b) set \<Rightarrow> bool"
  where "open_bcontfun S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"

lemma bounded_dist_le_SUP_dist:
  "bounded (range f) \<Longrightarrow> bounded (range g) \<Longrightarrow> dist (f x) (g x) \<le> (SUP x. dist (f x) (g x))"
  by (auto intro!: cSUP_upper bounded_imp_bdd_above bounded_dist_comp)

lemma dist_bounded:
  fixes f g :: "'a \<Rightarrow>\<^sub>C 'b"
  shows "dist (f x) (g x) \<le> dist f g"
  by transfer (auto intro!: bounded_dist_le_SUP_dist simp: bcontfun_def)

lemma dist_bound:
  fixes f g :: "'a \<Rightarrow>\<^sub>C 'b"
  assumes "\<And>x. dist (f x) (g x) \<le> b"
  shows "dist f g \<le> b"
  using assms
  by transfer (auto intro!: cSUP_least)

lemma dist_fun_lt_imp_dist_val_lt:
  fixes f g :: "'a \<Rightarrow>\<^sub>C 'b"
  assumes "dist f g < e"
  shows "dist (f x) (g x) < e"
  using dist_bounded assms by (rule le_less_trans)

instance
proof
  fix f g h :: "'a \<Rightarrow>\<^sub>C 'b"
  show "dist f g = 0 \<longleftrightarrow> f = g"
  proof
    have "\<And>x. dist (f x) (g x) \<le> dist f g"
      by (rule dist_bounded)
    also assume "dist f g = 0"
    finally show "f = g"
      by (auto simp: apply_bcontfun_inject[symmetric])
  qed (auto simp: dist_bcontfun_def intro!: cSup_eq)
  show "dist f g \<le> dist f h + dist g h"
  proof (rule dist_bound)
    fix x
    have "dist (f x) (g x) \<le> dist (f x) (h x) + dist (g x) (h x)"
      by (rule dist_triangle2)
    also have "dist (f x) (h x) \<le> dist f h"
      by (rule dist_bounded)
    also have "dist (g x) (h x) \<le> dist g h"
      by (rule dist_bounded)
    finally show "dist (f x) (g x) \<le> dist f h + dist g h"
      by simp
  qed
qed (rule open_bcontfun_def uniformity_bcontfun_def)+

end

lift_definition PiC::"'a::topological_space set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow>\<^sub>C 'b::metric_space) set"
  is "\<lambda>I X. Pi I X \<inter> bcontfun"
  by auto

lemma mem_PiC_iff: "x \<in> PiC I X \<longleftrightarrow> apply_bcontfun x \<in> Pi I X"
  by transfer simp

lemmas mem_PiCD = mem_PiC_iff[THEN iffD1]
  and mem_PiCI = mem_PiC_iff[THEN iffD2]

lemma tendsto_bcontfun_uniform_limit:
  fixes f::"'i \<Rightarrow> 'a::topological_space \<Rightarrow>\<^sub>C 'b::metric_space"
  assumes "(f \<longlongrightarrow> l) F"
  shows "uniform_limit UNIV f l F"
proof (rule uniform_limitI)
  fix e::real assume "e > 0"
  from tendstoD[OF assms this] have "\<forall>\<^sub>F x in F. dist (f x) l < e" .
  then show "\<forall>\<^sub>F n in F. \<forall>x\<in>UNIV. dist ((f n) x) (l x) < e"
    by eventually_elim (auto simp: dist_fun_lt_imp_dist_val_lt)
qed

lemma uniform_limit_tendsto_bcontfun:
  fixes f::"'i \<Rightarrow> 'a::topological_space \<Rightarrow>\<^sub>C 'b::metric_space"
    and l::"'a::topological_space \<Rightarrow>\<^sub>C 'b::metric_space"
  assumes "uniform_limit UNIV f l F"
  shows "(f \<longlongrightarrow> l) F"
proof (rule tendstoI)
  fix e::real assume "e > 0"
  then have "e / 2 > 0" by simp
  from uniform_limitD[OF assms this]
  have "\<forall>\<^sub>F i in F. \<forall>x. dist (f i x) (l x) < e / 2" by simp
  then have "\<forall>\<^sub>F x in F. dist (f x) l \<le> e / 2"
    by eventually_elim (blast intro: dist_bound less_imp_le)
  then show "\<forall>\<^sub>F x in F. dist (f x) l < e"
    by eventually_elim (use \<open>0 < e\<close> in auto)
qed

lemma uniform_limit_bcontfunE:
  fixes f::"'i \<Rightarrow> 'a::topological_space \<Rightarrow>\<^sub>C 'b::metric_space"
    and l::"'a::topological_space \<Rightarrow> 'b::metric_space"
  assumes "uniform_limit UNIV f l F" "F \<noteq> bot"
  obtains l'::"'a::topological_space \<Rightarrow>\<^sub>C 'b::metric_space"
  where "l = l'" "(f \<longlongrightarrow> l') F"
  by (metis (mono_tags, lifting) always_eventually apply_bcontfun apply_bcontfun_cases assms
      bcontfun_def mem_Collect_eq uniform_limit_bounded uniform_limit_tendsto_bcontfun
      uniform_limit_theorem)

lemma closed_PiC:
  fixes I :: "'a::metric_space set"
    and X :: "'a \<Rightarrow> 'b::complete_space set"
  assumes "\<And>i. i \<in> I \<Longrightarrow> closed (X i)"
  shows "closed (PiC I X)"
  unfolding closed_sequential_limits
proof safe
  fix f l
  assume seq: "\<forall>n. f n \<in> PiC I X" and lim: "f \<longlonglongrightarrow> l"
  show "l \<in> PiC I X"
  proof (safe intro!: mem_PiCI)
    fix x assume "x \<in> I"
    then have "closed (X x)"
      using assms by simp
    moreover have "eventually (\<lambda>i. f i x \<in> X x) sequentially"
      using seq \<open>x \<in> I\<close>
      by (auto intro!: eventuallyI dest!: mem_PiCD simp: Pi_iff)
    moreover note sequentially_bot
    moreover have "(\<lambda>n. (f n) x) \<longlonglongrightarrow> l x"
      using tendsto_bcontfun_uniform_limit[OF lim]
      by (rule tendsto_uniform_limitI) simp
    ultimately show "l x \<in> X x"
      by (rule Lim_in_closed_set)
  qed
qed


subsection \<open>Complete Space\<close>

instance\<^marker>\<open>tag important\<close> bcontfun :: (metric_space, complete_space) complete_space
proof
  fix f :: "nat \<Rightarrow> ('a, 'b) bcontfun"
  assume "Cauchy f"  \<comment> \<open>Cauchy equals uniform convergence\<close>
  then obtain g where "uniform_limit UNIV f g sequentially"
    using uniformly_convergent_eq_cauchy[of "\<lambda>_. True" f]
    unfolding Cauchy_def uniform_limit_sequentially_iff
    by (metis dist_fun_lt_imp_dist_val_lt)

  from uniform_limit_bcontfunE[OF this sequentially_bot]
  obtain l' where "g = apply_bcontfun l'" "(f \<longlonglongrightarrow> l')" by metis
  then show "convergent f"
    by (intro convergentI)
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Supremum norm for a normed vector space\<close>

instantiation\<^marker>\<open>tag unimportant\<close> bcontfun :: (topological_space, real_normed_vector) real_vector
begin

lemma uminus_cont: "f \<in> bcontfun \<Longrightarrow> (\<lambda>x. - f x) \<in> bcontfun" for f::"'a \<Rightarrow> 'b"
  by (auto simp: bcontfun_def intro!: continuous_intros)

lemma plus_cont: "f \<in> bcontfun \<Longrightarrow> g \<in> bcontfun \<Longrightarrow> (\<lambda>x. f x + g x) \<in> bcontfun" for f g::"'a \<Rightarrow> 'b"
  by (auto simp: bcontfun_def intro!: continuous_intros bounded_plus_comp)

lemma minus_cont: "f \<in> bcontfun \<Longrightarrow> g \<in> bcontfun \<Longrightarrow> (\<lambda>x. f x - g x) \<in> bcontfun" for f g::"'a \<Rightarrow> 'b"
  by (auto simp: bcontfun_def intro!: continuous_intros bounded_minus_comp)

lemma scaleR_cont: "f \<in> bcontfun \<Longrightarrow> (\<lambda>x. a *\<^sub>R f x) \<in> bcontfun" for f :: "'a \<Rightarrow> 'b"
  by (auto simp: bcontfun_def intro!: continuous_intros bounded_scaleR_comp)

lemma bcontfun_normI: "continuous_on UNIV f \<Longrightarrow> (\<And>x. norm (f x) \<le> b) \<Longrightarrow> f \<in> bcontfun"
  by (auto simp: bcontfun_def intro: boundedI)

lift_definition uminus_bcontfun::"('a \<Rightarrow>\<^sub>C 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>C 'b" is "\<lambda>f x. - f x"
  by (rule uminus_cont)

lift_definition plus_bcontfun::"('a \<Rightarrow>\<^sub>C 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>C 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>C 'b"  is "\<lambda>f g x. f x + g x"
  by (rule plus_cont)

lift_definition minus_bcontfun::"('a \<Rightarrow>\<^sub>C 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>C 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>C 'b"  is "\<lambda>f g x. f x - g x"
  by (rule minus_cont)

lift_definition zero_bcontfun::"'a \<Rightarrow>\<^sub>C 'b" is "\<lambda>_. 0"
  by (rule const_bcontfun)

lemma const_bcontfun_0_eq_0[simp]: "const_bcontfun 0 = 0"
  by transfer simp

lift_definition scaleR_bcontfun::"real \<Rightarrow> ('a \<Rightarrow>\<^sub>C 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>C 'b"  is "\<lambda>r g x. r *\<^sub>R g x"
  by (rule scaleR_cont)

lemmas [simp] =
  const_bcontfun.rep_eq
  uminus_bcontfun.rep_eq
  plus_bcontfun.rep_eq
  minus_bcontfun.rep_eq
  zero_bcontfun.rep_eq
  scaleR_bcontfun.rep_eq


instance
  by standard (auto intro!: bcontfun_eqI simp: algebra_simps)

end

instantiation\<^marker>\<open>tag unimportant\<close> bcontfun :: (topological_space, real_normed_vector) real_normed_vector
begin

definition norm_bcontfun :: "('a, 'b) bcontfun \<Rightarrow> real"
  where "norm_bcontfun f = dist f 0"

definition "sgn (f::('a,'b) bcontfun) = f /\<^sub>R norm f"

instance
proof
  fix a :: real
  fix f g :: "('a, 'b) bcontfun"
  show "dist f g = norm (f - g)"
    unfolding norm_bcontfun_def
    by transfer (simp add: dist_norm)
  show "norm (f + g) \<le> norm f + norm g"
    unfolding norm_bcontfun_def
    by transfer
      (auto intro!: cSUP_least norm_triangle_le add_mono bounded_norm_le_SUP_norm
        simp: dist_norm bcontfun_def)
  show "norm (a *\<^sub>R f) = \<bar>a\<bar> * norm f"
    unfolding norm_bcontfun_def
    apply transfer
    by (rule trans[OF _ continuous_at_Sup_mono[symmetric]])
      (auto intro!: monoI mult_left_mono continuous_intros bounded_imp_bdd_above
        simp: bounded_norm_comp bcontfun_def image_comp)
qed (auto simp: norm_bcontfun_def sgn_bcontfun_def)

end

lemma norm_bounded:
  fixes f :: "('a::topological_space, 'b::real_normed_vector) bcontfun"
  shows "norm (apply_bcontfun f x) \<le> norm f"
  using dist_bounded[of f x 0]
  by (simp add: dist_norm)

lemma norm_bound:
  fixes f :: "('a::topological_space, 'b::real_normed_vector) bcontfun"
  assumes "\<And>x. norm (apply_bcontfun f x) \<le> b"
  shows "norm f \<le> b"
  using dist_bound[of f 0 b] assms
  by (simp add: dist_norm)

subsection\<^marker>\<open>tag unimportant\<close> \<open>(bounded) continuous extenstion\<close>

lemma continuous_on_cbox_bcontfunE:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::metric_space"
  assumes "continuous_on (cbox a b) f"
  obtains g::"'a \<Rightarrow>\<^sub>C 'b" where
    "\<And>x. x \<in> cbox a b \<Longrightarrow> g x = f x"
    "\<And>x. g x = f (clamp a b x)"
proof -
  define g where "g \<equiv> ext_cont f a b"
  have "g \<in> bcontfun"
    using assms
    by (auto intro!: continuous_on_ext_cont simp: g_def bcontfun_def)
      (auto simp: g_def ext_cont_def
        intro!: clamp_bounded compact_imp_bounded[OF compact_continuous_image] assms)
  then obtain h where h: "g = apply_bcontfun h" by (rule bcontfunE)
  then have "h x = f x" if "x \<in> cbox a b" for x
    by (auto simp: h[symmetric] g_def that)
  moreover
  have "h x = f (clamp a b x)" for x
    by (auto simp: h[symmetric] g_def ext_cont_def)
  ultimately show ?thesis ..
qed

lifting_update bcontfun.lifting
lifting_forget bcontfun.lifting

end
