section {* Bounded Continuous Functions *}
theory Bounded_Continuous_Function
imports Integration
begin

subsection{* Definition *}

definition "bcontfun = {f :: 'a::topological_space \<Rightarrow> 'b::metric_space. continuous_on UNIV f \<and> bounded (range f)}"

typedef ('a, 'b) bcontfun =
    "bcontfun :: ('a::topological_space \<Rightarrow> 'b::metric_space) set"
  by (auto simp: bcontfun_def intro: continuous_intros simp: bounded_def)

lemma bcontfunE:
  assumes "f \<in> bcontfun"
  obtains y where "continuous_on UNIV f" "\<And>x. dist (f x) u \<le> y"
  using assms unfolding bcontfun_def
  by (metis (lifting) bounded_any_center dist_commute mem_Collect_eq rangeI)

lemma bcontfunE':
  assumes "f \<in> bcontfun"
  obtains y where "continuous_on UNIV f" "\<And>x. dist (f x) undefined \<le> y"
  using assms bcontfunE
  by metis

lemma bcontfunI:
  "continuous_on UNIV f \<Longrightarrow> (\<And>x. dist (f x) u \<le> b) \<Longrightarrow> f \<in> bcontfun"
  unfolding bcontfun_def
  by (metis (lifting, no_types) bounded_def dist_commute mem_Collect_eq rangeE)

lemma bcontfunI':
  "continuous_on UNIV f \<Longrightarrow> (\<And>x. dist (f x) undefined \<le> b) \<Longrightarrow> f \<in> bcontfun"
  using bcontfunI by metis

lemma continuous_on_Rep_bcontfun[intro, simp]: "continuous_on T (Rep_bcontfun x)"
  using Rep_bcontfun[of x]
  by (auto simp: bcontfun_def intro: continuous_on_subset)

instantiation bcontfun :: (topological_space, metric_space) metric_space
begin

definition dist_bcontfun::"('a, 'b) bcontfun \<Rightarrow> ('a, 'b) bcontfun \<Rightarrow> real" where
  "dist_bcontfun f g = (SUP x. dist (Rep_bcontfun f x) (Rep_bcontfun g x))"

definition
  open_bcontfun::"('a, 'b) bcontfun set \<Rightarrow> bool" where
  "open_bcontfun S = (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"

lemma dist_bounded:
  fixes f ::"('a, 'b) bcontfun"
  shows "dist (Rep_bcontfun f x) (Rep_bcontfun g x) \<le> dist f g"
proof -
  have "Rep_bcontfun f \<in> bcontfun" using Rep_bcontfun .
  from bcontfunE'[OF this] obtain y where y:
    "continuous_on UNIV (Rep_bcontfun f)"
    "\<And>x. dist (Rep_bcontfun f x) undefined \<le> y"
    by auto
  have "Rep_bcontfun g \<in> bcontfun" using Rep_bcontfun .
  from bcontfunE'[OF this] obtain z where z:
    "continuous_on UNIV (Rep_bcontfun g)"
    "\<And>x. dist (Rep_bcontfun g x) undefined \<le> z"
    by auto
  show ?thesis unfolding dist_bcontfun_def
  proof (intro cSUP_upper bdd_aboveI2)
    fix x
    have "dist (Rep_bcontfun f x) (Rep_bcontfun g x) \<le> dist (Rep_bcontfun f x) undefined + dist (Rep_bcontfun g x) undefined"
      by (rule dist_triangle2)
    also have "\<dots> \<le> y + z" using y(2)[of x] z(2)[of x] by (rule add_mono)
    finally show "dist (Rep_bcontfun f x) (Rep_bcontfun g x) \<le> y + z" .
  qed simp
qed

lemma dist_bound:
  fixes f ::"('a, 'b) bcontfun"
  assumes "\<And>x. dist (Rep_bcontfun f x) (Rep_bcontfun g x) \<le> b"
  shows "dist f g \<le> b"
  using assms by (auto simp: dist_bcontfun_def intro: cSUP_least)

lemma dist_bounded_Abs:
  fixes f g ::"'a \<Rightarrow> 'b"
  assumes "f \<in> bcontfun" "g \<in> bcontfun"
  shows "dist (f x) (g x) \<le> dist (Abs_bcontfun f) (Abs_bcontfun g)"
  by (metis Abs_bcontfun_inverse assms dist_bounded)

lemma const_bcontfun: "(\<lambda>x::'a. b::'b) \<in> bcontfun"
  by (auto intro: bcontfunI continuous_on_const)

lemma dist_fun_lt_imp_dist_val_lt:
  assumes "dist f g < e"
  shows "dist (Rep_bcontfun f x) (Rep_bcontfun g x) < e"
  using dist_bounded assms by (rule le_less_trans)

lemma dist_val_lt_imp_dist_fun_le:
  assumes "\<forall>x. dist (Rep_bcontfun f x) (Rep_bcontfun g x) < e"
  shows "dist f g \<le> e"
unfolding dist_bcontfun_def
proof (intro cSUP_least)
  fix x
  show "dist (Rep_bcontfun f x) (Rep_bcontfun g x) \<le> e"
    using assms[THEN spec[where x=x]] by (simp add: dist_norm)
qed (simp)

instance
proof
  fix f g::"('a, 'b) bcontfun"
  show "dist f g = 0 \<longleftrightarrow> f = g"
  proof
    have "\<And>x. dist (Rep_bcontfun f x) (Rep_bcontfun g x) \<le> dist f g" by (rule dist_bounded)
    also assume "dist f g = 0"
    finally  show "f = g" by (auto simp: Rep_bcontfun_inject[symmetric] Abs_bcontfun_inverse)
  qed (auto simp: dist_bcontfun_def SUP_def simp del: Sup_image_eq intro!: cSup_eq)
next
  fix f g h :: "('a, 'b) bcontfun"
  show "dist f g \<le> dist f h + dist g h"
  proof (subst dist_bcontfun_def, safe intro!: cSUP_least)
    fix x
    have "dist (Rep_bcontfun f x) (Rep_bcontfun g x) \<le>
      dist (Rep_bcontfun f x) (Rep_bcontfun h x) + dist (Rep_bcontfun g x) (Rep_bcontfun h x)"
      by (rule dist_triangle2)
    also have "dist (Rep_bcontfun f x) (Rep_bcontfun h x) \<le> dist f h" by (rule dist_bounded)
    also have "dist (Rep_bcontfun g x) (Rep_bcontfun h x) \<le> dist g h" by (rule dist_bounded)
    finally show "dist (Rep_bcontfun f x) (Rep_bcontfun g x) \<le> dist f h + dist g h" by simp
  qed
qed (simp add: open_bcontfun_def)
end

lemma closed_Pi_bcontfun:
  fixes I::"'a::metric_space set" and X::"'a \<Rightarrow> 'b::complete_space set"
  assumes "\<And>i. i \<in> I \<Longrightarrow> closed (X i)"
  shows "closed (Abs_bcontfun ` (Pi I X \<inter> bcontfun))"
  unfolding closed_sequential_limits
proof safe
  fix f l
  assume seq: "\<forall>n. f n \<in> Abs_bcontfun ` (Pi I X \<inter> bcontfun)" and lim: "f ----> l"
  have lim_fun: "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x. dist (Rep_bcontfun (f n) x) (Rep_bcontfun l x) < e"
    using LIMSEQ_imp_Cauchy[OF lim, simplified Cauchy_def] metric_LIMSEQ_D[OF lim]
    by (intro uniformly_cauchy_imp_uniformly_convergent[where P="%_. True", simplified])
      (metis dist_fun_lt_imp_dist_val_lt)+
  show "l \<in> Abs_bcontfun ` (Pi I X \<inter> bcontfun)"
  proof (rule, safe)
    fix x assume "x \<in> I"
    hence "closed (X x)" using assms by simp
    moreover have "eventually (\<lambda>xa. Rep_bcontfun (f xa) x \<in> X x) sequentially"
    proof (rule always_eventually, safe)
      fix i
      from seq[THEN spec, of i] `x \<in> I`
      show "Rep_bcontfun (f i) x \<in> X x"
        by (auto simp: Abs_bcontfun_inverse)
    qed
    moreover note sequentially_bot
    moreover have "(\<lambda>n. Rep_bcontfun (f n) x) ----> Rep_bcontfun l x"
      using lim_fun by (blast intro!: metric_LIMSEQ_I)
    ultimately show "Rep_bcontfun l x \<in> X x"
      by (rule Lim_in_closed_set)
  qed (auto simp: Rep_bcontfun Rep_bcontfun_inverse)
qed

subsection {* Complete Space *}

instance bcontfun :: (metric_space, complete_space) complete_space
proof
  fix f::"nat \<Rightarrow> ('a,'b) bcontfun"
  assume "Cauchy f" --{* Cauchy equals uniform convergence *}
  then obtain g where limit_function:
    "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x. dist (Rep_bcontfun (f n) x) (g x) < e"
    using uniformly_convergent_eq_cauchy[of "\<lambda>_. True"
      "\<lambda>n. Rep_bcontfun (f n)"]
    unfolding Cauchy_def by (metis dist_fun_lt_imp_dist_val_lt)

  then obtain N where fg_dist: --{* for an upper bound on g *}
    "\<forall>n\<ge>N. \<forall>x. dist (g x) ( Rep_bcontfun (f n) x) < 1"
    by (force simp add: dist_commute)
  from bcontfunE'[OF Rep_bcontfun, of "f N"] obtain b where
    f_bound: "\<forall>x. dist (Rep_bcontfun (f N) x) undefined \<le> b" by force
  have "g \<in> bcontfun" --{* The limit function is bounded and continuous *}
  proof (intro bcontfunI)
    show "continuous_on UNIV g"
      using bcontfunE[OF Rep_bcontfun] limit_function
      by (intro continuous_uniform_limit[where
        f="%n. Rep_bcontfun (f n)" and F="sequentially"]) (auto
        simp add: eventually_sequentially trivial_limit_def dist_norm)
  next
    fix x
    from fg_dist have "dist (g x) (Rep_bcontfun (f N) x) < 1"
      by (simp add: dist_norm norm_minus_commute)
    with dist_triangle[of "g x" undefined "Rep_bcontfun (f N) x"]
    show "dist (g x) undefined \<le> 1 + b" using f_bound[THEN spec, of x]
      by simp
  qed
  show "convergent f"
  proof (rule convergentI, subst LIMSEQ_def, safe)
    --{* The limit function converges according to its norm *}
    fix e::real
    assume "e > 0" hence "e/2 > 0" by simp
    with limit_function[THEN spec, of"e/2"]
    have "\<exists>N. \<forall>n\<ge>N. \<forall>x. dist (Rep_bcontfun (f n) x) (g x) < e/2"
      by simp
    then obtain N where N: "\<forall>n\<ge>N. \<forall>x. dist (Rep_bcontfun (f n) x) (g x) < e / 2" by auto
    show "\<exists>N. \<forall>n\<ge>N. dist (f n) (Abs_bcontfun g) < e"
    proof (rule, safe)
      fix n
      assume "N \<le> n"
      with N show "dist (f n) (Abs_bcontfun g) < e"
        using dist_val_lt_imp_dist_fun_le[of
          "f n" "Abs_bcontfun g" "e/2"]
          Abs_bcontfun_inverse[OF `g \<in> bcontfun`] `e > 0` by simp
    qed
  qed
qed

subsection{* Supremum norm for a normed vector space *}

instantiation bcontfun :: (topological_space, real_normed_vector) real_vector
begin

definition "-f = Abs_bcontfun (\<lambda>x. -(Rep_bcontfun f x))"

definition "f + g = Abs_bcontfun (\<lambda>x. Rep_bcontfun f x + Rep_bcontfun g x)"

definition "f - g = Abs_bcontfun (\<lambda>x. Rep_bcontfun f x - Rep_bcontfun g x)"

definition "0 = Abs_bcontfun (\<lambda>x. 0)"

definition "scaleR r f = Abs_bcontfun (\<lambda>x. r *\<^sub>R Rep_bcontfun f x)"

lemma plus_cont:
  fixes f g ::"'a \<Rightarrow> 'b"
  assumes f: "f \<in> bcontfun" and g: "g \<in> bcontfun"
  shows "(\<lambda>x. f x + g x) \<in> bcontfun"
proof -
  from bcontfunE'[OF f] obtain y where "continuous_on UNIV f" "\<And>x. dist (f x) undefined \<le> y"
    by auto
  moreover
  from bcontfunE'[OF g] obtain z where "continuous_on UNIV g" "\<And>x. dist (g x) undefined \<le> z"
    by auto
  ultimately show ?thesis
  proof (intro bcontfunI)
    fix x
    have "dist (f x + g x) 0 = dist (f x + g x) (0 + 0)" by simp
    also have "\<dots> \<le> dist (f x) 0 + dist (g x) 0" by (rule dist_triangle_add)
    also have "\<dots> \<le> dist (Abs_bcontfun f) 0 + dist (Abs_bcontfun g) 0"
      unfolding zero_bcontfun_def using assms
      by (auto intro!: add_mono dist_bounded_Abs const_bcontfun)
    finally
    show "dist (f x + g x) 0 <= dist (Abs_bcontfun f) 0 + dist (Abs_bcontfun g) 0" .
  qed (simp add: continuous_on_add)
qed

lemma Rep_bcontfun_plus[simp]: "Rep_bcontfun (f + g) x = Rep_bcontfun f x + Rep_bcontfun g x"
  by (simp add: plus_bcontfun_def Abs_bcontfun_inverse plus_cont Rep_bcontfun)

lemma uminus_cont:
  fixes f ::"'a \<Rightarrow> 'b"
  assumes "f \<in> bcontfun"
  shows "(\<lambda>x. - f x) \<in> bcontfun"
proof -
  from bcontfunE[OF assms, of 0] obtain y where "continuous_on UNIV f" "\<And>x. dist (f x) 0 \<le> y"
    by auto
  thus ?thesis
  proof (intro bcontfunI)
    fix x
    assume "\<And>x. dist (f x) 0 \<le> y"
    thus "dist (- f x) 0 \<le> y" by (subst dist_minus[symmetric]) simp
  qed (simp add: continuous_on_minus)
qed

lemma Rep_bcontfun_uminus[simp]:
  "Rep_bcontfun (- f) x = - Rep_bcontfun f x"
  by (simp add: uminus_bcontfun_def Abs_bcontfun_inverse uminus_cont Rep_bcontfun)

lemma minus_cont:
  fixes f g ::"'a \<Rightarrow> 'b"
  assumes f: "f \<in> bcontfun" and g: "g \<in> bcontfun"
  shows "(\<lambda>x. f x - g x) \<in> bcontfun"
  using plus_cont [of f "- g"] assms by (simp add: uminus_cont fun_Compl_def)

lemma Rep_bcontfun_minus[simp]:
  "Rep_bcontfun (f - g) x = Rep_bcontfun f x - Rep_bcontfun g x"
  by (simp add: minus_bcontfun_def Abs_bcontfun_inverse minus_cont Rep_bcontfun)

lemma scaleR_cont:
  fixes a and f::"'a \<Rightarrow> 'b"
  assumes "f \<in> bcontfun"
  shows " (\<lambda>x. a *\<^sub>R f x) \<in> bcontfun"
proof -
  from bcontfunE[OF assms, of 0] obtain y where "continuous_on UNIV f" "\<And>x. dist (f x) 0 \<le> y"
    by auto
  thus ?thesis
  proof (intro bcontfunI)
    fix x assume "\<And>x. dist (f x) 0 \<le> y"
    then show "dist (a *\<^sub>R f x) 0 \<le> abs a * y"
      by (metis norm_cmul_rule_thm norm_conv_dist)
  qed (simp add: continuous_intros)
qed

lemma Rep_bcontfun_scaleR[simp]:
   "Rep_bcontfun (a *\<^sub>R g) x = a *\<^sub>R Rep_bcontfun g x"
  by (simp add: scaleR_bcontfun_def Abs_bcontfun_inverse scaleR_cont Rep_bcontfun)

instance
proof
qed (simp_all add: plus_bcontfun_def zero_bcontfun_def minus_bcontfun_def scaleR_bcontfun_def
    Abs_bcontfun_inverse Rep_bcontfun_inverse Rep_bcontfun algebra_simps
    plus_cont const_bcontfun minus_cont scaleR_cont)
end

instantiation bcontfun :: (topological_space, real_normed_vector) real_normed_vector
begin

definition norm_bcontfun::"('a, 'b) bcontfun \<Rightarrow> real" where
  "norm_bcontfun f = dist f 0"

definition "sgn (f::('a,'b) bcontfun) = f /\<^sub>R norm f"

instance
proof
  fix f g::"('a, 'b) bcontfun"
  show "dist f g = norm (f - g)"
    by (simp add: norm_bcontfun_def dist_bcontfun_def zero_bcontfun_def
    Abs_bcontfun_inverse const_bcontfun norm_conv_dist[symmetric] dist_norm)
  show "norm (f + g) \<le> norm f + norm g"
    unfolding norm_bcontfun_def
  proof (subst dist_bcontfun_def, safe intro!: cSUP_least)
    fix x
    have "dist (Rep_bcontfun (f + g) x) (Rep_bcontfun 0 x) \<le>
      dist (Rep_bcontfun f x) 0 + dist (Rep_bcontfun g x) 0"
      by (metis (hide_lams, no_types) Rep_bcontfun_minus Rep_bcontfun_plus diff_0_right dist_norm
        le_less_linear less_irrefl norm_triangle_lt)
    also have "dist (Rep_bcontfun f x) 0 \<le> dist f 0"
      using dist_bounded[of f x 0]
      by (simp add: Abs_bcontfun_inverse const_bcontfun zero_bcontfun_def)
    also have "dist (Rep_bcontfun g x) 0 \<le> dist g 0" using dist_bounded[of g x 0]
      by (simp add: Abs_bcontfun_inverse const_bcontfun zero_bcontfun_def)
    finally show "dist (Rep_bcontfun (f + g) x) (Rep_bcontfun 0 x) \<le> dist f 0 + dist g 0" by simp
  qed
next
  fix a and f g:: "('a, 'b) bcontfun"
  show "norm (a *\<^sub>R f) = \<bar>a\<bar> * norm f"
  proof -
    have "\<bar>a\<bar> * Sup (range (\<lambda>x. dist (Rep_bcontfun f x) 0)) =
      (SUP i:range (\<lambda>x. dist (Rep_bcontfun f x) 0). \<bar>a\<bar> * i)"
    proof (intro continuous_at_Sup_mono bdd_aboveI2)
      fix x
      show "dist (Rep_bcontfun f x) 0 \<le> norm f" using dist_bounded[of f x 0]
        by (simp add: norm_bcontfun_def norm_conv_dist Abs_bcontfun_inverse zero_bcontfun_def
          const_bcontfun)
    qed (auto intro!: monoI mult_left_mono continuous_intros)
    moreover
    have "range (\<lambda>x. dist (Rep_bcontfun (a *\<^sub>R f) x) 0) = 
      (\<lambda>x. \<bar>a\<bar> * x) ` (range (\<lambda>x. dist (Rep_bcontfun f x) 0))"
      by (auto simp: norm_conv_dist[symmetric])
    ultimately
    show "norm (a *\<^sub>R f) = \<bar>a\<bar> * norm f"
      by (simp add: norm_bcontfun_def dist_bcontfun_def norm_conv_dist Abs_bcontfun_inverse
                    zero_bcontfun_def const_bcontfun SUP_def del: Sup_image_eq)
  qed
qed (auto simp: norm_bcontfun_def sgn_bcontfun_def)

end

lemma bcontfun_normI:
  "continuous_on UNIV f \<Longrightarrow> (\<And>x. norm (f x) \<le> b) \<Longrightarrow> f \<in> bcontfun"
  unfolding norm_conv_dist
  by (auto intro: bcontfunI)

lemma norm_bounded:
  fixes f ::"('a::topological_space, 'b::real_normed_vector) bcontfun"
  shows "norm (Rep_bcontfun f x) \<le> norm f"
  using dist_bounded[of f x 0]
  by (simp add: norm_bcontfun_def norm_conv_dist Abs_bcontfun_inverse zero_bcontfun_def
    const_bcontfun)

lemma norm_bound:
  fixes f ::"('a::topological_space, 'b::real_normed_vector) bcontfun"
  assumes "\<And>x. norm (Rep_bcontfun f x) \<le> b"
  shows "norm f \<le> b"
  using dist_bound[of f 0 b] assms
  by (simp add: norm_bcontfun_def norm_conv_dist Abs_bcontfun_inverse zero_bcontfun_def
    const_bcontfun)

subsection{* Continuously Extended Functions *}

definition clamp::"'a::euclidean_space \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "clamp a b x = (\<Sum>i\<in>Basis. (if x\<bullet>i < a\<bullet>i then a\<bullet>i else if x\<bullet>i \<le> b\<bullet>i then x\<bullet>i else b\<bullet>i) *\<^sub>R i)"

definition ext_cont::"('a::euclidean_space \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b) bcontfun"
  where "ext_cont f a b = Abs_bcontfun ((\<lambda>x. f (clamp a b x)))"

lemma ext_cont_def':
  "ext_cont f a b = Abs_bcontfun (\<lambda>x.
    f (\<Sum>i\<in>Basis. (if x\<bullet>i < a\<bullet>i then a\<bullet>i else if x\<bullet>i \<le> b\<bullet>i then x\<bullet>i else b\<bullet>i) *\<^sub>R i))"
unfolding ext_cont_def clamp_def ..

lemma clamp_in_interval:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i"
  shows "clamp a b x \<in> cbox a b"
  unfolding clamp_def
  using box_ne_empty(1)[of a b] assms by (auto simp: cbox_def)

lemma dist_clamps_le_dist_args:
  fixes x::"'a::euclidean_space"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i"
  shows "dist (clamp a b y) (clamp a b x) \<le> dist y x"
proof -
    from box_ne_empty(1)[of a b] assms have "(\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
      by (simp add: cbox_def)
    hence "(\<Sum>i\<in>Basis. (dist (clamp a b y \<bullet> i) (clamp a b x \<bullet> i))\<^sup>2)
        \<le> (\<Sum>i\<in>Basis. (dist (y \<bullet> i) (x \<bullet> i))\<^sup>2)"
      by (auto intro!: setsum_mono
        simp add: clamp_def dist_real_def real_abs_le_square_iff[symmetric])
    thus ?thesis
      by (auto intro: real_sqrt_le_mono
        simp add: euclidean_dist_l2[where y=x] euclidean_dist_l2[where y="clamp a b x"] setL2_def)
qed

lemma clamp_continuous_at:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::metric_space"
  fixes x
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i"
  assumes f_cont: "continuous_on (cbox a b) f"
  shows "continuous (at x) (\<lambda>x. f (clamp a b x))"
unfolding continuous_at_eps_delta
proof (safe)
  fix x::'a and e::real
  assume "0 < e"
  moreover
  have "clamp a b x \<in> cbox a b" by (simp add: clamp_in_interval assms)
  moreover
  note f_cont[simplified continuous_on_iff]
  ultimately
  obtain d where d: "0 < d"
    "\<And>x'. x' \<in> cbox a b \<Longrightarrow> dist x' (clamp a b x) < d \<Longrightarrow> dist (f x') (f (clamp a b x)) < e"
    by force
  show "\<exists>d>0. \<forall>x'. dist x' x < d \<longrightarrow>
    dist (f (clamp a b x')) (f (clamp a b x)) < e"
    by (auto intro!: d clamp_in_interval assms dist_clamps_le_dist_args[THEN le_less_trans])
qed

lemma clamp_continuous_on:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::metric_space"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i"
  assumes f_cont: "continuous_on (cbox a b) f"
  shows "continuous_on UNIV (\<lambda>x. f (clamp a b x))"
  using assms
  by (auto intro: continuous_at_imp_continuous_on clamp_continuous_at)

lemma clamp_bcontfun:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i"
  assumes continuous: "continuous_on (cbox a b) f"
  shows "(\<lambda>x. f (clamp a b x)) \<in> bcontfun"
proof -
  from compact_continuous_image[OF continuous compact_cbox[of a b], THEN compact_imp_bounded]
  have "bounded (f ` (cbox a b))" .
  then obtain c where f_bound: "\<forall>x\<in>f ` cbox a b. norm x \<le> c" by (auto simp add: bounded_pos)
  show "(\<lambda>x. f (clamp a b x)) \<in> bcontfun"
  proof (intro bcontfun_normI)
    fix x
    from clamp_in_interval[OF assms(1), of x] f_bound
    show "norm (f (clamp a b x)) \<le> c" by (simp add: ext_cont_def)
  qed (simp add: clamp_continuous_on assms)
qed

lemma integral_clamp:
  "integral {t0::real..clamp t0 t1 x} f =
    (if x < t0 then 0 else if x \<le> t1 then integral {t0..x} f else integral {t0..t1} f)"
  by (auto simp: clamp_def)


declare [[coercion Rep_bcontfun]]

lemma ext_cont_cancel[simp]:
  fixes x a b::"'a::euclidean_space"
  assumes x: "x \<in> cbox a b"
  assumes "continuous_on (cbox a b) f"
  shows "ext_cont f a b x = f x"
  using assms
  unfolding ext_cont_def
proof (subst Abs_bcontfun_inverse[OF clamp_bcontfun])
  show "f (clamp a b x) = f x"
    using x unfolding clamp_def mem_box
    by (intro arg_cong[where f=f] euclidean_eqI[where 'a='a]) (simp add: not_less)
qed (auto simp: cbox_def)

lemma ext_cont_cong:
  assumes "t0 = s0"
  assumes "t1 = s1"
  assumes "\<And>t. t \<in> (cbox t0 t1) \<Longrightarrow> f t = g t"
  assumes "continuous_on (cbox t0 t1) f"
  assumes "continuous_on (cbox s0 s1) g"
  assumes ord: "\<And>i. i \<in> Basis \<Longrightarrow> t0 \<bullet> i \<le> t1 \<bullet> i"
  shows "ext_cont f t0 t1 = ext_cont g s0 s1"
  unfolding assms ext_cont_def
  using assms clamp_in_interval[OF ord]
  by (subst Rep_bcontfun_inject[symmetric]) simp

end
