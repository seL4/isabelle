theory Rectifiable_Path
  imports Bounded_Variation Path_Connected Equivalence_Lebesgue_Henstock_Integration
begin


section \<open>Rectifiable paths and arc-length reparametrization\<close>

definition rectifiable_path :: \<open>(real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> bool\<close> where
  \<open>rectifiable_path g \<longleftrightarrow> path g \<and> has_bounded_variation_on g {0..1}\<close>

definition path_length :: \<open>(real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real\<close> where
  \<open>path_length g = vector_variation {0..1} g\<close>

text \<open>
  We can factor a BV function through its variation.  Moreover the factor is
  Lipschitz (hence continuous) on its domain, though without continuity of the
  original function that domain may not be an interval.
\<close>

lemma factor_through_variation:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>has_bounded_variation_on f {a..b}\<close>
  shows \<open>\<exists>g. (\<forall>x \<in> {a..b}. f x = g (vector_variation {a..x} f)) \<and>
             continuous_on ((\<lambda>x. vector_variation {a..x} f) ` {a..b}) g \<and>
             (\<forall>u \<in> (\<lambda>x. vector_variation {a..x} f) ` {a..b}.
              \<forall>v \<in> (\<lambda>x. vector_variation {a..x} f) ` {a..b}.
                dist (g u) (g v) \<le> dist u v)\<close>
proof -
  define S where \<open>S \<equiv> (\<lambda>x. vector_variation {a..x} f) ` {a..b}\<close>
  have claim1: \<open>\<exists>g. (\<forall>x \<in> {a..b}. f x = g (vector_variation {a..x} f)) \<and>
                    (\<forall>u \<in> S. \<forall>v \<in> S. dist (g u) (g v) \<le> dist u v)\<close>
  proof (cases \<open>{a..b} = {}\<close>)
    case True
    then show ?thesis unfolding S_def by auto
  next
    case False
    then have ab: \<open>a \<le> b\<close> by auto
    define V where \<open>V x \<equiv> vector_variation {a..x} f\<close> for x
    \<comment> \<open>Key injectivity-up-to-@{term f} property: @{term \<open>V x = V y\<close>} implies @{term \<open>f x = f y\<close>}\<close>
    have f_eq: \<open>f x = f y\<close>
      if \<open>x \<in> {a..b}\<close> \<open>y \<in> {a..b}\<close> \<open>V x = V y\<close> for x y
    proof -
      \<comment> \<open>Core argument: if @{term \<open>p \<le> q\<close>} with matching variation, then @{term \<open>f p = f q\<close>}\<close>
      have core: \<open>f p = f q\<close>
        if \<open>p \<le> q\<close> \<open>p \<in> {a..b}\<close> \<open>q \<in> {a..b}\<close> \<open>V p = V q\<close> for p q
      proof -
        have bv_aq: \<open>has_bounded_variation_on f {a..q}\<close>
          using has_bounded_variation_on_subset[OF assms] that ab by auto
        have p_in: \<open>p \<in> {a..q}\<close> using that by auto
        have vv0: \<open>vector_variation {p..q} f = 0\<close>
          by (metis V_def add.right_neutral add_left_cancel bv_aq
              \<open>V p = V q\<close> vector_variation_combine p_in)
        have bv_pq: \<open>has_bounded_variation_on f {p..q}\<close>
          using has_bounded_variation_on_subset[OF assms] that by auto
        from vector_variation_const_eq[OF bv_pq is_interval_cc] vv0
        show \<open>f p = f q\<close> using that by force
      qed
      show \<open>f x = f y\<close>
        using core[of x y] core[of y x] that by argo
    qed
    \<comment> \<open>Construct the factor @{term g} via Hilbert choice\<close>
    define g where \<open>g v \<equiv> f (SOME x. x \<in> {a..b} \<and> V x = v)\<close> for v
    have g_factor: \<open>f x = g (V x)\<close> if \<open>x \<in> {a..b}\<close> for x
      unfolding g_def
      by (metis (mono_tags, lifting) f_eq someI that)
    \<comment> \<open>Lipschitz property\<close>
    have g_lip: \<open>dist (g u) (g v) \<le> dist u v\<close>
      if \<open>u \<in> S\<close> \<open>v \<in> S\<close> for u v
    proof -
      from that obtain x y where
        x: \<open>x \<in> {a..b}\<close> \<open>u = V x\<close> and y: \<open>y \<in> {a..b}\<close> \<open>v = V y\<close>
        unfolding S_def V_def by auto
      \<comment> \<open>WLOG @{term \<open>x \<le> y\<close>}\<close>
      have lip: \<open>dist (g (V x)) (g (V y)) \<le> dist (V x) (V y)\<close>
        if xy: \<open>x \<le> y\<close> \<open>x \<in> {a..b}\<close> \<open>y \<in> {a..b}\<close> for x y
      proof -
        have bv_ay: \<open>has_bounded_variation_on f {a..y}\<close>
          using has_bounded_variation_on_subset[OF assms] xy(2,3) ab by auto
        have x_in: \<open>x \<in> {a..y}\<close> using xy by auto
        from vector_variation_combine[OF bv_ay x_in]
        have V_split: \<open>V y = V x + vector_variation {x..y} f\<close>
          unfolding V_def .
        have bv_xy: \<open>has_bounded_variation_on f {x..y}\<close>
          using has_bounded_variation_on_subset[OF assms] xy(1,2,3) by auto
        have Vx_le_Vy: \<open>V x \<le> V y\<close>
          using V_split vector_variation_pos_le[OF bv_xy] by linarith
        have \<open>dist (g (V x)) (g (V y)) = dist (f x) (f y)\<close>
          using g_factor xy(2,3) by simp
        also have \<open>\<dots> = norm (f x - f y)\<close> by (simp add: dist_norm)
        also have \<open>\<dots> \<le> vector_variation {x..y} f\<close>
          using vector_variation_ge_norm_function[OF bv_xy] xy(1) by auto
        also have \<open>\<dots> = V y - V x\<close> using V_split by simp
        also have \<open>\<dots> = dist (V x) (V y)\<close> using Vx_le_Vy by (simp add: dist_real_def)
        finally show ?thesis .
      qed
      show ?thesis
      proof (cases \<open>x \<le> y\<close>)
        case True then show ?thesis using lip x y by auto
      next
        case nle: False
        then have \<open>y \<le> x\<close> by auto
        then have \<open>dist (g (V y)) (g (V x)) \<le> dist (V y) (V x)\<close>
          using lip y(1) x(1) by auto
        then show ?thesis using x y by (simp add: dist_commute)
      qed
    qed
    show ?thesis
      using g_factor g_lip unfolding V_def by auto
  qed
  moreover
  have \<open>continuous_on S g\<close> if \<open>\<forall>u \<in> S. \<forall>v \<in> S. dist (g u) (g v) \<le> dist u v\<close> for g :: "real\<Rightarrow>'a"
    using continuous_on_iff order_le_less_trans that by blast
  ultimately show ?thesis
    using S_def by blast
qed

lemma factor_continuous_through_variation:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>a \<le> b\<close>
    and \<open>continuous_on {a..b} f\<close>
    and \<open>has_bounded_variation_on f {a..b}\<close>
  defines \<open>l \<equiv> vector_variation {a..b} f\<close>
  obtains g where \<open>\<forall>x \<in> {a..b}. f x = g (vector_variation {a..x} f)\<close>
    and \<open>continuous_on {0..l} g\<close>
    and \<open>\<forall>u \<in> {0..l}. \<forall>v \<in> {0..l}. dist (g u) (g v) \<le> dist u v\<close>
    and \<open>has_bounded_variation_on g {0..l}\<close>
    and \<open>(\<lambda>x. vector_variation {a..x} f) ` {a..b} = {0..l}\<close>
    and \<open>g ` {0..l} = f ` {a..b}\<close>
    and \<open>\<forall>x \<in> {0..l}. vector_variation {0..x} g = x\<close>
proof -
  define S where \<open>S \<equiv> (\<lambda>x. vector_variation {a..x} f) ` {a..b}\<close>
  obtain g where g_factor: \<open>\<forall>x \<in> {a..b}. f x = g (vector_variation {a..x} f)\<close>
    and g_cont: \<open>continuous_on S g\<close>
    and g_lip: \<open>\<forall>u \<in> S. \<forall>v \<in> S. dist (g u) (g v) \<le> dist u v\<close>
    using factor_through_variation[OF assms(3)] unfolding S_def by blast
  define V where \<open>V \<equiv> \<lambda>x. vector_variation {a..x} f\<close>
  have V_a: \<open>V a = 0\<close>
    unfolding V_def using vector_variation_on_null[of a a f] by simp
  have V_b: \<open>V b = l\<close>
    unfolding V_def l_def by simp
  have V_mono: \<open>V x \<le> V y\<close> if \<open>x \<in> {a..b}\<close> \<open>y \<in> {a..b}\<close> \<open>x \<le> y\<close> for x y
  proof -
    have bv_ay: \<open>has_bounded_variation_on f {a..y}\<close>
      using has_bounded_variation_on_subset[OF assms(3)] that by auto
    have \<open>V y = V x + vector_variation {x..y} f\<close>
      unfolding V_def using vector_variation_combine[OF bv_ay] that by auto
    moreover have \<open>vector_variation {x..y} f \<ge> 0\<close>
      by (rule vector_variation_pos_le[OF has_bounded_variation_on_subset[OF assms(3)]])
         (use that in auto)
    ultimately show ?thesis by linarith
  qed
  have V_cont: \<open>continuous_on {a..b} V\<close>
    unfolding V_def continuous_on_eq_continuous_within
    using vector_variation_continuous[OF assms(3)] assms(2)[unfolded continuous_on_eq_continuous_within]
    by simp
  have S_eq: \<open>S = {0..l}\<close>
  proof (rule antisym)
    show \<open>S \<subseteq> {0..l}\<close>
      using V_a V_b V_mono \<open>a \<le> b\<close> unfolding S_def V_def by force
    show \<open>{0..l} \<subseteq> S\<close>
    proof -
      have \<open>connected S\<close>
        unfolding S_def V_def[symmetric]
        using connected_continuous_image[OF V_cont] by auto
      moreover have \<open>0 \<in> S\<close> using V_a \<open>a \<le> b\<close> unfolding S_def V_def by force
      moreover have \<open>l \<in> S\<close> using V_b \<open>a \<le> b\<close> unfolding S_def V_def by force
      ultimately show ?thesis using connected_contains_Icc by blast
    qed
  qed
  show thesis
  proof
    show g_bv: \<open>has_bounded_variation_on g {0..l}\<close>
      using Lipschitz_imp_has_bounded_variation[where B=1]
      by (metis S_eq bounded_closed_interval dist_norm g_lip mult_1)
    show \<open>g ` {0..l} = f ` {a..b}\<close>
        using S_def S_eq g_factor by auto
    have \<open>vector_variation {0..x} g = x\<close> if \<open>x \<in> {0..l}\<close> for x
    proof (rule antisym)
      \<comment> \<open>Upper bound: 1-Lipschitz implies variation is at most length of interval\<close>
      show \<open>vector_variation {0..x} g \<le> x\<close>
      proof (rule has_bounded_variation_works(2)[OF has_bounded_variation_on_subset[OF g_bv]])
        show \<open>{0..x} \<subseteq> {0..l}\<close> using that by auto
      next
        fix d t assume dt: \<open>d division_of t\<close> \<open>t \<subseteq> {0..x}\<close>
        have \<open>(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> (\<Sum>k\<in>d. content k)\<close>
        proof (rule sum_mono)
          fix k assume kd: \<open>k \<in> d\<close>
          obtain lk uk where k_eq: \<open>k = {lk..uk}\<close> and lk_le: \<open>lk \<le> uk\<close>
            by (metis atLeastatMost_empty_iff2 box_real(2) division_ofD(3,4) dt(1) kd)
          have k_sub: \<open>k \<subseteq> {0..x}\<close> using division_ofD(2)[OF dt(1) kd] dt(2) by auto
          then have lk_in: \<open>lk \<in> {0..l}\<close> and uk_in: \<open>uk \<in> {0..l}\<close>
            using k_eq lk_le that by auto
          have \<open>norm (g (Sup k) - g (Inf k)) = norm (g uk - g lk)\<close>
            using lk_le k_eq by (simp add: cbox_interval)
          also have \<open>\<dots> \<le> dist (g uk) (g lk)\<close> by (simp add: dist_norm)
          also have \<open>\<dots> \<le> dist uk lk\<close>
            using g_lip lk_in uk_in S_eq by auto
          also have \<open>\<dots> = uk - lk\<close> using lk_le by (simp add: dist_real_def)
          also have \<open>\<dots> = content k\<close> using lk_le k_eq by (simp add: cbox_interval)
          finally show \<open>norm (g (Sup k) - g (Inf k)) \<le> content k\<close> .
        qed
        also have \<open>(\<Sum>k\<in>d. content k) \<le> content (cbox 0 x)\<close>
          using subadditive_content_division[OF dt(1)] dt(2)
          by (simp add: cbox_interval)
        also have \<open>\<dots> = x\<close> using that by (simp add: cbox_interval)
        finally show \<open>(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> x\<close> .
      qed
    next
      \<comment> \<open>Lower bound: variation of @{term g} on @{term \<open>{0..x}\<close>} at least  @{term x} 
           via factoring through @{term f}\<close>
      show \<open>x \<le> vector_variation {0..x} g\<close>
      proof -
        have x_in_S: \<open>x \<in> S\<close> using that S_eq by auto
        then obtain t where t_in: \<open>t \<in> {a..b}\<close> and Vt: \<open>V t = x\<close>
          unfolding S_def V_def by auto
        have bv_at: \<open>has_bounded_variation_on f {a..t}\<close>
          using has_bounded_variation_on_subset[OF assms(3)] t_in by auto
        have mono_V_at: \<open>mono_on {a..t} V\<close>
          unfolding mono_on_def using V_mono t_in by auto
        have g_bv_0x: \<open>has_bounded_variation_on g {V a..V t}\<close>
          using has_bounded_variation_on_subset[OF g_bv] V_a Vt that by auto
            \<comment> \<open>@{term \<open>g \<circ> V\<close>} agrees with @{term f} on @{term \<open>{a..t}\<close>}\<close>
        have gV_eq_f: \<open>g (V u) = f u\<close> if \<open>u \<in> {a..t}\<close> for u
          using g_factor t_in that V_def by auto
            \<comment> \<open>Therefore their variations on @{term \<open>{a..t}\<close>} are equal\<close>
        have var_eq: \<open>vector_variation {a..t} (g \<circ> V) = vector_variation {a..t} f\<close>
        proof -
          have eq: \<open>norm ((g \<circ> V) (Sup k) - (g \<circ> V) (Inf k)) = norm (f (Sup k) - f (Inf k))\<close>
            if div: \<open>d division_of s\<close> \<open>s \<subseteq> {a..t}\<close> and kd: \<open>k \<in> d\<close> for d s k
          proof -
            obtain lk uk where \<open>k = cbox lk uk\<close> \<open>k \<noteq> {}\<close> and lu: \<open>lk \<le> uk\<close>
              using division_ofD(3,4)[OF div(1) kd] by auto
            then have k_eq: \<open>k = {lk..uk}\<close> and Inf_k: \<open>Inf k = lk\<close> and Sup_k: \<open>Sup k = uk\<close>
              using \<open>k = cbox lk uk\<close> by (auto simp: cbox_interval)
            have \<open>k \<subseteq> {a..t}\<close>
              using division_ofD(2)[OF div(1) kd] div(2) by auto
            then have \<open>Inf k \<in> {a..t}\<close> \<open>Sup k \<in> {a..t}\<close> using lu Inf_k Sup_k k_eq by auto
            then show ?thesis using gV_eq_f by (simp add: comp_def)
          qed
          have sum_eq: \<open>(\<Sum>k\<in>d. norm ((g \<circ> V) (Sup k) - (g \<circ> V) (Inf k))) =
              (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))\<close>
            if \<open>d division_of s\<close> \<open>s \<subseteq> {a..t}\<close> for d s
            by (intro sum.cong refl eq[OF that])
          have \<open>{\<Sum>k\<in>d. norm ((g \<circ> V) (Sup k) - (g \<circ> V) (Inf k)) |d. \<exists>s. d division_of s \<and> s \<subseteq> {a..t}}
              = {\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) |d. \<exists>s. d division_of s \<and> s \<subseteq> {a..t}}\<close>
            (is \<open>?L = ?R\<close>)
          proof (rule antisym; rule subsetI)
            fix v assume \<open>v \<in> ?L\<close>
            then obtain d s where ds: \<open>d division_of s\<close> \<open>s \<subseteq> {a..t}\<close>
              and \<open>v = (\<Sum>k\<in>d. norm ((g \<circ> V) (Sup k) - (g \<circ> V) (Inf k)))\<close> by auto
            then have \<open>v = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))\<close>
              using sum_eq[OF ds] by simp
            then show \<open>v \<in> ?R\<close> using ds by blast
          next
            fix v assume \<open>v \<in> ?R\<close>
            then obtain d s where ds: \<open>d division_of s\<close> \<open>s \<subseteq> {a..t}\<close>
              and \<open>v = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))\<close> by auto
            then have \<open>v = (\<Sum>k\<in>d. norm ((g \<circ> V) (Sup k) - (g \<circ> V) (Inf k)))\<close>
              using sum_eq[OF ds] by simp
            then show \<open>v \<in> ?L\<close> using ds by blast
          qed
          then show ?thesis
            unfolding vector_variation_def set_variation_def comp_def by auto
        qed
          \<comment> \<open>Composition lemma: variation of @{term \<open>g \<circ> V\<close>} on 
               @{term \<open>{a..t}\<close>} is at most variation of @{term g} on @{term \<open>{V a..V t}\<close>}\<close>
        have \<open>vector_variation {a..t} (g \<circ> V) \<le> vector_variation {V a..V t} g\<close>
          using has_bounded_variation_compose_monotone(2)[OF g_bv_0x mono_V_at] .
        then have \<open>vector_variation {a..t} f \<le> vector_variation {0..x} g\<close>
          using var_eq V_a Vt by simp
        moreover have \<open>x = vector_variation {a..t} f\<close>
          using Vt[symmetric] by (simp add: V_def)
        ultimately show ?thesis by linarith
      qed
    qed
    then show \<open>\<forall>x\<in>{0..l}. vector_variation {0..x} g = x\<close>
      by blast
  qed (use S_def S_eq g_cont g_factor g_lip  in auto)+
qed

text \<open>Arc-length reparametrization and existence of shortest paths.\<close>

lemma arc_length_reparametrization:
  fixes g :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>rectifiable_path g\<close>
  obtains h where
    \<open>rectifiable_path h\<close>
    \<open>path_image h = path_image g\<close>
    \<open>pathstart h = pathstart g\<close>
    \<open>pathfinish h = pathfinish g\<close>
    \<open>path_length h = path_length g\<close>
    \<open>arc g \<Longrightarrow> arc h\<close>
    \<open>simple_path g \<Longrightarrow> simple_path h\<close>
    \<open>\<forall>t \<in> {0..1}. path_length (subpath 0 t h) = path_length g * t\<close>
    \<open>\<forall>x \<in> {0..1}. \<forall>y \<in> {0..1}.
        dist (h x) (h y) \<le> path_length g * dist x y\<close>
proof -
  define l where \<open>l \<equiv> path_length g\<close>
  from assms have g_path: \<open>path g\<close> and g_bv: \<open>has_bounded_variation_on g {0..1}\<close>
    unfolding rectifiable_path_def by auto
  then have g_cont: \<open>continuous_on {0..1} g\<close>
    by (simp add: path_def pathin_def continuous_map_iff_continuous)
  have l_eq: \<open>l = vector_variation {0..1} g\<close>
    unfolding l_def path_length_def by simp
  obtain h where
    h_factor: \<open>\<forall>x \<in> {0..1}. g x = h (vector_variation {0..x} g)\<close>
    and h_cont: \<open>continuous_on {0..l} h\<close>
    and h_lip: \<open>\<forall>u \<in> {0..l}. \<forall>v \<in> {0..l}. dist (h u) (h v) \<le> dist u v\<close>
    and h_bv: \<open>has_bounded_variation_on h {0..l}\<close>
    and h_image_var: \<open>(\<lambda>x. vector_variation {0..x} g) ` {0..1} = {0..l}\<close>
    and h_image: \<open>h ` {0..l} = g ` {0..1}\<close>
    and h_var: \<open>\<forall>x \<in> {0..l}. vector_variation {0..x} h = x\<close>
    using factor_continuous_through_variation[of 0 1 g, folded l_eq]
    using g_cont g_bv by auto
  have l_nonneg: \<open>0 \<le> l\<close>
    using vector_variation_pos_le[OF g_bv] l_eq by simp
  have scale_image: \<open>(\<lambda>x. x *\<^sub>R l) ` {0..1} = {0..l}\<close>
    using l_nonneg image_mult_atLeastAtMost_if'[of l 0 1] by auto
  have scale_mono: \<open>mono_on {0..1} (\<lambda>x. x *\<^sub>R l)\<close>
    using l_nonneg by (intro mono_onI) (simp add: mult_right_mono)
  have h_0: \<open>h 0 = g 0\<close>
    using h_factor[rule_format, of 0] vector_variation_on_null[of 0 0 g]
    by simp
  have h_l: \<open>h l = g 1\<close>
    using h_factor[rule_format, of 1] l_eq by simp
  show ?thesis
  proof
    show \<open>rectifiable_path (h \<circ> (\<lambda>x. x *\<^sub>R l))\<close>
    proof -
      have \<open>continuous_on {0..1} (\<lambda>x. x * l)\<close>
        by (intro continuous_intros)
      then have path: \<open>path (h \<circ> (\<lambda>x. x *\<^sub>R l))\<close>
        unfolding path_def pathin_def continuous_map_iff_continuous
        using continuous_on_compose[of \<open>{0..1}\<close> \<open>\<lambda>x. x * l\<close> h] h_cont scale_image
        by (simp add: image_comp comp_def)
      have bv: \<open>has_bounded_variation_on (h \<circ> (\<lambda>x. x *\<^sub>R l)) {0..1}\<close>
        using has_bounded_variation_compose_monotone(1)[OF _ scale_mono] h_bv
        by simp
      show ?thesis
        unfolding rectifiable_path_def using path bv by simp
    qed
    show \<open>path_image (h \<circ> (\<lambda>x. x *\<^sub>R l)) = path_image g\<close>
      unfolding path_image_def image_comp[symmetric] scale_image
      using h_image by simp
    show \<open>pathstart (h \<circ> (\<lambda>x. x *\<^sub>R l)) = pathstart g\<close>
      unfolding pathstart_def using h_0 by simp
    show \<open>pathfinish (h \<circ> (\<lambda>x. x *\<^sub>R l)) = pathfinish g\<close>
      unfolding pathfinish_def using h_l by simp
    show \<open>path_length (h \<circ> (\<lambda>x. x *\<^sub>R l)) = path_length g\<close>
    proof -
      have h_var_l: \<open>vector_variation {0..l} h = l\<close>
        using h_var l_nonneg by simp
      have upper: \<open>vector_variation {0..1} (h \<circ> (\<lambda>x. x *\<^sub>R l)) \<le> l\<close>
        by (metis (no_types, lifting) h_bv h_var_l has_bounded_variation_compose_monotone(2) pth_1
            pth_4(1) scale_mono)
      have lower: \<open>l \<le> vector_variation {0..1} (h \<circ> (\<lambda>x. x *\<^sub>R l))\<close>
      proof (cases \<open>l = 0\<close>)
        case True
        then show ?thesis
          using vector_variation_pos_le[OF has_bounded_variation_compose_monotone(1)[OF _ scale_mono] ] h_bv
          by simp
      next
        case False
        then have l_pos: \<open>0 < l\<close> using l_nonneg by simp
        have inv_mono: \<open>mono_on {0..l} (\<lambda>x. x / l)\<close>
          using l_pos by (intro mono_onI) (simp add: divide_right_mono)
        have inv_bv: \<open>has_bounded_variation_on (h \<circ> (\<lambda>x. x *\<^sub>R l)) {(0::real) / l..l / l}\<close>
          using has_bounded_variation_compose_monotone(1)[OF _ scale_mono] h_bv l_pos
          by simp
        have eq: \<open>(h \<circ> (\<lambda>x. x *\<^sub>R l)) \<circ> (\<lambda>x. x / l) = h\<close> (is \<open>?lhs = ?rhs\<close>)
          using False by auto
        have \<open>vector_variation {0..l} ((h \<circ> (\<lambda>x. x *\<^sub>R l)) \<circ> (\<lambda>x. x / l))
              \<le> vector_variation {0 / l..l / l} (h \<circ> (\<lambda>x. x *\<^sub>R l))\<close>
          using has_bounded_variation_compose_monotone(2)[OF inv_bv inv_mono] .
        then show ?thesis
          using eq h_var_l l_pos by simp
      qed
      show ?thesis
        unfolding path_length_def using upper lower l_eq by linarith
    qed
    show \<open>arc (h \<circ> (\<lambda>x. x *\<^sub>R l))\<close> if \<open>arc g\<close>
    proof -
      have g_inj: \<open>inj_on g {0..1}\<close>
        using arc_def that by blast
      have l_pos: \<open>0 < l\<close>
      proof (rule ccontr)
        assume \<open>\<not> 0 < l\<close>
        then have \<open>l = 0\<close> using l_nonneg by simp
        then have \<open>\<exists>c. \<forall>t \<in> {0..1}. g t = c\<close>
          using vector_variation_const_eq[OF g_bv] l_eq by auto
        then have \<open>g 0 = g 1\<close> by auto
        then show False using arc_distinct_ends[OF that]
          unfolding pathstart_def pathfinish_def by simp
      qed
      have h_inj: \<open>inj_on h {0..l}\<close>
        using that
        by (smt (verit, ccfv_SIG) arcD h_factor h_image_var image_iff linorder_inj_onI')
      have scale_inj: \<open>inj_on (\<lambda>x. x *\<^sub>R l) {0..1}\<close>
        using l_pos by (intro inj_onI) simp
      have comp_inj: \<open>inj_on (h \<circ> (\<lambda>x. x *\<^sub>R l)) {0..1}\<close>
        using comp_inj_on[OF scale_inj] h_inj scale_image by auto
      show \<open>arc (h \<circ> (\<lambda>x. x *\<^sub>R l))\<close>
        unfolding arc_def using comp_inj
        using \<open>rectifiable_path (h \<circ> (\<lambda>x. x *\<^sub>R l))\<close> rectifiable_path_def by blast
    qed
    show \<open>simple_path (h \<circ> (\<lambda>x. x *\<^sub>R l))\<close> if sp: \<open>simple_path g\<close>
    proof -
      have g_lf: \<open>loop_free g\<close>
        using simple_path_def that by blast
      have l_pos: \<open>0 < l\<close>
      proof (rule ccontr)
        assume \<open>\<not> 0 < l\<close>
        then have \<open>l = 0\<close> using l_nonneg by simp
        then obtain c where \<open>\<forall>t \<in> {0..1}. g t = c\<close>
          using vector_variation_const_eq[OF g_bv] l_eq by auto
        then have eq: \<open>g 0 = g (1/2)\<close> by auto
        then show False
          using g_lf[unfolded loop_free_def, rule_format, of 0 \<open>1/2\<close>] by auto
      qed
      show \<open>simple_path (h \<circ> (\<lambda>x. x *\<^sub>R l))\<close>
        unfolding simple_path_def
      proof (intro conjI)
        show \<open>path (h \<circ> (\<lambda>x. x *\<^sub>R l))\<close>
          using \<open>rectifiable_path (h \<circ> (\<lambda>x. x *\<^sub>R l))\<close> rectifiable_path_def by blast
        show \<open>loop_free (h \<circ> (\<lambda>x. x *\<^sub>R l))\<close>
          unfolding loop_free_def comp_def
        proof (intro ballI impI)
          fix x y assume x01: \<open>x \<in> {0..1}\<close> and y01: \<open>y \<in> {0..1}\<close>
            and eq: \<open>h (x *\<^sub>R l) = h (y *\<^sub>R l)\<close>
          have xl_in: \<open>x * l \<in> {0..l}\<close> and yl_in: \<open>y * l \<in> {0..l}\<close>
            using x01 y01 l_nonneg mult_right_mono[of _ 1 l] by auto
          from xl_in obtain s where s01: \<open>s \<in> {0..1}\<close> and xs: \<open>x * l = vector_variation {0..s} g\<close>
            using h_image_var[symmetric] by auto
          from yl_in obtain t where t01: \<open>t \<in> {0..1}\<close> and yt: \<open>y * l = vector_variation {0..t} g\<close>
            using h_image_var[symmetric] by auto
          have \<open>g s = h (vector_variation {0..s} g)\<close> using h_factor s01 by auto
          also have \<open>\<dots> = h (y * l)\<close> using xs eq by simp
          also have \<open>\<dots> = h (vector_variation {0..t} g)\<close> using yt by simp
          also have \<open>\<dots> = g t\<close> using h_factor t01 by auto
          finally have \<open>s = t \<or> s = 0 \<and> t = 1 \<or> s = 1 \<and> t = 0\<close>
            using g_lf s01 t01 unfolding loop_free_def by blast
          then have \<open>x * l = y * l \<or> x * l = 0 \<and> y * l = l \<or> x * l = l \<and> y * l = 0\<close>
            using xs yt l_eq vector_variation_on_null[of 0 0 g] by auto
          then show \<open>x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0\<close>
            using l_pos by auto
        qed
      qed
    qed
    show \<open>\<forall>t \<in> {0..1}. path_length (subpath 0 t (h \<circ> (\<lambda>x. x *\<^sub>R l))) = path_length g * t\<close>
    proof (intro ballI)
      fix t :: real assume t01: \<open>t \<in> {0..1}\<close>
      then have t_nonneg: \<open>0 \<le> t\<close> and t_le1: \<open>t \<le> 1\<close> by auto
      define m where \<open>m = t * l\<close>
      have m_nonneg: \<open>0 \<le> m\<close> unfolding m_def using t_nonneg l_nonneg by simp
      have m_le_l: \<open>m \<le> l\<close> unfolding m_def
        using mult_right_mono[of t 1 l] t_le1 l_nonneg by simp
      have m_in: \<open>m \<in> {0..l}\<close> using m_nonneg m_le_l by simp
      have sub_eq: \<open>subpath 0 t (h \<circ> (\<lambda>x. x *\<^sub>R l)) = h \<circ> (\<lambda>x. x *\<^sub>R m)\<close>
        unfolding subpath_def comp_def m_def by (auto simp: algebra_simps)
      have scale_m_image: \<open>(\<lambda>x. x *\<^sub>R m) ` {0..1} = {0..m}\<close>
        using m_nonneg image_mult_atLeastAtMost_if'[of m 0 1] by auto
      have scale_m_mono: \<open>mono_on {0..1} (\<lambda>x. x *\<^sub>R m)\<close>
        using m_nonneg by (intro mono_onI) (simp add: mult_right_mono)
      have h_bv_m: \<open>has_bounded_variation_on h {0..m}\<close>
        using has_bounded_variation_on_subset[OF h_bv] m_le_l m_nonneg by auto
      have h_var_m: \<open>vector_variation {0..m} h = m\<close>
        using h_var m_in by auto
      have upper: \<open>vector_variation {0..1} (h \<circ> (\<lambda>x. x *\<^sub>R m)) \<le> m\<close>
        by (metis (no_types, lifting) h_bv_m h_var_m has_bounded_variation_compose_monotone(2)
            pth_1 pth_4(1) scale_m_mono)
      have lower: \<open>m \<le> vector_variation {0..1} (h \<circ> (\<lambda>x. x *\<^sub>R m))\<close>
      proof (cases \<open>m = 0\<close>)
        case True
        then show ?thesis
          using vector_variation_pos_le[OF has_bounded_variation_compose_monotone(1)[OF _ scale_m_mono]]
            h_bv_m by simp
      next
        case False
        then have m_pos: \<open>0 < m\<close> using m_nonneg by simp
        have inv_mono: \<open>mono_on {0..m} (\<lambda>x. x / m)\<close>
          using m_pos by (intro mono_onI) (simp add: divide_right_mono)
        have inv_bv: \<open>has_bounded_variation_on (h \<circ> (\<lambda>x. x *\<^sub>R m)) {(0::real) / m..m / m}\<close>
          using has_bounded_variation_compose_monotone(1)[OF _ scale_m_mono] h_bv_m m_pos
          by simp
        have eq: \<open>(h \<circ> (\<lambda>x. x *\<^sub>R m)) \<circ> (\<lambda>x. x / m) = h\<close>
          using False by auto
        have \<open>vector_variation {0..m} ((h \<circ> (\<lambda>x. x *\<^sub>R m)) \<circ> (\<lambda>x. x / m))
              \<le> vector_variation {0 / m..m / m} (h \<circ> (\<lambda>x. x *\<^sub>R m))\<close>
          using has_bounded_variation_compose_monotone(2)[OF inv_bv inv_mono] .
        then show ?thesis
          using eq h_var_m m_pos by simp
      qed
      show \<open>path_length (subpath 0 t (h \<circ> (\<lambda>x. x *\<^sub>R l))) = path_length g * t\<close>
        unfolding path_length_def sub_eq l_eq[symmetric]
        using upper lower m_def by (simp add: mult.commute)
    qed
    show \<open>\<forall>x \<in> {0..1}. \<forall>y \<in> {0..1}.
        dist ((h \<circ> (\<lambda>x. x *\<^sub>R l)) x) ((h \<circ> (\<lambda>x. x *\<^sub>R l)) y) \<le> path_length g * dist x y\<close>
    proof (intro ballI)
      fix x y :: real assume \<open>x \<in> {0..1}\<close> \<open>y \<in> {0..1}\<close>
      then have \<open>x * l \<in> {0..l}\<close> \<open>y * l \<in> {0..l}\<close>
        using l_nonneg mult_right_mono[of _ 1 l] by auto
      then have \<open>dist (h (x * l)) (h (y * l)) \<le> dist (x * l) (y * l)\<close>
        using h_lip by auto
      also have \<open>\<dots> = l * dist x y\<close>
        unfolding dist_real_def using l_nonneg
        by (simp add: abs_mult left_diff_distrib[symmetric])
      finally show \<open>dist ((h \<circ> (\<lambda>x. x *\<^sub>R l)) x) ((h \<circ> (\<lambda>x. x *\<^sub>R l)) y) \<le> path_length g * dist x y\<close>
        unfolding l_def comp_def by simp
    qed
  qed
qed

corollary bounded_variation_absolutely_integrable_real_interval:
  fixes f :: "real \<Rightarrow> 'm::euclidean_space"
  assumes "f integrable_on {a..b}"
    and "\<And>d. d division_of {a..b} \<Longrightarrow> sum (\<lambda>K. norm(integral K f)) d \<le> B"
  shows "f absolutely_integrable_on {a..b}"
  by (metis assms bounded_variation_absolutely_integrable_interval interval_cbox)

lemma absolutely_integrable_bounded_variation_eq:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  shows \<open>f absolutely_integrable_on {a..b} \<longleftrightarrow>
    f integrable_on {a..b} \<and>
    has_bounded_variation_on (\<lambda>t. integral {a..t} f) {a..b}\<close>
  (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof
  assume L: ?L
  then have int: \<open>f integrable_on {a..b}\<close>
    using absolutely_integrable_on_def by blast
  have nint: \<open>(\<lambda>x. norm (f x)) integrable_on {a..b}\<close>
    using L absolutely_integrable_on_def by blast
  have bv: \<open>has_bounded_variation_on (\<lambda>t. integral {a..t} f) {a..b}\<close>
    unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
  proof (intro exI allI impI)
    fix d t assume dt: \<open>d division_of t \<and> t \<subseteq> {a..b}\<close>
    then have div: \<open>d division_of t\<close> and sub: \<open>t \<subseteq> {a..b}\<close> by auto
    have \<open>(\<Sum>k\<in>d. norm (integral {a..Sup k} f - integral {a..Inf k} f))
        = (\<Sum>k\<in>d. norm (integral k f))\<close>
    proof (rule sum.cong[OF refl])
      fix k assume kd: \<open>k \<in> d\<close>
      obtain c e where ke: \<open>k = {c..e}\<close> \<open>c \<le> e\<close>
        using division_ofD(4)[OF div kd] unfolding box_real
        by (metis atLeastatMost_empty_iff2 division_ofD(3) dt kd)
      have ksub: \<open>k \<subseteq> {a..b}\<close> using division_ofD(2)[OF div kd] sub by auto
      then have ce_sub: \<open>a \<le> c\<close> \<open>e \<le> b\<close> using ke by auto
      have \<open>Inf k = c\<close> \<open>Sup k = e\<close> using ke by auto
      have fint_ac: \<open>f integrable_on {a..c}\<close>
        using integrable_on_subinterval[OF int] ce_sub \<open>c \<le> e\<close> by auto
      have fint_ce: \<open>f integrable_on {c..e}\<close>
        using integrable_on_subinterval[OF int] ce_sub ke by auto
      have fint_ae: \<open>f integrable_on {a..e}\<close>
        using integrable_on_subinterval[OF int] ce_sub by auto
      have \<open>integral {a..e} f = integral {a..c} f + integral {c..e} f\<close>
        by (simp add: Henstock_Kurzweil_Integration.integral_combine ce_sub(1) fint_ae ke(2))
      then have \<open>integral {a..e} f - integral {a..c} f = integral {c..e} f\<close>
        by simp
      then show \<open>norm (integral {a..Sup k} f - integral {a..Inf k} f) = norm (integral k f)\<close>
        using \<open>Inf k = c\<close> \<open>Sup k = e\<close> ke by auto
    qed
    also have \<open>\<dots> \<le> (\<Sum>k\<in>d. integral k (\<lambda>x. norm (f x)))\<close>
    proof (rule sum_mono)
      fix k assume \<open>k \<in> d\<close>
      obtain c e where ke: \<open>k = {c..e}\<close> \<open>c \<le> e\<close>
        using division_ofD(4)[OF div \<open>k \<in> d\<close>] unfolding box_real
        by (metis atLeastatMost_empty_iff2 division_ofD(3) dt \<open>k \<in> d\<close>)
      have ksub: \<open>k \<subseteq> {a..b}\<close> using division_ofD(2)[OF div \<open>k \<in> d\<close>] sub by auto
      have fint: \<open>f integrable_on k\<close>
        using integrable_on_subinterval[OF int] ksub ke(1) by blast
      show \<open>norm (integral k f) \<le> integral k (\<lambda>x. norm (f x))\<close>
        using Henstock_Kurzweil_Integration.integral_norm_bound_integral fint
              integrable_on_subinterval ke(1) ksub nint by blast
    qed
    also have \<open>\<dots> \<le> integral t (\<lambda>x. norm (f x))\<close>
      by (metis dt integrable_on_subdivision integral_combine_division_topdown landau_omega.R_refl
      nint)
    also have \<open>\<dots> \<le> integral {a..b} (\<lambda>x. norm (f x))\<close>
      by (metis dt integrable_on_subdivision integral_subset_le nint norm_ge_zero)
    finally show \<open>(\<Sum>k\<in>d. norm (integral {a..Sup k} f - integral {a..Inf k} f))
        \<le> integral {a..b} (\<lambda>x. norm (f x))\<close> .
  qed
  show ?R using int bv by blast
next
  assume R: ?R
  then have int: \<open>f integrable_on {a..b}\<close>
    and bv: \<open>has_bounded_variation_on (\<lambda>t. integral {a..t} f) {a..b}\<close>
    by auto
 then obtain B where B: \<open>\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> {a..b} \<Longrightarrow>
          (\<Sum>k\<in>d. norm (integral {a..Sup k} f - integral {a..Inf k} f)) \<le> B\<close>
   unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def by meson
  show ?L
  proof (rule bounded_variation_absolutely_integrable_real_interval[OF int])
    fix d assume ddiv: \<open>d division_of {a..b}\<close>
    have \<open>(\<Sum>k\<in>d. norm (integral k f))
        = (\<Sum>k\<in>d. norm (integral {a..Sup k} f - integral {a..Inf k} f))\<close>
    proof (rule sum.cong[OF refl])
      fix k assume kd: \<open>k \<in> d\<close>
      obtain c e where ke: \<open>k = {c..e}\<close> \<open>c \<le> e\<close>
        using division_ofD(4)[OF ddiv kd] unfolding box_real
        by (metis atLeastatMost_empty_iff2 division_ofD(3) ddiv kd)
      have ksub: \<open>k \<subseteq> {a..b}\<close> using division_ofD(2)[OF ddiv kd] by auto
      then have ce_sub: \<open>a \<le> c\<close> \<open>e \<le> b\<close> using ke by auto
      have \<open>Inf k = c\<close> \<open>Sup k = e\<close> using ke by auto
      have fint_ac: \<open>f integrable_on {a..c}\<close>
        using integrable_on_subinterval[OF int] ce_sub \<open>c \<le> e\<close> by auto
      have fint_ce: \<open>f integrable_on {c..e}\<close>
        using integrable_on_subinterval[OF int] ce_sub ke by auto
      have fint_ae: \<open>f integrable_on {a..e}\<close>
        using integrable_on_subinterval[OF int] ce_sub by auto
      have \<open>integral {a..e} f = integral {a..c} f + integral {c..e} f\<close>
        by (simp add: Henstock_Kurzweil_Integration.integral_combine ce_sub(1) fint_ae ke(2))
      then have \<open>integral {a..e} f - integral {a..c} f = integral {c..e} f\<close>
        by simp
      then show \<open>norm (integral k f) = norm (integral {a..Sup k} f - integral {a..Inf k} f)\<close>
        using \<open>Inf k = c\<close> \<open>Sup k = e\<close> ke by auto
    qed
    also have \<open>\<dots> \<le> B\<close> using B[OF ddiv] by auto
    finally show \<open>(\<Sum>k\<in>d. norm (integral k f)) \<le> B\<close> .
  qed
qed

section \<open>Basic properties\<close>

lemma rectifiable_path_imp_path:
  "rectifiable_path g \<Longrightarrow> path g"
  unfolding rectifiable_path_def by simp

lemma path_length_pos_le:
  "rectifiable_path g \<Longrightarrow> 0 \<le> path_length g"
  unfolding rectifiable_path_def path_length_def
  by (auto intro: vector_variation_pos_le)

lemma path_length_eq_0:
  "rectifiable_path g \<Longrightarrow>
    (path_length g = 0 \<longleftrightarrow> (\<exists>c. \<forall>t \<in> {0..1}. g t = c))"
  unfolding rectifiable_path_def path_length_def
  by (rule vector_variation_const_eq) auto

lemma simple_path_length_pos_lt:
  "rectifiable_path g \<Longrightarrow> simple_path g \<Longrightarrow> 0 < path_length g"
 proof -
  assume rect: "rectifiable_path g" and sp: "simple_path g"
  have "path_length g \<noteq> 0"
  proof
    assume "path_length g = 0"
    then obtain c where c: "\<And>t. t \<in> {0..1} \<Longrightarrow> g t = c"
      using path_length_eq_0[OF rect] by auto
    hence "g (1/4) = g (3/4)" by auto
    moreover from sp have "inj_on g {0<..<1}" by (rule simple_path_inj_on)
    ultimately have "(1/4::real) = 3/4"
      by (auto dest: inj_onD)
    thus False by simp
  qed
  with path_length_pos_le[OF rect] show "0 < path_length g"
    by linarith
 qed

section \<open>Invariance under transformations\<close>

lemma rectifiable_path_translation_eq:
  "rectifiable_path ((\<lambda>x. a + x) \<circ> g) \<longleftrightarrow> rectifiable_path g"
proof -
  have "path g"
    if "path (\<lambda>x. a + g x)"
      and "has_bounded_variation_on (\<lambda>x. a + g x) {0..1}"
    using that path_translation_eq[of a g] by (simp add: o_def)
  moreover have "has_bounded_variation_on g {0..1}"
    if "path (\<lambda>x. a + g x)"
      and "has_bounded_variation_on (\<lambda>x. a + g x) {0..1}"
  proof -
    have "has_bounded_variation_on (\<lambda>x. a + g x + (- a)) {0..1}"
      using that(2) has_bounded_variation_on_const[of "-a" "{0..1}"]
      by (rule has_bounded_variation_on_add)
    then show ?thesis by simp
  qed
  moreover have "path (\<lambda>x. a + g x)"
    if "path g"
      and "has_bounded_variation_on g {0..1}"
    using that path_translation_eq[of a g] by (simp add: o_def)
  moreover have "has_bounded_variation_on (\<lambda>x. a + g x) {0..1}"
    if "path g"
      and "has_bounded_variation_on g {0..1}"
    using that(2) has_bounded_variation_on_const[of a "{0..1}"]
    by (auto intro: has_bounded_variation_on_add)
  ultimately show ?thesis
    by (auto simp: o_def rectifiable_path_def)
qed

lemma path_length_translation:
  "path_length ((\<lambda>x. a + x) \<circ> g) = path_length g"
  unfolding path_length_def vector_variation_def comp_def
  by (simp add: algebra_simps)

lemma has_bounded_variation_on_linear_image:
  assumes "linear f" "has_bounded_variation_on g {0..1}"
  shows "has_bounded_variation_on (f \<circ> g) {0..1}"
proof -
  have bl: "bounded_linear f" using assms(1) linear_conv_bounded_linear by auto
  have bound: "\<And>d. d division_of {0..1} \<Longrightarrow>
    (\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k)))
    \<le> onorm f * vector_variation {0..1} g"
  proof -
    fix d :: "real set set" assume div: "d division_of {0..1}"
    have "(\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k)))
      = (\<Sum>k\<in>d. norm (f (g (Sup k) - g (Inf k))))" 
      using assms(1) by (simp add: o_def linear_diff)
    also have "\<dots> \<le> (\<Sum>k\<in>d. onorm f * norm (g (Sup k) - g (Inf k)))" 
      by (intro sum_mono onorm[OF bl])
    also have "\<dots> = onorm f * (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))" 
      by (simp add: sum_distrib_left)
    also have "\<dots> \<le> onorm f * vector_variation {0..1} g" 
      by (intro mult_left_mono has_bounded_variation_works(1)[OF assms(2) div order_refl]
          onorm_pos_le[OF bl])
    finally show "(\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k)))
      \<le> onorm f * vector_variation {0..1} g" .
  qed
  then show ?thesis
    unfolding has_bounded_variation_on_interval by blast
qed

lemma rectifiable_path_linear_image_eq:
  assumes "linear f" "inj f"
  shows "rectifiable_path (f \<circ> g) \<longleftrightarrow> rectifiable_path g"
proof
  assume "rectifiable_path g"
  then show "rectifiable_path (f \<circ> g)"
    unfolding rectifiable_path_def
    using path_linear_image_eq[OF assms] has_bounded_variation_on_linear_image[OF assms(1)]
    by auto
next
  assume fg: "rectifiable_path (f \<circ> g)"
  have invf: "has_bounded_variation_on g {0..1}"
  proof -
    obtain B where "B > 0" and Bbound: "\<And>x. B * norm x \<le> norm (f x)"
      using linear_inj_bounded_below_pos[OF assms(1) assms(2)] by auto
    have bv_fg: "has_bounded_variation_on (f \<circ> g) {0..1}"
      using fg unfolding rectifiable_path_def by auto
    show ?thesis unfolding has_bounded_variation_on_interval
    proof -
      obtain C where C: "\<And>d. d division_of {0..1} \<Longrightarrow>
        (\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k))) \<le> C"
        using bv_fg unfolding has_bounded_variation_on_interval by auto
      { fix d :: "real set set" assume div: "d division_of {0..1}"
        have "(\<Sum>k\<in>d. B * norm (g (Sup k) - g (Inf k)))
          \<le> (\<Sum>k\<in>d. norm (f (g (Sup k) - g (Inf k))))" 
          by (intro sum_mono Bbound)
        also have "\<dots> = (\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k)))"
          using assms(1) by (simp add: o_def real_vector.linear_diff)
        also have "\<dots> \<le> C" using C[OF div] .
        finally have "B * (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> C"
          by (simp add: sum_distrib_left)
        then have "(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> C / B"
          using \<open>B > 0\<close> by (simp add: field_simps) }
      then show "\<exists>B. \<forall>d. d division_of {0..1} \<longrightarrow>
        (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> B" by blast
    qed
  qed
  moreover have "path g"
    using fg path_linear_image_eq[OF assms(1) assms(2)] unfolding rectifiable_path_def by auto
  ultimately show "rectifiable_path g"
    unfolding rectifiable_path_def by auto
qed


lemma path_length_linear_image:
  assumes "linear f" "\<And>x. norm (f x) = norm x"
  shows "path_length (f \<circ> g) = path_length g"
proof -
  have eq: "\<And>k. norm (f (g (Sup k)) - f (g (Inf k))) = norm (g (Sup k) - g (Inf k))"
    by (metis assms(1) assms(2) real_vector.linear_diff)
  then show ?thesis
    unfolding path_length_def vector_variation_def set_variation_def comp_def by presburger
qed


lemma rectifiable_path_eq:
  assumes eq: "\<And>t. t \<in> {0..1} \<Longrightarrow> g t = h t"
    and rect: "rectifiable_path g"
  shows "rectifiable_path h"
proof -
  have "path h"
  proof -
    have "continuous_on {0..1} h = continuous_on {0..1} g"
      by (rule continuous_on_cong_simp[OF refl]) (use eq in \<open>simp add: simp_implies_def\<close>)
    then show ?thesis using rect unfolding rectifiable_path_def path_def by auto
  qed
  moreover have "has_bounded_variation_on h {0..1}"
  proof -
    from rect have bv: "has_bounded_variation_on g {0..1}"
      unfolding rectifiable_path_def by auto
    have sup_inf_in: "Sup k \<in> {0..1} \<and> Inf k \<in> {0..1}"
      if "d division_of {(0::real)..1}" "k \<in> d" for d k
    proof -
      from division_ofD(2)[OF that] have ks: "k \<subseteq> {0..1}" .
      from division_ofD(3)[OF that] have kne: "k \<noteq> {}" .
      from division_ofD(4)[OF that] obtain a b where kab: "k = cbox a b" by auto
      with kne have "a \<le> b" by auto
      then have "Sup k = b" "Inf k = a"
        using kab by (auto simp: cSup_atLeastAtMost cInf_atLeastAtMost)
      then show ?thesis using ks kab \<open>a \<le> b\<close> by auto
    qed
    have sums_eq: "(\<Sum>k\<in>d. norm (h (Sup k) - h (Inf k))) = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
      if "d division_of {(0::real)..1}" for d
      using sup_inf_in[OF that] by (intro sum.cong refl) (auto simp: eq)
    then show ?thesis
      using bv unfolding has_bounded_variation_on_interval by auto
  qed
  ultimately show ?thesis unfolding rectifiable_path_def by auto
qed

lemma path_length_eq:
  assumes eq: "\<And>t. t \<in> {0..1} \<Longrightarrow> g t = h t"
    and rect: "rectifiable_path g"
  shows "path_length g = path_length h"
proof -
  have sup_inf_in: "Sup k \<in> {0..1} \<and> Inf k \<in> {0..1}"
    if "d division_of t" "t \<subseteq> {(0::real)..1}" "k \<in> d" for d t k
  proof -
    from division_ofD(2)[OF that(1) that(3)] that(2) have ks: "k \<subseteq> {0..1}" by auto
    from division_ofD(3)[OF that(1) that(3)] have kne: "k \<noteq> {}" .
    from division_ofD(4)[OF that(1) that(3)] obtain a b where kab: "k = cbox a b" by auto
    with kne have "a \<le> b" by auto
    then have "Sup k = b" "Inf k = a"
      using kab by (auto simp: cSup_atLeastAtMost cInf_atLeastAtMost)
    then show ?thesis using ks kab \<open>a \<le> b\<close> by auto
  qed
  have sums_eq: "(\<Sum>k\<in>d. norm (h (Sup k) - h (Inf k))) = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
    if "d division_of t" "t \<subseteq> {(0::real)..1}" for d t
    using sup_inf_in[OF that] by (intro sum.cong refl) (auto simp: eq)
  have "{\<Sum>k\<in>d. norm (h (Sup k) - h (Inf k)) |d. \<exists>t. d division_of t \<and> t \<subseteq> {0..1}}
      = {\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)) |d. \<exists>t. d division_of t \<and> t \<subseteq> {0..1}}"
    by (metis (lifting) sums_eq)
  then show ?thesis
    unfolding path_length_def vector_variation_def set_variation_def by auto
qed


lemma path_length_reversepath:
  "rectifiable_path g \<Longrightarrow> path_length (reversepath g) = path_length g"
  unfolding path_length_def reversepath_def comp_def[symmetric]
  using vector_variation_reflect[of 0 1 g 1] by simp

lemma rectifiable_path_subpath:
  "\<lbrakk>rectifiable_path g; u \<in> {0..1}; v \<in> {0..1}\<rbrakk> \<Longrightarrow>
    rectifiable_path (subpath u v g)"
  unfolding rectifiable_path_def subpath_def
proof (intro conjI)
  assume rect: "path g \<and> has_bounded_variation_on g {0..1}" and u: "u \<in> {0..1}" and v: "v \<in> {0..1}"
  show "path (\<lambda>x. g ((v - u) * x + u))"
    using rect u v path_subpath unfolding subpath_def by auto
  have bv: "has_bounded_variation_on g {0..1}" using rect by auto
  have seg: "closed_segment u v \<subseteq> {0..1}" using u v
    by (auto simp: closed_segment_eq_real_ivl split: if_splits)
  show "has_bounded_variation_on (\<lambda>x. g ((v - u) * x + u)) {0..1}"
  proof (cases "u \<le> v")
    case True
    have mono: "mono_on {0..1} (\<lambda>x. (v - u) * x + u)"
      using True by (auto intro!: mono_onI mult_left_mono)
    have "has_bounded_variation_on g {u..v}"
      using bv seg True by (auto simp: closed_segment_eq_real_ivl
        intro: has_bounded_variation_on_subset)
    then show ?thesis
      using has_bounded_variation_compose_monotone(1)[of g "\<lambda>x. (v-u)*x+u" 0 1]
        mono True by (simp add: comp_def)
  next
    case False
    then have vu: "v \<le> u" by auto
    have mono: "mono_on {0..1} (\<lambda>x. (u - v) * x + v)"
      using vu by (auto intro!: mono_onI mult_left_mono)
    have bvvu: "has_bounded_variation_on g {v..u}"
      using bv seg vu
      by (auto simp: closed_segment_eq_real_ivl split: if_splits
        intro: has_bounded_variation_on_subset)
    have "(\<lambda>x. g ((v - u) * x + u)) = (\<lambda>x. g ((u - v) * (1 - x) + v))"
      by (auto simp: algebra_simps)
    also have "\<dots> = (g \<circ> (\<lambda>x. (u-v)*x + v)) \<circ> (\<lambda>x. 1 - x)"
      by (auto simp: comp_def)
    finally have eq: "(\<lambda>x. g ((v - u) * x + u)) = (g \<circ> (\<lambda>x. (u-v)*x + v)) \<circ> (-) 1"
      by (auto simp: comp_def)
    have "has_bounded_variation_on (g \<circ> (\<lambda>x. (u-v)*x + v)) {0..1}"
      using has_bounded_variation_compose_monotone(1)[of g "\<lambda>x. (u-v)*x+v" 0 1]
        mono bvvu by (simp add: comp_def)
    then have "has_bounded_variation_on (g \<circ> (\<lambda>x. (u-v)*x + v)) {1 - 1..1 - 0}"
      by simp
    then have "has_bounded_variation_on ((g \<circ> (\<lambda>x. (u-v)*x + v)) \<circ> (-) 1) {0..1}"
      by (rule has_bounded_variation_on_reflect)
    then show ?thesis
      using eq by simp
  qed
qed

lemma division_of_affine_image:
  fixes c d :: real
  assumes cpos: "c > 0" and div: "D division_of T" and sub: "T \<subseteq> {a..b}"
  shows "((`) (\<lambda>x. c * x + d)) ` D division_of ((\<lambda>x. c * x + d) ` T)"
    and "(\<lambda>x. c * x + d) ` T \<subseteq> {c*a+d..c*b+d}"
proof -
  let ?\<phi> = "\<lambda>x::real. c * x + d"
  have inj: "inj ?\<phi>" using cpos by (intro injI) simp
  have mono: "mono ?\<phi>" using cpos by (intro monoI) auto
  show sub': "?\<phi> ` T \<subseteq> {c*a+d..c*b+d}"
    using sub cpos by (auto simp: mult_left_mono)
  show "((`) ?\<phi>) ` D division_of (?\<phi> ` T)"
    unfolding division_of_def
  proof (intro conjI ballI impI)
    show "finite (((`) ?\<phi>) ` D)"
      using division_ofD(1)[OF div] by auto
  next
    fix K assume "K \<in> ((`) ?\<phi>) ` D"
    then obtain K0 where K0: "K0 \<in> D" "K = ?\<phi> ` K0" by auto
    from division_ofD(2)[OF div K0(1)] have K0sub: "K0 \<subseteq> T" .
    from division_ofD(3)[OF div K0(1)] have K0ne: "K0 \<noteq> {}" .
    then show "K \<subseteq> ?\<phi> ` T" "K \<noteq> {}" using K0(2) K0sub by auto
    from division_ofD(4)[OF div K0(1)] obtain \<alpha> \<beta> where ab: "K0 = cbox \<alpha> \<beta>" by auto
    then have "K0 = {\<alpha>..\<beta>}" by auto
    with K0ne have \<alpha>\<beta>: "\<alpha> \<le> \<beta>" by auto
    have "K = ?\<phi> ` {\<alpha>..\<beta>}" using K0(2) \<open>K0 = {\<alpha>..\<beta>}\<close> by auto
    also have "\<dots> = {c*\<alpha>+d..c*\<beta>+d}"
    proof -
      have "?\<phi> ` {\<alpha>..\<beta>} = {y. \<exists>x. \<alpha> \<le> x \<and> x \<le> \<beta> \<and> y = c*x+d}"
        by (auto simp: image_def)
      also have "\<dots> = {c*\<alpha>+d..c*\<beta>+d}"
      proof (auto simp: mult_left_mono[OF _ less_imp_le[OF cpos]])
        fix y assume "c * \<alpha> + d \<le> y" "y \<le> c * \<beta> + d"
        then have "\<alpha> \<le> (y - d) / c" "((y - d) / c) \<le> \<beta>"
          using cpos by (auto simp: field_simps)
        moreover have "y = c * ((y - d) / c) + d" using cpos by auto
        ultimately show "\<exists>x\<ge>\<alpha>. x \<le> \<beta> \<and> y = c * x + d" by auto
      qed
      finally show ?thesis .
    qed
    finally show "\<exists>\<alpha> \<beta>. K = cbox \<alpha> \<beta>" by (auto simp: cbox_interval)
  next
    fix K1 K2
    assume "K1 \<in> ((`) ?\<phi>) ` D" "K2 \<in> ((`) ?\<phi>) ` D" "K1 \<noteq> K2"
    then obtain K1' K2' where K1': "K1' \<in> D" "K1 = ?\<phi> ` K1'"
      and K2': "K2' \<in> D" "K2 = ?\<phi> ` K2'" by auto
    have "K1' \<noteq> K2'" using \<open>K1 \<noteq> K2\<close> K1'(2) K2'(2) inj_image_eq_iff[OF inj] by auto
    then have disj: "interior K1' \<inter> interior K2' = {}"
      using division_ofD(5)[OF div K1'(1) K2'(1)] by auto
    show "interior K1 \<inter> interior K2 = {}"
    proof (rule ccontr)
      assume "interior K1 \<inter> interior K2 \<noteq> {}"
      then obtain y where "y \<in> interior K1" "y \<in> interior K2" by auto
      from division_ofD(4)[OF div K1'(1)] obtain a1 b1 where "K1' = cbox a1 b1" by auto
      from division_ofD(4)[OF div K2'(1)] obtain a2 b2 where "K2' = cbox a2 b2" by auto
      then have K1eq: "K1' = {a1..b1}" and K2eq: "K2' = {a2..b2}"
        using \<open>K1' = cbox a1 b1\<close> by auto
      from division_ofD(3)[OF div K1'(1)] K1eq have "a1 \<le> b1" by (auto split: if_splits)
      from division_ofD(3)[OF div K2'(1)] K2eq have "a2 \<le> b2" by (auto split: if_splits)
      have K1img: "K1 = {c*a1+d..c*b1+d}" 
      proof -
        have "K1 = ?\<phi> ` {a1..b1}" using K1'(2) K1eq by auto
        also have "\<dots> = {c*a1+d..c*b1+d}"
        proof safe
          fix x assume "x \<in> {a1..b1}"
          then show "?\<phi> x \<in> {c*a1+d..c*b1+d}" using cpos
            by (auto intro: mult_left_mono)
        next
          fix y assume "y \<in> {c*a1+d..c*b1+d}"
          then have mem: "(y-d)/c \<in> {a1..b1}" using cpos by (auto simp: field_simps)
          moreover have "?\<phi> ((y-d)/c) = y" using cpos by (simp add: field_simps)
          ultimately show "y \<in> ?\<phi> ` {a1..b1}" by force
        qed
        finally show ?thesis .
      qed
      have K2img: "K2 = {c*a2+d..c*b2+d}"
      proof -
        have "K2 = ?\<phi> ` {a2..b2}" using K2'(2) K2eq by auto
        also have "\<dots> = {c*a2+d..c*b2+d}"
        proof safe
          fix x assume "x \<in> {a2..b2}"
          then show "?\<phi> x \<in> {c*a2+d..c*b2+d}" using cpos
            by (auto intro: mult_left_mono)
        next
          fix y assume "y \<in> {c*a2+d..c*b2+d}"
          then have "(y-d)/c \<in> {a2..b2}" using cpos by (auto simp: field_simps)
          moreover have "?\<phi> ((y-d)/c) = y" using cpos by (simp add: field_simps)
          ultimately show "y \<in> ?\<phi> ` {a2..b2}" by force
        qed
        finally show ?thesis .
      qed
      from \<open>y \<in> interior K1\<close> K1img have "c*a1+d < y" "y < c*b1+d"
        using \<open>a1 \<le> b1\<close> interior_atLeastAtMost_real by auto
      then have "a1 < (y-d)/c" "(y-d)/c < b1" using cpos by (auto simp: field_simps)
      then have "(y-d)/c \<in> interior K1'"
        using K1eq interior_atLeastAtMost_real by auto
      from \<open>y \<in> interior K2\<close> K2img have "c*a2+d < y" "y < c*b2+d"
        using \<open>a2 \<le> b2\<close> interior_atLeastAtMost_real by auto
      then have "a2 < (y-d)/c" "(y-d)/c < b2" using cpos by (auto simp: field_simps)
      then have "(y-d)/c \<in> interior K2'"
        using K2eq interior_atLeastAtMost_real by auto
      with \<open>(y-d)/c \<in> interior K1'\<close> disj show False by auto
    qed
  next
    have "\<Union> (((`) ?\<phi>) ` D) = ?\<phi> ` (\<Union> D)" by auto
    also have "\<Union> D = T" using division_ofD(6)[OF div] by auto
    finally show "\<Union> (((`) ?\<phi>) ` D) = ?\<phi> ` T" .
  qed
qed

lemma vector_variation_affine_eq:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space" and c d :: real
  assumes "c > 0" "a \<le> b"
  shows "vector_variation {a..b} (g \<circ> (\<lambda>x. c * x + d)) = vector_variation {c*a+d..c*b+d} g"
proof -
  let ?\<phi> = "\<lambda>x::real. c * x + d"
  let ?\<psi> = "\<lambda>x::real. (x - d) / c"
  have cne: "c \<noteq> 0" using assms(1) by auto
  have cpos: "0 < c" using assms(1) .
  have inj_\<phi>: "inj ?\<phi>" using cne by (intro injI) simp
  have \<phi>\<psi>: "\<And>x. ?\<phi> (?\<psi> x) = x" using cne by (simp add: field_simps)
  have \<psi>\<phi>: "\<And>x. ?\<psi> (?\<phi> x) = x" using cne by (simp add: field_simps)
  have ab': "c*a+d \<le> c*b+d" using assms by (auto intro: mult_left_mono)
  have img_ivl: "\<And>\<alpha> \<beta>. \<alpha> \<le> \<beta> \<Longrightarrow> ?\<phi> ` {\<alpha>..\<beta>} = {c*\<alpha>+d..c*\<beta>+d}"
  proof safe
    fix \<alpha> \<beta> x :: real assume "\<alpha> \<le> \<beta>" "x \<in> {\<alpha>..\<beta>}"
    then show "?\<phi> x \<in> {c*\<alpha>+d..c*\<beta>+d}" using cpos by (auto intro: mult_left_mono)
  next
    fix \<alpha> \<beta> y :: real assume "\<alpha> \<le> \<beta>" "y \<in> {c*\<alpha>+d..c*\<beta>+d}"
    then have "(y-d)/c \<in> {\<alpha>..\<beta>}" using cpos by (auto simp: field_simps)
    moreover have "?\<phi> ((y-d)/c) = y" using cne by (simp add: field_simps)
    ultimately show "y \<in> ?\<phi> ` {\<alpha>..\<beta>}" by force
  qed
  \<comment> \<open>Key: the variation sums over divisions of any T equal those over \<phi>(T)\<close>
  have sum_transform: "(\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
    = (\<Sum>k\<in>((`) ?\<phi>) ` D. norm (g (Sup k) - g (Inf k)))"
    if "D division_of T" for D :: "real set set" and T :: "real set"
  proof -
    have div: "D division_of T" using that .
    have inj_on_img: "inj_on ((`) ?\<phi>) D"
      using inj_image_eq_iff[OF inj_\<phi>] by (auto intro!: inj_onI)
    have "(\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>D. norm (g (?\<phi> (Sup k)) - g (?\<phi> (Inf k))))" by (simp add: o_def)
    also have "\<dots> = (\<Sum>k\<in>D. norm (g (Sup (?\<phi> ` k)) - g (Inf (?\<phi> ` k))))"
    proof (intro sum.cong refl arg_cong[where f=norm] arg_cong2[where f="(-)"])
      fix k assume "k \<in> D"
      from division_ofD(4)[OF div this] obtain \<alpha> \<beta> where kab: "k = cbox \<alpha> \<beta>" by auto
      from division_ofD(3)[OF div \<open>k \<in> D\<close>] have kne: "k \<noteq> {}" .
      with kab have le: "\<alpha> \<le> \<beta>" by auto
      have k_ivl: "k = {\<alpha>..\<beta>}" using kab by auto
      have img: "?\<phi> ` k = {c*\<alpha>+d..c*\<beta>+d}" using img_ivl[OF le] k_ivl by simp
      have le': "c*\<alpha>+d \<le> c*\<beta>+d" using le cpos by (auto intro: mult_left_mono)
      show "g (?\<phi> (Sup k)) = g (Sup (?\<phi> ` k))"
        using k_ivl le img le' by (simp add: cSup_atLeastAtMost)
      show "g (?\<phi> (Inf k)) = g (Inf (?\<phi> ` k))"
        using k_ivl le img le' by (simp add: cInf_atLeastAtMost)
    qed
    also have "\<dots> = (\<Sum>k\<in>((`) ?\<phi>) ` D. norm (g (Sup k) - g (Inf k)))"
      by (metis (no_types, lifting) inj_on_img sum.reindex_cong)
    finally show "(\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>((`) ?\<phi>) ` D. norm (g (Sup k) - g (Inf k)))" .
  qed
  \<comment> \<open>Now show the Sup sets in the vector_variation definition are equal\<close>
  have sets_eq: "{\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)) |D.
      \<exists>T. D division_of T \<and> T \<subseteq> {a..b}}
    = {\<Sum>k\<in>D. norm (g (Sup k) - g (Inf k)) |D.
      \<exists>T. D division_of T \<and> T \<subseteq> {c*a+d..c*b+d}}"
  proof safe
    fix D T assume div: "D division_of T" and sub: "T \<subseteq> {a..b}"
    let ?D' = "((`) ?\<phi>) ` D"
    have div': "?D' division_of (?\<phi> ` T)"
      using division_of_affine_image(1)[OF cpos div sub] .
    have sub': "?\<phi> ` T \<subseteq> {c*a+d..c*b+d}"
      using division_of_affine_image(2)[OF cpos div sub] .
    have sum_eq: "(\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>?D'. norm (g (Sup k) - g (Inf k)))"
      using sum_transform[OF div] .
    show "\<exists>Da. (\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>Da. norm (g (Sup k) - g (Inf k)))
      \<and> (\<exists>T. Da division_of T \<and> T \<subseteq> {c*a+d..c*b+d})"
      using sum_eq div' sub' by blast
  next
    fix D T assume div: "D division_of T" and sub: "T \<subseteq> {c*a+d..c*b+d}"
    \<comment> \<open>Map back via the inverse affine map (1/c)*x + (-d/c)\<close>
    let ?c' = "1/c" and ?d' = "-d/c"
    have cpos': "?c' > 0" using cpos by auto
    have div': "((`) (\<lambda>x. ?c' * x + ?d')) ` D division_of ((\<lambda>x. ?c' * x + ?d') ` T)"
      using division_of_affine_image(1)[OF cpos' div sub] .
    have sub': "(\<lambda>x. ?c' * x + ?d') ` T \<subseteq> {?c'*(c*a+d)+?d'..?c'*(c*b+d)+?d'}"
      using division_of_affine_image(2)[OF cpos' div sub] .
    have endpoints: "?c'*(c*a+d)+?d' = a" "?c'*(c*b+d)+?d' = b"
      using cne by (auto simp: field_simps)
    \<comment> \<open>The inverse map equals \<psi>\<close>
    have inv_eq: "(\<lambda>x::real. ?c' * x + ?d') = ?\<psi>"
      by (rule ext) (simp add: diff_divide_distrib)
    have div'': "((`) ?\<psi>) ` D division_of (?\<psi> ` T)"
      using div' unfolding inv_eq .
    have sub'': "?\<psi> ` T \<subseteq> {a..b}"
    proof -
      have "(\<lambda>x::real. ?c' * x + ?d') ` T \<subseteq> {a..b}"
        using sub' endpoints by auto
      then show ?thesis unfolding inv_eq .
    qed
    \<comment> \<open>Show the sum over D equals the sum over \<psi>-image composed with \<phi>\<close>
    have sum_eq: "(\<Sum>k\<in>((`) ?\<psi>) ` D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>((`) ?\<phi>) ` ((`) ?\<psi>) ` D. norm (g (Sup k) - g (Inf k)))"
      using sum_transform[OF div''] .
    have \<phi>\<psi>_img: "?\<phi> ` ?\<psi> ` S = S" for S :: "real set"
    proof -
      have "?\<phi> ` ?\<psi> ` S = (?\<phi> \<circ> ?\<psi>) ` S" by (simp add: image_image)
      also have "(?\<phi> \<circ> ?\<psi>) = id"
        using cne by (auto simp: o_def field_simps)
      also have "id ` S = S" by simp
      finally show ?thesis .
    qed
    have img_back: "((`) ?\<phi>) ` ((`) ?\<psi>) ` D = D"
    proof -
      have "((`) ?\<phi>) ` ((`) ?\<psi>) ` D = ((`) ?\<phi> \<circ> (`) ?\<psi>) ` D"
        by (simp add: image_comp)
      also have "((`) ?\<phi> \<circ> (`) ?\<psi>) = id"
        by (rule ext) (simp add: \<phi>\<psi>_img)
      also have "id ` D = D" by simp
      finally show ?thesis .
    qed
    have sum_eq': "(\<Sum>k\<in>((`) ?\<psi>) ` D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>D. norm (g (Sup k) - g (Inf k)))"
      using sum_eq img_back by simp
    show "\<exists>E. (\<Sum>k\<in>D. norm (g (Sup k) - g (Inf k))) = (\<Sum>k\<in>E. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      \<and> (\<exists>T. E division_of T \<and> T \<subseteq> {a..b})"
      using sum_eq' div'' sub'' by (metis (no_types, lifting))
  qed
  show ?thesis
    unfolding vector_variation_def set_variation_def using sets_eq by auto
qed

lemma path_length_subpath_eq:
  assumes "s \<in> {0..1}" "t \<in> {0..1}"
    and rect: "rectifiable_path g"
  shows "path_length (subpath s t g) = vector_variation (closed_segment s t) g"
  using assms
proof (cases "s \<le> t")
  case True
  then have cs: "closed_segment s t = {s..t}"
    by (simp add: closed_segment_eq_real_ivl)
  show ?thesis
  proof (cases "s = t")
    case True
    then show ?thesis
    proof -
      from \<open>s = t\<close> have cs': "closed_segment s t = {t..t}" using cs by simp
      have "path_length (subpath t t g) = 0"
        by (metis \<open>t \<in> {0..1}\<close> eq_iff_diff_eq_0 mult_zero_left path_length_eq_0 rect
            rectifiable_path_subpath subpath_def)
      moreover have "vector_variation {t..t} g = 0"
        by (rule vector_variation_on_null) (simp add: content_real_eq_0)
      ultimately show ?thesis using \<open>s = t\<close> cs' by simp
    qed
  next
    case False
    with \<open>s \<le> t\<close> have "s < t" by auto
    then have "t - s > 0" by auto
    have "path_length (subpath s t g) = vector_variation {0..1} (g \<circ> (\<lambda>x. (t-s)*x + s))"
      unfolding path_length_def subpath_def by (simp add: comp_def)
    also have "\<dots> = vector_variation {(t-s)*0+s..(t-s)*1+s} g"
      using vector_variation_affine_eq[OF \<open>t - s > 0\<close> zero_le_one, where d=s and g=g] by simp
    also have "\<dots> = vector_variation {s..t} g"
      by simp
    finally show ?thesis by (simp add: cs)
  qed
next
  case False
  then have ts: "t < s" by auto
  then have cs: "closed_segment s t = {t..s}"
    by (simp add: closed_segment_eq_real_ivl)
  have "s - t > 0" using ts by auto
  have "path_length (subpath s t g) = vector_variation {0..1} (\<lambda>x. g ((t - s) * x + s))"
    unfolding path_length_def subpath_def by simp
  also have "\<dots> = vector_variation {0..1} (g \<circ> (\<lambda>x. (s - t) * x + t) \<circ> (-) 1)"
    by (simp add: comp_def algebra_simps)
  finally
   show ?thesis
    using vector_variation_affine_eq[OF \<open>s - t > 0\<close> zero_le_one, where d=t and g=g]
    by (simp add: cs vector_variation_reflect)
qed

lemma vector_variation_cong:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "vector_variation s f = vector_variation s g"
proof -
  have sum_eq: "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
    if "d division_of t" "t \<subseteq> s" for d t
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> d"
    then have "k \<subseteq> t" "k \<noteq> {}" "\<exists>a b. k = cbox a b"
      using division_ofD(2,3,4)[OF that(1)] by auto
    then obtain a b where "k = cbox a b" "a \<le> b" by fastforce
    then have "Inf k \<in> k" "Sup k \<in> k" by auto
    then have "Inf k \<in> s" "Sup k \<in> s" using \<open>k \<subseteq> t\<close> that(2) by auto
    then show "norm (f (Sup k) - f (Inf k)) = norm (g (Sup k) - g (Inf k))"
      using assms by auto
  qed
  have "{\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) |d. \<exists>t. d division_of t \<and> t \<subseteq> s}
      = {\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)) |d. \<exists>t. d division_of t \<and> t \<subseteq> s}"
    (is "?L = ?R")
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> ?L"
    then obtain d t where "x = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))" "d division_of t" "t \<subseteq> s"
      by auto
    then show "x \<in> ?R" using sum_eq by auto
  next
    fix x assume "x \<in> ?R"
    then obtain d t where "x = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))" "d division_of t" "t \<subseteq> s"
      by auto
    then show "x \<in> ?L" using sum_eq
      by (metis (mono_tags, lifting) mem_Collect_eq)
  qed
  then show ?thesis
    unfolding vector_variation_def set_variation_def by simp
qed

lemma has_bounded_variation_on_cong:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "has_bounded_variation_on f s \<longleftrightarrow> has_bounded_variation_on g s"
proof -
  have "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
  proof -
    fix d t assume dt: "d division_of t" "t \<subseteq> s"
    show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> d"
      then have "k \<subseteq> t" "k \<noteq> {}" "\<exists>a b. k = cbox a b"
        using division_ofD(2,3,4)[OF dt(1)] by auto
      then obtain a b where "k = cbox a b" "a \<le> b" by fastforce
      then have "Inf k \<in> k" "Sup k \<in> k" by auto
      then have "Inf k \<in> s" "Sup k \<in> s" using \<open>k \<subseteq> t\<close> dt(2) by auto
      then show "norm (f (Sup k) - f (Inf k)) = norm (g (Sup k) - g (Inf k))"
        using assms by auto
    qed
  qed
  then show ?thesis
    unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def by (metis (lifting))
qed

lemma has_bounded_variation_on_affine_iff:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space" and c d :: real
  assumes "c > 0" "a \<le> b"
  shows "has_bounded_variation_on (g \<circ> (\<lambda>x. c * x + d)) {a..b} \<longleftrightarrow>
    has_bounded_variation_on g {c*a+d..c*b+d}"
proof
  assume "has_bounded_variation_on g {c*a+d..c*b+d}"
  moreover have "mono_on {a..b} (\<lambda>x. c * x + d)"
    using assms(1) by (auto intro!: mono_onI mult_left_mono)
  ultimately show "has_bounded_variation_on (g \<circ> (\<lambda>x. c * x + d)) {a..b}"
    by (rule has_bounded_variation_compose_monotone(1))
next
  assume bv: "has_bounded_variation_on (g \<circ> (\<lambda>x. c * x + d)) {a..b}"
  let ?inv = "\<lambda>x. (x - d) / c"
  have inv_mono: "mono_on {c*a+d..c*b+d} ?inv"
    using assms(1) by (smt (verit, ccfv_SIG) divide_less_cancel monotone_on_def)
  have inv_a: "?inv (c*a+d) = a" and inv_b: "?inv (c*b+d) = b"
    using assms(1) by (auto simp: field_simps)
  have comp_eq: "(g \<circ> (\<lambda>x. c * x + d)) \<circ> ?inv = g"
    using assms(1) by (auto simp: comp_def field_simps)
  have "has_bounded_variation_on ((g \<circ> (\<lambda>x. c * x + d)) \<circ> ?inv) {c*a+d..c*b+d}"
    by (metis (lifting) bv has_bounded_variation_compose_monotone(1) inv_a inv_b
        inv_mono)
  then show "has_bounded_variation_on g {c*a+d..c*b+d}"
    by (simp add: comp_eq)
qed

lemma rectifiable_path_join:
  assumes "pathfinish g1 = pathstart g2"
  shows "rectifiable_path (g1 +++ g2) \<longleftrightarrow>
    rectifiable_path g1 \<and> rectifiable_path g2"
proof -
  have half: "(0::real) \<le> 1/2" "1/2 \<le> (1::real)" by auto
  \<comment> \<open>On {0..1/2}, the joinpath agrees with g1 \<circ> (\<lambda>x. 2*x)\<close>
  have eq1: "(g1 +++ g2) x = (g1 \<circ> (\<lambda>x. 2 * x)) x" if "x \<in> {0..1/2}" for x
    using that by (auto simp: joinpaths_def)
  \<comment> \<open>On {1/2..1}, the joinpath agrees with g2 \<circ> (\<lambda>x. 2*x - 1)\<close>
  have eq2: "(g1 +++ g2) x = (g2 \<circ> (\<lambda>x. 2 * x + (-1))) x" if "x \<in> {1/2..1}" for x
  proof -
    from that have "x = 1/2 \<or> x > 1/2" by auto
    then show ?thesis
    proof
      assume "x = 1/2"
      then show ?thesis
        using assms by (simp add: joinpaths_def mult.commute pathfinish_def pathstart_def)
    next
      assume "x > 1/2"
      then show ?thesis by (auto simp: joinpaths_def comp_def)
    qed
  qed
  \<comment> \<open>Bounded variation equivalences\<close>
  have bv1: "has_bounded_variation_on (g1 +++ g2) {0..1/2} \<longleftrightarrow>
    has_bounded_variation_on g1 {0..1}"
  proof -
    have "has_bounded_variation_on (g1 +++ g2) {0..1/2} \<longleftrightarrow>
      has_bounded_variation_on (g1 \<circ> (\<lambda>x. 2 * x)) {0..1/2}"
      by (rule has_bounded_variation_on_cong[OF eq1])
    also have "\<dots> \<longleftrightarrow> has_bounded_variation_on g1 {2*0+0..2*(1/2)+0}"
      using has_bounded_variation_on_affine_iff [of 2 0 \<open>1/2\<close> _ 0] by force
    also have "{2*0+(0::real)..2*(1/2)+0} = {0..1}" by auto
    finally show ?thesis .
  qed
  have bv2: "has_bounded_variation_on (g1 +++ g2) {1/2..1} \<longleftrightarrow>
    has_bounded_variation_on g2 {0..1}"
  proof -
    have "has_bounded_variation_on (g1 +++ g2) {1/2..1} \<longleftrightarrow>
      has_bounded_variation_on (g2 \<circ> (\<lambda>x. 2 * x + (-1))) {1/2..1}"
      by (rule has_bounded_variation_on_cong[OF eq2])
    also have "\<dots> \<longleftrightarrow> has_bounded_variation_on g2 {2*(1/2)+(-1)..2*1+(-1)}"
      by (rule has_bounded_variation_on_affine_iff) auto
    also have "{2*(1/2)+(-1::real)..2*1+(-1)} = {0..1}" by auto
    finally show ?thesis .
  qed
  show ?thesis
    unfolding rectifiable_path_def
    using path_join[OF assms]
      has_bounded_variation_on_combine[OF half(1) half(2), of "g1 +++ g2"]
      bv1 bv2
    by auto
qed

lemma path_length_join:
  assumes "rectifiable_path g1"
    and "rectifiable_path g2"
    and "pathfinish g1 = pathstart g2"
  shows "path_length (g1 +++ g2) = path_length g1 + path_length g2"
proof -
  have half: "(0::real) \<le> 1/2" "1/2 \<le> (1::real)" by auto
  have bvj: "has_bounded_variation_on (g1 +++ g2) {0..1}"
    using rectifiable_path_def assms rectifiable_path_join by blast
  \<comment> \<open>On {0..1/2}, the joinpath agrees with g1 \<circ> (\<lambda>x. 2*x)\<close>
  have eq1: "(g1 +++ g2) x = (g1 \<circ> (\<lambda>x. 2 * x)) x" if "x \<in> {0..1/2}" for x
    using that by (auto simp: joinpaths_def)
  \<comment> \<open>On {1/2..1}, the joinpath agrees with g2 \<circ> (\<lambda>x. 2*x - 1)\<close>
  have eq2: "(g1 +++ g2) x = (g2 \<circ> (\<lambda>x. 2 * x + (-1))) x" if "x \<in> {1/2..1}" for x
  proof -
    from that have "x = 1/2 \<or> x > 1/2" by auto
    then show ?thesis
    proof
      assume "x = 1/2"
      then show ?thesis
        using assms by (simp add: joinpaths_def mult.commute pathfinish_def pathstart_def)
    next
      assume "x > 1/2"
      then show ?thesis by (auto simp: joinpaths_def comp_def)
    qed
  qed
  \<comment> \<open>Variation on left half\<close>
  have vv1: "vector_variation {0..1/2} (g1 +++ g2) = path_length g1"
  proof -
    have "vector_variation {0..1/2} (g1 +++ g2) =
      vector_variation {0..1/2} (g1 \<circ> (\<lambda>x. 2 * x))"
      by (rule vector_variation_cong[OF eq1])
    also have "\<dots> = vector_variation {2*0+0..2*(1/2)+0} g1"
      using vector_variation_affine_eq
      by (metis (no_types, lifting) ext add.right_neutral half(1) zero_less_numeral)
    also have "{2*0+(0::real)..2*(1/2)+0} = {0..1}" by auto
    finally show ?thesis unfolding path_length_def .
  qed
  \<comment> \<open>Variation on right half\<close>
  have vv2: "vector_variation {1/2..1} (g1 +++ g2) = path_length g2"
  proof -
    have "vector_variation {1/2..1} (g1 +++ g2) =
      vector_variation {1/2..1} (g2 \<circ> (\<lambda>x. 2 * x + (-1)))"
      by (rule vector_variation_cong[OF eq2])
    also have "\<dots> = vector_variation {2*(1/2)+(-1)..2*1+(-1)} g2"
      by (rule vector_variation_affine_eq) auto
    also have "{2*(1/2)+(-1::real)..2*1+(-1)} = {0..1}" by auto
    finally show ?thesis unfolding path_length_def .
  qed
  \<comment> \<open>Combine\<close>
  show ?thesis
    unfolding path_length_def
    using vector_variation_combine[OF bvj, of "1/2"] half vv1 vv2
    unfolding path_length_def
    by auto
qed

section \<open>Shiftpath\<close>

lemma rectifiable_path_shiftpath:
  assumes "rectifiable_path g"
    and "pathfinish g = pathstart g"
    and "t \<in> {0..1}"
  shows "rectifiable_path (shiftpath t g)"
proof -
  note rg = assms(1) and loop = assms(2) and t01 = assms(3)
  from rg have pg: "path g" and bvg: "has_bounded_variation_on g {0..1}"
    unfolding rectifiable_path_def by auto
  from t01 have t0: "0 \<le> t" and t1: "t \<le> 1" and mt: "0 \<le> 1 - t" and mt1: "1 - t \<le> 1" by auto
  \<comment> \<open>On {0..1-t}, shiftpath t g agrees with g \<circ> (\<lambda>x. x + t)\<close>
  have eq1: "shiftpath t g x = (g \<circ> (\<lambda>x. 1 * x + t)) x" if "x \<in> {0..1-t}" for x
    by (metis add.commute atLeastAtMost_iff comp_def mult_1 shiftpath_alt_def that)
  \<comment> \<open>On {1-t..1}, shiftpath t g agrees with g \<circ> (\<lambda>x. x + (t-1))\<close>
  have eq2: "shiftpath t g x = (g \<circ> (\<lambda>x. 1 * x + (t - 1))) x" if "x \<in> {1-t..1}" for x
  proof -
    from that have "x = 1-t \<or> x > 1-t" by auto
    then show ?thesis
    proof
      assume "x = 1-t"
      then show ?thesis
        using loop t1 by (simp add: shiftpath_def pathfinish_def pathstart_def)
    next
      assume "x > 1-t"
      then have "t + x > 1" by auto
      then show ?thesis
        by (simp add: add.commute add_diff_eq shiftpath_def)
    qed
  qed
  \<comment> \<open>Bounded variation on each half\<close>
  have bv1: "has_bounded_variation_on (shiftpath t g) {0..1-t}"
  proof -
    have "has_bounded_variation_on (shiftpath t g) {0..1-t} \<longleftrightarrow>
      has_bounded_variation_on (g \<circ> (\<lambda>x. 1 * x + t)) {0..1-t}"
      by (rule has_bounded_variation_on_cong[OF eq1])
    also have "\<dots> \<longleftrightarrow> has_bounded_variation_on g {1*0+t..1*(1-t)+t}"
      using has_bounded_variation_on_affine_iff mt zero_less_one by blast
    also have "{1*0+t..1*(1-t)+t} = {t..1::real}" by auto
    finally show ?thesis
      using has_bounded_variation_on_subset[OF bvg, of "{t..1}"] t0 t1 by auto
  qed
  have bv2: "has_bounded_variation_on (shiftpath t g) {1-t..1}"
  proof -
    have "has_bounded_variation_on (shiftpath t g) {1-t..1} \<longleftrightarrow>
      has_bounded_variation_on (g \<circ> (\<lambda>x. 1 * x + (t - 1))) {1-t..1}"
      by (rule has_bounded_variation_on_cong[OF eq2])
    also have "\<dots> \<longleftrightarrow> has_bounded_variation_on g {1*(1-t)+(t-1)..1*1+(t-1)}"
      using has_bounded_variation_on_affine_iff mt1 zero_less_one by blast
    also have "{1*(1-t)+(t-1)..1*1+(t-1)} = {0..t::real}" by auto
    finally show ?thesis
      using has_bounded_variation_on_subset[OF bvg, of "{0..t}"] t0 t1 by auto
  qed
  \<comment> \<open>Combine\<close>
  have "has_bounded_variation_on (shiftpath t g) {0..1}"
    using has_bounded_variation_on_combine[of 0 "1-t" 1 "shiftpath t g"] mt mt1 bv1 bv2 by auto
  then show "rectifiable_path (shiftpath t g)"
    unfolding rectifiable_path_def
    using path_shiftpath[OF pg loop t01] by auto
qed

lemma path_length_shiftpath:
  assumes rg: "rectifiable_path g"
    and loop: "pathfinish g = pathstart g"
    and t01: "t \<in> {0..1}"
  shows "path_length (shiftpath t g) = path_length g"
proof -
  from rg have bvg: "has_bounded_variation_on g {0..1}"
    unfolding rectifiable_path_def by auto
  have bvs: "has_bounded_variation_on (shiftpath t g) {0..1}"
    using rectifiable_path_shiftpath[OF rg loop t01]
    unfolding rectifiable_path_def by auto
  from t01 have t0: "0 \<le> t" and t1: "t \<le> 1" and mt: "0 \<le> 1 - t" and mt1: "1 - t \<le> 1" by auto
  \<comment> \<open>Pointwise agreements (reuse from rectifiable_path_shiftpath proof)\<close>
  have eq1: "shiftpath t g x = (g \<circ> (\<lambda>x. 1 * x + t)) x" if "x \<in> {0..1-t}" for x
    using that t1 by (auto simp: shiftpath_def algebra_simps)
  have eq2: "shiftpath t g x = (g \<circ> (\<lambda>x. 1 * x + (t - 1))) x" if "x \<in> {1-t..1}" for x
  proof -
    from that have "x = 1-t \<or> x > 1-t" by auto
    then show ?thesis
    proof
      assume "x = 1-t"
      then show ?thesis
        using loop t1 by (simp add: shiftpath_def pathfinish_def pathstart_def algebra_simps)
    next
      assume "x > 1-t"
      then have "t + x > 1" by auto
      then show ?thesis by (auto simp: shiftpath_def comp_def algebra_simps)
    qed
  qed
  \<comment> \<open>Variation on {0..1-t}\<close>
  have vv1: "vector_variation {0..1-t} (shiftpath t g) = vector_variation {t..1} g"
  proof -
    have "vector_variation {0..1-t} (shiftpath t g) =
      vector_variation {0..1-t} (g \<circ> (\<lambda>x. 1 * x + t))"
      by (rule vector_variation_cong[OF eq1])
    also have "\<dots> = vector_variation {1*0+t..1*(1-t)+t} g"
      by (rule vector_variation_affine_eq) (use t1 in auto)
    also have "{1*0+t..1*(1-t)+t} = {t..1::real}" by auto
    finally show ?thesis .
  qed
  \<comment> \<open>Variation on {1-t..1}\<close>
  have vv2: "vector_variation {1-t..1} (shiftpath t g) = vector_variation {0..t} g"
  proof -
    have "vector_variation {1-t..1} (shiftpath t g) =
      vector_variation {1-t..1} (g \<circ> (\<lambda>x. 1 * x + (t - 1)))"
      by (rule vector_variation_cong[OF eq2])
    also have "\<dots> = vector_variation {1*(1-t)+(t-1)..1*1+(t-1)} g"
      by (rule vector_variation_affine_eq) (use t0 in auto)
    also have "{1*(1-t)+(t-1)..1*1+(t-1)} = {0..t::real}" by auto
    finally show ?thesis .
  qed
  \<comment> \<open>Combine\<close>
  have "path_length (shiftpath t g) = vector_variation {0..1} (shiftpath t g)"
    unfolding path_length_def ..
  also have "\<dots> = vector_variation {0..1-t} (shiftpath t g) +
    vector_variation {1-t..1} (shiftpath t g)"
    using vector_variation_combine[OF bvs, of "1-t"] mt mt1 by auto
  also have "\<dots> = vector_variation {t..1} g + vector_variation {0..t} g"
    using vv1 vv2 by simp
  also have "\<dots> = vector_variation {0..t} g + vector_variation {t..1} g"
    by (rule add.commute)
  also have "\<dots> = vector_variation {0..1} g"
    using vector_variation_combine[OF bvg, of t] t01 by auto
  also have "\<dots> = path_length g"
    unfolding path_length_def ..
  finally show "path_length (shiftpath t g) = path_length g" .
qed

section \<open>Lipschitz and distance bounds\<close>

lemma lipschitz_imp_rectifiable_path:
  assumes "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow>
    norm (g x - g y) \<le> B * norm (x - y)"
  shows "rectifiable_path g"
  unfolding rectifiable_path_def
proof
  show "path g"
    unfolding path_def
  proof (rule continuous_onI)
    fix x e :: real assume "x \<in> {0..1}" "e > 0"
    define d where "d = (if B \<le> 0 then 1 else e / B)"
    have "d > 0" using \<open>e > 0\<close> unfolding d_def by (auto simp: field_simps)
    moreover have "\<And>x'. x' \<in> {0..1} \<Longrightarrow> dist x' x < d \<Longrightarrow> dist (g x') (g x) < e"
    proof -
      fix x' assume "x' \<in> {0..1}" "dist x' x < d"
      have "dist (g x') (g x) = norm (g x' - g x)" by (simp add: dist_norm)
      also have "\<dots> \<le> B * norm (x' - x)" using assms[OF \<open>x' \<in> {0..1}\<close> \<open>x \<in> {0..1}\<close>] .
      also have "\<dots> \<le> B * dist x' x" by (simp add: dist_norm)
      also have "\<dots> < e"
      proof (cases "B \<le> 0")
        case True
        then have "B * dist x' x \<le> 0" by (simp add: mult_nonpos_nonneg)
        also have "0 < e" using \<open>e > 0\<close> .
        finally show ?thesis .
      next
        case False
        then have "B > 0" by auto
        then have "B * dist x' x < B * d"
          using \<open>dist x' x < d\<close> by auto
        also have "\<dots> = e" using \<open>B > 0\<close> unfolding d_def by auto
        finally show ?thesis .
      qed
      finally show "dist (g x') (g x) < e" .
    qed
    ultimately show "\<exists>d>0. \<forall>x'\<in>{0..1}. dist x' x < d \<longrightarrow> dist (g x') (g x) \<le> e"
      using less_le_not_le by blast 
  qed
next
  show "has_bounded_variation_on g {0..1}"
    using Lipschitz_imp_has_bounded_variation[of "{0..1}" g B] assms
    by auto
qed

lemma path_length_lipschitz:
  assumes "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> norm (g x - g y) \<le> B * norm (x - y)"
  shows "path_length g \<le> B"
  unfolding path_length_def
proof (rule has_bounded_variation_works(2)[OF Lipschitz_imp_has_bounded_variation[of "{0..1}" g B]])
  show "bounded {0..1::real}" by simp
  show "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> norm (g x - g y) \<le> B * norm (x - y)"
    using assms by auto
next
  fix d t assume dt: "d division_of t" "t \<subseteq> {(0::real)..1}"
  have \<open>B \<ge> 0\<close>
    using assms [of 0 1] norm_ge_zero by (fastforce elim: order_trans)
  have "(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> (\<Sum>k\<in>d. B * content k)"
  proof (rule sum_mono)
    fix k assume kd: "k \<in> d"
    from division_ofD(2,3,4)[OF dt(1) kd] obtain l u where
      k_eq: "k = cbox l u" and ksub: "k \<subseteq> t" and kne: "k \<noteq> {}" by auto
    then have lu: "l \<le> u" by fastforce
    obtain ls: "l \<in> {0..1}" and us: "u \<in> {0..1}"
      using ksub dt(2) lu k_eq cbox_interval atLeastAtMost_iff by blast
    have "norm (g (Sup k) - g (Inf k)) = norm (g u - g l)"
      using lu k_eq by (simp add: cbox_interval)
    also have "\<dots> \<le> B * norm (u - l)"
      using assms[OF us ls] by (simp add: norm_minus_commute)
    also have "\<dots> = B * (u - l)" using lu by (simp add: real_norm_def)
    also have "\<dots> = B * content k"
      using lu k_eq by (simp add: cbox_interval)
    finally show "norm (g (Sup k) - g (Inf k)) \<le> B * content k" .
  qed
  also have "\<dots> = B * (\<Sum>k\<in>d. content k)" by (simp add: sum_distrib_left)
  also have "\<dots> \<le> B * 1"
  proof (intro mult_left_mono \<open>B\<ge>0\<close>)
    have "(\<Sum>k\<in>d. content k) \<le> content {0..1::real}"
      using subadditive_content_division[OF dt(1)] dt(2) by force
    then show "(\<Sum>k\<in>d. content k) \<le> 1" by simp
  qed
  finally show "(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> B" by simp
qed


lemma dist_points_le_path_length:
  "\<lbrakk>rectifiable_path g; a \<in> {0..1}; b \<in> {0..1}\<rbrakk> \<Longrightarrow>
    dist (g a) (g b) \<le> path_length g"
  unfolding rectifiable_path_def path_length_def dist_norm
  using vector_variation_ge_norm_function by blast

lemma dist_endpoints_le_path_length:
  "rectifiable_path g \<Longrightarrow> dist (pathstart g) (pathfinish g) \<le> path_length g"
  using dist_points_le_path_length[of g 0 1]
  by (simp add: pathstart_def pathfinish_def)

lemma path_length_eq_line_segment:
  assumes rect: "rectifiable_path g"
    and len: "path_length g = dist (pathstart g) (pathfinish g)"
  shows "path_image g = closed_segment (pathstart g) (pathfinish g)"
proof (rule equalityI)
  have pg: "path g" and bv: "has_bounded_variation_on g {0..1}"
    using rect unfolding rectifiable_path_def by auto
  have vv_eq: "vector_variation {0..1} g = norm (g 1 - g 0)"
    using len unfolding path_length_def pathstart_def pathfinish_def dist_norm
    by (simp add: norm_minus_commute)
  show sub: "path_image g \<subseteq> closed_segment (pathstart g) (pathfinish g)"
  proof
    fix x assume "x \<in> path_image g"
    then obtain t where t: "t \<in> {0..1}" "x = g t"
      unfolding path_image_def by auto
    have t01: "0 \<le> t" "t \<le> 1" using t(1) by auto
    have bv_0t: "has_bounded_variation_on g {0..t}"
      using has_bounded_variation_on_subset[OF bv] t(1) by auto
    have bv_t1: "has_bounded_variation_on g {t..1}"
      using has_bounded_variation_on_subset[OF bv] t(1) by auto
    have n1: "norm (g t - g 0) \<le> vector_variation {0..t} g"
      using vector_variation_ge_norm_function[OF bv_0t] t01 by auto
    have n2: "norm (g 1 - g t) \<le> vector_variation {t..1} g"
      using vector_variation_ge_norm_function[OF bv_t1] t01 by auto
    have split: "vector_variation {0..t} g + vector_variation {t..1} g =
      vector_variation {0..1} g"
      using vector_variation_combine[OF bv] t(1) by auto
    have tri: "norm (g 1 - g 0) \<le> norm (g t - g 0) + norm (g 1 - g t)"
      using norm_triangle_ineq[of "g t - g 0" "g 1 - g t"] by simp
    have "norm (g t - g 0) + norm (g 1 - g t) = norm (g 1 - g 0)"
      using n1 n2 split vv_eq tri by linarith
    then have "dist (g 0) (g 1) = dist (g 0) (g t) + dist (g t) (g 1)"
      by (simp add: dist_norm norm_minus_commute)
    then have "between (g 0, g 1) (g t)"
      unfolding between by simp
    then show "x \<in> closed_segment (pathstart g) (pathfinish g)"
      unfolding t(2) pathstart_def pathfinish_def between_mem_segment by simp
  qed
  show "closed_segment (pathstart g) (pathfinish g) \<subseteq> path_image g"
  proof -
    have ne: "path_image g \<noteq> {}"
      unfolding path_image_def by auto
    have compact: "compact (path_image g)"
      using compact_path_image[OF pg] .
    have conn: "connected (path_image g)"
      using connected_path_image[OF pg] .
    have col: "collinear (path_image g)"
    proof -
      from sub have "path_image g \<subseteq> closed_segment (pathstart g) (pathfinish g)" .
      moreover have "collinear (closed_segment (pathstart g) (pathfinish g))"
        by (rule collinear_closed_segment)
      ultimately show ?thesis
        unfolding collinear_def by (meson subsetD)
    qed
    obtain p q where pq: "path_image g = closed_segment p q"
      using compact_convex_collinear_segment_alt[OF ne compact conn col] by auto
    have "pathstart g \<in> path_image g"
      unfolding path_image_def pathstart_def by auto
    moreover have "pathfinish g \<in> path_image g"
      unfolding path_image_def pathfinish_def by auto
    ultimately have "pathstart g \<in> closed_segment p q" "pathfinish g \<in> closed_segment p q"
      using pq by auto
    then have "closed_segment (pathstart g) (pathfinish g) \<subseteq> closed_segment p q"
      using subset_closed_segment by blast
    then show ?thesis using pq by simp
  qed
qed

section \<open>Linepath\<close>

lemma rectifiable_path_linepath:
  "rectifiable_path (linepath a b)"
proof (rule lipschitz_imp_rectifiable_path[where B="dist a b"])
  fix x y :: real assume "x \<in> {0..1}" "y \<in> {0..1}"
  have "linepath a b x - linepath a b y = (x - y) *\<^sub>R (b - a)"
    by (simp add: linepath_def algebra_simps)
  then have "norm (linepath a b x - linepath a b y) = \<bar>x - y\<bar> * norm (b - a)"
    by simp
  also have "\<dots> = norm (b - a) * norm (x - y)"
    by (simp add: abs_real_def real_norm_def mult.commute)
  also have "\<dots> = dist a b * norm (x - y)"
    by (simp add: dist_norm norm_minus_commute)
  finally show "norm (linepath a b x - linepath a b y) \<le> dist a b * norm (x - y)"
    by simp
qed

lemma path_length_linepath:
  "path_length (linepath a b) = dist a b"
proof (rule antisym)
  show "path_length (linepath a b) \<le> dist a b"
  proof (rule path_length_lipschitz)
    fix x y :: real assume "x \<in> {0..1}" "y \<in> {0..1}"
    have "linepath a b x - linepath a b y = (x - y) *\<^sub>R (b - a)"
      by (simp add: linepath_def algebra_simps)
    then have "norm (linepath a b x - linepath a b y) = \<bar>x - y\<bar> * norm (b - a)"
      by simp
    also have "\<dots> = dist a b * norm (x - y)"
      by (simp add: dist_norm norm_minus_commute abs_real_def real_norm_def mult.commute)
    finally show "norm (linepath a b x - linepath a b y) \<le> dist a b * norm (x - y)"
      by simp
  qed
next
  have "dist a b = dist (pathstart (linepath a b)) (pathfinish (linepath a b))"
    by (simp add: pathstart_def pathfinish_def linepath_def dist_norm)
  also have "\<dots> \<le> path_length (linepath a b)"
    by (rule dist_endpoints_le_path_length[OF rectifiable_path_linepath])
  finally show "dist a b \<le> path_length (linepath a b)" .
qed

section \<open>Rectifiable path image bound\<close>

lemma rectifiable_path_image_subset_cball:
  assumes "rectifiable_path g"
  shows "path_image g \<subseteq> cball (pathstart g) (path_length g)"
proof
  fix x assume "x \<in> path_image g"
  then obtain t where t: "t \<in> {0..1}" "x = g t"
    unfolding path_image_def by auto
  have "dist (pathstart g) x = dist (g 0) (g t)"
    by (simp add: t(2) pathstart_def)
  also have "\<dots> \<le> path_length g"
    using dist_points_le_path_length[OF assms _ t(1)] by simp
  finally show "x \<in> cball (pathstart g) (path_length g)"
    by (simp add: mem_cball)
qed

end
