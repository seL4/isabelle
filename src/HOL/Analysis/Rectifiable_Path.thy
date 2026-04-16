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
      \<comment> \<open>Upper bound: 1-Lipschitz implies variation \<le> length of interval\<close>
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
      \<comment> \<open>Lower bound: variation of @{term g} on @{term \<open>{0..x}\<close>} \<ge> @{term x} via factoring through @{term f}\<close>
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
          \<comment> \<open>Composition lemma: variation of @{term \<open>g \<circ> V\<close>} on @{term \<open>{a..t}\<close>} \<le> variation of @{term g} on @{term \<open>{V a..V t}\<close>}\<close>
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

end
