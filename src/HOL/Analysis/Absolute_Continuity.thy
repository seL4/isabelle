theory Absolute_Continuity
  imports Bounded_Variation Equivalence_Lebesgue_Henstock_Integration Equivalence_Measurable_On_Borel

begin

text \<open>
  Absolute continuity for functions @{typ "real \<Rightarrow> 'a::euclidean_space"},
   and the fundamental theorem of calculus for absolutely continuous functions.
  Taken from HOL Light.
\<close>

lemma lebesgue_measure_eq_content:
  assumes "d division_of S"
  shows "measure lebesgue S = sum Henstock_Kurzweil_Integration.content d"
  by (metis assms content_division division_ofD(4) fmeasurableD fmeasurable_cbox
      measure_completion sum.cong)

lemma content_box_cases:
  "measure lborel (box a b) = (if \<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i then prod (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis else 0)"
  by (simp add: measure_lborel_box_eq inner_diff)

lemma content_box_cbox:
  shows "measure lborel (box a b) = measure lborel (cbox a b)"
  by (simp add: content_box_cases content_cbox_cases)

lemma content_eq_0: "measure lborel (box a b) = 0 \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i \<le> a\<bullet>i)"
  by (auto simp: content_box_cases not_le intro: less_imp_le antisym eq_refl)

lemma box_subset_imp_measure_le: "cbox a b \<subseteq> box c d \<Longrightarrow> measure lborel (cbox a b) \<le> measure lborel (box c d)"
  unfolding measure_def
  by (intro enn2real_mono emeasure_mono) (auto simp: emeasure_lborel_cbox_eq emeasure_lborel_box_eq)

section \<open>Absolute set-continuity\<close>

definition absolutely_setcontinuous_on ::
  "('a::euclidean_space set \<Rightarrow> 'b::euclidean_space) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "absolutely_setcontinuous_on f S \<equiv>
    (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta> 
     \<longrightarrow> (\<Sum>k\<in>d. norm (f k)) < \<epsilon>)"

lemma absolutely_setcontinuous_on_subset:
  assumes \<open>absolutely_setcontinuous_on f S\<close> \<open>T \<subseteq> S\<close>
  shows \<open>absolutely_setcontinuous_on f T\<close>
  using assms unfolding absolutely_setcontinuous_on_def by (meson order_trans)

lemma absolutely_setcontinuous_on_imp_has_bounded_setvariation_on:
  fixes f :: "real set \<Rightarrow> 'a::euclidean_space"
  assumes "operative (+) 0 f" "absolutely_setcontinuous_on f S" "bounded S"
  shows "has_bounded_setvariation_on f S"
proof -
  from assms
  obtain r where r_pos: \<open>r > 0\<close>
    and r_bound: \<open>\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> (\<Sum>k\<in>d. content k) < r \<Longrightarrow> (\<Sum>k\<in>d. norm (f k)) < 1\<close>
    by (metis absolutely_setcontinuous_on_def zero_less_one)
  from \<open>bounded S\<close> obtain a :: real where s_sub: \<open>S \<subseteq> cbox (-a) a\<close>
    using bounded_subset_cbox_symmetric by blast
  define \<delta> where \<open>\<delta> = min r 1 / 3\<close>
  have \<delta>_pos: \<open>\<delta> > 0\<close> unfolding \<delta>_def using r_pos by auto
  obtain p where p_div: \<open>p tagged_division_of {-a..a}\<close> and p_fine: \<open>(\<lambda>x. ball x \<delta>) fine p\<close>
    using fine_division_exists_real[OF gauge_ball[OF \<delta>_pos]] by blast
  define D where \<open>D \<equiv> snd ` p\<close>
  have D_div: \<open>D division_of {-a..a}\<close>
    unfolding D_def using division_of_tagged_division[OF p_div] by simp
  have fin_D: \<open>finite D\<close> using division_ofD(1)[OF D_div] by auto
  have f_empty: \<open>f {} = 0\<close> using operative.empty[OF assms(1)] .
  have "(\<Sum>k\<in>d. norm (f k)) \<le> card D * 1"
    if div: "d division_of T" and sub: "T \<subseteq> S" for d T
  proof -
    have t_sub: "T \<subseteq> cbox (-a) a"
      using sub s_sub by auto
    \<comment> \<open>First inequality: pointwise bound via operative splitting\<close>
    have step1: "(\<Sum>k\<in>d. norm (f k)) \<le> (\<Sum>k\<in>d. \<Sum>l\<in>D. norm (f (k \<inter> l)))"
    proof (rule sum_mono)
      fix k assume kd: "k \<in> d"
      then obtain c' d' where k_eq: "k = cbox c' d'" and k_ne: "k \<noteq> {}" and k_sub: "k \<subseteq> cbox (-a) a"
        by (metis cbox_division_memE div dual_order.trans t_sub)
      \<comment> \<open>The intersections @{term \<open>{k \<inter> l | l. l \<in> D \<and> k \<inter> l \<noteq> {}}\<close>} form a division of @{term k}\<close>
      have k_div_self: "{cbox c' d'} division_of cbox c' d'"
        by (metis k_ne k_eq division_of_self)
      have inter_div: "{k1 \<inter> k2 |k1 k2. k1 \<in> {cbox c' d'} \<and> k2 \<in> D \<and> k1 \<inter> k2 \<noteq> {}}
                       division_of (cbox c' d' \<inter> cbox (-a) a)"
        using division_inter[OF k_div_self D_div] by auto
      have k_inter: "cbox c' d' \<inter> cbox (-a) a = cbox c' d'"
        using k_sub k_eq by blast
      then have E_div: "{cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}}
                        division_of cbox c' d'"
        using inter_div by force
      \<comment> \<open>By operativity, @{term \<open>f k\<close>} equals the sum of @{term f} over the division\<close>
      have f_split: "sum f {cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}} = f (cbox c' d')"
        using operative.division[OF assms(1) E_div] by (simp add: sum_def)
      \<comment> \<open>Triangle inequality\<close>
      have step_eq: "norm (f k) = norm (sum f {cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}})"
        by (metis f_split k_eq)
      \<comment> \<open>Extend the sum from the image to all of @{term D}\<close>
      have step_ext: "(\<Sum>j\<in>{cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}}. norm (f j))
                     \<le> (\<Sum>l\<in>D. norm (f (k \<inter> l)))"
      proof -
        have eq: "(\<lambda>l. cbox c' d' \<inter> l) ` {l \<in> D. cbox c' d' \<inter> l \<noteq> {}}
                 = {cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}}"
          by auto
        have "(\<Sum>j\<in>{cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}}. norm (f j))
              \<le> (\<Sum>l\<in>{l \<in> D. cbox c' d' \<inter> l \<noteq> {}}. norm (f (cbox c' d' \<inter> l)))"
          unfolding eq[symmetric]
          by (intro order_trans[OF sum_image_le]) (auto simp: fin_D o_def)
        also have \<open>\<dots> \<le> (\<Sum>l\<in>D. norm (f (k \<inter> l)))\<close>
          by (auto intro!: sum_mono2[OF fin_D] simp: k_eq)
        finally show ?thesis .
      qed
      show "norm (f k) \<le> (\<Sum>l\<in>D. norm (f (k \<inter> l)))"
        using step_eq norm_sum step_ext
        by (metis (mono_tags, lifting) order_trans)
    qed
    \<comment> \<open>Second inequality: swap sums and bound each inner sum by 1\<close>
    also have "(\<Sum>k\<in>d. \<Sum>l\<in>D. norm (f (k \<inter> l))) = (\<Sum>l\<in>D. \<Sum>k\<in>d. norm (f (k \<inter> l)))"
      by (rule sum.swap)
    also have "\<dots> \<le> card D * 1"
    proof -
      have "(\<Sum>l\<in>D. \<Sum>k\<in>d. norm (f (k \<inter> l))) \<le> of_nat (card D) * 1"
      proof (rule sum_bounded_above)
        fix l assume lD: "l \<in> D"
        then obtain u v where luv: \<open>l = {u..v}\<close> and \<open>{u..v} \<in> D\<close> \<open>{u..v} \<noteq> {}\<close>
          by (metis D_div cbox_division_memE cbox_interval)
        define d' where \<open>d' \<equiv> (\<lambda>k. k \<inter> {u..v}) ` {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close>
        have \<open>d' division_of T \<inter> {u..v}\<close>
        proof -
          have \<open>{u..v} = cbox u v\<close> by (simp add: cbox_interval)
          then have \<open>{{u..v}} division_of {u..v}\<close>
            using \<open>{u..v} \<noteq> {}\<close> division_of_self by metis
          from division_inter[OF div this] show ?thesis 
            by (simp add: setcompr_eq_image d'_def)
        qed

        moreover have \<open>T \<inter> {u..v} \<subseteq> S\<close>
          using sub by auto
        moreover have \<open>sum content d' < r\<close>
        proof -
          have content_bound: \<open>sum content d' \<le> content (cbox u v)\<close>
            using subadditive_content_division[OF \<open>d' division_of T \<inter> {u..v}\<close>] by auto
          obtain x where \<open>(x, {u..v}) \<in> p\<close>
            using \<open>{u..v} \<in> D\<close> unfolding D_def by auto
          then have \<open>{u..v} \<subseteq> ball x \<delta>\<close>
            using fineD[OF p_fine] by auto
          then have uv_in: \<open>u \<in> ball x \<delta>\<close> \<open>v \<in> ball x \<delta>\<close>
            using \<open>{u..v} \<noteq> {}\<close> by auto
          have \<open>u \<le> v\<close> using \<open>{u..v} \<noteq> {}\<close> by auto
          have \<open>content (cbox u v) < r\<close>
          proof -
            from uv_in have \<open>dist x u < \<delta>\<close> \<open>dist x v < \<delta>\<close> by auto
            then have \<open>v - u < 2 * \<delta>\<close>
              by (auto simp: dist_real_def)
            also have \<open>\<dots> \<le> 2 * (r / 3)\<close>
              unfolding \<delta>_def by (auto simp: min_def)
            also have \<open>\<dots> < r\<close> using r_pos by auto
            finally show ?thesis
              using \<open>u \<le> v\<close> by (simp add: cbox_interval content_real)
          qed
          then show ?thesis using content_bound by linarith
        qed
        ultimately have less1: \<open>(\<Sum>k\<in>d'. norm (f k)) < 1\<close>
          using r_bound by presburger
        show "(\<Sum>k\<in>d. norm (f (k \<inter> l))) \<le> 1"
        proof -
          have fin_d: \<open>finite d\<close> using division_ofD(1)[OF div] .
          have collision: \<open>norm (f (k1 \<inter> {u..v})) = 0\<close>
            if k1d: \<open>k1 \<in> d\<close> and k2d: \<open>k2 \<in> d\<close> and neq: \<open>k1 \<noteq> k2\<close>
              and coll: \<open>k1 \<inter> {u..v} = k2 \<inter> {u..v}\<close>
            for k1 k2
          proof -
            have \<open>interior k1 \<inter> interior {u..v} = interior k2 \<inter> interior {u..v}\<close>
              using arg_cong[OF coll, of interior] by simp
            then have \<open>interior (k1 \<inter> {u..v}) \<subseteq> interior k1 \<inter> interior k2\<close>
              by auto
            then have \<open>interior (k1 \<inter> {u..v}) = {}\<close>
              using division_ofD(5)[OF div k1d k2d neq] by auto
            obtain a1 b1 where k1_eq: \<open>k1 = cbox a1 b1\<close>
              using division_ofD(4)[OF div k1d] by blast
            have k1_uv: \<open>k1 \<inter> {u..v} = cbox (max a1 u) (min b1 v)\<close>
              by (simp add: k1_eq cbox_interval)
            then have \<open>box (max a1 u) (min b1 v) = {}\<close>
              using \<open>interior (k1 \<inter> {u..v}) = {}\<close> by simp
            then show ?thesis
              using operative.box_empty_imp[OF assms(1)] k1_uv by auto
          qed
          \<comment> \<open>Reindex via @{text SUM_IMAGE_NONZERO}\<close>
          have fin_A: \<open>finite {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close> using fin_d by auto
          have reindex: \<open>sum (\<lambda>k. norm (f k)) ((\<lambda>k. k \<inter> {u..v}) ` {k \<in> d. k \<inter> {u..v} \<noteq> {}})
              = sum ((\<lambda>k. norm (f k)) \<circ> (\<lambda>k. k \<inter> {u..v})) {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close>
            by (smt (verit) collision fin_A mem_Collect_eq sum.reindex_nontrivial)
          have \<open>(\<Sum>k\<in>d. norm (f (k \<inter> l)))
              = (\<Sum>k\<in>{k \<in> d. k \<inter> {u..v} \<noteq> {}}. norm (f (k \<inter> {u..v})))\<close>
            by (auto intro!: sum.mono_neutral_right simp: luv f_empty fin_d)
          also have \<open>\<dots> = (\<Sum>k\<in>d'. norm (f k))\<close>
            using reindex unfolding d'_def comp_def by auto
          also have \<open>\<dots> < 1\<close> using less1 .
          finally show ?thesis by simp
        qed
      qed
      then show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  then show ?thesis
    using has_bounded_setvariation_on_def by blast
qed

section \<open>Absolute continuity for functions\<close>

definition absolutely_continuous_on ::
  "real set \<Rightarrow> (real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> bool" where
  "absolutely_continuous_on S f \<equiv>
    absolutely_setcontinuous_on (\<lambda>k. f (Sup k) - f (Inf k)) S"

subsection \<open>Basic properties\<close>

lemma absolutely_continuous_on_eq:
  assumes eq: "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
    and ac: "absolutely_continuous_on S f"
  shows "absolutely_continuous_on S g"
proof -
  have "g (Sup k) - g (Inf k) = f (Sup k) - f (Inf k)" if "k \<in> d" "d division_of T" "T \<subseteq> S"
    for k d T
  proof -
    from that obtain a b where kb: "k = {a..b}" and "k \<subseteq> T" and "a \<le> b"
      by (metis atLeastatMost_empty_iff box_real(2) cbox_division_memE)
    then have "a \<in> S" "b \<in> S"
      using \<open>k \<subseteq> T\<close> \<open>T \<subseteq> S\<close> kb by auto
    then show "g (Sup k) - g (Inf k) = f (Sup k) - f (Inf k)"
      using eq kb \<open>a \<le> b\<close> by auto
  qed
  then show ?thesis
    using ac unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
    by (metis (no_types, lifting) sum.cong)
qed

lemma absolutely_continuous_on_subset:
  "absolutely_continuous_on S f \<Longrightarrow> T \<subseteq> S \<Longrightarrow> absolutely_continuous_on T f"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  by (meson order_trans)

lemma absolutely_continuous_on_const [continuous_intros]:
  "absolutely_continuous_on S (\<lambda>x. c)"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  by simp

lemma absolutely_continuous_on_cmul [continuous_intros]:
  assumes ac: "absolutely_continuous_on S f"
  shows "absolutely_continuous_on S (\<lambda>x. a *\<^sub>R f x)"
proof (cases "a = 0")
  case True then show ?thesis
    by (simp add: absolutely_continuous_on_const)
next
  case False
  show ?thesis
    unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    then have "\<epsilon> / \<bar>a\<bar> > 0" using False by simp
    then obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> S \<Longrightarrow>
      (\<Sum>k\<in>d. content k) < \<delta> \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / \<bar>a\<bar>"
      using ac unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
      by (meson order.strict_trans2)
    show "\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm (a *\<^sub>R f (Sup k) - a *\<^sub>R f (Inf k))) < \<epsilon>"
    proof (intro exI conjI allI impI)
      show "\<delta> > 0" by fact
    next
      fix d T assume H: "d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta>"
      then have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / \<bar>a\<bar>"
        using \<delta> by auto
      then have "\<bar>a\<bar> * (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
        using False by (simp add: field_simps)
      moreover have "(\<Sum>k\<in>d. norm (a *\<^sub>R f (Sup k) - a *\<^sub>R f (Inf k))) =
        \<bar>a\<bar> * (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))" 
        by (simp add: scaleR_diff_right[symmetric] sum_distrib_left)
      ultimately show "(\<Sum>k\<in>d. norm (a *\<^sub>R f (Sup k) - a *\<^sub>R f (Inf k))) < \<epsilon>"
        by linarith
    qed
  qed
qed

lemma absolutely_continuous_on_neg [continuous_intros]:
  "absolutely_continuous_on S f \<Longrightarrow> absolutely_continuous_on S (\<lambda>x. - f x)"
  using absolutely_continuous_on_cmul[of S f "-1"] by simp

lemma absolutely_continuous_on_add [continuous_intros]:
  assumes "absolutely_continuous_on S f" and g: "absolutely_continuous_on S g"
  shows "absolutely_continuous_on S (\<lambda>x. f x + g x)"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
proof (intro allI impI)
  fix \<epsilon> :: real assume "\<epsilon> > 0"
  obtain \<delta>1 \<delta>2 where "\<delta>1 > 0" and \<delta>1: "\<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta>1 \<longrightarrow>
                (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>/2"
                 and "\<delta>2 > 0" and \<delta>2: "\<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta>2 \<longrightarrow>
    (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) < \<epsilon>/2"
    using assms \<open>\<epsilon> > 0\<close>
    unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
    by (metis (lifting) less_divide_eq_numeral1(1) mult_zero_left) 
  show "\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) + g (Sup k) - (f (Inf k) + g (Inf k)))) < \<epsilon>"
  proof (intro exI conjI allI impI)
    show "min \<delta>1 \<delta>2 > 0" using \<open>\<delta>1 > 0\<close> \<open>\<delta>2 > 0\<close> by auto
  next
    fix d T assume H: "d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < min \<delta>1 \<delta>2"
    have f_bd: "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>/2" using \<delta>1 H by auto
    have g_bd: "(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) < \<epsilon>/2" using \<delta>2 H by auto
    have "(\<Sum>k\<in>d. norm (f (Sup k) + g (Sup k) - (f (Inf k) + g (Inf k)))) \<le>
      (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) + norm (g (Sup k) - g (Inf k)))"
      by (intro sum_mono norm_diff_triangle_ineq)
    also have "\<dots> = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) + (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
      by (rule sum.distrib)
    also have "\<dots> < \<epsilon>" using f_bd g_bd by linarith
    finally show "(\<Sum>k\<in>d. norm (f (Sup k) + g (Sup k) - (f (Inf k) + g (Inf k)))) < \<epsilon>" .
  qed
qed

lemma absolutely_continuous_on_sub [continuous_intros]:
  "absolutely_continuous_on S f \<Longrightarrow> absolutely_continuous_on S g \<Longrightarrow>
    absolutely_continuous_on S (\<lambda>x. f x - g x)"
  using absolutely_continuous_on_add[of S f "\<lambda>x. - g x"] absolutely_continuous_on_neg by auto

lemma absolutely_continuous_on_norm [continuous_intros]:
  assumes ac: "absolutely_continuous_on S f"
  shows "absolutely_continuous_on S (\<lambda>x. norm (f x) *\<^sub>R e)"
proof (cases "e = 0")
  case True then show ?thesis by (simp add: absolutely_continuous_on_const)
next
  case False
  show ?thesis
    unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    then have "\<epsilon> / norm e > 0" using False by simp
    then obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> S \<Longrightarrow>
      (\<Sum>k\<in>d. content k) < \<delta> \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / norm e"
      using ac unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
      by (meson order.strict_trans2)
    show "\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm (norm (f (Sup k)) *\<^sub>R e - norm (f (Inf k)) *\<^sub>R e)) < \<epsilon>"
    proof (intro exI conjI allI impI)
      show "\<delta> > 0" by fact
    next
      fix d T assume H: "d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta>"
      have bd: "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / norm e"
        using \<delta> H by auto
      have "(\<Sum>k\<in>d. norm (norm (f (Sup k)) *\<^sub>R e - norm (f (Inf k)) *\<^sub>R e)) =
        (\<Sum>k\<in>d. \<bar>norm (f (Sup k)) - norm (f (Inf k))\<bar> * norm e)"
        by (simp add: scaleR_diff_left[symmetric] abs_real_def norm_scaleR)
      also have "\<dots> \<le> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) * norm e)"
        by (intro sum_mono mult_right_mono norm_triangle_ineq3) auto
      also have "\<dots> = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) * norm e"
        by (simp add: sum_distrib_right)
      also have "\<dots> < (\<epsilon> / norm e) * norm e"
        using bd False by (intro mult_strict_right_mono) auto
      also have "\<dots> = \<epsilon>" using False by simp
      finally show "(\<Sum>k\<in>d. norm (norm (f (Sup k)) *\<^sub>R e - norm (f (Inf k)) *\<^sub>R e)) < \<epsilon>" .
    qed
  qed
qed

lemma absolutely_continuous_on_compose_linear [continuous_intros]:
  assumes ac: "absolutely_continuous_on S f" and lin: "linear h"
  shows "absolutely_continuous_on S (h \<circ> f)"
proof -
  obtain K where "K > 0" and K: "\<And>x. norm (h x) \<le> norm x * K"
     using lin linear_conv_bounded_linear bounded_linear.pos_bounded by blast
  show ?thesis
    unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def o_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    then have "\<epsilon> / K > 0" using \<open>K > 0\<close> by simp
    then obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> S \<Longrightarrow>
      (\<Sum>k\<in>d. content k) < \<delta> \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / K"
      using ac unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
      by (meson order.strict_trans2)
    show "\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm (h (f (Sup k)) - h (f (Inf k)))) < \<epsilon>"
    proof (intro exI conjI allI impI)
      show "\<delta> > 0" by fact
    next
      fix d T assume H: "d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta>"
      have "(\<Sum>k\<in>d. norm (h (f (Sup k)) - h (f (Inf k)))) =
        (\<Sum>k\<in>d. norm (h (f (Sup k) - f (Inf k))))"
        using lin by (simp add: linear_diff)
      also have "\<dots> \<le> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) * K)"
        by (intro sum_mono K)
      also have "\<dots> = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) * K"
        by (simp add: sum_distrib_right)
      also have "\<dots> < (\<epsilon> / K) * K"
        using \<delta> H \<open>K > 0\<close> by (intro mult_strict_right_mono) auto
      also have "\<dots> = \<epsilon>" using \<open>K > 0\<close> by simp
      finally show "(\<Sum>k\<in>d. norm (h (f (Sup k)) - h (f (Inf k)))) < \<epsilon>" .
    qed
  qed
qed

lemma absolutely_continuous_on_null:
  assumes "content {a..b} = 0"
  shows "absolutely_continuous_on {a..b} f"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
proof (intro allI impI)
  fix \<epsilon> :: real assume "\<epsilon> > 0"
  show "\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
  proof (intro exI conjI allI impI)
    fix d T assume H: "d division_of T \<and> T \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < 1"
    then have div: "d division_of T" and sub: "T \<subseteq> {a..b}" by auto
    have "\<forall>k\<in>d. f (Sup k) - f (Inf k) = 0"
    proof
      fix k assume kd: "k \<in> d"
      then obtain u v where uv: "k = cbox u v" and kt: "k \<subseteq> T" and "u \<le> v" "k \<subseteq> {a..b}"
        by (metis atLeastatMost_empty' box_real(2) cbox_division_memE div sub subset_trans)
      then have "u = v"
        using assms by auto
      then show "f (Sup k) - f (Inf k) = 0"
        using uv by simp
    qed
    then show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
      using \<open>\<epsilon> > 0\<close> by simp
  qed auto
qed

lemma absolutely_continuous_on_id: "absolutely_continuous_on {a..b} id"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
proof (intro allI impI)
  fix \<epsilon> :: real assume "\<epsilon> > 0"
  show "\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
    (\<Sum>k\<in>d. norm (id (Sup k) - id (Inf k))) < \<epsilon>"
  proof (intro exI conjI allI impI)
    show "\<epsilon> > 0" by fact
  next
    fix d T assume H: "d division_of T \<and> T \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < \<epsilon>"
    then have div: "d division_of T" by auto
    have "(\<Sum>k\<in>d. norm (id (Sup k) - id (Inf k))) = (\<Sum>k\<in>d. content k)"
    proof (rule sum.cong, simp)
      fix k assume kd: "k \<in> d"
      then obtain u v where uv: "k = cbox u v" and kt: "k \<subseteq> T" and "u \<le> v"
        by (metis div atLeastatMost_empty_iff box_real(2) cbox_division_memE) 
      then show "norm (id (Sup k) - id (Inf k)) = content k"
        using uv by (simp add: content_real)
    qed
    also have "\<dots> < \<epsilon>" using H by auto
    finally show "(\<Sum>k\<in>d. norm (id (Sup k) - id (Inf k))) < \<epsilon>" .
  qed
qed

subsection \<open>Relationship to bounded variation and continuity\<close>

lemma absolutely_continuous_on_imp_continuous:
  assumes "absolutely_continuous_on S f" "is_interval S"
  shows "continuous_on S f"
proof (rule continuous_on_iff[THEN iffD2], intro ballI allI impI)
  fix x \<epsilon> :: real assume xs: "x \<in> S" and "\<epsilon> > 0"
  then obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> S \<Longrightarrow>
    (\<Sum>k\<in>d. content k) < \<delta> \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
    using assms(1) unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
    by (meson order.strict_trans2)
  show "\<exists>\<delta>>0. \<forall>x'\<in>S. dist x' x < \<delta> \<longrightarrow> dist (f x') (f x) < \<epsilon>"
  proof (intro exI conjI ballI impI)
    show "\<delta> > 0" by fact
  next
    fix y assume ys: "y \<in> S" and dyx: "dist y x < \<delta>"
    show "dist (f y) (f x) < \<epsilon>"
    proof (cases "x = y")
      case True then show ?thesis using \<open>\<epsilon> > 0\<close> by simp
    next
      case False
      define lo hi where "lo = min x y" and "hi = max x y"
      then have lohi: "lo \<le> hi" and lox: "lo \<le> x" and hix: "x \<le> hi"
        and loy: "lo \<le> y" and hiy: "y \<le> hi"
        by (auto simp: min_def max_def)
      have sub: "{lo..hi} \<subseteq> S"
        by (metis assms(2) box_real(2) hi_def interval_subset_is_interval lo_def max_def min_def xs ys)
      have ne: "cbox lo hi \<noteq> {}" using lohi by auto
      have div: "{cbox lo hi} division_of cbox lo hi"
        by (rule division_of_self[OF ne])
      have "(\<Sum>k\<in>{cbox lo hi}. content k) = content {lo..hi}" by simp
      also have "\<dots> = hi - lo" using content_real lohi by auto
      also have "\<dots> = dist y x"
        unfolding lo_def hi_def dist_real_def by (auto simp: min_def max_def)
      also have "\<dots> < \<delta>" by fact
      finally have sm: "(\<Sum>k\<in>{cbox lo hi}. content k) < \<delta>" .
      have "(\<Sum>k\<in>{cbox lo hi}. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
        using \<delta>[OF div] sub sm by auto
      then have "norm (f hi - f lo) < \<epsilon>" using lohi by simp
      then show "dist (f y) (f x) < \<epsilon>"
        using \<open>norm (f hi - f lo) < \<epsilon>\<close> lo_def hi_def 
        by (cases "x \<le> y") (auto simp: dist_norm norm_minus_commute)
    qed
  qed
qed

lemma operative_function_endpoint_diff:
  fixes f :: \<open>real \<Rightarrow> 'a::real_normed_vector\<close>
  defines \<open>h \<equiv> \<lambda>S. if S = {} then 0 else f (Sup S) - f (Inf S)\<close>
  shows \<open>operative (+) 0 h\<close>
proof (rule operative.intro)
  show \<open>comm_monoid_set (+) (0::'a)\<close>
    using sum.comm_monoid_set_axioms .
next
  show \<open>operative_axioms (+) 0 h\<close>
  proof (rule operative_axioms.intro)
    fix a b :: real
    assume \<open>box a b = {}\<close>
    then show \<open>h (cbox a b) = 0\<close>
      by (cases \<open>a = b\<close>) (auto simp: h_def cbox_interval)
  next
    fix a b c :: real and k :: real
    assume \<open>k \<in> Basis\<close>
    then have k1: \<open>k = 1\<close> by (simp add: Basis_real_def)
    have eq1: \<open>cbox a b \<inter> {x. x \<bullet> k \<le> c} = {a..min b c}\<close> if \<open>a \<le> b\<close> for c
      using k1 that by (auto simp: cbox_interval min_def)
    have eq2: \<open>cbox a b \<inter> {x. c \<le> x \<bullet> k} = {max a c..b}\<close> if \<open>a \<le> b\<close> for c
      using k1 that by (auto simp: cbox_interval max_def)
    show \<open>h (cbox a b) = h (cbox a b \<inter> {x. x \<bullet> k \<le> c}) + h (cbox a b \<inter> {x. c \<le> x \<bullet> k})\<close>
    proof (cases \<open>a \<le> b\<close>)
      case True
      then show ?thesis
        using eq1[OF True] eq2[OF True]
        by (cases \<open>c < a\<close>; cases \<open>b < c\<close>) (auto simp: h_def cbox_interval min_def max_def)
    next
      case False
      then have \<open>cbox a b = {}\<close> by (auto simp: cbox_interval)
      then show ?thesis by (simp add: h_def)
    qed
  qed
qed

lemma operative_absolutely_setcontinuous_on:
  fixes g :: \<open>'a::euclidean_space set \<Rightarrow> 'b::euclidean_space\<close>
  assumes \<open>operative (+) 0 g\<close>
  shows \<open>operative (\<and>) True (absolutely_setcontinuous_on g)\<close>
proof (intro operative.intro comm_monoid_set_and operative_axioms.intro iffI)
  note null = operative.box_empty_imp[OF assms]
  note split = operative.Basis_imp[OF assms, symmetric]
  show \<open>absolutely_setcontinuous_on g (cbox a b)\<close> if \<open>box a b = {}\<close> for a b
  proof -
    have \<open>g k = 0\<close> if \<open>k \<in> d\<close> and \<open>d division_of T\<close> and \<open>T \<subseteq> cbox a b\<close> for k d T
      by (metis \<open>box a b = {}\<close> cbox_division_memE negligible_interval(1) negligible_subset null
          that)
    then show ?thesis using that
      unfolding absolutely_setcontinuous_on_def
      by (intro iffI TrueI allI impI exI[of _ 1]) (auto simp: division_ofD(1))
  qed

  fix a b c and k::'a
  assume \<open>k \<in> Basis\<close>
  assume ac: \<open>absolutely_setcontinuous_on g (cbox a b \<inter> {x. x \<bullet> k \<le> c}) \<and>
                absolutely_setcontinuous_on g (cbox a b \<inter> {x. c \<le> x \<bullet> k})\<close>
  show \<open>absolutely_setcontinuous_on g (cbox a b)\<close>
    unfolding absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix e :: real assume \<open>e > 0\<close>
    then have e2: \<open>e / 2 > 0\<close> by simp
    from ac[unfolded absolutely_setcontinuous_on_def] e2
    obtain r1 where r1: \<open>r1 > 0\<close>
      and L: \<open>\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> cbox a b \<inter> {x. x \<bullet> k \<le> c} \<Longrightarrow>
          (\<Sum>k\<in>d. content k) < r1 \<Longrightarrow> (\<Sum>k\<in>d. norm (g k)) < e / 2\<close>
      by metis
    from ac[unfolded absolutely_setcontinuous_on_def] e2
    obtain r2 where r2: \<open>r2 > 0\<close>
      and R: \<open>\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> cbox a b \<inter> {x. c \<le> x \<bullet> k} \<Longrightarrow>
          (\<Sum>k\<in>d. content k) < r2 \<Longrightarrow> (\<Sum>k\<in>d. norm (g k)) < e / 2\<close>
      by metis
    show \<open>\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> cbox a b \<and>
        (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow> (\<Sum>k\<in>d. norm (g k)) < e\<close>
    proof (intro exI[of _ \<open>min r1 r2\<close>] conjI allI impI)
      show \<open>min r1 r2 > 0\<close> using r1 r2 by simp
    next
      fix d T
      assume H: \<open>d division_of T \<and> T \<subseteq> cbox a b \<and> (\<Sum>k\<in>d. content k) < min r1 r2\<close>
      then have div: \<open>d division_of T\<close> and sub: \<open>T \<subseteq> cbox a b\<close>
        and content_bound: \<open>(\<Sum>k\<in>d. content k) < r1\<close> \<open>(\<Sum>k\<in>d. content k) < r2\<close>
        by auto
      define dL where \<open>dL = (\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c}) ` {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
      define dR where \<open>dR = (\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k}) ` {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
      have fin_d: \<open>finite d\<close> using division_of_finite[OF div] .
      have g_empty: \<open>g {} = 0\<close> using operative.empty[OF assms] .
          \<comment> \<open>Step 1: split axiom + triangle inequality\<close>
      have \<open>(\<Sum>K\<in>d. norm (g K))
              \<le> (\<Sum>K\<in>d. norm (g (K \<inter> {x. x \<bullet> k \<le> c})) + norm (g (K \<inter> {x. c \<le> x \<bullet> k})))\<close>
      proof (rule sum_mono)
        fix K assume Kd: \<open>K \<in> d\<close>
        then obtain aK bK where K_eq: \<open>K = cbox aK bK\<close> using division_ofD(4)[OF div] by blast
        have \<open>g K = g (K \<inter> {x. x \<bullet> k \<le> c}) + g (K \<inter> {x. c \<le> x \<bullet> k})\<close>
          using local.split[OF \<open>k \<in> Basis\<close>, of aK bK c] K_eq by simp
        then show \<open>norm (g K) \<le> norm (g (K \<inter> {x. x \<bullet> k \<le> c})) + norm (g (K \<inter> {x. c \<le> x \<bullet> k}))\<close>
          by (metis norm_triangle_ineq)
      qed
      then have step1: \<open>(\<Sum>K\<in>d. norm (g K))
            \<le> (\<Sum>K\<in>d. norm (g (K \<inter> {x. x \<bullet> k \<le> c}))) + (\<Sum>K\<in>d. norm (g (K \<inter> {x. c \<le> x \<bullet> k})))\<close>
        by (metis (no_types, lifting) sum.distrib sum.cong)
        \<comment> \<open>Step 2: drop zero terms (where intersection is empty, @{term \<open>g {} = 0\<close>})\<close>
      have step2L: \<open>(\<Sum>K\<in>d. norm (g (K \<inter> {x. x \<bullet> k \<le> c})))
            = (\<Sum>K\<in>{l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}. norm (g (K \<inter> {x. x \<bullet> k \<le> c})))\<close>
        by (rule sum.mono_neutral_right) (auto simp: fin_d g_empty)
      have step2R: \<open>(\<Sum>K\<in>d. norm (g (K \<inter> {x. c \<le> x \<bullet> k})))
            = (\<Sum>K\<in>{l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}. norm (g (K \<inter> {x. c \<le> x \<bullet> k})))\<close>
        by (rule sum.mono_neutral_right) (auto simp: fin_d g_empty)
      have collision_L: \<open>norm (g (K1 \<inter> {x. x \<bullet> k \<le> c})) = 0\<close>
        if K1d: \<open>K1 \<in> d\<close> and K2d: \<open>K2 \<in> d\<close> and neq: \<open>K1 \<noteq> K2\<close>
          and coll: \<open>K1 \<inter> {x. x \<bullet> k \<le> c} = K2 \<inter> {x. x \<bullet> k \<le> c}\<close>
        for K1 K2
      proof -
        obtain a1 b1 where K1_eq: \<open>K1 = cbox a1 b1\<close> using division_ofD(4)[OF div K1d] by blast
        have eq: \<open>K1 \<inter> {x. x \<bullet> k \<le> c} = cbox a1 (\<Sum>i\<in>Basis. (if i = k then min (b1 \<bullet> k) c else b1 \<bullet> i) *\<^sub>R i)\<close>
          using interval_split(1)[OF \<open>k \<in> Basis\<close>] K1_eq by simp
        have \<open>interior (K1 \<inter> {x. x \<bullet> k \<le> c}) \<subseteq> interior K1 \<inter> interior K2\<close>
          using coll by (metis inf.cobounded1 interior_mono le_inf_iff)
        also have \<open>\<dots> = {}\<close> using division_ofD(5)[OF div K1d K2d neq] .
        finally have \<open>box a1 (\<Sum>i\<in>Basis. (if i = k then min (b1 \<bullet> k) c else b1 \<bullet> i) *\<^sub>R i) = {}\<close>
          using eq interior_cbox by auto
        then show ?thesis using null eq by auto
      qed
      have collision_R: \<open>norm (g (K1 \<inter> {x. c \<le> x \<bullet> k})) = 0\<close>
        if K1d: \<open>K1 \<in> d\<close> and K2d: \<open>K2 \<in> d\<close> and neq: \<open>K1 \<noteq> K2\<close>
          and coll: \<open>K1 \<inter> {x. c \<le> x \<bullet> k} = K2 \<inter> {x. c \<le> x \<bullet> k}\<close>
        for K1 K2
      proof -
        obtain a1 b1 where K1_eq: \<open>K1 = cbox a1 b1\<close> using division_ofD(4)[OF div K1d] by blast
        have eq: \<open>K1 \<inter> {x. c \<le> x \<bullet> k} = cbox (\<Sum>i\<in>Basis. (if i = k then max (a1 \<bullet> k) c else a1 \<bullet> i) *\<^sub>R i) b1\<close>
          using interval_split(2)[OF \<open>k \<in> Basis\<close>] K1_eq by simp
        have \<open>interior (K1 \<inter> {x. c \<le> x \<bullet> k}) \<subseteq> interior K1 \<inter> interior K2\<close>
          using coll by (metis inf.cobounded1 interior_mono le_inf_iff)
        also have \<open>\<dots> = {}\<close> using division_ofD(5)[OF div K1d K2d neq] .
        finally have \<open>box (\<Sum>i\<in>Basis. (if i = k then max (a1 \<bullet> k) c else a1 \<bullet> i) *\<^sub>R i) b1 = {}\<close>
          using eq interior_cbox by auto
        then show ?thesis using null eq by auto
      qed
      have fin_filt: \<open>finite {l \<in> d. l \<inter> S \<noteq> {}}\<close> for S :: \<open>'a set\<close>
        using fin_d by auto
      have reindexL: \<open>(\<Sum>K\<in>dL. norm (g K))
            = (\<Sum>K\<in>{l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}. norm (g (K \<inter> {x. x \<bullet> k \<le> c})))\<close>
        unfolding dL_def
        using collision_L 
        by (subst sum.reindex_nontrivial[OF fin_filt]) (auto simp: o_def) 
      have reindexR: \<open>(\<Sum>K\<in>dR. norm (g K))
            = (\<Sum>K\<in>{l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}. norm (g (K \<inter> {x. c \<le> x \<bullet> k})))\<close>
        unfolding dR_def
        using collision_R
        by (subst sum.reindex_nontrivial[OF fin_filt]) (auto simp: o_def) 
      have step3L: \<open>(\<Sum>K\<in>{l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}. norm (g (K \<inter> {x. x \<bullet> k \<le> c})))
            = (\<Sum>K\<in>dL. norm (g K))\<close>
        using reindexL by simp
      have step3R: \<open>(\<Sum>K\<in>{l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}. norm (g (K \<inter> {x. c \<le> x \<bullet> k})))
            = (\<Sum>K\<in>dR. norm (g K))\<close>
        using reindexR by simp
      have split_ineq: \<open>(\<Sum>k\<in>d. norm (g k)) \<le> (\<Sum>k\<in>dL. norm (g k)) + (\<Sum>k\<in>dR. norm (g k))\<close>
        using step1 step2L step2R step3L step3R by linarith
          \<comment> \<open>Step 4: each half is $< \varepsilon/2$\<close>
      have divL: \<open>dL division_of (T \<inter> {x. x \<bullet> k \<le> c})\<close>
        unfolding dL_def division_of_def
      proof (intro conjI ballI allI impI)
        show \<open>finite ((\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c}) ` {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}})\<close>
          using fin_d by auto
      next
        fix K assume \<open>K \<in> (\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c}) ` {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
        then obtain l  al bl where ld: \<open>l \<in> d\<close> and lne: \<open>l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}\<close> and Keq: \<open>K = l \<inter> {x. x \<bullet> k \<le> c}\<close>
          and leq: \<open>l = cbox al bl\<close> using division_ofD(4)[OF div] by blast
        show \<open>K \<subseteq> T \<inter> {x. x \<bullet> k \<le> c}\<close> using Keq division_ofD(2)[OF div ld] by auto
        show \<open>K \<noteq> {}\<close> using Keq lne by auto
        show \<open>\<exists>a b. K = cbox a b\<close> using Keq leq interval_split(1)[OF \<open>k \<in> Basis\<close>] by blast
      next
        fix K1 K2
        assume K1m: \<open>K1 \<in> (\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c}) ` {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
          and K2m: \<open>K2 \<in> (\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c}) ` {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
          and neq: \<open>K1 \<noteq> K2\<close>
        obtain l1 where l1d: \<open>l1 \<in> d\<close> and K1eq: \<open>K1 = l1 \<inter> {x. x \<bullet> k \<le> c}\<close> using K1m by auto
        obtain l2 where l2d: \<open>l2 \<in> d\<close> and K2eq: \<open>K2 = l2 \<inter> {x. x \<bullet> k \<le> c}\<close> using K2m by auto
        have \<open>l1 \<noteq> l2\<close> using neq K1eq K2eq by auto
        then have \<open>interior l1 \<inter> interior l2 = {}\<close> using division_ofD(5)[OF div l1d l2d] by auto
        then show \<open>interior K1 \<inter> interior K2 = {}\<close>
          using K1eq K2eq by auto
      next
        show \<open>\<Union> ((\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c}) ` {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}) = T \<inter> {x. x \<bullet> k \<le> c}\<close>
          using division_ofD(6)[OF div] by auto
      qed
      have divR: \<open>dR division_of (T \<inter> {x. c \<le> x \<bullet> k})\<close>
        unfolding dR_def division_of_def
      proof (intro conjI ballI allI impI)
        show \<open>finite ((\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k}) ` {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}})\<close>
          using fin_d by auto
      next
        fix K assume \<open>K \<in> (\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k}) ` {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
        then obtain l al bl where ld: \<open>l \<in> d\<close> and lne: \<open>l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}\<close> and Keq: \<open>K = l \<inter> {x. c \<le> x \<bullet> k}\<close>
          and leq: \<open>l = cbox al bl\<close> using division_ofD(4)[OF div] by blast
        show \<open>K \<subseteq> T \<inter> {x. c \<le> x \<bullet> k}\<close> using Keq division_ofD(2)[OF div ld] by auto
        show \<open>K \<noteq> {}\<close> using Keq lne by auto
        show \<open>\<exists>a b. K = cbox a b\<close> using Keq leq interval_split(2)[OF \<open>k \<in> Basis\<close>] by blast
      next
        fix K1 K2
        assume K1m: \<open>K1 \<in> (\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k}) ` {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
          and K2m: \<open>K2 \<in> (\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k}) ` {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
          and neq: \<open>K1 \<noteq> K2\<close>
        obtain l1 where l1d: \<open>l1 \<in> d\<close> and K1eq: \<open>K1 = l1 \<inter> {x. c \<le> x \<bullet> k}\<close> using K1m by auto
        obtain l2 where l2d: \<open>l2 \<in> d\<close> and K2eq: \<open>K2 = l2 \<inter> {x. c \<le> x \<bullet> k}\<close> using K2m by auto
        have \<open>l1 \<noteq> l2\<close> using neq K1eq K2eq by auto
        then have \<open>interior l1 \<inter> interior l2 = {}\<close> using division_ofD(5)[OF div l1d l2d] by auto
        then show \<open>interior K1 \<inter> interior K2 = {}\<close>
          using K1eq K2eq by auto
      next
        show \<open>\<Union> ((\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k}) ` {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}) = T \<inter> {x. c \<le> x \<bullet> k}\<close>
          using division_ofD(6)[OF div] by auto
      qed
      have subL: \<open>T \<inter> {x. x \<bullet> k \<le> c} \<subseteq> cbox a b \<inter> {x. x \<bullet> k \<le> c}\<close> using sub by auto
      have subR: \<open>T \<inter> {x. c \<le> x \<bullet> k} \<subseteq> cbox a b \<inter> {x. c \<le> x \<bullet> k}\<close> using sub by auto
      have contentL: \<open>sum content dL < r1\<close>
      proof -
        have \<open>sum content dL
              \<le> sum (content \<circ> (\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c})) {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
          unfolding dL_def by (rule sum_image_le) (auto simp: fin_d content_pos_le)
        also have \<open>\<dots> \<le> sum content {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
        proof (rule sum_mono)
          fix l assume \<open>l \<in> {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
          then have ld: \<open>l \<in> d\<close> by auto
          obtain al bl where leq: \<open>l = cbox al bl\<close> using division_ofD(4)[OF div ld] by blast
          have \<open>l \<inter> {x. x \<bullet> k \<le> c} = cbox al (\<Sum>i\<in>Basis. (if i = k then min (bl \<bullet> k) c else bl \<bullet> i) *\<^sub>R i)\<close>
            using interval_split(1)[OF \<open>k \<in> Basis\<close>] leq by simp
          then show \<open>(content \<circ> (\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c})) l \<le> content l\<close>
            using content_subset leq
            by (metis (lifting) comp_apply inf_le1)
        qed
        also have \<open>\<dots> \<le> sum content d\<close>
          by (rule sum_mono2) (auto simp: fin_d content_pos_le)
        also have \<open>\<dots> < r1\<close> using content_bound by simp
        finally show ?thesis .
      qed
      have contentR: \<open>sum content dR < r2\<close>
      proof -
        have \<open>sum content dR
              \<le> sum (content \<circ> (\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k})) {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
          unfolding dR_def by (rule sum_image_le) (auto simp: fin_d content_pos_le)
        also have \<open>\<dots> \<le> sum content {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
        proof (rule sum_mono)
          fix l assume \<open>l \<in> {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
          then have ld: \<open>l \<in> d\<close> by auto
          obtain al bl where leq: \<open>l = cbox al bl\<close> using division_ofD(4)[OF div ld] by blast
          have \<open>l \<inter> {x. c \<le> x \<bullet> k} = cbox (\<Sum>i\<in>Basis. (if i = k then max (al \<bullet> k) c else al \<bullet> i) *\<^sub>R i) bl\<close>
            using interval_split(2)[OF \<open>k \<in> Basis\<close>] leq by simp
          then show \<open>(content \<circ> (\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k})) l \<le> content l\<close>
            using content_subset leq by (metis (lifting) comp_apply inf_le1)
        qed
        also have \<open>\<dots> \<le> sum content d\<close>
          by (rule sum_mono2) (auto simp: fin_d content_pos_le)
        also have \<open>\<dots> < r2\<close> using content_bound by simp
        finally show ?thesis .
      qed
      have halves: \<open>(\<Sum>k\<in>dL. norm (g k)) + (\<Sum>k\<in>dR. norm (g k)) < e\<close>
        using L[OF divL subL contentL] R[OF divR subR contentR] by linarith
      show \<open>(\<Sum>k\<in>d. norm (g k)) < e\<close>
        using split_ineq halves by linarith
    qed
  qed
qed (use absolutely_setcontinuous_on_subset in fastforce)+

lemma operative_absolutely_continuous_on:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  shows \<open>operative (\<and>) True (\<lambda>S. absolutely_continuous_on S f)\<close>
proof -
  define h where \<open>h \<equiv> \<lambda>S. if S = {} then 0 else f (Sup S) - f (Inf S)\<close>
  have op_h: \<open>operative (+) 0 h\<close> using operative_function_endpoint_diff[of f, folded h_def] .
  have op_ac_h: \<open>operative (\<and>) True (absolutely_setcontinuous_on h)\<close>
    using operative_absolutely_setcontinuous_on[OF op_h] .
  have h_eq: \<open>h k = f (Sup k) - f (Inf k)\<close> if \<open>k \<noteq> {}\<close> for k
    using that by (simp add: h_def)
  have sum_eq: \<open>(\<Sum>k\<in>d. norm (h k)) = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))\<close>
    if div: \<open>d division_of T\<close> for d T
    by (intro sum.cong refl arg_cong[where f=norm] h_eq) (use division_ofD(3)[OF div] in auto)
  have ac_eq: \<open>absolutely_setcontinuous_on h S = absolutely_setcontinuous_on (\<lambda>k. f (Sup k) - f (Inf k)) S\<close> for S
    unfolding absolutely_setcontinuous_on_def
    by (metis (lifting) local.sum_eq)
  show ?thesis
    using op_ac_h unfolding absolutely_continuous_on_def ac_eq .
qed

lemma absolutely_continuous_on_imp_has_bounded_variation_on:
  assumes \<open>absolutely_continuous_on S f\<close> \<open>bounded S\<close>
  shows \<open>has_bounded_variation_on f S\<close>
  unfolding has_bounded_variation_on_def
proof -
  define h where \<open>h \<equiv> \<lambda>S. if S = {} then 0 else f (Sup S) - f (Inf S)\<close>
  have h_eq: \<open>h k = f (Sup k) - f (Inf k)\<close> if \<open>k \<in> d\<close> \<open>d division_of T\<close> for k d T
    using division_ofD(3)[OF that(2) that(1)] by (simp add: h_def)
  have sum_eq: \<open>(\<Sum>k\<in>d. norm (h k)) = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))\<close>
    if \<open>d division_of T\<close> for d T
    by (rule sum.cong) (auto simp: h_eq[OF _ that])
  have ac_h: \<open>absolutely_setcontinuous_on h S\<close>
    unfolding absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
    then obtain \<delta> where \<open>\<delta> > 0\<close> and \<delta>: \<open>\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> S \<Longrightarrow>
      (\<Sum>k\<in>d. content k) < \<delta> \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>\<close>
      using assms unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def by meson
    show \<open>\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm (h k)) < \<epsilon>\<close>
      using \<open>\<delta> > 0\<close> \<delta> sum_eq by auto
  qed
  from absolutely_setcontinuous_on_imp_has_bounded_setvariation_on
    [OF operative_function_endpoint_diff[of f, folded h_def] this \<open>bounded S\<close>]
  show \<open>has_bounded_setvariation_on (\<lambda>k. f (Sup k) - f (Inf k)) S\<close>
    unfolding has_bounded_setvariation_on_def by (metis sum_eq)
qed

lemma Lipschitz_imp_absolutely_continuous:
  assumes "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> norm (f x - f y) \<le> B * \<bar>x - y\<bar>"
  shows "absolutely_continuous_on S f"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
proof (intro allI impI)
  fix \<epsilon> :: real assume "\<epsilon> > 0"
  show "\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
  proof (cases "B \<le> 0")
    case True
    show ?thesis
    proof (intro exI conjI allI impI)
      show "(1::real) > 0" by simp
    next
      fix d T assume H: "d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < 1"
      then have div: "d division_of T" and sub: "T \<subseteq> S" by auto
      have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>d. B * \<bar>Sup k - Inf k\<bar>)"
      proof (rule sum_mono)
        fix k assume kd: "k \<in> d"
        then obtain u v where uv: "k = cbox u v" and "u \<le> v" "k \<subseteq> T"
          by (metis atLeastatMost_empty_iff box_real(2) cbox_division_memE div)
        then have "u \<in> S" "v \<in> S" using sub by auto
        then have "norm (f v - f u) \<le> B * \<bar>v - u\<bar>" using assms by auto
        then show "norm (f (Sup k) - f (Inf k)) \<le> B * \<bar>Sup k - Inf k\<bar>"
          using uv \<open>u \<le> v\<close> by simp
      qed
      also have "\<dots> \<le> (\<Sum>k\<in>d. 0)"
        by (simp add: True split_mult_neg_le sum_nonpos)
      also have "\<dots> = 0" by simp
      finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>" using \<open>\<epsilon> > 0\<close> by linarith
    qed
  next
    case False
    then have Bpos: "B > 0" by linarith
    show ?thesis
    proof (intro exI conjI allI impI)
      show "\<epsilon> / B > 0" using \<open>\<epsilon> > 0\<close> Bpos by simp
    next
      fix d T assume H: "d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<epsilon> / B"
      then have div: "d division_of T" and sub: "T \<subseteq> S"
        and sm: "(\<Sum>k\<in>d. content k) < \<epsilon> / B" by auto
      have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>d. B * content k)"
      proof (rule sum_mono)
        fix k assume kd: "k \<in> d"
        then obtain u v where uv: "k = cbox u v" and "u \<le> v" "k \<subseteq> T"
          by (metis atLeastatMost_empty_iff box_real(2) cbox_division_memE div)
        then have "u \<in> S" "v \<in> S" using sub uv \<open>u \<le> v\<close> by auto
        then have "norm (f v - f u) \<le> B * \<bar>v - u\<bar>" using assms by auto
        also have "\<dots> = B * content k" using uv \<open>u \<le> v\<close> by (simp add: content_real)
        finally show "norm (f (Sup k) - f (Inf k)) \<le> B * content k"
          using uv \<open>u \<le> v\<close> by simp
      qed
      also have "\<dots> = B * (\<Sum>k\<in>d. content k)" by (simp add: sum_distrib_left)
      also have "\<dots> < B * (\<epsilon> / B)" using sm Bpos by (intro mult_strict_left_mono) auto
      also have "\<dots> = \<epsilon>" using Bpos by simp
      finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>" .
    qed
  qed
qed

subsection \<open>Combining intervals\<close>

lemma absolutely_continuous_on_combine:
  assumes "absolutely_continuous_on {a..c} f"
    and "absolutely_continuous_on {c..b} f" and "a \<le> c" "c \<le> b"
  shows "absolutely_continuous_on {a..b} f"
proof -
  have split: \<open>absolutely_continuous_on {a..b} f =
    (absolutely_continuous_on ({a..b} \<inter> {x. x \<le> c}) f \<and>
     absolutely_continuous_on ({a..b} \<inter> {x. c \<le> x}) f)\<close>
    using operative.Basis_imp[OF operative_absolutely_continuous_on[of f],
      of 1 a b c] by (simp add: Basis_real_def inner_real_def)
  have \<open>{a..b} \<inter> {x::real. x \<le> c} = {a..c}\<close> using assms by auto
  moreover have \<open>{a..b} \<inter> {x::real. c \<le> x} = {c..b}\<close> using assms by auto
  ultimately show ?thesis using split assms by simp
qed

lemma absolutely_continuous_on_division:
  assumes "\<And>k. k \<in> d \<Longrightarrow> absolutely_continuous_on k f"
    "d division_of {a..b}"
  shows "absolutely_continuous_on {a..b} f"
proof -
  have \<open>comm_monoid_set.F (\<and>) True (\<lambda>S. absolutely_continuous_on S f) d
        = absolutely_continuous_on (cbox a b) f\<close>
    using operative.division[OF operative_absolutely_continuous_on assms(2)[unfolded cbox_interval[symmetric]]] .
  then have \<open>(finite d \<longrightarrow> (\<forall>k\<in>d. absolutely_continuous_on k f))
             = absolutely_continuous_on {a..b} f\<close>
    by (simp add: comm_monoid_set_F_and cbox_interval)
  moreover have \<open>finite d\<close> using division_ofD(1)[OF assms(2)] .
  ultimately show ?thesis using assms(1) by simp
qed

subsection \<open>Bilinear and product\<close>

lemma ac_on_bounded_image:
  assumes \<open>absolutely_continuous_on S f\<close> \<open>is_interval S\<close> \<open>bounded S\<close>
  obtains B where \<open>B > 0\<close> \<open>\<And>x. x \<in> S \<Longrightarrow> norm (f x) < B\<close>
proof -
  have \<open>bounded (f ` S)\<close>
    by (intro has_bounded_variation_on_imp_bounded[OF _ assms(2)]
             absolutely_continuous_on_imp_has_bounded_variation_on[OF assms(1,3)])
  then obtain B where \<open>B > 0\<close> \<open>\<And>x. x \<in> S \<Longrightarrow> norm (f x) < B\<close>
    unfolding bounded_pos_less by (fastforce simp: image_iff)
  then show ?thesis using that by blast
qed

lemma absolutely_continuous_on_bilinear:
  fixes h :: \<open>'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::euclidean_space\<close>
    and f :: \<open>real \<Rightarrow> 'a\<close> and g :: \<open>real \<Rightarrow> 'b\<close>
  assumes \<open>bilinear h\<close> 
    and f: \<open>absolutely_continuous_on S f\<close> 
    and g: \<open>absolutely_continuous_on S g\<close> 
    and S: \<open>is_interval S\<close> \<open>bounded S\<close>
  shows \<open>absolutely_continuous_on S (\<lambda>x. h (f x) (g x))\<close>
proof -
  obtain B1 where \<open>B1 > 0\<close> and f_bound: \<open>\<And>x. x \<in> S \<Longrightarrow> norm (f x) < B1\<close>
    using ac_on_bounded_image[OF f S] by blast
  obtain B2 where \<open>B2 > 0\<close> and g_bound: \<open>\<And>x. x \<in> S \<Longrightarrow> norm (g x) < B2\<close>
    using ac_on_bounded_image[OF g S] by blast
  obtain K where \<open>K > 0\<close> and K: \<open>\<And>x y. norm (h x y) \<le> K * norm x * norm y\<close>
    using bilinear_bounded_pos[OF assms(1)] by auto
  note bl = bilinear_ladd[OF assms(1)] bilinear_radd[OF assms(1)]
    bilinear_lsub[OF assms(1)] bilinear_rsub[OF assms(1)]
  have decomp: \<open>h (f (Sup k)) (g (Sup k)) - h (f (Inf k)) (g (Inf k)) =
    h (f (Sup k) - f (Inf k)) (g (Sup k)) + h (f (Inf k)) (g (Sup k) - g (Inf k))\<close> for k
    by (simp add: bl algebra_simps)
  show ?thesis
    unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
    have eB2K: \<open>\<epsilon>/2 / B2 / K > 0\<close> using \<open>\<epsilon> > 0\<close> \<open>B2 > 0\<close> \<open>K > 0\<close> by simp
    have eB1K: \<open>\<epsilon>/2 / B1 / K > 0\<close> using \<open>\<epsilon> > 0\<close> \<open>B1 > 0\<close> \<open>K > 0\<close> by simp
    obtain \<delta>1 where \<open>\<delta>1 > 0\<close> and \<delta>1: \<open>\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> S \<Longrightarrow>
      (\<Sum>k\<in>d. content k) < \<delta>1 \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>/2 / B2 / K\<close>
      using f unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
      using eB2K by (meson order.strict_trans2)
    obtain \<delta>2 where \<open>\<delta>2 > 0\<close> and \<delta>2: \<open>\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> S \<Longrightarrow>
      (\<Sum>k\<in>d. content k) < \<delta>2 \<Longrightarrow> (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) < \<epsilon>/2 / B1 / K\<close>
      using g unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
      using eB1K by (meson order.strict_trans2)
    show \<open>\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm (h (f (Sup k)) (g (Sup k)) - h (f (Inf k)) (g (Inf k)))) < \<epsilon>\<close>
    proof (intro exI conjI allI impI)
      show \<open>min \<delta>1 \<delta>2 > 0\<close> using \<open>\<delta>1 > 0\<close> \<open>\<delta>2 > 0\<close> by simp
    next
      fix d T assume H: \<open>d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < min \<delta>1 \<delta>2\<close>
      then have div: \<open>d division_of T\<close> and sub: \<open>T \<subseteq> S\<close>
        and meas: \<open>(\<Sum>k\<in>d. content k) < \<delta>1\<close> \<open>(\<Sum>k\<in>d. content k) < \<delta>2\<close> by auto
      have fin: \<open>finite d\<close> using division_of_finite[OF div] .
      have mem_s: \<open>Sup k \<in> S\<close> \<open>Inf k \<in> S\<close> if kd: \<open>k \<in> d\<close> for k
      proof -
        obtain u v where uv: "k = cbox u v" and "u \<le> v" "k \<subseteq> T"
          by (metis atLeastatMost_empty_iff cbox_division_memE cbox_interval div kd)
        then show \<open>Sup k \<in> S\<close> \<open>Inf k \<in> S\<close>
          using sub by (auto simp: interval_bounds_real)
      qed
      \<comment> \<open>Main inequality chain\<close>
      have \<open>(\<Sum>k\<in>d. norm (h (f (Sup k)) (g (Sup k)) - h (f (Inf k)) (g (Inf k))))
        = (\<Sum>k\<in>d. norm (h (f (Sup k) - f (Inf k)) (g (Sup k)) +
                       h (f (Inf k)) (g (Sup k) - g (Inf k))))\<close>
        by (simp add: decomp)
      also have \<open>\<dots> \<le> (\<Sum>k\<in>d. norm (h (f (Sup k) - f (Inf k)) (g (Sup k))) +
                             norm (h (f (Inf k)) (g (Sup k) - g (Inf k))))\<close>
        by (intro sum_mono norm_triangle_ineq)
      also have \<open>\<dots> \<le> (\<Sum>k\<in>d. K * norm (f (Sup k) - f (Inf k)) * norm (g (Sup k)) +
                             K * norm (f (Inf k)) * norm (g (Sup k) - g (Inf k)))\<close>
        by (intro sum_mono add_mono K)
      also have \<open>\<dots> \<le> (\<Sum>k\<in>d. K * norm (f (Sup k) - f (Inf k)) * B2 +
                             K * B1 * norm (g (Sup k) - g (Inf k)))\<close>
      proof (intro sum_mono add_mono mult_left_mono mult_right_mono)
        fix k assume kd: \<open>k \<in> d\<close>
        show \<open>norm (g (Sup k)) \<le> B2\<close>
          using g_bound[OF mem_s(1)[OF kd]] by linarith
        show \<open>norm (f (Inf k)) \<le> B1\<close>
          using f_bound[OF mem_s(2)[OF kd]] by linarith
      qed (use \<open>K > 0\<close> in auto)
      also have \<open>\<dots> = K * B2 * (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) +
                      K * B1 * (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))\<close>
        by (simp add: sum.distrib sum_distrib_left algebra_simps)
      also have \<open>\<dots> < \<epsilon>\<close>
        using \<delta>1[OF div sub meas(1)] \<delta>2[OF div sub meas(2)] \<open>K > 0\<close> \<open>B1 > 0\<close> \<open>B2 > 0\<close>
        by (simp add: field_simps)
      finally show \<open>(\<Sum>k\<in>d. norm (h (f (Sup k)) (g (Sup k)) - h (f (Inf k)) (g (Inf k)))) < \<epsilon>\<close> .
    qed
  qed
qed

lemma absolutely_continuous_on_mul:
  fixes f :: \<open>real \<Rightarrow> real\<close> and g :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>absolutely_continuous_on S f\<close>
    \<open>absolutely_continuous_on S g\<close>
    \<open>is_interval S\<close> \<open>bounded S\<close>
  shows \<open>absolutely_continuous_on S (\<lambda>x. f x *\<^sub>R g x)\<close>
  using absolutely_continuous_on_bilinear
    [OF bilinear_conv_bounded_bilinear[THEN iffD2, OF bounded_bilinear_scaleR] assms] .

lemma absolutely_continuous_on_vsum:
  assumes \<open>finite k\<close>
    \<open>\<And>i. i \<in> k \<Longrightarrow> absolutely_continuous_on S (f i)\<close>
  shows \<open>absolutely_continuous_on S (\<lambda>x. \<Sum>i\<in>k. f i x)\<close>
  using assms
proof (induction k rule: finite_induct)
  case empty
  then show ?case by (simp add: absolutely_continuous_on_const)
next
  case (insert a F)
  then have \<open>absolutely_continuous_on S (f a)\<close>
    and \<open>absolutely_continuous_on S (\<lambda>x. \<Sum>i\<in>F. f i x)\<close> by auto
  then show ?case using insert.hyps
    by (simp add: absolutely_continuous_on_add)
qed

lemma absolutely_continuous_on_sing:
  \<open>absolutely_continuous_on {a} f\<close>
  using absolutely_continuous_on_null[of a a f] by (simp add: content_real_eq_0)


subsection \<open>Fundamental theorem of calculus\<close>

text \<open>
  Strong form of the fundamental theorem of calculus (Bartle's theorem).
  The derivative @{term f'} need only exist outside a negligible set @{term S},
  provided the \<open>Henstock–Sacks\<close> condition holds: for every @{term \<open>\<epsilon> > 0\<close>}
  there is a gauge witnessing that the oscillation of @{term f} over any
  fine tagged partial division with all tags in @{term S} is small.
\<close>

theorem fundamental_theorem_of_calculus_Bartle:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close> and f' :: \<open>real \<Rightarrow> 'a\<close>
  assumes neg: \<open>negligible S\<close>
    and \<open>a \<le> b\<close>
    and deriv: \<open>\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})\<close>
    and HS: \<open>\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow>
                  \<exists>g. gauge g \<and>
                    (\<forall>p. p tagged_partial_division_of cbox a b \<and> g fine p \<and> fst ` p \<subseteq> S \<longrightarrow>
                      norm (\<Sum>(x,k)\<in>p. f (Sup k) - f (Inf k)) < \<epsilon>)\<close>
  shows \<open>(f' has_integral (f b - f a)) {a..b}\<close>
proof (cases \<open>a<b\<close>)
  case True
  define g where \<open>g \<equiv> (\<lambda>x. if x \<in> S then 0 else f' x)\<close>
  show ?thesis
  proof (rule has_integral_spike [OF neg])
   show "(g has_integral f b - f a) {a..b}"
      unfolding has_integral_real
    proof (intro strip)
      fix \<epsilon> :: real
      assume "0 < \<epsilon>"
      then obtain g1 where \<open>gauge g1\<close> 
           and g1: \<open>\<And>p. \<lbrakk>p tagged_partial_division_of cbox a b; g1 fine p; fst ` p \<subseteq> S\<rbrakk>
                   \<Longrightarrow> norm (\<Sum>(x,k)\<in>p. f (Sup k) - f (Inf k)) < \<epsilon>/2\<close>
        using HS[of \<open>\<epsilon>/2\<close>] by force
      have \<open>\<exists>d>0. (x \<in> {a..b} - S \<longrightarrow>
              (\<forall>y. \<bar>y - x\<bar> < d \<and> y \<in> {a..b} \<longrightarrow>
                norm (f y - f x - (y - x) *\<^sub>R g x) \<le> \<epsilon>/2 / (b-a) * \<bar>y - x\<bar>))\<close> for x
      proof (cases \<open>x \<in> {a..b} - S\<close>)
        case False
        then show ?thesis
          by (intro exI[of _ 1]) auto
      next
        case True
        then have \<open>(f has_derivative (\<lambda>h. h *\<^sub>R f' x)) (at x within {a..b})\<close>
          using deriv has_vector_derivative_def by blast
        moreover have \<open>0 < \<epsilon>/2 / (b-a)\<close>
          using \<open>0 < \<epsilon>\<close> \<open>a < b\<close> by simp
        ultimately obtain d where \<open>d > 0\<close>
          and d: \<open>\<And>y. y \<in> {a..b} \<Longrightarrow> norm (y - x) < d \<Longrightarrow>
                       norm (f y - f x - (y - x) *\<^sub>R f' x) \<le> \<epsilon>/2 / (b-a) * norm (y - x)\<close>
          unfolding has_derivative_within_alt by blast
        have gx: \<open>g x = f' x\<close>
          using True by (simp add: g_def)
        show ?thesis
          using \<open>0 < d\<close> d gx by auto
      qed
      then obtain d where dpos: \<open>\<And>x. d x >0\<close>
          and D: \<open>\<And>x. x \<in> {a..b} - S \<longrightarrow>
                      (\<forall>y. \<bar>y - x\<bar> < d x \<and> y \<in> {a..b} \<longrightarrow>
                      norm (f y - f x - (y - x) *\<^sub>R g x) \<le> \<epsilon>/2 / (b-a) * \<bar>y - x\<bar>)\<close>
        by metis
      define \<gamma> where \<open>\<gamma> \<equiv> \<lambda>x. g1 x \<inter> ball x (d x)\<close>
      show "\<exists>\<gamma>. gauge \<gamma> \<and> (\<forall>\<D>. \<D> tagged_division_of {a..b} \<and> \<gamma> fine \<D> \<longrightarrow> norm ((\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R g x) - (f b - f a)) < \<epsilon>)"
      proof (intro exI conjI strip)
        show "gauge \<gamma>"
          by (simp add: \<gamma>_def \<open>gauge g1\<close> dpos gauge_Int gauge_ball_dependent)
      next
        fix \<D> :: "(real \<times> real set) set"
        assume \<D>: "\<D> tagged_division_of {a..b} \<and> \<gamma> fine \<D>"
        then have *: \<open>(\<Sum>(x, K)\<in>\<D>. f (Sup K) - f (Inf K)) = f b - f a\<close>
          by (simp add: additive_tagged_division_1 assms)
        show "norm ((\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R g x) - (f b - f a)) < \<epsilon>"
        proof -
          have tpd: \<open>\<D> tagged_partial_division_of cbox a b\<close>
            using \<D> tagged_division_of_def by auto
          have g1_fine: \<open>g1 fine \<D>\<close>
            using \<D> unfolding \<gamma>_def by (auto simp: fine_Int)
          have ball_fine: \<open>(\<lambda>x. ball x (d x)) fine \<D>\<close>
            using \<D> unfolding \<gamma>_def by (auto simp: fine_Int)
          have \<D>_split: \<open>\<D> = {(x,k) \<in> \<D>. x \<in> S} \<union> {(x,k) \<in> \<D>. x \<notin> S}\<close>
            by auto
          define \<D>S where \<open>\<D>S \<equiv> {(x,k) \<in> \<D>. x \<in> S}\<close>
          define \<D>N where \<open>\<D>N \<equiv> {(x,k) \<in> \<D>. x \<notin> S}\<close>
          have sum_len: \<open>(\<Sum>(x, K)\<in>\<D>. Sup K - Inf K) = b - a\<close>
            using additive_tagged_division_1[OF \<open>a \<le> b\<close>] \<D> by force
          \<comment> \<open>S-component: $< \varepsilon/2$\<close>
          have S_bound: \<open>norm (\<Sum>(x,k)\<in>\<D>S. f (Sup k) - f (Inf k)) < \<epsilon>/2\<close>
          proof (rule g1)
            show \<open>\<D>S tagged_partial_division_of cbox a b\<close>
              unfolding \<D>S_def using tpd tagged_partial_division_subset
              using \<D>_split by auto
            show \<open>g1 fine \<D>S\<close>
              using g1_fine fine_subset by (force simp: \<D>S_def fine_def)
            show \<open>fst ` \<D>S \<subseteq> S\<close>
              unfolding \<D>S_def by force
          qed
          \<comment> \<open>Non-S-component: $\le \varepsilon/2$\<close>
          have N_bound: \<open>norm (\<Sum>(x,k)\<in>\<D>N. content k *\<^sub>R g x - (f (Sup k) - f (Inf k))) \<le> \<epsilon>/2\<close> (is "?L \<le> _")
          proof -
            \<comment> \<open>Fact 1: norm bound by per-element derivative bound\<close>
            have step1: \<open>?L \<le> (\<Sum>(x,k)\<in>\<D>N. \<epsilon>/2 / (b-a) * (Sup k - Inf k))\<close>
            proof (rule sum_norm_le)
              fix xk assume xk_in: \<open>xk \<in> \<D>N\<close>
              obtain x k where xk: \<open>xk = (x, k)\<close> and mem: \<open>(x, k) \<in> \<D>\<close> \<open>x \<notin> S\<close>
                using \<D>N_def xk_in by blast
              from \<D> mem obtain c e where k_eq: \<open>k = {c..e}\<close> and xk_props: \<open>x \<in> k\<close> \<open>k \<subseteq> {a..b}\<close>
                by (metis box_real(2) tagged_division_ofD(2-4))
              with xk_props have ce: \<open>c \<le> e\<close> \<open>c \<le> x\<close> \<open>x \<le> e\<close> 
                by auto
              have sup_k: \<open>Sup k = e\<close> and inf_k: \<open>Inf k = c\<close>
                using ce by (auto simp: k_eq)
              have cont: \<open>content k = Sup k - Inf k\<close>
                using ce content_real k_eq sup_k inf_k by auto
              have x_ab: \<open>x \<in> {a..b} - S\<close> using xk_props mem by auto
              \<comment> \<open>From ball-fineness: @{term \<open>Sup k\<close>} and @{term \<open>Inf k\<close>} are within @{term \<open>d x\<close>} of @{term x}\<close>
              have k_ball: \<open>k \<subseteq> ball x (d x)\<close>
                using ball_fine mem unfolding fine_def by auto
              have sup_in: \<open>Sup k \<in> k\<close> using ce by (auto simp: k_eq)
              have inf_in: \<open>Inf k \<in> k\<close> using ce by (auto simp: k_eq)
              have sup_ab: \<open>Sup k \<in> {a..b}\<close> using sup_in xk_props by auto
              have inf_ab: \<open>Inf k \<in> {a..b}\<close> using inf_in xk_props by auto
              have sup_near: \<open>\<bar>Sup k - x\<bar> < d x\<close>
                using k_ball sup_in by (auto simp: dist_real_def)
              have inf_near: \<open>\<bar>Inf k - x\<bar> < d x\<close>
                using k_ball inf_in by (auto simp: dist_real_def)
              \<comment> \<open>Apply derivative bound @{term D} at @{term \<open>Sup k\<close>} and @{term \<open>Inf k\<close>}\<close>
              have bnd_sup: \<open>norm (f (Sup k) - f x - (Sup k - x) *\<^sub>R g x)
                            \<le> \<epsilon>/2 / (b-a) * \<bar>Sup k - x\<bar>\<close>
                using D x_ab sup_near sup_ab by auto
              have bnd_inf: \<open>norm (f (Inf k) - f x - (Inf k - x) *\<^sub>R g x)
                            \<le> \<epsilon>/2 / (b-a) * \<bar>Inf k - x\<bar>\<close>
                using D x_ab inf_near inf_ab by auto
              \<comment> \<open>Algebraic decomposition\<close>
              have decomp: \<open>content k *\<^sub>R g x - (f (Sup k) - f (Inf k))
                          = (f (Inf k) - f x - (Inf k - x) *\<^sub>R g x)
                          - (f (Sup k) - f x - (Sup k - x) *\<^sub>R g x)\<close>
                by (simp add: cont sup_k inf_k algebra_simps)
              \<comment> \<open>Triangle inequality + derivative bounds\<close>
              have \<open>norm (content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))
                  \<le> norm (f (Inf k) - f x - (Inf k - x) *\<^sub>R g x)
                   + norm (f (Sup k) - f x - (Sup k - x) *\<^sub>R g x)\<close>
                unfolding decomp by (rule norm_triangle_ineq4)
              also have \<open>\<dots> \<le> \<epsilon>/2 / (b-a) * \<bar>Inf k - x\<bar> + \<epsilon>/2 / (b-a) * \<bar>Sup k - x\<bar>\<close>
                using bnd_inf bnd_sup by linarith
              also have \<open>\<dots> = \<epsilon>/2 / (b-a) * (Sup k - Inf k)\<close>
                by (simp add: ce(2,3) inf_k right_diff_distrib' sup_k)
              finally show \<open>norm (case xk of (x,k) \<Rightarrow> content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))
                          \<le> (case xk of (x,k) \<Rightarrow> \<epsilon>/2 / (b-a) * (Sup k - Inf k))\<close>
                by (simp add: xk)
            qed
            \<comment> \<open>Fact 2: subset monotonicity of nonneg sum\<close>
            have step2: \<open>(\<Sum>(x,k)\<in>\<D>N. \<epsilon>/2 / (b-a) * (Sup k - Inf k))
                        \<le> (\<Sum>(x,k)\<in>\<D>.  \<epsilon>/2 / (b-a) * (Sup k - Inf k))\<close>
            proof (rule sum_mono2)
              show \<open>finite \<D>\<close> using tagged_division_of_finite \<D> by metis
              show \<open>\<D>N \<subseteq> \<D>\<close> unfolding \<D>N_def by auto
              fix xk assume \<open>xk \<in> \<D> - \<D>N\<close>
              then obtain x k where \<open>xk = (x,k)\<close> \<open>(x,k) \<in> \<D>\<close> by (cases xk) auto
              then obtain c e where \<open>k = cbox c e\<close> \<open>c \<le> e\<close>
                using tagged_division_ofD(4,2) \<D>
                by (smt (verit) atLeastAtMost_iff box_real(2) subset_iff)
              then have \<open>Sup k \<ge> Inf k\<close> by simp
              then show \<open>0 \<le> (case xk of (x,k) \<Rightarrow> \<epsilon>/2 / (b-a) * (Sup k - Inf k))\<close>
                using \<open>0 < \<epsilon>\<close> True \<open>xk = (x,k)\<close> by (auto intro!: mult_nonneg_nonneg)
            qed
            have sum_eq: \<open>(\<Sum>(x,k)\<in>\<D>. \<epsilon>/2 / (b-a) * (Sup k - Inf k)) = \<epsilon>/2 / (b-a) * (b-a)\<close>
              by (smt (verit) case_prod_unfold divide_divide_eq_left sum.cong sum_distrib_left sum_len)
            have \<open>?L \<le> \<epsilon>/2 / (b-a) * (b-a)\<close>
              using step1 step2 sum_eq by linarith
            also have \<open>\<dots> = \<epsilon>/2\<close>
              using True divide_eq_eq by fastforce
            finally show ?thesis .
          qed
          \<comment> \<open>Combine the two halves\<close>
          have fin\<D>: \<open>finite \<D>\<close> using tagged_division_of_finite \<D> by metis
          have disj: \<open>\<D>S \<inter> \<D>N = {}\<close> unfolding \<D>S_def \<D>N_def by auto
          have union: \<open>\<D> = \<D>S \<union> \<D>N\<close> unfolding \<D>S_def \<D>N_def using \<D>_split by auto
          have fin_S: \<open>finite \<D>S\<close> and fin_N: \<open>finite \<D>N\<close>
            using fin\<D> union by (auto intro: finite_subset)
          \<comment> \<open>Rewrite goal using * and combine sums\<close>
          have \<open>norm ((\<Sum>(x,k)\<in>\<D>. content k *\<^sub>R g x) - (f b - f a))
              = norm (\<Sum>(x,k)\<in>\<D>. content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))\<close>
            by (smt (verit) "*" split_def sum.cong sum_subtractf)
          \<comment> \<open>Split into @{term S} and non-@{term S} parts\<close>
          also have \<open>\<dots> = norm ((\<Sum>(x,k)\<in>\<D>S. content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))
                            + (\<Sum>(x,k)\<in>\<D>N. content k *\<^sub>R g x - (f (Sup k) - f (Inf k))))\<close>
            by (simp add: sum.union_disjoint[OF fin_S fin_N disj, symmetric] union)
          \<comment> \<open>On @{term \<D>S}, @{term \<open>g x = 0\<close>} so @{term \<open>content k *\<^sub>R g x = 0\<close>}\<close>
          also have \<open>(\<Sum>(x,k)\<in>\<D>S. content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))
                   = (\<Sum>(x,k)\<in>\<D>S. f (Inf k) - f (Sup k))\<close>
          proof (rule sum.cong[OF refl])
            fix xk assume \<open>xk \<in> \<D>S\<close>
            then obtain x k where \<open>xk = (x,k)\<close> \<open>x \<in> S\<close> 
              unfolding \<D>S_def by auto
            then show \<open>(case xk of (x,k) \<Rightarrow> content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))
                     = (case xk of (x,k) \<Rightarrow> (f (Inf k) - f (Sup k)))\<close>
              by (simp add: g_def split: prod.splits)
          qed
          also have \<open>\<dots> = - (\<Sum>(x,k)\<in>\<D>S. f (Sup k) - f (Inf k))\<close>
            by (simp add: split_def sum_subtractf)
          also have \<open>norm (- (\<Sum>(x,k)\<in>\<D>S. f (Sup k) - f (Inf k))
                         + (\<Sum>(x,k)\<in>\<D>N. content k *\<^sub>R g x - (f (Sup k) - f (Inf k))))
                   \<le> norm (\<Sum>(x,k)\<in>\<D>S. f (Sup k) - f (Inf k))
                    + norm (\<Sum>(x,k)\<in>\<D>N. content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))\<close>
            using norm_add_rule_thm norm_imp_pos_and_ge norm_minus_cancel by blast
          also have \<open>\<dots> < \<epsilon>/2 + \<epsilon>/2\<close>
            using S_bound N_bound by linarith
          also have \<open>\<dots> = \<epsilon>\<close> by simp
          finally show ?thesis .
        qed
      qed
    qed
  qed (auto simp: g_def)
qed (use \<open>a \<le> b\<close> in auto)

lemma negligible_content_gauge:
  fixes a b :: real
  assumes \<open>negligible S\<close> \<open>\<delta> > 0\<close>
  shows \<open>\<exists>g. gauge g \<and>
    (\<forall>p. p tagged_partial_division_of cbox a b \<and> g fine p \<and> fst ` p \<subseteq> S \<longrightarrow>
      (\<Sum>(x,k)\<in>p. content k) < \<delta>)\<close>
proof -
  have int: \<open>(indicat_real S has_integral 0) (cbox a b)\<close>
    using assms(1) negligible_def by blast
  then have intble: \<open>indicat_real S integrable_on cbox a b\<close>
    by (rule has_integral_integrable)
  obtain \<gamma> where \<open>gauge \<gamma>\<close> and \<gamma>:
    \<open>\<And>p. \<lbrakk>p tagged_partial_division_of cbox a b; \<gamma> fine p\<rbrakk>
     \<Longrightarrow> (\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R indicat_real S x - integral k (indicat_real S))) < \<delta>\<close>
    using Henstock_lemma[OF intble \<open>\<delta> > 0\<close>] by blast
  show ?thesis
  proof (intro exI conjI allI impI)
    show \<open>gauge \<gamma>\<close> by fact
    fix p assume p: \<open>p tagged_partial_division_of cbox a b \<and> \<gamma> fine p \<and> fst ` p \<subseteq> S\<close>
    have eq: \<open>content k *\<^sub>R indicat_real S x - integral k (indicat_real S) = content k\<close>
      if \<open>(x, k) \<in> p\<close> for x k
    proof -
      from p that have \<open>x \<in> S\<close> by force
      then have \<open>indicat_real S x = 1\<close> by (simp add: indicator_def)
      moreover have \<open>integral k (indicat_real S) = 0\<close>
        by (metis assms(1) integral_unique negligible_def p tagged_partial_division_ofD(4)
            that)
      ultimately show ?thesis by simp
    qed
    have \<open>(\<Sum>(x,k)\<in>p. content k) = (\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R indicat_real S x - integral k (indicat_real S)))\<close>
      using eq content_pos_le
      by (intro sum.cong[OF refl]) fastforce
    then show \<open>(\<Sum>(x,k)\<in>p. content k) < \<delta>\<close>
      using \<gamma> p by presburger
  qed
qed

lemma absolutely_continuous_on_imp_Henstock_Sacks:
  assumes \<open>negligible S\<close> \<open>absolutely_continuous_on {a..b} f\<close> \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>g. gauge g \<and>
    (\<forall>p. p tagged_partial_division_of cbox a b \<and> g fine p \<and> fst ` p \<subseteq> S \<longrightarrow>
      norm (\<Sum>(x,k)\<in>p. f (Sup k) - f (Inf k)) < \<epsilon>)\<close>
proof -
  define F where \<open>F \<equiv> \<lambda>k. f (Sup k) - f (Inf k)\<close>
  from assms(2) have ac: \<open>absolutely_setcontinuous_on F {a..b}\<close>
    unfolding absolutely_continuous_on_def F_def .
  then obtain \<delta> where \<open>\<delta> > 0\<close> and \<delta>:
    \<open>\<And>d T. \<lbrakk>d division_of T; T \<subseteq> {a..b}; sum content d < \<delta>\<rbrakk> \<Longrightarrow> (\<Sum>k\<in>d. norm (F k)) < \<epsilon>\<close>
    using assms(3) unfolding absolutely_setcontinuous_on_def by meson
  obtain g where \<open>gauge g\<close> and g:
    \<open>\<And>p. \<lbrakk>p tagged_partial_division_of cbox a b; g fine p; fst ` p \<subseteq> S\<rbrakk>
      \<Longrightarrow> (\<Sum>(x,k)\<in>p. content k) < \<delta>\<close>
    using negligible_content_gauge[OF assms(1) \<open>\<delta> > 0\<close>, of a b] by auto
  show ?thesis
  proof (intro exI conjI allI impI)
    show \<open>gauge g\<close> by fact
    fix p assume asm: \<open>p tagged_partial_division_of cbox a b \<and> g fine p \<and> fst ` p \<subseteq> S\<close>
    then have pd: \<open>p tagged_partial_division_of cbox a b\<close> and fine: \<open>g fine p\<close>
      and tags: \<open>fst ` p \<subseteq> S\<close> by auto
    have inj: \<open>inj_on snd p\<close>
    proof (rule inj_onI)
      fix xk1 xk2 assume \<open>xk1 \<in> p\<close> \<open>xk2 \<in> p\<close> \<open>snd xk1 = snd xk2\<close>
      then obtain x1 K1 x2 K2 where eq: \<open>xk1 = (x1, K1)\<close> \<open>xk2 = (x2, K2)\<close> \<open>K1 = K2\<close>
        by (metis prod.collapse)
      show \<open>xk1 = xk2\<close>
      proof (rule ccontr)
        assume \<open>xk1 \<noteq> xk2\<close>
        with eq \<open>xk1 \<in> p\<close> \<open>xk2 \<in> p\<close> pd
        have \<open>interior K1 \<inter> interior K2 = {}\<close>
          using tagged_partial_division_ofD(5) by blast
        with eq have \<open>interior K1 = {}\<close> by auto
        moreover from \<open>xk1 \<in> p\<close> pd eq obtain c d where \<open>K1 = cbox c d\<close>
          using tagged_partial_division_ofD(4) by blast
        ultimately have \<open>box c d = {}\<close> using interior_cbox by metis
        moreover from \<open>xk1 \<in> p\<close> pd eq have \<open>x1 \<in> K1\<close> using tagged_partial_division_ofD(2) by blast
        moreover from \<open>xk2 \<in> p\<close> pd eq have \<open>x2 \<in> K1\<close> using tagged_partial_division_ofD(2) by blast
        ultimately have \<open>x1 = x2\<close> using \<open>K1 = cbox c d\<close> by (simp add: mem_box)
        with eq show False using \<open>xk1 \<noteq> xk2\<close> by auto
      qed
    qed
    have div: \<open>snd ` p division_of \<Union>(snd ` p)\<close>
      using partial_division_of_tagged_division[OF pd] .
    have sub: \<open>\<Union>(snd ` p) \<subseteq> {a..b}\<close>
      using asm tagged_partial_division_ofD(3) by fastforce
    have content_bound: \<open>sum content (snd ` p) < \<delta>\<close>
      by (metis (no_types, lifting) asm case_prod_unfold g inj sum.reindex_cong)
    have \<open>(\<Sum>k\<in>snd ` p. norm (F k)) < \<epsilon>\<close>
      using \<delta>[OF div sub content_bound] .
    then have \<open>(\<Sum>(x,k)\<in>p. norm (F k)) < \<epsilon>\<close>
      using sum.reindex[OF inj, of \<open>\<lambda>k. norm (F k)\<close>] by (simp add: o_def case_prod_unfold)
    then show \<open>norm (\<Sum>(x,k)\<in>p. f (Sup k) - f (Inf k)) < \<epsilon>\<close>
      unfolding F_def
      by (smt (verit) case_prod_unfold sum_norm_le)
  qed
qed

theorem fundamental_theorem_of_calculus_absolutely_continuous:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "negligible S" "a \<le> b"
    "absolutely_continuous_on {a..b} f"
    and fvd: "\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})"
  shows "(f' has_integral (f b - f a)) {a..b}"
proof (intro fundamental_theorem_of_calculus_Bartle)
  fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
  \<comment> \<open>Need: @{term absolutely_continuous_on} implies the Henstock–Sacks condition\<close>
  show \<open>\<exists>g. gauge g \<and>
        (\<forall>p. p tagged_partial_division_of cbox a b \<and> g fine p \<and> fst ` p \<subseteq> S \<longrightarrow>
          norm (\<Sum>(x,k)\<in>p. f (Sup k) - f (Inf k)) < \<epsilon>)\<close>
    using \<open>0 < \<epsilon>\<close> absolutely_continuous_on_imp_Henstock_Sacks assms(1,3) by fastforce
qed (use assms in auto)

subsection \<open>Closure and interior\<close>

lemma absolutely_continuous_on_interior:
  assumes abc: "absolutely_continuous_on (interior S) f" 
    and contf: "continuous_on S f" 
  shows "absolutely_continuous_on S f"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
proof (intro allI impI)
  fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
  then have \<open>\<epsilon>/2 > 0\<close> by simp

  from abc[unfolded absolutely_continuous_on_def absolutely_setcontinuous_on_def]
  have \<open>\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> interior S \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>\<close> .
  from this[rule_format, OF \<open>\<epsilon>/2 > 0\<close>]
  obtain r where \<open>r > 0\<close> and
    r_int: \<open>\<forall>d T. d division_of T \<and> T \<subseteq> interior S \<and> (\<Sum>k\<in>d. content k) < r \<longrightarrow>
      (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>/2\<close>
    by auto
  have r_int': \<open>(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>/2\<close>
    if \<open>d division_of \<Union>d\<close> \<open>\<Union>d \<subseteq> interior S\<close> \<open>(\<Sum>k\<in>d. content k) < r\<close> for d
    using r_int that by blast
  show \<open>\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>\<close>
  proof (rule exI[of _ r], intro conjI allI impI)
    show \<open>r > 0\<close> by fact
  next
    fix d T
    assume H: \<open>d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < r\<close>
    have dt: \<open>d division_of T\<close> and ts: \<open>T \<subseteq> S\<close> and content_small: \<open>(\<Sum>k\<in>d. content k) < r\<close>
      using H by auto
    show \<open>(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>\<close>
    proof -
      have fin_d: \<open>finite d\<close> using dt division_of_finite by blast
      \<comment> \<open>Define the sequence of shrunken sums: shrink each interval K by $1/2^n$ on each side\<close>
      define \<sigma> where \<open>\<sigma> n = (\<Sum>K\<in>d. norm (f (Sup K - (Sup K - Inf K) / 2^n) -
        f (Inf K + (Sup K - Inf K) / 2^n)))\<close> for n :: nat
      \<comment> \<open>The target sum\<close>
      define L where \<open>L = (\<Sum>K\<in>d. norm (f (Sup K) - f (Inf K)))\<close>
      \<comment> \<open>Convergence: @{term \<sigma>} $n \to$ @{term L} as $n \to \infty$\<close>
      have conv: \<open>\<sigma> \<longlonglongrightarrow> L\<close>
      proof -
        \<comment> \<open>Pointwise convergence of each summand\<close>
        have summand_conv: \<open>(\<lambda>n. norm (f (Sup K - (Sup K - Inf K) / 2^n) -
          f (Inf K + (Sup K - Inf K) / 2^n))) \<longlonglongrightarrow> norm (f (Sup K) - f (Inf K))\<close>
          if \<open>K \<in> d\<close> for K
        proof (intro tendsto_norm tendsto_diff)
          obtain a b where Kab: \<open>K = cbox a b\<close> and \<open>K \<subseteq> S\<close> \<open>a \<le> b\<close>
            using division_ofD dt \<open>K \<in> d\<close>
            by (metis H atLeastatMost_empty_iff2 box_real(2) subset_trans)
          then obtain InfK: \<open>Inf K = a\<close> and SupK: \<open>Sup K = b\<close> 
                  and endpts: \<open>Inf K \<in> S\<close> \<open>Sup K \<in> S\<close>
            using in_mono by fastforce
          have mid_in_K: \<open>x \<in> K\<close> if \<open>Inf K \<le> x\<close> \<open>x \<le> Sup K\<close> for x
            using that InfK SupK Kab by auto
          have *: \<open>(\<lambda>n. f (x + y / 2^n)) \<longlonglongrightarrow> f x\<close> if \<open>x \<in> S\<close> \<open>\<forall>n. x + y / 2^n \<in> S\<close> for x y
          proof (rule continuous_on_tendsto_compose[OF contf _ that(1)])
            show \<open>(\<lambda>n. x + y / 2^n) \<longlonglongrightarrow> x\<close>
              using tendsto_add[OF tendsto_const, of \<open>\<lambda>n. y / 2^n\<close> 0 sequentially x]
              by (simp add: LIMSEQ_divide_realpow_zero)
            show \<open>\<forall>\<^sub>F n in sequentially. x + y / 2^n \<in> S\<close>
              using that(2) by simp
          qed
          \<comment> \<open>Reduce to: @{term f} at shrunken upper endpoint $\to$ @{term \<open>f (Sup K)\<close>}\<close>
          show \<open>(\<lambda>n. f (Sup K - (Sup K - Inf K) / 2^n)) \<longlonglongrightarrow> f (Sup K)\<close>
          proof -
            have eq: \<open>Sup K - (Sup K - Inf K) / 2^n = Sup K + (Inf K - Sup K) / 2^n\<close> for n :: nat
              by (simp add: field_simps)
            have \<open>\<forall>n. Sup K + (Inf K - Sup K) / 2^n \<in> S\<close>
            proof
              fix n :: nat
              have \<open>(Sup K - Inf K) * 1 \<le> (Sup K - Inf K) * 2^n\<close>
                using \<open>a \<le> b\<close> InfK SupK by (intro mult_left_mono) auto
              then have \<open>Inf K \<le> Sup K + (Inf K - Sup K) / 2^n\<close>
                by (simp add: field_simps)
              moreover 
              have \<open>(Inf K - Sup K) / 2^n \<le> 0\<close>
                using \<open>a \<le> b\<close> InfK SupK by (intro divide_nonpos_nonneg) auto
              then have \<open>Sup K + (Inf K - Sup K) / 2^n \<le> Sup K\<close>
                by linarith
              ultimately show \<open>Sup K + (Inf K - Sup K) / 2^n \<in> S\<close>
                using mid_in_K \<open>K \<subseteq> S\<close> by auto
            qed
            then show ?thesis using *[OF endpts(2)] by (simp add: eq)
          qed
          \<comment> \<open>Reduce to: @{term f} at shrunken lower endpoint $\to$ @{term \<open>f (Inf K)\<close>}\<close>
          show \<open>(\<lambda>n. f (Inf K + (Sup K - Inf K) / 2^n)) \<longlonglongrightarrow> f (Inf K)\<close>
          proof -
            have \<open>\<forall>n. Inf K + (Sup K - Inf K) / 2^n \<in> S\<close>
            proof
              fix n :: nat
              have \<open>Inf K \<le> Inf K + (Sup K - Inf K) / 2^n\<close>
                by (simp add: InfK SupK \<open>a \<le> b\<close>)
              moreover have \<open>Inf K + (Sup K - Inf K) / 2^n \<le> Sup K\<close>
                by (metis InfK SupK \<open>a \<le> b\<close> dual_order.refl mult_1 one_le_numeral 
                          one_le_power power_0 scaling_mono zero_le_power)
              ultimately show \<open>Inf K + (Sup K - Inf K) / 2^n \<in> S\<close>
                using mid_in_K \<open>K \<subseteq> S\<close> by auto
            qed
            then show ?thesis using *[OF endpts(1)] by simp
          qed
        qed
        \<comment> \<open>Lift pointwise convergence to sum convergence over finite @{term d}\<close>
        show \<open>\<sigma> \<longlonglongrightarrow> L\<close>
          unfolding \<sigma>_def L_def using summand_conv by (rule tendsto_sum)
      qed
      \<comment> \<open>Eventually bounded: @{term \<open>\<sigma> n \<le> \<epsilon>/2\<close>} for all sufficiently large $n$\<close>
      have bound: \<open>\<forall>\<^sub>F n in sequentially. \<sigma> n \<le> \<epsilon>/2\<close>
      proof
        fix n :: nat
        assume "2 \<le> n"
        define d' where \<open>d' \<equiv> (\<lambda>k. cbox (Inf k + (Sup k - Inf k) / 2^n) 
                                         (Sup k - (Sup k - Inf k) / 2^n))
                                      ` {k \<in> d. content k \<noteq> 0}\<close>
        let ?S = \<open>{k \<in> d. content k \<noteq> 0}\<close>
        let ?shrink = \<open>\<lambda>k. cbox (Inf k + (Sup k - Inf k) / 2^n) (Sup k - (Sup k - Inf k) / 2^n)\<close>
        have d'_eq: \<open>d' = ?shrink ` ?S\<close> 
          unfolding d'_def ..
        have fin_S: \<open>finite ?S\<close> using fin_d by auto
            \<comment> \<open>Key properties of each $k$ in @{term \<open>{k \<in> d. content k \<noteq> 0}\<close>}\<close>
        have k_props: \<open>Inf k < Sup k\<close> \<open>k = {Inf k .. Sup k}\<close> \<open>k \<subseteq> S\<close>
          \<open>?shrink k \<subseteq> k\<close> \<open>?shrink k \<noteq> {}\<close>
          if \<open>k \<in> ?S\<close> for k
        proof -
          from that have kd: \<open>k \<in> d\<close> and kcont: \<open>content k \<noteq> 0\<close> by auto
          obtain a b where kab: \<open>k = {a..b}\<close> and \<open>a < b\<close>
            using H content_real_eq_0 kcont kd by auto
          moreover have \<open>Inf k = a\<close> \<open>Sup k = b\<close> using kab \<open>a < b\<close> by auto
          ultimately show \<open>Inf k < Sup k\<close> by auto
          show \<open>k = {Inf k .. Sup k}\<close> using kab \<open>Inf k = a\<close> \<open>Sup k = b\<close> by auto
          show \<open>k \<subseteq> S\<close> using division_ofD(2)[OF dt kd] ts by auto
          have pos: \<open>(Sup k - Inf k) / 2^n > 0\<close> using \<open>Inf k < Sup k\<close> by auto
          have two_le: \<open>(2::real) \<le> 2^n\<close> using \<open>2 \<le> n\<close>
            by (metis One_nat_def le_eq_less_or_eq le_simps(3) numerals(2) one_le_numeral
                power_increasing power_one_right)
          show \<open>?shrink k \<subseteq> k\<close>
            unfolding box_real using pos \<open>k = {Inf k .. Sup k}\<close>
            by fastforce
          have \<open>(Sup k - Inf k) * 2 \<le> (Sup k - Inf k) * 2^n\<close>
            using \<open>Inf k < Sup k\<close> two_le by (intro mult_left_mono) auto
          then have \<open>2 * (Sup k - Inf k) / 2^n \<le> Sup k - Inf k\<close>
            by (simp add: pos_divide_le_eq)
          then show \<open>?shrink k \<noteq> {}\<close>
            by auto
        qed
          \<comment> \<open>Key properties of each $k$ in @{term \<open>{k \<in> d. content k \<noteq> 0}\<close>}\<close>
          \<comment> \<open>Claim 1: @{term d'} is a division of @{term \<open>\<Union>d'\<close>}\<close>
        have \<open>d' division_of \<Union>d'\<close>
          unfolding division_of_def
        proof (intro conjI ballI impI)
          fix K :: "real set"
          assume "K \<in> d'"
          then obtain k where kS: \<open>k \<in> ?S\<close> and Keq: \<open>K = ?shrink k\<close> 
            unfolding d'_eq by auto
          show \<open>K \<noteq> {}\<close> using Keq k_props(5)[OF kS] by auto 
          show "\<exists>a b. K = cbox a b"
            using \<open>K \<in> d'\<close> d'_def by blast
        next
          fix K1 K2
          assume \<open>K1 \<in> d'\<close> \<open>K2 \<in> d'\<close> \<open>K1 \<noteq> K2\<close>
          then obtain k1 k2 where k1S: \<open>k1 \<in> ?S\<close> and K1eq: \<open>K1 = ?shrink k1\<close>
            and k2S: \<open>k2 \<in> ?S\<close> and K2eq: \<open>K2 = ?shrink k2\<close>
            unfolding d'_eq by auto
          have \<open>k1 \<noteq> k2\<close> using \<open>K1 \<noteq> K2\<close> K1eq K2eq by auto
          have \<open>k1 \<in> d\<close> \<open>k2 \<in> d\<close> using k1S k2S by auto
          have \<open>interior k1 \<inter> interior k2 = {}\<close>
            using division_ofD(5)[OF dt \<open>k1 \<in> d\<close> \<open>k2 \<in> d\<close> \<open>k1 \<noteq> k2\<close>] .
          moreover have \<open>interior K1 \<subseteq> interior k1\<close>
            using interior_mono[OF k_props(4)[OF k1S]] K1eq by auto
          moreover have \<open>interior K2 \<subseteq> interior k2\<close>
            using interior_mono[OF k_props(4)[OF k2S]] K2eq by auto
          ultimately show \<open>interior K1 \<inter> interior K2 = {}\<close> by auto
        qed (auto simp: d'_def fin_d Sup_upper)
          \<comment> \<open>Claim 2: @{term \<open>\<Union>d' \<subseteq> interior S\<close>}\<close>
        moreover have \<open>\<Union>d' \<subseteq> interior S\<close>
        proof
          fix x assume \<open>x \<in> \<Union>d'\<close>
          then obtain K k where \<open>K \<in> d'\<close> \<open>x \<in> K\<close> and kS: \<open>k \<in> ?S\<close> and Keq: \<open>K = ?shrink k\<close> 
            unfolding d'_eq by auto
          have \<open>x \<in> interior k\<close>
          proof -
            have \<open>Inf k < Inf k + (Sup k - Inf k) / 2^n\<close>
              using k_props(1)[OF kS] by auto
            moreover have \<open>Sup k - (Sup k - Inf k) / 2^n < Sup k\<close>
              using k_props(1)[OF kS] by auto
            moreover have \<open>x \<in> {Inf k + (Sup k - Inf k) / 2^n .. Sup k - (Sup k - Inf k) / 2^n}\<close>
              using \<open>x \<in> K\<close> Keq box_real by auto
            ultimately have \<open>x \<in> {Inf k <..< Sup k}\<close> by auto
            also have \<open>\<dots> = interior {Inf k .. Sup k}\<close>
              using interior_atLeastAtMost_real by auto
            also have \<open>\<dots> = interior k\<close> using k_props(2)[OF kS] by auto
            finally show ?thesis .
          qed
          also have \<open>interior k \<subseteq> interior S\<close>
            by (rule interior_mono[OF k_props(3)[OF kS]])
          finally show \<open>x \<in> interior S\<close> .
        qed
          \<comment> \<open>Claim 3: total content of @{term d'} $< r$\<close>
        moreover have \<open>(\<Sum>k\<in>d'. content k) < r\<close>
        proof -
          have \<open>(\<Sum>k\<in>d'. content k) \<le> (\<Sum>k\<in>?S. content (?shrink k))\<close>
            unfolding d'_eq using sum_image_le[OF fin_S, of content ?shrink] content_pos_le
            by fastforce
          also have \<open>\<dots> \<le> (\<Sum>k\<in>?S. content k)\<close>
            by (metis (lifting) box_real(2) content_subset k_props(2,4) sum_mono)
          also have \<open>\<dots> \<le> (\<Sum>k\<in>d. content k)\<close>
            by (rule sum_mono2[OF fin_d]) (auto simp: content_pos_le)
          also have \<open>\<dots> < r\<close> using content_small .
          finally show ?thesis .
        qed
          \<comment> \<open>Conclude with @{text r_int'}\<close>
        ultimately have r_int'_d': \<open>(\<Sum>k\<in>d'. norm (f (Sup k) - f (Inf k))) < \<epsilon>/2\<close>
          using r_int by blast
        \<comment> \<open>Injectivity of shrink on @{term \<open>{k \<in> d. content k \<noteq> 0}\<close>}\<close>
        have inj_shrink: \<open>inj_on ?shrink ?S\<close>
        proof (rule inj_onI)
          fix k1 k2
          assume k1S: \<open>k1 \<in> ?S\<close> and k2S: \<open>k2 \<in> ?S\<close> and eq: \<open>?shrink k1 = ?shrink k2\<close>
          show \<open>k1 = k2\<close>
          proof (rule ccontr)
            assume \<open>k1 \<noteq> k2\<close>
            have \<open>k1 \<in> d\<close> \<open>k2 \<in> d\<close> using k1S k2S by auto
            have \<open>interior k1 \<inter> interior k2 = {}\<close>
              using division_ofD(5)[OF dt \<open>k1 \<in> d\<close> \<open>k2 \<in> d\<close> \<open>k1 \<noteq> k2\<close>] .
            moreover have \<open>?shrink k1 \<subseteq> interior k1\<close>
            proof
              fix x assume \<open>x \<in> ?shrink k1\<close>
              then have \<open>x \<in> {Inf k1 + (Sup k1 - Inf k1) / 2^n .. Sup k1 - (Sup k1 - Inf k1) / 2^n}\<close>
                using box_real by auto
              moreover have \<open>Inf k1 < Inf k1 + (Sup k1 - Inf k1) / 2^n\<close>
                using k_props(1)[OF k1S] by auto
              moreover have \<open>Sup k1 - (Sup k1 - Inf k1) / 2^n < Sup k1\<close>
                using k_props(1)[OF k1S] by auto
              ultimately have \<open>x \<in> {Inf k1 <..< Sup k1}\<close> by auto
              also have \<open>\<dots> = interior {Inf k1 .. Sup k1}\<close>
                using interior_atLeastAtMost_real by auto
              also have \<open>\<dots> = interior k1\<close> using k_props(2)[OF k1S] by auto
              finally show \<open>x \<in> interior k1\<close> .
            qed
            moreover have \<open>?shrink k1 \<noteq> {}\<close> using k_props(5)[OF k1S] .
            ultimately have \<open>?shrink k1 \<inter> interior k2 = {}\<close> by auto
            moreover have \<open>?shrink k2 \<subseteq> interior k2\<close>
            proof
              fix x assume \<open>x \<in> ?shrink k2\<close>
              then have \<open>x \<in> {Inf k2 + (Sup k2 - Inf k2) / 2^n .. Sup k2 - (Sup k2 - Inf k2) / 2^n}\<close>
                using box_real by auto
              moreover have \<open>Inf k2 < Inf k2 + (Sup k2 - Inf k2) / 2^n\<close>
                using k_props(1)[OF k2S] by auto
              moreover have \<open>Sup k2 - (Sup k2 - Inf k2) / 2^n < Sup k2\<close>
                using k_props(1)[OF k2S] by auto
              ultimately have \<open>x \<in> {Inf k2 <..< Sup k2}\<close> by auto
              also have \<open>\<dots> = interior {Inf k2 .. Sup k2}\<close>
                using interior_atLeastAtMost_real by auto
              also have \<open>\<dots> = interior k2\<close> using k_props(2)[OF k2S] by auto
              finally show \<open>x \<in> interior k2\<close> .
            qed
            ultimately have \<open>?shrink k1 \<inter> ?shrink k2 = {}\<close> by blast
            then show False using eq k_props(5)[OF k1S]
              by blast
          qed
        qed
        \<comment> \<open>Inf and Sup of shrunken intervals\<close>
        have shrink_bounds: \<open>Inf (?shrink k) = Inf k + (Sup k - Inf k) / 2^n\<close>
                            \<open>Sup (?shrink k) = Sup k - (Sup k - Inf k) / 2^n\<close>
          if \<open>k \<in> ?S\<close> for k
        proof -
          have ne: \<open>Inf k + (Sup k - Inf k) / 2^n \<le> Sup k - (Sup k - Inf k) / 2^n\<close>
            using k_props(5)[OF that] by (auto simp: box_real)
          show \<open>Inf (?shrink k) = Inf k + (Sup k - Inf k) / 2^n\<close>
            unfolding box_real using cInf_atLeastAtMost[OF ne] .
          show \<open>Sup (?shrink k) = Sup k - (Sup k - Inf k) / 2^n\<close>
            unfolding box_real using cSup_atLeastAtMost[OF ne] .
        qed
        \<comment> \<open>Rewrite the @{term d'}-sum as a sum over @{term \<open>{k \<in> d. content k \<noteq> 0}\<close>}\<close>
        have d'_sum: \<open>(\<Sum>K\<in>d'. norm (f (Sup K) - f (Inf K))) =
          (\<Sum>k\<in>?S. norm (f (Sup k - (Sup k - Inf k) / 2^n) - f (Inf k + (Sup k - Inf k) / 2^n)))\<close>
        proof -
          have \<open>(\<Sum>K\<in>d'. norm (f (Sup K) - f (Inf K))) =
            (\<Sum>k\<in>?S. norm (f (Sup (?shrink k)) - f (Inf (?shrink k))))\<close>
            unfolding d'_eq using sum.reindex[OF inj_shrink] by (simp add: o_def)
          also have \<open>\<dots> = (\<Sum>k\<in>?S. norm (f (Sup k - (Sup k - Inf k) / 2^n) - 
                                         f (Inf k + (Sup k - Inf k) / 2^n)))\<close>
            using shrink_bounds by simp
          finally show ?thesis .
        qed
        have zero_summands: \<open>(\<Sum>k\<in>d. norm (f (Sup k - (Sup k - Inf k) / 2^n) - 
          f (Inf k + (Sup k - Inf k) / 2^n))) =
          (\<Sum>k\<in>?S. norm (f (Sup k - (Sup k - Inf k) / 2^n) - 
            f (Inf k + (Sup k - Inf k) / 2^n)))\<close>
        proof (rule sum.mono_neutral_right[OF fin_d])
          show \<open>?S \<subseteq> d\<close> by auto
          show \<open>\<forall>k\<in>d - ?S. norm (f (Sup k - (Sup k - Inf k) / 2^n) - 
            f (Inf k + (Sup k - Inf k) / 2^n)) = 0\<close>
          proof
            fix k assume \<open>k \<in> d - ?S\<close>
            then have kd: \<open>k \<in> d\<close> and kcont: \<open>content k = 0\<close> by auto
            then obtain a b where kab: \<open>k = cbox a b\<close> \<open>a = b\<close> 
              by (metis H antisym atLeastatMost_empty_iff2 cbox_division_memE content_real_eq_0 interval_cbox)
            then have \<open>Inf k = Sup k\<close> by (auto simp: box_real)
            then show \<open>norm (f (Sup k - (Sup k - Inf k) / 2^n) - 
              f (Inf k + (Sup k - Inf k) / 2^n)) = 0\<close> by simp
          qed
        qed
        \<comment> \<open>Conclude: @{term \<open>\<sigma> n < \<epsilon>/2\<close>}, hence @{term \<open>\<sigma> n \<le> \<epsilon>/2\<close>}\<close>
        have \<open>\<sigma> n = (\<Sum>k\<in>d'. norm (f (Sup k) - f (Inf k)))\<close>
          unfolding \<sigma>_def using zero_summands d'_sum by auto
        then show \<open>\<sigma> n \<le> \<epsilon>/2\<close> using r_int'_d' by linarith
      qed
      \<comment> \<open>Conclude: @{term \<open>L \<le> \<epsilon>/2\<close>} $< \varepsilon$\<close>
      have \<open>L \<le> \<epsilon>/2\<close>
        by (rule tendsto_le[OF sequentially_bot tendsto_const conv bound])
      then show ?thesis unfolding L_def using \<open>\<epsilon> > 0\<close> by linarith
    qed
  qed
qed


lemma absolutely_continuous_on_closure:
  assumes "absolutely_continuous_on (interior S) f"
    "continuous_on (closure S) f" "is_interval S"
  shows "absolutely_continuous_on S f"
  by (meson absolutely_continuous_on_interior assms closure_subset continuous_on_subset)

section \<open>Bounded variation and absolutely integrable derivatives\<close>

lemma countable_imp_negligible:
  fixes S :: \<open>real set\<close>
  assumes \<open>countable S\<close>
  shows \<open>negligible S\<close>
  using negligible_countable_Union[OF countable_image[OF assms]]
  by (metis (mono_tags, lifting) UN_singleton image_iff negligible_sing)


lemma absolutely_setcontinuous_on_componentwise:
  fixes f :: \<open>'a::euclidean_space set \<Rightarrow> 'b::euclidean_space\<close>
  shows \<open>absolutely_setcontinuous_on f S \<longleftrightarrow>
    (\<forall>b\<in>Basis. absolutely_setcontinuous_on (\<lambda>k. f k \<bullet> b) S)\<close>
    (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof
  assume L: \<open>?L\<close>
  show \<open>?R\<close>
    unfolding absolutely_setcontinuous_on_def
  proof (intro ballI allI impI)
    fix b :: 'b and \<epsilon> :: real
    assume \<open>b \<in> Basis\<close> and \<open>0 < \<epsilon>\<close>
    with L obtain \<delta> where \<open>0 < \<delta>\<close> and
      \<delta>: \<open>\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> sum content d < \<delta> \<Longrightarrow> (\<Sum>k\<in>d. norm (f k)) < \<epsilon>\<close>
      unfolding absolutely_setcontinuous_on_def
      by metis
    show \<open>\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
              (\<Sum>k\<in>d. norm (f k \<bullet> b)) < \<epsilon>\<close>
      by (metis (mono_tags, lifting) norm_nth_le \<delta> \<open>0 < \<delta>\<close> \<open>b \<in> Basis\<close> order.strict_trans1 sum_mono)
  qed
next
  assume R: \<open>?R\<close>
  show \<open>?L\<close>
    unfolding absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume \<epsilon>_pos: \<open>0 < \<epsilon>\<close>
    have comp: \<open>\<forall>b\<in>(Basis :: 'b set). \<exists>r>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> sum content d < r
              \<longrightarrow> (\<Sum>k\<in>d. \<bar>f k \<bullet> b\<bar>) < \<epsilon> / DIM('b)\<close>
    proof (intro ballI)
      fix b :: 'b assume \<open>b \<in> Basis\<close>
      with R have \<open>absolutely_setcontinuous_on (\<lambda>k. f k \<bullet> b) S\<close> by blast
      moreover have \<open>0 < \<epsilon> / DIM('b)\<close> using \<epsilon>_pos DIM_positive by simp
      ultimately obtain r where \<open>0 < r\<close> and
        r: \<open>\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> sum content d < r \<Longrightarrow> (\<Sum>k\<in>d. norm ((\<lambda>k. f k \<bullet> b) k)) < \<epsilon> / DIM('b)\<close>
        unfolding absolutely_setcontinuous_on_def by meson
      then show \<open>\<exists>r>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> sum content d < r
                \<longrightarrow> (\<Sum>k\<in>d. \<bar>f k \<bullet> b\<bar>) < \<epsilon> / DIM('b)\<close>
        by (intro exI[of _ r]) (auto simp: real_norm_def)
    qed
    then obtain r where r_pos: \<open>\<And>b. b \<in> (Basis :: 'b set) \<Longrightarrow> (0::real) < r b\<close>
      and r_bound: \<open>\<And>b d T. b \<in> (Basis :: 'b set) \<Longrightarrow> d division_of T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> sum content d < r b
                      \<Longrightarrow> (\<Sum>k\<in>d. \<bar>f k \<bullet> b\<bar>) < \<epsilon> / DIM('b)\<close>
      by (metis bchoice)
    define \<delta> where \<open>\<delta> = Min (r ` (Basis :: 'b set))\<close>
    have \<delta>_pos: \<open>0 < \<delta>\<close>
      unfolding \<delta>_def using r_pos finite_Basis nonempty_Basis
      by (subst Min_gr_iff) (auto simp: image_is_empty)
    moreover have \<open>\<forall>d T. d division_of T \<and> T \<subseteq> S \<and> sum content d < \<delta>
                    \<longrightarrow> (\<Sum>k\<in>d. norm (f k)) < \<epsilon>\<close>
    proof (intro allI impI)
      fix d T assume asm: \<open>d division_of T \<and> T \<subseteq> S \<and> sum content d < \<delta>\<close>
      have finite_d: \<open>finite d\<close> using asm division_of_finite by blast
      have \<open>(\<Sum>k\<in>d. norm (f k)) \<le> (\<Sum>k\<in>d. \<Sum>b\<in>(Basis :: 'b set). \<bar>f k \<bullet> b\<bar>)\<close>
        by (rule sum_mono) (rule norm_le_l1)
      also have \<open>\<dots> = (\<Sum>b\<in>(Basis :: 'b set). \<Sum>k\<in>d. \<bar>f k \<bullet> b\<bar>)\<close>
        by (rule sum.swap)
      also have \<open>\<dots> < of_nat (DIM('b)) * (\<epsilon> / of_nat (DIM('b)))\<close>
      proof (rule sum_bounded_above_strict)
        fix b :: 'b assume \<open>b \<in> Basis\<close>
        then have \<open>\<delta> \<le> r b\<close>
          unfolding \<delta>_def by (intro Min_le finite_imageI finite_Basis) (auto simp: image_iff)
        then have \<open>sum content d < r b\<close>
          using asm by linarith
        then show \<open>(\<Sum>k\<in>d. \<bar>f k \<bullet> b\<bar>) < \<epsilon> / real DIM('b)\<close>
          using r_bound \<open>b \<in> Basis\<close> asm by blast
      next
        show \<open>0 < card (Basis :: 'b set)\<close> by (simp add: DIM_positive)
      qed
      also have \<open>\<dots> = \<epsilon>\<close>
        using DIM_positive[where 'a='b] by simp
      finally show \<open>(\<Sum>k\<in>d. norm (f k)) < \<epsilon>\<close> .
    qed
    ultimately show \<open>\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> sum content d < \<delta> \<longrightarrow> (\<Sum>k\<in>d. norm (f k)) < \<epsilon>\<close>
      by auto
  qed
qed


lemma absolutely_setcontinuous_on_alt:
  \<open>absolutely_setcontinuous_on f S \<longleftrightarrow>
    (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and>
      (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow> norm (\<Sum>k\<in>d. f k) < \<epsilon>)\<close>  (is \<open>?L = ?R\<close>)
proof
  show \<open>?L \<Longrightarrow> ?R\<close>
    by (meson absolutely_setcontinuous_on_def norm_sum order_le_less_trans)
next
  assume R: \<open>?R\<close>
  show \<open>?L\<close>
  proof -
    have "absolutely_setcontinuous_on (\<lambda>k. f k \<bullet> b) S"
      if "b \<in> Basis" for b :: 'b
      unfolding absolutely_setcontinuous_on_def
    proof (intro strip)
      fix \<epsilon> :: real
      assume "0 < \<epsilon>"
      show "\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> sum content d < \<delta> \<longrightarrow> (\<Sum>k\<in>d. norm (f k \<bullet> b)) < \<epsilon>"
      proof -
        have \<open>0 < \<epsilon>/2\<close> using \<open>0 < \<epsilon>\<close> by simp
        with R obtain r where \<open>0 < r\<close> and
          r: \<open>\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> sum content d < r \<Longrightarrow> norm (\<Sum>k\<in>d. f k) < \<epsilon>/2\<close>
          by meson
        show ?thesis
        proof (intro exI conjI allI impI)
          show \<open>0 < r\<close> by fact
        next
          fix d T
          assume dt: \<open>d division_of T \<and> T \<subseteq> S \<and> sum content d < r\<close>
          have fin: \<open>finite d\<close> using dt division_of_finite by blast
          define d_pos where \<open>d_pos = {k \<in> d. 0 \<le> f k \<bullet> b}\<close>
          define d_neg where \<open>d_neg = {k \<in> d. f k \<bullet> b < 0}\<close>
          have d_split: \<open>d = d_pos \<union> d_neg\<close> and d_disj: \<open>d_pos \<inter> d_neg = {}\<close> 
             and fin_pos: \<open>finite d_pos\<close> and fin_neg: \<open>finite d_neg\<close> and d_pos_sub: \<open>d_pos \<subseteq> d\<close> and d_neg_sub: \<open>d_neg \<subseteq> d\<close>
            using fin unfolding d_pos_def d_neg_def by auto
          obtain div_pos: \<open>d_pos division_of \<Union>d_pos\<close> and div_neg: \<open>d_neg division_of \<Union>d_neg\<close>
            by (meson d_neg_sub d_pos_sub division_of_subset division_of_union_self dt)
          have union_pos_sub: \<open>\<Union>d_pos \<subseteq> S\<close> and union_neg_sub: \<open>\<Union>d_neg \<subseteq> S\<close>
            using dt d_pos_sub d_split by blast+
          have content_pos: \<open>sum content d_pos < r\<close>
            by (meson dt content_pos_le d_pos_sub fin order_le_less_trans sum_mono2)
          have content_neg: \<open>sum content d_neg < r\<close>
            by (meson dt content_pos_le d_neg_sub fin order_le_less_trans sum_mono2)
          have norm_pos: \<open>norm (sum f d_pos) < \<epsilon>/2\<close>
            using r[OF div_pos union_pos_sub content_pos] .
          have norm_neg: \<open>norm (sum f d_neg) < \<epsilon>/2\<close>
            using r[OF div_neg union_neg_sub content_neg] .
          have sum_pos: \<open>(\<Sum>k\<in>d_pos. norm (f k \<bullet> b)) \<le> norm (sum f d_pos)\<close>
          proof -
            have \<open>(\<Sum>k\<in>d_pos. norm (f k \<bullet> b)) = (\<Sum>k\<in>d_pos. f k \<bullet> b)\<close>
              by (rule sum.cong) (auto simp: d_pos_def real_norm_def abs_of_nonneg)
            also have \<open>\<dots> = (sum f d_pos) \<bullet> b\<close>
              by (simp add: inner_sum_left)
            also have \<open>\<dots> \<le> norm (sum f d_pos)\<close>
              by (smt (verit, best) Basis_le_norm that)
            finally show ?thesis .
          qed
          have sum_neg: \<open>(\<Sum>k\<in>d_neg. norm (f k \<bullet> b)) \<le> norm (sum f d_neg)\<close>
          proof -
            have \<open>(\<Sum>k\<in>d_neg. norm (f k \<bullet> b)) = (\<Sum>k\<in>d_neg. -(f k \<bullet> b))\<close>
              by (rule sum.cong) (auto simp: d_neg_def real_norm_def abs_of_neg)
            also have \<open>\<dots> = -((sum f d_neg) \<bullet> b)\<close>
              by (simp add: inner_sum_left sum_negf)
            also have \<open>\<dots> \<le> norm (sum f d_neg)\<close> 
              by (smt (verit, best) Basis_le_norm that)
            finally show ?thesis .
          qed
          show \<open>(\<Sum>k\<in>d. norm (f k \<bullet> b)) < \<epsilon>\<close>
          proof -
            have \<open>(\<Sum>k\<in>d. norm (f k \<bullet> b)) = (\<Sum>k\<in>d_pos. norm (f k \<bullet> b)) + (\<Sum>k\<in>d_neg. norm (f k \<bullet> b))\<close>
              by (subst d_split) (rule sum.union_disjoint[OF fin_pos fin_neg d_disj])
            also have \<open>\<dots> \<le> norm (sum f d_pos) + norm (sum f d_neg)\<close>
              by (rule add_mono[OF sum_pos sum_neg])
            also have \<open>\<dots> < \<epsilon>/2 + \<epsilon>/2\<close>
              by (rule add_strict_mono[OF norm_pos norm_neg])
            finally show ?thesis by simp
          qed
        qed
      qed
    qed
    then show ?thesis
    using absolutely_setcontinuous_on_componentwise by blast
  qed  
qed

lemma absolutely_integrable_approximate_continuous_vector:
  fixes f :: \<open>'a::euclidean_space \<Rightarrow> 'b::euclidean_space\<close>
    and S :: \<open>'a set\<close>
  assumes \<open>S \<in> lmeasurable\<close>
    and \<open>f absolutely_integrable_on S\<close>
    and \<open>e > 0\<close>
  obtains g where \<open>g absolutely_integrable_on S\<close> \<open>continuous_on UNIV g\<close>
    \<open>bounded (range g)\<close> 
    \<open>norm (integral S (\<lambda>x. norm (f x - g x))) < e\<close>
proof -
  obtain h where hint: "h absolutely_integrable_on S" 
    and hbo: "bounded (h ` UNIV)" 
    and he2: "norm (integral S (\<lambda>x. norm (f x - h x))) < e/2"
  proof -
    define trunc where "trunc \<equiv> \<lambda>n x. \<Sum>b\<in>Basis. max (- real n) (min (real n) (f x \<bullet> b)) *\<^sub>R b"
    have trunc_abs_int: \<open>trunc n absolutely_integrable_on S\<close> for n
    proof -
      define c where \<open>c = (\<Sum>b\<in>Basis. real n *\<^sub>R b :: 'b)\<close>
      have c_inner[simp]: \<open>c \<bullet> b = real n\<close> if \<open>b \<in> Basis\<close> for b
        unfolding c_def using inner_sum_left_Basis[OF that] by simp
      have mc_inner[simp]: \<open>(- c) \<bullet> b = - real n\<close> if \<open>b \<in> Basis\<close> for b
        by (simp add: that)
      have const_int: \<open>(\<lambda>_::'a. d) absolutely_integrable_on S\<close> for d :: 'b
        using absolutely_integrable_on_const assms(1) by blast
      have min_int: \<open>(\<lambda>x. \<Sum>b\<in>Basis. min (f x \<bullet> b) (c \<bullet> b) *\<^sub>R b)
                     absolutely_integrable_on S\<close>
        by (rule absolutely_integrable_min[OF assms(2) const_int])
      then have min_int': \<open>(\<lambda>x. \<Sum>b\<in>Basis. min (f x \<bullet> b) (real n) *\<^sub>R b)
                            absolutely_integrable_on S\<close>
        by (simp cong: sum.cong)
      have max_int: \<open>(\<lambda>x. \<Sum>b\<in>Basis. max ((- c) \<bullet> b) ((\<Sum>b\<in>Basis. min (f x \<bullet> b) (real n) *\<^sub>R b) \<bullet> b) *\<^sub>R b)
                     absolutely_integrable_on S\<close>
        by (rule absolutely_integrable_max[OF const_int min_int'])
      then show ?thesis
        by (simp add: trunc_def inner_sum_left_Basis max.commute min.commute cong: sum.cong)
    qed
    have conv: \<open>(\<lambda>k. integral S (\<lambda>x. norm (f x - trunc k x))) \<longlonglongrightarrow> 0\<close>
    proof -
      let ?fn = \<open>\<lambda>k x. norm (f x - trunc k x)\<close>
      have \<open>(\<lambda>k. integral S (?fn k)) \<longlonglongrightarrow> integral S (\<lambda>x. 0 :: real)\<close>
      proof (rule dominated_convergence(2))
        show fn_int: \<open>(\<lambda>x. ?fn k x) integrable_on S\<close> for k
          by (metis absolutely_integrable_on_def assms(2) set_integral_diff(1) trunc_abs_int)
        show dom_int: \<open>(\<lambda>x. 2 * norm (f x)) integrable_on S\<close>
          using assms(2)[unfolded absolutely_integrable_on_def]
          by (auto intro: integrable_on_mult_right)
        show norm_bound: \<open>norm (?fn k x) \<le> 2 * norm (f x)\<close> if \<open>x \<in> S\<close> for k x
        proof -
          have trunc_inner: \<open>trunc k x \<bullet> b = max (- real k) (min (real k) (f x \<bullet> b))\<close>
            if \<open>b \<in> Basis\<close> for b
            using inner_sum_left_Basis[OF that] by (simp add: trunc_def)
          have clip_le: \<open>\<bar>max (- real k) (min (real k) (c::real))\<bar> \<le> \<bar>c\<bar>\<close> for c
            by auto
          have \<open>trunc k x \<bullet> trunc k x \<le> f x \<bullet> f x\<close>
            by (metis clip_le norm_le norm_le_componentwise trunc_inner)
          then have \<open>norm (trunc k x) \<le> norm (f x)\<close>
            by (simp add: norm_eq_sqrt_inner real_sqrt_le_mono)
          then show ?thesis
            by (simp add: norm_triangle_ineq4 [THEN order_trans])
        qed
        show \<open>(\<lambda>k. ?fn k x) \<longlonglongrightarrow> 0\<close> if \<open>x \<in> S\<close> for x
        proof -
          obtain N where N: \<open>real N \<ge> norm (f x)\<close>
            using real_nat_ceiling_ge by blast
          have \<open>?fn k x = 0\<close> if \<open>k \<ge> N\<close> for k
          proof -
            have \<open>real k \<ge> norm (f x)\<close> using N that by linarith
            then obtain \<open>f x \<bullet> b \<le> real k\<close> \<open>- real k \<le> f x \<bullet> b\<close> if \<open>b \<in> Basis\<close> for b
              using norm_bound_Basis_le by fastforce
            then have \<open>trunc k x = f x\<close>
              by (simp add: trunc_def euclidean_eqI)
            then show ?thesis by simp
          qed
          then show ?thesis
            using LIMSEQ_iff by force
        qed
      qed
      then show ?thesis by simp
    qed
    then obtain n where n: "norm (integral S (\<lambda>x. norm (f x - trunc n x))) < e/2"
      by (metis (no_types, lifting) LIMSEQ_iff assms(3) half_gt_zero order.refl diff_0_right)
    show ?thesis
    proof 
      show "bounded (range (trunc n))"
        unfolding bounded_iff
      proof (intro exI allI ballI)
        fix y assume "y \<in> range (trunc n)"
        then obtain x where y: "y = trunc n x" by auto
        have "norm (max (- real n) (min (real n) (f x \<bullet> b)) *\<^sub>R b) \<le> real n" if "b \<in> Basis" for b
          by (simp add: that)
        then have "norm (trunc n x) \<le> real DIM('b) * real n"
          unfolding trunc_def by (rule sum_norm_bound)
        then show "norm y \<le> real DIM('b) * real n"
          by (simp add: y)
      qed
    qed (use n trunc_abs_int in auto)
  qed
  obtain B where "B > 0" and B: "\<And>z. norm (h z) \<le> B"
    by (meson UNIV_I bounded_pos hbo image_eqI)

  obtain k g where neg_k: \<open>negligible k\<close>
    and g_cont: \<open>\<And>n. continuous_on UNIV (g n)\<close>
    and g_bound: \<open>\<And>n x. norm (g n x) \<le> norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))\<close>
    and g_conv: \<open>\<And>x. x \<in> S - k \<Longrightarrow> (\<lambda>n. g n x) \<longlonglongrightarrow> h x\<close>
  proof -
    have \<open>h integrable_on S\<close>
      using hint absolutely_integrable_on_def set_lebesgue_integral_eq_integral(1) by blast
    then have \<open>h \<in> borel_measurable (lebesgue_on S)\<close>
      by (rule integrable_imp_measurable)
    then have h_meas: \<open>h measurable_on S\<close>
      using assms
      by (auto simp: measurable_on_iff_borel_measurable lmeasurable_iff_integrable fmeasurable_def)
    then obtain N g where "negligible N"
      and contg: "\<And>n. continuous_on UNIV (g n)"
      and lim: "\<And>x. x \<notin> N \<Longrightarrow> (\<lambda>n. g n x) \<longlonglongrightarrow> (if x \<in> S then h x else 0)"
      by (auto simp: measurable_on_def)
    define j where "j \<equiv> \<lambda>n x. \<Sum>b\<in>Basis. max (-B) (min B (g n x \<bullet> b)) *\<^sub>R b :: 'b"
    show ?thesis
    proof
      show "continuous_on UNIV (j n)" for n
        unfolding j_def by (intro continuous_intros contg)
      fix n x
      show "norm (j n x::'b) \<le> norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))"
      proof (rule norm_le_componentwise)
        fix b :: 'b assume b: "b \<in> Basis"
        have "\<bar>max (- B) (min B (g n x \<bullet> b))\<bar> \<le> B"
          using \<open>B > 0\<close> by (auto simp: abs_le_iff)
        moreover have "(\<Sum>i\<in>Basis. max (- B) (min B (g n x \<bullet> i)) *\<^sub>R i) \<bullet> b
                      = max (- B) (min B (g n x \<bullet> b))"
          using inner_sum_left_Basis[OF b] by simp
        moreover have "(B *\<^sub>R (\<Sum>i\<in>Basis. i::'b)) \<bullet> b = B"
          by (simp add: inner_scaleR_left inner_sum_Basis[OF b])
        ultimately show "\<bar>j n x \<bullet> b\<bar> \<le> \<bar>(B *\<^sub>R (\<Sum>b\<in>Basis. b::'b)) \<bullet> b\<bar>"
          using \<open>B > 0\<close> by (simp add: j_def)
      qed
    next
      fix x :: 'a
      assume xS: "x \<in> S - N"
      show "(\<lambda>n. j n x) \<longlonglongrightarrow> h x"
      proof -
        define clamp where "clamp \<equiv> \<lambda>v::'b. \<Sum>b\<in>Basis. max (-B) (min B (v \<bullet> b)) *\<^sub>R b"
        have j_eq: "j n x = clamp (g n x)" for n
          by (simp add: j_def clamp_def)
        have clamp_cont: "continuous_on UNIV clamp"
          unfolding clamp_def by (intro continuous_intros)
        have clamp_h: "clamp (h x) = h x"
        proof -
          have *: "max (- B) (min B (h x \<bullet> b)) = h x \<bullet> b" if "b \<in> Basis" for b
            using norm_nth_le[OF that, of "h x"] B by (smt (verit) real_norm_def)
          show ?thesis
            unfolding clamp_def using * by (simp cong: sum.cong add: euclidean_representation)
        qed
        have g_lim: "(\<lambda>n. g n x) \<longlonglongrightarrow> h x"
          using lim xS by fastforce
        have "isCont clamp (h x)"
          using clamp_cont continuous_on_eq_continuous_at open_UNIV by fastforce
        then have "(\<lambda>n. clamp (g n x)) \<longlonglongrightarrow> clamp (h x)"
          using continuous_imp_tendsto g_lim by (auto simp: o_def)
        then show ?thesis
          by (simp add: j_eq clamp_h)
      qed
    qed (use \<open>negligible N\<close> contg in auto)
  qed
  have S_sets: "S \<in> sets lebesgue"
    using assms(1) by blast
  have gn_int: "g n absolutely_integrable_on S" for n
  proof -
    have meas: "g n \<in> borel_measurable (lebesgue_on S)"
      using continuous_imp_measurable_on_sets_lebesgue[OF continuous_on_subset[OF g_cont subset_UNIV] S_sets] .
    have "integrable (lebesgue_on S) (norm \<circ> g n)"
      using finite_measure.integrable_const_bound[OF finite_measure_lebesgue_on[OF assms(1)]] g_bound
      by (metis (no_types, lifting) ext comp_apply eventuallyI integrable_norm_iff meas)
    then show ?thesis
      using meas S_sets absolutely_integrable_measurable by blast
  qed
  show ?thesis
  proof -
    define fn where "fn \<equiv> \<lambda>n x. norm (f x - g n x)"
    have fn_int: "fn n integrable_on S" for n
      using gn_int absolutely_integrable_on_def assms(2) fn_def
      by fastforce
    have fn_bound: "fn n x \<le> norm (f x) + norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))" for n x
      by (metis add_left_mono fn_def g_bound norm_triangle_le_diff)
    have dom_int: "(\<lambda>x. norm (f x) + norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))) integrable_on S"
    proof -
      have "f integrable_on S"
        using assms(2) set_lebesgue_integral_eq_integral(1) by blast
      then have "(\<lambda>x. norm (f x)) integrable_on S"
        using absolutely_integrable_norm[OF assms(2)] set_lebesgue_integral_eq_integral(1)    
        by (simp add: absolutely_integrable_on_def)
      moreover have "(\<lambda>_::'a. norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))) integrable_on S"
        using absolutely_integrable_on_const[OF assms(1)] set_lebesgue_integral_eq_integral(1) by blast
      ultimately show ?thesis
        by (rule integrable_add)
    qed
    have fn_conv: "(\<lambda>n. fn n x) \<longlonglongrightarrow> norm (f x - h x)" if "x \<in> S - k" for x
      using fn_def g_conv tendsto_diff tendsto_norm that by blast
    have conv_Sk: "(\<lambda>n. integral (S - k) (fn n)) \<longlonglongrightarrow> integral (S - k) (\<lambda>x. norm (f x - h x))"
    proof (rule dominated_convergence(2))
      show "fn n integrable_on (S - k)" for n
        using fn_int integrable_spike_set negligible_subset[OF neg_k]
        by (simp add: has_integral_iff integrable_negligible integrable_setdiff)
      show "(\<lambda>x. norm (f x) + norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))) integrable_on (S - k)"
        using dom_int negligible_subset[OF neg_k]
        by (metis (lifting) eq_integralD integrable_negligible integrable_setdiff neg_k
            negligible_diff)
      show "norm (fn n x) \<le> norm (f x) + norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))"
        if "x \<in> S - k" for n x
        using fn_bound fn_def by fastforce
      show "(\<lambda>n. fn n x) \<longlonglongrightarrow> norm (f x - h x)" if "x \<in> S - k" for x
        using fn_conv that by blast
    qed
    have int_eq: "integral (S - k) (fn n) = integral S (fn n)" for n
      using integral_subset_negligible[of "S - k" S "fn n"] neg_k
      by (simp add: Diff_Diff_Int negligible_Int)
    have int_eq': "integral (S - k) (\<lambda>x. norm (f x - h x)) = integral S (\<lambda>x. norm (f x - h x))"
      using integral_subset_negligible[of "S - k" S "\<lambda>x. norm (f x - h x)"] neg_k
      by (simp add: Diff_Diff_Int negligible_Int)
    have conv_S: "(\<lambda>n. integral S (fn n)) \<longlonglongrightarrow> integral S (\<lambda>x. norm (f x - h x))"
      using conv_Sk int_eq int_eq' by simp
    have limit_small: "integral S (\<lambda>x. norm (f x - h x)) < e"
      using he2 by simp
    then obtain N where "\<forall>n\<ge>N. norm (integral S (fn n) - integral S (\<lambda>x. norm (f x - h x))) < e - integral S (\<lambda>x. norm (f x - h x))"
      using conv_S LIMSEQ_iff
      by (smt (verit) assms(3) diff_gt_0_iff_gt)
    then have "norm (integral S (fn N)) < e"
      by (smt (verit, best) Henstock_Kurzweil_Integration.integral_norm_bound_integral
          dual_order.refl fn_def fn_int norm_ge_zero real_norm_def)
    moreover have \<open>bounded (range (g N)) \<close>
      using bounded_iff g_bound by blast
    ultimately show ?thesis
      using that[OF \<open>g N absolutely_integrable_on S\<close> g_cont] fn_def by blast
  qed
qed

theorem absolutely_integrable_approximate_continuous:
  fixes f :: \<open>'a::euclidean_space \<Rightarrow> 'b::euclidean_space\<close>
    and S :: \<open>'a set\<close>
  assumes S_meas: \<open>S \<in> sets lebesgue\<close>
    and f_int: \<open>f absolutely_integrable_on S\<close>
    and e_pos: \<open>e > 0\<close>
  obtains g where \<open>g absolutely_integrable_on S\<close> \<open>continuous_on UNIV g\<close>
    \<open>bounded (g ` UNIV)\<close>
    \<open>norm (integral S (\<lambda>x. norm (f x - g x))) < e\<close>
proof -
  text \<open>Claim 1: absolute integrability on intersections and differences with boxes.\<close>
  have f_int_inter: \<open>f absolutely_integrable_on (S \<inter> cbox u v)\<close> for u v
    by (meson assms fmeasurableD fmeasurable_cbox inf.cobounded1 set_integrable_subset
        sets.Int sets_completionI_sets)
  have f_int_diff: \<open>f absolutely_integrable_on (S - cbox u v)\<close> for u v
    by (meson Diff_subset assms fmeasurableD lmeasurable_cbox set_integrable_subset
        sets.Diff)
  text \<open>Claim 2: approximation of the norm integral by boxes.\<close>
  have norm_int: \<open>(\<lambda>x. norm (f x)) integrable_on S\<close>
    using f_int absolutely_integrable_on_def by blast
  obtain a b where approx:
    \<open>norm (integral (S \<inter> cbox a b) (\<lambda>x. norm (f x)) - integral S (\<lambda>x. norm (f x))) < e / 3\<close>
  proof -
    have \<open>((\<lambda>x. norm (f x)) has_integral integral S (\<lambda>x. norm (f x))) S\<close>
      using integrable_integral [OF norm_int] .
    then have alt: \<open>\<forall>\<epsilon>>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
                     norm (integral (cbox a b) (\<lambda>x. if x \<in> S then norm (f x) else 0) -
                           integral S (\<lambda>x. norm (f x))) < \<epsilon>\<close>
      using has_integral_alt' [of \<open>\<lambda>x. norm (f x)\<close> \<open>integral S (\<lambda>x. norm (f x))\<close> S]
      by blast
    have \<open>e / 3 > 0\<close> using e_pos by auto
    then obtain B where \<open>B > 0\<close> and B:
      \<open>\<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
         norm (integral (cbox a b) (\<lambda>x. if x \<in> S then norm (f x) else 0) -
               integral S (\<lambda>x. norm (f x))) < e / 3\<close>
      using alt by blast
    obtain c where \<open>ball (0::'a) B \<subseteq> cbox (- c) c\<close>
      using bounded_subset_cbox_symmetric [OF bounded_ball] by blast
    then have \<open>norm (integral (cbox (- c) c) (\<lambda>x. if x \<in> S then norm (f x) else 0) -
                     integral S (\<lambda>x. norm (f x))) < e / 3\<close>
      using B by blast
    moreover have \<open>integral (cbox (- c) c) (\<lambda>x. if x \<in> S then norm (f x) else 0) =
                   integral (S \<inter> cbox (- c) c) (\<lambda>x. norm (f x))\<close>
      by (rule integral_restrict_Int)
    ultimately show ?thesis
      using that by auto
  qed
  text \<open>Apply the existing lemma to get a continuous bounded approximation on the box.\<close>
  have meas_inter: \<open>S \<inter> cbox a b \<in> lmeasurable\<close>
    by (intro bounded_set_imp_lmeasurable bounded_Int)
       (use S_meas lmeasurable_cbox fmeasurableD sets.Int in auto)
  obtain g where g_int: \<open>g absolutely_integrable_on (S \<inter> cbox a b)\<close>
    and g_cont: \<open>continuous_on UNIV g\<close>
    and g_bdd: \<open>bounded (g ` UNIV)\<close>
    and g_approx: \<open>norm (integral (S \<inter> cbox a b) (\<lambda>x. norm (f x - g x))) < e / 3\<close>
    using absolutely_integrable_approximate_continuous_vector[of "S \<inter> cbox a b" f "e / 3"]
      divide_pos_pos[of e "3"] e_pos f_int_inter[of a b] meas_inter
      zero_less_numeral by blast
  text \<open>Extract an explicit positive bound on @{term g}.\<close>
  obtain B where B_pos: \<open>B > 0\<close> and B_bound: \<open>\<And>x. norm (g x) \<le> B\<close>
    using g_bdd [unfolded bounded_pos] by (auto simp: image_iff)
  have eB: \<open>e / 3 / B > 0\<close> using e_pos B_pos by auto
  obtain c d where cd_sub: \<open>cbox a b \<subseteq> box c d\<close>
    and cd_meas: \<open>measure lborel (box c d) - measure lborel (cbox a b) < e / 3 / B\<close>
  proof (cases \<open>cbox a b = {}\<close>)
    case True
    then show ?thesis using eB by (intro that [of 0 0]) auto
  next
    case False
    then have ab: \<open>\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i\<close> by (simp add: box_ne_empty)
    define F where \<open>F \<equiv> \<lambda>\<delta>::real. \<Prod>i\<in>Basis. (b \<bullet> i - a \<bullet> i) + 2 * \<delta>\<close>
    have F_cont: \<open>isCont F 0\<close>
      unfolding F_def by (intro continuous_intros)
    have F_0: \<open>F 0 = measure lborel (cbox a b)\<close>
      unfolding F_def using content_cbox' [OF False] by simp
    then obtain \<delta> where \<open>\<delta> > 0\<close> and
      \<delta>_bound: \<open>\<And>\<delta>'. \<bar>\<delta>'\<bar> < \<delta> \<Longrightarrow> \<bar>F \<delta>' - F 0\<bar> < e / 3 / B\<close>
      using F_cont [unfolded continuous_at_real_range] eB by (auto simp: real_norm_def)
    define \<delta>' where \<open>\<delta>' \<equiv> min \<delta> 1 / 2\<close>
    have \<delta>'_pos: \<open>\<delta>' > 0\<close> using \<open>\<delta> > 0\<close> unfolding \<delta>'_def by auto
    have \<delta>'_lt: \<open>\<bar>\<delta>'\<bar> < \<delta>\<close> using \<open>\<delta> > 0\<close> unfolding \<delta>'_def by auto
    define c' d' where \<open>c' \<equiv> a - \<delta>' *\<^sub>R One\<close> and \<open>d' \<equiv> b + \<delta>' *\<^sub>R One\<close>
    have inner_c': \<open>i \<in> Basis \<Longrightarrow> c' \<bullet> i = a \<bullet> i - \<delta>'\<close> for i
      unfolding c'_def by (simp add: inner_diff_left inner_scaleR_left inner_sum_Basis)
    have inner_d': \<open>i \<in> Basis \<Longrightarrow> d' \<bullet> i = b \<bullet> i + \<delta>'\<close> for i
      unfolding d'_def by (simp add: inner_add_left inner_scaleR_left inner_sum_Basis)
    have sub: \<open>cbox a b \<subseteq> box c' d'\<close>
      by (intro subset_box_imp ballI conjI)
         (simp_all add: inner_c' inner_d' \<delta>'_pos)
    have cd_le: \<open>i \<in> Basis \<Longrightarrow> c' \<bullet> i \<le> d' \<bullet> i\<close> for i
      using ab [of i] \<delta>'_pos by (simp add: inner_c' inner_d')
    have cd_ne: \<open>cbox c' d' \<noteq> {}\<close>
      using False sub box_subset_cbox [of c' d'] by auto
    have content_cd: \<open>measure lborel (cbox c' d') = F \<delta>'\<close>
      unfolding F_def using content_cbox' [OF cd_ne]
      by (simp add: inner_c' inner_d' algebra_simps)
    have content_mono: \<open>measure lborel (cbox a b) \<le> measure lborel (cbox c' d')\<close>
      using Henstock_Kurzweil_Integration.content_subset
            [OF subset_trans [OF sub box_subset_cbox]] .
    have \<open>\<bar>F \<delta>' - F 0\<bar> < e / 3 / B\<close>
      using \<delta>_bound \<delta>'_lt by blast
    then have \<open>measure lborel (cbox c' d') - measure lborel (cbox a b) < e / 3 / B\<close>
      using content_cd F_0 content_mono by linarith
    then show ?thesis
      using sub that content_box_cbox [of c' d'] by simp
  qed

  text \<open>Apply Tietze to obtain @{term h} extending @{term \<open>\<lambda>x. if x \<in> cbox a b then g x else 0\<close>}
    from the closed set @{term \<open>cbox a b \<union> (UNIV - box c d)\<close>} to all of @{term UNIV},
    with bound @{term B}.\<close>
  obtain h where h_cont: \<open>continuous_on UNIV h\<close>
    and h_eq: \<open>\<And>x. x \<in> cbox a b \<union> (UNIV - box c d) \<Longrightarrow> h x = (if x \<in> cbox a b then g x else 0)\<close>
    and h_bound: \<open>\<And>x. norm (h x) \<le> B\<close>
  proof (rule Tietze [of \<open>cbox a b \<union> (UNIV - box c d)\<close>
      \<open>\<lambda>x. if x \<in> cbox a b then g x else 0\<close> UNIV B])
    show \<open>continuous_on (cbox a b \<union> (UNIV - box c d))
          (\<lambda>x. if x \<in> cbox a b then g x else 0)\<close>
    proof (rule continuous_on_cases)
      show \<open>closed (cbox a b)\<close> by (rule closed_cbox)
      show \<open>closed (UNIV - box c d)\<close>
        using closed_Compl [OF open_box] by (simp add: Compl_eq_Diff_UNIV)
      show \<open>continuous_on (cbox a b) g\<close>
        using g_cont continuous_on_subset by blast
      show \<open>continuous_on (UNIV - box c d) (\<lambda>x. 0)\<close>
        by (rule continuous_on_const)
      show \<open>\<forall>x. x \<in> cbox a b \<and> x \<notin> cbox a b \<or>
              x \<in> UNIV - box c d \<and> x \<in> cbox a b \<longrightarrow> g x = 0\<close>
        using cd_sub by auto
    qed
    show \<open>closedin (top_of_set UNIV) (cbox a b \<union> (UNIV - box c d))\<close>
      unfolding subtopology_UNIV closed_closedin [symmetric]
      by (intro closed_Un closed_cbox closed_Compl [OF open_box, simplified Compl_eq_Diff_UNIV])
    show \<open>0 \<le> B\<close> using B_pos by linarith
    fix x assume \<open>x \<in> cbox a b \<union> (UNIV - box c d)\<close>
    then show \<open>norm (if x \<in> cbox a b then g x else 0) \<le> B\<close>
      using B_bound B_pos by (auto simp: less_imp_le)
  next
    fix h assume \<open>continuous_on UNIV h\<close>
      and \<open>\<And>x. x \<in> cbox a b \<union> (UNIV - box c d) \<Longrightarrow> h x = (if x \<in> cbox a b then g x else 0)\<close>
      and \<open>\<And>x. x \<in> UNIV \<Longrightarrow> norm (h x) \<le> B\<close>
    then show thesis
      by (intro that [of h]) auto
  qed
  text \<open>Show that @{term h} is absolutely integrable on @{term S}.\<close>
  have h_zero: \<open>h x = 0\<close> if \<open>x \<notin> cbox c d\<close> for x
    by (metis DiffI Diff_partition UNIV_I UnCI box_subset_cbox cd_sub h_eq that)
  have h_abs_cbox: \<open>h absolutely_integrable_on cbox c d\<close>
    by (rule absolutely_integrable_continuous [OF continuous_on_subset [OF h_cont subset_UNIV]])
  have h_abs_inter: \<open>h absolutely_integrable_on (S \<inter> cbox c d)\<close>
    using h_abs_cbox S_meas
    by (meson fmeasurableD fmeasurable_cbox inf.cobounded2 set_integrable_subset
        sets.Int sets_completionI_sets)
  have h_abs_S: \<open>h absolutely_integrable_on S\<close>
  proof (rule absolutely_integrable_spike_set [OF h_abs_inter])
    show \<open>negligible {x \<in> S \<inter> cbox c d - S. h x \<noteq> 0}\<close>
      by (simp add: Int_Diff)
    show \<open>negligible {x \<in> S - S \<inter> cbox c d. h x \<noteq> 0}\<close>
      by (simp add: h_zero cong: conj_cong)
  qed
  have h_int_inter: \<open>h absolutely_integrable_on (S \<inter> cbox u v)\<close> for u v
    by (meson h_abs_S S_meas fmeasurableD fmeasurable_cbox inf.cobounded1 set_integrable_subset
        sets.Int sets_completionI_sets)
  have h_int_diff: \<open>h absolutely_integrable_on (S - cbox u v)\<close> for u v
    by (meson h_abs_S S_meas Diff_subset fmeasurableD lmeasurable_cbox set_integrable_subset
        sets.Diff)
  show ?thesis
  proof
    show \<open>h absolutely_integrable_on S\<close> by (rule h_abs_S)
  next
    have fh_abs_inter: \<open>(\<lambda>x. f x - h x) absolutely_integrable_on (S \<inter> cbox a b)\<close>
      using f_int_inter h_int_inter by (rule set_integral_diff(1))
    have fh_abs_diff: \<open>(\<lambda>x. f x - h x) absolutely_integrable_on (S - cbox a b)\<close>
      using f_int_diff h_int_diff by (rule set_integral_diff(1))
    have nfh_int_inter: \<open>(\<lambda>x. norm (f x - h x)) integrable_on (S \<inter> cbox a b)\<close>
      using absolutely_integrable_norm [OF fh_abs_inter]
      by (auto intro: set_lebesgue_integral_eq_integral(1) simp: o_def)
    have nfh_int_diff: \<open>(\<lambda>x. norm (f x - h x)) integrable_on (S - cbox a b)\<close>
      using absolutely_integrable_norm [OF fh_abs_diff]
      by (auto intro: set_lebesgue_integral_eq_integral(1) simp: o_def)
    have split_eq: \<open>integral S (\<lambda>x. norm (f x - h x)) =
        integral (S \<inter> cbox a b) (\<lambda>x. norm (f x - h x)) + integral (S - cbox a b) (\<lambda>x. norm (f x - h x))\<close>
      by (metis (lifting) Diff_disjoint Int_Diff_Un Int_assoc integral_Un negligible_Int
          negligible_empty nfh_int_diff nfh_int_inter)
    have h_eq_g_on_ab: \<open>h x = g x\<close> if \<open>x \<in> cbox a b\<close> for x
      using h_eq [of x] that by auto
    have integral_fg_eq: \<open>integral (S \<inter> cbox a b) (\<lambda>x. norm (f x - g x)) =
        integral (S \<inter> cbox a b) (\<lambda>x. norm (f x - h x))\<close>
      by (intro integral_unique has_integral_eq [OF _ integrable_integral [OF nfh_int_inter]])
         (auto simp: h_eq_g_on_ab)
    have nf_int_diff: \<open>(\<lambda>x. norm (f x)) integrable_on (S - cbox a b)\<close>
      using absolutely_integrable_norm [OF f_int_diff]
      by (auto intro: set_lebesgue_integral_eq_integral(1) simp: o_def)
    have nh_int_diff: \<open>(\<lambda>x. norm (h x)) integrable_on (S - cbox a b)\<close>
      using absolutely_integrable_norm [OF h_int_diff]
      by (auto intro: set_lebesgue_integral_eq_integral(1) simp: o_def)
    have nfh_sum_int_diff: \<open>(\<lambda>x. norm (f x) + norm (h x)) integrable_on (S - cbox a b)\<close>
      by (rule integrable_add [OF nf_int_diff nh_int_diff])
    have norm_diff_bound: \<open>norm (integral (S - cbox a b) (\<lambda>x. norm (f x - h x))) \<le>
        integral (S - cbox a b) (\<lambda>x. norm (f x) + norm (h x))\<close>
      by (rule integral_norm_bound_integral [OF nfh_int_diff nfh_sum_int_diff])
        (simp add: norm_triangle_ineq4)
    have nf_int_inter: \<open>(\<lambda>x. norm (f x)) integrable_on (S \<inter> cbox a b)\<close>
      using absolutely_integrable_norm [OF f_int_inter]
      by (auto intro: set_lebesgue_integral_eq_integral(1) simp: o_def)
    have nf_split: \<open>integral (S \<inter> cbox a b) (\<lambda>x. norm (f x)) + integral (S - cbox a b) (\<lambda>x. norm (f x))
        = integral S (\<lambda>x. norm (f x))\<close>
      by (metis Diff_disjoint Int_Diff_Un Int_assoc integral_Un negligible_Int
          negligible_empty nf_int_diff nf_int_inter)

    have nf_diff_bound: \<open>integral (S - cbox a b) (\<lambda>x. norm (f x)) < e / 3\<close>
      using nf_split approx integral_nonneg [OF nf_int_diff]
      by (simp add: abs_le_iff)
    have nh_diff_bound: \<open>integral (S - cbox a b) (\<lambda>x. norm (h x)) < e / 3\<close>
    proof -
      have cd_ab_meas: \<open>box c d - cbox a b \<in> lmeasurable\<close>
        using lmeasurable_box lmeasurable_cbox by (rule fmeasurable.Diff)
      have int1: \<open>(\<lambda>x. if x \<in> S - cbox a b then norm (h x) else 0) integrable_on UNIV\<close>
        using nh_int_diff integrable_restrict_UNIV by fastforce
      have int2: \<open>(\<lambda>x. if x \<in> box c d - cbox a b then B else 0) integrable_on UNIV\<close>
        using integrable_on_const [OF cd_ab_meas] integrable_restrict_UNIV by fastforce
      have pw: \<open>norm (if x \<in> S - cbox a b then norm (h x) else 0) \<le>
              (if x \<in> box c d - cbox a b then B else 0)\<close> for x
        using B_pos h_bound h_eq by force

      have \<open>integral (S - cbox a b) (\<lambda>x. norm (h x)) =
                integral UNIV (\<lambda>x. if x \<in> S - cbox a b then norm (h x) else 0)\<close>
        by (rule integral_restrict_UNIV [symmetric])
      moreover have \<open>integral (box c d - cbox a b) (\<lambda>x. B) =
                integral UNIV (\<lambda>x. if x \<in> box c d - cbox a b then B else 0)\<close>
        by (rule integral_restrict_UNIV [symmetric])
      moreover have \<open>norm (integral UNIV (\<lambda>x. if x \<in> S - cbox a b then norm (h x) else 0)) \<le>
              integral UNIV (\<lambda>x. if x \<in> box c d - cbox a b then B else 0)\<close>
        by (rule integral_norm_bound_integral [OF int1 int2 pw])
      ultimately have nh_le_const:
        \<open>integral (S - cbox a b) (\<lambda>x. norm (h x)) \<le> integral (box c d - cbox a b) (\<lambda>x. B)\<close>
        by simp
      also have \<open>\<dots> = B * (measure lebesgue (box c d) - measure lebesgue (cbox a b))\<close>
        by (metis (no_types, lifting) ext Henstock_Kurzweil_Integration.integral_mult_right
            cd_ab_meas lmeasure_integral mult_1_right
            measurable_measure_Diff [OF lmeasurable_box]
            lmeasurable_cbox fmeasurableD cd_sub)
      also have \<open>\<dots> < B * (e / 3 / B)\<close>
        using cd_meas B_pos by (intro mult_strict_left_mono) auto
      also have \<open>\<dots> = e / 3\<close>
        using B_pos by auto
      finally show ?thesis .
    qed
    have step1: \<open>norm (integral (S \<inter> cbox a b) (\<lambda>x. norm (f x - h x))) < e / 3\<close>
      using g_approx by (simp add: integral_fg_eq)
    have step2: \<open>norm (integral (S - cbox a b) (\<lambda>x. norm (f x - h x))) < 2 / 3 * e\<close>
      using norm_diff_bound integral_add [OF nf_int_diff nh_int_diff]
            nf_diff_bound nh_diff_bound
      by linarith
    have \<open>norm (integral S (\<lambda>x. norm (f x - h x))) \<le>
        norm (integral (S \<inter> cbox a b) (\<lambda>x. norm (f x - h x))) +
        norm (integral (S - cbox a b) (\<lambda>x. norm (f x - h x)))\<close>
      by (simp add: split_eq norm_triangle_ineq)
    also have \<open>\<dots> < e / 3 + 2 / 3 * e\<close>
      using step1 step2 by linarith
    also have \<open>\<dots> = e\<close> by simp
    finally show "norm (integral S (\<lambda>x. norm (f x - h x))) < e" .
  qed (use h_bound h_cont bounded_iff in auto)
qed

lemma absolutely_continuous_integral:
  fixes f :: \<open>'a::euclidean_space \<Rightarrow> 'b::euclidean_space\<close>
  assumes \<open>f absolutely_integrable_on S\<close> \<open>0 < \<epsilon>\<close>
  obtains \<delta> where \<open>\<delta>>0\<close> \<open>\<And>T. T \<subseteq> S \<Longrightarrow> T \<in> lmeasurable \<Longrightarrow> measure lebesgue T < \<delta>
              \<Longrightarrow> norm (integral T f) < \<epsilon>\<close>
proof -
  define f0 where "f0 \<equiv> \<lambda>x. if x \<in> S then f x else 0"
  have f0_ai: "f0 absolutely_integrable_on UNIV"
    using assms(1) unfolding f0_def absolutely_integrable_restrict_UNIV .
  have f0_int: "f0 integrable_on UNIV"
    using f0_ai absolutely_integrable_on_def by blast
  have nf0_int: "(\<lambda>x. norm (f0 x)) integrable_on UNIV"
    using f0_ai absolutely_integrable_on_def by blast
  have f0_eq: "\<And>x. x \<in> S \<Longrightarrow> f0 x = f x" unfolding f0_def by simp
  obtain g :: \<open>'a \<Rightarrow> 'b\<close> where g_ai: \<open>g absolutely_integrable_on UNIV\<close> 
               and g_bdd: \<open>bounded (range g)\<close> 
               and g_approx: \<open>norm (integral UNIV (\<lambda>x. norm (f0 x - g x))) < \<epsilon>/2\<close>
      using \<open>0 < \<epsilon>\<close> absolutely_integrable_approximate_continuous [OF _ f0_ai, where e = \<open> \<epsilon>/2\<close>]
      by force
  obtain B where \<open>B > 0\<close> and B: \<open>\<And>x. norm (g x) \<le> B\<close>
    using g_bdd bounded_pos[of \<open>range g\<close>] by auto
  show ?thesis
  proof
    show "\<epsilon>/2/B > 0"
      by (simp add: \<open>0 < B\<close> \<open>0 < \<epsilon>\<close>)
  next
    fix T
    assume "T \<subseteq> S"
      and "T \<in> lmeasurable"
      and *: "Sigma_Algebra.measure lebesgue T < \<epsilon>/2/B"
    have g_ai_t: \<open>g absolutely_integrable_on T\<close>
      by (meson \<open>T \<in> lmeasurable\<close> fmeasurableD g_ai set_integrable_subset subset_UNIV)
    have f0_ai_t: \<open>f0 absolutely_integrable_on T\<close>
      by (meson \<open>T \<in> lmeasurable\<close> f0_ai fmeasurableD set_integrable_subset subset_UNIV)
    have f_ai_t: \<open>f absolutely_integrable_on T\<close>
      using \<open>T \<in> lmeasurable\<close> \<open>T \<subseteq> S\<close> assms(1) set_integrable_subset by blast
    have f0g_ai_t: \<open>(\<lambda>x. f0 x - g x) absolutely_integrable_on T\<close>
      using f0_ai_t g_ai_t by blast
    have nf0g_int_t: \<open>(\<lambda>x. norm (f0 x - g x)) integrable_on T\<close>
      using f0g_ai_t absolutely_integrable_on_def by metis
    have ng_int_t: \<open>(\<lambda>x. norm (g x)) integrable_on T\<close>
      using g_ai_t absolutely_integrable_on_def by blast
    have bnd_int_t: \<open>(\<lambda>x. norm (f0 x - g x) + norm (g x)) integrable_on T\<close>
      using nf0g_int_t ng_int_t integrable_add by blast
    have ineq1: \<open>norm (integral T f) \<le> integral T (\<lambda>x. norm (f0 x - g x) + norm (g x))\<close>
    proof (rule integral_norm_bound_integral)
      show \<open>f integrable_on T\<close>
        using f_ai_t set_lebesgue_integral_eq_integral by blast
      show \<open>(\<lambda>x. norm (f0 x - g x) + norm (g x)) integrable_on T\<close>
        using bnd_int_t .
      fix x assume \<open>x \<in> T\<close>
      then have \<open>f x = f0 x\<close> using \<open>T \<subseteq> S\<close> f0_eq by auto
      then show \<open>norm (f x) \<le> norm (f0 x - g x) + norm (g x)\<close>
        using norm_triangle_ineq[of \<open>f0 x - g x\<close> \<open>g x\<close>] by simp
    qed
    also have \<open>\<dots> = integral T (\<lambda>x. norm (f0 x - g x)) + integral T (\<lambda>x. norm (g x))\<close>
      using integral_add[OF nf0g_int_t ng_int_t] .
    also have \<open>\<dots> < \<epsilon>\<close>
    proof -
      have ineq2a: \<open>integral T (\<lambda>x. norm (f0 x - g x)) < \<epsilon>/2\<close>
      proof -
        have nf0g_int: \<open>(\<lambda>x. norm (f0 x - g x)) integrable_on UNIV\<close>
          using f0_ai g_ai absolutely_integrable_on_def set_integral_diff
          by metis
        have \<open>integral T (\<lambda>x. norm (f0 x - g x)) \<le> integral UNIV (\<lambda>x. norm (f0 x - g x))\<close>
          by (rule integral_subset_le[OF subset_UNIV nf0g_int_t nf0g_int]) simp
        also have \<open>\<dots> \<le> norm (integral UNIV (\<lambda>x. norm (f0 x - g x)))\<close>
          by auto
        also have \<open>\<dots> < \<epsilon>/2\<close>
          using g_approx .
        finally show ?thesis .
      qed
      have ineq2b: \<open>integral T (\<lambda>x. norm (g x)) < \<epsilon>/2\<close>
      proof -
        have B_int_t: \<open>(\<lambda>x. B) integrable_on T\<close>
          using \<open>T \<in> lmeasurable\<close> integrable_on_const by blast
        have \<open>integral T (\<lambda>x. norm (g x)) \<le> integral T (\<lambda>x. B)\<close>
          by (rule integral_le[OF ng_int_t B_int_t]) (use B in auto)
        also have \<open>\<dots> = B * measure lebesgue T\<close>
          using Henstock_Kurzweil_Integration.integral_mult_right[of T B "\<lambda>_. 1"] \<open>T \<in> lmeasurable\<close>
            lmeasure_integral[of T] by fastforce
        also have \<open>\<dots> < \<epsilon>/2\<close>
          using * \<open>B > 0\<close> by (simp add: field_simps)
        finally show ?thesis .
      qed
      from ineq2a ineq2b show ?thesis by linarith
    qed
    finally show "norm (integral T f) < \<epsilon>" .
  qed 
qed

text \<open>Integration by parts for absolutely integrable functions.
  The first lemma is a direct specialisation of @{thm integration_by_parts}
  to real-valued multiplication.\<close>

lemma real_integration_by_parts_simple:
  fixes f g f' g' :: "real \<Rightarrow> real" and a b y :: real
  assumes "a \<le> b"
    and "continuous_on {a..b} f" and "continuous_on {a..b} g"
    and "\<And>x. x \<in> {a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
    and "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
    and "((\<lambda>x. f x * g' x) has_integral (f b * g b - f a * g a - y)) {a..b}"
  shows "((\<lambda>x. f' x * g x) has_integral y) {a..b}"
  by (rule integration_by_parts [OF bounded_bilinear_mult]) (use assms in auto)


text \<open>Integration by parts for absolutely integrable functions with indefinite integrals.
  This is the bilinear generalisation.\<close>

lemma L1_bound:
  fixes a b :: real and hh' :: "real \<Rightarrow> 'a::euclidean_space" and h' :: "real \<Rightarrow> 'a"
  assumes x_ab: \<open>x \<in> {a..b}\<close>
    and hh'_int: \<open>hh' integrable_on {a..b}\<close>
    and h'_int: \<open>h' integrable_on {a..b}\<close>
    and norm_diff_int: \<open>(\<lambda>t. norm (h' t - hh' t)) integrable_on {a..b}\<close>
    and h_eq: \<open>h x = integral {a..x} h'\<close>
  shows \<open>norm (integral {a..x} hh' - h x) \<le> integral {a..b} (\<lambda>t. norm (h' t - hh' t))\<close>
proof -
  have ac_sub: \<open>{a..x} \<subseteq> {a..b}\<close> using x_ab by auto
  have hh'_int_x: \<open>hh' integrable_on {a..x}\<close>
    using integrable_on_subinterval[OF hh'_int ac_sub] .
  have h'_int_x: \<open>h' integrable_on {a..x}\<close>
    using integrable_on_subinterval[OF h'_int ac_sub] .
  have diff_int_x: \<open>(\<lambda>t. hh' t - h' t) integrable_on {a..x}\<close>
    using integrable_diff[OF hh'_int_x h'_int_x] .
  have norm_diff_int_x: \<open>(\<lambda>t. norm (h' t - hh' t)) integrable_on {a..x}\<close>
    using integrable_on_subinterval[OF norm_diff_int ac_sub] .
  have \<open>norm (integral {a..x} hh' - h x) = norm (integral {a..x} hh' - integral {a..x} h')\<close>
    using h_eq by simp
  also have \<open>\<dots> = norm (integral {a..x} (\<lambda>t. hh' t - h' t))\<close>
    using integral_diff[OF hh'_int_x h'_int_x] by simp
  also have \<open>\<dots> \<le> integral {a..x} (\<lambda>t. norm (h' t - hh' t))\<close>
    using integral_norm_bound_integral[OF diff_int_x norm_diff_int_x]
    by (simp add: norm_minus_commute)
  also have \<open>\<dots> \<le> integral {a..b} (\<lambda>t. norm (h' t - hh' t))\<close>
    using integral_subset_le[OF ac_sub norm_diff_int_x norm_diff_int] by simp
  finally show ?thesis .
qed

lemma uniform_from_L1:
  fixes a b :: real and hh' :: "[nat, real] \<Rightarrow> 'a::euclidean_space"
  assumes ab: \<open>a \<le> b\<close>
    and hh': \<open>\<And>n. hh' n absolutely_integrable_on {a..b} \<and>
              norm (integral {a..b} (\<lambda>x. norm (h' x - hh' n x))) < inverse (real n + 1)\<close>
    and h'_abs: \<open>h' absolutely_integrable_on {a..b}\<close>
    and h'_has: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (h' has_integral h x) {a..x}\<close>
    and hh'_cont: \<open>\<And>n. continuous_on {a..b} (hh' n)\<close>
  defines \<open>hh \<equiv> \<lambda>n x. integral {a..x} (hh' n)\<close>
  shows \<open>(\<lambda>n. SUP x\<in>{a..b}. norm (hh n x - h x)) \<longlonglongrightarrow> 0\<close>
proof -
  have h'_int: \<open>h' integrable_on {a..b}\<close>
    using h'_abs set_lebesgue_integral_eq_integral(1) by blast
  have hh'_L1: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. norm (h' x - hh' n x))) \<longlonglongrightarrow> 0\<close>
    by (metis (lifting) LIMSEQ_norm_0 Num.of_nat_simps(3) add.commute hh' inverse_eq_divide)
  have hh'n_int: \<open>hh' n integrable_on {a..b}\<close> for n
    using hh'_cont integrable_continuous_real by blast
  have norm_diff_int: \<open>(\<lambda>x. norm (h' x - hh' n x)) integrable_on {a..b}\<close> for n
    by (metis absolutely_integrable_on_def h'_abs hh' set_integral_diff(1))
  have h'int_eq: \<open>h x = integral {a..x} h'\<close> if \<open>x \<in> {a..b}\<close> for x
    using integral_unique[OF h'_has[OF that]] by simp
  show ?thesis
  proof (rule Lim_null_comparison[OF _ hh'_L1])
    show \<open>\<forall>\<^sub>F n in sequentially. norm (SUP x\<in>{a..b}. norm (hh n x - h x))
            \<le> integral {a..b} (\<lambda>x. norm (h' x - hh' n x))\<close>
    proof (intro always_eventually allI)
      fix n
      have ne: \<open>{a..b} \<noteq> {}\<close> using ab by auto
      have bound: \<open>norm (hh n x - h x) \<le> integral {a..b} (\<lambda>t. norm (h' t - hh' n t))\<close>
        if \<open>x \<in> {a..b}\<close> for x
        unfolding hh_def using L1_bound h'_int h'int_eq hh'n_int norm_diff_int that by blast
      have bdd: \<open>bdd_above ((\<lambda>x. norm (hh n x - h x)) ` {a..b})\<close>
        by (meson bdd_above.I2 bound)
      have sup_bound: \<open>(SUP x\<in>{a..b}. norm (hh n x - h x)) \<le> integral {a..b} (\<lambda>t. norm (h' t - hh' n t))\<close>
        by (metis (mono_tags, lifting) bound cSUP_least ne)
      have sup_nonneg: \<open>(SUP x\<in>{a..b}. norm (hh n x - h x)) \<ge> 0\<close>
        by (metis (no_types, lifting) ab atLeastAtMost_iff bdd cSUP_upper2 order.refl norm_ge_zero)
      show \<open>norm (SUP x\<in>{a..b}. norm (hh n x - h x)) \<le> integral {a..b} (\<lambda>x. norm (h' x - hh' n x))\<close>
        using sup_bound sup_nonneg by simp
    qed
  qed
qed


lemma pointwise:
  fixes a b::real and ff' :: "[nat,real] \<Rightarrow> 'a::euclidean_space"
  assumes c_ab: \<open>c \<in> {a..b}\<close>
    and ff': \<open>\<And>n. ff' n absolutely_integrable_on {a..b} \<and> 
              norm (integral {a..b} (\<lambda>x. norm (f' x - ff' n x))) < inverse (real n + 1)\<close>  
    and f'_abs: \<open>f' absolutely_integrable_on {a..b}\<close>
    and f'_has: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (f' has_integral f x) {a..x}\<close>
  defines \<open>ff \<equiv> \<lambda>n x. integral {a..x} (ff' n)\<close>
  shows \<open>(\<lambda>n. ff n c) \<longlonglongrightarrow> f c\<close>
proof -
  have f'_int: "f' integrable_on {a..b}"
    using f'_abs set_lebesgue_integral_eq_integral(1) by blast
  have ff'n_int: \<open>ff' n integrable_on {a..b}\<close> for n
    using absolutely_integrable_on_def ff' by blast
  have norm_diff_int: \<open>(\<lambda>x. norm (f' x - ff' n x)) integrable_on {a..b}\<close> for n
    using absolutely_integrable_on_def f'_abs set_integrable_norm ff' by blast
  have ff'_L1: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. norm (f' x - ff' n x))) \<longlonglongrightarrow> 0\<close>
    by (metis (lifting) LIMSEQ_norm_0 Num.of_nat_simps(3) add.commute ff' inverse_eq_divide)
  have f'int_eq: "f x = integral {a..x} f'" if "x \<in> {a..b}" for x
    using integral_unique[OF f'_has[OF that]] by simp
  have bound: \<open>norm (ff n c - f c) \<le> integral {a..b} (\<lambda>x. norm (f' x - ff' n x))\<close> for n
    unfolding ff_def using L1_bound c_ab f'_int f'int_eq ff'n_int norm_diff_int by blast
  show ?thesis
    using Lim_null_comparison[OF _ ff'_L1, of "(\<lambda>n. ff n c - f c)"] 
    using bound eventually_sequentially by (auto simp: LIM_zero_iff)
qed

lemma L1_inv_bound:
  fixes a b :: real and ff' :: "[nat, real] \<Rightarrow> 'a::euclidean_space"
  assumes x_ab: \<open>x \<in> {a..b}\<close>
    and ff': \<open>\<And>n. ff' n absolutely_integrable_on {a..b} \<and>
              norm (integral {a..b} (\<lambda>x. norm (f' x - ff' n x))) < inverse (real n + 1)\<close>
    and f'_abs: \<open>f' absolutely_integrable_on {a..b}\<close>
    and f'_has: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (f' has_integral f x) {a..x}\<close>
    and ff'_cont: \<open>continuous_on {a..b} (ff' n)\<close>
  defines \<open>ff \<equiv> \<lambda>x. integral {a..x} (ff' n)\<close>
  shows \<open>norm (ff x - f x) \<le> inverse (real n + 1)\<close>
proof -
  have f'_int: \<open>f' integrable_on {a..b}\<close>
    using f'_abs set_lebesgue_integral_eq_integral(1) by blast
  have ff'n_int: \<open>ff' n integrable_on {a..b}\<close>
    using ff'_cont integrable_continuous_real by blast
  have norm_diff_int: \<open>(\<lambda>t. norm (f' t - ff' n t)) integrable_on {a..b}\<close>
    by (metis absolutely_integrable_on_def f'_abs ff' set_integral_diff(1))
  have f'int_eq: \<open>f x = integral {a..x} f'\<close>
    using integral_unique[OF f'_has[OF x_ab]] by simp
  have bound: \<open>norm (ff x - f x) \<le> integral {a..b} (\<lambda>t. norm (f' t - ff' n t))\<close>
    unfolding ff_def
    using L1_bound f'_int f'int_eq ff'n_int norm_diff_int x_ab by blast
  have \<open>integral {a..b} (\<lambda>t. norm (f' t - ff' n t)) < inverse (real n + 1)\<close>
    using integral_nonneg[OF norm_diff_int] ff'[of n] by simp
  then show ?thesis using bound by linarith
qed

lemma integral_antiderivative_bound:
  fixes a b x :: real and h' :: \<open>real \<Rightarrow> 'a::banach\<close>
  assumes h'_int: \<open>h' integrable_on {a..b}\<close> and nh'_int: \<open>(\<lambda>x. norm (h' x)) integrable_on {a..b}\<close>
    and h_eq: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> h x = integral {a..x} h'\<close>
    and h'_B: \<open>integral {a..b} (\<lambda>x. norm (h' x)) \<le> B\<close> and x_ab: \<open>x \<in> {a..b}\<close>
  shows \<open>norm (h x) \<le> B\<close>
proof -
  have sub: \<open>{a..x} \<subseteq> {a..b}\<close> using x_ab by auto
  have h'_sub: \<open>h' integrable_on {a..x}\<close>
    using h'_int sub by (rule integrable_subinterval_real)
  have nh'_sub: \<open>(\<lambda>t. norm (h' t)) integrable_on {a..x}\<close>
    using nh'_int sub by (rule integrable_subinterval_real)
  have \<open>norm (h x) = norm (integral {a..x} h')\<close> using h_eq x_ab by simp
  also have \<open>\<dots> \<le> integral {a..x} (\<lambda>t. norm (h' t))\<close>
    using integral_norm_bound_integral[OF h'_sub nh'_sub] by simp
  also have \<open>\<dots> \<le> integral {a..b} (\<lambda>t. norm (h' t))\<close>
    using integral_subset_le[OF sub nh'_sub nh'_int] by simp
  also have \<open>\<dots> \<le> B\<close> using h'_B .
  finally show ?thesis .
qed

lemma bilinear_integral_bound:
  fixes bop :: \<open>'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::euclidean_space\<close>
  assumes bop_bound: \<open>\<And>u v. norm (bop u v) \<le> M * norm u * norm v\<close>
    and u_bound: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> norm (u x) \<le> C\<close>
    and v_int: \<open>(\<lambda>x. norm (v x)) integrable_on {a..b}\<close>
    and bop_int: \<open>(\<lambda>x. bop (u x) (v x)) integrable_on {a..b}\<close>
    and \<open>M \<ge> 0\<close> \<open>C \<ge> 0\<close>
  shows \<open>norm (integral {a..b} (\<lambda>x. bop (u x) (v x))) \<le> M * C * integral {a..b} (\<lambda>x. norm (v x))\<close>
proof -
  have bound_int: \<open>(\<lambda>x. M * C * norm (v x)) integrable_on {a..b}\<close>
    using integrable_cmul[OF v_int, of \<open>M * C\<close>] by (simp add: scaleR_conv_of_real mult.assoc)
  have \<open>norm (integral {a..b} (\<lambda>x. bop (u x) (v x)))
        \<le> integral {a..b} (\<lambda>x. M * C * norm (v x))\<close>
  proof (rule integral_norm_bound_integral[OF bop_int bound_int])
    fix x assume \<open>x \<in> {a..b}\<close>
    have \<open>norm (bop (u x) (v x)) \<le> M * norm (u x) * norm (v x)\<close>
      using bop_bound by blast
    also have \<open>\<dots> \<le> M * C * norm (v x)\<close>
      using u_bound[OF \<open>x \<in> {a..b}\<close>] \<open>M \<ge> 0\<close>
      by (intro mult_right_mono mult_left_mono) auto
    finally show \<open>norm (bop (u x) (v x)) \<le> M * C * norm (v x)\<close> .
  qed
  also have \<open>\<dots> = M * C * integral {a..b} (\<lambda>x. norm (v x))\<close>
    by simp
  finally show ?thesis .
qed

\<comment> \<open>Bundle of L1-approximation facts for an absolutely integrable function.
    Given @{term h'} abs.\ integrable with indefinite integral @{term h}, obtain a continuous
    approximation sequence @{term hh'} (with indefinite integrals @{term hh}) satisfying all the
    convergence and integrability properties needed for integration by parts.\<close>
lemma L1_approx_setup:
  fixes h' :: \<open>real \<Rightarrow> 'a::euclidean_space\<close> and h :: \<open>real \<Rightarrow> 'a\<close>
  assumes ab: \<open>a \<le> b\<close>
    and h'abs: \<open>h' absolutely_integrable_on {a..b}\<close>
    and h'int: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (h' has_integral h x) {a..x}\<close>
  obtains hh' hh where
    \<open>\<And>n. hh' n absolutely_integrable_on {a..b}\<close>
    \<open>\<And>n. continuous_on {a..b} (hh' n)\<close>
    \<open>\<And>n. continuous_on {a..b} (hh n)\<close>
    \<open>\<And>n. norm (integral {a..b} (\<lambda>x. norm (h' x - hh' n x))) < inverse (real n + 1)\<close>
    \<open>(\<lambda>n. integral {a..b} (\<lambda>x. norm (h' x - hh' n x))) \<longlonglongrightarrow> 0\<close>
    \<open>\<And>c. c \<in> {a..b} \<Longrightarrow> (\<lambda>n. hh n c) \<longlonglongrightarrow> h c\<close>
    \<open>(\<lambda>n. SUP x\<in>{a..b}. norm (hh n x - h x)) \<longlonglongrightarrow> 0\<close>
    \<open>\<And>n. (\<lambda>x. norm (h' x - hh' n x)) integrable_on {a..b}\<close>
    \<open>\<And>n x. x \<in> {a<..<b} \<Longrightarrow> (hh n has_vector_derivative hh' n x) (at x)\<close>
    \<open>\<And>n x. x \<in> {a..b} \<Longrightarrow> norm (hh n x - h x) \<le> inverse (real n + 1)\<close>
proof -
  have \<open>\<forall>n. \<exists>k. k absolutely_integrable_on {a..b} \<and> continuous_on UNIV k \<and> bounded (range k) \<and>
                norm (integral {a..b} (\<lambda>x. norm (h' x - k x))) < inverse (real n + 1)\<close>
    using absolutely_integrable_approximate_continuous_vector[OF _ h'abs]
    by (metis (full_types) bot_nat_0.extremum inverse_positive_iff_positive
        lmeasurable_interval(1) nat_le_real_less of_nat_0_eq_iff)
  then obtain hh' where hh'_props:
    \<open>\<And>n. hh' n absolutely_integrable_on {a..b} \<and> continuous_on UNIV (hh' n) \<and>
         bounded (range (hh' n)) \<and>
         norm (integral {a..b} (\<lambda>x. norm (h' x - hh' n x))) < inverse (real n + 1)\<close>
    unfolding choice_iff by blast
  define hh where \<open>hh \<equiv> \<lambda>n x. integral {a..x} (hh' n)\<close>
  show thesis
  proof
    show hh'_absint: \<open>hh' n absolutely_integrable_on {a..b}\<close> for n
      using hh'_props by blast
    show hh'_cont: \<open>continuous_on {a..b} (hh' n)\<close> for n
      using hh'_props continuous_on_subset by blast
    show hh'_approx: \<open>norm (integral {a..b} (\<lambda>x. norm (h' x - hh' n x))) < inverse (real n + 1)\<close> for n
      using hh'_props by blast
    show \<open>continuous_on {a..b} (hh n)\<close> for n
      unfolding hh_def using hh'_props indefinite_integral_continuous_1
        set_lebesgue_integral_eq_integral(1) by blast
    show \<open>(\<lambda>n. integral {a..b} (\<lambda>x. norm (h' x - hh' n x))) \<longlonglongrightarrow> 0\<close>
      by (metis (lifting) LIMSEQ_norm_0 Num.of_nat_simps(3) add.commute hh'_approx inverse_eq_divide)
    show \<open>(\<lambda>n. hh n c) \<longlonglongrightarrow> h c\<close> if \<open>c \<in> {a..b}\<close> for c
      unfolding hh_def using h'abs h'int hh'_props pointwise that by blast
    have hh'_conj: \<open>hh' n absolutely_integrable_on {a..b} \<and>
        norm (integral {a..b} (\<lambda>x. norm (h' x - hh' n x))) < inverse (real n + 1)\<close> for n
      using hh'_absint hh'_approx by blast
    show \<open>(\<lambda>n. SUP x\<in>{a..b}. norm (hh n x - h x)) \<longlonglongrightarrow> 0\<close>
      unfolding hh_def using uniform_from_L1[OF ab hh'_conj h'abs h'int hh'_cont] .
    show \<open>(\<lambda>x. norm (h' x - hh' n x)) integrable_on {a..b}\<close> for n
      by (metis absolutely_integrable_on_def h'abs hh'_props set_integral_diff(1))
    show \<open>(hh n has_vector_derivative hh' n x) (at x)\<close> if \<open>x \<in> {a<..<b}\<close> for n x
      using integral_has_vector_derivative[OF hh'_cont] that
      using at_within_Icc_at hh_def less_eq_real_def by fastforce
    show \<open>norm (hh n x - h x) \<le> inverse (real n + 1)\<close> if \<open>x \<in> {a..b}\<close> for n x
      unfolding hh_def using L1_inv_bound[OF that hh'_conj h'abs h'int hh'_cont] .
  qed
qed

lemma ibp_fun_setup:
  fixes h' :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes ab: \<open>a \<le> b\<close>
    and h'abs: \<open>h' absolutely_integrable_on {a..b}\<close>
    and h'int: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (h' has_integral h x) {a..x}\<close>
  shows h'int_eq: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> h x = integral {a..x} h'\<close>
    and h'_int: \<open>h' integrable_on {a..b}\<close>
    and h_cont: \<open>continuous_on {a..b} h\<close>
    and h_meas: \<open>h \<in> borel_measurable (lebesgue_on {a..b})\<close>
    and h_bounded: \<open>bounded (h ` {a..b})\<close>
    and norm_h'_int: \<open>(\<lambda>x. norm (h' x)) integrable_on {a..b}\<close>
proof -
  show eq: \<open>h x = integral {a..x} h'\<close> if \<open>x \<in> {a..b}\<close> for x
    using integral_unique[OF h'int[OF that]] by simp
  show int: \<open>h' integrable_on {a..b}\<close>
    using h'abs absolutely_integrable_on_def by blast
  show \<open>continuous_on {a..b} h\<close>
    by (metis (mono_tags, lifting) continuous_on_cong int eq indefinite_integral_continuous_1)
  then show \<open>h \<in> borel_measurable (lebesgue_on {a..b})\<close>
    using integrable_imp_measurable[OF integrable_continuous_real] by blast
  show \<open>bounded (h ` {a..b})\<close>
    using compact_continuous_image[OF \<open>continuous_on {a..b} h\<close> compact_Icc] compact_imp_bounded by blast
  show \<open>(\<lambda>x. norm (h' x)) integrable_on {a..b}\<close>
    using h'abs absolutely_integrable_on_def by blast
qed


theorem absolute_integration_by_parts:
  fixes bop :: \<open>'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::euclidean_space\<close>
    and f :: \<open>real \<Rightarrow> 'a\<close> and g :: \<open>real \<Rightarrow> 'b\<close>
    and f' :: \<open>real \<Rightarrow> 'a\<close> and g' :: \<open>real \<Rightarrow> 'b\<close>
  assumes \<open>bilinear bop\<close>
    and ab: \<open>a \<le> b\<close>
    and f'abs: \<open>f' absolutely_integrable_on {a..b}\<close>
    and g'abs: \<open>g' absolutely_integrable_on {a..b}\<close>
    and f'int: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (f' has_integral f x) {a..x}\<close>
    and g'int: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (g' has_integral g x) {a..x}\<close>
  shows \<open>(\<lambda>x. bop (f x) (g' x)) absolutely_integrable_on {a..b}\<close>
    and \<open>(\<lambda>x. bop (f' x) (g x)) absolutely_integrable_on {a..b}\<close>
    and \<open>integral {a..b} (\<lambda>x. bop (f x) (g' x)) + integral {a..b} (\<lambda>x. bop (f' x) (g x)) 
       = bop (f b) (g b) - bop (f a) (g a)\<close>
proof -
  have \<open>bounded_bilinear bop\<close>
    using \<open>bilinear bop\<close> bilinear_conv_bounded_bilinear by blast
  note f_setup = ibp_fun_setup[OF ab f'abs f'int]
  note f'int_eq = f_setup(1) and f'_int = f_setup(2) and f_cont = f_setup(3)
    and f_meas = f_setup(4) and f_bounded = f_setup(5) and norm_f'_int = f_setup(6)
  note g_setup = ibp_fun_setup[OF ab g'abs g'int]
  note g'int_eq = g_setup(1) and g'_int = g_setup(2) and g_cont = g_setup(3)
    and g_meas = g_setup(4) and g_bounded = g_setup(5) and norm_g'_int = g_setup(6)
  have ab_sets: "{a..b} \<in> sets lebesgue"
    by simp
  have bop_swap: "bilinear (\<lambda>x y. bop y x)"
    using \<open>bilinear bop\<close> by (simp add: bilinear_def)
  show "(\<lambda>x. bop (f x) (g' x)) absolutely_integrable_on {a..b}"
    using absolutely_integrable_bounded_measurable_product[OF \<open>bilinear bop\<close> f_meas ab_sets f_bounded g'abs] .
  show "(\<lambda>x. bop (f' x) (g x)) absolutely_integrable_on {a..b}"
    using absolutely_integrable_bounded_measurable_product[OF bop_swap g_meas ab_sets g_bounded f'abs] .
\<comment> \<open>Obtain continuous L1 approximation sequences for @{term f'} and @{term g'}.\<close>
  obtain ff' ff where
    ff'_absint: \<open>\<And>n. ff' n absolutely_integrable_on {a..b}\<close> and
    ff'_cont_ab: \<open>\<And>n. continuous_on {a..b} (ff' n)\<close> and
    ff_cont: \<open>\<And>n. continuous_on {a..b} (ff n)\<close> and
    ff'_approx: \<open>\<And>n. norm (integral {a..b} (\<lambda>x. norm (f' x - ff' n x))) < inverse (real n + 1)\<close> and
    ff'_L1: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. norm (f' x - ff' n x))) \<longlonglongrightarrow> 0\<close> and
    ff_ptwise: \<open>\<And>c. c \<in> {a..b} \<Longrightarrow> (\<lambda>n. ff n c) \<longlonglongrightarrow> f c\<close> and
    ff_uniform: \<open>(\<lambda>n. SUP x\<in>{a..b}. norm (ff n x - f x)) \<longlonglongrightarrow> 0\<close> and
    norm_ff'_diff_int: \<open>\<And>n. (\<lambda>x. norm (f' x - ff' n x)) integrable_on {a..b}\<close> and
    ff_deriv: \<open>\<And>n x. x \<in> {a<..<b} \<Longrightarrow> (ff n has_vector_derivative ff' n x) (at x)\<close> and
    ff_inv_bound: \<open>\<And>n x. x \<in> {a..b} \<Longrightarrow> norm (ff n x - f x) \<le> inverse (real n + 1)\<close>
    using L1_approx_setup[OF ab f'abs f'int] by blast
  obtain gg' gg where
    gg'_absint: \<open>\<And>n. gg' n absolutely_integrable_on {a..b}\<close> and
    gg'_cont_ab: \<open>\<And>n. continuous_on {a..b} (gg' n)\<close> and
    gg_cont: \<open>\<And>n. continuous_on {a..b} (gg n)\<close> and
    gg'_approx: \<open>\<And>n. norm (integral {a..b} (\<lambda>x. norm (g' x - gg' n x))) < inverse (real n + 1)\<close> and
    gg'_L1: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. norm (g' x - gg' n x))) \<longlonglongrightarrow> 0\<close> and
    gg_ptwise: \<open>\<And>c. c \<in> {a..b} \<Longrightarrow> (\<lambda>n. gg n c) \<longlonglongrightarrow> g c\<close> and
    gg_uniform: \<open>(\<lambda>n. SUP x\<in>{a..b}. norm (gg n x - g x)) \<longlonglongrightarrow> 0\<close> and
    norm_gg'_diff_int: \<open>\<And>n. (\<lambda>x. norm (g' x - gg' n x)) integrable_on {a..b}\<close> and
    gg_deriv: \<open>\<And>n x. x \<in> {a<..<b} \<Longrightarrow> (gg n has_vector_derivative gg' n x) (at x)\<close> and
    gg_inv_bound: \<open>\<And>n x. x \<in> {a..b} \<Longrightarrow> norm (gg n x - g x) \<le> inverse (real n + 1)\<close>
    using L1_approx_setup[OF ab g'abs g'int] by blast
\<comment> \<open>Bilinear product is absolutely integrable when one factor is abs.\ integrable
    and the other is continuous on the compact interval.\<close>
  have bop_absint_cont1: \<open>(\<lambda>x. bop (h x) (k x)) absolutely_integrable_on {a..b}\<close>
    if \<open>h absolutely_integrable_on {a..b}\<close> \<open>continuous_on {a..b} k\<close> for h :: \<open>real \<Rightarrow> 'a\<close> and k :: \<open>real \<Rightarrow> 'b\<close>
    using continuous_imp_measurable_on_sets_lebesgue[OF that(2) ab_sets] 
    using compact_imp_bounded[OF compact_continuous_image[OF that(2) compact_Icc]]
    using ab_sets absolutely_integrable_bounded_measurable_product bop_swap that(1) by blast 
  have bop_absint_cont2: \<open>(\<lambda>x. bop (h x) (k x)) absolutely_integrable_on {a..b}\<close>
    if \<open>continuous_on {a..b} h\<close> \<open>k absolutely_integrable_on {a..b}\<close> for h :: \<open>real \<Rightarrow> 'a\<close> and k :: \<open>real \<Rightarrow> 'b\<close>
    by (simp add: absolutely_integrable_bounded_measurable_product assms(1) compact_continuous_image
        compact_imp_bounded continuous_imp_measurable_on_sets_lebesgue that)
  define S where \<open>S \<equiv> \<lambda>n.
      (integral {a..b} (\<lambda>x. bop (ff n x) (gg' n x)) +
       integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x))) -
      (bop (ff n b) (gg n b) - bop (ff n a) (gg n a))\<close>
  have \<open>S n = 0\<close> for n
  proof -
    have bop_int1: \<open>(\<lambda>x. bop (ff n x) (gg' n x)) integrable_on {a..b}\<close>
      using bop_absint_cont2[OF ff_cont gg'_cont_ab[THEN absolutely_integrable_continuous_real]]
        set_lebesgue_integral_eq_integral(1) by blast
    have ibp: \<open>((\<lambda>x. bop (ff' n x) (gg n x)) has_integral
            (bop (ff n b) (gg n b) - bop (ff n a) (gg n a) - integral {a..b} (\<lambda>x. bop (ff n x) (gg' n x)))) {a..b}\<close>
      using integration_by_parts_interior[OF \<open>bounded_bilinear bop\<close> ab ff_cont gg_cont ff_deriv gg_deriv]
      by (simp add: bop_int1 integrable_integral)
    show ?thesis
      using integral_unique[OF ibp] by (simp add: S_def algebra_simps)
  qed
  then have lim_zero: \<open>S \<longlonglongrightarrow> 0\<close>
    by (simp add: lim_explicit)
  obtain K where \<open>K > 0\<close> and K: \<open>\<And>u v. norm (bop u v) \<le> norm u * norm v * K\<close>
    using bounded_bilinear.pos_bounded[OF \<open>bounded_bilinear bop\<close>] by blast
  have \<open>(\<lambda>n. bop (ff n c) (gg n c)) \<longlonglongrightarrow> bop (f c) (g c)\<close> if c_ab: \<open>c \<in> {a..b}\<close> for c
    using \<open>bounded_bilinear bop\<close> bounded_bilinear.tendsto c_ab ff_ptwise gg_ptwise by blast
  then have *: \<open>(\<lambda>n. bop (ff n b) (gg n b) - bop (ff n a) (gg n a)) 
         \<longlonglongrightarrow> bop (f b) (g b) - bop (f a) (g a)\<close>
    by (simp add: ab tendsto_diff)
  obtain ff_a: \<open>(\<lambda>n. ff n a) \<longlonglongrightarrow> f a\<close> and ff_b: \<open>(\<lambda>n. ff n b) \<longlonglongrightarrow> f b\<close>
    by (simp add: ab ff_ptwise)
  obtain gg_a: \<open>(\<lambda>n. gg n a) \<longlonglongrightarrow> g a\<close> and gg_b: \<open>(\<lambda>n. gg n b) \<longlonglongrightarrow> g b\<close>
    by (simp add: ab gg_ptwise)
      \<comment> \<open>Bilinear limit at endpoints.\<close>
  have bop_b: \<open>(\<lambda>n. bop (ff n b) (gg n b)) \<longlonglongrightarrow> bop (f b) (g b)\<close>
    using Lim_bilinear[OF ff_b gg_b \<open>bounded_bilinear bop\<close>] .
  have bop_a: \<open>(\<lambda>n. bop (ff n a) (gg n a)) \<longlonglongrightarrow> bop (f a) (g a)\<close>
    using Lim_bilinear[OF ff_a gg_a \<open>bounded_bilinear bop\<close>] .
      \<comment> \<open>Obtain @{term B} bounding integral norms of $|f'|$ and $|g'|$.\<close>
  obtain B where \<open>B > 0\<close> and B_f': \<open>integral {a..b} (\<lambda>x. norm (f' x)) \<le> B\<close>
    and B_g': \<open>integral {a..b} (\<lambda>x. norm (g' x)) \<le> B\<close>
    by (smt (verit, best) gt_ex)
      \<comment> \<open>Bound on sup norm of @{term f} on @{term \<open>{a..b}\<close>}.\<close>
  obtain M_f where \<open>M_f > 0\<close> and M_f: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> norm (f x) \<le> M_f\<close>
    using bounded_normE[OF f_bounded] by (metis image_eqI)

  obtain M where "M>0" and M: "norm (bop x y) \<le> M * norm x * norm y" for x y
    using assms(1) bilinear_bounded_pos by blast
  define \<phi> where "\<phi> \<equiv> \<lambda>n. 2 * M * B * inverse(real n + 1) + M * inverse(real n + 1)^2"
    \<comment> \<open>Integral convergence: int1.\<close> \<comment> \<open>Could this be done better following int2?\<close>
  have int1: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. bop (ff n x) (gg' n x))) \<longlonglongrightarrow>
               integral {a..b} (\<lambda>x. bop (f x) (g' x))\<close>
  proof (rule LIM_zero_iff[THEN iffD1])
    \<comment> \<open>Decompose the integrand difference using bilinearity.\<close>
    have decomp: \<open>bop (ff n x) (gg' n x) - bop (f x) (g' x) =
            bop (ff n x - f x) (gg' n x - g' x) + bop (ff n x - f x) (g' x) +
            bop (f x) (gg' n x - g' x)\<close> for n x
      using bounded_bilinear.prod_diff_prod[OF \<open>bounded_bilinear bop\<close>] by blast
        \<comment> \<open>Integrability of each term.\<close>
    have fg'_int: \<open>(\<lambda>x. bop (f x) (g' x)) integrable_on {a..b}\<close>
      using set_lebesgue_integral_eq_integral(1)
        [OF bop_absint_cont2[OF f_cont g'abs]] .
    have ffgg'_int: \<open>(\<lambda>x. bop (ff n x) (gg' n x)) integrable_on {a..b}\<close> for n
      by (simp add: bop_absint_cont2 ff_cont gg'_absint set_lebesgue_integral_eq_integral(1))
        \<comment> \<open>Now show the integral of the decomposed sum $\to 0$.\<close>
    have eq: \<open>integral {a..b} (\<lambda>x. bop (ff n x) (gg' n x)) - integral {a..b} (\<lambda>x. bop (f x) (g' x))
                = integral {a..b} (\<lambda>x. bop (ff n x) (gg' n x) - bop (f x) (g' x))\<close> for n
      by (simp add: Henstock_Kurzweil_Integration.integral_diff ffgg'_int fg'_int)
        \<comment> \<open>Integrability of each bilinear term.\<close>
    have t1_int: \<open>(\<lambda>x. bop (ff n x - f x) (gg' n x - g' x)) integrable_on {a..b}\<close> for n
      by (metis bop_absint_cont2 continuous_on_diff f_cont ff_cont g'abs gg'_absint set_integral_diff(1)
          set_lebesgue_integral_eq_integral(1))
    have t2_int: \<open>(\<lambda>x. bop (ff n x - f x) (g' x)) integrable_on {a..b}\<close> for n
      using assms by (metis absolutely_integrable_on_def bop_absint_cont2 continuous_on_diff f_cont ff_cont g'abs)
    have t3_int: \<open>(\<lambda>x. bop (f x) (gg' n x - g' x)) integrable_on {a..b}\<close> for n
      using absolutely_integrable_on_def assms(4) bop_absint_cont2 f_cont gg'_absint by blast
    show "(\<lambda>n. integral {a..b} (\<lambda>x. bop (ff n x) (gg' n x)) -
                 integral {a..b} (\<lambda>x. bop (f x) (g' x))) \<longlonglongrightarrow> 0"
    proof -
      \<comment> \<open>@{term bdd_above} for the uniform-convergence sup.\<close>
      have bdd_ff: \<open>bdd_above ((\<lambda>x. norm (ff n x - f x)) ` {a..b})\<close> for n
        by (meson bdd_above.I2 ff_inv_bound)
      have sup_bound: \<open>norm (ff n x - f x) \<le> (SUP x\<in>{a..b}. norm (ff n x - f x))\<close>
        if \<open>x \<in> {a..b}\<close> for n x
        using cSUP_upper[OF that bdd_ff] .
          \<comment> \<open>Term 1: $\int \mathrm{bop}(ff\,n - f)(gg'\,n - g') \to 0$.\<close>
      have I1: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. bop (ff n x - f x) (gg' n x - g' x))) \<longlonglongrightarrow> 0\<close>
      proof -
        have lim_bound: \<open>(\<lambda>n. M * ((SUP x\<in>{a..b}. norm (ff n x - f x)) *
              integral {a..b} (\<lambda>x. norm (g' x - gg' n x)))) \<longlonglongrightarrow> 0\<close>
          using ff_uniform gg'_L1 tendsto_mult_right_zero tendsto_mult_zero by blast
        show ?thesis
        proof (rule Lim_null_comparison[OF _ lim_bound])
          show \<open>\<forall>\<^sub>F n in sequentially. norm (integral {a..b} (\<lambda>x. bop (ff n x - f x) (gg' n x - g' x)))
                 \<le> M * ((SUP x\<in>{a..b}. norm (ff n x - f x)) * integral {a..b} (\<lambda>x. norm (g' x - gg' n x)))\<close>
          proof (intro always_eventually allI)
            fix n
            have \<open>norm (integral {a..b} (\<lambda>x. bop (ff n x - f x) (gg' n x - g' x)))
                  \<le> M * (SUP x\<in>{a..b}. norm (ff n x - f x)) * integral {a..b} (\<lambda>x. norm (gg' n x - g' x))\<close>
              using bilinear_integral_bound[OF M sup_bound _ t1_int]
                norm_gg'_diff_int[of n] \<open>M > 0\<close> cSUP_upper[OF _ bdd_ff] ab
              by (auto simp: norm_minus_commute intro: order.trans[OF norm_ge_zero])
            then show \<open>norm (integral {a..b} (\<lambda>x. bop (ff n x - f x) (gg' n x - g' x))) \<le>
                  M * ((SUP x\<in>{a..b}. norm (ff n x - f x)) *
                  integral {a..b} (\<lambda>x. norm (g' x - gg' n x)))\<close>
              by (simp add: norm_minus_commute mult.assoc)
          qed
        qed
      qed
      show ?thesis
      proof -
        have I2: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. bop (ff n x - f x) (g' x))) \<longlonglongrightarrow> 0\<close>
        proof (rule Lim_null_comparison)
          show \<open>\<forall>\<^sub>F n in sequentially. norm (integral {a..b} (\<lambda>x. bop (ff n x - f x) (g' x))) \<le>
                M * (SUP x\<in>{a..b}. norm (ff n x - f x)) * integral {a..b} (\<lambda>x. norm (g' x))\<close>
          proof (intro always_eventually allI)
            fix n
            show \<open>norm (integral {a..b} (\<lambda>x. bop (ff n x - f x) (g' x))) \<le>
                  M * (SUP x\<in>{a..b}. norm (ff n x - f x)) * integral {a..b} (\<lambda>x. norm (g' x))\<close>
              using bilinear_integral_bound[OF M sup_bound norm_g'_int t2_int]
                \<open>M > 0\<close> cSUP_upper[OF _ bdd_ff] ab by (auto intro: order.trans[OF norm_ge_zero])
          qed
        next
          show \<open>(\<lambda>n. M * (SUP x\<in>{a..b}. norm (ff n x - f x)) * integral {a..b} (\<lambda>x. norm (g' x))) \<longlonglongrightarrow> 0\<close>
            using ff_uniform tendsto_mult_left[of _ 0 sequentially M]
            using tendsto_mult_left_zero by fastforce
        qed
        have I3: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. bop (f x) (gg' n x - g' x))) \<longlonglongrightarrow> 0\<close>
        proof (rule Lim_null_comparison[where g=\<open>\<lambda>n. M * M_f * integral {a..b} (\<lambda>x. norm (g' x - gg' n x))\<close>])
          show \<open>\<forall>\<^sub>F n in sequentially. norm (integral {a..b} (\<lambda>x. bop (f x) (gg' n x - g' x))) \<le>
                M * M_f * integral {a..b} (\<lambda>x. norm (g' x - gg' n x))\<close>
          proof (intro always_eventually allI)
            fix n
            have \<open>norm (integral {a..b} (\<lambda>x. bop (f x) (gg' n x - g' x)))
                  \<le> M * M_f * integral {a..b} (\<lambda>x. norm (gg' n x - g' x))\<close>
              using bilinear_integral_bound[OF M M_f _ t3_int]
                norm_gg'_diff_int[of n] \<open>M > 0\<close> \<open>M_f > 0\<close>
              by (simp add: norm_minus_commute)
            then show \<open>norm (integral {a..b} (\<lambda>x. bop (f x) (gg' n x - g' x))) \<le>
                  M * M_f * integral {a..b} (\<lambda>x. norm (g' x - gg' n x))\<close>
              by (simp add: norm_minus_commute)
          qed
        next
          show \<open>(\<lambda>n. M * M_f * integral {a..b} (\<lambda>x. norm (g' x - gg' n x))) \<longlonglongrightarrow> 0\<close>
            using gg'_L1 tendsto_mult_right_zero by blast
        qed
        show ?thesis
        proof -
          have sum_eq: \<open>integral {a..b} (\<lambda>x. bop (ff n x) (gg' n x) - bop (f x) (g' x)) =
                integral {a..b} (\<lambda>x. bop (ff n x - f x) (gg' n x - g' x)) +
                integral {a..b} (\<lambda>x. bop (ff n x - f x) (g' x)) +
                integral {a..b} (\<lambda>x. bop (f x) (gg' n x - g' x))\<close> (is "?L = ?R") for n 
          proof -
            have \<open>?L = integral {a..b} (\<lambda>x. bop (ff n x - f x) (gg' n x - g' x) + bop (ff n x - f x) (g' x) +
                      bop (f x) (gg' n x - g' x))\<close>
              by (simp only: decomp)
            also have \<open>\<dots> = ?R\<close>
              by (simp add: Henstock_Kurzweil_Integration.integrable_add
                  Henstock_Kurzweil_Integration.integral_add t1_int t2_int t3_int)
            finally show ?thesis .
          qed
          then show ?thesis
            using I1 I2 I3 add_0 sum_eq by (simp add: eq tendsto_add_zero)
        qed
      qed
    qed
  qed

  have int2: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x))) \<longlonglongrightarrow>
               integral {a..b} (\<lambda>x. bop (f' x) (g x))\<close>
  proof (rule LIM_zero_iff[THEN iffD1, OF Lim_null_comparison])
    \<comment> \<open>Integrability of limit and approximation terms.\<close>
    have fg'_int: \<open>(\<lambda>x. bop (f' x) (g x)) integrable_on {a..b}\<close>
      using \<open>(\<lambda>x. bop (f' x) (g x)) absolutely_integrable_on {a..b}\<close>
        set_lebesgue_integral_eq_integral(1) by blast
    have ffgg'_int: \<open>(\<lambda>x. bop (ff' n x) (gg n x)) integrable_on {a..b}\<close> for n
      by (simp add: bop_absint_cont1 ff'_absint gg_cont set_lebesgue_integral_eq_integral(1))
    have eq: \<open>integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x)) - integral {a..b} (\<lambda>x. bop (f' x) (g x))
                = integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x) - bop (f' x) (g x))\<close> for n
      by (simp add: Henstock_Kurzweil_Integration.integral_diff ffgg'_int fg'_int)

    have g_bound: \<open>norm (g x) \<le> B\<close> if \<open>x \<in> {a..b}\<close> for x
    proof -
      have ac_sub: \<open>{a..x} \<subseteq> {a..b}\<close> using that by auto
      have \<open>norm (g x) = norm (integral {a..x} g')\<close> 
        using g'int_eq that by presburger
      also have \<open>\<dots> \<le> integral {a..x} (\<lambda>t. norm (g' t))\<close>
        using integral_norm_bound_integral
          [OF integrable_on_subinterval[OF g'_int ac_sub]
              integrable_on_subinterval[OF norm_g'_int ac_sub]] by simp
      also have \<open>\<dots> \<le> integral {a..b} (\<lambda>t. norm (g' t))\<close>
        using integral_subset_le[OF ac_sub
            integrable_on_subinterval[OF norm_g'_int ac_sub] norm_g'_int] by simp
      also have \<open>\<dots> \<le> B\<close> using B_g' .
      finally show ?thesis .
    qed

    have gg_bound: \<open>norm (gg n x) \<le> B + inverse (real n + 1)\<close>
      if \<open>x \<in> {a..b}\<close> for n x
      using norm_triangle_sub[of "gg n x" "g x"] g_bound[OF that] gg_inv_bound[OF that, of n]
      by linarith
    show "\<forall>\<^sub>F n in sequentially.
               norm (integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x)) -
                     integral {a..b} (\<lambda>x. bop (f' x) (g x))) \<le> \<phi> n"
    proof (rule eventually_sequentiallyI [of 1])
      fix n :: nat
      assume "1 \<le> n"
      have \<section>: \<open>bop a b - bop c d = (bop a b - bop c b) + (bop c b - bop c d)\<close> for a b c d
        by simp
      have f'gg_int: \<open>(\<lambda>x. bop (f' x) (gg n x)) integrable_on {a..b}\<close>
        using set_lebesgue_integral_eq_integral(1)[OF bop_absint_cont1[OF assms(3) gg_cont]] .
      have split_int: \<open>integral {a..b}
           (\<lambda>x. bop (ff' n x) (gg n x) - bop (f' x) (gg n x) +
                (bop (f' x) (gg n x) - bop (f' x) (g x))) =
           integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x) - bop (f' x) (gg n x)) +
           integral {a..b} (\<lambda>x. bop (f' x) (gg n x) - bop (f' x) (g x))\<close>
        by (intro Henstock_Kurzweil_Integration.integral_add
            Henstock_Kurzweil_Integration.integrable_diff ffgg'_int f'gg_int fg'_int)
      have "norm (integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x) - bop (f' x) (g x))) \<le> \<phi> n"
      proof -
        have M_swap: \<open>norm ((\<lambda>x y. bop y x) u v) \<le> M * norm u * norm v\<close> for u v
          using M[of v u] by (simp add: mult.commute mult.left_commute)
        have diff_left: \<open>bop (ff' n x) (gg n x) - bop (f' x) (gg n x)
                         = bop (ff' n x - f' x) (gg n x)\<close> for x
          using bounded_bilinear.diff_left[OF \<open>bounded_bilinear bop\<close>] by simp
        have diff_right: \<open>bop (f' x) (gg n x) - bop (f' x) (g x) = bop (f' x) (gg n x - g x)\<close> for x
          using bounded_bilinear.diff_right[OF \<open>bounded_bilinear bop\<close>] by simp
            \<comment> \<open>I1: $\lVert\int \mathrm{bop}(ff'\,n - f',\, gg\,n)\rVert \le M \cdot (B + 1/(n{+}1)) \cdot 1/(n{+}1)$.\<close>
        have I1: \<open>norm (integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x) - bop (f' x) (gg n x)))
                  \<le> M * (B + inverse (real n + 1)) * inverse (real n + 1)\<close>
        proof -
          have int1: \<open>(\<lambda>x. (\<lambda>u v. bop v u) (gg n x) (ff' n x - f' x)) integrable_on {a..b}\<close>
            using Henstock_Kurzweil_Integration.integrable_diff[OF ffgg'_int f'gg_int]
            by (simp add: diff_left[symmetric])
          have \<open>norm (integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x) - bop (f' x) (gg n x)))
                = norm (integral {a..b} (\<lambda>x. (\<lambda>u v. bop v u) (gg n x) (ff' n x - f' x)))\<close>
            by (simp add: diff_left)
          also have \<open>\<dots> \<le> M * (B + inverse (real n + 1)) * integral {a..b} (\<lambda>x. norm (ff' n x - f' x))\<close>
            using bilinear_integral_bound[OF M_swap gg_bound _ int1] norm_ff'_diff_int[of n]
              \<open>M > 0\<close> \<open>B > 0\<close> by (auto simp: norm_minus_commute)
          also have \<open>\<dots> \<le> M * (B + inverse (real n + 1)) * inverse (real n + 1)\<close>
            using ff'_approx[of n] \<open>M > 0\<close> \<open>B > 0\<close>
            by (intro mult_left_mono) (auto simp: norm_minus_commute)
          finally show ?thesis .
        qed
            \<comment> \<open>I2: $\lVert\int \mathrm{bop}(f',\, gg\,n - g)\rVert \le M \cdot B \cdot 1/(n{+}1)$.\<close>
        have I2: \<open>norm (integral {a..b} (\<lambda>x. bop (f' x) (gg n x) - bop (f' x) (g x)))
                   \<le> M * B * inverse (real n + 1)\<close>
        proof -
          have bop_int: \<open>(\<lambda>x. (\<lambda>u v. bop v u) (gg n x - g x) (f' x)) integrable_on {a..b}\<close>
            using Henstock_Kurzweil_Integration.integrable_diff[OF f'gg_int fg'_int]
            by (simp add: diff_right)
          have \<open>norm (integral {a..b} (\<lambda>x. bop (f' x) (gg n x) - bop (f' x) (g x)))
                = norm (integral {a..b} (\<lambda>x. (\<lambda>u v. bop v u) (gg n x - g x) (f' x)))\<close>
            by (simp add: diff_right)
          also have \<open>\<dots> \<le> M * inverse (real n + 1) * integral {a..b} (\<lambda>x. norm (f' x))\<close>
            using bilinear_integral_bound[OF M_swap gg_inv_bound norm_f'_int bop_int] \<open>M > 0\<close>
            by auto
          also have \<open>\<dots> \<le> M * inverse (real n + 1) * B\<close>
            using B_f' \<open>M > 0\<close> by (intro mult_left_mono) auto
          also have \<open>\<dots> = M * B * inverse (real n + 1)\<close>
            by (simp add: mult.commute mult.left_commute)
          finally show ?thesis .
        qed
        have step1: \<open>integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x) - bop (f' x) (g x))
               = integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x) - bop (f' x) (gg n x)) +
                 integral {a..b} (\<lambda>x. bop (f' x) (gg n x) - bop (f' x) (g x))\<close>
          using split_int by auto
        have \<open>norm (integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x) - bop (f' x) (g x)))
               \<le> norm (integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x) - bop (f' x) (gg n x))) +
                 norm (integral {a..b} (\<lambda>x. bop (f' x) (gg n x) - bop (f' x) (g x)))\<close>
          by (subst step1, rule norm_triangle_ineq)
        also have \<open>\<dots> \<le> M * (B + inverse (real n + 1)) * inverse (real n + 1) +
                         M * B * inverse (real n + 1)\<close>
          by (intro add_mono I1 I2)
        also have \<open>\<dots> = \<phi> n\<close>
          unfolding \<phi>_def by (simp add: algebra_simps power2_eq_square)
        finally show ?thesis .
      qed
      then show "norm (integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x)) - integral {a..b} (\<lambda>x. bop (f' x) (g x))) \<le> \<phi> n"
        by (simp add: eq)
    qed
    show "\<phi> \<longlonglongrightarrow> 0"
      unfolding \<phi>_def by real_asymp
  qed
  then have \<open>S \<longlonglongrightarrow> (integral {a..b} (\<lambda>x. bop (f x) (g' x)) + integral {a..b} (\<lambda>x. bop (f' x) (g x)))
              - (bop (f b) (g b) - bop (f a) (g a))\<close>
    unfolding S_def
    using tendsto_diff[OF tendsto_add[OF int1 int2] tendsto_diff[OF bop_b bop_a]]
    by blast 
  then show "integral {a..b} (\<lambda>x. bop (f x) (g' x)) + integral {a..b} (\<lambda>x. bop (f' x) (g x))
       = bop (f b) (g b) - bop (f a) (g a)"
    using lim_zero LIMSEQ_unique eq_iff_diff_eq_0 by blast
qed

text \<open>The real-valued specialisation: HOL Light's @{text ABSOLUTE_REAL_INTEGRATION_BY_PARTS}.\<close>

lemma absolute_real_integration_by_parts:
  fixes f g f' g' :: "real \<Rightarrow> real"
  assumes ab: "a \<le> b"
    and f'abs: "f' absolutely_integrable_on {a..b}"
    and g'abs: "g' absolutely_integrable_on {a..b}"
    and f'int: "\<And>x. x \<in> {a..b} \<Longrightarrow> (f' has_integral f x) {a..x}"
    and g'int: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g' has_integral g x) {a..x}"
  shows fg'_abs: "(\<lambda>x. f x * g' x) absolutely_integrable_on {a..b}"
    and f'g_abs: "(\<lambda>x. f' x * g x) absolutely_integrable_on {a..b}"
    and ibp_eq: "integral {a..b} (\<lambda>x. f x * g' x) +
      integral {a..b} (\<lambda>x. f' x * g x) = f b * g b - f a * g a"
  using absolute_integration_by_parts[OF bilinear_times ab f'abs g'abs f'int g'int]
  by auto
  
lemma absolutely_integrable_bounded_variation_eq:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  shows \<open>f absolutely_integrable_on (cbox a b) \<longleftrightarrow>
         f integrable_on (cbox a b) \<and> has_bounded_variation_on (\<lambda>t. integral (cbox a t) f) (cbox a b)\<close>
proof (cases \<open>f integrable_on cbox a b\<close>)
  case False
  then show ?thesis
    by (auto simp: absolutely_integrable_on_def)
next
  case fint: True
  show ?thesis
  proof (intro iffI conjI)
    assume abs: \<open>f absolutely_integrable_on cbox a b\<close>
    from abs show \<open>f integrable_on cbox a b\<close>
      by (simp add: absolutely_integrable_on_def)
    show \<open>has_bounded_variation_on (\<lambda>t. integral (cbox a t) f) (cbox a b)\<close>
      unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
    proof (intro exI strip)
      fix d T
      assume dt: \<open>d division_of T \<and> T \<subseteq> cbox a b\<close>
      from abs have nint: \<open>(\<lambda>x. norm (f x)) integrable_on cbox a b\<close>
        by (simp add: absolutely_integrable_on_def)
      have \<open>(\<Sum>k\<in>d. norm (integral (cbox a (Sup k)) f - integral (cbox a (Inf k)) f))
            \<le> integral (cbox a b) (\<lambda>x. norm (f x))\<close>
      proof -
        have div: \<open>d division_of T\<close> and sub: \<open>T \<subseteq> cbox a b\<close> using dt by auto
        have step1: \<open>\<And>k. k \<in> d \<Longrightarrow>
          integral (cbox a (Sup k)) f - integral (cbox a (Inf k)) f = integral k f\<close>
        proof -
          fix k assume kd: \<open>k \<in> d\<close>
          obtain c e where ke: \<open>k = cbox c e\<close>
            using division_ofD(4)[OF div kd] by auto
          have ce: \<open>c \<le> e\<close>
            using division_ofD(3)[OF div kd] ke
            by (simp add: box_real atLeastatMost_empty_iff)
          have ksub: \<open>k \<subseteq> cbox a b\<close> using division_ofD(2)[OF div kd] sub by auto
          then have ac: \<open>a \<le> c\<close> and eb: \<open>e \<le> b\<close>
            using ke ce by (auto simp: box_real atLeastatMost_subset_iff)
          have fint_ae: \<open>f integrable_on {a..e}\<close>
            using integrable_subinterval_real[OF fint[unfolded box_real]]
              ac ce eb by (auto simp: atLeastatMost_subset_iff)
          have eq: \<open>integral {a..c} f + integral {c..e} f = integral {a..e} f\<close>
            using Henstock_Kurzweil_Integration.integral_combine[OF ac ce fint_ae] by simp
          have \<open>Sup k = e\<close> \<open>Inf k = c\<close>
            using ke ce by (simp_all add: box_real interval_bounds_real)
          then show \<open>integral (cbox a (Sup k)) f - integral (cbox a (Inf k)) f = integral k f\<close>
            using eq ke by (simp add: box_real algebra_simps)
        qed
        have step2: \<open>\<And>k. k \<in> d \<Longrightarrow> norm (integral k f) \<le> integral k (\<lambda>x. norm (f x))\<close>
          by (smt (verit, ccfv_SIG) integral_norm_bound_integral fint
              division_ofD(2,4) dt elementary_interval integrable_on_subdivision nint)
        have nf_int_t: \<open>(\<lambda>x. norm (f x)) integrable_on T\<close>
          using integrable_on_subdivision[OF div nint sub] .
        have \<open>(\<Sum>k\<in>d. norm (integral (cbox a (Sup k)) f - integral (cbox a (Inf k)) f))
              = (\<Sum>k\<in>d. norm (integral k f))\<close>
          by (rule sum.cong[OF refl]) (use step1 in auto)
        also have \<open>\<dots> \<le> (\<Sum>k\<in>d. integral k (\<lambda>x. norm (f x)))\<close>
          by (rule sum_mono) (use step2 in auto)
        also have \<open>\<dots> = integral T (\<lambda>x. norm (f x))\<close>
          using integral_combine_division_topdown[OF nf_int_t div] by simp
        also have \<open>\<dots> \<le> integral (cbox a b) (\<lambda>x. norm (f x))\<close> 
          using integral_subset_le[OF sub nf_int_t nint] by auto
        finally show ?thesis .
      qed
      then show \<open>(\<Sum>k\<in>d. norm ((\<lambda>t. integral (cbox a t) f) (Sup k) -
                               (\<lambda>t. integral (cbox a t) f) (Inf k))) \<le>
                  integral (cbox a b) (\<lambda>x. norm (f x))\<close>
        by simp
    qed
  next
    assume rhs: \<open>f integrable_on cbox a b \<and>
      has_bounded_variation_on (\<lambda>t. integral (cbox a t) f) (cbox a b)\<close>
    show \<open>f absolutely_integrable_on cbox a b\<close>
    proof -
      from rhs have bv: \<open>has_bounded_variation_on (\<lambda>t. integral (cbox a t) f) (cbox a b)\<close>
        by simp
      have key: \<open>\<And>c d. c \<le> d \<Longrightarrow> {c..d} \<subseteq> {a..b} \<Longrightarrow>
        integral {c..d} f = integral {a..d} f - integral {a..c} f\<close>
      proof -
        fix c d :: real assume cd: \<open>c \<le> d\<close> and sub: \<open>{c..d} \<subseteq> {a..b}\<close>
        from sub cd have ac: \<open>a \<le> c\<close> and db: \<open>d \<le> b\<close>
          by auto
        have fint_ad: \<open>f integrable_on {a..d}\<close>
          using integrable_subinterval_real[OF fint[unfolded box_real]] ac cd db
          by auto
        have eq: \<open>integral {a..c} f + integral {c..d} f = integral {a..d} f\<close>
          using Henstock_Kurzweil_Integration.integral_combine[OF ac cd fint_ad] by simp
        show \<open>integral {c..d} f = integral {a..d} f - integral {a..c} f\<close>
          using eq by (simp add: algebra_simps)
      qed
      have integral_eq: \<open>integral K f =
        integral (cbox a (Sup K)) f - integral (cbox a (Inf K)) f\<close>
        if div: \<open>d division_of cbox a b\<close> and Kd: \<open>K \<in> d\<close> for d K
        by (metis Kd atLeastatMost_empty_iff cSup_atLeastAtMost cbox_division_memE cbox_interval
            div interval_bounds_real(2) key)
      have sum_eq: \<open>(\<Sum>K\<in>d. norm (integral K f)) =
        (\<Sum>K\<in>d. norm (integral (cbox a (Sup K)) f - integral (cbox a (Inf K)) f))\<close>
        if \<open>d division_of cbox a b\<close> for d
        using integral_eq[OF that] by (intro sum.cong refl) auto
      from bv have bvsv: \<open>has_bounded_setvariation_on
        (\<lambda>k. integral (cbox a (Sup k)) f - integral (cbox a (Inf k)) f) (cbox a b)\<close>
        unfolding has_bounded_variation_on_def .
      obtain B where B: \<open>\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> cbox a b \<Longrightarrow>
        (\<Sum>k\<in>d. norm (integral (cbox a (Sup k)) f - integral (cbox a (Inf k)) f)) \<le> B\<close>
        using bvsv unfolding has_bounded_setvariation_on_def by blast
      show ?thesis
        using bounded_variation_absolutely_integrable_interval[OF fint] sum_eq
        by (metis (lifting) B order.refl)
    qed
  qed
qed

text \<open>If @{term f} is absolutely continuous on $[a,b]$ and has vector derivative $f'(x)$ a.e.,
  then @{term f'} is absolutely integrable on $[a,b]$.\<close>

lemma absolutely_integrable_absolutely_continuous_derivative:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close> and f' :: \<open>real \<Rightarrow> 'a\<close>
  assumes ac: \<open>absolutely_continuous_on {a..b} f\<close>
    and neg: \<open>negligible S\<close>
    and deriv: \<open>\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})\<close>
  shows \<open>f' absolutely_integrable_on {a..b}\<close>
proof (cases \<open>a \<le> b\<close>)
  case ab: True
  show ?thesis
  proof -
    have \<open>f' integrable_on {a..b} \<and>
         has_bounded_variation_on (\<lambda>t. integral {a..t} f') {a..b}\<close>
    proof (intro conjI)
      \<comment> \<open>Part 1: @{term f'} is integrable (via FTC for absolutely continuous functions)\<close>
      show \<open>f' integrable_on {a..b}\<close>
        using fundamental_theorem_of_calculus_absolutely_continuous [OF neg ab ac deriv]
        by (auto simp: integrable_on_def)
    next
      \<comment> \<open>Part 2: the indefinite integral of @{term f'} has bounded variation\<close>
      show \<open>has_bounded_variation_on (\<lambda>t. integral {a..t} f') {a..b}\<close>
      proof -
        \<comment> \<open>On $[a,c]$ for $c \in [a,b]$, FTC gives @{term \<open>integral {a..c} f' = f c - f a\<close>}\<close>
        have eq: \<open>integral {a..c} f' = f c - f a\<close> if \<open>c \<in> {a..b}\<close> for c
        proof -
          from that have ac_le: \<open>a \<le> c\<close> and cb: \<open>c \<le> b\<close> by auto
          have \<open>(f' has_integral (f c - f a)) {a..c}\<close>
          proof (rule fundamental_theorem_of_calculus_absolutely_continuous
                      [OF _ ac_le])
            show \<open>negligible S\<close> by (rule neg)
            show \<open>absolutely_continuous_on {a..c} f\<close>
              by (rule absolutely_continuous_on_subset[OF ac])
                 (use cb in auto)
            fix x assume \<open>x \<in> {a..c} - S\<close>
            then have \<open>x \<in> {a..b} - S\<close>
              using cb by auto
            then have \<open>(f has_vector_derivative f' x) (at x within {a..b})\<close>
              by (rule deriv)
            then show \<open>(f has_vector_derivative f' x) (at x within {a..c})\<close>
              by (rule has_vector_derivative_within_subset) (use cb in auto)
          qed
          then show ?thesis
            by (rule integral_unique)
        qed
        \<comment> \<open>So @{term \<open>\<lambda>t. integral {a..t} f'\<close>} agrees with @{term \<open>\<lambda>t. f t - f a\<close>} on $[a,b]$\<close>
        have \<open>absolutely_continuous_on {a..b} (\<lambda>t. f t - f a)\<close>
          by (intro absolutely_continuous_on_sub ac absolutely_continuous_on_const)
        then show ?thesis
          by (metis (no_types, lifting) absolutely_continuous_on_eq eq
              absolutely_continuous_on_imp_has_bounded_variation_on compact_Icc compact_imp_bounded)
      qed
    qed
    then show ?thesis
      using box_real absolutely_integrable_bounded_variation_eq by auto
  qed
qed auto


lemma absolutely_setcontinuous_indefinite_integral:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>f absolutely_integrable_on S\<close> \<open>S \<in> lmeasurable\<close>
  shows \<open>absolutely_setcontinuous_on (\<lambda>k. integral k f) S\<close>
  unfolding absolutely_setcontinuous_on_alt
proof (intro strip)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain \<delta> where "\<delta>>0" 
    and d: "\<And>T. T \<subseteq> S \<Longrightarrow> T \<in> lmeasurable \<Longrightarrow> measure lebesgue T < \<delta>
                       \<Longrightarrow> norm (integral T f) < \<epsilon>"
    using absolutely_continuous_integral assms(1) by blast
  have "norm (\<Sum>k\<in>d. integral k f) < \<epsilon>"
    if "d division_of T" "T \<subseteq> S" "sum content d < \<delta>" for d T
  proof -
    have f_int: "f integrable_on T"
      using integrable_on_subdivision[OF that(1)] set_lebesgue_integral_eq_integral(1)[OF assms(1)] that(2) by auto
    then have eq: "integral T f = (\<Sum>k\<in>d. integral k f)"
      using integral_combine_division_topdown[OF _ that(1)] by auto
    have meas: "T \<in> lmeasurable"
      using lmeasurable_division that(1) by auto
    then have "measure lebesgue T < \<delta>"
      using that by (metis lebesgue_measure_eq_content)
    then show ?thesis
      using d[OF that(2) meas] eq by auto
  qed
  then show "\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> sum content d < \<delta> \<longrightarrow> norm (\<Sum>k\<in>d. integral k f) < \<epsilon>"
    using \<open>0 < \<delta>\<close> by blast
qed

lemma absolutely_continuous_indefinite_integral_right:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>f absolutely_integrable_on {a..b}\<close>
  shows \<open>absolutely_continuous_on {a..b} (\<lambda>x. integral {a..x} f)\<close>
proof -
  have sc: \<open>absolutely_setcontinuous_on (\<lambda>k. integral k f) {a..b}\<close>
    using absolutely_setcontinuous_indefinite_integral assms by blast
  have key: \<open>integral {a..Sup k} f - integral {a..Inf k} f = integral k f\<close>
    if \<open>k \<in> d\<close> \<open>d division_of T\<close> \<open>T \<subseteq> {a..b}\<close> for k d T
  proof -
    obtain c e where ke: \<open>k = cbox c e\<close> and \<open>k \<subseteq> T\<close>
      using division_ofD(4,2) \<open>k \<in> d\<close> \<open>d division_of T\<close> by meson
    have \<open>k \<noteq> {}\<close> using that(1,2) division_ofD(3) by blast
    then have \<open>c \<le> e\<close> using ke by auto
    have \<open>c \<in> {a..b}\<close> \<open>e \<in> {a..b}\<close>
      using \<open>k \<subseteq> T\<close> that(3) ke \<open>c \<le> e\<close> by (auto simp add: subset_eq)
    then have \<open>a \<le> c\<close> \<open>a \<le> e\<close> \<open>e \<le> b\<close> by auto
    have f_int: \<open>f integrable_on {a..e}\<close>
      using assms absolutely_integrable_on_def integrable_on_subinterval
      by (meson \<open>a \<le> e\<close> \<open>e \<le> b\<close> atLeastatMost_subset_iff order_refl)
    have \<open>integral {a..e} f - integral {a..c} f
        = (if e \<le> c then - integral {e..c} f else integral {c..e} f)\<close>
      by (simp add: \<open>a \<le> c\<close> \<open>a \<le> e\<close> \<open>c \<le> e\<close> f_int integral_minus_sets)
    then show ?thesis using ke \<open>c \<le> e\<close> by auto
  qed
  show ?thesis
    unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  proof (intro strip)
    fix \<epsilon> :: real assume \<open>0 < \<epsilon>\<close>
    then obtain \<delta> where \<open>\<delta> > 0\<close>
      and \<delta>: \<open>\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> {a..b} \<Longrightarrow> sum content d < \<delta>
                    \<Longrightarrow> (\<Sum>k\<in>d. norm (integral k f)) < \<epsilon>\<close>
      using sc unfolding absolutely_setcontinuous_on_def by meson
    show \<open>\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> {a..b} \<and> sum content d < \<delta> \<longrightarrow>
               (\<Sum>k\<in>d. norm (integral {a..Sup k} f - integral {a..Inf k} f)) < \<epsilon>\<close>
      using \<open>0 < \<delta>\<close>  \<delta> key by auto
  qed
qed

lemma absolutely_continuous_indefinite_integral_left:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>f absolutely_integrable_on {a..b}\<close>
  shows \<open>absolutely_continuous_on {a..b} (\<lambda>x. integral {x..b} f)\<close>
proof (rule absolutely_continuous_on_eq)
  show \<open>x \<in> {a..b} \<Longrightarrow> integral {a..b} f - integral {a..x} f = integral {x..b} f\<close> for x
    using integral_minus_sets[of a b x f] absolutely_integrable_on_def assms
    by (fastforce simp: algebra_simps max_def)
  show \<open>absolutely_continuous_on {a..b} (\<lambda>x. integral {a..b} f - integral {a..x} f)\<close>
    by (intro absolutely_continuous_on_sub absolutely_continuous_on_const
              absolutely_continuous_indefinite_integral_right assms)
qed

theorem has_vector_derivative_indefinite_integral:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>f integrable_on {a..b}\<close>
  obtains k where \<open>negligible k\<close>
    \<open>\<And>x. x \<in> {a..b} - k \<Longrightarrow>
      ((\<lambda>u. integral {a..u} f) has_vector_derivative f x) (at x within {a..b})\<close>
proof -
  have onesided: \<open>\<exists>k. negligible k \<and>
        (\<forall>x\<in>{u..v} - k. \<forall>e>0.
          \<exists>d>0. \<forall>x'\<in>{u..v}.
            x < x' \<and> x' < x + d \<longrightarrow> norm (integral {x..x'} f - (x' - x) *\<^sub>R f x) / norm (x' - x) < e)\<close>
    if \<open>f integrable_on {u..v}\<close> for f::"real \<Rightarrow> 'a" and u v::real
  proof -
    define g where \<open>g \<equiv> \<lambda>x. if x \<in> {u..v} then f x else 0\<close>
    have gint: \<open>g integrable_on cbox a b\<close> for a b
      unfolding g_def using integrable_altD(1) that by blast
    show ?thesis
    proof (rule integrable_ccontinuous_explicit[OF gint])
      fix N :: \<open>real set\<close>
      assume negN: \<open>negligible N\<close>
      assume Nprop: \<open>\<And>x e. x \<notin> N \<Longrightarrow> 0 < e \<Longrightarrow>
        \<exists>d>0. \<forall>h. 0 < h \<and> h < d \<longrightarrow> norm (integral (cbox x (x + h *\<^sub>R One)) g /\<^sub>R h ^ DIM(real) - g x) < e\<close>
      show \<open>\<exists>k. negligible k \<and>
        (\<forall>x\<in>{u..v} - k. \<forall>e>0.
          \<exists>d>0. \<forall>y\<in>{u..v}.
            x < y \<and> y < x + d \<longrightarrow> norm (integral {x..y} f - (y - x) *\<^sub>R f x) / norm (y - x) < e)\<close>
      proof (intro exI[of _ N] conjI strip)
        show \<open>negligible N\<close>
          by (rule negN)
      next
        fix x e
        assume xmem: \<open>x \<in> {u..v} - N\<close> and epos: \<open>(0::real) < e\<close>
        then have xN: \<open>x \<notin> N\<close> and xu: \<open>u \<le> x\<close> and xv: \<open>x \<le> v\<close> by auto
        obtain d where dpos: \<open>0 < d\<close> 
          and dprop: \<open>\<And>h. 0 < h \<and> h < d \<Longrightarrow>
            norm (integral (cbox x (x + h *\<^sub>R One)) g /\<^sub>R h ^ DIM(real) - g x) < e\<close>
          using Nprop[OF xN epos] by auto
        show \<open>\<exists>d>0. \<forall>x'\<in>{u..v}. x < x' \<and> x' < x + d \<longrightarrow>
            norm (integral {x..x'} f - (x' - x) *\<^sub>R f x) / norm (x' - x) < e\<close>
        proof (intro exI[of _ d] conjI ballI impI)
          show \<open>0 < d\<close> by (rule dpos)
        next
          fix x'
          assume x'mem: \<open>x' \<in> {u..v}\<close> and x'bd: \<open>x < x' \<and> x' < x + d\<close>
          define h where \<open>h \<equiv> x' - x\<close>
          have hpos: \<open>0 < h\<close> and hd: \<open>h < d\<close>
            using x'bd unfolding h_def by auto
          have x'eq: \<open>x' = x + h\<close> unfolding h_def by simp
          have sub: \<open>{x..x'} \<subseteq> {u..v}\<close>
            using xu xv x'mem by auto
          have cbox_eq: \<open>cbox x (x + h *\<^sub>R One) = {x..x'}\<close>
            by (simp add: x'eq cbox_interval)
          have int_if_eq: \<open>integral {x..x'} (\<lambda>t. if t \<in> {u..v} then f t else 0) = integral {x..x'} f\<close>
            by (metis (mono_tags) Henstock_Kurzweil_Integration.integral_restrict_Int Int_absorb1 sub)
          have int_eq: \<open>integral {x..x + h} g = integral {x..x + h} f\<close>
            unfolding g_def
            using int_if_eq x'eq by simp
          have gx_eq: \<open>g x = f x\<close>
            unfolding g_def using xu xv by simp
          have \<open>norm (integral (cbox x (x + h *\<^sub>R One)) g /\<^sub>R h ^ DIM(real) - g x) < e\<close>
            by (rule dprop) (use hpos hd in auto)
          then have \<open>norm (integral {x..x'} f /\<^sub>R h - f x) < e\<close>
            by (simp add: cbox_eq int_eq gx_eq x'eq)
          moreover have \<open>norm (integral {x..x'} f - (x' - x) *\<^sub>R f x) / norm (x' - x) =
                norm (integral {x..x'} f /\<^sub>R h - f x)\<close>
            by (smt (verit, best) mult.commute scale_right_diff_distrib divideR_right divide_inverse h_def
                hpos norm_inverse norm_scaleR real_norm_def)
          ultimately show \<open>norm (integral {x..x'} f - (x' - x) *\<^sub>R f x) / norm (x' - x) < e\<close>
            by simp
        qed
      qed
    qed
  qed

  obtain K1 where \<open>negligible K1\<close> and K1:
    \<open>\<And>x e. \<lbrakk>x \<in> {a..b} - K1; 0 < e\<rbrakk> \<Longrightarrow>
      \<exists>d>0. \<forall>x'\<in>{a..b}. x < x' \<and> x' < x + d \<longrightarrow>
        norm (integral {x..x'} f - (x' - x) *\<^sub>R f x) / norm (x' - x) < e\<close>
    using onesided [OF assms] by auto
  have \<open>((\<lambda>x. f (- x)) integrable_on {- b..- a})\<close>
    by (simp add: assms)
  then obtain K2 where \<open>negligible K2\<close> and K2:
    \<open>\<And>x e. \<lbrakk>x \<in> {-b..-a} - K2; 0 < e\<rbrakk> \<Longrightarrow>
      \<exists>d>0. \<forall>x'\<in>{-b..-a}. x < x' \<and> x' < x + d \<longrightarrow>
        norm (integral {x..x'} (\<lambda>x. f (-x)) - (x' - x) *\<^sub>R f (-x)) / norm (x' - x) < e\<close>
    using onesided by metis 
  define K where "K \<equiv> K1 \<union> uminus ` K2"
  show ?thesis
  proof
    show "negligible K"
      by (simp add: K_def \<open>negligible K1\<close> \<open>negligible K2\<close> module_hom_uminus negligible_linear_image)
  next
    fix x :: real
    assume x: "x \<in> {a..b} - K"
    have "bounded_linear (\<lambda>u. u *\<^sub>R f x)"
      by (simp add: bounded_linear_scaleR_left)
    moreover have "\<exists>d>0. \<forall>y\<in>{a..b}. \<bar>y - x\<bar> < d \<longrightarrow> norm (integral {a..y} f - integral {a..x} f - (y - x) *\<^sub>R f x) \<le> e * \<bar>y - x\<bar>"
      if "0 < e"
      for e :: real
    proof -
      have xK1: \<open>x \<in> {a..b} - K1\<close> and xK2: \<open>-x \<in> {-b..-a} - K2\<close>
        using x by (auto simp: K_def image_iff)
      obtain d1 where \<open>d1 > 0\<close> and d1:
        \<open>\<And>x'. \<lbrakk>x' \<in> {a..b}; x < x'; x' < x + d1\<rbrakk>
          \<Longrightarrow> norm (integral {x..x'} f - (x' - x) *\<^sub>R f x) / norm (x' - x) < e\<close>
        using K1 [OF xK1 \<open>0 < e\<close>] x by metis
      obtain d2 where \<open>d2 > 0\<close> and d2:
        \<open>\<And>x'. \<lbrakk>x' \<in> {-b..-a}; -x < x'; x' < -x + d2\<rbrakk>
          \<Longrightarrow> norm (integral {-x..x'} (\<lambda>x. f (-x)) - (x'+x) *\<^sub>R f x) / norm (x' + x) < e\<close>
        using K2[OF xK2 \<open>0 < e\<close>] xK2 by force
      have d2': \<open>norm (integral {y'..x} f - (x - y') *\<^sub>R f x) / \<bar>x - y'\<bar> < e\<close>
        if \<open>y' \<in> {a..b}\<close> \<open>y' < x\<close> \<open>x - y' < d2\<close> for y'
        using d2[of \<open>-y'\<close>] that by (simp add: integral_reflect_real real_norm_def)
      show ?thesis
      proof (intro exI conjI strip)
        show "0 < min d1 d2"
          by (simp add: \<open>0 < d1\<close> \<open>0 < d2\<close>)
      next
        fix y :: real
        assume "y \<in> {a..b}" and y: "\<bar>y - x\<bar> < min d1 d2"

        have step: \<open>norm (integral {a..y} f - integral {a..x} f - (y - x) *\<^sub>R f x) \<le> e * \<bar>y - x\<bar>\<close>
          if local_bound: \<open>norm (integral {p..q} f - (q - p) *\<^sub>R f x) / (q - p) < e\<close>
             and ord: \<open>a \<le> p\<close> \<open>p < q\<close> \<open>q \<le> b\<close>
             and pq_eq: \<open>{p..q} = {min x y..max x y}\<close>
          for p q
        proof -
          have fint: \<open>f integrable_on {a..q}\<close>
            using integrable_on_subinterval[OF assms] ord by auto
          have \<open>integral {a..p} f + integral {p..q} f = integral {a..q} f\<close>
            by (rule Henstock_Kurzweil_Integration.integral_combine) (use ord fint in linarith)+
          then have \<open>norm (integral {a..y} f - integral {a..x} f - (y - x) *\<^sub>R f x)
                 = norm (integral {p..q} f - (q - p) *\<^sub>R f x)\<close>
            by (smt (verit, best) add_diff_cancel_left' add_uminus_conv_diff interval_bounds_real minus_diff_eq
                norm_uminus_minus ord(2) pq_eq scale_minus_left)
          also have \<open>\<dots> < e * (q - p)\<close>
            using local_bound ord by (simp add: divide_simps)
          also have \<open>\<dots> = e * \<bar>y - x\<bar>\<close>
            using pq_eq ord by (auto simp: min_def max_def split: if_splits)
          finally show ?thesis by simp
        qed
        show "norm (integral {a..y} f - integral {a..x} f - (y - x) *\<^sub>R f x) \<le> e * \<bar>y - x\<bar>"
        proof (cases \<open>x = y\<close>)
          case True then show ?thesis by simp
        next
          case False
          define p q where \<open>p \<equiv> min x y\<close> and \<open>q \<equiv> max x y\<close>
          have pq: \<open>p < q\<close> \<open>{p..q} = {min x y..max x y}\<close>
            using False by (auto simp: p_def q_def)
          have ord: \<open>a \<le> p\<close> \<open>q \<le> b\<close>
            using x \<open>y \<in> {a..b}\<close> by (auto simp: p_def q_def K_def)
          have bd: \<open>norm (integral {p..q} f - (q - p) *\<^sub>R f x) / (q - p) < e\<close>
          proof (cases \<open>x < y\<close>)
            case True
            then show ?thesis
              using d1[of y] \<open>y \<in> {a..b}\<close> y by (auto simp: p_def q_def real_norm_def)
          next
            case False
            then show ?thesis
              using \<open>x \<noteq> y\<close> d2'[of y] \<open>y \<in> {a..b}\<close> y by (auto simp: p_def q_def real_norm_def)
          qed
          then show ?thesis
            using step[of p q] pq ord by auto
        qed
      qed
    qed
    ultimately show "((\<lambda>u. integral {a..u} f) has_vector_derivative f x) (at x within {a..b})"
      unfolding has_vector_derivative_def has_derivative_within_alt2
      unfolding eventually_at_filter eventually_nhds_metric
      by (force simp: dist_real_def)
  qed
qed


lemma absolute_integral_absolutely_continuous_derivative_eq:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close> and f' :: \<open>real \<Rightarrow> 'a\<close>
  shows \<open>(f' absolutely_integrable_on {a..b} \<and>
          (\<forall>x \<in> {a..b}. (f' has_integral (f x - f a)) {a..x}))
     \<longleftrightarrow> (absolutely_continuous_on {a..b} f \<and>
          (\<exists>S. negligible S \<and>
               (\<forall>x \<in> {a..b} - S. (f has_vector_derivative f' x) (at x within {a..b}))))\<close>
    (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof
  assume L: ?L
  have f'abs: \<open>f' absolutely_integrable_on {a..b}\<close> and
    f'int: \<open>\<And>c. c \<in> {a..b} \<Longrightarrow> (f' has_integral (f c - f a)) {a..c}\<close>
    using L by auto
  have feq: \<open>f a + integral {a..c} f' = f c\<close> if \<open>c \<in> {a..b}\<close> for c
    using integral_unique[OF f'int[OF that]] by simp
  obtain S where negs: \<open>negligible S\<close> and
    ideriv: \<open>\<And>x. x \<in> {a..b} - S \<Longrightarrow> ((\<lambda>u. integral {a..u} f') has_vector_derivative f' x) (at x within {a..b})\<close>
    using has_vector_derivative_indefinite_integral[of f' a b] f'abs
    by (auto simp: absolutely_integrable_on_def)
  show ?R
  proof (intro conjI)
    show \<open>absolutely_continuous_on {a..b} f\<close>
    proof (rule absolutely_continuous_on_eq)
      show \<open>absolutely_continuous_on {a..b} (\<lambda>x. f a + integral {a..x} f')\<close>
        using absolutely_continuous_indefinite_integral_right
        using absolutely_continuous_on_add absolutely_continuous_on_const f'abs by blast
      show \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> f a + integral {a..x} f' = f x\<close>
        using feq by blast
    qed
  next
    show \<open>\<exists>S. negligible S \<and>
              (\<forall>x \<in> {a..b} - S. (f has_vector_derivative f' x) (at x within {a..b}))\<close>
    proof (intro exI conjI ballI)
      show \<open>negligible S\<close> by (rule negs)
    next
      fix x assume xmem: \<open>x \<in> {a..b} - S\<close>
      have \<open>((\<lambda>u. integral {a..u} f') has_vector_derivative f' x) (at x within {a..b})\<close>
        using ideriv[OF xmem] .
      then have \<open>((\<lambda>u. f a + integral {a..u} f') has_vector_derivative 0 + f' x) (at x within {a..b})\<close>
        by (intro has_vector_derivative_add has_vector_derivative_const)
      then have \<open>((\<lambda>u. f a + integral {a..u} f') has_vector_derivative f' x) (at x within {a..b})\<close>
        by simp
      then show \<open>(f has_vector_derivative f' x) (at x within {a..b})\<close>
        by (metis (no_types, lifting) Diff_iff feq has_vector_derivative_transform xmem)
    qed
  qed
next
  assume R: ?R
  then obtain S where ac: \<open>absolutely_continuous_on {a..b} f\<close> and negs: \<open>negligible S\<close> and
    deriv: \<open>\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})\<close>
    by auto
  show ?L
  proof (intro conjI ballI)
    show \<open>f' absolutely_integrable_on {a..b}\<close>
      by (rule absolutely_integrable_absolutely_continuous_derivative[OF ac negs deriv])
  next
    fix c assume cmem: \<open>c \<in> {a..b}\<close>
    then have ac_le: \<open>a \<le> c\<close> and cb: \<open>c \<le> b\<close> by auto
    show \<open>(f' has_integral (f c - f a)) {a..c}\<close>
    proof (rule fundamental_theorem_of_calculus_absolutely_continuous[OF negs ac_le])
      show \<open>absolutely_continuous_on {a..c} f\<close>
        by (rule absolutely_continuous_on_subset[OF ac]) (use cb in auto)
    next
      fix x assume \<open>x \<in> {a..c} - S\<close>
      then have \<open>x \<in> {a..b} - S\<close>
        using cb by auto
      then have \<open>(f has_vector_derivative f' x) (at x within {a..b})\<close>
        by (rule deriv)
      then show \<open>(f has_vector_derivative f' x) (at x within {a..c})\<close>
        by (rule has_vector_derivative_within_subset) (use cb in auto)
    qed
  qed
qed


text \<open>Existential version: @{term f'} is absolutely integrable iff there exists an
  absolutely continuous antiderivative.\<close>

lemma absolutely_integrable_absolutely_continuous_derivative_eq:
  fixes f' :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  shows \<open>f' absolutely_integrable_on {a..b} \<longleftrightarrow>
    (\<exists>f S. absolutely_continuous_on {a..b} f \<and>
           negligible S \<and> (\<forall>x \<in> {a..b} - S. (f has_vector_derivative f' x) (at x within {a..b})))\<close>
    (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof
  assume L: ?L
  define f where \<open>f \<equiv> \<lambda>t. integral {a..t} f'\<close>
  have f'int: \<open>f' integrable_on {a..b}\<close>
    using L set_lebesgue_integral_eq_integral by blast
  have f_a: \<open>f a = 0\<close>
    unfolding f_def by (simp add: integral_singleton)
  have hi: \<open>(f' has_integral (f x - f a)) {a..x}\<close> if \<open>x \<in> {a..b}\<close> for x
    using f'int f_def integrable_on_subinterval that by fastforce
  have \<open>f' absolutely_integrable_on {a..b} \<and>
        (\<forall>x \<in> {a..b}. (f' has_integral (f x - f a)) {a..x})\<close>
    using L hi by auto
  then show ?R
    by (metis absolute_integral_absolutely_continuous_derivative_eq)
next
  assume ?R then show ?L
    using absolutely_integrable_absolutely_continuous_derivative by blast
qed


lemma absolute_integral_absolutely_continuous_derivative_eq_alt:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close> and f' :: \<open>real \<Rightarrow> 'a\<close>
  shows \<open>(f' absolutely_integrable_on {a..b} \<and>
          (\<forall>x \<in> {a..b}. (f' has_integral (f x - f a)) {a..x}))
     \<longleftrightarrow> (absolutely_continuous_on {a..b} f \<and>
          (\<exists>S. negligible S \<and> (\<forall>x \<in> {a..b} - S. (f has_vector_derivative f' x) (at x))))\<close>
    (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof -
  have base: \<open>?L \<longleftrightarrow> (absolutely_continuous_on {a..b} f \<and>
          (\<exists>S. negligible S \<and> (\<forall>x \<in> {a..b} - S. (f has_vector_derivative f' x) (at x within {a..b}))))\<close>
    (is \<open>_ \<longleftrightarrow> ?M\<close>)
    by (rule absolute_integral_absolutely_continuous_derivative_eq)
  also have \<open>?M \<longleftrightarrow> ?R\<close>
  proof (intro conj_cong refl iffI)
    assume \<open>\<exists>S. negligible S \<and> (\<forall>x \<in> {a..b} - S. (f has_vector_derivative f' x) (at x within {a..b}))\<close>
    then obtain S where negs: \<open>negligible S\<close> and
      deriv: \<open>\<And>x. x \<in> {a..b} - S \<Longrightarrow>
                  (f has_vector_derivative f' x) (at x within {a..b})\<close>
      by auto
    show \<open>\<exists>S. negligible S \<and> (\<forall>x \<in> {a..b} - S. (f has_vector_derivative f' x) (at x))\<close>
    proof (intro exI conjI ballI)
      show \<open>negligible ({a, b} \<union> S)\<close>
        using negs by (simp add: negligible_insert)
    next
      fix x assume xmem: \<open>x \<in> {a..b} - ({a, b} \<union> S)\<close>
      then show \<open>(f has_vector_derivative f' x) (at x)\<close>
        by (metis Diff_iff Diff_insert UnCI atLeastAtMost_iff atLeastAtMost_singleton at_within_Icc_at deriv leI)
    qed
  next
    assume \<open>\<exists>S. negligible S \<and> (\<forall>x \<in> {a..b} - S. (f has_vector_derivative f' x) (at x))\<close>
    then show \<open>\<exists>S. negligible S \<and> (\<forall>x \<in> {a..b} - S. (f has_vector_derivative f' x) (at x within {a..b}))\<close>
      by (meson has_vector_derivative_at_within)
  qed
  finally show ?thesis .
qed


text \<open>Integration by parts for absolutely integrable functions (shifted / sum version).
  Bilinear generalisation: HOL Light's @{text ABSOLUTE_INTEGRATION_BY_PARTS_SUM}.\<close>

theorem absolute_integration_by_parts_sum:
  fixes bop :: \<open>'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::euclidean_space\<close>
    and f :: \<open>real \<Rightarrow> 'a\<close> and g :: \<open>real \<Rightarrow> 'b\<close>
    and f' :: \<open>real \<Rightarrow> 'a\<close> and g' :: \<open>real \<Rightarrow> 'b\<close>
    and a b :: real
  assumes bop: \<open>bilinear bop\<close>
    and ab: \<open>a \<le> b\<close>
    and f'abs: \<open>f' absolutely_integrable_on {a..b}\<close>
    and g'abs: \<open>g' absolutely_integrable_on {a..b}\<close>
    and f'int: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (f' has_integral (f x - f a)) {a..x}\<close>
    and g'int: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (g' has_integral (g x - g a)) {a..x}\<close>
  shows \<open>(\<lambda>x. bop (f x) (g' x) + bop (f' x) (g x)) absolutely_integrable_on {a..b}\<close>
    and \<open>\<And>x. x \<in> {a..b} \<Longrightarrow>
      ((\<lambda>x. bop (f x) (g' x) + bop (f' x) (g x))
        has_integral (bop (f x) (g x) - bop (f a) (g a))) {a..x}\<close>
proof -
  have bb: \<open>bounded_bilinear bop\<close>
    using bop bilinear_conv_bounded_bilinear by blast
  \<comment> \<open>Rewrite both pairs of conditions using the characterisation.\<close>
  have fL: \<open>absolutely_continuous_on {a..b} f \<and>
    (\<exists>S. negligible S \<and> (\<forall>x \<in> {a..b} - S. (f has_vector_derivative f' x) (at x within {a..b})))\<close>
    by (subst absolute_integral_absolutely_continuous_derivative_eq[symmetric])
       (use f'abs f'int in auto)
  have gL: \<open>absolutely_continuous_on {a..b} g \<and>
    (\<exists>S. negligible S \<and> (\<forall>x \<in> {a..b} - S. (g has_vector_derivative g' x) (at x within {a..b})))\<close>
    by (subst absolute_integral_absolutely_continuous_derivative_eq[symmetric])
       (use g'abs g'int in auto)
  obtain S where f_ac: \<open>absolutely_continuous_on {a..b} f\<close> and negs: \<open>negligible S\<close>
    and f_deriv: \<open>\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})\<close>
    using fL by auto
  obtain T where g_ac: \<open>absolutely_continuous_on {a..b} g\<close> and negt: \<open>negligible T\<close>
    and g_deriv: \<open>\<And>x. x \<in> {a..b} - T \<Longrightarrow> (g has_vector_derivative g' x) (at x within {a..b})\<close>
    using gL by auto
  \<comment> \<open>The composed function is absolutely continuous.\<close>
  have fg_ac: \<open>absolutely_continuous_on {a..b} (\<lambda>x. bop (f x) (g x))\<close>
    by (rule absolutely_continuous_on_bilinear[OF bop f_ac g_ac is_interval_cc
            compact_imp_bounded[OF compact_Icc]])
  \<comment> \<open>The negligible set for the derivative.\<close>
  have neg_st: \<open>negligible (S \<union> T)\<close>
    using negs negt negligible_Un by blast
  \<comment> \<open>The derivative of @{term \<open>bop (f x) (g x)\<close>} at each point outside @{term \<open>S \<union> T\<close>}.\<close>
  have fg_deriv: \<open>((\<lambda>x. bop (f x) (g x)) has_vector_derivative bop (f x) (g' x) + bop (f' x) (g x)) (at x within {a..b})\<close>
    if \<open>x \<in> {a..b} - (S \<union> T)\<close> for x
  proof -
    have \<open>x \<in> {a..b} - S\<close> \<open>x \<in> {a..b} - T\<close> using that by auto
    then show ?thesis
      using bounded_bilinear.has_vector_derivative[OF bb f_deriv g_deriv] by blast
  qed
  \<comment> \<open>Now apply the characterisation in the reverse direction.\<close>
  have main: \<open>(\<lambda>x. bop (f x) (g' x) + bop (f' x) (g x)) absolutely_integrable_on {a..b} \<and>
    (\<forall>x \<in> {a..b}. ((\<lambda>x. bop (f x) (g' x) + bop (f' x) (g x))
      has_integral ((\<lambda>x. bop (f x) (g x)) x - (\<lambda>x. bop (f x) (g x)) a)) {a..x})\<close>
    by (subst absolute_integral_absolutely_continuous_derivative_eq)
       (use fg_ac neg_st fg_deriv in \<open>blast+\<close>)
  show \<open>(\<lambda>x. bop (f x) (g' x) + bop (f' x) (g x)) absolutely_integrable_on {a..b}\<close>
    using main by blast
  show \<open>((\<lambda>x. bop (f x) (g' x) + bop (f' x) (g x))
        has_integral (bop (f x) (g x) - bop (f a) (g a))) {a..x}\<close>
    if \<open>x \<in> {a..b}\<close> for x
    using main that by auto
qed


text \<open>Helper: the indefinite integral of an absolutely integrable function
  is absolutely continuous.\<close>

lemmas indefinite_integral_absolutely_continuous = absolutely_continuous_indefinite_integral_right


text \<open>The real-valued shifted version\<close>

lemma absolute_real_integration_by_parts_sum:
  fixes f g f' g' :: "real \<Rightarrow> real"
  assumes ab: "a \<le> b"
    and f'abs: "f' absolutely_integrable_on {a..b}"
    and g'abs: "g' absolutely_integrable_on {a..b}"
    and f'int: "\<And>x. x \<in> {a..b} \<Longrightarrow> (f' has_integral (f x - f a)) {a..x}"
    and g'int: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g' has_integral (g x - g a)) {a..x}"
  shows fgsum_abs: "(\<lambda>x. f x * g' x + f' x * g x) absolutely_integrable_on {a..b}"
    and fgsum_int: "\<And>x. x \<in> {a..b} \<Longrightarrow>
      ((\<lambda>x. f x * g' x + f' x * g x) has_integral (f x * g x - f a * g a)) {a..x}"
proof -
  \<comment> \<open>Apply IBP with shifted antiderivatives @{term \<open>F x = f x - f a\<close>}, @{term \<open>G x = g x - g a\<close>}.\<close>
  define F where "F \<equiv> \<lambda>x. f x - f a"
  define G where "G \<equiv> \<lambda>x. g x - g a"
  have F_int: "\<And>x. x \<in> {a..b} \<Longrightarrow> (f' has_integral F x) {a..x}"
    unfolding F_def using f'int by simp
  have G_int: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g' has_integral G x) {a..x}"
    unfolding G_def using g'int by simp
  note ibp = absolute_real_integration_by_parts[OF ab f'abs g'abs F_int G_int]
  \<comment> \<open>IBP gives us three facts about @{term F} and @{term G}.\<close>
  have Fg'_abs: "(\<lambda>x. F x * g' x) absolutely_integrable_on {a..b}" using ibp(1) .
  have f'G_abs: "(\<lambda>x. f' x * G x) absolutely_integrable_on {a..b}" using ibp(2) .
  have ibp_eq: "integral {a..b} (\<lambda>x. F x * g' x) + integral {a..b} (\<lambda>x. f' x * G x) = F b * G b - F a * G a"
    using ibp(3) .
  \<comment> \<open>Constant-multiple terms are absolutely integrable.\<close>
  have cg'_abs: "(\<lambda>x. f a * g' x) absolutely_integrable_on {a..b}"
    using absolutely_integrable_scaleR_left[OF g'abs, of "f a"]
    by (simp add: scaleR_conv_of_real)
  have f'c_abs: "(\<lambda>x. f' x * g a) absolutely_integrable_on {a..b}"
    using absolutely_integrable_scaleR_right[OF f'abs, of "g a"]
    by (simp add: scaleR_conv_of_real)
  \<comment> \<open>Each component is integrable.\<close>
  have Fg'_int: "(\<lambda>x. F x * g' x) integrable_on {a..b}"
    using Fg'_abs set_lebesgue_integral_eq_integral by blast
  have f'G_int: "(\<lambda>x. f' x * G x) integrable_on {a..b}"
    using f'G_abs set_lebesgue_integral_eq_integral by blast
  have cg'_int: "(\<lambda>x. f a * g' x) integrable_on {a..b}"
    using cg'_abs set_lebesgue_integral_eq_integral by blast
  have f'c_int: "(\<lambda>x. f' x * g a) integrable_on {a..b}"
    using f'c_abs set_lebesgue_integral_eq_integral by blast
  \<comment> \<open>The norm of each component is integrable.\<close>
  have Fg'_norm: "(\<lambda>x. norm (F x * g' x)) integrable_on {a..b}"
    using Fg'_abs absolutely_integrable_on_def by metis
  have f'G_norm: "(\<lambda>x. norm (f' x * G x)) integrable_on {a..b}"
    using f'G_abs absolutely_integrable_on_def by metis
  have cg'_norm: "(\<lambda>x. norm (f a * g' x)) integrable_on {a..b}"
    using cg'_abs absolutely_integrable_on_def by metis
  have f'c_norm: "(\<lambda>x. norm (f' x * g a)) integrable_on {a..b}"
    using f'c_abs absolutely_integrable_on_def by metis
  \<comment> \<open>The decomposition: $f\,x \cdot g'\,x + f'\,x \cdot g\,x = F\,x \cdot g'\,x + f\,a \cdot g'\,x + f'\,x \cdot G\,x + f'\,x \cdot g\,a$.\<close>
  have decomp: "\<And>x. f x * g' x + f' x * g x = F x * g' x + f a * g' x + (f' x * G x + f' x * g a)"
    unfolding F_def G_def by (simp add: algebra_simps)
  \<comment> \<open>Sum is integrable.\<close>
  have sum_int: "(\<lambda>x. f x * g' x + f' x * g x) integrable_on {a..b}"
    unfolding decomp using integrable_add[OF integrable_add[OF Fg'_int cg'_int] integrable_add[OF f'G_int f'c_int]] .
  \<comment> \<open>Norm bound: $|f\,x \cdot g'\,x + f'\,x \cdot g\,x| \le |F\,x \cdot g'\,x| + |f\,a \cdot g'\,x| + |f'\,x \cdot G\,x| + |f'\,x \cdot g\,a|$.\<close>
  have bound_int: "(\<lambda>x. norm (F x * g' x) + norm (f a * g' x) + (norm (f' x * G x) + norm (f' x * g a))) integrable_on {a..b}"
    using integrable_add[OF integrable_add[OF Fg'_norm cg'_norm] integrable_add[OF f'G_norm f'c_norm]] .
  have norm_bound: "\<And>x. x \<in> {a..b} \<Longrightarrow> norm (f x * g' x + f' x * g x) \<le>
    norm (F x * g' x) + norm (f a * g' x) + (norm (f' x * G x) + norm (f' x * g a))"
    unfolding decomp by (intro order_trans[OF norm_triangle_ineq] add_mono order_trans[OF norm_triangle_ineq] order_refl)+
  show fgsum_abs: "(\<lambda>x. f x * g' x + f' x * g x) absolutely_integrable_on {a..b}"
    by (rule absolutely_integrable_integrable_bound[OF norm_bound sum_int bound_int])
  \<comment> \<open>Goal 2: @{text has_integral} on @{term \<open>{a..x}\<close>} for each @{term \<open>x \<in> {a..b}\<close>}.\<close>
  show "\<And>x. x \<in> {a..b} \<Longrightarrow>
    ((\<lambda>x. f x * g' x + f' x * g x) has_integral (f x * g x - f a * g a)) {a..x}"
  proof -
    fix x assume xab: "x \<in> {a..b}"
    hence ax: "a \<le> x" and xb: "x \<le> b" by auto
    have sub: "{a..x} \<subseteq> {a..b}" using xb by auto
    \<comment> \<open>Absolute integrability on the subinterval.\<close>
    have f'abs_sub: "f' absolutely_integrable_on {a..x}"
      using absolutely_integrable_on_subinterval[OF f'abs sub] .
    have g'abs_sub: "g' absolutely_integrable_on {a..x}"
      using absolutely_integrable_on_subinterval[OF g'abs sub] .
    \<comment> \<open>@{text has_integral} results on @{term \<open>{a..x}\<close>}.\<close>
    have F_int_sub: "\<And>y. y \<in> {a..x} \<Longrightarrow> (f' has_integral F y) {a..y}"
      using F_int sub by auto
    have G_int_sub: "\<And>y. y \<in> {a..x} \<Longrightarrow> (g' has_integral G y) {a..y}"
      using G_int sub by auto
    \<comment> \<open>Apply IBP on @{term \<open>{a..x}\<close>}.\<close>
    note ibp_sub = absolute_real_integration_by_parts[OF ax f'abs_sub g'abs_sub F_int_sub G_int_sub]
    \<comment> \<open>From IBP: integral of $F \cdot g' + f' \cdot G$ on @{term \<open>{a..x}\<close>} equals @{term \<open>F x * G x - F a * G a\<close>} $=$ @{term \<open>F x * G x\<close>}.\<close>
    have Fg'_int_sub: "(\<lambda>t. F t * g' t) integrable_on {a..x}"
      using ibp_sub(1) set_lebesgue_integral_eq_integral by blast
    have f'G_int_sub: "(\<lambda>t. f' t * G t) integrable_on {a..x}"
      using ibp_sub(2) set_lebesgue_integral_eq_integral by blast
    have ibp_eq_sub: "integral {a..x} (\<lambda>t. F t * g' t) + integral {a..x} (\<lambda>t. f' t * G t) = F x * G x - F a * G a"
      using ibp_sub(3) .
    \<comment> \<open>@{term \<open>F a = 0\<close>} and @{term \<open>G a = 0\<close>}.\<close>
    have Fa: "F a = 0" unfolding F_def by simp
    have Ga: "G a = 0" unfolding G_def by simp
    \<comment> \<open>Combine: @{text has_integral} of $F \cdot g' + f' \cdot G$ on @{term \<open>{a..x}\<close>} gives @{term \<open>F x * G x\<close>}.\<close>
    have hi_FG: "((\<lambda>t. F t * g' t + f' t * G t) has_integral (F x * G x)) {a..x}"
      using has_integral_add[OF integrable_integral[OF Fg'_int_sub] integrable_integral[OF f'G_int_sub]]
        ibp_eq_sub Fa Ga by simp
    \<comment> \<open>@{text has_integral} for constant-multiple terms.\<close>
    have hi_cg: "((\<lambda>t. f a * g' t) has_integral (f a * (g x - g a))) {a..x}"
      using has_integral_mult_right[OF g'int[OF xab]] unfolding G_def by simp
    have hi_fc: "((\<lambda>t. f' t * g a) has_integral ((f x - f a) * g a)) {a..x}"
      using has_integral_mult_left[OF f'int[OF xab]] unfolding F_def by simp
    \<comment> \<open>Combine all four terms.\<close>
    have hi_const: "((\<lambda>t. f a * g' t + f' t * g a) has_integral (f a * (g x - g a) + (f x - f a) * g a)) {a..x}"
      using has_integral_add[OF hi_cg hi_fc] .
    have hi_sum: "((\<lambda>t. (F t * g' t + f' t * G t) + (f a * g' t + f' t * g a))
      has_integral (F x * G x + (f a * (g x - g a) + (f x - f a) * g a))) {a..x}"
      using has_integral_add[OF hi_FG hi_const] .
    \<comment> \<open>Rewrite to match the goal.\<close>
    have eq_fn: "\<And>T. (F T * g' T + f' T * G T) + (f a * g' T + f' T * g a) = f T * g' T + f' T * g T"
      unfolding F_def G_def by (simp add: algebra_simps)
    have eq_val: "F x * G x + (f a * (g x - g a) + (f x - f a) * g a) = f x * g x - f a * g a"
      unfolding F_def G_def by (simp add: algebra_simps)
    show "((\<lambda>x. f x * g' x + f' x * g x) has_integral (f x * g x - f a * g a)) {a..x}"
      using hi_sum unfolding eq_fn eq_val .
  qed
qed

end

