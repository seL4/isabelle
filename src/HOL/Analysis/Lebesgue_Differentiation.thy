theory Lebesgue_Differentiation
  imports Equivalence_Measurable_On_Borel Bounded_Variation Weierstrass_Theorems
begin

lemma Lebesgue_diff_aux1:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and a b :: real
  assumes "has_bounded_variation_on f {a..b}"
  shows "\<exists>t. negligible t \<and>
             (\<forall>x \<in> {a..b} - t.
                \<exists>B>0. eventually (\<lambda>y. norm (f y - f x) \<le> B * norm (y-x)) (at x))"
proof -
  define t where "t = {x \<in> {a<..<b}. isCont f x \<and>
    \<not> (\<exists>B>0. eventually (\<lambda>y. norm (f y - f x) \<le> B * norm (y-x)) (at x))}"
    \<comment> \<open>the "bad set": points in the open interval where f is continuous 
        but fails to have a local Lipschitz bound.\<close>
  obtain B where B: "\<And>d T. \<lbrakk>d division_of T; T \<subseteq> {a..b}\<rbrakk> \<Longrightarrow>
      (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B"
    using assms unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
    by blast
  obtain T where tn: "negligible T" and
    tc: "\<And>x. x \<in> {a..b} - T \<Longrightarrow> isCont f x \<Longrightarrow>
       \<exists>B>0. eventually (\<lambda>y. norm (f y - f x) \<le> B * norm (y-x)) (at x)"
  proof 
    show "negligible ({a, b} \<union> t)"
    proof (rule negligible_Un)
      show "negligible t"
        unfolding negligible_outer_le
      proof (intro strip)
        fix \<epsilon> :: real
        assume "0 < \<epsilon>"
        define M where "M = 3 * (\<bar>B\<bar> + 1) / \<epsilon>"
        have "0 < M"
          unfolding M_def using \<open>0 < \<epsilon>\<close> by (auto intro: divide_pos_pos)
        have interval_witness: 
          "\<exists>u v. u \<in> {a..b} \<and> v \<in> {a..b} \<and> x \<in> {u<..<v} \<and>
                  M * \<bar>v - u\<bar> \<le> norm (f u - f v)" if "x \<in> t" for x
        proof -
          from that have xab: "x \<in> {a<..<b}" and xcont: "isCont f x"
            and xnlip: "\<not> (\<exists>B>0. eventually (\<lambda>y. norm (f y - f x) \<le> B * norm (y-x)) (at x))"
            unfolding t_def by auto
          from xab obtain d where "d > 0" and dsub: "\<And>x'. \<bar>x' - x\<bar> < d \<Longrightarrow> x' \<in> {a<..<b}"
            by (meson open_greaterThanLessThan open_real)
          have False if "d > 0" 
            and hd: "\<And>y. 0 < dist y x \<Longrightarrow> dist y x < d \<Longrightarrow> norm (f y - f x) \<le> (3*M) * norm (y-x)" for d
          proof -
            have "eventually (\<lambda>y. norm (f y - f x) \<le> (3*M) * norm (y-x)) (at x)"
              unfolding eventually_at using \<open>d > 0\<close> hd by auto
            then show False using xnlip \<open>M>0\<close> by auto
          qed
          then obtain y where yx: "0 < dist y x" "dist y x < d"
            and ylip: "(3*M) * norm (y-x) < norm (f y - f x)"
            by (meson \<open>0 < d\<close> not_le)
          have yab: "y \<in> {a<..<b}"
            using dsub yx(2) by (auto simp: dist_real_def)
          have xab': "x \<in> {a..b}" and yab': "y \<in> {a..b}"
            using xab yab by auto
          \<comment> \<open>Use continuity to find a point z on the opposite side of x from y,
              then the pair (min y z, max y z) witnesses the claim.\<close>
          define \<delta> where "\<delta> = \<bar>y - x\<bar>"
          have "\<delta> > 0" unfolding \<delta>_def using yx by (auto simp: dist_real_def)
          have M\<delta>: "M * \<delta> > 0" using \<open>0 < M\<close> \<open>\<delta> > 0\<close> by auto
          have ylip': "3 * M * \<delta> < norm (f y - f x)"
            using ylip unfolding \<delta>_def by (simp add: real_norm_def)
          from xcont have "(f \<longlongrightarrow> f x) (at x)" by (simp add: isCont_def)
          from tendstoD[OF this M\<delta>]
          obtain d' where "d' > 0" and
            hd': "\<And>z. z \<noteq> x \<Longrightarrow> dist z x < d' \<Longrightarrow> dist (f z) (f x) < M * \<delta>"
            unfolding eventually_at by auto
          \<comment> \<open>Pick z on the opposite side of x from y, close to x\<close>
          define z where "z = (if x < y then x - min \<delta> (min d d') / 2
                                        else x + min \<delta> (min d d') / 2)"
          have zx: "z \<noteq> x"
            unfolding z_def using \<open>d > 0\<close> \<open>d' > 0\<close> \<open>\<delta> > 0\<close> by (auto simp: min_def)
          have dist_zx: "dist z x < min \<delta> (min d d')"
            unfolding z_def \<delta>_def dist_real_def
            using yx \<open>d > 0\<close> \<open>d' > 0\<close> by force
          have xbetween: "x \<in> {min y z <..< max y z}"
            unfolding z_def using yx \<open>d > 0\<close> \<open>d' > 0\<close> \<open>\<delta> > 0\<close>
            by (simp add: \<delta>_def dist_real_def min_def max_def field_simps split: if_split_asm)
          have zab: "z \<in> {a<..<b}"
            using dist_real_def dist_zx dsub by force
          have zab': "z \<in> {a..b}" using zab by auto
          have fz_bound: "norm (f z - f x) < M * \<delta>"
            by (metis dist_norm dist_zx hd' min_less_iff_conj zx)
          have gap_bound: "\<bar>max y z - min y z\<bar> < 2 * \<delta>"
            by (smt (verit) \<delta>_def dist_real_def dist_zx)
          have key: "norm (f z - f y) > 2 * M * \<delta>"
            using norm_triangle_ineq[of "f y - f z" "f z - f x"] ylip' fz_bound
            by (simp add: norm_minus_commute)
          have "M * \<bar>max y z - min y z\<bar> < norm (f (min y z) - f (max y z))"
          proof -
            have "M * \<bar>max y z - min y z\<bar> < M * (2 * \<delta>)"
              using gap_bound \<open>0 < M\<close> by auto
            also have "\<dots> < norm (f (min y z) - f (max y z))"
              using key by (simp add: min_def norm_minus_commute)
            finally show ?thesis .
          qed
          then show ?thesis
            using zab' yab' xbetween
            by (intro exI[of _ "min y z"] exI[of _ "max y z"]) auto
        qed
        then obtain u v where uv: "\<And>x. x \<in> t \<Longrightarrow> u x \<in> {a..b} \<and> v x \<in> {a..b} \<and> x \<in> {u x <..< v x}
                             \<and> M * \<bar>v x - u x\<bar> \<le> norm (f (u x) - f (v x))"
          by metis
        let ?UVT = "(\<lambda>x. box (u x) (v x)) ` t"
        obtain \<F> where "\<F> \<subseteq> ?UVT" "countable \<F>" "\<Union>\<F> = \<Union>?UVT"
          by (smt (verit, best) Lindelof imageE open_box)
        then obtain c where "countable c" and "c \<subseteq> t" 
          and c: "\<Union>((\<lambda>x. box (u x) (v x)) ` c) = \<Union> ?UVT"
          by (metis (lifting) countable_subset_image)
        show "\<exists>T. t \<subseteq> T \<and> T \<in> lmeasurable \<and> Sigma_Algebra.measure lebesgue T \<le> \<epsilon>"
        proof (rule ccontr)
          assume non: "\<nexists>T. t \<subseteq> T \<and> T \<in> lmeasurable \<and> Sigma_Algebra.measure lebesgue T \<le> \<epsilon>"
          let ?\<C> =  "(\<lambda>x. cbox (u x) (v x)) ` c"
          have cnt: "countable ?\<C>"
            using \<open>countable c\<close> by auto
          have meas: "\<And>D. D \<in> ?\<C> \<Longrightarrow> D \<in> lmeasurable"
            by auto
          have tsub: "t \<subseteq> \<Union>?\<C>"
          proof
            fix x assume "x \<in> t"
            then obtain z where "z \<in> c" "x \<in> box (u z) (v z)"
              using c uv by fastforce
            then show "x \<in> \<Union>?\<C>"
              using box_subset_cbox by blast
          qed
          have "\<exists>P. finite P \<and> P \<subseteq> ?\<C> \<and> \<epsilon> < measure lebesgue (\<Union>P)"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then have bound: "\<And>\<E>. \<E> \<subseteq> ?\<C> \<Longrightarrow> finite \<E> \<Longrightarrow> measure lebesgue (\<Union>\<E>) \<le> \<epsilon>"
              by (meson linorder_not_less)
            then have "\<exists>T. t \<subseteq> T \<and> T \<in> lmeasurable \<and> measure lebesgue T \<le> \<epsilon>"
              using tsub
              by (metis (no_types, lifting) cnt fmeasurable_Union_bound meas measure_Union_bound)
            then show False using non by auto
          qed
          then obtain p where "finite p" "p \<subseteq> c"
            and p: "\<epsilon> < measure lebesgue (Union ((\<lambda>x. cbox (u x) (v x)) ` p))"
            by (metis (no_types, lifting) finite_subset_image)
          show False
          proof -
            define \<D> where "\<D> = (\<lambda>x. cbox (u x) (v x)) ` p"
            have fin\<D>: "finite \<D>" unfolding \<D>_def using \<open>finite p\<close> by auto
            have cube: "\<exists>k a' b'. D = cbox a' b' \<and> (\<forall>i\<in>Basis. b' \<bullet> i - a' \<bullet> i = k)"
              if "D \<in> \<D>" for D
            proof -
              from that obtain x where "x \<in> p" "D = cbox (u x) (v x)"
                unfolding \<D>_def by auto
              then show ?thesis
                by (intro exI[of _ "v x - u x"] exI[of _ "u x"] exI[of _ "v x"])
                   (auto simp: Basis_real_def inner_real_def)
            qed
            obtain \<C> where "\<C> \<subseteq> \<D>" "disjoint \<C>"
              and \<C>meas: "measure lebesgue (\<Union>\<D>) / 3 ^ DIM(real) \<le> measure lebesgue (\<Union>\<C>)"
              using Austin_Lemma[OF fin\<D> cube] by auto
            have "\<epsilon> / 3 < measure lebesgue (\<Union>\<C>)"
              using p \<C>meas \<D>_def by force
            moreover obtain p' where "p' \<subseteq> p" and \<C>_eq: "\<C> = (\<lambda>x. cbox (u x) (v x)) ` p'"
              and inj: "inj_on (\<lambda>x. cbox (u x) (v x)) p'"
            proof -
              let ?f = "\<lambda>x. cbox (u x) (v x)"
              have Csub_im: "\<C> \<subseteq> ?f ` p"
                using \<open>\<C> \<subseteq> \<D>\<close> unfolding \<D>_def by auto
              define p' where "p' = inv_into p ?f ` \<C>"
              have p'_sub: "p' \<subseteq> p"
                unfolding p'_def using Csub_im by (auto intro: inv_into_into)
              have C_eq: "\<C> = ?f ` p'"
                by (metis Csub_im image_inv_into_cancel p'_def)
              have "inj_on ?f p'"
              proof (rule inj_onI)
                fix x y assume "x \<in> p'" "y \<in> p'" and eq: "?f x = ?f y"
                from \<open>x \<in> p'\<close> obtain K1 where "K1 \<in> \<C>" and K1: "x = inv_into p ?f K1"
                  unfolding p'_def by auto
                from \<open>y \<in> p'\<close> obtain K2 where "K2 \<in> \<C>" and K2: "y = inv_into p ?f K2"
                  unfolding p'_def by auto
                have "K1 = ?f (inv_into p ?f K1)"
                  using f_inv_into_f[of K1 ?f p] \<open>K1 \<in> \<C>\<close> Csub_im by auto
                also have "\<dots> = ?f (inv_into p ?f K2)" 
                  using eq K1 K2 by fastforce
                also have "\<dots> = K2"
                  using f_inv_into_f[of K2 ?f p] \<open>K2 \<in> \<C>\<close> Csub_im by auto
                finally have "K1 = K2" .
                then show "x = y" using K1 K2 by simp
              qed
              then show ?thesis using that p'_sub C_eq by blast
            qed
            have finp': "finite p'" using \<open>p' \<subseteq> p\<close> \<open>finite p\<close> finite_subset by blast
            have p'sub: "p' \<subseteq> t" using \<open>p' \<subseteq> p\<close> \<open>p \<subseteq> c\<close> \<open>c \<subseteq> t\<close> by auto
            have ux_less_vx: "u x < v x" if "x \<in> p'" for x
              using uv[of x] p'sub that by auto
            have "measure lebesgue (\<Union>\<C>) \<le> (\<Sum>x\<in>p'. v x - u x)"
            proof -
              have "measure lebesgue (\<Union>\<C>) \<le> (\<Sum>D\<in>\<C>. measure lebesgue D)"
                by (metis (no_types, lifting) \<C>_eq \<open>\<C> \<subseteq> \<D>\<close> cbox_borel fin\<D> finite_subset 
                    imageE measure_Union_le sets_completionI_sets sets_lborel)
              also have "\<dots> \<le> (\<Sum>x\<in>p'. measure lebesgue (cbox (u x) (v x)))"
                by (metis (no_types, lifting) \<C>_eq dual_order.eq_iff inj sum.reindex_cong)
              also have "\<dots> = (\<Sum>x\<in>p'. v x - u x)"
                by (simp add: measure_lborel_cbox_eq content_real less_imp_le ux_less_vx)
              finally show ?thesis .
            qed
            also have "\<dots> \<le> (\<Sum>x\<in>p'. norm (f (u x) - f (v x))) / M"
            proof -
              have "(\<Sum>x\<in>p'. v x - u x) \<le> (\<Sum>x\<in>p'. norm (f (u x) - f (v x)) / M)"
              proof (intro sum_mono)
                fix x assume "x \<in> p'"
                then have "M * (v x - u x) \<le> norm (f (u x) - f (v x))"
                  using uv p'sub ux_less_vx by fastforce
                then show "v x - u x \<le> norm (f (u x) - f (v x)) / M"
                  using \<open>0 < M\<close> by (simp add: field_simps)
              qed
              also have "\<dots> = (\<Sum>x\<in>p'. norm (f (u x) - f (v x))) / M"
                by (simp add: sum_divide_distrib)
              finally show ?thesis .
            qed
            also have "\<dots> \<le> B / M"
            proof -
              have div: "\<C> division_of \<Union>\<C>"
                unfolding division_of_def
              proof (intro conjI)
                show "finite \<C>"
                  using finp' unfolding \<C>_eq by auto
                show "\<forall>K\<in>\<C>. K \<subseteq> \<Union>\<C> \<and> K \<noteq> {} \<and> (\<exists>a b. K = cbox a b)"
                  unfolding \<C>_eq using p'sub uv by fastforce
                show "\<forall>K1\<in>\<C>. \<forall>K2\<in>\<C>. K1 \<noteq> K2 \<longrightarrow> interior K1 \<inter> interior K2 = {}"
                  by (metis \<open>disjoint \<C>\<close> disjointD interior_Int interior_empty)
              qed auto
              have Csub: "\<Union>\<C> \<subseteq> {a..b}"
                unfolding \<C>_eq using p'sub uv by fastforce
              have "(\<Sum>x\<in>p'. norm (f (u x) - f (v x)))
                    = (\<Sum>x\<in>p'. norm (f (Sup (cbox (u x) (v x))) - f (Inf (cbox (u x) (v x)))))"
                by (simp add: less_imp_le ux_less_vx norm_minus_commute)
              also have "\<dots> = (\<Sum>K\<in>\<C>. norm (f (Sup K) - f (Inf K)))"
                unfolding \<C>_eq using sum.reindex[OF inj, of "\<lambda>K. norm (f (Sup K) - f (Inf K))"]
                by (simp add: comp_def)
              also have "\<dots> \<le> B" using B[OF div Csub] .
              finally have "(\<Sum>x\<in>p'. norm (f (u x) - f (v x))) \<le> B" .
              then show ?thesis using \<open>0 < M\<close> by (simp add: divide_right_mono)
            qed
            also have "\<dots> < \<epsilon> / 3"
              unfolding M_def using \<open>0 < \<epsilon>\<close> by (simp add: abs_if field_simps)
            ultimately show False by linarith
          qed
        qed
      qed
    qed auto
  qed (auto simp: t_def)
  define D where "D = {x \<in> {a..b}. \<not> isCont f x}"
  have "countable D"
    unfolding D_def using has_bounded_variation_countable_discontinuities[OF assms] .
  hence "negligible (T \<union> D)"
    using tn negligible_Un countable_imp_negligible by blast
  then show ?thesis
    using D_def tc by blast
qed

lemma cover_T:
  fixes f :: "real \<Rightarrow> real" and a b k :: real
  assumes f: "has_bounded_variation_on f {a..b}" and "0 < k"
    and key_fn: "\<And>x. x \<in> T \<Longrightarrow> {cx x..dx x} \<in> D \<and> x \<in> {cx x<..<dx x} \<and>
                   ux x \<in> {cx x<..<dx x} \<and> vx x \<in> {cx x<..<dx x} \<and>
                   x \<in> {ux x<..<vx x} \<and>
                   (f (cx x) \<le> f (dx x) \<longrightarrow> f (vx x) - f (ux x) \<le> -k * (vx x - ux x)) \<and>
                   (f (dx x) < f (cx x) \<longrightarrow> k * (vx x - ux x) \<le> f (vx x) - f (ux x))"
    and D_div: "D division_of {a..b}"
    and D_sum: "vector_variation {a..b} f - k * e / 3 < (\<Sum>K\<in>D. norm (f (Sup K) - f (Inf K)))"
  obtains C where "T \<subseteq> C" "C \<in> lmeasurable" "measure lebesgue C \<le> e"
proof (rule ccontr)
  assume non: "\<not> ?thesis"
    \<comment> \<open>Apply Lindelöf to the family of open intervals\<close>
  have fin_D: "finite D"
    using D_div division_of_finite by blast
  let ?UVT = "(\<lambda>x. {ux x<..<vx x}) ` T"
  obtain \<F> where "\<F> \<subseteq> ?UVT" "countable \<F>" "\<Union>\<F> = \<Union>?UVT"
    by (smt (verit, best) Lindelof imageE open_greaterThanLessThan)
  then obtain c where "countable c" and "c \<subseteq> T"
    and c_union: "\<Union>((\<lambda>x. {ux x<..<vx x}) ` c) = \<Union>?UVT"
    by (metis (lifting) countable_subset_image)
  have "\<exists>p. finite p \<and> p \<subseteq> (\<lambda>x. {ux x..vx x}) ` c \<and> e < measure lebesgue (\<Union>p)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have le_e: "\<And>p. p \<subseteq> (\<lambda>x. {ux x..vx x}) ` c \<Longrightarrow> finite p \<Longrightarrow> measure lebesgue (\<Union>p) \<le> e"
      by (meson linorder_not_less)
    have union_le: "measure lebesgue (\<Union>((\<lambda>x. {ux x..vx x}) ` c)) \<le> e"
      by (rule measure_Union_bound)
        (use \<open>countable c\<close> le_e lmeasurable_cbox in \<open>auto simp: cbox_interval\<close>)
    have "T \<subseteq> \<Union>((\<lambda>x. {ux x..vx x}) ` c)"
    proof
      fix x assume "x \<in> T"
      then have "x \<in> \<Union>((\<lambda>x. {ux x<..<vx x}) ` T)" using key_fn by auto
      then show "x \<in> \<Union>((\<lambda>x. {ux x..vx x}) ` c)" using c_union by force
    qed
    moreover have "\<Union>((\<lambda>x. {ux x..vx x}) ` c) \<in> lmeasurable"
      using \<open>countable c\<close> le_e by (intro fmeasurable_Union_bound[where B=e]) auto
    ultimately have *: "e < measure lebesgue (\<Union>((\<lambda>x. {ux x..vx x}) ` c))"
      using non that union_le by blast
    with union_le show False by linarith
  qed
  then obtain Q where "finite Q" "Q \<subseteq> (\<lambda>x. {ux x..vx x}) ` c"
    "e < measure lebesgue (\<Union>Q)" by auto
  from finite_subset_image[OF \<open>finite Q\<close> \<open>Q \<subseteq> (\<lambda>x. {ux x..vx x}) ` c\<close>]
  obtain p where "p \<subseteq> c" "finite p" "Q = (\<lambda>x. {ux x..vx x}) ` p" by auto
  then have fin_p: "finite p" and p_sub: "p \<subseteq> c"
    and p_meas: "e < measure lebesgue (\<Union>((\<lambda>x. {ux x..vx x}) ` p))"
    using \<open>e < measure lebesgue (\<Union>Q)\<close> by auto                                       
      \<comment> \<open>Apply Austin's lemma to the finite collection of intervals\<close>
  define \<D> where "\<D> = (\<lambda>x. {ux x..vx x}) ` p"
  have fin\<D>: "finite \<D>" unfolding \<D>_def using fin_p by auto
  have cube: "\<exists>k a b. D = cbox a b \<and> (\<forall>i\<in>Basis. b \<bullet> i - a \<bullet> i = k)" if "D \<in> \<D>" for D
    using \<D>_def that by auto
  obtain d where "d \<subseteq> \<D>" "disjoint d"
    and d_meas: "measure lebesgue (\<Union>\<D>) / 3 ^ DIM(real) \<le> measure lebesgue (\<Union>d)"
    using Austin_Lemma[OF fin\<D> cube] by auto
  have "\<exists>j. j \<in> D \<and> i \<subseteq> j" if "i \<in> d" for i    
  proof -
    from that \<open>d \<subseteq> \<D>\<close> obtain x where "x \<in> p" and x: "i = {ux x..vx x}"
      unfolding \<D>_def by auto
    then have "x \<in> T" using p_sub \<open>c \<subseteq> T\<close> by auto
    from key_fn[OF this] show ?thesis
      by (metis atLeastatMost_subset_iff greaterThanLessThan_iff less_eq_real_def x)
  qed
  then have d_decomp: "\<Union>d = (\<Union>j\<in>D. \<Union>{i \<in> d. i \<subseteq> j})"
    by blast
  let ?F = "(\<lambda>j. \<Union>{i \<in> d. i \<subseteq> j}) ` D"
  have fin_F: "finite ?F"
    using fin_D by auto
  have fin_d: "finite d" using finite_subset[OF \<open>d \<subseteq> \<D>\<close> fin\<D>] .
  have meas_F: "S \<in> sets lebesgue" if "S \<in> ?F" for S           
    using fin_d \<open>d \<subseteq> \<D>\<close> fmeasurableD[OF fmeasurable_cbox] that
    by (auto intro!: sets.finite_Union simp: \<D>_def cbox_interval)
  have "measure lebesgue (\<Union>d) = measure lebesgue (\<Union>?F)"
    using d_decomp by (simp add: image_UN)
  also have "\<dots> \<le> sum (measure lebesgue) ?F"
    using measure_Union_le[OF fin_F meas_F] .
  also have "\<dots> \<le> (\<Sum>j\<in>D. measure lebesgue (\<Union>{i \<in> d. i \<subseteq> j}))"
    using sum_image_le [unfolded o_def] fin_D measure_nonneg by blast
  also have "\<dots> < e / 3"
  proof -
    have per_elt: "measure lebesgue (\<Union>{i \<in> d. i \<subseteq> K}) * k \<le> vector_variation K f - norm (f (Sup K) - f (Inf K))"
      if "K \<in> D" for K
    proof -
      obtain l r where K_eq: "K = {l..r}" and "l \<le> r"
        using division_ofD[OF D_div] \<open>K \<in> D\<close> by (metis atLeastatMost_empty_iff2 box_real(2))
      have meas_i: "i \<in> sets lebesgue" if "i \<in> d" "i \<subseteq> {l..r}" for i
        using fmeasurableD[OF fmeasurable_cbox[of "ux x" "vx x"]]
        using \<D>_def \<open>d \<subseteq> \<D>\<close> that(1) by auto
      define d' where "d' = {i \<in> d. i \<subseteq> {l..r}}"
      have disj_d': "disjoint d'"
        using \<open>disjoint d\<close> d'_def pairwise_subset by force
      have d'_ne: "K \<noteq> {}" if "K \<in> d'" for K
      proof -
        from that obtain x where "x \<in> p" "K = {ux x..vx x}"
          using \<open>d \<subseteq> \<D>\<close> unfolding d'_def \<D>_def by auto
        then have "x \<in> T" using p_sub \<open>c \<subseteq> T\<close> by auto
        from key_fn[OF this]  show ?thesis using \<open>K = {ux x..vx x}\<close> by auto
      qed
      have fin_d': "finite d'" unfolding d'_def using fin_d by auto
      have d'_div: "d' division_of \<Union>d'"
        unfolding division_of_def
      proof (intro conjI ballI impI)
        fix K assume "K \<in> d'"
        then have "K \<in> \<D>" using \<open>d \<subseteq> \<D>\<close> d'_def by blast
        then show "\<exists>a b. K = cbox a b"
          unfolding \<D>_def by (auto simp: cbox_interval)
      next
        fix K1 K2 assume "K1 \<in> d'" "K2 \<in> d'" "K1 \<noteq> K2"
        then show "interior K1 \<inter> interior K2 = {}"
          using disj_d' by (metis disjointD interior_Int interior_empty)
      qed (use fin_d' d'_ne in auto)
      have d'_sub_lr: "\<Union>d' \<subseteq> {l..r}"
        unfolding d'_def by auto
      obtain d'' where d'_sub_d'': "d' \<subseteq> d''" and d''_div: "d'' division_of {l..r}"
        and "finite d''"
        by (metis box_real(2) d'_div d'_sub_lr division_of_finite partial_division_extend_interval)
      have "measure lebesgue (\<Union> d') \<le> (\<Sum>i\<in>d'. measure lebesgue i)"
        using meas_i d'_div by (intro measure_Union_le) (auto simp: d'_def)
      also have "\<dots> \<le> (vector_variation {l..r} f - \<bar>f r - f l\<bar>) / k"
      proof -
        define s where "s \<equiv> if f l \<le> f r then (1::real) else -1"
        have s_abs: "s * (f r - f l) = \<bar>f r - f l\<bar>"
          unfolding s_def by auto
        have bv_lr: "has_bounded_variation_on f {l..r}"
          by (metis D_div K_eq assms(1) cbox_division_memE has_bounded_variation_on_subset that)
        have sum_abs_le: "(\<Sum>i\<in>d''. \<bar>f (Sup i) - f (Inf i)\<bar>) \<le> vector_variation {l..r} f"
          using has_bounded_variation_works(1)[OF bv_lr d''_div order_refl]
          by (simp add: real_norm_def)
        have sum_telesc: "(\<Sum>i\<in>d''. f (Sup i) - f (Inf i)) = f r - f l"
          using division_telescope_eq[OF d''_div \<open>l \<le> r\<close>] .
        have elt_bound: "measure lebesgue i * k \<le> \<bar>f (Sup i) - f (Inf i)\<bar> - s * (f (Sup i) - f (Inf i))"
          if i_in_d': "i \<in> d'" for i
        proof -
          from i_in_d' obtain x where "x \<in> p" "i = {ux x..vx x}"
            using \<open>d \<subseteq> \<D>\<close> unfolding d'_def \<D>_def by auto
          have "x \<in> T" using \<open>x \<in> p\<close> p_sub \<open>c \<subseteq> T\<close> by auto
          have uv_lt: "ux x < vx x" using key_fn[OF \<open>x \<in> T\<close>] by auto
          have i_sub_lr: "{ux x..vx x} \<subseteq> {l..r}"
            using i_in_d' unfolding d'_def \<open>i = {ux x..vx x}\<close> by auto
          have "interior {l..r} \<inter> interior {cx x..dx x} \<noteq> {}"
            using key_fn[OF \<open>x \<in> T\<close>] i_sub_lr by auto
          then have "{cx x..dx x} = {l..r}"
            using D_div K_eq \<open>K \<in> D\<close> key_fn[OF \<open>x \<in> T\<close>] by blast
          then have "cx x = l" "dx x = r"
            using key_fn[OF \<open>x \<in> T\<close>] \<open>l \<le> r\<close> by (auto simp: Icc_eq_Icc)
          have meas_eq: "measure lebesgue i = vx x - ux x"
            unfolding \<open>i = {ux x..vx x}\<close>
            using uv_lt by (simp add: measure_lborel_cbox_eq content_real less_imp_le cbox_interval)
          have eq: "Sup i = vx x" "Inf i = ux x" unfolding \<open>i = {ux x..vx x}\<close>
            using uv_lt by (simp_all add: less_imp_le)
          show ?thesis
          proof (cases "f l \<le> f r")
            case True
            then have "f (vx x) - f (ux x) \<le> - k * (vx x - ux x)"
              using key_fn[OF \<open>x \<in> T\<close>] \<open>cx x = l\<close> \<open>dx x = r\<close> by auto
            with True uv_lt \<open>0 < k\<close>
            have fvu_neg: "f (vx x) - f (ux x) \<le> 0"
              by (smt (verit, ccfv_threshold) mult_neg_pos)
            then show ?thesis unfolding eq meas_eq s_def
              using \<open>f (vx x) - f (ux x) \<le> - k * (vx x - ux x)\<close> uv_lt \<open>0 < k\<close> True
              by (simp add: mult.commute)
          next
            case False
            then have "k * (vx x - ux x) \<le> f (vx x) - f (ux x)"
              using key_fn[OF \<open>x \<in> T\<close>] \<open>cx x = l\<close> \<open>dx x = r\<close> by auto
            with False uv_lt \<open>0 < k\<close>
            have fvu_pos: "f (vx x) - f (ux x) \<ge> 0"
              by (metis order.trans ge_iff_diff_ge_0 less_le zero_le_mult_iff)
            then show ?thesis unfolding eq meas_eq s_def
              using \<open>k * (vx x - ux x) \<le> f (vx x) - f (ux x)\<close> uv_lt \<open>0 < k\<close>
              by (simp add: False mult.commute)
          qed
        qed
        have "(\<Sum>i\<in>d'. measure lebesgue i) * k = (\<Sum>i\<in>d'. measure lebesgue i * k)"
          by (simp add: sum_distrib_right)
        also have "\<dots> \<le> (\<Sum>i\<in>d'. \<bar>f (Sup i) - f (Inf i)\<bar> - s * (f (Sup i) - f (Inf i)))"
          by (rule sum_mono) (use elt_bound in auto)
        also have "\<dots> \<le> (\<Sum>i\<in>d''. \<bar>f (Sup i) - f (Inf i)\<bar> - s * (f (Sup i) - f (Inf i)))"
          using \<open>finite d''\<close> d'_sub_d''
          by (intro sum_mono2) (auto simp: s_def)
        also have "\<dots> = (\<Sum>i\<in>d''. \<bar>f (Sup i) - f (Inf i)\<bar>) - s * (\<Sum>i\<in>d''. f (Sup i) - f (Inf i))"
          by (simp add: sum_subtractf sum_distrib_left[symmetric])
        also have "\<dots> = (\<Sum>i\<in>d''. \<bar>f (Sup i) - f (Inf i)\<bar>) - s * (f r - f l)"
          by (simp add: sum_telesc)
        also have "\<dots> \<le> vector_variation {l..r} f - \<bar>f r - f l\<bar>"
          using sum_abs_le by (simp add: s_abs)
        finally show ?thesis using \<open>0 < k\<close>
          by (simp add: divide_simps)
      qed
      finally show ?thesis using \<open>l \<le> r\<close> \<open>k>0\<close>
        by (simp add: K_eq d'_def divide_simps)
    qed
    have "(\<Sum>j\<in>D. measure lebesgue (\<Union>{i \<in> d. i \<subseteq> j})) * k
        = (\<Sum>j\<in>D. measure lebesgue (\<Union>{i \<in> d. i \<subseteq> j}) * k)"
      by (simp add: sum_distrib_right)
    also have "\<dots> \<le> (\<Sum>j\<in>D. vector_variation j f - norm (f (Sup j) - f (Inf j)))"
      by (rule sum_mono) (rule per_elt)
    also have "\<dots> = (\<Sum>j\<in>D. vector_variation j f) - (\<Sum>K\<in>D. norm (f (Sup K) - f (Inf K)))"
      by (simp add: sum_subtractf)
    also have "\<dots> \<le> vector_variation {a..b} f - (\<Sum>K\<in>D. norm (f (Sup K) - f (Inf K)))"
    proof -
      have "(\<Sum>j\<in>E. vector_variation j f) \<le> vector_variation (\<Union>E) f"
        if "finite E" "E \<subseteq> D" for E
        using that 
      proof (induction rule: finite_induct)
        case empty
        then show ?case by (simp add: vector_variation_def set_variation_def)
      next
        case (insert K F)
        then have "F \<subseteq> D" and K_in_D: "K \<in> D" by auto
        have IH: "(\<Sum>j\<in>F. vector_variation j f) \<le> vector_variation (\<Union>F) f"
          using insert(3)[OF \<open>F \<subseteq> D\<close>] .
        have disj_int: "interior K \<inter> interior (\<Union>F) = {}"
        proof (rule Int_interior_Union_intervals)
          fix U assume "U \<in> F"
          then have "U \<in> D" using \<open>F \<subseteq> D\<close> by auto
          show "\<exists>a b. U = cbox a b"
            using division_ofD(4)[OF D_div \<open>U \<in> D\<close>] by auto
          have "K \<noteq> U" using insert \<open>U \<in> F\<close> by auto
          show "interior K \<inter> interior U = {}"
            using division_ofD(5)[OF D_div K_in_D \<open>U \<in> D\<close> \<open>K \<noteq> U\<close>] .
        qed (use insert in auto)
        have bv_KF: "has_bounded_variation_on f (K \<union> \<Union>F)"
          using division_ofD(2)[OF D_div] insert(4)
          by (intro has_bounded_variation_on_subset[OF assms(1)]) auto
        have "(\<Sum>j\<in>insert K F. vector_variation j f) = vector_variation K f + (\<Sum>j\<in>F. vector_variation j f)"
          using insert by auto
        also have "\<dots> \<le> vector_variation (K \<union> \<Union>F) f"
          using vector_variation_le_Un[OF bv_KF disj_int] IH by linarith
        also have "K \<union> \<Union>F = \<Union>(insert K F)" by auto
        finally show ?case by simp
      qed
      then show ?thesis
        by (metis (lifting) ext D_div diff_mono division_ofD(6) fin_D order.refl)
    qed
    finally have sum_k_le: "(\<Sum>j\<in>D. measure lebesgue (\<Union>{i \<in> d. i \<subseteq> j})) * k
                \<le> vector_variation {a..b} f - (\<Sum>K\<in>D. norm (f (Sup K) - f (Inf K)))" .
    with D_sum have "(\<Sum>j\<in>D. measure lebesgue (\<Union>{i \<in> d. i \<subseteq> j})) * k < k * e / 3"
      by linarith
    then show ?thesis
      using \<open>0 < k\<close> by (simp add: field_simps)
  qed
  finally have d_bound: "measure lebesgue (\<Union>d) < e / 3" .
  show False
    using p_meas d_meas d_bound unfolding \<D>_def by auto
qed

lemma Lebesgue_diff_aux2:
  fixes f :: "real \<Rightarrow> real" and a b k :: real
  assumes f: "has_bounded_variation_on f {a..b}" and "a < b" "0 < k"
  shows "negligible
           {x \<in> {a..b}.
              \<forall>S. open S \<and> x \<in> S \<longrightarrow>
                (\<exists>u v. u \<in> {a..b} \<and> u \<in> S \<and>
                       v \<in> {a..b} \<and> v \<in> S \<and>
                       x \<in> {u<..<v} \<and> k \<le> (f v - f u) / (v-u)) \<and>
                (\<exists>u v. u \<in> {a..b} \<and> u \<in> S \<and>
                       v \<in> {a..b} \<and> v \<in> S \<and>
                       x \<in> {u<..<v} \<and> (f v - f u) / (v-u) \<le> -k)}" (is "negligible ?N")
proof -
  define N where "N \<equiv> ?N"
  have "negligible N"
    unfolding negligible_outer_le
  proof (intro allI impI)
    fix e :: real assume "e > 0"
    have ke3_pos: "0 < k * e / 3"
      using \<open>0 < k\<close> \<open>e > 0\<close> by auto
        \<comment> \<open>Get a division D of @{term \<open>{a..b}\<close>} whose sum exceeds $\text{vector\_variation} - k\varepsilon/3$\<close>
    define S where "S \<equiv> {\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) |d. d division_of {a..b}}"
    have S_ne: "S \<noteq> {}"
      by (metis (mono_tags, lifting) S_def box_real(2) elementary_interval empty_Collect_eq)
    have "vector_variation {a..b} f - k * e / 3 < Sup S"
      using ke3_pos vector_variation_on_interval[OF f] unfolding S_def by linarith
    then obtain x where "x \<in> S" "vector_variation {a..b} f - k * e / 3 < x"
      using less_cSupD[OF S_ne] by auto
    then obtain D where D_div: "D division_of {a..b}"
      and D_sum: "vector_variation {a..b} f - k * e / 3 < (\<Sum>K\<in>D. norm (f (Sup K) - f (Inf K)))"
      unfolding S_def by auto
    have fin_D: "finite D"
      using D_div division_of_finite by blast
    define N' where "N' \<equiv> N - \<Union>(frontier ` D)"
    have neg_frontiers: "negligible (\<Union>(frontier ` D))"
      using fin_D D_div convex_box(1) negligible_convex_frontier by blast
        \<comment> \<open>For each x in t, find division element and witnessing u, v\<close>
    have key: "\<exists>c d u v. {c..d} \<in> D \<and> x \<in> {c<..<d} \<and> u \<in> {c<..<d} \<and> v \<in> {c<..<d} \<and>
                  x \<in> {u<..<v} \<and>
                  (f c \<le> f d \<longrightarrow> f v - f u \<le> -k * (v-u)) \<and>
                  (f d < f c \<longrightarrow> k * (v-u) \<le> f v - f u)" if "x \<in> N'" for x
    proof -
      have xN: "x \<in> N" and xnf: "x \<notin> \<Union>(frontier ` D)" and xab: "x \<in> {a..b}"
        using that unfolding N'_def N_def by auto
          \<comment> \<open>Find the division element containing x\<close>
      have "x \<in> \<Union>D" using xab division_ofD(6)[OF D_div] by auto
      then obtain K c d where "K \<in> D" "x \<in> K" and Kcd: "K = {c..d}"
        by (metis D_div UnionE box_real(2) division_ofD(4))
      then obtain KD: "{c..d} \<in> D" and xK: "x \<in> {c..d}" 
        by blast
      have "x \<notin> frontier K" using xnf \<open>K \<in> D\<close> by auto
      then have "x \<notin> {c..d} - {c<..<d}"
        by (simp add: Kcd frontier_def)
      then have x_int: "x \<in> {c<..<d}" using xK by auto
          \<comment> \<open>Apply the N property with open set {c<..<d}\<close>
      show ?thesis
      proof (cases "f c \<le> f d")
        case True
        from x_int xN obtain u v where
          uv: "u \<in> {c<..<d}" "v \<in> {c<..<d}" "x \<in> {u<..<v}" "(f v - f u) / (v-u) \<le> -k"
          using N_def by auto
        then have "f v - f u \<le> -k * (v-u)" 
          by (simp add: pos_divide_le_eq mult.commute)
        then show ?thesis
          by (smt (verit, ccfv_SIG) KD True uv x_int)
      next
        case False
        from x_int xN obtain u v where uv: "u \<in> {c<..<d}" "v \<in> {c<..<d}" 
                    "x \<in> {u<..<v}" "k \<le> (f v - f u) / (v-u)"
          using N_def by auto
        then have "k * (v-u) \<le> f v - f u" by (simp add: pos_le_divide_eq mult.commute)
        then show ?thesis using False KD uv x_int by blast
      qed
    qed
    then obtain cx dx ux vx where
      key_fn: "\<And>x. x \<in> N' \<Longrightarrow> {cx x..dx x} \<in> D \<and> x \<in> {cx x<..<dx x} \<and>
                   ux x \<in> {cx x<..<dx x} \<and> vx x \<in> {cx x<..<dx x} \<and>
                   x \<in> {ux x<..<vx x} \<and>
                   (f (cx x) \<le> f (dx x) \<longrightarrow> f (vx x) - f (ux x) \<le> -k * (vx x - ux x)) \<and>
                   (f (dx x) < f (cx x) \<longrightarrow> k * (vx x - ux x) \<le> f (vx x) - f (ux x))"
      by metis
        \<comment> \<open>Reduce to finding a cover\<close>
    obtain C where C_sub: "N' \<subseteq> C" and C_meas: "C \<in> lmeasurable" and C_bound: "measure lebesgue C \<le> e"
      using cover_T [OF f \<open>k>0\<close> key_fn D_div D_sum] by metis
    define T where "T \<equiv> C \<union> \<Union>(frontier ` D)"
    have "N \<subseteq> T" unfolding T_def using C_sub unfolding N'_def by auto
    moreover have "T \<in> lmeasurable"
      using T_def C_meas neg_frontiers negligible_imp_measurable by blast
    moreover have "measure lebesgue T \<le> e"
      by (simp add: C_bound C_meas T_def measure_Un2 neg_frontiers negligible_diff
          negligible_imp_measurable negligible_imp_measure0)
    ultimately show "\<exists>T. N \<subseteq> T \<and> T \<in> lmeasurable \<and> measure lebesgue T \<le> e"
      by blast
  qed
  then show ?thesis
    by (simp add: N_def)
qed

lemma Lebesgue_diff_aux3:
  fixes f :: "real \<Rightarrow> real" and a b k :: real
  assumes "has_bounded_variation_on f {a..b}" "a < b" "0 < k"
  defines "I \<equiv> \<lambda>n x. ball x (inverse (real n + 1)) \<inter> {a..b}"
  shows "negligible
           {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and> k \<le> (f v - f x) / (v-x) \<and>
                             (f u - f x) / (u-x) \<le> -k}" (is "negligible ?T")
proof -
  define T where "T \<equiv> ?T"
  \<comment> \<open>The superset: endpoints U discontinuities U previous set is negligible\<close>
  define L2 where "L2 \<equiv> {x \<in> {a..b}.
      \<forall>S. open S \<and> x \<in> S \<longrightarrow>
        (\<exists>u v. u \<in> {a..b} \<and> u \<in> S \<and> v \<in> {a..b} \<and> v \<in> S \<and>
               x \<in> {u<..<v} \<and> k/2 \<le> (f v - f u) / (v-u)) \<and>
        (\<exists>u v. u \<in> {a..b} \<and> u \<in> S \<and> v \<in> {a..b} \<and> v \<in> S \<and>
               x \<in> {u<..<v} \<and> (f v - f u) / (v-u) \<le> -(k/2))}"
  have neg_endpts: "negligible {a, b}"
    by (rule negligible_finite) simp
  have neg_discont: "negligible {x \<in> {a..b}. \<not> isCont f x}"
    using countable_imp_negligible[OF has_bounded_variation_countable_discontinuities[OF assms(1)]] .
  have neg_L2: "negligible L2"
    unfolding L2_def using Lebesgue_diff_aux2[OF assms(1,2), of "k/2"] assms(3) by simp
  have neg_super: "negligible (({a, b} \<union> {x \<in> {a..b}. \<not> isCont f x}) \<union> L2)"
    by (rule negligible_Un[OF negligible_Un[OF neg_endpts neg_discont] neg_L2])
  show "negligible T"
  proof (rule negligible_subset[OF neg_super])
    show "T \<subseteq> ({a, b} \<union> {x \<in> {a..b}. \<not> isCont f x}) \<union> L2"
    proof (rule subsetI)
      fix x assume "x \<in> T"
      show "x \<in> ({a, b} \<union> {x \<in> {a..b}. \<not> isCont f x}) \<union> L2"
      proof (cases "x = a \<or> x = b \<or> \<not> isCont f x")
        case True
        with \<open>x \<in> T\<close> show ?thesis by (auto simp: T_def)
      next
        case False
          \<comment> \<open>x is interior, continuous, and has the oscillation property\<close>
        have "x \<in> L2"
          unfolding L2_def
        proof (intro CollectI conjI strip)
          show "x \<in> {a..b}"
            using \<open>x \<in> T\<close> by (auto simp: T_def)
        next
          fix S :: "real set"
          assume "open S \<and> x \<in> S"
          then have "open S" "x \<in> S" by auto
          have "x \<in> {a<..<b}"
            using \<open>x \<in> T\<close> False by (auto simp: T_def)
          have "open (S \<inter> {a<..<b})"
            using \<open>open S\<close> open_real_greaterThanLessThan by blast
          then have "\<exists>e>0. ball x e \<subseteq> S \<inter> {a<..<b}"
            using \<open>x \<in> S\<close> \<open>x \<in> {a<..<b}\<close>
            by (simp add: open_contains_ball)
          then obtain e where "e > 0" "ball x e \<subseteq> S \<inter> {a<..<b}"
            by auto
          obtain n :: nat where n_pos: "n \<noteq> 0" and inv_lt: "inverse (real n) < e"
            using real_arch_invD[OF \<open>e > 0\<close>] by blast
          have inv_n1_lt: "inverse (real n + 1) < e"
            by (smt (verit) inv_lt less_imp_inverse_less n_pos of_nat_0_eq_iff of_nat_less_0_iff)
          have ball_sub: "ball x (inverse (real n + 1)) \<subseteq> S \<inter> {a<..<b}"
            using \<open>ball x e \<subseteq> S \<inter> {a<..<b}\<close> inv_n1_lt by auto
          from \<open>x \<in> T\<close> obtain u v where
            uv: "u \<in> I n x" "v \<in> I n x" "u \<noteq> x" "v \<noteq> x" 
                "k \<le> (f v - f x) / (v-x)" "(f u - f x) / (u-x) \<le> -k"
            by (force simp add: T_def)
          have uS: "u \<in> S" and u_int: "u \<in> {a<..<b}" and vS: "v \<in> S" and v_int: "v \<in> {a<..<b}"
            and uab: "u \<in> {a..b}" and vab: "v \<in> {a..b}"
            using uv ball_sub by (auto simp: I_def)
          have fx_cont: "isCont f x" using False by simp
          have cont_slope: "isCont (\<lambda>y. (f v - f y) / (v-y)) x"
            by (intro fx_cont continuous_intros) (auto simp: uv)
          then have eps_delta: "\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow>
              \<bar>(f v - f y) / (v-y) - (f v - f x) / (v-x)\<bar> < \<epsilon>"
            by (simp add: continuous_at_real_range real_norm_def)
          with half_gt_zero[OF \<open>k>0\<close>]
          obtain d where "d > 0" and
            d_prop: "\<forall>y. \<bar>y - x\<bar> < d \<longrightarrow> \<bar>(f v - f y) / (v-y) - (f v - f x) / (v-x)\<bar> < k / 2"
            by blast
          have min_pos: "min d (inverse (real n + 1)) > 0"
            using \<open>d > 0\<close> by (simp add: min_def)
          show "\<exists>u v. u \<in> {a..b} \<and> u \<in> S \<and> v \<in> {a..b} \<and> v \<in> S \<and> x \<in> {u<..<v} \<and> k / 2 \<le> (f v - f u) / (v-u)"
          proof (cases "v < x")
            case True
              \<comment> \<open>v < x; witness y = x + min d (inv(n+1)) / 2 to the right of x\<close>
            define y where "y = x + min d (inverse (real n + 1)) / 2"
            have y_gt_x: "x < y"
              unfolding y_def using min_pos by simp
            have y_dist_d: "\<bar>y - x\<bar> < d" and y_in_ball: "y \<in> ball x (inverse (real n + 1))"
              unfolding y_def using \<open>d > 0\<close> min_pos by (auto simp: min_def dist_real_def ball_def)
            have yS: "y \<in> S" and y_int: "y \<in> {a<..<b}" and yab: "y \<in> {a..b}"
              using y_in_ball ball_sub by auto
            have x_between: "x \<in> {v<..<y}"
              using True y_gt_x by auto
            have "(f v - f y) / (v-y) > (f v - f x) / (v-x) - k / 2"
              using d_prop y_dist_d by (smt (verit))
            with uv have "(f v - f y) / (v-y) > k / 2"
              by linarith
            hence "k / 2 \<le> (f y - f v) / (y-v)"
              using True y_gt_x by (simp add: field_simps)
            then show ?thesis
              using vS vab x_between yS yab by blast
          next
            case False
            define y where "y = x - min d (inverse (real n + 1)) / 2"
            have y_dist: "\<bar>y - x\<bar> < inverse (real n + 1)" and y_dist_d: "\<bar>y - x\<bar> < d"
              unfolding y_def using \<open>d > 0\<close> min_pos by (auto simp: min_def)
            have y_in_ball: "y \<in> ball x (inverse (real n + 1))"
              using y_dist by (simp add: dist_real_def ball_def)
            have yS: "y \<in> S" and y_int: "y \<in> {a<..<b}"
              using y_in_ball ball_sub by auto
            have x_between: "x \<in> {y<..<v}"
              using y_def min_pos False uv by (fastforce simp: I_def)
            have slope_close: "(f v - f y) / (v-y) > (f v - f x) / (v-x) - k / 2"
              using d_prop y_dist_d by (smt (verit))
            with uv have "(f v - f y) / (v-y) > k / 2"
              by linarith
            then show ?thesis
              using less_le uv vS x_between yS y_int by (fastforce simp: I_def)
          qed
          have cont_slope_u: "isCont (\<lambda>y. (f u - f y) / (u-y)) x"
            by (intro fx_cont continuous_intros) (auto simp: uv)
          then have eps_delta_u: "\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow>
                \<bar>(f u - f y) / (u-y) - (f u - f x) / (u-x)\<bar> < \<epsilon>"
            by (simp add: continuous_at_real_range real_norm_def)
          obtain d' where "d' > 0" and
            d'_prop: "\<forall>y. \<bar>y - x\<bar> < d' \<longrightarrow>
                \<bar>(f u - f y) / (u-y) - (f u - f x) / (u-x)\<bar> < k / 2"
            using \<open>0 < k / 2\<close> eps_delta_u by blast
          have min_pos': "min d' (inverse (real n + 1)) > 0"
            using \<open>d' > 0\<close> by (simp add: min_def)
          show "\<exists>u v. u \<in> {a..b} \<and> u \<in> S \<and> v \<in> {a..b} \<and> v \<in> S \<and> x \<in> {u<..<v} \<and> (f v - f u) / (v-u) \<le> - (k/2)"
          proof (cases "u < x")
            case True
              \<comment> \<open>u < x; witness y = x + min d' (inv(n+1)) / 2 to the right of x\<close>
            define y where "y = x + min d' (inverse (real n + 1)) / 2"
            have y_gt_x: "x < y"
              unfolding y_def using min_pos' by simp
            have y_dist: "\<bar>y - x\<bar> < inverse (real n + 1)" and y_dist_d: "\<bar>y - x\<bar> < d'"
              unfolding y_def using \<open>d' > 0\<close> min_pos' by (auto simp: min_def)
            have y_in_ball: "y \<in> ball x (inverse (real n + 1))"
              using y_dist by (simp add: dist_real_def ball_def)
            have yS: "y \<in> S" and y_int: "y \<in> {a<..<b}"
              using y_in_ball ball_sub by auto
            have x_between: "x \<in> {u<..<y}"
              using True y_gt_x by auto
            have "\<bar>(f u - f y) / (u-y) - (f u - f x) / (u-x)\<bar> < k / 2"
              using d'_prop y_dist_d by auto
            then have slope_upper: "(f u - f y) / (u-y) < - (k/2)"
              using uv by linarith
            have "(f y - f u) / (y-u) = (f u - f y) / (u-y)"
              using True y_gt_x by (simp add: field_simps)
            hence "(f y - f u) / (y-u) \<le> - (k/2)"
              using slope_upper by linarith
            then show ?thesis
              using uS uv x_between yS y_int less_le_not_le by (force simp: I_def)
          next
            case False
              \<comment> \<open>x < u; witness y is to the left of x\<close>
            hence xu: "x < u" using uv by linarith
            define y where "y = x - min d' (inverse (real n + 1)) / 2"
            have y_lt_x: "y < x"
              unfolding y_def using min_pos' by simp
            have y_dist: "\<bar>y - x\<bar> < inverse (real n + 1)"
              unfolding y_def using \<open>d' > 0\<close> min_pos' by (auto simp: min_def)
            have y_dist_d: "\<bar>y - x\<bar> < d'"
              unfolding y_def using \<open>d' > 0\<close> min_pos' by (auto simp: min_def)
            have y_in_ball: "y \<in> ball x (inverse (real n + 1))"
              using y_dist by (simp add: dist_real_def ball_def)
            have yS: "y \<in> S" and y_int: "y \<in> {a<..<b}"
              using y_in_ball ball_sub by auto
            have yab: "y \<in> {a..b}"
              using y_int by auto
            have x_between: "x \<in> {y<..<u}"
              using y_lt_x xu by auto
            have y_lt_u: "y < u" using y_lt_x xu by linarith
            have "\<bar>(f u - f y) / (u-y) - (f u - f x) / (u-x)\<bar> < k / 2"
              using d'_prop y_dist_d by auto
            with uv have slope_upper: "(f u - f y) / (u-y) \<le> - (k/2)"
              by linarith
            then show ?thesis
              using uS uv x_between yS yab unfolding I_def by blast
          qed
        qed
        then show ?thesis
          by fastforce 
      qed
    qed
  qed
qed

lemma Lebesgue_diff_aux4:
  fixes f :: "real \<Rightarrow> real" and a b k :: real
  assumes f: "has_bounded_variation_on f {a..b}" and "a < b" "0 < k"
  defines "I \<equiv> \<lambda>n x. ball x (inverse (real n + 1)) \<inter> {a..b}"
  shows "negligible
           {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> (f v - f x) / (v-x) - (f u - f x) / (u-x)}" 
     (is "negligible ?T")
proof -
  define T where "T \<equiv> ?T"
  \<comment> \<open>we get a negligible set outside which f has a local Lipschitz bound\<close>
  from Lebesgue_diff_aux1[OF assms(1)]
  obtain U where neg_U: "negligible U" 
    and U_prop: "\<forall>x \<in> {a..b} - U. \<exists>B>0. \<forall>\<^sub>F y in at x. norm (f y - f x) \<le> B * norm (y-x)"
    by auto
  \<comment> \<open>Define the rational-indexed family\<close>
  define S where "S q \<equiv> {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                             k / 3 \<le> (f v - f x) / (v-x) - q \<and>
                             (f u - f x) / (u-x) - q \<le> -(k/3)}" for q :: real
  \<comment> \<open>The target set T is a subset of this\<close>
  have neg_super: "negligible (U \<union> \<Union>(S ` \<rat>))"
  proof (rule negligible_Un[OF neg_U])
    show "negligible (\<Union>(S ` \<rat>))"
    proof (rule negligible_countable_Union)
      show "countable (S ` \<rat>)"
        using countable_rat by (rule countable_image)
    next
      fix Sq assume "Sq \<in> S ` \<rat>"
      then obtain q where "q \<in> \<rat>" and "Sq = S q" by auto
      show "negligible Sq"
      proof -
        define g where "g \<equiv> \<lambda>x. f x - q * x"
        have bv_id: "has_bounded_variation_on id {a..b}"
          by (rule increasing_bounded_variation) (auto simp: mono_on_def)
        have "has_bounded_variation_on (\<lambda>x. q *\<^sub>R x) {a..b}"
          using has_bounded_variation_on_cmul[OF bv_id] by simp
        then have bv_g: "has_bounded_variation_on g {a..b}"
          unfolding g_def using f has_bounded_variation_on_sub by force
        have Sq_eq: "S q = {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                             k / 3 \<le> (g v - g x) / (v-x) \<and> (g u - g x) / (u-x) \<le> -(k/3)}"
          unfolding S_def
            apply (intro arg_cong[where f="\<lambda>P. {x \<in> {a..b}. P x}"] ext all_cong1 ex_cong1)
            by (auto simp: g_def algebra_simps divide_simps)
        show ?thesis unfolding \<open>Sq = S q\<close> Sq_eq
          using Lebesgue_diff_aux3[OF bv_g \<open>a<b\<close>, of "k/3"] \<open>k>0\<close> by (simp add: I_def)
      qed
    qed
  qed
  show "negligible T"
  proof (rule negligible_subset[OF neg_super])
    show "T \<subseteq> U \<union> \<Union>(S ` \<rat>)"
    proof (rule subsetI)
      fix x assume "x \<in> T"
      then obtain xab: "x \<in> {a..b}" and
        xprop: "\<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                               k \<le> (f v - f x) / (v-x) - (f u - f x) / (u-x)"
        unfolding T_def by blast
      show "x \<in> U \<union> \<Union>(S ` \<rat>)"
      proof (cases "x \<in> U")
        case True then show ?thesis by auto
      next
        case False
        \<comment> \<open>Now x is not in U, so f has a local Lipschitz bound at x\<close>
        have "x \<in> {a..b} - U" using xab False by auto
        from U_prop[rule_format, OF this]
        obtain B where "B > 0" and
          B_ev: "eventually (\<lambda>y. norm (f y - f x) \<le> B * norm (y-x)) (at x)"
          by auto
        \<comment> \<open>The difference quotients are bounded near x; extract a uniform bound on
            difference quotients in sufficiently small balls, then find a rational separator\<close>
        obtain N where dq_bound: "\<And>n u. N \<le> n \<Longrightarrow> u \<in> ball x (inverse (real n + 1)) \<Longrightarrow> u \<noteq> x
            \<Longrightarrow> \<bar>(f u - f x) / (u-x)\<bar> \<le> B"
        proof -
          from B_ev obtain d :: real where "d > 0" and
            d_prop: "\<And>y. y \<noteq> x \<Longrightarrow> dist y x < d \<Longrightarrow> norm (f y - f x) \<le> B * norm (y-x)"
            unfolding eventually_at by auto
          from real_arch_invD[OF \<open>d > 0\<close>]
          obtain N :: nat where "N \<noteq> 0" and "inverse (real N) < d" by auto
          show thesis
          proof 
            fix n u
            assume "N \<le> n" "u \<in> ball x (inverse (real n + 1))" "u \<noteq> x"
            then have "dist u x < inverse (real n + 1)"
              by (simp add: dist_commute)
            also have "inverse (real n + 1) \<le> inverse (real N)"
              using \<open>N \<le> n\<close> \<open>N \<noteq> 0\<close> by auto
            also have "\<dots> < d" by fact
            finally have "dist u x < d" .
            have "\<bar>u - x\<bar> > 0" using \<open>u \<noteq> x\<close> by auto
            with d_prop[OF \<open>u \<noteq> x\<close>] show "\<bar>(f u - f x) / (u-x)\<bar> \<le> B"
              by (simp add: \<open>dist u x < d\<close> pos_divide_le_eq)
          qed
        qed
        have balls_nonempty: "\<And>n. \<exists>u. u \<in> I n x \<and> u \<noteq> x"
          using xprop by blast 
        \<comment> \<open>The infimum of difference quotients over shrinking balls converges\<close>
        define DQ where "DQ n = {(f u - f x) / (u-x) | u.
          u \<in> I n x \<and> u \<noteq> x}" for n
        have S_nonempty: "DQ n \<noteq> {}" for n
          using balls_nonempty[of n] unfolding DQ_def by blast
        have S_bdd: "bdd_below (DQ n)" if "N \<le> n" for n
          using DQ_def abs_le_D2[OF dq_bound[OF \<open>N \<le> n\<close>]] that 
          by (auto simp: bdd_below.unfold minus_le_iff I_def)
        have S_subset: "DQ n \<subseteq> DQ m" if "m \<le> n" for m n
          unfolding DQ_def I_def using less_le_trans that by fastforce
        define g where "g \<equiv> \<lambda>n. Inf (DQ n)"
        have g_mono: "g m \<le> g n" if "N \<le> m" "m \<le> n" for m n
          by (simp add: S_bdd S_nonempty S_subset cInf_superset_mono g_def that)
        have g_bounded: "norm (g (n+N)) \<le> B" for n
        proof -
          have nN: "N \<le> n + N" by simp
          obtain u where u: "u \<in> ball x (inverse (real (n+N) + 1))" "u \<in> {a..b}" "u \<noteq> x"
            using balls_nonempty[of "n + N"] I_def by auto
          have mem: "(f u - f x) / (u-x) \<in> DQ (n+N)" 
            unfolding DQ_def I_def using u by auto
          have "g (n+N) \<le> (f u - f x) / (u-x)"
            unfolding g_def by (rule cInf_lower[OF mem S_bdd[OF nN]])
          also have "\<dots> \<le> B"
            using abs_le_D1[OF dq_bound[OF nN u(1) u(3)]] .
          finally have upper: "g (n+N) \<le> B" .
          have "- B \<le> y" if y: "y \<in> DQ (n+N)" for y
            using dq_bound nN y  
            by (simp add: DQ_def I_def) (metis of_nat_add abs_divide abs_le_D2 add.commute le_add1 minus_le_iff)
          then have "- B \<le> Inf (DQ (n+N))"
            using le_cInf_iff[OF S_nonempty S_bdd[OF nN]] by auto
          with upper show ?thesis
            by (simp add: g_def abs_le_iff)
        qed
        have bseq: "Bseq (\<lambda>n. g (n+N))"
          unfolding Bseq_def using \<open>B > 0\<close> g_bounded by auto
        have "convergent g"
          using Bseq_monoseq_convergent'_inc bseq g_mono by blast
        then obtain l where l_conv: "g \<longlonglongrightarrow> l" using convergentD by auto
        \<comment> \<open>The supremum of difference quotients over shrinking balls converges\<close>
        have S_upper: "y \<le> B" if "N \<le> n" "y \<in> DQ n" for n y
          using abs_le_D1[OF dq_bound] DQ_def I_def that by auto 
        have S_bdd_above: "bdd_above (DQ n)" if "N \<le> n" for n
          using S_upper[OF \<open>N \<le> n\<close>] by fastforce
        define h where "h \<equiv> \<lambda>n. Sup (DQ n)" 
        have h_mono: "h n \<le> h m" if "N \<le> m" "m \<le> n" for m n
          by (simp add: S_bdd_above S_nonempty S_subset cSup_subset_mono h_def that)
        have h_bounded: "norm (h (n+N)) \<le> B" for n
        proof -
          have nN: "N \<le> n + N" by simp
          have upper: "h (n+N) \<le> B"
            using cSup_le_iff[OF S_nonempty S_bdd_above[OF nN]]
            by (metis S_upper add.commute h_def le_add1)
          obtain u where u: "u \<in> ball x (inverse (real (n+N) + 1))" "u \<in> {a..b}" "u \<noteq> x"
            using balls_nonempty[of "n + N"] I_def by auto
          have mem: "(f u - f x) / (u-x) \<in> DQ (n+N)" 
            unfolding DQ_def I_def using u by auto
          have "(f u - f x) / (u-x) \<le> h (n+N)"
            unfolding h_def by (rule cSup_upper[OF mem S_bdd_above[OF nN]])
          moreover have "- B \<le> (f u - f x) / (u-x)"
            using abs_le_D2[OF dq_bound[OF nN u(1) u(3)]] by linarith
          ultimately have lower: "- B \<le> h (n+N)" by linarith
          from upper lower show ?thesis
            by (simp add: abs_le_iff)
        qed
        have bseq_h: "Bseq (\<lambda>n. h (n+N))"
          unfolding Bseq_def using \<open>B > 0\<close> h_bounded by auto
        obtain m where m_conv: "h \<longlonglongrightarrow> m" 
          using convergentD Bseq_monoseq_convergent'_dec bseq_h h_mono by blast 
        have diff_conv: "(\<lambda>n. h n - g n) \<longlonglongrightarrow> m - l"
          by (rule tendsto_diff[OF m_conv l_conv])
        have "k \<le> (\<lambda>n. h n - g n) n" if "N \<le> n" for n
        proof -
          obtain u v where uv: "u \<in> I n x" "v \<in> I n x" "u \<noteq> x" "v \<noteq> x"
            and kle: "k \<le> (f v - f x) / (v-x) - (f u - f x) / (u-x)"
            by (meson xab xprop)
          have *: "(f u - f x) / (u-x) \<in> DQ n"  "(f v - f x) / (v-x) \<in> DQ n"
            unfolding DQ_def using uv by auto
          have "g n \<le> (f u - f x) / (u-x)"
            by (simp add: "*" S_bdd g_def cInf_lower that)
          moreover have "(f v - f x) / (v-x) \<le> h n"
            by (simp add: "*" S_bdd_above h_def cSup_upper that)
          ultimately show "k \<le> (\<lambda>n. h n - g n) n" using kle by linarith
        qed
        then have k_le: "k \<le> m - l" using Lim_bounded2[OF diff_conv]
          by blast
            \<comment> \<open>find a rational witness q\<close>
        have mid: "(l+m) / 2 - k / 6 < (l+m) / 2 + k / 6"
          using assms by auto
        then obtain q where q: "q \<in> \<rat>" "(l+m) / 2 - k / 6 < q" "q < (l+m) / 2 + k / 6"
          using Rats_dense_in_real by blast
        with k_le \<open>0 < k\<close>  have q_l: "k / 3 < q - l" and q_m: "k / 3 < m - q"
          by (auto simp add: field_simps)
        have main: "\<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                            k / 3 \<le> (f v - f x) / (v-x) - q \<and>
                            (f u - f x) / (u-x) - q \<le> - (k/3)" for n
        proof -
          \<comment> \<open>First reduction\<close>
          have neg_lower: False 
            if A: "\<forall>u. u \<in> I n x \<and> u \<noteq> x \<longrightarrow> q - k / 3 \<le> (f u - f x) / (u-x)"
          proof -
            have lb: "q - k / 3 \<le> y" if "y \<in> DQ p" "n \<le> p" for y p
              using S_subset[OF that(2)] that(1) using A DQ_def by auto
            have "q - k / 3 \<le> g p" if "max n N \<le> p" for p
            proof -
              have "q - k / 3 \<le> Inf (DQ p)"
                using le_cInf_iff[OF S_nonempty S_bdd[OF max.cobounded2[THEN le_trans[OF _ that]]]]
                  lb[OF _ max.cobounded1[THEN le_trans[OF _ that]]]
                by auto
              then show ?thesis unfolding g_def .
            qed
            with Lim_bounded2[OF l_conv] have "q - k / 3 \<le> l" by blast
            with q_l show False by linarith
          qed
            \<comment> \<open>Second reduction\<close>
          have neg_upper: False
            if A: "\<forall>v. v \<in> I n x \<and> v \<noteq> x \<longrightarrow> (f v - f x) / (v-x) \<le> k / 3 + q"
          proof -
            have ub: "y \<le> k / 3 + q" if "y \<in> DQ p" "n \<le> p" for y p
              using S_subset[OF that(2)] that(1) using A DQ_def by auto 
            have "h p \<le> k / 3 + q" if "max n N \<le> p" for p
            proof -
              have "Sup (DQ p) \<le> k / 3 + q"
                using cSup_le_iff[OF S_nonempty S_bdd_above[OF max.cobounded2[THEN le_trans[OF _ that]]]]
                  ub[OF _ max.cobounded1[THEN le_trans[OF _ that]]]
                by auto
              then show ?thesis unfolding h_def .
            qed
            then have "\<forall>p \<ge> max n N. h p \<le> k / 3 + q" by auto
            with Lim_bounded[OF m_conv] have "m \<le> k / 3 + q" .
            with q_m show False by linarith
          qed
          show ?thesis
            by (smt (verit) neg_lower neg_upper)
        qed
        have "x \<in> S q" unfolding S_def using xab main by auto
        with \<open>q \<in> \<rat>\<close> q_l show ?thesis
          by blast
      qed
    qed
  qed
qed

lemma Lebesgue_diff_aux5:
  fixes f :: "real \<Rightarrow> real" and a b k :: real
  assumes f: "has_bounded_variation_on f {a..b}" and "a < b" "0 < k"
  defines "I n x \<equiv> ball x (inverse (real n + 1)) \<inter> {a..b}" 
  shows "negligible
           {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> \<bar>(f v - f x) / (v-x) - (f u - f x) / (u-x)\<bar>}"
proof -
  have neg_union: "negligible (
           {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> (f v - f x) / (v-x) - (f u - f x) / (u-x)} \<union>
           {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> ((-f v) - (-f x)) / (v-x) - ((-f u) - (-f x)) / (u-x)})"
    using Lebesgue_diff_aux4 assms unfolding I_def
    by (blast intro: negligible_Un has_bounded_variation_on_neg[OF f])+
  \<comment> \<open>The target set is a subset of the union\<close>
  then show ?thesis
  proof (rule negligible_subset)
    show "{x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> \<bar>(f v - f x) / (v-x) - (f u - f x) / (u-x)\<bar>} \<subseteq>
           {x \<in> {a..b}. \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> (f v - f x) / (v-x) - (f u - f x) / (u-x)} \<union>
           {x \<in> {a..b}. \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> ((-f v) - (-f x)) / (v-x) - ((-f u) - (-f x)) / (u-x)}"
    proof (rule subsetI)
      fix x assume x: "x \<in> {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> \<bar>(f v - f x) / (v-x) - (f u - f x) / (u-x)\<bar>}"
      \<comment> \<open>For any m, n, use m+n to get witnesses in the smaller ball\<close>
      have "\<exists>u v. (u \<in> I m x \<and> v \<in> I m x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                         k \<le> (f v - f x) / (v-x) - (f u - f x) / (u-x)) \<or>
                       (u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                         k \<le> ((-f v) - (-f x)) / (v-x) - ((-f u) - (-f x)) / (u-x))" for m n
      proof -
        from x
        obtain u v where uv: "u \<in> I (m+n) x" "v \<in> I (m+n) x" "u \<noteq> x" "v \<noteq> x"
          "k \<le> \<bar>(f v - f x) / (v-x) - (f u - f x) / (u-x)\<bar>"
          by blast
        have ball_m: "ball x (inverse (real (m+n) + 1)) \<subseteq> ball x (inverse (real m + 1))"
          by (intro subset_ball le_imp_inverse_le) linarith+
        have ball_n: "ball x (inverse (real (m+n) + 1)) \<subseteq> ball x (inverse (real n + 1))"
          by (intro subset_ball le_imp_inverse_le) linarith+
        from uv have "k \<le> (f v - f x) / (v-x) - (f u - f x) / (u-x) \<or>
                         k \<le> -((f v - f x) / (v-x) - (f u - f x) / (u-x))"
          by linarith
        then show ?thesis
          using uv ball_m ball_n x unfolding I_def
          by (smt (verit, ccfv_threshold) mem_Collect_eq)
      qed
      then show "x \<in> {x \<in> {a..b}. \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> (f v - f x) / (v-x) - (f u - f x) / (u-x)} \<union>
                {x \<in> {a..b}. \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> ((-f v) - (-f x)) / (v-x) - ((-f u) - (-f x)) / (u-x)}"
        by (smt (verit) UnCI mem_Collect_eq x)
    qed
  qed
qed

lemma Lebesgue_diff_aux6:
  fixes f :: "real \<Rightarrow> real"
  assumes "has_bounded_variation_on f {a..b}" "a < b"
  defines "I \<equiv> \<lambda>n x. ball x (inverse (real n + 1)) \<inter> {a..b}"
  shows "negligible {x \<in> {a..b}. \<not> f differentiable (at x within {a..b})}"
proof -
  have "negligible {x \<in> {a..b}. \<not> (\<exists>f'. ((\<lambda>y. (f y - f x) / (y-x)) \<longlongrightarrow> f') (at x within {a..b}))}"
  proof -
    define S where "S m = {x \<in> {a..b}.
      \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                     inverse (real m + 1) \<le> \<bar>(f v - f x) / (v-x) - (f u - f x) / (u-x)\<bar>}" for m
    have neg: "negligible (S m)" for m
      unfolding S_def using Lebesgue_diff_aux5 assms by auto
    have "negligible (\<Union>(range S))"
      by (rule negligible_Union_nat[OF neg])
    moreover have "{x \<in> {a..b}. \<not> (\<exists>f'. ((\<lambda>y. (f y - f x) / (y-x)) \<longlongrightarrow> f') (at x within {a..b}))} \<subseteq> \<Union>(range S)"
    proof (rule subsetI)
      fix x assume x: "x \<in> {x \<in> {a..b}. \<not> (\<exists>f'. ((\<lambda>y. (f y - f x) / (y-x)) \<longlongrightarrow> f') (at x within {a..b}))}"
      then obtain e where "e > 0" and osc: "\<forall>d>0. \<exists>u\<in>{a..b}. \<exists>v\<in>{a..b}.
          u \<noteq> x \<and> dist u x < d \<and> v \<noteq> x \<and> dist v x < d \<and>
          e \<le> dist ((f u - f x) / (u-x)) ((f v - f x) / (v-x))"
        unfolding convergent_eq_Cauchy_within by (force simp: not_less)
      obtain m where m: "inverse (real m + 1) < e"
        using reals_Archimedean[OF \<open>e > 0\<close>] by (metis add.commute of_nat_Suc)
      have "x \<in> S m"
        unfolding S_def
      proof (intro CollectI conjI allI)
        fix n :: nat
        have "inverse (real n + 1) > 0" by auto
        with osc obtain u v where "u \<in> {a..b}" "v \<in> {a..b}" "u \<noteq> x" "dist u x < inverse (real n + 1)"
          "v \<noteq> x" "dist v x < inverse (real n + 1)"
          "e \<le> dist ((f u - f x) / (u-x)) ((f v - f x) / (v-x))"
          by blast
        then have "inverse (real m + 1) \<le> \<bar>(f v - f x) / (v-x) - (f u - f x) / (u-x)\<bar>"
          using m by (simp add: dist_real_def)
        moreover have "u \<in> ball x (inverse (real n + 1))" "v \<in> ball x (inverse (real n + 1))"
          using \<open>dist u x < inverse (real n + 1)\<close> \<open>dist v x < inverse (real n + 1)\<close>
          by (simp_all add: dist_commute)
        ultimately show "\<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                     inverse (real m + 1) \<le> \<bar>(f v - f x) / (v-x) - (f u - f x) / (u-x)\<bar>"
          using \<open>u \<in> {a..b}\<close> \<open>v \<in> {a..b}\<close> \<open>u \<noteq> x\<close> \<open>v \<noteq> x\<close>
          using I_def by blast
      qed (use x in auto)
      then show "x \<in> \<Union>(range S)" by auto
    qed
    ultimately show ?thesis by (rule negligible_subset)
  qed
  moreover
  have "\<And>x. f differentiable (at x within {a..b}) \<longleftrightarrow>
            (\<exists>D. ((\<lambda>y. (f y - f x) / (y-x)) \<longlongrightarrow> D) (at x within {a..b}))"
    unfolding vector_differentiable has_vector_derivative_within_1D
    by (simp add: mult.commute[of "inverse _"] divide_inverse)
  ultimately show ?thesis by simp
qed

theorem Lebesgue_differentiation_thm_compact:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "has_bounded_variation_on f (cbox a b)"
  shows "negligible {x \<in> cbox a b. \<not> f differentiable (at x)}"
proof -
  let ?g = "\<lambda>i. (\<lambda>x. f x \<bullet> i)"
  have cw: "(f differentiable at x) = (\<forall>i\<in>Basis. ?g i differentiable at x)" for x
  proof -
    have "at x within UNIV = at x" by (rule at_within_open[OF UNIV_I open_UNIV])
    then show ?thesis using differentiable_componentwise_within[where S=UNIV and a=x and f=f]
      by simp
  qed
  have eq: "{x \<in> cbox a b. \<not> f differentiable (at x)} =
            (\<Union>i\<in>Basis. {x \<in> cbox a b. \<not> ?g i differentiable (at x)})"
    by (auto simp: cw)
  show ?thesis unfolding eq
  proof (rule negligible_Union[OF finite_imageI[OF finite_Basis]], clarsimp)
    fix i :: 'a assume "i \<in> Basis"
    show "negligible {x. a \<le> x \<and> x \<le> b \<and> \<not> ?g i differentiable (at x)}"
    proof (cases "a < b")
      case True
      have sub: "{x \<in> {a..b}. \<not> ?g i differentiable (at x)} \<subseteq>
             insert a (insert b {x \<in> {a..b}. \<not> ?g i differentiable (at x within {a..b})})"
        by (auto simp: at_within_Icc_at)
      have "negligible (insert a (insert b {x \<in> {a..b}. \<not> ?g i differentiable (at x within {a..b})}))"
        using Lebesgue_diff_aux6 [OF has_bounded_variation_on_inner_left] assms True by auto
      with negligible_subset [OF _ sub] show ?thesis by simp
    next
      case False
      then show ?thesis
        by (force intro: negligible_subset[OF negligible_sing[of a]])
    qed
  qed
qed

lemma Lebesgue_differentiation_thm_open:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "open S" "has_bounded_variation_on f S"
  shows "negligible {x \<in> S. \<not> f differentiable (at x)}"
proof -
  obtain \<D> where cnt: "countable \<D>" and sub: "\<D> \<subseteq> Pow S"
    and boxes: "\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>a b. X = cbox a b" and cov: "\<Union> \<D> = S"
    using open_countable_Union_open_cbox[OF assms(1)] by metis
  have eq: "{x \<in> S. \<not> f differentiable (at x)} = \<Union> ((\<lambda>T. {x \<in> T. \<not> f differentiable (at x)}) ` \<D>)"
    using cov by auto
  have "negligible (\<Union> ((\<lambda>T. {x \<in> T. \<not> f differentiable (at x)}) ` \<D>))"
  proof (rule negligible_countable_Union)
    show "countable ((\<lambda>T. {x \<in> T. \<not> f differentiable (at x)}) ` \<D>)"
      using cnt by (rule countable_image)
  next
    fix U assume "U \<in> (\<lambda>T. {x \<in> T. \<not> f differentiable (at x)}) ` \<D>"
    then obtain T where T: "T \<in> \<D>" and Seq: "U = {x \<in> T. \<not> f differentiable (at x)}"
      by auto
    obtain a b where Tab: "T = cbox a b" using boxes[OF T] by auto
    have "has_bounded_variation_on f T"
      using has_bounded_variation_on_subset[OF assms(2)] sub T by auto
    then show "negligible U"
      unfolding Seq Tab
      by (rule Lebesgue_differentiation_thm_compact)
  qed
  then show ?thesis using eq by simp
qed

corollary Lebesgue_differentiation_thm:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "is_interval S" "has_bounded_variation_on f S"
  shows "negligible {x \<in> S. \<not> f differentiable (at x)}"
proof -
  have sub: "{x \<in> S. \<not> f differentiable (at x)} \<subseteq>
             {x \<in> frontier S. \<not> f differentiable (at x)} \<union>
             {x \<in> interior S. \<not> f differentiable (at x)}"
    using closure_subset[of S] by (auto simp: frontier_def)
  have fr: "negligible {x \<in> frontier S. \<not> f differentiable (at x)}"
  proof (rule negligible_subset[OF negligible_finite])
    show "finite (frontier S)"
      using finite_frontier_interval_real[OF assms(1)] by blast
    show "{x \<in> frontier S. \<not> f differentiable (at x)} \<subseteq> frontier S"
      by auto
  qed
  have int: "negligible {x \<in> interior S. \<not> f differentiable (at x)}"
  proof -
    have bv: "has_bounded_variation_on f (interior S)"
      using has_bounded_variation_on_subset[OF assms(2) interior_subset] .
    have op: "open (interior S)" by (rule open_interior)
    \<comment> \<open>Reduces to the open-set case, proved below\<close>
    show ?thesis using Lebesgue_differentiation_thm_open[OF op bv] .
  qed
  show ?thesis
    using negligible_subset[OF negligible_Un[OF fr int] sub] .
qed

corollary Lebesgue_differentiation_thm_alt:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "is_interval S" "has_bounded_variation_on f S"
  shows "\<exists>t. t \<subseteq> S \<and> negligible t \<and> (\<forall>x \<in> S - t. f differentiable (at x))"
proof -
  let ?t = "{x \<in> S. \<not> f differentiable (at x)}"
  have "?t \<subseteq> S" "negligible ?t"
    using Lebesgue_differentiation_thm[OF assms] by auto
  moreover have "\<forall>x \<in> S - ?t. f differentiable (at x)" by auto
  ultimately show ?thesis by blast
qed

corollary Lebesgue_differentiation_thm_gen:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "countable (components S)" "has_bounded_variation_on f S"
  shows "negligible {x \<in> S. \<not> f differentiable (at x)}" proof -
  have "\<exists>y\<in>components S. x \<in> y"
    if "x \<in> S" and "\<not> f differentiable at x"
    for x
    using that
    by (metis UnionE Union_components)
  then have eq: "{x \<in> S. \<not> f differentiable (at x)} =
            \<Union> ((\<lambda>C. {x \<in> C. \<not> f differentiable (at x)}) ` components S)"
    using in_components_subset by blast
  show ?thesis unfolding eq
  proof (rule negligible_countable_Union)
    show "countable ((\<lambda>C. {x \<in> C. \<not> f differentiable (at x)}) ` components S)"
      using assms(1) by (rule countable_image)
  next
    fix U assume "U \<in> (\<lambda>C. {x \<in> C. \<not> f differentiable (at x)}) ` components S"
    then obtain C where C: "C \<in> components S" and Seq: "U = {x \<in> C. \<not> f differentiable (at x)}"
      by auto
    have "is_interval C"
      using in_components_connected[OF C] is_interval_connected_1 by auto
    moreover have "has_bounded_variation_on f C"
      using has_bounded_variation_on_subset[OF assms(2) in_components_subset[OF C]] .
    ultimately show "negligible U"
      unfolding Seq by (rule Lebesgue_differentiation_thm)
  qed
qed

corollary Lebesgue_differentiation_thm_increasing:
  fixes f :: "real \<Rightarrow> real"
  assumes "is_interval S" "mono_on S f"
  shows "negligible {x \<in> S. \<not> f differentiable (at x)}"
proof -
  let ?N = "{x \<in> S. \<not> f differentiable (at x)}"
  have "locally negligible ?N"
    unfolding locally_def
  proof (intro allI impI)
    fix w x assume wx: "openin (top_of_set ?N) w \<and> x \<in> w"
    then have xN: "x \<in> ?N" using openin_imp_subset by blast
    then have "x \<in> S" by simp
    from interval_contains_compact_neighbourhood[OF \<open>is_interval S\<close> this]
    obtain a b d where "0 < d" "x \<in> cbox a b" "cbox a b \<subseteq> S"
      and ball_sub: "ball x d \<inter> S \<subseteq> cbox a b"
      by auto
    have mono_ab: "mono_on {a..b} f"
      using mono_on_subset[OF \<open>mono_on S f\<close> \<open>cbox a b \<subseteq> S\<close>] by (simp add: cbox_interval)
    have neg: "negligible {y \<in> cbox a b. \<not> f differentiable (at y)}"
      by (rule Lebesgue_differentiation_thm_compact[OF
            increasing_bounded_variation[OF mono_ab, folded cbox_interval]])
    let ?U = "w \<inter> ball x d"
    let ?V = "{y \<in> cbox a b. \<not> f differentiable (at y)} \<inter> w"
    have U_open: "openin (top_of_set ?N) ?U"
      using wx by (auto intro!: openin_Int_open[OF _ open_ball])
    have "x \<in> ?U" using wx \<open>0 < d\<close> by auto
    moreover have "?U \<subseteq> ?V"
      using wx openin_imp_subset ball_sub by fastforce
    moreover have "?V \<subseteq> w" by auto
    ultimately show "\<exists>U V. openin (top_of_set ?N) U \<and> negligible V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> w"
      using U_open negligible_subset[OF neg] by (meson inf_le1)
  qed
  then show ?thesis by (simp add: locally_negligible)
qed

corollary Lebesgue_differentiation_thm_decreasing:
  fixes f :: "real \<Rightarrow> real"
  assumes "is_interval S" "antimono_on S f"
  shows "negligible {x \<in> S. \<not> f differentiable (at x)}"
proof -
  have mono: "mono_on S (\<lambda>x. - f x)"
    using assms(2) by (auto simp: monotone_on_def)
  have sub: "{x \<in> S. \<not> f differentiable (at x)} \<subseteq> {x \<in> S. \<not> (\<lambda>x. - f x) differentiable (at x)}"
      using differentiable_minus[of "(\<lambda>x. - f x)"] by auto
  moreover have "negligible {x \<in> S. \<not> (\<lambda>x. - f x) differentiable (at x)}"
    by (rule Lebesgue_differentiation_thm_increasing[OF assms(1) mono])
  ultimately show ?thesis by (rule negligible_subset[rotated])
qed
 
end
