(*  Title:      HOL/Analysis/Improper_Integral.thy
    Author: LC Paulson (ported from HOL Light)
*)

section \<open>Continuity of the indefinite integral; improper integral theorem\<close>

theory "Improper_Integral"
  imports Equivalence_Lebesgue_Henstock_Integration
begin

subsection \<open>Equiintegrability\<close>

text\<open>The definition here only really makes sense for an elementary set.
     We just use compact intervals in applications below.\<close>

definition\<^marker>\<open>tag important\<close> equiintegrable_on (infixr "equiintegrable'_on" 46)
  where "F equiintegrable_on I \<equiv>
         (\<forall>f \<in> F. f integrable_on I) \<and>
         (\<forall>e > 0. \<exists>\<gamma>. gauge \<gamma> \<and>
                    (\<forall>f \<D>. f \<in> F \<and> \<D> tagged_division_of I \<and> \<gamma> fine \<D>
                          \<longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral I f) < e))"

lemma equiintegrable_on_integrable:
     "\<lbrakk>F equiintegrable_on I; f \<in> F\<rbrakk> \<Longrightarrow> f integrable_on I"
  using equiintegrable_on_def by metis

lemma equiintegrable_on_sing [simp]:
     "{f} equiintegrable_on cbox a b \<longleftrightarrow> f integrable_on cbox a b"
  by (simp add: equiintegrable_on_def has_integral_integral has_integral integrable_on_def)

lemma equiintegrable_on_subset: "\<lbrakk>F equiintegrable_on I; G \<subseteq> F\<rbrakk> \<Longrightarrow> G equiintegrable_on I"
  unfolding equiintegrable_on_def Ball_def
  by (erule conj_forward imp_forward all_forward ex_forward | blast)+

lemma equiintegrable_on_Un:
  assumes "F equiintegrable_on I" "G equiintegrable_on I"
  shows "(F \<union> G) equiintegrable_on I"
  unfolding equiintegrable_on_def
proof (intro conjI impI allI)
  show "\<forall>f\<in>F \<union> G. f integrable_on I"
    using assms unfolding equiintegrable_on_def by blast
  show "\<exists>\<gamma>. gauge \<gamma> \<and>
            (\<forall>f \<D>. f \<in> F \<union> G \<and>
                   \<D> tagged_division_of I \<and> \<gamma> fine \<D> \<longrightarrow>
                   norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral I f) < \<epsilon>)"
         if "\<epsilon> > 0" for \<epsilon>
  proof -
    obtain \<gamma>1 where "gauge \<gamma>1"
      and \<gamma>1: "\<And>f \<D>. f \<in> F \<and> \<D> tagged_division_of I \<and> \<gamma>1 fine \<D>
                    \<Longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral I f) < \<epsilon>"
      using assms \<open>\<epsilon> > 0\<close> unfolding equiintegrable_on_def by auto
    obtain \<gamma>2 where  "gauge \<gamma>2"
      and \<gamma>2: "\<And>f \<D>. f \<in> G \<and> \<D> tagged_division_of I \<and> \<gamma>2 fine \<D>
                    \<Longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral I f) < \<epsilon>"
      using assms \<open>\<epsilon> > 0\<close> unfolding equiintegrable_on_def by auto
    have "gauge (\<lambda>x. \<gamma>1 x \<inter> \<gamma>2 x)"
      using \<open>gauge \<gamma>1\<close> \<open>gauge \<gamma>2\<close> by blast
    moreover have "\<forall>f \<D>. f \<in> F \<union> G \<and> \<D> tagged_division_of I \<and> (\<lambda>x. \<gamma>1 x \<inter> \<gamma>2 x) fine \<D> \<longrightarrow>
          norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral I f) < \<epsilon>"
      using \<gamma>1 \<gamma>2 by (auto simp: fine_Int)
    ultimately show ?thesis
      by (intro exI conjI) assumption+
  qed
qed


lemma equiintegrable_on_insert:
  assumes "f integrable_on cbox a b" "F equiintegrable_on cbox a b"
  shows "(insert f F) equiintegrable_on cbox a b"
  by (metis assms equiintegrable_on_Un equiintegrable_on_sing insert_is_Un)


lemma equiintegrable_cmul:
  assumes F: "F equiintegrable_on I"
  shows "(\<Union>c \<in> {-k..k}. \<Union>f \<in> F. {(\<lambda>x. c *\<^sub>R f x)}) equiintegrable_on I"
  unfolding equiintegrable_on_def
  proof (intro conjI impI allI ballI)
  show "f integrable_on I"
    if "f \<in> (\<Union>c\<in>{- k..k}. \<Union>f\<in>F. {\<lambda>x. c *\<^sub>R f x})"
    for f :: "'a \<Rightarrow> 'b"
    using that assms equiintegrable_on_integrable integrable_cmul by blast
  show "\<exists>\<gamma>. gauge \<gamma> \<and> (\<forall>f \<D>. f \<in> (\<Union>c\<in>{- k..k}. \<Union>f\<in>F. {\<lambda>x. c *\<^sub>R f x}) \<and> \<D> tagged_division_of I
          \<and> \<gamma> fine \<D> \<longrightarrow> norm ((\<Sum>(x, K)\<in>\<D>. content K *\<^sub>R f x) - integral I f) < \<epsilon>)"
    if "\<epsilon> > 0" for \<epsilon>
  proof -
    obtain \<gamma> where "gauge \<gamma>"
      and \<gamma>: "\<And>f \<D>. \<lbrakk>f \<in> F; \<D> tagged_division_of I; \<gamma> fine \<D>\<rbrakk>
                    \<Longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral I f) < \<epsilon> / (\<bar>k\<bar> + 1)"
      using assms \<open>\<epsilon> > 0\<close> unfolding equiintegrable_on_def
      by (metis add.commute add.right_neutral add_strict_mono divide_pos_pos norm_eq_zero real_norm_def zero_less_norm_iff zero_less_one)
    moreover have "norm ((\<Sum>(x, K)\<in>\<D>. content K *\<^sub>R c *\<^sub>R (f x)) - integral I (\<lambda>x. c *\<^sub>R f x)) < \<epsilon>"
      if c: "c \<in> {- k..k}"
        and "f \<in> F" "\<D> tagged_division_of I" "\<gamma> fine \<D>"
      for \<D> c f
    proof -
      have "norm ((\<Sum>x\<in>\<D>. case x of (x, K) \<Rightarrow> content K *\<^sub>R c *\<^sub>R f x) - integral I (\<lambda>x. c *\<^sub>R f x))
          = \<bar>c\<bar> * norm ((\<Sum>x\<in>\<D>. case x of (x, K) \<Rightarrow> content K *\<^sub>R f x) - integral I f)"
        by (simp add: algebra_simps scale_sum_right case_prod_unfold flip: norm_scaleR)
      also have "\<dots> \<le> (\<bar>k\<bar> + 1) * norm ((\<Sum>x\<in>\<D>. case x of (x, K) \<Rightarrow> content K *\<^sub>R f x) - integral I f)"
        using c by (auto simp: mult_right_mono)
      also have "\<dots> < (\<bar>k\<bar> + 1) * (\<epsilon> / (\<bar>k\<bar> + 1))"
        by (rule mult_strict_left_mono) (use \<gamma> less_eq_real_def that in auto)
      also have "\<dots> = \<epsilon>"
        by auto
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by (rule_tac x="\<gamma>" in exI) auto
  qed
qed


lemma equiintegrable_add:
  assumes F: "F equiintegrable_on I" and G: "G equiintegrable_on I"
  shows "(\<Union>f \<in> F. \<Union>g \<in> G. {(\<lambda>x. f x + g x)}) equiintegrable_on I"
  unfolding equiintegrable_on_def
proof (intro conjI impI allI ballI)
  show "f integrable_on I"
    if "f \<in> (\<Union>f\<in>F. \<Union>g\<in>G. {\<lambda>x. f x + g x})" for f
    using that equiintegrable_on_integrable assms  by (auto intro: integrable_add)
  show "\<exists>\<gamma>. gauge \<gamma> \<and> (\<forall>f \<D>. f \<in> (\<Union>f\<in>F. \<Union>g\<in>G. {\<lambda>x. f x + g x}) \<and> \<D> tagged_division_of I
          \<and> \<gamma> fine \<D> \<longrightarrow> norm ((\<Sum>(x, K)\<in>\<D>. content K *\<^sub>R f x) - integral I f) < \<epsilon>)"
    if "\<epsilon> > 0" for \<epsilon>
  proof -
    obtain \<gamma>1 where "gauge \<gamma>1"
      and \<gamma>1: "\<And>f \<D>. \<lbrakk>f \<in> F; \<D> tagged_division_of I; \<gamma>1 fine \<D>\<rbrakk>
                    \<Longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral I f) < \<epsilon>/2"
      using assms \<open>\<epsilon> > 0\<close> unfolding equiintegrable_on_def by (meson half_gt_zero_iff)
    obtain \<gamma>2 where  "gauge \<gamma>2"
      and \<gamma>2: "\<And>g \<D>. \<lbrakk>g \<in> G; \<D> tagged_division_of I; \<gamma>2 fine \<D>\<rbrakk>
                    \<Longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g x) - integral I g) < \<epsilon>/2"
      using assms \<open>\<epsilon> > 0\<close> unfolding equiintegrable_on_def by (meson half_gt_zero_iff)
    have "gauge (\<lambda>x. \<gamma>1 x \<inter> \<gamma>2 x)"
      using \<open>gauge \<gamma>1\<close> \<open>gauge \<gamma>2\<close> by blast
    moreover have "norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R h x) - integral I h) < \<epsilon>"
      if h: "h \<in> (\<Union>f\<in>F. \<Union>g\<in>G. {\<lambda>x. f x + g x})"
        and \<D>: "\<D> tagged_division_of I" and fine: "(\<lambda>x. \<gamma>1 x \<inter> \<gamma>2 x) fine \<D>"
      for h \<D>
    proof -
      obtain f g where "f \<in> F" "g \<in> G" and heq: "h = (\<lambda>x. f x + g x)"
        using h by blast
      then have int: "f integrable_on I" "g integrable_on I"
        using F G equiintegrable_on_def by blast+
      have "norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R h x) - integral I h)
          = norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x + content K *\<^sub>R g x) - (integral I f + integral I g))"
        by (simp add: heq algebra_simps integral_add int)
      also have "\<dots> = norm (((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral I f + (\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g x) - integral I g))"
        by (simp add: sum.distrib algebra_simps case_prod_unfold)
      also have "\<dots> \<le> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral I f) + norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g x) - integral I g)"
        by (metis (mono_tags) add_diff_eq norm_triangle_ineq)
      also have "\<dots> < \<epsilon>/2 + \<epsilon>/2"
        using \<gamma>1 [OF \<open>f \<in> F\<close> \<D>] \<gamma>2 [OF \<open>g \<in> G\<close> \<D>] fine  by (simp add: fine_Int)
      finally show ?thesis by simp
    qed
    ultimately show ?thesis
      by meson
  qed
qed

lemma equiintegrable_minus:
  assumes "F equiintegrable_on I"
  shows "(\<Union>f \<in> F. {(\<lambda>x. - f x)}) equiintegrable_on I"
  by (force intro: equiintegrable_on_subset [OF equiintegrable_cmul [OF assms, of 1]])

lemma equiintegrable_diff:
  assumes F: "F equiintegrable_on I" and G: "G equiintegrable_on I"
  shows "(\<Union>f \<in> F. \<Union>g \<in> G. {(\<lambda>x. f x - g x)}) equiintegrable_on I"
  by (rule equiintegrable_on_subset [OF equiintegrable_add [OF F equiintegrable_minus [OF G]]]) auto


lemma equiintegrable_sum:
  fixes F :: "('a::euclidean_space \<Rightarrow> 'b::euclidean_space) set"
  assumes "F equiintegrable_on cbox a b"
  shows "(\<Union>I \<in> Collect finite. \<Union>c \<in> {c. (\<forall>i \<in> I. c i \<ge> 0) \<and> sum c I = 1}.
          \<Union>f \<in> I \<rightarrow> F. {(\<lambda>x. sum (\<lambda>i::'j. c i *\<^sub>R f i x) I)}) equiintegrable_on cbox a b"
    (is "?G equiintegrable_on _")
  unfolding equiintegrable_on_def
proof (intro conjI impI allI ballI)
  show "f integrable_on cbox a b" if "f \<in> ?G" for f
    using that assms by (auto simp: equiintegrable_on_def intro!: integrable_sum integrable_cmul)
  show "\<exists>\<gamma>. gauge \<gamma>
           \<and> (\<forall>g \<D>. g \<in> ?G \<and> \<D> tagged_division_of cbox a b \<and> \<gamma> fine \<D>
              \<longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g x) - integral (cbox a b) g) < \<epsilon>)"
    if "\<epsilon> > 0" for \<epsilon>
  proof -
    obtain \<gamma> where "gauge \<gamma>"
      and \<gamma>: "\<And>f \<D>. \<lbrakk>f \<in> F; \<D> tagged_division_of cbox a b; \<gamma> fine \<D>\<rbrakk>
                    \<Longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral (cbox a b) f) < \<epsilon> / 2"
      using assms \<open>\<epsilon> > 0\<close> unfolding equiintegrable_on_def by (meson half_gt_zero_iff)
    moreover have "norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g x) - integral (cbox a b) g) < \<epsilon>"
      if g: "g \<in> ?G"
        and \<D>: "\<D> tagged_division_of cbox a b"
        and fine: "\<gamma> fine \<D>"
      for \<D> g
    proof -
      obtain I c f where "finite I" and 0: "\<And>i::'j. i \<in> I \<Longrightarrow> 0 \<le> c i"
        and 1: "sum c I = 1" and f: "f \<in> I \<rightarrow> F" and geq: "g = (\<lambda>x. \<Sum>i\<in>I. c i *\<^sub>R f i x)"
        using g by auto
      have fi_int: "f i integrable_on cbox a b" if "i \<in> I" for i
        by (metis Pi_iff assms equiintegrable_on_def f that)
      have *: "integral (cbox a b) (\<lambda>x. c i *\<^sub>R f i x) = (\<Sum>(x, K)\<in>\<D>. integral K (\<lambda>x. c i *\<^sub>R f i x))"
        if "i \<in> I" for i
      proof -
        have "f i integrable_on cbox a b"
          by (metis Pi_iff assms equiintegrable_on_def f that)
        then show ?thesis
          by (intro \<D> integrable_cmul integral_combine_tagged_division_topdown)
      qed
      have "finite \<D>"
        using \<D> by blast
      have swap: "(\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R (\<Sum>i\<in>I. c i *\<^sub>R f i x))
            = (\<Sum>i\<in>I. c i *\<^sub>R (\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f i x))"
        by (simp add: scale_sum_right case_prod_unfold algebra_simps) (rule sum.swap)
      have "norm ((\<Sum>(x, K)\<in>\<D>. content K *\<^sub>R g x) - integral (cbox a b) g)
          = norm ((\<Sum>i\<in>I. c i *\<^sub>R ((\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f i x) - integral (cbox a b) (f i))))"
        unfolding geq swap
        by (simp add: scaleR_right.sum algebra_simps integral_sum fi_int integrable_cmul \<open>finite I\<close> sum_subtractf flip: sum_diff)
      also have "\<dots> \<le> (\<Sum>i\<in>I. c i * \<epsilon> / 2)"
      proof (rule sum_norm_le)
        show "norm (c i *\<^sub>R ((\<Sum>(xa, K)\<in>\<D>. content K *\<^sub>R f i xa) - integral (cbox a b) (f i))) \<le> c i * \<epsilon> / 2"
          if "i \<in> I" for i
        proof -
          have "norm ((\<Sum>(x, K)\<in>\<D>. content K *\<^sub>R f i x) - integral (cbox a b) (f i)) \<le> \<epsilon>/2"
            using \<gamma> [OF _ \<D> fine, of "f i"] funcset_mem [OF f] that  by auto
          then show ?thesis
            using that by (auto simp: 0 mult.assoc intro: mult_left_mono)
        qed
      qed
      also have "\<dots> < \<epsilon>"
        using 1 \<open>\<epsilon> > 0\<close> by (simp add: flip: sum_divide_distrib sum_distrib_right)
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by (rule_tac x="\<gamma>" in exI) auto
  qed
qed

corollary equiintegrable_sum_real:
  fixes F :: "(real \<Rightarrow> 'b::euclidean_space) set"
  assumes "F equiintegrable_on {a..b}"
  shows "(\<Union>I \<in> Collect finite. \<Union>c \<in> {c. (\<forall>i \<in> I. c i \<ge> 0) \<and> sum c I = 1}.
          \<Union>f \<in> I \<rightarrow> F. {(\<lambda>x. sum (\<lambda>i. c i *\<^sub>R f i x) I)})
         equiintegrable_on {a..b}"
  using equiintegrable_sum [of F a b] assms by auto


text\<open> Basic combining theorems for the interval of integration.\<close>

lemma equiintegrable_on_null [simp]:
   "content(cbox a b) = 0 \<Longrightarrow> F equiintegrable_on cbox a b"
  unfolding equiintegrable_on_def 
  by (metis diff_zero gauge_trivial integrable_on_null integral_null norm_zero sum_content_null)


text\<open> Main limit theorem for an equiintegrable sequence.\<close>

theorem equiintegrable_limit:
  fixes g :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  assumes feq: "range f equiintegrable_on cbox a b"
      and to_g: "\<And>x. x \<in> cbox a b \<Longrightarrow> (\<lambda>n. f n x) \<longlonglongrightarrow> g x"
    shows "g integrable_on cbox a b \<and> (\<lambda>n. integral (cbox a b) (f n)) \<longlonglongrightarrow> integral (cbox a b) g"
proof -
  have "Cauchy (\<lambda>n. integral(cbox a b) (f n))"
  proof (clarsimp simp add: Cauchy_def)
    fix e::real
    assume "0 < e"
    then have e3: "0 < e/3"
      by simp
    then obtain \<gamma> where "gauge \<gamma>"
         and \<gamma>: "\<And>n \<D>. \<lbrakk>\<D> tagged_division_of cbox a b; \<gamma> fine \<D>\<rbrakk>
                       \<Longrightarrow> norm((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f n x) - integral (cbox a b) (f n)) < e/3"
      using feq unfolding equiintegrable_on_def
      by (meson image_eqI iso_tuple_UNIV_I)
    obtain \<D> where \<D>: "\<D> tagged_division_of (cbox a b)" and "\<gamma> fine \<D>"  "finite \<D>"
      by (meson \<open>gauge \<gamma>\<close> fine_division_exists tagged_division_of_finite)
    with \<gamma> have \<delta>T: "\<And>n. dist ((\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f n x)) (integral (cbox a b) (f n)) < e/3"
      by (force simp: dist_norm)
    have "(\<lambda>n. \<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f n x) \<longlonglongrightarrow> (\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R g x)"
      using \<D> to_g by (auto intro!: tendsto_sum tendsto_scaleR)
    then have "Cauchy (\<lambda>n. \<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f n x)"
      by (meson convergent_eq_Cauchy)
    with e3 obtain M where
      M: "\<And>m n. \<lbrakk>m\<ge>M; n\<ge>M\<rbrakk> \<Longrightarrow> dist (\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f m x) (\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f n x)
                      < e/3"
      unfolding Cauchy_def by blast
    have "\<And>m n. \<lbrakk>m\<ge>M; n\<ge>M;
                 dist (\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f m x) (\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f n x) < e/3\<rbrakk>
                \<Longrightarrow> dist (integral (cbox a b) (f m)) (integral (cbox a b) (f n)) < e"
       by (metis \<delta>T dist_commute dist_triangle_third [OF _ _ \<delta>T])
    then show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (integral (cbox a b) (f m)) (integral (cbox a b) (f n)) < e"
      using M by auto
  qed
  then obtain L where L: "(\<lambda>n. integral (cbox a b) (f n)) \<longlonglongrightarrow> L"
    by (meson convergent_eq_Cauchy)
  have "(g has_integral L) (cbox a b)"
  proof (clarsimp simp: has_integral)
    fix e::real assume "0 < e"
    then have e2: "0 < e/2"
      by simp
    then obtain \<gamma> where "gauge \<gamma>"
      and \<gamma>: "\<And>n \<D>. \<lbrakk>\<D> tagged_division_of cbox a b; \<gamma> fine \<D>\<rbrakk>
                    \<Longrightarrow> norm((\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f n x) - integral (cbox a b) (f n)) < e/2"
      using feq unfolding equiintegrable_on_def
      by (meson image_eqI iso_tuple_UNIV_I)
    moreover
    have "norm ((\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R g x) - L) < e"
              if "\<D> tagged_division_of cbox a b" "\<gamma> fine \<D>" for \<D>
    proof -
      have "norm ((\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R g x) - L) \<le> e/2"
      proof (rule Lim_norm_ubound)
        show "(\<lambda>n. (\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f n x) - integral (cbox a b) (f n)) \<longlonglongrightarrow> (\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R g x) - L"
          using to_g that L
          by (intro tendsto_diff tendsto_sum) (auto simp: tag_in_interval tendsto_scaleR)
        show "\<forall>\<^sub>F n in sequentially.
                norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f n x) - integral (cbox a b) (f n)) \<le> e/2"
          by (intro eventuallyI less_imp_le \<gamma> that)
      qed auto
      with \<open>0 < e\<close> show ?thesis
        by linarith
    qed
    ultimately
    show "\<exists>\<gamma>. gauge \<gamma> \<and>
             (\<forall>\<D>. \<D> tagged_division_of cbox a b \<and> \<gamma> fine \<D> \<longrightarrow>
                  norm ((\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R g x) - L) < e)"
      by meson
  qed
  with L show ?thesis
    by (simp add: \<open>(\<lambda>n. integral (cbox a b) (f n)) \<longlonglongrightarrow> L\<close> has_integral_integrable_integral)
qed


lemma equiintegrable_reflect:
  assumes "F equiintegrable_on cbox a b"
  shows "(\<lambda>f. f \<circ> uminus) ` F equiintegrable_on cbox (-b) (-a)"
proof -
  have \<section>: "\<exists>\<gamma>. gauge \<gamma> \<and>
            (\<forall>f \<D>. f \<in> (\<lambda>f. f \<circ> uminus) ` F \<and> \<D> tagged_division_of cbox (- b) (- a) \<and> \<gamma> fine \<D> \<longrightarrow>
                   norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral (cbox (- b) (- a)) f) < e)"
       if "gauge \<gamma>" and
           \<gamma>: "\<And>f \<D>. \<lbrakk>f \<in> F; \<D> tagged_division_of cbox a b; \<gamma> fine \<D>\<rbrakk> \<Longrightarrow>
                     norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral (cbox a b) f) < e" for e \<gamma>
  proof (intro exI, safe)
    show "gauge (\<lambda>x. uminus ` \<gamma> (-x))"
      by (metis \<open>gauge \<gamma>\<close> gauge_reflect)
    show "norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R (f \<circ> uminus) x) - integral (cbox (- b) (- a)) (f \<circ> uminus)) < e"
      if "f \<in> F" and tag: "\<D> tagged_division_of cbox (- b) (- a)"
         and fine: "(\<lambda>x. uminus ` \<gamma> (- x)) fine \<D>" for f \<D>
    proof -
      have 1: "(\<lambda>(x,K). (- x, uminus ` K)) ` \<D> tagged_partial_division_of cbox a b"
        if "\<D> tagged_partial_division_of cbox (- b) (- a)"
      proof -
        have "- y \<in> cbox a b"
          if "\<And>x K. (x,K) \<in> \<D> \<Longrightarrow> x \<in> K \<and> K \<subseteq> cbox (- b) (- a) \<and> (\<exists>a b. K = cbox a b)"
             "(x, Y) \<in> \<D>" "y \<in> Y" for x Y y
        proof -
          have "y \<in> uminus ` cbox a b"
            using that by auto
          then show "- y \<in> cbox a b"
            by force
        qed
        with that show ?thesis
          by (fastforce simp: tagged_partial_division_of_def interior_negations image_iff)
      qed
      have 2: "\<exists>K. (\<exists>x. (x,K) \<in> (\<lambda>(x,K). (- x, uminus ` K)) ` \<D>) \<and> x \<in> K"
              if "\<Union>{K. \<exists>x. (x,K) \<in> \<D>} = cbox (- b) (- a)" "x \<in> cbox a b" for x
      proof -
        have xm: "x \<in> uminus ` \<Union>{A. \<exists>a. (a, A) \<in> \<D>}"
          by (simp add: that)
        then obtain a X where "-x \<in> X" "(a, X) \<in> \<D>"
          by auto
        then show ?thesis
          by (metis (no_types, lifting) add.inverse_inverse image_iff pair_imageI)
      qed
      have 3: "\<And>x X y. \<lbrakk>\<D> tagged_partial_division_of cbox (- b) (- a); (x, X) \<in> \<D>; y \<in> X\<rbrakk> \<Longrightarrow> - y \<in> cbox a b"
        by (metis (no_types, lifting) equation_minus_iff imageE subsetD tagged_partial_division_ofD(3) uminus_interval_vector)
      have tag': "(\<lambda>(x,K). (- x, uminus ` K)) ` \<D> tagged_division_of cbox a b"
        using tag  by (auto simp: tagged_division_of_def dest: 1 2 3)
      have fine': "\<gamma> fine (\<lambda>(x,K). (- x, uminus ` K)) ` \<D>"
        using fine by (fastforce simp: fine_def)
      have inj: "inj_on (\<lambda>(x,K). (- x, uminus ` K)) \<D>"
        unfolding inj_on_def by force
      have eq: "content (uminus ` I) = content I"
               if I: "(x, I) \<in> \<D>" and fnz: "f (- x) \<noteq> 0" for x I
      proof -
        obtain a b where "I = cbox a b"
          using tag I that by (force simp: tagged_division_of_def tagged_partial_division_of_def)
        then show ?thesis
          using content_image_affinity_cbox [of "-1" 0] by auto
      qed
      have "(\<Sum>(x,K) \<in> (\<lambda>(x,K). (- x, uminus ` K)) ` \<D>.  content K *\<^sub>R f x) =
            (\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f (- x))"
        by (auto simp add: eq sum.reindex [OF inj] intro!: sum.cong)
      then show ?thesis
        using \<gamma> [OF \<open>f \<in> F\<close> tag' fine'] integral_reflect
        by (metis (mono_tags, lifting) Henstock_Kurzweil_Integration.integral_cong comp_apply split_def sum.cong)
    qed
  qed
   show ?thesis
    using assms
    apply (auto simp: equiintegrable_on_def)
    subgoal for f
      by (metis (mono_tags, lifting) comp_apply integrable_eq integrable_reflect)
    using \<section> by fastforce
qed

subsection\<open>Subinterval restrictions for equiintegrable families\<close>

text\<open>First, some technical lemmas about minimizing a "flat" part of a sum over a division.\<close>

lemma lemma0:
  assumes "i \<in> Basis"
    shows "content (cbox u v) / (interval_upperbound (cbox u v) \<bullet> i - interval_lowerbound (cbox u v) \<bullet> i) =
           (if content (cbox u v) = 0 then 0
            else \<Prod>j \<in> Basis - {i}. interval_upperbound (cbox u v) \<bullet> j - interval_lowerbound (cbox u v) \<bullet> j)"
proof (cases "content (cbox u v) = 0")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis
    using prod.subset_diff [of "{i}" Basis] assms
      by (force simp: content_cbox_if divide_simps  split: if_split_asm)
qed


lemma content_division_lemma1:
  assumes div: "\<D> division_of S" and S: "S \<subseteq> cbox a b" and i: "i \<in> Basis"
      and mt: "\<And>K. K \<in> \<D> \<Longrightarrow> content K \<noteq> 0"
      and disj: "(\<forall>K \<in> \<D>. K \<inter> {x. x \<bullet> i = a \<bullet> i} \<noteq> {}) \<or> (\<forall>K \<in> \<D>. K \<inter> {x. x \<bullet> i = b \<bullet> i} \<noteq> {})"
   shows "(b \<bullet> i - a \<bullet> i) * (\<Sum>K\<in>\<D>. content K / (interval_upperbound K \<bullet> i - interval_lowerbound K \<bullet> i))
          \<le> content(cbox a b)"   (is "?lhs \<le> ?rhs")
proof -
  have "finite \<D>"
    using div by blast
  define extend where
    "extend \<equiv> \<lambda>K. cbox (\<Sum>j \<in> Basis. if j = i then (a \<bullet> i) *\<^sub>R i else (interval_lowerbound K \<bullet> j) *\<^sub>R j)
                       (\<Sum>j \<in> Basis. if j = i then (b \<bullet> i) *\<^sub>R i else (interval_upperbound K \<bullet> j) *\<^sub>R j)"
  have div_subset_cbox: "\<And>K. K \<in> \<D> \<Longrightarrow> K \<subseteq> cbox a b"
    using S div by auto
  have "\<And>K. K \<in> \<D> \<Longrightarrow> K \<noteq> {}"
    using div by blast
  have extend_cbox: "\<And>K.  K \<in> \<D> \<Longrightarrow> \<exists>a b. extend K = cbox a b"
    using extend_def by blast
  have extend: "extend K \<noteq> {}" "extend K \<subseteq> cbox a b" if K: "K \<in> \<D>" for K
  proof -
    obtain u v where K: "K = cbox u v" "K \<noteq> {}" "K \<subseteq> cbox a b"
      using K cbox_division_memE [OF _ div] by (meson div_subset_cbox)
    with i show "extend K \<subseteq> cbox a b"
      by (auto simp: extend_def subset_box box_ne_empty)
    have "a \<bullet> i \<le> b \<bullet> i"
      using K by (metis bot.extremum_uniqueI box_ne_empty(1) i)
    with K show "extend K \<noteq> {}"
      by (simp add: extend_def i box_ne_empty)
  qed
  have int_extend_disjoint:
       "interior(extend K1) \<inter> interior(extend K2) = {}" if K: "K1 \<in> \<D>" "K2 \<in> \<D>" "K1 \<noteq> K2" for K1 K2
  proof -
    obtain u v where K1: "K1 = cbox u v" "K1 \<noteq> {}" "K1 \<subseteq> cbox a b"
      using K cbox_division_memE [OF _ div] by (meson div_subset_cbox)
    obtain w z where K2: "K2 = cbox w z" "K2 \<noteq> {}" "K2 \<subseteq> cbox a b"
      using K cbox_division_memE [OF _ div] by (meson div_subset_cbox)
    have cboxes: "cbox u v \<in> \<D>" "cbox w z \<in> \<D>" "cbox u v \<noteq> cbox w z"
      using K1 K2 that by auto
    with div have "interior (cbox u v) \<inter> interior (cbox w z) = {}"
      by blast
    moreover
    have "\<exists>x. x \<in> box u v \<and> x \<in> box w z"
         if "x \<in> interior (extend K1)" "x \<in> interior (extend K2)" for x
    proof -
      have "a \<bullet> i < x \<bullet> i" "x \<bullet> i < b \<bullet> i"
       and ux: "\<And>k. k \<in> Basis - {i} \<Longrightarrow> u \<bullet> k < x \<bullet> k"
       and xv: "\<And>k. k \<in> Basis - {i} \<Longrightarrow> x \<bullet> k < v \<bullet> k"
       and wx: "\<And>k. k \<in> Basis - {i} \<Longrightarrow> w \<bullet> k < x \<bullet> k"
       and xz: "\<And>k. k \<in> Basis - {i} \<Longrightarrow> x \<bullet> k < z \<bullet> k"
        using that K1 K2 i by (auto simp: extend_def box_ne_empty mem_box)
      have "box u v \<noteq> {}" "box w z \<noteq> {}"
        using cboxes interior_cbox by (auto simp: content_eq_0_interior dest: mt)
      then obtain q s
        where q: "\<And>k. k \<in> Basis \<Longrightarrow> w \<bullet> k < q \<bullet> k \<and> q \<bullet> k < z \<bullet> k"
          and s: "\<And>k. k \<in> Basis \<Longrightarrow> u \<bullet> k < s \<bullet> k \<and> s \<bullet> k < v \<bullet> k"
        by (meson all_not_in_conv mem_box(1))
      show ?thesis  using disj
      proof
        assume "\<forall>K\<in>\<D>. K \<inter> {x. x \<bullet> i = a \<bullet> i} \<noteq> {}"
        then have uva: "(cbox u v) \<inter> {x. x \<bullet> i = a \<bullet> i} \<noteq> {}"
             and  wza: "(cbox w z) \<inter> {x. x \<bullet> i = a \<bullet> i} \<noteq> {}"
          using cboxes by (auto simp: content_eq_0_interior)
        then obtain r t where "r \<bullet> i = a \<bullet> i" and r: "\<And>k. k \<in> Basis \<Longrightarrow> w \<bullet> k \<le> r \<bullet> k \<and> r \<bullet> k \<le> z \<bullet> k"
                        and "t \<bullet> i = a \<bullet> i" and t: "\<And>k. k \<in> Basis \<Longrightarrow> u \<bullet> k \<le> t \<bullet> k \<and> t \<bullet> k \<le> v \<bullet> k"
          by (fastforce simp: mem_box)
        have u: "u \<bullet> i < q \<bullet> i"
          using i K2(1) K2(3) \<open>t \<bullet> i = a \<bullet> i\<close> q s t [OF i] by (force simp: subset_box)
        have w: "w \<bullet> i < s \<bullet> i"
          using i K1(1) K1(3) \<open>r \<bullet> i = a \<bullet> i\<close> s r [OF i] by (force simp: subset_box)
        define \<xi> where "\<xi> \<equiv> (\<Sum>j \<in> Basis. if j = i then min (q \<bullet> i) (s \<bullet> i) *\<^sub>R i else (x \<bullet> j) *\<^sub>R j)"
        have [simp]: "\<xi> \<bullet> j = (if j = i then min (q \<bullet> j) (s \<bullet> j) else x \<bullet> j)" if "j \<in> Basis" for j
          unfolding \<xi>_def
          by (intro sum_if_inner that \<open>i \<in> Basis\<close>)
        show ?thesis
        proof (intro exI conjI)
          have "min (q \<bullet> i) (s \<bullet> i) < v \<bullet> i"
            using i s by fastforce
          with \<open>i \<in> Basis\<close> s u ux xv
          show "\<xi> \<in> box u v" 
            by (force simp: mem_box)
          have "min (q \<bullet> i) (s \<bullet> i) < z \<bullet> i"
            using i q by force
          with \<open>i \<in> Basis\<close> q w wx xz
          show "\<xi> \<in> box w z"
            by (force simp: mem_box)
        qed
      next
        assume "\<forall>K\<in>\<D>. K \<inter> {x. x \<bullet> i = b \<bullet> i} \<noteq> {}"
        then have uva: "(cbox u v) \<inter> {x. x \<bullet> i = b \<bullet> i} \<noteq> {}"
             and  wza: "(cbox w z) \<inter> {x. x \<bullet> i = b \<bullet> i} \<noteq> {}"
          using cboxes by (auto simp: content_eq_0_interior)
        then obtain r t where "r \<bullet> i = b \<bullet> i" and r: "\<And>k. k \<in> Basis \<Longrightarrow> w \<bullet> k \<le> r \<bullet> k \<and> r \<bullet> k \<le> z \<bullet> k"
                        and "t \<bullet> i = b \<bullet> i" and t: "\<And>k. k \<in> Basis \<Longrightarrow> u \<bullet> k \<le> t \<bullet> k \<and> t \<bullet> k \<le> v \<bullet> k"
          by (fastforce simp: mem_box)
        have z: "s \<bullet> i < z \<bullet> i"
          using K1(1) K1(3) \<open>r \<bullet> i = b \<bullet> i\<close> r [OF i] i s  by (force simp: subset_box)
        have v: "q \<bullet> i < v \<bullet> i"
          using K2(1) K2(3) \<open>t \<bullet> i = b \<bullet> i\<close> t [OF i] i q  by (force simp: subset_box)
        define \<xi> where "\<xi> \<equiv> (\<Sum>j \<in> Basis. if j = i then max (q \<bullet> i) (s \<bullet> i) *\<^sub>R i else (x \<bullet> j) *\<^sub>R j)"
        have [simp]: "\<xi> \<bullet> j = (if j = i then max (q \<bullet> j) (s \<bullet> j) else x \<bullet> j)" if "j \<in> Basis" for j
          unfolding \<xi>_def
          by (intro sum_if_inner that \<open>i \<in> Basis\<close>)
        show ?thesis
        proof (intro exI conjI)
          show "\<xi> \<in> box u v"
            using \<open>i \<in> Basis\<close> s by (force simp: mem_box ux v xv)
          show "\<xi> \<in> box w z"
            using \<open>i \<in> Basis\<close> q by (force simp: mem_box wx xz z)
        qed
      qed
    qed
    ultimately show ?thesis by auto
  qed
  define interv_diff where "interv_diff \<equiv> \<lambda>K. \<lambda>i::'a. interval_upperbound K \<bullet> i - interval_lowerbound K \<bullet> i"
  have "?lhs = (\<Sum>K\<in>\<D>. (b \<bullet> i - a \<bullet> i) * content K / (interv_diff K i))"
    by (simp add: sum_distrib_left interv_diff_def)
  also have "\<dots> = sum (content \<circ> extend) \<D>"
  proof (rule sum.cong [OF refl])
    fix K assume "K \<in> \<D>"
    then obtain u v where K: "K = cbox u v" "cbox u v \<noteq> {}" "K \<subseteq> cbox a b"
      using cbox_division_memE [OF _ div] div_subset_cbox by metis
    then have uv: "u \<bullet> i < v \<bullet> i"
      using mt [OF \<open>K \<in> \<D>\<close>] \<open>i \<in> Basis\<close> content_eq_0 by fastforce
    have "insert i (Basis \<inter> -{i}) = Basis"
      using \<open>i \<in> Basis\<close> by auto
    then have "(b \<bullet> i - a \<bullet> i) * content K / (interv_diff K i)
             = (b \<bullet> i - a \<bullet> i) * (\<Prod>i \<in> insert i (Basis \<inter> -{i}). v \<bullet> i - u \<bullet> i) / (interv_diff (cbox u v) i)"
      using K box_ne_empty(1) content_cbox by fastforce
    also have "... = (\<Prod>x\<in>Basis. if x = i then b \<bullet> x - a \<bullet> x
                      else (interval_upperbound (cbox u v) - interval_lowerbound (cbox u v)) \<bullet> x)"
      using \<open>i \<in> Basis\<close> K uv by (simp add: prod.If_cases interv_diff_def) (simp add: algebra_simps)
    also have "... = (\<Prod>k\<in>Basis.
                        (\<Sum>j\<in>Basis. if j = i then (b \<bullet> i - a \<bullet> i) *\<^sub>R i 
                                    else ((interval_upperbound (cbox u v) - interval_lowerbound (cbox u v)) \<bullet> j) *\<^sub>R j) \<bullet> k)"
      using \<open>i \<in> Basis\<close> by (subst prod.cong [OF refl sum_if_inner]; simp)
    also have "... = (\<Prod>k\<in>Basis.
                        (\<Sum>j\<in>Basis. if j = i then (b \<bullet> i) *\<^sub>R i else (interval_upperbound (cbox u v) \<bullet> j) *\<^sub>R j) \<bullet> k -
                        (\<Sum>j\<in>Basis. if j = i then (a \<bullet> i) *\<^sub>R i else (interval_lowerbound (cbox u v) \<bullet> j) *\<^sub>R j) \<bullet> k)"
      using \<open>i \<in> Basis\<close>
      by (intro prod.cong [OF refl]) (subst sum_if_inner; simp add: algebra_simps)+
    also have "... = (content \<circ> extend) K"
      using \<open>i \<in> Basis\<close> K box_ne_empty \<open>K \<in> \<D>\<close> extend(1) 
      by (auto simp add: extend_def content_cbox_if)
    finally show "(b \<bullet> i - a \<bullet> i) * content K / (interv_diff K i) = (content \<circ> extend) K" .
  qed
  also have "... = sum content (extend ` \<D>)"
  proof -
    have "\<lbrakk>K1 \<in> \<D>; K2 \<in> \<D>; K1 \<noteq> K2; extend K1 = extend K2\<rbrakk> \<Longrightarrow> content (extend K1) = 0" for K1 K2
      using int_extend_disjoint [of K1 K2] extend_def by (simp add: content_eq_0_interior)
    then show ?thesis
      by (simp add: comm_monoid_add_class.sum.reindex_nontrivial [OF \<open>finite \<D>\<close>])
  qed
  also have "... \<le> ?rhs"
  proof (rule subadditive_content_division)
    show "extend ` \<D> division_of \<Union> (extend ` \<D>)"
      using int_extend_disjoint  by (auto simp: division_of_def \<open>finite \<D>\<close> extend extend_cbox)
    show "\<Union> (extend ` \<D>) \<subseteq> cbox a b"
      using extend by fastforce
  qed
  finally show ?thesis .
qed


proposition sum_content_area_over_thin_division:
  assumes div: "\<D> division_of S" and S: "S \<subseteq> cbox a b" and i: "i \<in> Basis"
    and "a \<bullet> i \<le> c" "c \<le> b \<bullet> i"
    and nonmt: "\<And>K. K \<in> \<D> \<Longrightarrow> K \<inter> {x. x \<bullet> i = c} \<noteq> {}"
  shows "(b \<bullet> i - a \<bullet> i) * (\<Sum>K\<in>\<D>. content K / (interval_upperbound K \<bullet> i - interval_lowerbound K \<bullet> i))
          \<le> 2 * content(cbox a b)"
proof (cases "content(cbox a b) = 0")
  case True
  have "(\<Sum>K\<in>\<D>. content K / (interval_upperbound K \<bullet> i - interval_lowerbound K \<bullet> i)) = 0"
    using S div by (force intro!: sum.neutral content_0_subset [OF True])
  then show ?thesis
    by (auto simp: True)
next
  case False
  then have "content(cbox a b) > 0"
    using zero_less_measure_iff by blast
  then have "a \<bullet> i < b \<bullet> i" if "i \<in> Basis" for i
    using content_pos_lt_eq that by blast
  have "finite \<D>"
    using div by blast
  define Dlec where "Dlec \<equiv> {L \<in> (\<lambda>L. L \<inter> {x. x \<bullet> i \<le> c}) ` \<D>. content L \<noteq> 0}"
  define Dgec where "Dgec \<equiv> {L \<in> (\<lambda>L. L \<inter> {x. x \<bullet> i \<ge> c}) ` \<D>. content L \<noteq> 0}"
  define a' where "a' \<equiv> (\<Sum>j\<in>Basis. (if j = i then c else a \<bullet> j) *\<^sub>R j)"
  define b' where "b' \<equiv> (\<Sum>j\<in>Basis. (if j = i then c else b \<bullet> j) *\<^sub>R j)"
  define interv_diff where "interv_diff \<equiv> \<lambda>K. \<lambda>i::'a. interval_upperbound K \<bullet> i - interval_lowerbound K \<bullet> i"
  have Dlec_cbox: "\<And>K. K \<in> Dlec \<Longrightarrow> \<exists>a b. K = cbox a b"
    using interval_split [OF i] div by (fastforce simp: Dlec_def division_of_def)
  then have lec_is_cbox: "\<lbrakk>content (L \<inter> {x. x \<bullet> i \<le> c}) \<noteq> 0; L \<in> \<D>\<rbrakk> \<Longrightarrow> \<exists>a b. L \<inter> {x. x \<bullet> i \<le> c} = cbox a b" for L
    using Dlec_def by blast
  have Dgec_cbox: "\<And>K. K \<in> Dgec \<Longrightarrow> \<exists>a b. K = cbox a b"
    using interval_split [OF i] div by (fastforce simp: Dgec_def division_of_def)
  then have gec_is_cbox: "\<lbrakk>content (L \<inter> {x. x \<bullet> i \<ge> c}) \<noteq> 0; L \<in> \<D>\<rbrakk> \<Longrightarrow> \<exists>a b. L \<inter> {x. x \<bullet> i \<ge> c} = cbox a b" for L
    using Dgec_def by blast

  have zero_left: "\<And>x y. \<lbrakk>x \<in> \<D>; y \<in> \<D>; x \<noteq> y; x \<inter> {x. x \<bullet> i \<le> c} = y \<inter> {x. x \<bullet> i \<le> c}\<rbrakk>
           \<Longrightarrow> content (y \<inter> {x. x \<bullet> i \<le> c}) = 0"
    by (metis division_split_left_inj [OF div] lec_is_cbox content_eq_0_interior)
  have zero_right: "\<And>x y. \<lbrakk>x \<in> \<D>; y \<in> \<D>; x \<noteq> y; x \<inter> {x. c \<le> x \<bullet> i} = y \<inter> {x. c \<le> x \<bullet> i}\<rbrakk>
           \<Longrightarrow> content (y \<inter> {x. c \<le> x \<bullet> i}) = 0"
    by (metis division_split_right_inj [OF div] gec_is_cbox content_eq_0_interior)

  have "(b' \<bullet> i - a \<bullet> i) * (\<Sum>K\<in>Dlec. content K / interv_diff K i) \<le> content(cbox a b')"
    unfolding interv_diff_def
  proof (rule content_division_lemma1)
    show "Dlec division_of \<Union>Dlec"
      unfolding division_of_def
    proof (intro conjI ballI Dlec_cbox)
      show "\<And>K1 K2. \<lbrakk>K1 \<in> Dlec; K2 \<in> Dlec\<rbrakk> \<Longrightarrow> K1 \<noteq> K2 \<longrightarrow> interior K1 \<inter> interior K2 = {}"
        by (clarsimp simp: Dlec_def) (use div in auto)
    qed (use \<open>finite \<D>\<close> Dlec_def in auto)
    show "\<Union>Dlec \<subseteq> cbox a b'"
      using Dlec_def div S by (auto simp: b'_def division_of_def mem_box)
    show "(\<forall>K\<in>Dlec. K \<inter> {x. x \<bullet> i = a \<bullet> i} \<noteq> {}) \<or> (\<forall>K\<in>Dlec. K \<inter> {x. x \<bullet> i = b' \<bullet> i} \<noteq> {})"
      using nonmt by (fastforce simp: Dlec_def b'_def i)
  qed (use i Dlec_def in auto)
  moreover
  have "(\<Sum>K\<in>Dlec. content K / (interv_diff K i)) = (\<Sum>K\<in>(\<lambda>K. K \<inter> {x. x \<bullet> i \<le> c}) ` \<D>. content K / interv_diff K i)"
    unfolding Dlec_def using \<open>finite \<D>\<close> by (auto simp: sum.mono_neutral_left)
  moreover have "... =
        (\<Sum>K\<in>\<D>. ((\<lambda>K. content K / (interv_diff K i)) \<circ> ((\<lambda>K. K \<inter> {x. x \<bullet> i \<le> c}))) K)"
    by (simp add: zero_left sum.reindex_nontrivial [OF \<open>finite \<D>\<close>])
  moreover have "(b' \<bullet> i - a \<bullet> i) = (c - a \<bullet> i)"
    by (simp add: b'_def i)
  ultimately
  have lec: "(c - a \<bullet> i) * (\<Sum>K\<in>\<D>. ((\<lambda>K. content K / (interv_diff K i)) \<circ> ((\<lambda>K. K \<inter> {x. x \<bullet> i \<le> c}))) K)
             \<le> content(cbox a b')"
    by simp

  have "(b \<bullet> i - a' \<bullet> i) * (\<Sum>K\<in>Dgec. content K / (interv_diff K i)) \<le> content(cbox a' b)"
    unfolding interv_diff_def
  proof (rule content_division_lemma1)
    show "Dgec division_of \<Union>Dgec"
      unfolding division_of_def
    proof (intro conjI ballI Dgec_cbox)
      show "\<And>K1 K2. \<lbrakk>K1 \<in> Dgec; K2 \<in> Dgec\<rbrakk> \<Longrightarrow> K1 \<noteq> K2 \<longrightarrow> interior K1 \<inter> interior K2 = {}"
        by (clarsimp simp: Dgec_def) (use div in auto)
    qed (use \<open>finite \<D>\<close> Dgec_def in auto)
    show "\<Union>Dgec \<subseteq> cbox a' b"
      using Dgec_def div S by (auto simp: a'_def division_of_def mem_box)
    show "(\<forall>K\<in>Dgec. K \<inter> {x. x \<bullet> i = a' \<bullet> i} \<noteq> {}) \<or> (\<forall>K\<in>Dgec. K \<inter> {x. x \<bullet> i = b \<bullet> i} \<noteq> {})"
      using nonmt by (fastforce simp: Dgec_def a'_def i)
  qed (use i Dgec_def in auto)
  moreover
  have "(\<Sum>K\<in>Dgec. content K / (interv_diff K i)) = (\<Sum>K\<in>(\<lambda>K. K \<inter> {x. c \<le> x \<bullet> i}) ` \<D>.
       content K / interv_diff K i)"
    unfolding Dgec_def using \<open>finite \<D>\<close> by (auto simp: sum.mono_neutral_left)
  moreover have "\<dots> =
        (\<Sum>K\<in>\<D>. ((\<lambda>K. content K / (interv_diff K i)) \<circ> ((\<lambda>K. K \<inter> {x. x \<bullet> i \<ge> c}))) K)"
    by (simp add: zero_right sum.reindex_nontrivial [OF \<open>finite \<D>\<close>])
  moreover have "(b \<bullet> i - a' \<bullet> i) = (b \<bullet> i - c)"
    by (simp add: a'_def i)
  ultimately
  have gec: "(b \<bullet> i - c) * (\<Sum>K\<in>\<D>. ((\<lambda>K. content K / (interv_diff K i)) \<circ> ((\<lambda>K. K \<inter> {x. x \<bullet> i \<ge> c}))) K)
             \<le> content(cbox a' b)"
    by simp

  show ?thesis
  proof (cases "c = a \<bullet> i \<or> c = b \<bullet> i")
    case True
    then show ?thesis
    proof
      assume c: "c = a \<bullet> i"
      moreover
      have "(\<Sum>j\<in>Basis. (if j = i then a \<bullet> i else a \<bullet> j) *\<^sub>R j) = a"
        using euclidean_representation [of a] sum.cong [OF refl, of Basis "\<lambda>i. (a \<bullet> i) *\<^sub>R i"] by presburger
      ultimately have "a' = a"
        by (simp add: i a'_def cong: if_cong)
      then have "content (cbox a' b) \<le> 2 * content (cbox a b)"  by simp
      moreover
      have eq: "(\<Sum>K\<in>\<D>. content (K \<inter> {x. a \<bullet> i \<le> x \<bullet> i}) / interv_diff (K \<inter> {x. a \<bullet> i \<le> x \<bullet> i}) i)
              = (\<Sum>K\<in>\<D>. content K / interv_diff K i)"
        (is "sum ?f _ = sum ?g _")
      proof (rule sum.cong [OF refl])
        fix K assume "K \<in> \<D>"
        then have "a \<bullet> i \<le> x \<bullet> i" if "x \<in> K" for x
          by (metis S UnionI div division_ofD(6) i mem_box(2) subsetCE that)
        then have "K \<inter> {x. a \<bullet> i \<le> x \<bullet> i} = K"
          by blast
        then show "?f K = ?g K"
          by simp
      qed
      ultimately show ?thesis
        using gec c eq interv_diff_def by auto
    next
      assume c: "c = b \<bullet> i"
      moreover have "(\<Sum>j\<in>Basis. (if j = i then b \<bullet> i else b \<bullet> j) *\<^sub>R j) = b"
        using euclidean_representation [of b] sum.cong [OF refl, of Basis "\<lambda>i. (b \<bullet> i) *\<^sub>R i"] by presburger
      ultimately have "b' = b"
        by (simp add: i b'_def cong: if_cong)
      then have "content (cbox a b') \<le> 2 * content (cbox a b)"  by simp
      moreover
      have eq: "(\<Sum>K\<in>\<D>. content (K \<inter> {x. x \<bullet> i \<le> b \<bullet> i}) / interv_diff (K \<inter> {x. x \<bullet> i \<le> b \<bullet> i}) i)
              = (\<Sum>K\<in>\<D>. content K / interv_diff K i)"
               (is "sum ?f _ = sum ?g _")
      proof (rule sum.cong [OF refl])
        fix K assume "K \<in> \<D>"
        then have "x \<bullet> i \<le> b \<bullet> i" if "x \<in> K" for x
          by (metis S UnionI div division_ofD(6) i mem_box(2) subsetCE that)
        then have "K \<inter> {x. x \<bullet> i \<le> b \<bullet> i} = K"
          by blast
        then show "?f K = ?g K"
          by simp
      qed
      ultimately show ?thesis
        using lec c eq interv_diff_def by auto
    qed
  next
    case False
    have prod_if: "(\<Prod>k\<in>Basis \<inter> - {i}. f k) = (\<Prod>k\<in>Basis. f k) / f i" if "f i \<noteq> (0::real)" for f
    proof -
      have "f i * prod f (Basis \<inter> - {i}) = prod f Basis"
        using that mk_disjoint_insert [OF i]
        by (metis Int_insert_left_if0 finite_Basis finite_insert le_iff_inf order_refl prod.insert subset_Compl_singleton)
      then show ?thesis
        by (metis nonzero_mult_div_cancel_left that)
    qed
    have abc: "a \<bullet> i < c" "c < b \<bullet> i"
      using False assms by auto
    then have "(\<Sum>K\<in>\<D>. ((\<lambda>K. content K / (interv_diff K i)) \<circ> ((\<lambda>K. K \<inter> {x. x \<bullet> i \<le> c}))) K)
                  \<le> content(cbox a b') / (c - a \<bullet> i)"
              "(\<Sum>K\<in>\<D>. ((\<lambda>K. content K / (interv_diff K i)) \<circ> ((\<lambda>K. K \<inter> {x. x \<bullet> i \<ge> c}))) K)
                 \<le> content(cbox a' b) / (b \<bullet> i - c)"
      using lec gec by (simp_all add: field_split_simps)
    moreover
    have "(\<Sum>K\<in>\<D>. content K / (interv_diff K i))
          \<le> (\<Sum>K\<in>\<D>. ((\<lambda>K. content K / (interv_diff K i)) \<circ> ((\<lambda>K. K \<inter> {x. x \<bullet> i \<le> c}))) K) +
            (\<Sum>K\<in>\<D>. ((\<lambda>K. content K / (interv_diff K i)) \<circ> ((\<lambda>K. K \<inter> {x. x \<bullet> i \<ge> c}))) K)"
           (is "?lhs \<le> ?rhs")
    proof -
      have "?lhs \<le>
            (\<Sum>K\<in>\<D>. ((\<lambda>K. content K / (interv_diff K i)) \<circ> ((\<lambda>K. K \<inter> {x. x \<bullet> i \<le> c}))) K +
                    ((\<lambda>K. content K / (interv_diff K i)) \<circ> ((\<lambda>K. K \<inter> {x. x \<bullet> i \<ge> c}))) K)"
            (is "sum ?f _ \<le> sum ?g _")
      proof (rule sum_mono)
        fix K assume "K \<in> \<D>"
        then obtain u v where uv: "K = cbox u v"
          using div by blast
        obtain u' v' where uv': "cbox u v \<inter> {x. x \<bullet> i \<le> c} = cbox u v'"
                                "cbox u v \<inter> {x. c \<le> x \<bullet> i} = cbox u' v"
                                "\<And>k. k \<in> Basis \<Longrightarrow> u' \<bullet> k = (if k = i then max (u \<bullet> i) c else u \<bullet> k)"
                                "\<And>k. k \<in> Basis \<Longrightarrow> v' \<bullet> k = (if k = i then min (v \<bullet> i) c else v \<bullet> k)"
          using i by (auto simp: interval_split)
        have *: "\<lbrakk>content (cbox u v') = 0; content (cbox u' v) = 0\<rbrakk> \<Longrightarrow> content (cbox u v) = 0"
                "content (cbox u' v) \<noteq> 0 \<Longrightarrow> content (cbox u v) \<noteq> 0"
                "content (cbox u v') \<noteq> 0 \<Longrightarrow> content (cbox u v) \<noteq> 0"
          using i uv uv' by (auto simp: content_eq_0 le_max_iff_disj min_le_iff_disj split: if_split_asm intro: order_trans)
        have uniq: "\<And>j. \<lbrakk>j \<in> Basis; \<not> u \<bullet> j \<le> v \<bullet> j\<rbrakk> \<Longrightarrow> j = i"
          by (metis \<open>K \<in> \<D>\<close> box_ne_empty(1) div division_of_def uv)
        show "?f K \<le> ?g K"
          using i uv uv'  by (auto simp add: interv_diff_def lemma0 dest: uniq * intro!: prod_nonneg)
      qed
      also have "... = ?rhs"
        by (simp add: sum.distrib)
      finally show ?thesis .
    qed
    moreover have "content (cbox a b') / (c - a \<bullet> i) = content (cbox a b) / (b \<bullet> i - a \<bullet> i)"
      using i abc
      apply (simp add: field_simps a'_def b'_def measure_lborel_cbox_eq inner_diff)
      apply (auto simp: if_distrib if_distrib [of "\<lambda>f. f x" for x] prod.If_cases [of Basis "\<lambda>x. x = i", simplified] prod_if field_simps)
      done
    moreover have "content (cbox a' b) / (b \<bullet> i - c) = content (cbox a b) / (b \<bullet> i - a \<bullet> i)"
      using i abc
      apply (simp add: field_simps a'_def b'_def measure_lborel_cbox_eq inner_diff)
      apply (auto simp: if_distrib prod.If_cases [of Basis "\<lambda>x. x = i", simplified] prod_if field_simps)
      done
    ultimately
    have "(\<Sum>K\<in>\<D>. content K / (interv_diff K i)) \<le> 2 * content (cbox a b) / (b \<bullet> i - a \<bullet> i)"
      by linarith
    then show ?thesis
      using abc interv_diff_def by (simp add: field_split_simps)
  qed
qed


proposition bounded_equiintegral_over_thin_tagged_partial_division:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes F: "F equiintegrable_on cbox a b" and f: "f \<in> F" and "0 < \<epsilon>"
      and norm_f: "\<And>h x. \<lbrakk>h \<in> F; x \<in> cbox a b\<rbrakk> \<Longrightarrow> norm(h x) \<le> norm(f x)"
  obtains \<gamma> where "gauge \<gamma>"
             "\<And>c i S h. \<lbrakk>c \<in> cbox a b; i \<in> Basis; S tagged_partial_division_of cbox a b;
                         \<gamma> fine S; h \<in> F; \<And>x K. (x,K) \<in> S \<Longrightarrow> (K \<inter> {x. x \<bullet> i = c \<bullet> i} \<noteq> {})\<rbrakk>
                        \<Longrightarrow> (\<Sum>(x,K) \<in> S. norm (integral K h)) < \<epsilon>"
proof (cases "content(cbox a b) = 0")
  case True
  show ?thesis
  proof
    show "gauge (\<lambda>x. ball x 1)"
      by (simp add: gauge_trivial)
    show "(\<Sum>(x,K) \<in> S. norm (integral K h)) < \<epsilon>"
         if "S tagged_partial_division_of cbox a b" "(\<lambda>x. ball x 1) fine S" for S and h:: "'a \<Rightarrow> 'b"
    proof -
      have "(\<Sum>(x,K) \<in> S. norm (integral K h)) = 0"
          using that True content_0_subset
          by (fastforce simp: tagged_partial_division_of_def intro: sum.neutral)
      with \<open>0 < \<epsilon>\<close> show ?thesis
        by simp
    qed
  qed
next
  case False
  then have contab_gt0:  "content(cbox a b) > 0"
    by (simp add: zero_less_measure_iff)
  then have a_less_b: "\<And>i. i \<in> Basis \<Longrightarrow> a\<bullet>i < b\<bullet>i"
    by (auto simp: content_pos_lt_eq)
  obtain \<gamma>0 where "gauge \<gamma>0"
            and \<gamma>0: "\<And>S h. \<lbrakk>S tagged_partial_division_of cbox a b; \<gamma>0 fine S; h \<in> F\<rbrakk>
                           \<Longrightarrow> (\<Sum>(x,K) \<in> S. norm (content K *\<^sub>R h x - integral K h)) < \<epsilon>/2"
  proof -
    obtain \<gamma> where "gauge \<gamma>"
               and \<gamma>: "\<And>f \<D>. \<lbrakk>f \<in> F; \<D> tagged_division_of cbox a b; \<gamma> fine \<D>\<rbrakk>
                              \<Longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral (cbox a b) f)
                                  < \<epsilon>/(5 * (Suc DIM('b)))"
    proof -
      have e5: "\<epsilon>/(5 * (Suc DIM('b))) > 0"
        using \<open>\<epsilon> > 0\<close> by auto
      then show ?thesis
        using F that by (auto simp: equiintegrable_on_def)
    qed
    show ?thesis
    proof
      show "gauge \<gamma>"
        by (rule \<open>gauge \<gamma>\<close>)
      show "(\<Sum>(x,K) \<in> S. norm (content K *\<^sub>R h x - integral K h)) < \<epsilon>/2"
           if "S tagged_partial_division_of cbox a b" "\<gamma> fine S" "h \<in> F" for S h
      proof -
        have "(\<Sum>(x,K) \<in> S. norm (content K *\<^sub>R h x - integral K h)) \<le> 2 * real DIM('b) * (\<epsilon>/(5 * Suc DIM('b)))"
        proof (rule Henstock_lemma_part2 [of h a b])
          show "h integrable_on cbox a b"
            using that F equiintegrable_on_def by metis
          show "gauge \<gamma>"
            by (rule \<open>gauge \<gamma>\<close>)
        qed (use that \<open>\<epsilon> > 0\<close> \<gamma> in auto)
        also have "... < \<epsilon>/2"
          using \<open>\<epsilon> > 0\<close> by (simp add: divide_simps)
        finally show ?thesis .
      qed
    qed
  qed
  define \<gamma> where "\<gamma> \<equiv> \<lambda>x. \<gamma>0 x \<inter>
                          ball x ((\<epsilon>/8 / (norm(f x) + 1)) * (INF m\<in>Basis. b \<bullet> m - a \<bullet> m) / content(cbox a b))"
  define interv_diff where "interv_diff \<equiv> \<lambda>K. \<lambda>i::'a. interval_upperbound K \<bullet> i - interval_lowerbound K \<bullet> i"
  have "8 * content (cbox a b) + norm (f x) * (8 * content (cbox a b)) > 0" for x
    by (metis add.right_neutral add_pos_pos contab_gt0 mult_pos_pos mult_zero_left norm_eq_zero zero_less_norm_iff zero_less_numeral)
  then have "gauge (\<lambda>x. ball x
                    (\<epsilon> * (INF m\<in>Basis. b \<bullet> m - a \<bullet> m) / ((8 * norm (f x) + 8) * content (cbox a b))))"
    using \<open>0 < content (cbox a b)\<close> \<open>0 < \<epsilon>\<close> a_less_b 
    by (auto simp add: gauge_def field_split_simps add_nonneg_eq_0_iff finite_less_Inf_iff)
  then have "gauge \<gamma>"
    unfolding \<gamma>_def using \<open>gauge \<gamma>0\<close> gauge_Int by auto
  moreover
  have "(\<Sum>(x,K) \<in> S. norm (integral K h)) < \<epsilon>"
       if "c \<in> cbox a b" "i \<in> Basis" and S: "S tagged_partial_division_of cbox a b"
          and "\<gamma> fine S" "h \<in> F" and ne: "\<And>x K. (x,K) \<in> S \<Longrightarrow> K \<inter> {x. x \<bullet> i = c \<bullet> i} \<noteq> {}" for c i S h
  proof -
    have "cbox c b \<subseteq> cbox a b"
      by (meson mem_box(2) order_refl subset_box(1) that(1))
    have "finite S"
      using S unfolding tagged_partial_division_of_def by blast
    have "\<gamma>0 fine S" and fineS:
         "(\<lambda>x. ball x (\<epsilon> * (INF m\<in>Basis. b \<bullet> m - a \<bullet> m) / ((8 * norm (f x) + 8) * content (cbox a b)))) fine S"
      using \<open>\<gamma> fine S\<close> by (auto simp: \<gamma>_def fine_Int)
    then have "(\<Sum>(x,K) \<in> S. norm (content K *\<^sub>R h x - integral K h)) < \<epsilon>/2"
      by (intro \<gamma>0 that fineS)
    moreover have "(\<Sum>(x,K) \<in> S. norm (integral K h) - norm (content K *\<^sub>R h x - integral K h)) \<le> \<epsilon>/2"
    proof -
      have "(\<Sum>(x,K) \<in> S. norm (integral K h) - norm (content K *\<^sub>R h x - integral K h))
            \<le> (\<Sum>(x,K) \<in> S. norm (content K *\<^sub>R h x))"
      proof (clarify intro!: sum_mono)
        fix x K
        assume xK: "(x,K) \<in> S"
        have "norm (integral K h) - norm (content K *\<^sub>R h x - integral K h) \<le> norm (integral K h - (integral K h - content K *\<^sub>R h x))"
          by (metis norm_minus_commute norm_triangle_ineq2)
        also have "... \<le> norm (content K *\<^sub>R h x)"
          by simp
        finally show "norm (integral K h) - norm (content K *\<^sub>R h x - integral K h) \<le> norm (content K *\<^sub>R h x)" .
      qed
      also have "... \<le> (\<Sum>(x,K) \<in> S. \<epsilon>/4 * (b \<bullet> i - a \<bullet> i) / content (cbox a b) * content K / interv_diff K i)"
      proof (clarify intro!: sum_mono)
        fix x K
        assume xK: "(x,K) \<in> S"
        then have x: "x \<in> cbox a b"
          using S unfolding tagged_partial_division_of_def by (meson subset_iff)
        show "norm (content K *\<^sub>R h x) \<le> \<epsilon>/4 * (b \<bullet> i - a \<bullet> i) / content (cbox a b) * content K / interv_diff K i"
        proof (cases "content K = 0")
          case True
          then show ?thesis by simp
        next
          case False
          then have Kgt0: "content K > 0"
            using zero_less_measure_iff by blast
          moreover
          obtain u v where uv: "K = cbox u v"
            using S \<open>(x,K) \<in> S\<close> unfolding tagged_partial_division_of_def by blast
          then have u_less_v: "\<And>i. i \<in> Basis \<Longrightarrow> u \<bullet> i < v \<bullet> i"
            using content_pos_lt_eq uv Kgt0 by blast
          then have dist_uv: "dist u v > 0"
            using that by auto
          ultimately have "norm (h x) \<le> (\<epsilon> * (b \<bullet> i - a \<bullet> i)) / (4 * content (cbox a b) * interv_diff K i)"
          proof -
            have "dist x u < \<epsilon> * (INF m\<in>Basis. b \<bullet> m - a \<bullet> m) / (4 * (norm (f x) + 1) * content (cbox a b)) / 2"
                 "dist x v < \<epsilon> * (INF m\<in>Basis. b \<bullet> m - a \<bullet> m) / (4 * (norm (f x) + 1) * content (cbox a b)) / 2"
              using fineS u_less_v uv xK
              by (force simp: fine_def mem_box field_simps dest!: bspec)+
            moreover have "\<epsilon> * (INF m\<in>Basis. b \<bullet> m - a \<bullet> m) / (4 * (norm (f x) + 1) * content (cbox a b)) / 2
                  \<le> \<epsilon> * (b \<bullet> i - a \<bullet> i) / (4 * (norm (f x) + 1) * content (cbox a b)) / 2"
            proof (intro mult_left_mono divide_right_mono)
              show "(INF m\<in>Basis. b \<bullet> m - a \<bullet> m) \<le> b \<bullet> i - a \<bullet> i"
                using \<open>i \<in> Basis\<close> by (auto intro!: cInf_le_finite)
            qed (use \<open>0 < \<epsilon>\<close> in auto)
            ultimately
            have "dist x u < \<epsilon> * (b \<bullet> i - a \<bullet> i) / (4 * (norm (f x) + 1) * content (cbox a b)) / 2"
                 "dist x v < \<epsilon> * (b \<bullet> i - a \<bullet> i) / (4 * (norm (f x) + 1) * content (cbox a b)) / 2"
              by linarith+
            then have duv: "dist u v < \<epsilon> * (b \<bullet> i - a \<bullet> i) / (4 * (norm (f x) + 1) * content (cbox a b))"
              using dist_triangle_half_r by blast
            have uvi: "\<bar>v \<bullet> i - u \<bullet> i\<bar> \<le> norm (v - u)"
              by (metis inner_commute inner_diff_right \<open>i \<in> Basis\<close> Basis_le_norm)
            have "norm (h x) \<le> norm (f x)"
              using x that by (auto simp: norm_f)
            also have "... < (norm (f x) + 1)"
              by simp
            also have "... < \<epsilon> * (b \<bullet> i - a \<bullet> i) / dist u v / (4 * content (cbox a b))"
            proof -
              have "0 < norm (f x) + 1"
                by (simp add: add.commute add_pos_nonneg)
              then show ?thesis
                using duv dist_uv contab_gt0
                by (simp only: mult_ac divide_simps) auto
            qed
            also have "... = \<epsilon> * (b \<bullet> i - a \<bullet> i) / norm (v - u) / (4 * content (cbox a b))"
              by (simp add: dist_norm norm_minus_commute)
            also have "... \<le> \<epsilon> * (b \<bullet> i - a \<bullet> i) / \<bar>v \<bullet> i - u \<bullet> i\<bar> / (4 * content (cbox a b))"
            proof (intro mult_right_mono divide_left_mono divide_right_mono uvi)
              show "norm (v - u) * \<bar>v \<bullet> i - u \<bullet> i\<bar> > 0"
                using u_less_v [OF \<open>i \<in> Basis\<close>] 
                by (auto simp: less_eq_real_def zero_less_mult_iff that)
              show "\<epsilon> * (b \<bullet> i - a \<bullet> i) \<ge> 0"
                using a_less_b \<open>0 < \<epsilon>\<close> \<open>i \<in> Basis\<close> by force
            qed auto
            also have "... = \<epsilon> * (b \<bullet> i - a \<bullet> i) / (4 * content (cbox a b) * interv_diff K i)"
              using uv False that(2) u_less_v interv_diff_def by fastforce
            finally show ?thesis by simp
          qed
          with Kgt0 have "norm (content K *\<^sub>R h x) \<le> content K * ((\<epsilon>/4 * (b \<bullet> i - a \<bullet> i) / content (cbox a b)) / interv_diff K i)"
            using mult_left_mono by fastforce
          also have "... = \<epsilon>/4 * (b \<bullet> i - a \<bullet> i) / content (cbox a b) * content K / interv_diff K i"
            by (simp add: field_split_simps)
          finally show ?thesis .
        qed
      qed
      also have "... = (\<Sum>K\<in>snd ` S. \<epsilon>/4 * (b \<bullet> i - a \<bullet> i) / content (cbox a b) * content K / interv_diff K i)"
        unfolding interv_diff_def
        apply (rule sum.over_tagged_division_lemma [OF tagged_partial_division_of_Union_self [OF S]])
        apply (simp add: box_eq_empty(1) content_eq_0)
        done
      also have "... = \<epsilon>/2 * ((b \<bullet> i - a \<bullet> i) / (2 * content (cbox a b)) * (\<Sum>K\<in>snd ` S. content K / interv_diff K i))"
        by (simp add: interv_diff_def sum_distrib_left mult.assoc)
      also have "... \<le> (\<epsilon>/2) * 1"
      proof (rule mult_left_mono)
        have "(b \<bullet> i - a \<bullet> i) * (\<Sum>K\<in>snd ` S. content K / interv_diff K i) \<le> 2 * content (cbox a b)"
          unfolding interv_diff_def
        proof (rule sum_content_area_over_thin_division)
          show "snd ` S division_of \<Union>(snd ` S)"
            by (auto intro: S tagged_partial_division_of_Union_self division_of_tagged_division)
          show "\<Union>(snd ` S) \<subseteq> cbox a b"
            using S unfolding tagged_partial_division_of_def by force
          show "a \<bullet> i \<le> c \<bullet> i" "c \<bullet> i \<le> b \<bullet> i"
            using mem_box(2) that by blast+
        qed (use that in auto)
        then show "(b \<bullet> i - a \<bullet> i) / (2 * content (cbox a b)) * (\<Sum>K\<in>snd ` S. content K / interv_diff K i) \<le> 1"
          by (simp add: contab_gt0)
      qed (use \<open>0 < \<epsilon>\<close> in auto)
      finally show ?thesis by simp
    qed
    then have "(\<Sum>(x,K) \<in> S. norm (integral K h)) - (\<Sum>(x,K) \<in> S. norm (content K *\<^sub>R h x - integral K h)) \<le> \<epsilon>/2"
      by (simp add: Groups_Big.sum_subtractf [symmetric])
    ultimately show "(\<Sum>(x,K) \<in> S. norm (integral K h)) < \<epsilon>"
      by linarith
  qed
  ultimately show ?thesis using that by auto
qed



proposition equiintegrable_halfspace_restrictions_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes F: "F equiintegrable_on cbox a b" and f: "f \<in> F"
    and norm_f: "\<And>h x. \<lbrakk>h \<in> F; x \<in> cbox a b\<rbrakk> \<Longrightarrow> norm(h x) \<le> norm(f x)"
  shows "(\<Union>i \<in> Basis. \<Union>c. \<Union>h \<in> F. {(\<lambda>x. if x \<bullet> i \<le> c then h x else 0)})
         equiintegrable_on cbox a b"
proof (cases "content(cbox a b) = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "content(cbox a b) > 0"
    using zero_less_measure_iff by blast
  then have "a \<bullet> i < b \<bullet> i" if "i \<in> Basis" for i
    using content_pos_lt_eq that by blast
  have int_F: "f integrable_on cbox a b" if "f \<in> F" for f
    using F that by (simp add: equiintegrable_on_def)
  let ?CI = "\<lambda>K h x. content K *\<^sub>R h x - integral K h"
  show ?thesis
    unfolding equiintegrable_on_def
  proof (intro conjI; clarify)
    show int_lec: "\<lbrakk>i \<in> Basis; h \<in> F\<rbrakk> \<Longrightarrow> (\<lambda>x. if x \<bullet> i \<le> c then h x else 0) integrable_on cbox a b" for i c h
      using integrable_restrict_Int [of "{x. x \<bullet> i \<le> c}" h]
      by (simp add: inf_commute int_F integrable_split(1))
    show "\<exists>\<gamma>. gauge \<gamma> \<and>
              (\<forall>f T. f \<in> (\<Union>i\<in>Basis. \<Union>c. \<Union>h\<in>F. {\<lambda>x. if x \<bullet> i \<le> c then h x else 0}) \<and>
                     T tagged_division_of cbox a b \<and> \<gamma> fine T \<longrightarrow>
                     norm ((\<Sum>(x,K) \<in> T. content K *\<^sub>R f x) - integral (cbox a b) f) < \<epsilon>)"
      if "\<epsilon> > 0" for \<epsilon>
    proof -
      obtain \<gamma>0 where "gauge \<gamma>0" and \<gamma>0:
        "\<And>c i S h. \<lbrakk>c \<in> cbox a b; i \<in> Basis; S tagged_partial_division_of cbox a b;
                        \<gamma>0 fine S; h \<in> F; \<And>x K. (x,K) \<in> S \<Longrightarrow> (K \<inter> {x. x \<bullet> i = c \<bullet> i} \<noteq> {})\<rbrakk>
                       \<Longrightarrow> (\<Sum>(x,K) \<in> S. norm (integral K h)) < \<epsilon>/12"
      proof (rule bounded_equiintegral_over_thin_tagged_partial_division [OF F f, of \<open>\<epsilon>/12\<close>])
        show "\<And>h x. \<lbrakk>h \<in> F; x \<in> cbox a b\<rbrakk> \<Longrightarrow> norm (h x) \<le> norm (f x)"
          by (auto simp: norm_f)
      qed (use \<open>\<epsilon> > 0\<close> in auto)
      obtain \<gamma>1 where "gauge \<gamma>1"
        and \<gamma>1: "\<And>h T. \<lbrakk>h \<in> F; T tagged_division_of cbox a b; \<gamma>1 fine T\<rbrakk>
                              \<Longrightarrow> norm ((\<Sum>(x,K) \<in> T. content K *\<^sub>R h x) - integral (cbox a b) h)
                                  < \<epsilon>/(7 * (Suc DIM('b)))"
      proof -
        have e5: "\<epsilon>/(7 * (Suc DIM('b))) > 0"
          using \<open>\<epsilon> > 0\<close> by auto
        then show ?thesis
          using F that by (auto simp: equiintegrable_on_def)
      qed
      have h_less3: "(\<Sum>(x,K) \<in> T. norm (?CI K h x)) < \<epsilon>/3"
        if "T tagged_partial_division_of cbox a b" "\<gamma>1 fine T" "h \<in> F" for T h
      proof -
        have "(\<Sum>(x,K) \<in> T. norm (?CI K h x)) \<le> 2 * real DIM('b) * (\<epsilon>/(7 * Suc DIM('b)))"
        proof (rule Henstock_lemma_part2 [of h a b])
          show "h integrable_on cbox a b"
            using that F equiintegrable_on_def by metis
        qed (use that \<open>\<epsilon> > 0\<close> \<open>gauge \<gamma>1\<close> \<gamma>1 in auto)
        also have "... < \<epsilon>/3"
          using \<open>\<epsilon> > 0\<close> by (simp add: divide_simps)
        finally show ?thesis .
      qed
      have *: "norm ((\<Sum>(x,K) \<in> T. content K *\<^sub>R f x) - integral (cbox a b) f) < \<epsilon>"
                if f: "f = (\<lambda>x. if x \<bullet> i \<le> c then h x else 0)"
                and T: "T tagged_division_of cbox a b"
                and fine: "(\<lambda>x. \<gamma>0 x \<inter> \<gamma>1 x) fine T" and "i \<in> Basis" "h \<in> F" for f T i c h
      proof (cases "a \<bullet> i \<le> c \<and> c \<le> b \<bullet> i")
        case True
        have "finite T"
          using T by blast
        define T' where "T' \<equiv> {(x,K) \<in> T. K \<inter> {x. x \<bullet> i \<le> c} \<noteq> {}}"
        then have "T' \<subseteq> T"
          by auto
        then have "finite T'"
          using \<open>finite T\<close> infinite_super by blast
        have T'_tagged: "T' tagged_partial_division_of cbox a b"
          by (meson T \<open>T' \<subseteq> T\<close> tagged_division_of_def tagged_partial_division_subset)
        have fine': "\<gamma>0 fine T'" "\<gamma>1 fine T'"
          using \<open>T' \<subseteq> T\<close> fine_Int fine_subset fine by blast+
        have int_KK': "(\<Sum>(x,K) \<in> T. integral K f) = (\<Sum>(x,K) \<in> T'. integral K f)"
        proof (rule sum.mono_neutral_right [OF \<open>finite T\<close> \<open>T' \<subseteq> T\<close>])
          show "\<forall>i \<in> T - T'. (case i of (x, K) \<Rightarrow> integral K f) = 0"
            using f \<open>finite T\<close> \<open>T' \<subseteq> T\<close> integral_restrict_Int [of _ "{x. x \<bullet> i \<le> c}" h]
            by (auto simp: T'_def Int_commute)
        qed
        have "(\<Sum>(x,K) \<in> T. content K *\<^sub>R f x) = (\<Sum>(x,K) \<in> T'. content K *\<^sub>R f x)"
        proof (rule sum.mono_neutral_right [OF \<open>finite T\<close> \<open>T' \<subseteq> T\<close>])
          show "\<forall>i \<in> T - T'. (case i of (x, K) \<Rightarrow> content K *\<^sub>R f x) = 0"
            using T f \<open>finite T\<close> \<open>T' \<subseteq> T\<close> by (force simp: T'_def)
        qed
        moreover have "norm ((\<Sum>(x,K) \<in> T'. content K *\<^sub>R f x) - integral (cbox a b) f) < \<epsilon>"
        proof -
          have *: "norm y < \<epsilon>" if "norm x < \<epsilon>/3" "norm(x - y) \<le> 2 * \<epsilon>/3" for x y::'b
          proof -
            have "norm y \<le> norm x + norm(x - y)"
              by (metis norm_minus_commute norm_triangle_sub)
            also have "\<dots> < \<epsilon>/3 + 2*\<epsilon>/3"
              using that by linarith
            also have "... = \<epsilon>"
              by simp
            finally show ?thesis .
          qed
          have "norm (\<Sum>(x,K) \<in> T'. ?CI K h x)
                \<le> (\<Sum>(x,K) \<in> T'. norm (?CI K h x))"
            by (simp add: norm_sum split_def)
          also have "... < \<epsilon>/3"
            by (intro h_less3 T'_tagged fine' that)
          finally have "norm (\<Sum>(x,K) \<in> T'. ?CI K h x) < \<epsilon>/3" .
          moreover have "integral (cbox a b) f = (\<Sum>(x,K) \<in> T. integral K f)"
            using int_lec that by (auto simp: integral_combine_tagged_division_topdown)
          moreover have "norm (\<Sum>(x,K) \<in> T'. ?CI K h x - ?CI K f x)
                \<le> 2*\<epsilon>/3"
          proof -
            define T'' where "T'' \<equiv> {(x,K) \<in> T'. \<not> (K \<subseteq> {x. x \<bullet> i \<le> c})}"
            then have "T'' \<subseteq> T'"
              by auto
            then have "finite T''"
              using \<open>finite T'\<close> infinite_super by blast
            have T''_tagged: "T'' tagged_partial_division_of cbox a b"
              using T'_tagged \<open>T'' \<subseteq> T'\<close> tagged_partial_division_subset by blast
            have fine'': "\<gamma>0 fine T''" "\<gamma>1 fine T''"
              using \<open>T'' \<subseteq> T'\<close> fine' by (blast intro: fine_subset)+
            have "(\<Sum>(x,K) \<in> T'. ?CI K h x - ?CI K f x)
                = (\<Sum>(x,K) \<in> T''. ?CI K h x - ?CI K f x)"
            proof (clarify intro!: sum.mono_neutral_right [OF \<open>finite T'\<close> \<open>T'' \<subseteq> T'\<close>])
              fix x K
              assume "(x,K) \<in> T'" "(x,K) \<notin> T''"
              then have "x \<in> K" "x \<bullet> i \<le> c" "{x. x \<bullet> i \<le> c} \<inter> K = K"
                using T''_def T'_tagged tagged_partial_division_of_def by blast+
              then show "?CI K h x - ?CI K f x = 0"
                using integral_restrict_Int [of _ "{x. x \<bullet> i \<le> c}" h] by (auto simp: f)
            qed
            moreover have "norm (\<Sum>(x,K) \<in> T''. ?CI K h x - ?CI K f x) \<le> 2*\<epsilon>/3"
            proof -
              define A where "A \<equiv> {(x,K) \<in> T''. x \<bullet> i \<le> c}"
              define B where "B \<equiv> {(x,K) \<in> T''. x \<bullet> i > c}"
              then have "A \<subseteq> T''" "B \<subseteq> T''" and disj: "A \<inter> B = {}" and T''_eq: "T'' = A \<union> B"
                by (auto simp: A_def B_def)
              then have "finite A" "finite B"
                using \<open>finite T''\<close>  by (auto intro: finite_subset)
              have A_tagged: "A tagged_partial_division_of cbox a b"
                using T''_tagged \<open>A \<subseteq> T''\<close> tagged_partial_division_subset by blast
              have fineA: "\<gamma>0 fine A" "\<gamma>1 fine A"
                using \<open>A \<subseteq> T''\<close> fine'' by (blast intro: fine_subset)+
              have B_tagged: "B tagged_partial_division_of cbox a b"
                using T''_tagged \<open>B \<subseteq> T''\<close> tagged_partial_division_subset by blast
              have fineB: "\<gamma>0 fine B" "\<gamma>1 fine B"
                using \<open>B \<subseteq> T''\<close> fine'' by (blast intro: fine_subset)+
              have "norm (\<Sum>(x,K) \<in> T''. ?CI K h x - ?CI K f x)
                          \<le> (\<Sum>(x,K) \<in> T''. norm (?CI K h x - ?CI K f x))"
                by (simp add: norm_sum split_def)
              also have "... = (\<Sum>(x,K) \<in> A. norm (?CI K h x - ?CI K f x)) +
                               (\<Sum>(x,K) \<in> B. norm (?CI K h x - ?CI K f x))"
                by (simp add: sum.union_disjoint T''_eq disj \<open>finite A\<close> \<open>finite B\<close>)
              also have "... = (\<Sum>(x,K) \<in> A. norm (integral K h - integral K f)) +
                               (\<Sum>(x,K) \<in> B. norm (?CI K h x + integral K f))"
                by (auto simp: A_def B_def f norm_minus_commute intro!: sum.cong arg_cong2 [where f= "(+)"])
              also have "... \<le> (\<Sum>(x,K)\<in>A. norm (integral K h)) +
                                 (\<Sum>(x,K)\<in>(\<lambda>(x,K). (x,K \<inter> {x. x \<bullet> i \<le> c})) ` A. norm (integral K h))
                             + ((\<Sum>(x,K)\<in>B. norm (?CI K h x)) +
                                (\<Sum>(x,K)\<in>B. norm (integral K h)) +
                                  (\<Sum>(x,K)\<in>(\<lambda>(x,K). (x,K \<inter> {x. c \<le> x \<bullet> i})) ` B. norm (integral K h)))"
              proof (rule add_mono)
                show "(\<Sum>(x,K)\<in>A. norm (integral K h - integral K f))
                        \<le> (\<Sum>(x,K)\<in>A. norm (integral K h)) +
                           (\<Sum>(x,K)\<in>(\<lambda>(x,K). (x,K \<inter> {x. x \<bullet> i \<le> c})) ` A.
                              norm (integral K h))"
                proof (subst sum.reindex_nontrivial [OF \<open>finite A\<close>], clarsimp)
                  fix x K L
                  assume "(x,K) \<in> A" "(x,L) \<in> A"
                    and int_ne0: "integral (L \<inter> {x. x \<bullet> i \<le> c}) h \<noteq> 0"
                    and eq: "K \<inter> {x. x \<bullet> i \<le> c} = L \<inter> {x. x \<bullet> i \<le> c}"
                  have False if "K \<noteq> L"
                  proof -
                    obtain u v where uv: "L = cbox u v"
                      using T'_tagged \<open>(x, L) \<in> A\<close> \<open>A \<subseteq> T''\<close> \<open>T'' \<subseteq> T'\<close> by (blast dest: tagged_partial_division_ofD)
                    have "interior (K \<inter> {x. x \<bullet> i \<le> c}) = {}"
                    proof (rule tagged_division_split_left_inj [OF _ \<open>(x,K) \<in> A\<close> \<open>(x,L) \<in> A\<close>])
                      show "A tagged_division_of \<Union>(snd ` A)"
                        using A_tagged tagged_partial_division_of_Union_self by auto
                      show "K \<inter> {x. x \<bullet> i \<le> c} = L \<inter> {x. x \<bullet> i \<le> c}"
                        using eq \<open>i \<in> Basis\<close> by auto
                    qed (use that in auto)
                    then show False
                      using interval_split [OF \<open>i \<in> Basis\<close>] int_ne0 content_eq_0_interior eq uv by fastforce
                  qed
                  then show "K = L" by blast
                next
                  show "(\<Sum>(x,K) \<in> A. norm (integral K h - integral K f))
                          \<le> (\<Sum>(x,K) \<in> A. norm (integral K h)) +
                             sum ((\<lambda>(x,K). norm (integral K h)) \<circ> (\<lambda>(x,K). (x,K \<inter> {x. x \<bullet> i \<le> c}))) A"
                    using integral_restrict_Int [of _ "{x. x \<bullet> i \<le> c}" h] f
                    by (auto simp: Int_commute A_def [symmetric] sum.distrib [symmetric] intro!: sum_mono norm_triangle_ineq4)
                qed
              next
                show "(\<Sum>(x,K)\<in>B. norm (?CI K h x + integral K f))
                      \<le> (\<Sum>(x,K)\<in>B. norm (?CI K h x)) + (\<Sum>(x,K)\<in>B. norm (integral K h)) +
                         (\<Sum>(x,K)\<in>(\<lambda>(x,K). (x,K \<inter> {x. c \<le> x \<bullet> i})) ` B. norm (integral K h))"
                proof (subst sum.reindex_nontrivial [OF \<open>finite B\<close>], clarsimp)
                  fix x K L
                  assume "(x,K) \<in> B" "(x,L) \<in> B"
                    and int_ne0: "integral (L \<inter> {x. c \<le> x \<bullet> i}) h \<noteq> 0"
                    and eq: "K \<inter> {x. c \<le> x \<bullet> i} = L \<inter> {x. c \<le> x \<bullet> i}"
                  have False if "K \<noteq> L"
                  proof -
                    obtain u v where uv: "L = cbox u v"
                      using T'_tagged \<open>(x, L) \<in> B\<close> \<open>B \<subseteq> T''\<close> \<open>T'' \<subseteq> T'\<close> by (blast dest: tagged_partial_division_ofD)
                    have "interior (K \<inter> {x. c \<le> x \<bullet> i}) = {}"
                    proof (rule tagged_division_split_right_inj [OF _ \<open>(x,K) \<in> B\<close> \<open>(x,L) \<in> B\<close>])
                      show "B tagged_division_of \<Union>(snd ` B)"
                        using B_tagged tagged_partial_division_of_Union_self by auto
                      show "K \<inter> {x. c \<le> x \<bullet> i} = L \<inter> {x. c \<le> x \<bullet> i}"
                        using eq \<open>i \<in> Basis\<close> by auto
                    qed (use that in auto)
                    then show False
                      using interval_split [OF \<open>i \<in> Basis\<close>] int_ne0
                        content_eq_0_interior eq uv by fastforce
                  qed
                  then show "K = L" by blast
                next
                  show "(\<Sum>(x,K) \<in> B. norm (?CI K h x + integral K f))
                        \<le> (\<Sum>(x,K) \<in> B. norm (?CI K h x)) +
                           (\<Sum>(x,K) \<in> B. norm (integral K h)) + sum ((\<lambda>(x,K). norm (integral K h)) \<circ> (\<lambda>(x,K). (x,K \<inter> {x. c \<le> x \<bullet> i}))) B"
                  proof (clarsimp simp: B_def [symmetric] sum.distrib [symmetric] intro!: sum_mono)
                    fix x K
                    assume "(x,K) \<in> B"
                    have *: "i = i1 + i2 \<Longrightarrow> norm(c + i1) \<le> norm c + norm i + norm(i2)"
                      for i::'b and c i1 i2
                      by (metis add.commute add.left_commute add_diff_cancel_right' dual_order.refl norm_add_rule_thm norm_triangle_ineq4)
                    obtain u v where uv: "K = cbox u v"
                      using T'_tagged \<open>(x,K) \<in> B\<close> \<open>B \<subseteq> T''\<close> \<open>T'' \<subseteq> T'\<close> by (blast dest: tagged_partial_division_ofD)
                    have huv: "h integrable_on cbox u v"
                    proof (rule integrable_on_subcbox)
                      show "cbox u v \<subseteq> cbox a b"
                        using B_tagged \<open>(x,K) \<in> B\<close> uv by (blast dest: tagged_partial_division_ofD)
                      show "h integrable_on cbox a b"
                        by (simp add: int_F \<open>h \<in> F\<close>)
                    qed
                    have "integral K h = integral K f + integral (K \<inter> {x. c \<le> x \<bullet> i}) h"
                      using integral_restrict_Int [of _ "{x. x \<bullet> i \<le> c}" h] f uv \<open>i \<in> Basis\<close>
                      by (simp add: Int_commute integral_split [OF huv \<open>i \<in> Basis\<close>])
                  then show "norm (?CI K h x + integral K f)
                             \<le> norm (?CI K h x) + norm (integral K h) + norm (integral (K \<inter> {x. c \<le> x \<bullet> i}) h)"
                    by (rule *)
                qed
              qed
            qed
            also have "... \<le> 2*\<epsilon>/3"
            proof -
              have overlap: "K \<inter> {x. x \<bullet> i = c} \<noteq> {}" if "(x,K) \<in> T''" for x K
              proof -
                obtain y y' where y: "y' \<in> K" "c < y' \<bullet> i" "y \<in> K" "y \<bullet> i \<le> c"
                  using that  T''_def T'_def \<open>(x,K) \<in> T''\<close> by fastforce
                obtain u v where uv: "K = cbox u v"
                  using T''_tagged \<open>(x,K) \<in> T''\<close> by (blast dest: tagged_partial_division_ofD)
                then have "connected K"
                  by (simp add: is_interval_connected)
                then have "(\<exists>z \<in> K. z \<bullet> i = c)"
                  using y connected_ivt_component by fastforce
                then show ?thesis
                  by fastforce
              qed
              have **: "\<lbrakk>x < \<epsilon>/12; y < \<epsilon>/12; z \<le> \<epsilon>/2\<rbrakk> \<Longrightarrow> x + y + z \<le> 2 * \<epsilon>/3" for x y z
                by auto
              show ?thesis
              proof (rule **)
                have cb_ab: "(\<Sum>j \<in> Basis. if j = i then c *\<^sub>R i else (a \<bullet> j) *\<^sub>R j) \<in> cbox a b"
                  using \<open>i \<in> Basis\<close> True \<open>\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i < b \<bullet> i\<close>
                  by (force simp add: mem_box sum_if_inner [where f = "\<lambda>j. c"])
                show "(\<Sum>(x,K) \<in> A. norm (integral K h)) < \<epsilon>/12"
                  using \<open>i \<in> Basis\<close> \<open>A \<subseteq> T''\<close> overlap
                  by (force simp add: sum_if_inner [where f = "\<lambda>j. c"] 
                       intro!: \<gamma>0 [OF cb_ab \<open>i \<in> Basis\<close> A_tagged fineA(1) \<open>h \<in> F\<close>])
                let ?F = "\<lambda>(x,K). (x, K \<inter> {x. x \<bullet> i \<le> c})"
                have 1: "?F ` A tagged_partial_division_of cbox a b"
                  unfolding tagged_partial_division_of_def
                proof (intro conjI strip)
                  show "\<And>x K. (x, K) \<in> ?F ` A \<Longrightarrow> \<exists>a b. K = cbox a b"
                    using A_tagged interval_split(1) [OF \<open>i \<in> Basis\<close>, of _ _ c]
                    by (force dest: tagged_partial_division_ofD(4))
                  show "\<And>x K. (x, K) \<in> ?F ` A \<Longrightarrow> x \<in> K"
                    using A_def A_tagged by (fastforce dest: tagged_partial_division_ofD)
                qed (use A_tagged in \<open>fastforce dest: tagged_partial_division_ofD\<close>)+
                have 2: "\<gamma>0 fine (\<lambda>(x,K). (x,K \<inter> {x. x \<bullet> i \<le> c})) ` A"
                  using fineA(1) fine_def by fastforce
                show "(\<Sum>(x,K) \<in> (\<lambda>(x,K). (x,K \<inter> {x. x \<bullet> i \<le> c})) ` A. norm (integral K h)) < \<epsilon>/12"
                  using \<open>i \<in> Basis\<close> \<open>A \<subseteq> T''\<close> overlap
                  by (force simp add: sum_if_inner [where f = "\<lambda>j. c"] 
                       intro!: \<gamma>0 [OF cb_ab \<open>i \<in> Basis\<close> 1 2 \<open>h \<in> F\<close>])
                have *: "\<lbrakk>x < \<epsilon>/3; y < \<epsilon>/12; z < \<epsilon>/12\<rbrakk> \<Longrightarrow> x + y + z \<le> \<epsilon>/2" for x y z
                  by auto
                show "(\<Sum>(x,K) \<in> B. norm (?CI K h x)) +
                      (\<Sum>(x,K) \<in> B. norm (integral K h)) +
                      (\<Sum>(x,K) \<in> (\<lambda>(x,K). (x,K \<inter> {x. c \<le> x \<bullet> i})) ` B. norm (integral K h))
                      \<le> \<epsilon>/2"
                proof (rule *)
                  show "(\<Sum>(x,K) \<in> B. norm (?CI K h x)) < \<epsilon>/3"
                    by (intro h_less3 B_tagged fineB that)
                  show "(\<Sum>(x,K) \<in> B. norm (integral K h)) < \<epsilon>/12"
                  using \<open>i \<in> Basis\<close> \<open>B \<subseteq> T''\<close> overlap
                  by (force simp add: sum_if_inner [where f = "\<lambda>j. c"] 
                       intro!: \<gamma>0 [OF cb_ab \<open>i \<in> Basis\<close> B_tagged fineB(1) \<open>h \<in> F\<close>])
                  let ?F = "\<lambda>(x,K). (x, K \<inter> {x. c \<le> x \<bullet> i})"
                  have 1: "?F ` B tagged_partial_division_of cbox a b"
                    unfolding tagged_partial_division_of_def
                  proof (intro conjI strip)
                    show "\<And>x K. (x, K) \<in> ?F ` B \<Longrightarrow> \<exists>a b. K = cbox a b"
                      using B_tagged interval_split(2) [OF \<open>i \<in> Basis\<close>, of _ _ c]
                      by (force dest: tagged_partial_division_ofD(4))
                    show "\<And>x K. (x, K) \<in> ?F ` B \<Longrightarrow> x \<in> K"
                      using B_def B_tagged by (fastforce dest: tagged_partial_division_ofD)
                  qed (use B_tagged in \<open>fastforce dest: tagged_partial_division_ofD\<close>)+
                  have 2: "\<gamma>0 fine (\<lambda>(x,K). (x,K \<inter> {x. c \<le> x \<bullet> i})) ` B"
                    using fineB(1) fine_def by fastforce
                  show "(\<Sum>(x,K) \<in> (\<lambda>(x,K). (x,K \<inter> {x. c \<le> x \<bullet> i})) ` B. norm (integral K h)) < \<epsilon>/12"
                  using \<open>i \<in> Basis\<close> \<open>A \<subseteq> T''\<close> overlap
                  by (force simp add: B_def sum_if_inner [where f = "\<lambda>j. c"] 
                       intro!: \<gamma>0 [OF cb_ab \<open>i \<in> Basis\<close> 1 2 \<open>h \<in> F\<close>])
                qed
              qed
            qed
            finally show ?thesis .
          qed
          ultimately show ?thesis by metis
        qed
        ultimately show ?thesis
          by (simp add: sum_subtractf [symmetric] int_KK' *)
      qed
        ultimately show ?thesis by metis
      next
        case False
        then consider "c < a \<bullet> i" | "b \<bullet> i < c"
          by auto
        then show ?thesis
        proof cases
          case 1
          then have f0: "f x = 0" if "x \<in> cbox a b" for x
            using that f \<open>i \<in> Basis\<close> mem_box(2) by force
          then have int_f0: "integral (cbox a b) f = 0"
            by (simp add: integral_cong)
          have f0_tag: "f x = 0" if "(x,K) \<in> T" for x K
            using T f0 that by (meson tag_in_interval)
          then have "(\<Sum>(x,K) \<in> T. content K *\<^sub>R f x) = 0"
            by (metis (mono_tags, lifting) real_vector.scale_eq_0_iff split_conv sum.neutral surj_pair)
          then show ?thesis
            using \<open>0 < \<epsilon>\<close> by (simp add: int_f0)
      next
          case 2
          then have fh: "f x = h x" if "x \<in> cbox a b" for x
            using that f \<open>i \<in> Basis\<close> mem_box(2) by force
          then have int_f: "integral (cbox a b) f = integral (cbox a b) h"
            using integral_cong by blast
          have fh_tag: "f x = h x" if "(x,K) \<in> T" for x K
            using T fh that by (meson tag_in_interval)
          then have fh: "(\<Sum>(x,K) \<in> T. content K *\<^sub>R f x) = (\<Sum>(x,K) \<in> T. content K *\<^sub>R h x)"
            by (metis (mono_tags, lifting) split_cong sum.cong)
          show ?thesis
            unfolding fh int_f
          proof (rule less_trans [OF \<gamma>1])
            show "\<gamma>1 fine T"
              by (meson fine fine_Int)
            show "\<epsilon> / (7 * Suc DIM('b)) < \<epsilon>"
              using \<open>0 < \<epsilon>\<close> by (force simp: divide_simps)+
          qed (use that in auto)
        qed
      qed
      have  "gauge (\<lambda>x. \<gamma>0 x \<inter> \<gamma>1 x)"
        by (simp add: \<open>gauge \<gamma>0\<close> \<open>gauge \<gamma>1\<close> gauge_Int)
      then show ?thesis
        by (auto intro: *)
    qed
  qed
qed


corollary equiintegrable_halfspace_restrictions_ge:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes F: "F equiintegrable_on cbox a b" and f: "f \<in> F"
    and norm_f: "\<And>h x. \<lbrakk>h \<in> F; x \<in> cbox a b\<rbrakk> \<Longrightarrow> norm(h x) \<le> norm(f x)"
  shows "(\<Union>i \<in> Basis. \<Union>c. \<Union>h \<in> F. {(\<lambda>x. if x \<bullet> i \<ge> c then h x else 0)})
         equiintegrable_on cbox a b"
proof -
  have *: "(\<Union>i\<in>Basis. \<Union>c. \<Union>h\<in>(\<lambda>f. f \<circ> uminus) ` F. {\<lambda>x. if x \<bullet> i \<le> c then h x else 0})
           equiintegrable_on  cbox (- b) (- a)"
  proof (rule equiintegrable_halfspace_restrictions_le)
    show "(\<lambda>f. f \<circ> uminus) ` F equiintegrable_on cbox (- b) (- a)"
      using F equiintegrable_reflect by blast
    show "f \<circ> uminus \<in> (\<lambda>f. f \<circ> uminus) ` F"
      using f by auto
    show "\<And>h x. \<lbrakk>h \<in> (\<lambda>f. f \<circ> uminus) ` F; x \<in> cbox (- b) (- a)\<rbrakk> \<Longrightarrow> norm (h x) \<le> norm ((f \<circ> uminus) x)"
      using f unfolding comp_def image_iff
      by (metis (no_types, lifting) equation_minus_iff imageE norm_f uminus_interval_vector)
  qed
  have eq: "(\<lambda>f. f \<circ> uminus) `
            (\<Union>i\<in>Basis. \<Union>c. \<Union>h\<in>F. {\<lambda>x. if x \<bullet> i \<le> c then (h \<circ> uminus) x else 0}) =
            (\<Union>i\<in>Basis. \<Union>c. \<Union>h\<in>F. {\<lambda>x. if c \<le> x \<bullet> i then h x else 0})"   (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
      using minus_le_iff by fastforce
    show "?rhs \<subseteq> ?lhs"
    apply clarsimp
    apply (rule_tac x="\<lambda>x. if c \<le> (-x) \<bullet> i then h(-x) else 0" in image_eqI)
      using le_minus_iff by fastforce+
  qed
  show ?thesis
    using equiintegrable_reflect [OF *] by (auto simp: eq)
qed

corollary equiintegrable_halfspace_restrictions_lt:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes F: "F equiintegrable_on cbox a b" and f: "f \<in> F"
    and norm_f: "\<And>h x. \<lbrakk>h \<in> F; x \<in> cbox a b\<rbrakk> \<Longrightarrow> norm(h x) \<le> norm(f x)"
  shows "(\<Union>i \<in> Basis. \<Union>c. \<Union>h \<in> F. {(\<lambda>x. if x \<bullet> i < c then h x else 0)}) equiintegrable_on cbox a b"
         (is "?G equiintegrable_on cbox a b")
proof -
  have *: "(\<Union>i\<in>Basis. \<Union>c. \<Union>h\<in>F. {\<lambda>x. if c \<le> x \<bullet> i then h x else 0}) equiintegrable_on cbox a b"
    using equiintegrable_halfspace_restrictions_ge [OF F f] norm_f by auto
  have "(\<lambda>x. if x \<bullet> i < c then h x else 0) = (\<lambda>x. h x - (if c \<le> x \<bullet> i then h x else 0))"
    if "i \<in> Basis" "h \<in> F" for i c h
    using that by force
  then show ?thesis
    by (blast intro: equiintegrable_on_subset [OF equiintegrable_diff [OF F *]])
qed

corollary equiintegrable_halfspace_restrictions_gt:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes F: "F equiintegrable_on cbox a b" and f: "f \<in> F"
    and norm_f: "\<And>h x. \<lbrakk>h \<in> F; x \<in> cbox a b\<rbrakk> \<Longrightarrow> norm(h x) \<le> norm(f x)"
  shows "(\<Union>i \<in> Basis. \<Union>c. \<Union>h \<in> F. {(\<lambda>x. if x \<bullet> i > c then h x else 0)}) equiintegrable_on cbox a b"
         (is "?G equiintegrable_on cbox a b")
proof -
  have *: "(\<Union>i\<in>Basis. \<Union>c. \<Union>h\<in>F. {\<lambda>x. if c \<ge> x \<bullet> i then h x else 0}) equiintegrable_on cbox a b"
    using equiintegrable_halfspace_restrictions_le [OF F f] norm_f by auto
  have "(\<lambda>x. if x \<bullet> i > c then h x else 0) = (\<lambda>x. h x - (if c \<ge> x \<bullet> i then h x else 0))"
    if "i \<in> Basis" "h \<in> F" for i c h
    using that by force
  then show ?thesis
    by (blast intro: equiintegrable_on_subset [OF equiintegrable_diff [OF F *]])
qed

proposition equiintegrable_closed_interval_restrictions:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "f integrable_on cbox a b"
  shows "(\<Union>c d. {(\<lambda>x. if x \<in> cbox c d then f x else 0)}) equiintegrable_on cbox a b"
proof -
  let ?g = "\<lambda>B c d x. if \<forall>i\<in>B. c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i then f x else 0"
  have *: "insert f (\<Union>c d. {?g B c d}) equiintegrable_on cbox a b" if "B \<subseteq> Basis" for B
  proof -
    have "finite B"
      using finite_Basis finite_subset \<open>B \<subseteq> Basis\<close> by blast
    then show ?thesis using \<open>B \<subseteq> Basis\<close>
    proof (induction B)
      case empty
      with f show ?case by auto
    next
      case (insert i B)
      then have "i \<in> Basis" "B \<subseteq> Basis"
        by auto
      have *: "norm (h x) \<le> norm (f x)"
        if "h \<in> insert f (\<Union>c d. {?g B c d})" "x \<in> cbox a b" for h x
        using that by auto
      define F where "F \<equiv> (\<Union>i\<in>Basis.
                \<Union>\<xi>. \<Union>h\<in>insert f (\<Union>i\<in>Basis. \<Union>\<psi>. \<Union>h\<in>insert f (\<Union>c d. {?g B c d}). {\<lambda>x. if x \<bullet> i \<le> \<psi> then h x else 0}).
                {\<lambda>x. if \<xi> \<le> x \<bullet> i then h x else 0})"
      show ?case
      proof (rule equiintegrable_on_subset)
        have "F equiintegrable_on cbox a b"
          unfolding F_def
        proof (rule equiintegrable_halfspace_restrictions_ge)
          show "insert f (\<Union>i\<in>Basis. \<Union>\<xi>. \<Union>h\<in>insert f (\<Union>c d. {?g B c d}).
              {\<lambda>x. if x \<bullet> i \<le> \<xi> then h x else 0}) equiintegrable_on cbox a b"
            by (intro * f equiintegrable_on_insert equiintegrable_halfspace_restrictions_le [OF insert.IH insertI1] \<open>B \<subseteq> Basis\<close>)
          show "norm(h x) \<le> norm(f x)"
            if "h \<in> insert f (\<Union>i\<in>Basis. \<Union>\<xi>. \<Union>h\<in>insert f (\<Union>c d. {?g B c d}). {\<lambda>x. if x \<bullet> i \<le> \<xi> then h x else 0})"
              "x \<in> cbox a b" for h x
            using that by auto
        qed auto
        then show "insert f F
             equiintegrable_on cbox a b"
          by (blast intro: f equiintegrable_on_insert)
        show "insert f (\<Union>c d. {\<lambda>x. if \<forall>j\<in>insert i B. c \<bullet> j \<le> x \<bullet> j \<and> x \<bullet> j \<le> d \<bullet> j then f x else 0})
            \<subseteq> insert f F"
          using \<open>i \<in> Basis\<close> 
          apply clarify
          apply (simp add: F_def)
          apply (drule_tac x=i in bspec, assumption)
          apply (drule_tac x="c \<bullet> i" in spec, clarify)
          apply (drule_tac x=i in bspec, assumption)
          apply (drule_tac x="d \<bullet> i" in spec)
          apply (clarsimp simp: fun_eq_iff)
          apply (drule_tac x=c in spec)
          apply (drule_tac x=d in spec)
          apply (simp split: if_split_asm)
          done
      qed
    qed
  qed
  show ?thesis
    by (rule equiintegrable_on_subset [OF * [OF subset_refl]]) (auto simp: mem_box)
qed


subsection\<open>Continuity of the indefinite integral\<close>

proposition indefinite_integral_continuous:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes int_f: "f integrable_on cbox a b"
      and c: "c \<in> cbox a b" and d: "d \<in> cbox a b" "0 < \<epsilon>"
  obtains \<delta> where "0 < \<delta>"
              "\<And>c' d'. \<lbrakk>c' \<in> cbox a b; d' \<in> cbox a b; norm(c' - c) \<le> \<delta>; norm(d' - d) \<le> \<delta>\<rbrakk>
                        \<Longrightarrow> norm(integral(cbox c' d') f - integral(cbox c d) f) < \<epsilon>"
proof -
  { assume "\<exists>c' d'. c' \<in> cbox a b \<and> d' \<in> cbox a b \<and> norm(c' - c) \<le> \<delta> \<and> norm(d' - d) \<le> \<delta> \<and>
                    norm(integral(cbox c' d') f - integral(cbox c d) f) \<ge> \<epsilon>"
                    (is "\<exists>c' d'. ?\<Phi> c' d' \<delta>") if "0 < \<delta>" for \<delta>
    then have "\<exists>c' d'. ?\<Phi> c' d' (1 / Suc n)" for n
      by simp
    then obtain u v where "\<And>n. ?\<Phi> (u n) (v n) (1 / Suc n)"
      by metis
    then have u: "u n \<in> cbox a b" and norm_u: "norm(u n - c) \<le> 1 / Suc n"
         and  v: "v n \<in> cbox a b" and norm_v: "norm(v n - d) \<le> 1 / Suc n"
         and \<epsilon>: "\<epsilon> \<le> norm (integral (cbox (u n) (v n)) f - integral (cbox c d) f)" for n
      by blast+
    then have False
    proof -
      have uvn: "cbox (u n) (v n) \<subseteq> cbox a b" for n
        by (meson u v mem_box(2) subset_box(1))
      define S where "S \<equiv> \<Union>i \<in> Basis. {x. x \<bullet> i = c \<bullet> i} \<union> {x. x \<bullet> i = d \<bullet> i}"
      have "negligible S"
        unfolding S_def by force
      then have int_f': "(\<lambda>x. if x \<in> S then 0 else f x) integrable_on cbox a b"
        by (force intro: integrable_spike assms)
      have get_n: "\<exists>n. \<forall>m\<ge>n. x \<in> cbox (u m) (v m) \<longleftrightarrow> x \<in> cbox c d" if x: "x \<notin> S" for x
      proof -
        define \<epsilon> where "\<epsilon> \<equiv> Min ((\<lambda>i. min \<bar>x \<bullet> i - c \<bullet> i\<bar> \<bar>x \<bullet> i - d \<bullet> i\<bar>) ` Basis)"
        have "\<epsilon> > 0"
          using \<open>x \<notin> S\<close> by (auto simp: S_def \<epsilon>_def)
        then obtain n where "n \<noteq> 0" and n: "1 / (real n) < \<epsilon>"
          by (metis inverse_eq_divide real_arch_inverse)
        have emin: "\<epsilon> \<le> min \<bar>x \<bullet> i - c \<bullet> i\<bar> \<bar>x \<bullet> i - d \<bullet> i\<bar>" if "i \<in> Basis" for i
          unfolding \<epsilon>_def 
          by (meson Min.coboundedI euclidean_space_class.finite_Basis finite_imageI image_iff that)
        have "1 / real (Suc n) < \<epsilon>"
          using n \<open>n \<noteq> 0\<close> \<open>\<epsilon> > 0\<close> by (simp add: field_simps)
        have "x \<in> cbox (u m) (v m) \<longleftrightarrow> x \<in> cbox c d" if "m \<ge> n" for m
        proof -
          have *: "\<lbrakk>\<bar>u - c\<bar> \<le> n; \<bar>v - d\<bar> \<le> n; N < \<bar>x - c\<bar>; N < \<bar>x - d\<bar>; n \<le> N\<rbrakk>
                   \<Longrightarrow> u \<le> x \<and> x \<le> v \<longleftrightarrow> c \<le> x \<and> x \<le> d" for N n u v c d and x::real
            by linarith
          have "(u m \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> v m \<bullet> i) = (c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i)"
            if "i \<in> Basis" for i
          proof (rule *)
            show "\<bar>u m \<bullet> i - c \<bullet> i\<bar> \<le> 1 / Suc m"
              using norm_u [of m]
              by (metis (full_types) order_trans Basis_le_norm inner_commute inner_diff_right that)
            show "\<bar>v m \<bullet> i - d \<bullet> i\<bar> \<le> 1 / real (Suc m)"
              using norm_v [of m]
              by (metis (full_types) order_trans Basis_le_norm inner_commute inner_diff_right that)
            show "1/n < \<bar>x \<bullet> i - c \<bullet> i\<bar>" "1/n < \<bar>x \<bullet> i - d \<bullet> i\<bar>"
              using n \<open>n \<noteq> 0\<close> emin [OF \<open>i \<in> Basis\<close>]
              by (simp_all add: inverse_eq_divide)
            show "1 / real (Suc m) \<le> 1 / real n"
              using \<open>n \<noteq> 0\<close> \<open>m \<ge> n\<close> by (simp add: field_split_simps)
          qed
          then show ?thesis by (simp add: mem_box)
        qed
        then show ?thesis by blast
      qed
      have 1: "range (\<lambda>n x. if x \<in> cbox (u n) (v n) then if x \<in> S then 0 else f x else 0) equiintegrable_on cbox a b"
        by (blast intro: equiintegrable_on_subset [OF equiintegrable_closed_interval_restrictions [OF int_f']])
      have 2: "(\<lambda>n. if x \<in> cbox (u n) (v n) then if x \<in> S then 0 else f x else 0)
               \<longlonglongrightarrow> (if x \<in> cbox c d then if x \<in> S then 0 else f x else 0)" for x
        by (fastforce simp: dest: get_n intro: tendsto_eventually eventually_sequentiallyI)
      have [simp]: "cbox c d \<inter> cbox a b = cbox c d"
        using c d by (force simp: mem_box)
      have [simp]: "cbox (u n) (v n) \<inter> cbox a b = cbox (u n) (v n)" for n
        using u v by (fastforce simp: mem_box intro: order.trans)
      have "\<And>y A. y \<in> A - S \<Longrightarrow> f y = (\<lambda>x. if x \<in> S then 0 else f x) y"
        by simp
      then have "\<And>A. integral A (\<lambda>x. if x \<in> S then 0 else f (x)) = integral A (\<lambda>x. f (x))"
        by (blast intro: integral_spike [OF \<open>negligible S\<close>])
      moreover
      obtain N where "dist (integral (cbox (u N) (v N)) (\<lambda>x. if x \<in> S then 0 else f x))
                           (integral (cbox c d) (\<lambda>x. if x \<in> S then 0 else f x)) < \<epsilon>"
        using equiintegrable_limit [OF 1 2] \<open>0 < \<epsilon>\<close> by (force simp: integral_restrict_Int lim_sequentially)
      ultimately have "dist (integral (cbox (u N) (v N)) f) (integral (cbox c d) f) < \<epsilon>"
        by simp
      then show False
        by (metis dist_norm not_le \<epsilon>)
    qed
  }
  then show ?thesis
    by (meson not_le that)
qed

corollary indefinite_integral_uniformly_continuous:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f integrable_on cbox a b"
  shows "uniformly_continuous_on (cbox (Pair a a) (Pair b b)) (\<lambda>y. integral (cbox (fst y) (snd y)) f)"
proof -
  show ?thesis
  proof (rule compact_uniformly_continuous, clarsimp simp add: continuous_on_iff)
    fix c d and \<epsilon>::real
    assume c: "c \<in> cbox a b" and d: "d \<in> cbox a b" and "0 < \<epsilon>"
    obtain \<delta> where "0 < \<delta>" and \<delta>:
              "\<And>c' d'. \<lbrakk>c' \<in> cbox a b; d' \<in> cbox a b; norm(c' - c) \<le> \<delta>; norm(d' - d) \<le> \<delta>\<rbrakk>
                                  \<Longrightarrow> norm(integral(cbox c' d') f -
                                           integral(cbox c d) f) < \<epsilon>"
      using indefinite_integral_continuous \<open>0 < \<epsilon>\<close> assms c d by blast
    show "\<exists>\<delta> > 0. \<forall>x' \<in> cbox (a, a) (b, b).
                   dist x' (c, d) < \<delta> \<longrightarrow>
                   dist (integral (cbox (fst x') (snd x')) f)
                        (integral (cbox c d) f)
                   < \<epsilon>"
      using \<open>0 < \<delta>\<close>
      by (force simp: dist_norm intro: \<delta> order_trans [OF norm_fst_le] order_trans [OF norm_snd_le] less_imp_le)
  qed auto
qed


corollary bounded_integrals_over_subintervals:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f integrable_on cbox a b"
  shows "bounded {integral (cbox c d) f |c d. cbox c d \<subseteq> cbox a b}"
proof -
  have "bounded ((\<lambda>y. integral (cbox (fst y) (snd y)) f) ` cbox (a, a) (b, b))"
       (is "bounded ?I")
    by (blast intro: bounded_cbox bounded_uniformly_continuous_image indefinite_integral_uniformly_continuous [OF assms])
  then obtain B where "B > 0" and B: "\<And>x. x \<in> ?I \<Longrightarrow> norm x \<le> B"
    by (auto simp: bounded_pos)
  have "norm x \<le> B" if "x = integral (cbox c d) f" "cbox c d \<subseteq> cbox a b" for x c d
  proof (cases "cbox c d = {}")
    case True
    with \<open>0 < B\<close> that show ?thesis by auto
  next
    case False
    then have "\<exists>x \<in> cbox (a,a) (b,b). integral (cbox c d) f = integral (cbox (fst x) (snd x)) f"
      using that by (metis cbox_Pair_iff interval_subset_is_interval is_interval_cbox prod.sel)
    then show ?thesis
      using B that(1) by blast
  qed
  then show ?thesis
    by (blast intro: boundedI)
qed


text\<open>An existence theorem for "improper" integrals.
Hake's theorem implies that if the integrals over subintervals have a limit, the integral exists.
We only need to assume that the integrals are bounded, and we get absolute integrability,
but we also need a (rather weak) bound assumption on the function.\<close>

theorem absolutely_integrable_improper:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'N::euclidean_space"
  assumes int_f: "\<And>c d. cbox c d \<subseteq> box a b \<Longrightarrow> f integrable_on cbox c d"
      and bo: "bounded {integral (cbox c d) f |c d. cbox c d \<subseteq> box a b}"
      and absi: "\<And>i. i \<in> Basis
          \<Longrightarrow> \<exists>g. g absolutely_integrable_on cbox a b \<and>
                  ((\<forall>x \<in> cbox a b. f x \<bullet> i \<le> g x) \<or> (\<forall>x \<in> cbox a b. f x \<bullet> i \<ge> g x))"
      shows "f absolutely_integrable_on cbox a b"
proof (cases "content(cbox a b) = 0")
  case True
  then show ?thesis
    by auto
next
  case False
  then have pos: "content(cbox a b) > 0"
    using zero_less_measure_iff by blast
  show ?thesis
    unfolding absolutely_integrable_componentwise_iff [where f = f]
  proof
    fix j::'N
    assume "j \<in> Basis"
    then obtain g where absint_g: "g absolutely_integrable_on cbox a b"
                    and g: "(\<forall>x \<in> cbox a b. f x \<bullet> j \<le> g x) \<or> (\<forall>x \<in> cbox a b. f x \<bullet> j \<ge> g x)"
      using absi by blast
    have int_gab: "g integrable_on cbox a b"
      using absint_g set_lebesgue_integral_eq_integral(1) by blast
    define \<alpha> where "\<alpha> \<equiv> \<lambda>k. a + (b - a) /\<^sub>R real k"
    define \<beta> where "\<beta> \<equiv> \<lambda>k. b - (b - a) /\<^sub>R real k"
    define I where "I \<equiv> \<lambda>k. cbox (\<alpha> k) (\<beta> k)"
    have ISuc_box: "I (Suc n) \<subseteq> box a b" for n
      using pos unfolding I_def
      by (intro subset_box_imp) (auto simp: \<alpha>_def \<beta>_def content_pos_lt_eq algebra_simps)
    have ISucSuc: "I (Suc n) \<subseteq> I (Suc (Suc n))" for n
    proof -
      have "\<And>i. i \<in> Basis
                 \<Longrightarrow> a \<bullet> i / Suc n + b \<bullet> i / (real n + 2)  \<le> b \<bullet> i / Suc n + a \<bullet> i / (real n + 2)"
        using pos 
        by (simp add: content_pos_lt_eq divide_simps) (auto simp: algebra_simps)
      then show ?thesis
        unfolding I_def
        by (intro subset_box_imp) (auto simp: algebra_simps inverse_eq_divide \<alpha>_def \<beta>_def)
    qed
    have getN: "\<exists>N::nat. \<forall>k. k \<ge> N \<longrightarrow> x \<in> I k"
      if x: "x \<in> box a b" for x
    proof -
      define \<Delta> where "\<Delta> \<equiv> (\<Union>i \<in> Basis. {((x - a) \<bullet> i) / ((b - a) \<bullet> i), (b - x) \<bullet> i / ((b - a) \<bullet> i)})"
      obtain N where N: "real N > 1 / Inf \<Delta>"
        using reals_Archimedean2 by blast
      moreover have \<Delta>: "Inf \<Delta> > 0"
        using that by (auto simp: \<Delta>_def finite_less_Inf_iff mem_box algebra_simps divide_simps)
      ultimately have "N > 0"
        using of_nat_0_less_iff by fastforce
      show ?thesis
      proof (intro exI impI allI)
        fix k assume "N \<le> k"
        with \<open>0 < N\<close> have "k > 0"
          by linarith
        have xa_gt: "(x - a) \<bullet> i > ((b - a) \<bullet> i) / (real k)" if "i \<in> Basis" for i
        proof -
          have *: "Inf \<Delta> \<le> ((x - a) \<bullet> i) / ((b - a) \<bullet> i)"
            unfolding \<Delta>_def using that by (force intro: cInf_le_finite)
          have "1 / Inf \<Delta> \<ge> ((b - a) \<bullet> i) / ((x - a) \<bullet> i)"
            using le_imp_inverse_le [OF * \<Delta>]
            by (simp add: field_simps)
          with N have "k > ((b - a) \<bullet> i) / ((x - a) \<bullet> i)"
            using \<open>N \<le> k\<close> by linarith
          with x that show ?thesis
            by (auto simp: mem_box algebra_simps field_split_simps)
        qed
        have bx_gt: "(b - x) \<bullet> i > ((b - a) \<bullet> i) / k" if "i \<in> Basis" for i
        proof -
          have *: "Inf \<Delta> \<le> ((b - x) \<bullet> i) / ((b - a) \<bullet> i)"
            using that unfolding \<Delta>_def by (force intro: cInf_le_finite)
          have "1 / Inf \<Delta> \<ge> ((b - a) \<bullet> i) / ((b - x) \<bullet> i)"
            using le_imp_inverse_le [OF * \<Delta>]
            by (simp add: field_simps)
          with N have "k > ((b - a) \<bullet> i) / ((b - x) \<bullet> i)"
            using \<open>N \<le> k\<close> by linarith
          with x that show ?thesis
            by (auto simp: mem_box algebra_simps field_split_simps)
        qed
        show "x \<in> I k"
          using that \<Delta> \<open>k > 0\<close> unfolding I_def
          by (auto simp: \<alpha>_def \<beta>_def mem_box algebra_simps divide_inverse dest: xa_gt bx_gt)
      qed
    qed
    obtain Bf where  Bf: "\<And>c d. cbox c d \<subseteq> box a b \<Longrightarrow> norm (integral (cbox c d) f) \<le> Bf"
      using bo unfolding bounded_iff by blast
    obtain Bg where Bg:"\<And>c d. cbox c d \<subseteq> cbox a b \<Longrightarrow> \<bar>integral (cbox c d) g\<bar> \<le> Bg"
      using bounded_integrals_over_subintervals [OF int_gab] unfolding bounded_iff real_norm_def by blast
    show "(\<lambda>x. f x \<bullet> j) absolutely_integrable_on cbox a b"
      using g
    proof     \<comment> \<open>A lot of duplication in the two proofs\<close>
      assume fg [rule_format]: "\<forall>x\<in>cbox a b. f x \<bullet> j \<le> g x"
      have "(\<lambda>x. (f x \<bullet> j)) = (\<lambda>x. g x - (g x - (f x \<bullet> j)))"
        by simp
      moreover have "(\<lambda>x. g x - (g x - (f x \<bullet> j))) integrable_on cbox a b"
      proof (rule Henstock_Kurzweil_Integration.integrable_diff [OF int_gab])
        define \<phi> where "\<phi> \<equiv> \<lambda>k x. if x \<in> I (Suc k) then g x - f x \<bullet> j else 0"
        have "(\<lambda>x. g x - f x \<bullet> j) integrable_on box a b"
        proof (rule monotone_convergence_increasing [of \<phi>, THEN conjunct1])
          have *: "I (Suc k) \<inter> box a b = I (Suc k)" for k
            using box_subset_cbox ISuc_box by fastforce
          show "\<phi> k integrable_on box a b" for k
          proof -
            have "I (Suc k) \<subseteq> cbox a b"
              using "*" box_subset_cbox by blast
            moreover have "(\<lambda>m. f m \<bullet> j) integrable_on I (Suc k)"
              by (metis ISuc_box I_def int_f integrable_component)
            ultimately have "(\<lambda>m. g m - f m \<bullet> j) integrable_on I (Suc k)"
              by (metis Henstock_Kurzweil_Integration.integrable_diff I_def int_gab integrable_on_subcbox)
            then show ?thesis
              by (simp add: "*" \<phi>_def integrable_restrict_Int)
          qed
          show "\<phi> k x \<le> \<phi> (Suc k) x" if "x \<in> box a b" for k x
            using ISucSuc box_subset_cbox that by (force simp: \<phi>_def intro!: fg)
          show "(\<lambda>k. \<phi> k x) \<longlonglongrightarrow> g x - f x \<bullet> j" if x: "x \<in> box a b" for x
          proof (rule tendsto_eventually)
            obtain N::nat where N: "\<And>k. k \<ge> N \<Longrightarrow> x \<in> I k"
              using getN [OF x] by blast
            show "\<forall>\<^sub>F k in sequentially. \<phi> k x = g x - f x \<bullet> j"
            proof
              fix k::nat assume "N \<le> k"
              have "x \<in> I (Suc k)"
                by (metis \<open>N \<le> k\<close> le_Suc_eq N)
              then show "\<phi> k x = g x - f x \<bullet> j"
                by (simp add: \<phi>_def)
            qed
          qed
          have "\<bar>integral (box a b) (\<lambda>x. if x \<in> I (Suc k) then g x - f x \<bullet> j else 0)\<bar> \<le> Bg + Bf" for k
          proof -
            have ABK_def [simp]: "I (Suc k) \<inter> box a b = I (Suc k)"
              using ISuc_box by (simp add: Int_absorb2)
            have int_fI: "f integrable_on I (Suc k)"
              using ISuc_box I_def int_f by auto
            moreover
            have "\<bar>integral (I (Suc k)) (\<lambda>x. f x \<bullet> j)\<bar> \<le> norm (integral (I (Suc k)) f)"
              by (simp add: Basis_le_norm int_fI \<open>j \<in> Basis\<close>)
            with ISuc_box ABK_def have "\<bar>integral (I (Suc k)) (\<lambda>x. f x \<bullet> j)\<bar> \<le> Bf"
              by (metis Bf I_def \<open>j \<in> Basis\<close> int_fI integral_component_eq norm_bound_Basis_le) 
            ultimately 
            have "\<bar>integral (I (Suc k)) g - integral (I (Suc k)) (\<lambda>x. f x \<bullet> j)\<bar>  \<le> Bg + Bf"
              using "*" box_subset_cbox unfolding I_def
              by (blast intro: Bg add_mono order_trans [OF abs_triangle_ineq4])
            moreover have "g integrable_on I (Suc k)"
              by (metis ISuc_box I_def int_gab integrable_on_open_interval integrable_on_subcbox)
            moreover have "(\<lambda>x. f x \<bullet> j) integrable_on I (Suc k)"
              using int_fI by (simp add: integrable_component)
           ultimately show ?thesis
              by (simp add: integral_restrict_Int integral_diff)
          qed
          then show "bounded (range (\<lambda>k. integral (box a b) (\<phi> k)))"
            by (auto simp add: bounded_iff \<phi>_def)
        qed
        then show "(\<lambda>x. g x - f x \<bullet> j) integrable_on cbox a b"
          by (simp add: integrable_on_open_interval)
      qed
      ultimately have "(\<lambda>x. f x \<bullet> j) integrable_on cbox a b"
        by auto
      then show ?thesis
        using absolutely_integrable_component_ubound [OF _ absint_g] fg by force
    next
      assume gf [rule_format]: "\<forall>x\<in>cbox a b. g x \<le> f x \<bullet> j"
      have "(\<lambda>x. (f x \<bullet> j)) = (\<lambda>x. ((f x \<bullet> j) - g x) + g x)"
        by simp
      moreover have "(\<lambda>x. (f x \<bullet> j - g x) + g x) integrable_on cbox a b"
      proof (rule Henstock_Kurzweil_Integration.integrable_add [OF _ int_gab])
        let ?\<phi> = "\<lambda>k x. if x \<in> I(Suc k) then f x \<bullet> j - g x else 0"
        have "(\<lambda>x. f x \<bullet> j - g x) integrable_on box a b"
        proof (rule monotone_convergence_increasing [of ?\<phi>, THEN conjunct1])
          have *: "I (Suc k) \<inter> box a b = I (Suc k)" for k
            using box_subset_cbox ISuc_box by fastforce
          show "?\<phi> k integrable_on box a b" for k
          proof (simp add: integrable_restrict_Int integral_restrict_Int *)
            show "(\<lambda>x. f x \<bullet> j - g x) integrable_on I (Suc k)"
              by (metis ISuc_box Henstock_Kurzweil_Integration.integrable_diff I_def int_f int_gab integrable_component integrable_on_open_interval integrable_on_subcbox)
          qed
          show "?\<phi> k x \<le> ?\<phi> (Suc k) x" if "x \<in> box a b" for k x
            using ISucSuc box_subset_cbox that by (force simp: I_def intro!: gf)
          show "(\<lambda>k. ?\<phi> k x) \<longlonglongrightarrow> f x \<bullet> j - g x" if x: "x \<in> box a b" for x
          proof (rule tendsto_eventually)
            obtain N::nat where N: "\<And>k. k \<ge> N \<Longrightarrow> x \<in> I k"
              using getN [OF x] by blast
            then show "\<forall>\<^sub>F k in sequentially. ?\<phi> k x = f x \<bullet> j - g x"
              by (metis (no_types, lifting) eventually_at_top_linorderI le_Suc_eq)
          qed
          have "\<bar>integral (box a b)
                      (\<lambda>x. if x \<in> I (Suc k) then f x \<bullet> j - g x else 0)\<bar> \<le> Bf + Bg" for k
          proof -
            define ABK where "ABK \<equiv> cbox (a + (b - a) /\<^sub>R (1 + real k)) (b - (b - a) /\<^sub>R (1 + real k))"
            have ABK_eq [simp]: "ABK \<inter> box a b = ABK"
              using "*" I_def \<alpha>_def \<beta>_def ABK_def by auto
            have int_fI: "f integrable_on ABK"
              unfolding ABK_def
              using ISuc_box I_def \<alpha>_def \<beta>_def int_f by force
            then have "(\<lambda>x. f x \<bullet> j) integrable_on ABK"
              by (simp add: integrable_component)
            moreover have "g integrable_on ABK"
              by (metis ABK_def ABK_eq IntE box_subset_cbox int_gab integrable_on_subcbox subset_eq)
            moreover
            have "\<bar>integral ABK (\<lambda>x. f x \<bullet> j)\<bar> \<le> norm (integral ABK f)"
              by (simp add: Basis_le_norm int_fI \<open>j \<in> Basis\<close>)
            then have "\<bar>integral ABK (\<lambda>x. f x \<bullet> j)\<bar> \<le> Bf"
              by (metis ABK_eq  ABK_def Bf IntE dual_order.trans subset_eq)
            ultimately show ?thesis
              using "*" box_subset_cbox
              apply (simp add: integral_restrict_Int integral_diff ABK_def I_def \<alpha>_def \<beta>_def)
               by (blast intro: Bg add_mono order_trans [OF abs_triangle_ineq4])
          qed
          then show "bounded (range (\<lambda>k. integral (box a b) (?\<phi> k)))"
            by (auto simp add: bounded_iff)
        qed
        then show "(\<lambda>x. f x \<bullet> j - g x) integrable_on cbox a b"
          by (simp add: integrable_on_open_interval)
      qed
      ultimately have "(\<lambda>x. f x \<bullet> j) integrable_on cbox a b"
        by auto
      then show ?thesis
        using absint_g absolutely_integrable_absolutely_integrable_lbound gf by blast
    qed
  qed
qed

subsection\<open>Second mean value theorem and corollaries\<close>

lemma level_approx:
  fixes f :: "real \<Rightarrow> real" and n::nat
  assumes f: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f x \<and> f x \<le> 1" and "x \<in> S" "n \<noteq> 0"
  shows "\<bar>f x - (\<Sum>k = Suc 0..n. if k / n \<le> f x then inverse n else 0)\<bar> < inverse n"
        (is "?lhs < _")
proof -
  have "n * f x \<ge> 0"
    using assms by auto
  then obtain m::nat where m: "floor(n * f x) = int m"
    using nonneg_int_cases zero_le_floor by blast
  then have kn: "real k / real n \<le> f x \<longleftrightarrow> k \<le> m" for k
    using \<open>n \<noteq> 0\<close> by (simp add: field_split_simps) linarith
  then have "Suc n / real n \<le> f x \<longleftrightarrow> Suc n \<le> m"
    by blast
  have "real n * f x \<le> real n"
    by (simp add: \<open>x \<in> S\<close> f mult_left_le)
  then have "m \<le> n"
    using m by linarith
  have "?lhs = \<bar>f x - (\<Sum>k \<in> {Suc 0..n} \<inter> {..m}. inverse n)\<bar>"
    by (subst sum.inter_restrict) (auto simp: kn)
  also have "\<dots> < inverse n"
    using \<open>m \<le> n\<close> \<open>n \<noteq> 0\<close> m
    by (simp add: min_absorb2 field_split_simps) linarith
  finally show ?thesis .
qed


lemma SMVT_lemma2:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f integrable_on {a..b}"
    and g: "\<And>x y. x \<le> y \<Longrightarrow> g x \<le> g y"
  shows "(\<Union>y::real. {\<lambda>x. if g x \<ge> y then f x else 0}) equiintegrable_on {a..b}"
proof -
  have ffab: "{f} equiintegrable_on {a..b}"
    by (metis equiintegrable_on_sing f interval_cbox)
  then have ff: "{f} equiintegrable_on (cbox a b)"
    by simp
  have ge: "(\<Union>c. {\<lambda>x. if x \<ge> c then f x else 0}) equiintegrable_on {a..b}"
    using equiintegrable_halfspace_restrictions_ge [OF ff] by auto
  have gt: "(\<Union>c. {\<lambda>x. if x > c then f x else 0}) equiintegrable_on {a..b}"
    using equiintegrable_halfspace_restrictions_gt [OF ff] by auto
  have 0: "{(\<lambda>x. 0)} equiintegrable_on {a..b}"
    by (metis box_real(2) equiintegrable_on_sing integrable_0)
  have \<dagger>: "(\<lambda>x. if g x \<ge> y then f x else 0) \<in> {(\<lambda>x. 0), f} \<union> (\<Union>z. {\<lambda>x. if z < x then f x else 0}) \<union> (\<Union>z. {\<lambda>x. if z \<le> x then f x else 0})"
    for y
  proof (cases "(\<forall>x. g x \<ge> y) \<or> (\<forall>x. \<not> (g x \<ge> y))")
    let ?\<mu> = "Inf {x. g x \<ge> y}"
    case False
    have lower: "?\<mu> \<le> x" if "g x \<ge> y" for x
    proof (rule cInf_lower)
      show "x \<in> {x. y \<le> g x}"
        using False by (auto simp: that)
      show "bdd_below {x. y \<le> g x}"
        by (metis False bdd_belowI dual_order.trans g linear mem_Collect_eq)
    qed
    have greatest: "?\<mu> \<ge> z" if  "(\<And>x. g x \<ge> y \<Longrightarrow> z \<le> x)" for z
      by (metis False cInf_greatest empty_iff mem_Collect_eq that)
    show ?thesis
    proof (cases "g ?\<mu> \<ge> y")
      case True
      then obtain \<zeta> where \<zeta>: "\<And>x. g x \<ge> y \<longleftrightarrow> x \<ge> \<zeta>"
        by (metis g lower order.trans)  \<comment> \<open>in fact y is @{term ?\<mu>}\<close>
      then show ?thesis
        by (force simp: \<zeta>)
    next
      case False
      have "(y \<le> g x) \<longleftrightarrow> (?\<mu> < x)" for x
      proof
        show "?\<mu> < x" if "y \<le> g x"
          using that False less_eq_real_def lower by blast
        show "y \<le> g x" if "?\<mu> < x"
          by (metis g greatest le_less_trans that less_le_trans linear not_less)
      qed
      then obtain \<zeta> where \<zeta>: "\<And>x. g x \<ge> y \<longleftrightarrow> x > \<zeta>" ..
      then show ?thesis
        by (force simp: \<zeta>)
    qed
  qed auto
  show ?thesis
    using \<dagger> by (simp add: UN_subset_iff equiintegrable_on_subset [OF equiintegrable_on_Un [OF gt equiintegrable_on_Un [OF ge equiintegrable_on_Un [OF ffab 0]]]])
qed


lemma SMVT_lemma4:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f integrable_on {a..b}"
    and "a \<le> b"
    and g: "\<And>x y. x \<le> y \<Longrightarrow> g x \<le> g y"
    and 01: "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> 0 \<le> g x \<and> g x \<le> 1"
  obtains c where "a \<le> c" "c \<le> b" "((\<lambda>x. g x *\<^sub>R f x) has_integral integral {c..b} f) {a..b}"
proof -
  have "connected ((\<lambda>x. integral {x..b} f) ` {a..b})"
    by (simp add: f indefinite_integral_continuous_1' connected_continuous_image)
  moreover have "compact ((\<lambda>x. integral {x..b} f) ` {a..b})"
    by (simp add: compact_continuous_image f indefinite_integral_continuous_1')
  ultimately obtain m M where int_fab: "(\<lambda>x. integral {x..b} f) ` {a..b} = {m..M}"
    using connected_compact_interval_1 by meson
  have "\<exists>c. c \<in> {a..b} \<and>
              integral {c..b} f =
              integral {a..b} (\<lambda>x. (\<Sum>k = 1..n. if g x \<ge> real k / real n then inverse n *\<^sub>R f x else 0))" for n
  proof (cases "n=0")
    case True
    then show ?thesis
      using \<open>a \<le> b\<close> by auto
  next
    case False
    have "(\<Union>c::real. {\<lambda>x. if g x \<ge> c then f x else 0}) equiintegrable_on {a..b}"
      using SMVT_lemma2 [OF f g] .
    then have int: "(\<lambda>x. if g x \<ge> c then f x else 0) integrable_on {a..b}" for c
      by (simp add: equiintegrable_on_def)
    have int': "(\<lambda>x. if g x \<ge> c then u * f x else 0) integrable_on {a..b}" for c u
    proof -
      have "(\<lambda>x. if g x \<ge> c then u * f x else 0) = (\<lambda>x. u * (if g x \<ge> c then f x else 0))"
        by (force simp: if_distrib)
      then show ?thesis
        using integrable_on_cmult_left [OF int] by simp
    qed
    have "\<exists>d. d \<in> {a..b} \<and> integral {a..b} (\<lambda>x. if g x \<ge> y then f x else 0) = integral {d..b} f" for y
    proof -
      let ?X = "{x. g x \<ge> y}"
      have *: "\<exists>a. ?X = {a..} \<or> ?X = {a<..}"
        if 1: "?X \<noteq> {}" and 2: "?X \<noteq> UNIV"
      proof -
        let ?\<mu> = "Inf{x. g x \<ge> y}"
        have lower: "?\<mu> \<le> x" if "g x \<ge> y" for x
        proof (rule cInf_lower)
          show "x \<in> {x. y \<le> g x}"
            using 1 2 by (auto simp: that)
          show "bdd_below {x. y \<le> g x}"
            unfolding bdd_below_def
            by (metis "2" UNIV_eq_I dual_order.trans g less_eq_real_def mem_Collect_eq not_le)
        qed
        have greatest: "?\<mu> \<ge> z" if "\<And>x. g x \<ge> y \<Longrightarrow> z \<le> x" for z
          by (metis cInf_greatest mem_Collect_eq that 1)
        show ?thesis
        proof (cases "g ?\<mu> \<ge> y")
          case True
          then obtain \<zeta> where \<zeta>: "\<And>x. g x \<ge> y \<longleftrightarrow> x \<ge> \<zeta>"
            by (metis g lower order.trans)  \<comment> \<open>in fact y is @{term ?\<mu>}\<close>
          then show ?thesis
            by (force simp: \<zeta>)
        next
          case False
          have "(y \<le> g x) = (?\<mu> < x)" for x
          proof
            show "?\<mu> < x" if "y \<le> g x"
              using that False less_eq_real_def lower by blast
            show "y \<le> g x" if "?\<mu> < x"
              by (metis g greatest le_less_trans that less_le_trans linear not_less)
          qed
          then obtain \<zeta> where \<zeta>: "\<And>x. g x \<ge> y \<longleftrightarrow> x > \<zeta>" ..
          then show ?thesis
            by (force simp: \<zeta>)
        qed
      qed
      then consider "?X = {}" | "?X = UNIV" | (intv) d where "?X = {d..} \<or> ?X = {d<..}"
        by metis
      then have "\<exists>d. d \<in> {a..b} \<and> integral {a..b} (\<lambda>x. if x \<in> ?X then f x else 0) = integral {d..b} f"
      proof cases
        case (intv d)
        show ?thesis
        proof (cases "d < a")
          case True
          with intv have "integral {a..b} (\<lambda>x. if y \<le> g x then f x else 0) = integral {a..b} f"
            by (intro Henstock_Kurzweil_Integration.integral_cong) force
          then show ?thesis
            by (rule_tac x=a in exI) (simp add: \<open>a \<le> b\<close>)
        next
          case False
          show ?thesis
          proof (cases "b < d")
            case True
            have "integral {a..b} (\<lambda>x. if x \<in> {x. y \<le> g x} then f x else 0) = integral {a..b} (\<lambda>x. 0)"
              by (rule Henstock_Kurzweil_Integration.integral_cong) (use intv True in fastforce)
            then show ?thesis
              using \<open>a \<le> b\<close> by auto
          next
            case False
            with \<open>\<not> d < a\<close> have eq: "{d..} \<inter> {a..b} = {d..b}" "{d<..} \<inter> {a..b} = {d<..b}"
              by force+
            moreover have "integral {d<..b} f = integral {d..b} f"
              by (rule integral_spike_set [OF empty_imp_negligible negligible_subset [OF negligible_sing [of d]]]) auto
            ultimately 
            have "integral {a..b} (\<lambda>x. if x \<in> {x. y \<le> g x} then f x else 0) =  integral {d..b} f"
              unfolding integral_restrict_Int using intv by presburger
            moreover have "d \<in> {a..b}"
              using \<open>\<not> d < a\<close> \<open>a \<le> b\<close> False by auto
            ultimately show ?thesis
              by auto
          qed
        qed
      qed (use \<open>a \<le> b\<close> in auto)
      then show ?thesis
        by auto
    qed
    then have "\<forall>k. \<exists>d. d \<in> {a..b} \<and> integral {a..b} (\<lambda>x. if real k / real n \<le> g x then f x else 0) = integral {d..b} f"
      by meson
    then obtain d where dab: "\<And>k. d k \<in> {a..b}"
      and deq: "\<And>k::nat. integral {a..b} (\<lambda>x. if k/n \<le> g x then f x else 0) = integral {d k..b} f"
      by metis
    have "(\<Sum>k = 1..n. integral {a..b} (\<lambda>x. if real k / real n \<le> g x then f x else 0)) /\<^sub>R n \<in> {m..M}"
      unfolding scaleR_right.sum
    proof (intro conjI allI impI convex [THEN iffD1, rule_format])
      show "integral {a..b} (\<lambda>xa. if real k / real n \<le> g xa then f xa else 0) \<in> {m..M}" for k
        by (metis (no_types, lifting) deq image_eqI int_fab dab)
    qed (use \<open>n \<noteq> 0\<close> in auto)
    then have "\<exists>c. c \<in> {a..b} \<and>
              integral {c..b} f = inverse n *\<^sub>R (\<Sum>k = 1..n. integral {a..b} (\<lambda>x. if g x \<ge> real k / real n then f x else 0))"
      by (metis (no_types, lifting) int_fab imageE)
    then show ?thesis
      by (simp add: sum_distrib_left if_distrib integral_sum int' flip: integral_mult_right cong: if_cong)
  qed
  then obtain c where cab: "\<And>n. c n \<in> {a..b}"
    and c: "\<And>n. integral {c n..b} f = integral {a..b} (\<lambda>x. (\<Sum>k = 1..n. if g x \<ge> real k / real n then f x /\<^sub>R n else 0))"
    by metis
  obtain d and \<sigma> :: "nat\<Rightarrow>nat"
    where "d \<in> {a..b}" and \<sigma>: "strict_mono \<sigma>" and d: "(c \<circ> \<sigma>) \<longlonglongrightarrow> d" and non0: "\<And>n. \<sigma> n \<ge> Suc 0"
  proof -
    have "compact{a..b}"
      by auto
    with cab obtain d and s0
      where "d \<in> {a..b}" and s0: "strict_mono s0" and tends: "(c \<circ> s0) \<longlonglongrightarrow> d"
      unfolding compact_def
      using that by blast
    show thesis
    proof
      show "d \<in> {a..b}"
        by fact
      show "strict_mono (s0 \<circ> Suc)"
        using s0 by (auto simp: strict_mono_def)
      show "(c \<circ> (s0 \<circ> Suc)) \<longlonglongrightarrow> d"
        by (metis tends LIMSEQ_subseq_LIMSEQ Suc_less_eq comp_assoc strict_mono_def)
      show "\<And>n. (s0 \<circ> Suc) n \<ge> Suc 0"
        by (metis comp_apply le0 not_less_eq_eq old.nat.exhaust s0 seq_suble)
    qed
  qed
  define \<phi> where "\<phi> \<equiv> \<lambda>n x. \<Sum>k = Suc 0..\<sigma> n. if k/(\<sigma> n) \<le> g x then f x /\<^sub>R (\<sigma> n) else 0"
  define \<psi> where "\<psi> \<equiv> \<lambda>n x. \<Sum>k = Suc 0..\<sigma> n. if k/(\<sigma> n) \<le> g x then inverse (\<sigma> n) else 0"
  have **: "(\<lambda>x. g x *\<^sub>R f x) integrable_on cbox a b \<and>
            (\<lambda>n. integral (cbox a b) (\<phi> n)) \<longlonglongrightarrow> integral (cbox a b) (\<lambda>x. g x *\<^sub>R f x)"
  proof (rule equiintegrable_limit)
    have \<dagger>: "((\<lambda>n. \<lambda>x. (\<Sum>k = Suc 0..n. if k / n \<le> g x then inverse n *\<^sub>R f x else 0)) ` {Suc 0..}) equiintegrable_on {a..b}"
    proof -
      have *: "(\<Union>c::real. {\<lambda>x. if g x \<ge> c then f x else 0}) equiintegrable_on {a..b}"
        using SMVT_lemma2 [OF f g] .
      show ?thesis
        apply (rule equiintegrable_on_subset [OF equiintegrable_sum_real [OF *]], clarify)
        apply (rule_tac a="{Suc 0..n}" in UN_I, force)
        apply (rule_tac a="\<lambda>k. inverse n" in UN_I, auto)
        apply (rule_tac x="\<lambda>k x. if real k / real n \<le> g x then f x else 0" in bexI)
         apply (force intro: sum.cong)+
        done
    qed
    show "range \<phi> equiintegrable_on cbox a b"
      unfolding \<phi>_def
      by (auto simp: non0 intro: equiintegrable_on_subset [OF \<dagger>])
    show "(\<lambda>n. \<phi> n x) \<longlonglongrightarrow> g x *\<^sub>R f x"
      if x: "x \<in> cbox a b" for x
    proof -
      have eq: "\<phi> n x = \<psi> n x *\<^sub>R f x"  for n
        by (auto simp: \<phi>_def \<psi>_def sum_distrib_right if_distrib intro: sum.cong)
      show ?thesis
        unfolding eq
      proof (rule tendsto_scaleR [OF _ tendsto_const])
        show "(\<lambda>n. \<psi> n x) \<longlonglongrightarrow> g x"
          unfolding lim_sequentially dist_real_def
        proof (intro allI impI)
          fix e :: real
          assume "e > 0"
          then obtain N where "N \<noteq> 0" "0 < inverse (real N)" and N: "inverse (real N) < e"
            using real_arch_inverse by metis
          moreover have "\<bar>\<psi> n x - g x\<bar> < inverse (real N)" if "n\<ge>N" for n
          proof -
            have "\<bar>g x - \<psi> n x\<bar> < inverse (real (\<sigma> n))"
              unfolding \<psi>_def
            proof (rule level_approx [of "{a..b}" g])
              show "\<sigma> n \<noteq> 0"
                by (metis Suc_n_not_le_n non0)
            qed (use x 01 non0 in auto)
            also have "\<dots> \<le> inverse N"
              using seq_suble [OF \<sigma>] \<open>N \<noteq> 0\<close> non0 that by (auto intro: order_trans simp: field_split_simps)
            finally show ?thesis
              by linarith
          qed
          ultimately show "\<exists>N. \<forall>n\<ge>N. \<bar>\<psi> n x - g x\<bar> < e"
            using less_trans by blast
        qed
      qed
    qed
  qed
  show thesis
  proof
    show "a \<le> d" "d \<le> b"
      using \<open>d \<in> {a..b}\<close> atLeastAtMost_iff by blast+
    show "((\<lambda>x. g x *\<^sub>R f x) has_integral integral {d..b} f) {a..b}"
      unfolding has_integral_iff
    proof
      show "(\<lambda>x. g x *\<^sub>R f x) integrable_on {a..b}"
        using ** by simp
      show "integral {a..b} (\<lambda>x. g x *\<^sub>R f x) = integral {d..b} f"
      proof (rule tendsto_unique)
        show "(\<lambda>n. integral {c(\<sigma> n)..b} f) \<longlonglongrightarrow> integral {a..b} (\<lambda>x. g x *\<^sub>R f x)"
          using ** by (simp add: c \<phi>_def)
        have "continuous (at d within {a..b}) (\<lambda>x. integral {x..b} f)"
          using indefinite_integral_continuous_1' [OF f] \<open>d \<in> {a..b}\<close> 
          by (simp add: continuous_on_eq_continuous_within)
        then show "(\<lambda>n. integral {c(\<sigma> n)..b} f) \<longlonglongrightarrow> integral {d..b} f"
          using d cab unfolding o_def
          by (simp add: continuous_within_sequentially o_def)
      qed auto
    qed
  qed
qed


theorem second_mean_value_theorem_full:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f integrable_on {a..b}" and "a \<le> b"
    and g: "\<And>x y. \<lbrakk>a \<le> x; x \<le> y; y \<le> b\<rbrakk> \<Longrightarrow> g x \<le> g y"
  obtains c where "c \<in> {a..b}"
    and "((\<lambda>x. g x * f x) has_integral (g a * integral {a..c} f + g b * integral {c..b} f)) {a..b}"
proof -
  have gab: "g a \<le> g b"
    using \<open>a \<le> b\<close> g by blast
  then consider "g a < g b" | "g a = g b"
    by linarith
  then show thesis
  proof cases
    case 1
    define h where "h \<equiv> \<lambda>x. if x < a then 0 else if b < x then 1
                             else (g x - g a) / (g b - g a)"
    obtain c where "a \<le> c" "c \<le> b" and c: "((\<lambda>x. h x *\<^sub>R f x) has_integral integral {c..b} f) {a..b}"
    proof (rule SMVT_lemma4 [OF f \<open>a \<le> b\<close>, of h])
      show "h x \<le> h y" "0 \<le> h x \<and> h x \<le> 1"  if "x \<le> y" for x y
        using that gab by (auto simp: divide_simps g h_def)
    qed
    show ?thesis
    proof
      show "c \<in> {a..b}"
        using \<open>a \<le> c\<close> \<open>c \<le> b\<close> by auto
      have I: "((\<lambda>x. g x * f x - g a * f x) has_integral (g b - g a) * integral {c..b} f) {a..b}"
      proof (subst has_integral_cong)
        show "g x * f x - g a * f x = (g b - g a) * h x *\<^sub>R f x"
          if "x \<in> {a..b}" for x
          using 1 that by (simp add: h_def field_split_simps)
        show "((\<lambda>x. (g b - g a) * h x *\<^sub>R f x) has_integral (g b - g a) * integral {c..b} f) {a..b}"
          using has_integral_mult_right [OF c, of "g b - g a"] .
      qed
      have II: "((\<lambda>x. g a * f x) has_integral g a * integral {a..b} f) {a..b}"
        using has_integral_mult_right [where c = "g a", OF integrable_integral [OF f]] .
      have "((\<lambda>x. g x * f x) has_integral (g b - g a) * integral {c..b} f + g a * integral {a..b} f) {a..b}"
        using has_integral_add [OF I II] by simp
      then show "((\<lambda>x. g x * f x) has_integral g a * integral {a..c} f + g b * integral {c..b} f) {a..b}"
        by (simp add: algebra_simps flip: integral_combine [OF \<open>a \<le> c\<close> \<open>c \<le> b\<close> f])
    qed
  next
    case 2
    show ?thesis
    proof
      show "a \<in> {a..b}"
        by (simp add: \<open>a \<le> b\<close>)
      have "((\<lambda>x. g x * f x) has_integral g a * integral {a..b} f) {a..b}"
      proof (rule has_integral_eq)
        show "((\<lambda>x. g a * f x) has_integral g a * integral {a..b} f) {a..b}"
          using f has_integral_mult_right by blast
        show "g a * f x = g x * f x"
          if "x \<in> {a..b}" for x
          by (metis atLeastAtMost_iff g less_eq_real_def not_le that 2)
      qed
      then show "((\<lambda>x. g x * f x) has_integral g a * integral {a..a} f + g b * integral {a..b} f) {a..b}"
        by (simp add: 2)
    qed
  qed
qed


corollary second_mean_value_theorem:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f integrable_on {a..b}" and "a \<le> b"
   and g: "\<And>x y. \<lbrakk>a \<le> x; x \<le> y; y \<le> b\<rbrakk> \<Longrightarrow> g x \<le> g y"
 obtains c where "c \<in> {a..b}"
                 "integral {a..b} (\<lambda>x. g x * f x) = g a * integral {a..c} f + g b * integral {c..b} f"
    using second_mean_value_theorem_full [where g=g, OF assms]
    by (metis (full_types) integral_unique)

end

