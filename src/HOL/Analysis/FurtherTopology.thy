section \<open>Extending Continous Maps, Invariance of Domain, etc..\<close>

text\<open>Ported from HOL Light (moretop.ml) by L C Paulson\<close>

theory "FurtherTopology"
  imports Equivalence_Lebesgue_Henstock_Integration Weierstrass_Theorems Polytope

begin

subsection\<open>A map from a sphere to a higher dimensional sphere is nullhomotopic\<close>

lemma spheremap_lemma1:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "subspace S" "subspace T" and dimST: "dim S < dim T"
      and "S \<subseteq> T"
      and diff_f: "f differentiable_on sphere 0 1 \<inter> S"
    shows "f ` (sphere 0 1 \<inter> S) \<noteq> sphere 0 1 \<inter> T"
proof
  assume fim: "f ` (sphere 0 1 \<inter> S) = sphere 0 1 \<inter> T"
  have inS: "\<And>x. \<lbrakk>x \<in> S; x \<noteq> 0\<rbrakk> \<Longrightarrow> (x /\<^sub>R norm x) \<in> S"
    using subspace_mul \<open>subspace S\<close> by blast
  have subS01: "(\<lambda>x. x /\<^sub>R norm x) ` (S - {0}) \<subseteq> sphere 0 1 \<inter> S"
    using \<open>subspace S\<close> subspace_mul by fastforce
  then have diff_f': "f differentiable_on (\<lambda>x. x /\<^sub>R norm x) ` (S - {0})"
    by (rule differentiable_on_subset [OF diff_f])
  define g where "g \<equiv> \<lambda>x. norm x *\<^sub>R f(inverse(norm x) *\<^sub>R x)"
  have gdiff: "g differentiable_on S - {0}"
    unfolding g_def
    by (rule diff_f' derivative_intros differentiable_on_compose [where f=f] | force)+
  have geq: "g ` (S - {0}) = T - {0}"
  proof
    have "g ` (S - {0}) \<subseteq> T"
      apply (auto simp: g_def subspace_mul [OF \<open>subspace T\<close>])
      apply (metis (mono_tags, lifting) DiffI subS01 subspace_mul [OF \<open>subspace T\<close>] fim image_subset_iff inf_le2 singletonD)
      done
    moreover have "g ` (S - {0}) \<subseteq> UNIV - {0}"
    proof (clarsimp simp: g_def)
      fix y
      assume "y \<in> S" and f0: "f (y /\<^sub>R norm y) = 0"
      then have "y \<noteq> 0 \<Longrightarrow> y /\<^sub>R norm y \<in> sphere 0 1 \<inter> S"
        by (auto simp: subspace_mul [OF \<open>subspace S\<close>])
      then show "y = 0"
        by (metis fim f0 Int_iff image_iff mem_sphere_0 norm_eq_zero zero_neq_one)
    qed
    ultimately show "g ` (S - {0}) \<subseteq> T - {0}"
      by auto
  next
    have *: "sphere 0 1 \<inter> T \<subseteq> f ` (sphere 0 1 \<inter> S)"
      using fim by (simp add: image_subset_iff)
    have "x \<in> (\<lambda>x. norm x *\<^sub>R f (x /\<^sub>R norm x)) ` (S - {0})"
          if "x \<in> T" "x \<noteq> 0" for x
    proof -
      have "x /\<^sub>R norm x \<in> T"
        using \<open>subspace T\<close> subspace_mul that by blast
      then show ?thesis
        using * [THEN subsetD, of "x /\<^sub>R norm x"] that apply clarsimp
        apply (rule_tac x="norm x *\<^sub>R xa" in image_eqI, simp)
        apply (metis norm_eq_zero right_inverse scaleR_one scaleR_scaleR)
        using \<open>subspace S\<close> subspace_mul apply force
        done
    qed
    then have "T - {0} \<subseteq> (\<lambda>x. norm x *\<^sub>R f (x /\<^sub>R norm x)) ` (S - {0})"
      by force
    then show "T - {0} \<subseteq> g ` (S - {0})"
      by (simp add: g_def)
  qed
  define T' where "T' \<equiv> {y. \<forall>x \<in> T. orthogonal x y}"
  have "subspace T'"
    by (simp add: subspace_orthogonal_to_vectors T'_def)
  have dim_eq: "dim T' + dim T = DIM('a)"
    using dim_subspace_orthogonal_to_vectors [of T UNIV] \<open>subspace T\<close>
    by (simp add: dim_UNIV T'_def)
  have "\<exists>v1 v2. v1 \<in> span T \<and> (\<forall>w \<in> span T. orthogonal v2 w) \<and> x = v1 + v2" for x
    by (force intro: orthogonal_subspace_decomp_exists [of T x])
  then obtain p1 p2 where p1span: "p1 x \<in> span T"
                      and "\<And>w. w \<in> span T \<Longrightarrow> orthogonal (p2 x) w"
                      and eq: "p1 x + p2 x = x" for x
    by metis
  then have p1: "\<And>z. p1 z \<in> T" and ortho: "\<And>w. w \<in> T \<Longrightarrow> orthogonal (p2 x) w" for x
    using span_eq \<open>subspace T\<close> by blast+
  then have p2: "\<And>z. p2 z \<in> T'"
    by (simp add: T'_def orthogonal_commute)
  have p12_eq: "\<And>x y. \<lbrakk>x \<in> T; y \<in> T'\<rbrakk> \<Longrightarrow> p1(x + y) = x \<and> p2(x + y) = y"
  proof (rule orthogonal_subspace_decomp_unique [OF eq p1span, where T=T'])
    show "\<And>x y. \<lbrakk>x \<in> T; y \<in> T'\<rbrakk> \<Longrightarrow> p2 (x + y) \<in> span T'"
      using span_eq p2 \<open>subspace T'\<close> by blast
    show "\<And>a b. \<lbrakk>a \<in> T; b \<in> T'\<rbrakk> \<Longrightarrow> orthogonal a b"
      using T'_def by blast
  qed (auto simp: span_superset)
  then have "\<And>c x. p1 (c *\<^sub>R x) = c *\<^sub>R p1 x \<and> p2 (c *\<^sub>R x) = c *\<^sub>R p2 x"
    by (metis eq \<open>subspace T\<close> \<open>subspace T'\<close> p1 p2 scaleR_add_right subspace_mul)
  moreover have lin_add: "\<And>x y. p1 (x + y) = p1 x + p1 y \<and> p2 (x + y) = p2 x + p2 y"
  proof (rule orthogonal_subspace_decomp_unique [OF _ p1span, where T=T'])
    show "\<And>x y. p1 (x + y) + p2 (x + y) = p1 x + p1 y + (p2 x + p2 y)"
      by (simp add: add.assoc add.left_commute eq)
    show  "\<And>a b. \<lbrakk>a \<in> T; b \<in> T'\<rbrakk> \<Longrightarrow> orthogonal a b"
      using T'_def by blast
  qed (auto simp: p1span p2 span_superset subspace_add)
  ultimately have "linear p1" "linear p2"
    by unfold_locales auto
  have "(\<lambda>z. g (p1 z)) differentiable_on {x + y |x y. x \<in> S - {0} \<and> y \<in> T'}"
    apply (rule differentiable_on_compose [where f=g])
    apply (rule linear_imp_differentiable_on [OF \<open>linear p1\<close>])
    apply (rule differentiable_on_subset [OF gdiff])
    using p12_eq \<open>S \<subseteq> T\<close> apply auto
    done
  then have diff: "(\<lambda>x. g (p1 x) + p2 x) differentiable_on {x + y |x y. x \<in> S - {0} \<and> y \<in> T'}"
    by (intro derivative_intros linear_imp_differentiable_on [OF \<open>linear p2\<close>])
  have "dim {x + y |x y. x \<in> S - {0} \<and> y \<in> T'} \<le> dim {x + y |x y. x \<in> S  \<and> y \<in> T'}"
    by (blast intro: dim_subset)
  also have "... = dim S + dim T' - dim (S \<inter> T')"
    using dim_sums_Int [OF \<open>subspace S\<close> \<open>subspace T'\<close>]
    by (simp add: algebra_simps)
  also have "... < DIM('a)"
    using dimST dim_eq by auto
  finally have neg: "negligible {x + y |x y. x \<in> S - {0} \<and> y \<in> T'}"
    by (rule negligible_lowdim)
  have "negligible ((\<lambda>x. g (p1 x) + p2 x) ` {x + y |x y. x \<in> S - {0} \<and> y \<in> T'})"
    by (rule negligible_differentiable_image_negligible [OF order_refl neg diff])
  then have "negligible {x + y |x y. x \<in> g ` (S - {0}) \<and> y \<in> T'}"
  proof (rule negligible_subset)
    have "\<lbrakk>t' \<in> T'; s \<in> S; s \<noteq> 0\<rbrakk>
          \<Longrightarrow> g s + t' \<in> (\<lambda>x. g (p1 x) + p2 x) `
                         {x + t' |x t'. x \<in> S \<and> x \<noteq> 0 \<and> t' \<in> T'}" for t' s
      apply (rule_tac x="s + t'" in image_eqI)
      using \<open>S \<subseteq> T\<close> p12_eq by auto
    then show "{x + y |x y. x \<in> g ` (S - {0}) \<and> y \<in> T'}
          \<subseteq> (\<lambda>x. g (p1 x) + p2 x) ` {x + y |x y. x \<in> S - {0} \<and> y \<in> T'}"
      by auto
  qed
  moreover have "- T' \<subseteq> {x + y |x y. x \<in> g ` (S - {0}) \<and> y \<in> T'}"
  proof clarsimp
    fix z assume "z \<notin> T'"
    show "\<exists>x y. z = x + y \<and> x \<in> g ` (S - {0}) \<and> y \<in> T'"
      apply (rule_tac x="p1 z" in exI)
      apply (rule_tac x="p2 z" in exI)
      apply (simp add: p1 eq p2 geq)
      by (metis \<open>z \<notin> T'\<close> add.left_neutral eq p2)
  qed
  ultimately have "negligible (-T')"
    using negligible_subset by blast
  moreover have "negligible T'"
    using negligible_lowdim
    by (metis add.commute assms(3) diff_add_inverse2 diff_self_eq_0 dim_eq le_add1 le_antisym linordered_semidom_class.add_diff_inverse not_less0)
  ultimately have  "negligible (-T' \<union> T')"
    by (metis negligible_Un_eq)
  then show False
    using negligible_Un_eq non_negligible_UNIV by simp
qed


lemma spheremap_lemma2:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes ST: "subspace S" "subspace T" "dim S < dim T"
      and "S \<subseteq> T"
      and contf: "continuous_on (sphere 0 1 \<inter> S) f"
      and fim: "f ` (sphere 0 1 \<inter> S) \<subseteq> sphere 0 1 \<inter> T"
    shows "\<exists>c. homotopic_with (\<lambda>x. True) (sphere 0 1 \<inter> S) (sphere 0 1 \<inter> T) f (\<lambda>x. c)"
proof -
  have [simp]: "\<And>x. \<lbrakk>norm x = 1; x \<in> S\<rbrakk> \<Longrightarrow> norm (f x) = 1"
    using fim by (simp add: image_subset_iff)
  have "compact (sphere 0 1 \<inter> S)"
    by (simp add: \<open>subspace S\<close> closed_subspace compact_Int_closed)
  then obtain g where pfg: "polynomial_function g" and gim: "g ` (sphere 0 1 \<inter> S) \<subseteq> T"
                and g12: "\<And>x. x \<in> sphere 0 1 \<inter> S \<Longrightarrow> norm(f x - g x) < 1/2"
    apply (rule Stone_Weierstrass_polynomial_function_subspace [OF _ contf _ \<open>subspace T\<close>, of "1/2"])
    using fim apply auto
    done
  have gnz: "g x \<noteq> 0" if "x \<in> sphere 0 1 \<inter> S" for x
  proof -
    have "norm (f x) = 1"
      using fim that by (simp add: image_subset_iff)
    then show ?thesis
      using g12 [OF that] by auto
  qed
  have diffg: "g differentiable_on sphere 0 1 \<inter> S"
    by (metis pfg differentiable_on_polynomial_function)
  define h where "h \<equiv> \<lambda>x. inverse(norm(g x)) *\<^sub>R g x"
  have h: "x \<in> sphere 0 1 \<inter> S \<Longrightarrow> h x \<in> sphere 0 1 \<inter> T" for x
    unfolding h_def
    using gnz [of x]
    by (auto simp: subspace_mul [OF \<open>subspace T\<close>] subsetD [OF gim])
  have diffh: "h differentiable_on sphere 0 1 \<inter> S"
    unfolding h_def
    apply (intro derivative_intros diffg differentiable_on_compose [OF diffg])
    using gnz apply auto
    done
  have homfg: "homotopic_with (\<lambda>z. True) (sphere 0 1 \<inter> S) (T - {0}) f g"
  proof (rule homotopic_with_linear [OF contf])
    show "continuous_on (sphere 0 1 \<inter> S) g"
      using pfg by (simp add: differentiable_imp_continuous_on diffg)
  next
    have non0fg: "0 \<notin> closed_segment (f x) (g x)" if "norm x = 1" "x \<in> S" for x
    proof -
      have "f x \<in> sphere 0 1"
        using fim that by (simp add: image_subset_iff)
      moreover have "norm(f x - g x) < 1/2"
        apply (rule g12)
        using that by force
      ultimately show ?thesis
        by (auto simp: norm_minus_commute dest: segment_bound)
    qed
    show "\<And>x. x \<in> sphere 0 1 \<inter> S \<Longrightarrow> closed_segment (f x) (g x) \<subseteq> T - {0}"
      apply (simp add: subset_Diff_insert non0fg)
      apply (simp add: segment_convex_hull)
      apply (rule hull_minimal)
       using fim image_eqI gim apply force
      apply (rule subspace_imp_convex [OF \<open>subspace T\<close>])
      done
  qed
  obtain d where d: "d \<in> (sphere 0 1 \<inter> T) - h ` (sphere 0 1 \<inter> S)"
    using h spheremap_lemma1 [OF ST \<open>S \<subseteq> T\<close> diffh] by force
  then have non0hd: "0 \<notin> closed_segment (h x) (- d)" if "norm x = 1" "x \<in> S" for x
    using midpoint_between [of 0 "h x" "-d"] that h [of x]
    by (auto simp: between_mem_segment midpoint_def)
  have conth: "continuous_on (sphere 0 1 \<inter> S) h"
    using differentiable_imp_continuous_on diffh by blast
  have hom_hd: "homotopic_with (\<lambda>z. True) (sphere 0 1 \<inter> S) (T - {0}) h (\<lambda>x. -d)"
    apply (rule homotopic_with_linear [OF conth continuous_on_const])
    apply (simp add: subset_Diff_insert non0hd)
    apply (simp add: segment_convex_hull)
    apply (rule hull_minimal)
     using h d apply (force simp: subspace_neg [OF \<open>subspace T\<close>])
    apply (rule subspace_imp_convex [OF \<open>subspace T\<close>])
    done
  have conT0: "continuous_on (T - {0}) (\<lambda>y. inverse(norm y) *\<^sub>R y)"
    by (intro continuous_intros) auto
  have sub0T: "(\<lambda>y. y /\<^sub>R norm y) ` (T - {0}) \<subseteq> sphere 0 1 \<inter> T"
    by (fastforce simp: assms(2) subspace_mul)
  obtain c where homhc: "homotopic_with (\<lambda>z. True) (sphere 0 1 \<inter> S) (sphere 0 1 \<inter> T) h (\<lambda>x. c)"
    apply (rule_tac c="-d" in that)
    apply (rule homotopic_with_eq)
       apply (rule homotopic_compose_continuous_left [OF hom_hd conT0 sub0T])
    using d apply (auto simp: h_def)
    done
  show ?thesis
    apply (rule_tac x=c in exI)
    apply (rule homotopic_with_trans [OF _ homhc])
    apply (rule homotopic_with_eq)
       apply (rule homotopic_compose_continuous_left [OF homfg conT0 sub0T])
      apply (auto simp: h_def)
    done
qed


lemma spheremap_lemma3:
  assumes "bounded S" "convex S" "subspace U" and affSU: "aff_dim S \<le> dim U"
  obtains T where "subspace T" "T \<subseteq> U" "S \<noteq> {} \<Longrightarrow> aff_dim T = aff_dim S"
                  "(rel_frontier S) homeomorphic (sphere 0 1 \<inter> T)"
proof (cases "S = {}")
  case True
  with \<open>subspace U\<close> subspace_0 show ?thesis
    by (rule_tac T = "{0}" in that) auto
next
  case False
  then obtain a where "a \<in> S"
    by auto
  then have affS: "aff_dim S = int (dim ((\<lambda>x. -a+x) ` S))"
    by (metis hull_inc aff_dim_eq_dim)
  with affSU have "dim ((\<lambda>x. -a+x) ` S) \<le> dim U"
    by linarith
  with choose_subspace_of_subspace
  obtain T where "subspace T" "T \<subseteq> span U" and dimT: "dim T = dim ((\<lambda>x. -a+x) ` S)" .
  show ?thesis
  proof (rule that [OF \<open>subspace T\<close>])
    show "T \<subseteq> U"
      using span_eq \<open>subspace U\<close> \<open>T \<subseteq> span U\<close> by blast
    show "aff_dim T = aff_dim S"
      using dimT \<open>subspace T\<close> affS aff_dim_subspace by fastforce
    show "rel_frontier S homeomorphic sphere 0 1 \<inter> T"
    proof -
      have "aff_dim (ball 0 1 \<inter> T) = aff_dim (T)"
        by (metis IntI interior_ball \<open>subspace T\<close> aff_dim_convex_Int_nonempty_interior centre_in_ball empty_iff inf_commute subspace_0 subspace_imp_convex zero_less_one)
      then have affS_eq: "aff_dim S = aff_dim (ball 0 1 \<inter> T)"
        using \<open>aff_dim T = aff_dim S\<close> by simp
      have "rel_frontier S homeomorphic rel_frontier(ball 0 1 \<inter> T)"
        apply (rule homeomorphic_rel_frontiers_convex_bounded_sets [OF \<open>convex S\<close> \<open>bounded S\<close>])
          apply (simp add: \<open>subspace T\<close> convex_Int subspace_imp_convex)
         apply (simp add: bounded_Int)
        apply (rule affS_eq)
        done
      also have "... = frontier (ball 0 1) \<inter> T"
        apply (rule convex_affine_rel_frontier_Int [OF convex_ball])
         apply (simp add: \<open>subspace T\<close> subspace_imp_affine)
        using \<open>subspace T\<close> subspace_0 by force
      also have "... = sphere 0 1 \<inter> T"
        by auto
      finally show ?thesis .
    qed
  qed
qed


proposition inessential_spheremap_lowdim_gen:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "convex S" "bounded S" "convex T" "bounded T"
      and affST: "aff_dim S < aff_dim T"
      and contf: "continuous_on (rel_frontier S) f"
      and fim: "f ` (rel_frontier S) \<subseteq> rel_frontier T"
  obtains c where "homotopic_with (\<lambda>z. True) (rel_frontier S) (rel_frontier T) f (\<lambda>x. c)"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp add: that)
next
  case False
  then show ?thesis
  proof (cases "T = {}")
    case True
    then show ?thesis
      using fim that by auto
  next
    case False
    obtain T':: "'a set"
      where "subspace T'" and affT': "aff_dim T' = aff_dim T"
        and homT: "rel_frontier T homeomorphic sphere 0 1 \<inter> T'"
      apply (rule spheremap_lemma3 [OF \<open>bounded T\<close> \<open>convex T\<close> subspace_UNIV, where 'b='a])
       apply (simp add: dim_UNIV aff_dim_le_DIM)
      using \<open>T \<noteq> {}\<close> by blast
    with homeomorphic_imp_homotopy_eqv
    have relT: "sphere 0 1 \<inter> T'  homotopy_eqv rel_frontier T"
      using homotopy_eqv_sym by blast
    have "aff_dim S \<le> int (dim T')"
      using affT' \<open>subspace T'\<close> affST aff_dim_subspace by force
    with spheremap_lemma3 [OF \<open>bounded S\<close> \<open>convex S\<close> \<open>subspace T'\<close>] \<open>S \<noteq> {}\<close>
    obtain S':: "'a set" where "subspace S'" "S' \<subseteq> T'"
       and affS': "aff_dim S' = aff_dim S"
       and homT: "rel_frontier S homeomorphic sphere 0 1 \<inter> S'"
        by metis
    with homeomorphic_imp_homotopy_eqv
    have relS: "sphere 0 1 \<inter> S'  homotopy_eqv rel_frontier S"
      using homotopy_eqv_sym by blast
    have dimST': "dim S' < dim T'"
      by (metis \<open>S' \<subseteq> T'\<close> \<open>subspace S'\<close> \<open>subspace T'\<close> affS' affST affT' less_irrefl not_le subspace_dim_equal)
    have "\<exists>c. homotopic_with (\<lambda>z. True) (rel_frontier S) (rel_frontier T) f (\<lambda>x. c)"
      apply (rule homotopy_eqv_homotopic_triviality_null_imp [OF relT contf fim])
      apply (rule homotopy_eqv_cohomotopic_triviality_null[OF relS, THEN iffD1, rule_format])
       apply (metis dimST' \<open>subspace S'\<close>  \<open>subspace T'\<close>  \<open>S' \<subseteq> T'\<close> spheremap_lemma2, blast)
      done
    with that show ?thesis by blast
  qed
qed

lemma inessential_spheremap_lowdim:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes
   "DIM('M) < DIM('a)" and f: "continuous_on (sphere a r) f" "f ` (sphere a r) \<subseteq> (sphere b s)"
   obtains c where "homotopic_with (\<lambda>z. True) (sphere a r) (sphere b s) f (\<lambda>x. c)"
proof (cases "s \<le> 0")
  case True then show ?thesis
    by (meson nullhomotopic_into_contractible f contractible_sphere that)
next
  case False
  show ?thesis
  proof (cases "r \<le> 0")
    case True then show ?thesis
      by (meson f nullhomotopic_from_contractible contractible_sphere that)
  next
    case False
    with \<open>~ s \<le> 0\<close> have "r > 0" "s > 0" by auto
    show ?thesis
      apply (rule inessential_spheremap_lowdim_gen [of "cball a r" "cball b s" f])
      using  \<open>0 < r\<close> \<open>0 < s\<close> assms(1)
             apply (simp_all add: f aff_dim_cball)
      using that by blast
  qed
qed



subsection\<open> Some technical lemmas about extending maps from cell complexes.\<close>

lemma extending_maps_Union_aux:
  assumes fin: "finite \<F>"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> closed S"
      and "\<And>S T. \<lbrakk>S \<in> \<F>; T \<in> \<F>; S \<noteq> T\<rbrakk> \<Longrightarrow> S \<inter> T \<subseteq> K"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>g. continuous_on S g \<and> g ` S \<subseteq> T \<and> (\<forall>x \<in> S \<inter> K. g x = h x)"
   shows "\<exists>g. continuous_on (\<Union>\<F>) g \<and> g ` (\<Union>\<F>) \<subseteq> T \<and> (\<forall>x \<in> \<Union>\<F> \<inter> K. g x = h x)"
using assms
proof (induction \<F>)
  case empty show ?case by simp
next
  case (insert S \<F>)
  then obtain f where contf: "continuous_on (S) f" and fim: "f ` S \<subseteq> T" and feq: "\<forall>x \<in> S \<inter> K. f x = h x"
    by (meson insertI1)
  obtain g where contg: "continuous_on (\<Union>\<F>) g" and gim: "g ` \<Union>\<F> \<subseteq> T" and geq: "\<forall>x \<in> \<Union>\<F> \<inter> K. g x = h x"
    using insert by auto
  have fg: "f x = g x" if "x \<in> T" "T \<in> \<F>" "x \<in> S" for x T
  proof -
    have "T \<inter> S \<subseteq> K \<or> S = T"
      using that by (metis (no_types) insert.prems(2) insertCI)
    then show ?thesis
      using UnionI feq geq \<open>S \<notin> \<F>\<close> subsetD that by fastforce
  qed
  show ?case
    apply (rule_tac x="\<lambda>x. if x \<in> S then f x else g x" in exI, simp)
    apply (intro conjI continuous_on_cases)
    apply (simp_all add: insert closed_Union contf contg)
    using fim gim feq geq
    apply (force simp: insert closed_Union contf contg inf_commute intro: fg)+
    done
qed

lemma extending_maps_Union:
  assumes fin: "finite \<F>"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>g. continuous_on S g \<and> g ` S \<subseteq> T \<and> (\<forall>x \<in> S \<inter> K. g x = h x)"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> closed S"
      and K: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>; ~ X \<subseteq> Y; ~ Y \<subseteq> X\<rbrakk> \<Longrightarrow> X \<inter> Y \<subseteq> K"
    shows "\<exists>g. continuous_on (\<Union>\<F>) g \<and> g ` (\<Union>\<F>) \<subseteq> T \<and> (\<forall>x \<in> \<Union>\<F> \<inter> K. g x = h x)"
apply (simp add: Union_maximal_sets [OF fin, symmetric])
apply (rule extending_maps_Union_aux)
apply (simp_all add: Union_maximal_sets [OF fin] assms)
by (metis K psubsetI)


lemma extend_map_lemma:
  assumes "finite \<F>" "\<G> \<subseteq> \<F>" "convex T" "bounded T"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and aff: "\<And>X. X \<in> \<F> - \<G> \<Longrightarrow> aff_dim X < aff_dim T"
      and face: "\<And>S T. \<lbrakk>S \<in> \<F>; T \<in> \<F>\<rbrakk> \<Longrightarrow> (S \<inter> T) face_of S \<and> (S \<inter> T) face_of T"
      and contf: "continuous_on (\<Union>\<G>) f" and fim: "f ` (\<Union>\<G>) \<subseteq> rel_frontier T"
  obtains g where "continuous_on (\<Union>\<F>) g" "g ` (\<Union>\<F>) \<subseteq> rel_frontier T" "\<And>x. x \<in> \<Union>\<G> \<Longrightarrow> g x = f x"
proof (cases "\<F> - \<G> = {}")
  case True
  then have "\<Union>\<F> \<subseteq> \<Union>\<G>"
    by (simp add: Union_mono)
  then show ?thesis
    apply (rule_tac g=f in that)
      using contf continuous_on_subset apply blast
     using fim apply blast
    by simp
next
  case False
  then have "0 \<le> aff_dim T"
    by (metis aff aff_dim_empty aff_dim_geq aff_dim_negative_iff all_not_in_conv not_less)
  then obtain i::nat where i: "int i = aff_dim T"
    by (metis nonneg_eq_int)
  have Union_empty_eq: "\<Union>{D. D = {} \<and> P D} = {}" for P :: "'a set \<Rightarrow> bool"
    by auto
  have extendf: "\<exists>g. continuous_on (\<Union>(\<G> \<union> {D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D < i})) g \<and>
                     g ` (\<Union> (\<G> \<union> {D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D < i})) \<subseteq> rel_frontier T \<and>
                     (\<forall>x \<in> \<Union>\<G>. g x = f x)"
       if "i \<le> aff_dim T" for i::nat
  using that
  proof (induction i)
    case 0 then show ?case
      apply (simp add: Union_empty_eq)
      apply (rule_tac x=f in exI)
      apply (intro conjI)
      using contf continuous_on_subset apply blast
      using fim apply blast
      by simp
  next
    case (Suc p)
    with \<open>bounded T\<close> have "rel_frontier T \<noteq> {}"
      by (auto simp: rel_frontier_eq_empty affine_bounded_eq_lowdim [of T])
    then obtain t where t: "t \<in> rel_frontier T" by auto
    have ple: "int p \<le> aff_dim T" using Suc.prems by force
    obtain h where conth: "continuous_on (\<Union>(\<G> \<union> {D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D < p})) h"
               and him: "h ` (\<Union> (\<G> \<union> {D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D < p}))
                         \<subseteq> rel_frontier T"
               and heq: "\<And>x. x \<in> \<Union>\<G> \<Longrightarrow> h x = f x"
      using Suc.IH [OF ple] by auto
    let ?Faces = "{D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D \<le> p}"
    have extendh: "\<exists>g. continuous_on D g \<and>
                       g ` D \<subseteq> rel_frontier T \<and>
                       (\<forall>x \<in> D \<inter> \<Union>(\<G> \<union> {D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D < p}). g x = h x)"
      if D: "D \<in> \<G> \<union> ?Faces" for D
    proof (cases "D \<subseteq> \<Union>(\<G> \<union> {D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D < p})")
      case True
      then show ?thesis
        apply (rule_tac x=h in exI)
        apply (intro conjI)
        apply (blast intro: continuous_on_subset [OF conth])
        using him apply blast
        by simp
    next
      case False
      note notDsub = False
      show ?thesis
      proof (cases "\<exists>a. D = {a}")
        case True
        then obtain a where "D = {a}" by auto
        with notDsub t show ?thesis
          by (rule_tac x="\<lambda>x. t" in exI) simp
      next
        case False
        have "D \<noteq> {}" using notDsub by auto
        have Dnotin: "D \<notin> \<G> \<union> {D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D < p}"
          using notDsub by auto
        then have "D \<notin> \<G>" by simp
        have "D \<in> ?Faces - {D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D < p}"
          using Dnotin that by auto
        then obtain C where "C \<in> \<F>" "D face_of C" and affD: "aff_dim D = int p"
          by auto
        then have "bounded D"
          using face_of_polytope_polytope poly polytope_imp_bounded by blast
        then have [simp]: "\<not> affine D"
          using affine_bounded_eq_trivial False \<open>D \<noteq> {}\<close> \<open>bounded D\<close> by blast
        have "{F. F facet_of D} \<subseteq> {E. E face_of C \<and> aff_dim E < int p}"
          apply clarify
          apply (metis \<open>D face_of C\<close> affD eq_iff face_of_trans facet_of_def zle_diff1_eq)
          done
        moreover have "polyhedron D"
          using \<open>C \<in> \<F>\<close> \<open>D face_of C\<close> face_of_polytope_polytope poly polytope_imp_polyhedron by auto
        ultimately have relf_sub: "rel_frontier D \<subseteq> \<Union> {E. E face_of C \<and> aff_dim E < p}"
          by (simp add: rel_frontier_of_polyhedron Union_mono)
        then have him_relf: "h ` rel_frontier D \<subseteq> rel_frontier T"
          using \<open>C \<in> \<F>\<close> him by blast
        have "convex D"
          by (simp add: \<open>polyhedron D\<close> polyhedron_imp_convex)
        have affD_lessT: "aff_dim D < aff_dim T"
          using Suc.prems affD by linarith
        have contDh: "continuous_on (rel_frontier D) h"
          using \<open>C \<in> \<F>\<close> relf_sub by (blast intro: continuous_on_subset [OF conth])
        then have *: "(\<exists>c. homotopic_with (\<lambda>x. True) (rel_frontier D) (rel_frontier T) h (\<lambda>x. c)) =
                      (\<exists>g. continuous_on UNIV g \<and>  range g \<subseteq> rel_frontier T \<and>
                           (\<forall>x\<in>rel_frontier D. g x = h x))"
          apply (rule nullhomotopic_into_rel_frontier_extension [OF closed_rel_frontier])
          apply (simp_all add: assms rel_frontier_eq_empty him_relf)
          done
        have "(\<exists>c. homotopic_with (\<lambda>x. True) (rel_frontier D)
              (rel_frontier T) h (\<lambda>x. c))"
          by (metis inessential_spheremap_lowdim_gen
                 [OF \<open>convex D\<close> \<open>bounded D\<close> \<open>convex T\<close> \<open>bounded T\<close> affD_lessT contDh him_relf])
        then obtain g where contg: "continuous_on UNIV g"
                        and gim: "range g \<subseteq> rel_frontier T"
                        and gh: "\<And>x. x \<in> rel_frontier D \<Longrightarrow> g x = h x"
          by (metis *)
        have "D \<inter> E \<subseteq> rel_frontier D"
             if "E \<in> \<G> \<union> {D. Bex \<F> (op face_of D) \<and> aff_dim D < int p}" for E
        proof (rule face_of_subset_rel_frontier)
          show "D \<inter> E face_of D"
            using that \<open>C \<in> \<F>\<close> \<open>D face_of C\<close> face
            apply auto
            apply (meson face_of_Int_subface \<open>\<G> \<subseteq> \<F>\<close> face_of_refl_eq poly polytope_imp_convex subsetD)
            using face_of_Int_subface apply blast
            done
          show "D \<inter> E \<noteq> D"
            using that notDsub by auto
        qed
        then show ?thesis
          apply (rule_tac x=g in exI)
          apply (intro conjI ballI)
            using continuous_on_subset contg apply blast
           using gim apply blast
          using gh by fastforce
      qed
    qed
    have intle: "i < 1 + int j \<longleftrightarrow> i \<le> int j" for i j
      by auto
    have "finite \<G>"
      using \<open>finite \<F>\<close> \<open>\<G> \<subseteq> \<F>\<close> rev_finite_subset by blast
    then have fin: "finite (\<G> \<union> ?Faces)"
      apply simp
      apply (rule_tac B = "\<Union>{{D. D face_of C}| C. C \<in> \<F>}" in finite_subset)
       by (auto simp: \<open>finite \<F>\<close> finite_polytope_faces poly)
    have clo: "closed S" if "S \<in> \<G> \<union> ?Faces" for S
      using that \<open>\<G> \<subseteq> \<F>\<close> face_of_polytope_polytope poly polytope_imp_closed by blast
    have K: "X \<inter> Y \<subseteq> \<Union>(\<G> \<union> {D. \<exists>C\<in>\<F>. D face_of C \<and> aff_dim D < int p})"
                if "X \<in> \<G> \<union> ?Faces" "Y \<in> \<G> \<union> ?Faces" "~ Y \<subseteq> X" for X Y
    proof -
      have ff: "X \<inter> Y face_of X \<and> X \<inter> Y face_of Y"
        if XY: "X face_of D" "Y face_of E" and DE: "D \<in> \<F>" "E \<in> \<F>" for D E
        apply (rule face_of_Int_subface [OF _ _ XY])
        apply (auto simp: face DE)
        done
      show ?thesis
        using that
        apply auto
        apply (drule_tac x="X \<inter> Y" in spec, safe)
        using ff face_of_imp_convex [of X] face_of_imp_convex [of Y]
        apply (fastforce dest: face_of_aff_dim_lt)
        by (meson face_of_trans ff)
    qed
    obtain g where "continuous_on (\<Union>(\<G> \<union> ?Faces)) g"
                   "g ` \<Union>(\<G> \<union> ?Faces) \<subseteq> rel_frontier T"
                   "(\<forall>x \<in> \<Union>(\<G> \<union> ?Faces) \<inter>
                          \<Union>(\<G> \<union> {D. \<exists>C\<in>\<F>. D face_of C \<and> aff_dim D < p}). g x = h x)"
      apply (rule exE [OF extending_maps_Union [OF fin extendh clo K]], blast+)
      done
    then show ?case
      apply (simp add: intle local.heq [symmetric], blast)
      done
  qed
  have eq: "\<Union>(\<G> \<union> {D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D < i}) = \<Union>\<F>"
  proof
    show "\<Union>(\<G> \<union> {D. \<exists>C\<in>\<F>. D face_of C \<and> aff_dim D < int i}) \<subseteq> \<Union>\<F>"
      apply (rule Union_subsetI)
      using \<open>\<G> \<subseteq> \<F>\<close> face_of_imp_subset  apply force
      done
    show "\<Union>\<F> \<subseteq> \<Union>(\<G> \<union> {D. \<exists>C\<in>\<F>. D face_of C \<and> aff_dim D < i})"
      apply (rule Union_mono)
      using face  apply (fastforce simp: aff i)
      done
  qed
  have "int i \<le> aff_dim T" by (simp add: i)
  then show ?thesis
    using extendf [of i] unfolding eq by (metis that)
qed

lemma extend_map_lemma_cofinite0:
  assumes "finite \<F>"
      and "pairwise (\<lambda>S T. S \<inter> T \<subseteq> K) \<F>"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>a g. a \<notin> U \<and> continuous_on (S - {a}) g \<and> g ` (S - {a}) \<subseteq> T \<and> (\<forall>x \<in> S \<inter> K. g x = h x)"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> closed S"
    shows "\<exists>C g. finite C \<and> disjnt C U \<and> card C \<le> card \<F> \<and>
                 continuous_on (\<Union>\<F> - C) g \<and> g ` (\<Union>\<F> - C) \<subseteq> T
                  \<and> (\<forall>x \<in> (\<Union>\<F> - C) \<inter> K. g x = h x)"
  using assms
proof induction
  case empty then show ?case
    by force
next
  case (insert X \<F>)
  then have "closed X" and clo: "\<And>X. X \<in> \<F> \<Longrightarrow> closed X"
        and \<F>: "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>a g. a \<notin> U \<and> continuous_on (S - {a}) g \<and> g ` (S - {a}) \<subseteq> T \<and> (\<forall>x \<in> S \<inter> K. g x = h x)"
        and pwX: "\<And>Y. Y \<in> \<F> \<and> Y \<noteq> X \<longrightarrow> X \<inter> Y \<subseteq> K \<and> Y \<inter> X \<subseteq> K"
        and pwF: "pairwise (\<lambda> S T. S \<inter> T \<subseteq> K) \<F>"
    by (simp_all add: pairwise_insert)
  obtain C g where C: "finite C" "disjnt C U" "card C \<le> card \<F>"
               and contg: "continuous_on (\<Union>\<F> - C) g"
               and gim: "g ` (\<Union>\<F> - C) \<subseteq> T"
               and gh:  "\<And>x. x \<in> (\<Union>\<F> - C) \<inter> K \<Longrightarrow> g x = h x"
    using insert.IH [OF pwF \<F> clo] by auto
  obtain a f where "a \<notin> U"
               and contf: "continuous_on (X - {a}) f"
               and fim: "f ` (X - {a}) \<subseteq> T"
               and fh: "(\<forall>x \<in> X \<inter> K. f x = h x)"
    using insert.prems by (meson insertI1)
  show ?case
  proof (intro exI conjI)
    show "finite (insert a C)"
      by (simp add: C)
    show "disjnt (insert a C) U"
      using C \<open>a \<notin> U\<close> by simp
    show "card (insert a C) \<le> card (insert X \<F>)"
      by (simp add: C card_insert_if insert.hyps le_SucI)
    have "closed (\<Union>\<F>)"
      using clo insert.hyps by blast
    have "continuous_on (X - insert a C \<union> (\<Union>\<F> - insert a C)) (\<lambda>x. if x \<in> X then f x else g x)"
       apply (rule continuous_on_cases_local)
          apply (simp_all add: closedin_closed)
        using \<open>closed X\<close> apply blast
        using \<open>closed (\<Union>\<F>)\<close> apply blast
        using contf apply (force simp: elim: continuous_on_subset)
        using contg apply (force simp: elim: continuous_on_subset)
        using fh gh insert.hyps pwX by fastforce
    then show "continuous_on (\<Union>insert X \<F> - insert a C) (\<lambda>a. if a \<in> X then f a else g a)"
      by (blast intro: continuous_on_subset)
    show "\<forall>x\<in>(\<Union>insert X \<F> - insert a C) \<inter> K. (if x \<in> X then f x else g x) = h x"
      using gh by (auto simp: fh)
    show "(\<lambda>a. if a \<in> X then f a else g a) ` (\<Union>insert X \<F> - insert a C) \<subseteq> T"
      using fim gim by auto force
  qed
qed


lemma extend_map_lemma_cofinite1:
assumes "finite \<F>"
    and \<F>: "\<And>X. X \<in> \<F> \<Longrightarrow> \<exists>a g. a \<notin> U \<and> continuous_on (X - {a}) g \<and> g ` (X - {a}) \<subseteq> T \<and> (\<forall>x \<in> X \<inter> K. g x = h x)"
    and clo: "\<And>X. X \<in> \<F> \<Longrightarrow> closed X"
    and K: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>; ~(X \<subseteq> Y); ~(Y \<subseteq> X)\<rbrakk> \<Longrightarrow> X \<inter> Y \<subseteq> K"
  obtains C g where "finite C" "disjnt C U" "card C \<le> card \<F>" "continuous_on (\<Union>\<F> - C) g"
                    "g ` (\<Union>\<F> - C) \<subseteq> T"
                    "\<And>x. x \<in> (\<Union>\<F> - C) \<inter> K \<Longrightarrow> g x = h x"
proof -
  let ?\<F> = "{X \<in> \<F>. \<forall>Y\<in>\<F>. \<not> X \<subset> Y}"
  have [simp]: "\<Union>?\<F> = \<Union>\<F>"
    by (simp add: Union_maximal_sets assms)
  have fin: "finite ?\<F>"
    by (force intro: finite_subset [OF _ \<open>finite \<F>\<close>])
  have pw: "pairwise (\<lambda> S T. S \<inter> T \<subseteq> K) ?\<F>"
    by (simp add: pairwise_def) (metis K psubsetI)
  have "card {X \<in> \<F>. \<forall>Y\<in>\<F>. \<not> X \<subset> Y} \<le> card \<F>"
    by (simp add: \<open>finite \<F>\<close> card_mono)
  moreover
  obtain C g where "finite C \<and> disjnt C U \<and> card C \<le> card ?\<F> \<and>
                 continuous_on (\<Union>?\<F> - C) g \<and> g ` (\<Union>?\<F> - C) \<subseteq> T
                  \<and> (\<forall>x \<in> (\<Union>?\<F> - C) \<inter> K. g x = h x)"
    apply (rule exE [OF extend_map_lemma_cofinite0 [OF fin pw, of U T h]])
      apply (fastforce intro!:  clo \<F>)+
    done
  ultimately show ?thesis
    by (rule_tac C=C and g=g in that) auto
qed


lemma extend_map_lemma_cofinite:
  assumes "finite \<F>" "\<G> \<subseteq> \<F>" and T: "convex T" "bounded T"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and contf: "continuous_on (\<Union>\<G>) f" and fim: "f ` (\<Union>\<G>) \<subseteq> rel_frontier T"
      and face: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> (X \<inter> Y) face_of X \<and> (X \<inter> Y) face_of Y"
      and aff: "\<And>X. X \<in> \<F> - \<G> \<Longrightarrow> aff_dim X \<le> aff_dim T"
  obtains C g where
     "finite C" "disjnt C (\<Union>\<G>)" "card C \<le> card \<F>" "continuous_on (\<Union>\<F> - C) g"
     "g ` (\<Union> \<F> - C) \<subseteq> rel_frontier T" "\<And>x. x \<in> \<Union>\<G> \<Longrightarrow> g x = f x"
proof -
  define \<H> where "\<H> \<equiv> \<G> \<union> {D. \<exists>C \<in> \<F> - \<G>. D face_of C \<and> aff_dim D < aff_dim T}"
  have "finite \<G>"
    using assms finite_subset by blast
  moreover have "finite (\<Union>{{D. D face_of C} |C. C \<in> \<F>})"
    apply (rule finite_Union)
     apply (simp add: \<open>finite \<F>\<close>)
    using finite_polytope_faces poly by auto
  ultimately have "finite \<H>"
    apply (simp add: \<H>_def)
    apply (rule finite_subset [of _ "\<Union> {{D. D face_of C} | C. C \<in> \<F>}"], auto)
    done
  have *: "\<And>X Y. \<lbrakk>X \<in> \<H>; Y \<in> \<H>\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X \<and> X \<inter> Y face_of Y"
    unfolding \<H>_def
    apply (elim UnE bexE CollectE DiffE)
    using subsetD [OF \<open>\<G> \<subseteq> \<F>\<close>] apply (simp_all add: face)
      apply (meson subsetD [OF \<open>\<G> \<subseteq> \<F>\<close>] face face_of_Int_subface face_of_imp_subset face_of_refl poly polytope_imp_convex)+
    done
  obtain h where conth: "continuous_on (\<Union>\<H>) h" and him: "h ` (\<Union>\<H>) \<subseteq> rel_frontier T"
             and hf: "\<And>x. x \<in> \<Union>\<G> \<Longrightarrow> h x = f x"
    using \<open>finite \<H>\<close>
    unfolding \<H>_def
    apply (rule extend_map_lemma [OF _ Un_upper1 T _ _ _ contf fim])
    using \<open>\<G> \<subseteq> \<F>\<close> face_of_polytope_polytope poly apply fastforce
    using * apply (auto simp: \<H>_def)
    done
  have "bounded (\<Union>\<G>)"
    using \<open>finite \<G>\<close> \<open>\<G> \<subseteq> \<F>\<close> poly polytope_imp_bounded by blast
  then have "\<Union>\<G> \<noteq> UNIV"
    by auto
  then obtain a where a: "a \<notin> \<Union>\<G>"
    by blast
  have \<F>: "\<exists>a g. a \<notin> \<Union>\<G> \<and> continuous_on (D - {a}) g \<and>
                  g ` (D - {a}) \<subseteq> rel_frontier T \<and> (\<forall>x \<in> D \<inter> \<Union>\<H>. g x = h x)"
       if "D \<in> \<F>" for D
  proof (cases "D \<subseteq> \<Union>\<H>")
    case True
    then show ?thesis
      apply (rule_tac x=a in exI)
      apply (rule_tac x=h in exI)
      using him apply (blast intro!: \<open>a \<notin> \<Union>\<G>\<close> continuous_on_subset [OF conth]) +
      done
  next
    case False
    note D_not_subset = False
    show ?thesis
    proof (cases "D \<in> \<G>")
      case True
      with D_not_subset show ?thesis
        by (auto simp: \<H>_def)
    next
      case False
      then have affD: "aff_dim D \<le> aff_dim T"
        by (simp add: \<open>D \<in> \<F>\<close> aff)
      show ?thesis
      proof (cases "rel_interior D = {}")
        case True
        with \<open>D \<in> \<F>\<close> poly a show ?thesis
          by (force simp: rel_interior_eq_empty polytope_imp_convex)
      next
        case False
        then obtain b where brelD: "b \<in> rel_interior D"
          by blast
        have "polyhedron D"
          by (simp add: poly polytope_imp_polyhedron that)
        have "rel_frontier D retract_of affine hull D - {b}"
          by (simp add: rel_frontier_retract_of_punctured_affine_hull poly polytope_imp_bounded polytope_imp_convex that brelD)
        then obtain r where relfD: "rel_frontier D \<subseteq> affine hull D - {b}"
                        and contr: "continuous_on (affine hull D - {b}) r"
                        and rim: "r ` (affine hull D - {b}) \<subseteq> rel_frontier D"
                        and rid: "\<And>x. x \<in> rel_frontier D \<Longrightarrow> r x = x"
          by (auto simp: retract_of_def retraction_def)
        show ?thesis
        proof (intro exI conjI ballI)
          show "b \<notin> \<Union>\<G>"
          proof clarify
            fix E
            assume "b \<in> E" "E \<in> \<G>"
            then have "E \<inter> D face_of E \<and> E \<inter> D face_of D"
              using \<open>\<G> \<subseteq> \<F>\<close> face that by auto
            with face_of_subset_rel_frontier \<open>E \<in> \<G>\<close> \<open>b \<in> E\<close> brelD rel_interior_subset [of D]
                 D_not_subset rel_frontier_def \<H>_def
            show False
              by blast
          qed
          have "r ` (D - {b}) \<subseteq> r ` (affine hull D - {b})"
            by (simp add: Diff_mono hull_subset image_mono)
          also have "... \<subseteq> rel_frontier D"
            by (rule rim)
          also have "... \<subseteq> \<Union>{E. E face_of D \<and> aff_dim E < aff_dim T}"
            using affD
            by (force simp: rel_frontier_of_polyhedron [OF \<open>polyhedron D\<close>] facet_of_def)
          also have "... \<subseteq> \<Union>(\<H>)"
            using D_not_subset \<H>_def that by fastforce
          finally have rsub: "r ` (D - {b}) \<subseteq> \<Union>(\<H>)" .
          show "continuous_on (D - {b}) (h \<circ> r)"
            apply (intro conjI \<open>b \<notin> \<Union>\<G>\<close> continuous_on_compose)
               apply (rule continuous_on_subset [OF contr])
            apply (simp add: Diff_mono hull_subset)
            apply (rule continuous_on_subset [OF conth rsub])
            done
          show "(h \<circ> r) ` (D - {b}) \<subseteq> rel_frontier T"
            using brelD him rsub by fastforce
          show "(h \<circ> r) x = h x" if x: "x \<in> D \<inter> \<Union>\<H>" for x
          proof -
            consider A where "x \<in> D" "A \<in> \<G>" "x \<in> A"
                 | A B where "x \<in> D" "A face_of B" "B \<in> \<F>" "B \<notin> \<G>" "aff_dim A < aff_dim T" "x \<in> A"
              using x by (auto simp: \<H>_def)
            then have xrel: "x \<in> rel_frontier D"
            proof cases
              case 1 show ?thesis
              proof (rule face_of_subset_rel_frontier [THEN subsetD])
                show "D \<inter> A face_of D"
                  using \<open>A \<in> \<G>\<close> \<open>\<G> \<subseteq> \<F>\<close> face \<open>D \<in> \<F>\<close> by blast
                show "D \<inter> A \<noteq> D"
                  using \<open>A \<in> \<G>\<close> D_not_subset \<H>_def by blast
              qed (auto simp: 1)
            next
              case 2 show ?thesis
              proof (rule face_of_subset_rel_frontier [THEN subsetD])
                show "D \<inter> A face_of D"
                  apply (rule face_of_Int_subface [of D B _ A, THEN conjunct1])
                     apply (simp_all add: 2 \<open>D \<in> \<F>\<close> face)
                   apply (simp add: \<open>polyhedron D\<close> polyhedron_imp_convex face_of_refl)
                  done
                show "D \<inter> A \<noteq> D"
                  using "2" D_not_subset \<H>_def by blast
              qed (auto simp: 2)
            qed
            show ?thesis
              by (simp add: rid xrel)
          qed
        qed
      qed
    qed
  qed
  have clo: "\<And>S. S \<in> \<F> \<Longrightarrow> closed S"
    by (simp add: poly polytope_imp_closed)
  obtain C g where "finite C" "disjnt C (\<Union>\<G>)" "card C \<le> card \<F>" "continuous_on (\<Union>\<F> - C) g"
                   "g ` (\<Union>\<F> - C) \<subseteq> rel_frontier T"
               and gh: "\<And>x. x \<in> (\<Union>\<F> - C) \<inter> \<Union>\<H> \<Longrightarrow> g x = h x"
  proof (rule extend_map_lemma_cofinite1 [OF \<open>finite \<F>\<close> \<F> clo])
    show "X \<inter> Y \<subseteq> \<Union>\<H>" if XY: "X \<in> \<F>" "Y \<in> \<F>" and "\<not> X \<subseteq> Y" "\<not> Y \<subseteq> X" for X Y
    proof (cases "X \<in> \<G>")
      case True
      then show ?thesis
        by (auto simp: \<H>_def)
    next
      case False
      have "X \<inter> Y \<noteq> X"
        using \<open>\<not> X \<subseteq> Y\<close> by blast
      with XY
      show ?thesis
        by (clarsimp simp: \<H>_def)
           (metis Diff_iff Int_iff aff antisym_conv face face_of_aff_dim_lt face_of_refl
                  not_le poly polytope_imp_convex)
    qed
  qed (blast)+
  with \<open>\<G> \<subseteq> \<F>\<close> show ?thesis
    apply (rule_tac C=C and g=g in that)
     apply (auto simp: disjnt_def hf [symmetric] \<H>_def intro!: gh)
    done
qed

text\<open>The next two proofs are similar\<close>
theorem extend_map_cell_complex_to_sphere:
  assumes "finite \<F>" and S: "S \<subseteq> \<Union>\<F>" "closed S" and T: "convex T" "bounded T"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and aff: "\<And>X. X \<in> \<F> \<Longrightarrow> aff_dim X < aff_dim T"
      and face: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> (X \<inter> Y) face_of X \<and> (X \<inter> Y) face_of Y"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> rel_frontier T"
  obtains g where "continuous_on (\<Union>\<F>) g"
     "g ` (\<Union>\<F>) \<subseteq> rel_frontier T" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  obtain V g where "S \<subseteq> V" "open V" "continuous_on V g" and gim: "g ` V \<subseteq> rel_frontier T" and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    using neighbourhood_extension_into_ANR [OF contf fim _ \<open>closed S\<close>] ANR_rel_frontier_convex T by blast
  have "compact S"
    by (meson assms compact_Union poly polytope_imp_compact seq_compact_closed_subset seq_compact_eq_compact)
  then obtain d where "d > 0" and d: "\<And>x y. \<lbrakk>x \<in> S; y \<in> - V\<rbrakk> \<Longrightarrow> d \<le> dist x y"
    using separate_compact_closed [of S "-V"] \<open>open V\<close> \<open>S \<subseteq> V\<close> by force
  obtain \<G> where "finite \<G>" "\<Union>\<G> = \<Union>\<F>"
             and diaG: "\<And>X. X \<in> \<G> \<Longrightarrow> diameter X < d"
             and polyG: "\<And>X. X \<in> \<G> \<Longrightarrow> polytope X"
             and affG: "\<And>X. X \<in> \<G> \<Longrightarrow> aff_dim X \<le> aff_dim T - 1"
             and faceG: "\<And>X Y. \<lbrakk>X \<in> \<G>; Y \<in> \<G>\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X \<and> X \<inter> Y face_of Y"
  proof (rule cell_complex_subdivision_exists [OF \<open>d>0\<close> \<open>finite \<F>\<close> poly _ face])
    show "\<And>X. X \<in> \<F> \<Longrightarrow> aff_dim X \<le> aff_dim T - 1"
      by (simp add: aff)
  qed auto
  obtain h where conth: "continuous_on (\<Union>\<G>) h" and him: "h ` \<Union>\<G> \<subseteq> rel_frontier T" and hg: "\<And>x. x \<in> \<Union>(\<G> \<inter> Pow V) \<Longrightarrow> h x = g x"
  proof (rule extend_map_lemma [of \<G> "\<G> \<inter> Pow V" T g])
    show "continuous_on (\<Union>(\<G> \<inter> Pow V)) g"
      by (metis Union_Int_subset Union_Pow_eq \<open>continuous_on V g\<close> continuous_on_subset le_inf_iff)
  qed (use \<open>finite \<G>\<close> T polyG affG faceG gim in fastforce)+
  show ?thesis
  proof
    show "continuous_on (\<Union>\<F>) h"
      using \<open>\<Union>\<G> = \<Union>\<F>\<close> conth by auto
    show "h ` \<Union>\<F> \<subseteq> rel_frontier T"
      using \<open>\<Union>\<G> = \<Union>\<F>\<close> him by auto
    show "h x = f x" if "x \<in> S" for x
    proof -
      have "x \<in> \<Union>\<G>"
        using \<open>\<Union>\<G> = \<Union>\<F>\<close> \<open>S \<subseteq> \<Union>\<F>\<close> that by auto
      then obtain X where "x \<in> X" "X \<in> \<G>" by blast
      then have "diameter X < d" "bounded X"
        by (auto simp: diaG \<open>X \<in> \<G>\<close> polyG polytope_imp_bounded)
      then have "X \<subseteq> V" using d [OF \<open>x \<in> S\<close>] diameter_bounded_bound [OF \<open>bounded X\<close> \<open>x \<in> X\<close>]
        by fastforce
      have "h x = g x"
        apply (rule hg)
        using \<open>X \<in> \<G>\<close> \<open>X \<subseteq> V\<close> \<open>x \<in> X\<close> by blast
      also have "... = f x"
        by (simp add: gf that)
      finally show "h x = f x" .
    qed
  qed
qed


theorem extend_map_cell_complex_to_sphere_cofinite:
  assumes "finite \<F>" and S: "S \<subseteq> \<Union>\<F>" "closed S" and T: "convex T" "bounded T"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and aff: "\<And>X. X \<in> \<F> \<Longrightarrow> aff_dim X \<le> aff_dim T"
      and face: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> (X \<inter> Y) face_of X \<and> (X \<inter> Y) face_of Y"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> rel_frontier T"
  obtains C g where "finite C" "disjnt C S" "continuous_on (\<Union>\<F> - C) g"
     "g ` (\<Union>\<F> - C) \<subseteq> rel_frontier T" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  obtain V g where "S \<subseteq> V" "open V" "continuous_on V g" and gim: "g ` V \<subseteq> rel_frontier T" and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    using neighbourhood_extension_into_ANR [OF contf fim _ \<open>closed S\<close>] ANR_rel_frontier_convex T by blast
  have "compact S"
    by (meson assms compact_Union poly polytope_imp_compact seq_compact_closed_subset seq_compact_eq_compact)
  then obtain d where "d > 0" and d: "\<And>x y. \<lbrakk>x \<in> S; y \<in> - V\<rbrakk> \<Longrightarrow> d \<le> dist x y"
    using separate_compact_closed [of S "-V"] \<open>open V\<close> \<open>S \<subseteq> V\<close> by force
  obtain \<G> where "finite \<G>" "\<Union>\<G> = \<Union>\<F>"
             and diaG: "\<And>X. X \<in> \<G> \<Longrightarrow> diameter X < d"
             and polyG: "\<And>X. X \<in> \<G> \<Longrightarrow> polytope X"
             and affG: "\<And>X. X \<in> \<G> \<Longrightarrow> aff_dim X \<le> aff_dim T"
             and faceG: "\<And>X Y. \<lbrakk>X \<in> \<G>; Y \<in> \<G>\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X \<and> X \<inter> Y face_of Y"
    by (rule cell_complex_subdivision_exists [OF \<open>d>0\<close> \<open>finite \<F>\<close> poly aff face]) auto
  obtain C h where "finite C" and dis: "disjnt C (\<Union>(\<G> \<inter> Pow V))"
               and card: "card C \<le> card \<G>" and conth: "continuous_on (\<Union>\<G> - C) h"
               and him: "h ` (\<Union>\<G> - C) \<subseteq> rel_frontier T"
               and hg: "\<And>x. x \<in> \<Union>(\<G> \<inter> Pow V) \<Longrightarrow> h x = g x"
  proof (rule extend_map_lemma_cofinite [of \<G> "\<G> \<inter> Pow V" T g])
    show "continuous_on (\<Union>(\<G> \<inter> Pow V)) g"
      by (metis Union_Int_subset Union_Pow_eq \<open>continuous_on V g\<close> continuous_on_subset le_inf_iff)
    show "g ` \<Union>(\<G> \<inter> Pow V) \<subseteq> rel_frontier T"
      using gim by force
  qed (auto intro: \<open>finite \<G>\<close> T polyG affG dest: faceG)
  have Ssub: "S \<subseteq> \<Union>(\<G> \<inter> Pow V)"
  proof
    fix x
    assume "x \<in> S"
    then have "x \<in> \<Union>\<G>"
      using \<open>\<Union>\<G> = \<Union>\<F>\<close> \<open>S \<subseteq> \<Union>\<F>\<close> by auto
    then obtain X where "x \<in> X" "X \<in> \<G>" by blast
    then have "diameter X < d" "bounded X"
      by (auto simp: diaG \<open>X \<in> \<G>\<close> polyG polytope_imp_bounded)
    then have "X \<subseteq> V" using d [OF \<open>x \<in> S\<close>] diameter_bounded_bound [OF \<open>bounded X\<close> \<open>x \<in> X\<close>]
      by fastforce
    then show "x \<in> \<Union>(\<G> \<inter> Pow V)"
      using \<open>X \<in> \<G>\<close> \<open>x \<in> X\<close> by blast
  qed
  show ?thesis
  proof
    show "continuous_on (\<Union>\<F>-C) h"
      using \<open>\<Union>\<G> = \<Union>\<F>\<close> conth by auto
    show "h ` (\<Union>\<F> - C) \<subseteq> rel_frontier T"
      using \<open>\<Union>\<G> = \<Union>\<F>\<close> him by auto
    show "h x = f x" if "x \<in> S" for x
    proof -
      have "h x = g x"
        apply (rule hg)
        using Ssub that by blast
      also have "... = f x"
        by (simp add: gf that)
      finally show "h x = f x" .
    qed
    show "disjnt C S"
      using dis Ssub  by (meson disjnt_iff subset_eq)
  qed (intro \<open>finite C\<close>)
qed



subsection\<open> Special cases and corollaries involving spheres.\<close>

lemma disjnt_Diff1: "X \<subseteq> Y' \<Longrightarrow> disjnt (X - Y) (X' - Y')"
  by (auto simp: disjnt_def)

proposition extend_map_affine_to_sphere_cofinite_simple:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "compact S" "convex U" "bounded U"
      and aff: "aff_dim T \<le> aff_dim U"
      and "S \<subseteq> T" and contf: "continuous_on S f"
      and fim: "f ` S \<subseteq> rel_frontier U"
 obtains K g where "finite K" "K \<subseteq> T" "disjnt K S" "continuous_on (T - K) g"
                   "g ` (T - K) \<subseteq> rel_frontier U"
                   "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  have "\<exists>K g. finite K \<and> disjnt K S \<and> continuous_on (T - K) g \<and>
              g ` (T - K) \<subseteq> rel_frontier U \<and> (\<forall>x \<in> S. g x = f x)"
       if "affine T" "S \<subseteq> T" and aff: "aff_dim T \<le> aff_dim U"  for T
  proof (cases "S = {}")
    case True
    show ?thesis
    proof (cases "rel_frontier U = {}")
      case True
      with \<open>bounded U\<close> have "aff_dim U \<le> 0"
        using affine_bounded_eq_lowdim rel_frontier_eq_empty by auto
      with aff have "aff_dim T \<le> 0" by auto
      then obtain a where "T \<subseteq> {a}"
        using \<open>affine T\<close> affine_bounded_eq_lowdim affine_bounded_eq_trivial by auto
      then show ?thesis
        using \<open>S = {}\<close> fim
        by (metis Diff_cancel contf disjnt_empty2 finite.emptyI finite_insert finite_subset)
    next
      case False
      then obtain a where "a \<in> rel_frontier U"
        by auto
      then show ?thesis
        using continuous_on_const [of _ a] \<open>S = {}\<close> by force
    qed
  next
    case False
    have "bounded S"
      by (simp add: \<open>compact S\<close> compact_imp_bounded)
    then obtain b where b: "S \<subseteq> cbox (-b) b"
      using bounded_subset_cbox_symmetric by blast
    define bbox where "bbox \<equiv> cbox (-(b+One)) (b+One)"
    have "cbox (-b) b \<subseteq> bbox"
      by (auto simp: bbox_def algebra_simps intro!: subset_box_imp)
    with b \<open>S \<subseteq> T\<close> have "S \<subseteq> bbox \<inter> T"
      by auto
    then have Ssub: "S \<subseteq> \<Union>{bbox \<inter> T}"
      by auto
    then have "aff_dim (bbox \<inter> T) \<le> aff_dim U"
      by (metis aff aff_dim_subset inf_commute inf_le1 order_trans)
    obtain K g where K: "finite K" "disjnt K S"
                 and contg: "continuous_on (\<Union>{bbox \<inter> T} - K) g"
                 and gim: "g ` (\<Union>{bbox \<inter> T} - K) \<subseteq> rel_frontier U"
                 and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    proof (rule extend_map_cell_complex_to_sphere_cofinite
              [OF _ Ssub _ \<open>convex U\<close> \<open>bounded U\<close> _ _ _ contf fim])
      show "closed S"
        using \<open>compact S\<close> compact_eq_bounded_closed by auto
      show poly: "\<And>X. X \<in> {bbox \<inter> T} \<Longrightarrow> polytope X"
        by (simp add: polytope_Int_polyhedron bbox_def polytope_interval affine_imp_polyhedron \<open>affine T\<close>)
      show "\<And>X Y. \<lbrakk>X \<in> {bbox \<inter> T}; Y \<in> {bbox \<inter> T}\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X \<and> X \<inter> Y face_of Y"
        by (simp add:poly face_of_refl polytope_imp_convex)
      show "\<And>X. X \<in> {bbox \<inter> T} \<Longrightarrow> aff_dim X \<le> aff_dim U"
        by (simp add: \<open>aff_dim (bbox \<inter> T) \<le> aff_dim U\<close>)
    qed auto
    define fro where "fro \<equiv> \<lambda>d. frontier(cbox (-(b + d *\<^sub>R One)) (b + d *\<^sub>R One))"
    obtain d where d12: "1/2 \<le> d" "d \<le> 1" and dd: "disjnt K (fro d)"
    proof (rule disjoint_family_elem_disjnt [OF _ \<open>finite K\<close>])
      show "infinite {1/2..1::real}"
        by (simp add: infinite_Icc)
      have dis1: "disjnt (fro x) (fro y)" if "x<y" for x y
        by (auto simp: algebra_simps that subset_box_imp disjnt_Diff1 frontier_def fro_def)
      then show "disjoint_family_on fro {1/2..1}"
        by (auto simp: disjoint_family_on_def disjnt_def neq_iff)
    qed auto
    define c where "c \<equiv> b + d *\<^sub>R One"
    have cbsub: "cbox (-b) b \<subseteq> box (-c) c"  "cbox (-b) b \<subseteq> cbox (-c) c"  "cbox (-c) c \<subseteq> bbox"
      using d12 by (auto simp: algebra_simps subset_box_imp c_def bbox_def)
    have clo_cbT: "closed (cbox (- c) c \<inter> T)"
      by (simp add: affine_closed closed_Int closed_cbox \<open>affine T\<close>)
    have cpT_ne: "cbox (- c) c \<inter> T \<noteq> {}"
      using \<open>S \<noteq> {}\<close> b cbsub(2) \<open>S \<subseteq> T\<close> by fastforce
    have "closest_point (cbox (- c) c \<inter> T) x \<notin> K" if "x \<in> T" "x \<notin> K" for x
    proof (cases "x \<in> cbox (-c) c")
      case True with that show ?thesis
        by (simp add: closest_point_self)
    next
      case False
      have int_ne: "interior (cbox (-c) c) \<inter> T \<noteq> {}"
        using \<open>S \<noteq> {}\<close> \<open>S \<subseteq> T\<close> b \<open>cbox (- b) b \<subseteq> box (- c) c\<close> by force
      have "convex T"
        by (meson \<open>affine T\<close> affine_imp_convex)
      then have "x \<in> affine hull (cbox (- c) c \<inter> T)"
          by (metis Int_commute Int_iff \<open>S \<noteq> {}\<close> \<open>S \<subseteq> T\<close> cbsub(1) \<open>x \<in> T\<close> affine_hull_convex_Int_nonempty_interior all_not_in_conv b hull_inc inf.orderE interior_cbox)
      then have "x \<in> affine hull (cbox (- c) c \<inter> T) - rel_interior (cbox (- c) c \<inter> T)"
        by (meson DiffI False Int_iff rel_interior_subset subsetCE)
      then have "closest_point (cbox (- c) c \<inter> T) x \<in> rel_frontier (cbox (- c) c \<inter> T)"
        by (rule closest_point_in_rel_frontier [OF clo_cbT cpT_ne])
      moreover have "(rel_frontier (cbox (- c) c \<inter> T)) \<subseteq> fro d"
        apply (subst convex_affine_rel_frontier_Int [OF _  \<open>affine T\<close> int_ne])
         apply (auto simp: fro_def c_def)
        done
      ultimately show ?thesis
        using dd  by (force simp: disjnt_def)
    qed
    then have cpt_subset: "closest_point (cbox (- c) c \<inter> T) ` (T - K) \<subseteq> \<Union>{bbox \<inter> T} - K"
      using closest_point_in_set [OF clo_cbT cpT_ne] cbsub(3) by force
    show ?thesis
    proof (intro conjI ballI exI)
      have "continuous_on (T - K) (closest_point (cbox (- c) c \<inter> T))"
        apply (rule continuous_on_closest_point)
        using \<open>S \<noteq> {}\<close> cbsub(2) b that
        by (auto simp: affine_imp_convex convex_Int affine_closed closed_Int closed_cbox \<open>affine T\<close>)
      then show "continuous_on (T - K) (g \<circ> closest_point (cbox (- c) c \<inter> T))"
        by (metis continuous_on_compose continuous_on_subset [OF contg cpt_subset])
      have "(g \<circ> closest_point (cbox (- c) c \<inter> T)) ` (T - K) \<subseteq> g ` (\<Union>{bbox \<inter> T} - K)"
        by (metis image_comp image_mono cpt_subset)
      also have "... \<subseteq> rel_frontier U"
        by (rule gim)
      finally show "(g \<circ> closest_point (cbox (- c) c \<inter> T)) ` (T - K) \<subseteq> rel_frontier U" .
      show "(g \<circ> closest_point (cbox (- c) c \<inter> T)) x = f x" if "x \<in> S" for x
      proof -
        have "(g \<circ> closest_point (cbox (- c) c \<inter> T)) x = g x"
          unfolding o_def
          by (metis IntI \<open>S \<subseteq> T\<close> b cbsub(2) closest_point_self subset_eq that)
        also have "... = f x"
          by (simp add: that gf)
        finally show ?thesis .
      qed
    qed (auto simp: K)
  qed
  then obtain K g where "finite K" "disjnt K S"
               and contg: "continuous_on (affine hull T - K) g"
               and gim:  "g ` (affine hull T - K) \<subseteq> rel_frontier U"
               and gf:   "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    by (metis aff affine_affine_hull aff_dim_affine_hull
              order_trans [OF \<open>S \<subseteq> T\<close> hull_subset [of T affine]])
  then obtain K g where "finite K" "disjnt K S"
               and contg: "continuous_on (T - K) g"
               and gim:  "g ` (T - K) \<subseteq> rel_frontier U"
               and gf:   "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    by (rule_tac K=K and g=g in that) (auto simp: hull_inc elim: continuous_on_subset)
  then show ?thesis
    by (rule_tac K="K \<inter> T" and g=g in that) (auto simp: disjnt_iff Diff_Int contg)
qed

subsection\<open>Extending maps to spheres\<close>

(*Up to extend_map_affine_to_sphere_cofinite_gen*)

lemma closedin_closed_subset:
 "\<lbrakk>closedin (subtopology euclidean U) V; T \<subseteq> U; S = V \<inter> T\<rbrakk>
             \<Longrightarrow> closedin (subtopology euclidean T) S"
  by (metis (no_types, lifting) Int_assoc Int_commute closedin_closed inf.orderE)

lemma extend_map_affine_to_sphere1:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::topological_space"
  assumes "finite K" "affine U" and contf: "continuous_on (U - K) f"
      and fim: "f ` (U - K) \<subseteq> T"
      and comps: "\<And>C. \<lbrakk>C \<in> components(U - S); C \<inter> K \<noteq> {}\<rbrakk> \<Longrightarrow> C \<inter> L \<noteq> {}"
      and clo: "closedin (subtopology euclidean U) S" and K: "disjnt K S" "K \<subseteq> U"
  obtains g where "continuous_on (U - L) g" "g ` (U - L) \<subseteq> T" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof (cases "K = {}")
  case True
  then show ?thesis
    by (metis Diff_empty Diff_subset contf fim continuous_on_subset image_subsetI rev_image_eqI subset_iff that)
next
  case False
  have "S \<subseteq> U"
    using clo closedin_limpt by blast
  then have "(U - S) \<inter> K \<noteq> {}"
    by (metis Diff_triv False Int_Diff K disjnt_def inf.absorb_iff2 inf_commute)
  then have "\<Union>(components (U - S)) \<inter> K \<noteq> {}"
    using Union_components by simp
  then obtain C0 where C0: "C0 \<in> components (U - S)" "C0 \<inter> K \<noteq> {}"
    by blast
  have "convex U"
    by (simp add: affine_imp_convex \<open>affine U\<close>)
  then have "locally connected U"
    by (rule convex_imp_locally_connected)
  have "\<exists>a g. a \<in> C \<and> a \<in> L \<and> continuous_on (S \<union> (C - {a})) g \<and>
              g ` (S \<union> (C - {a})) \<subseteq> T \<and> (\<forall>x \<in> S. g x = f x)"
       if C: "C \<in> components (U - S)" and CK: "C \<inter> K \<noteq> {}" for C
  proof -
    have "C \<subseteq> U-S" "C \<inter> L \<noteq> {}"
      by (simp_all add: in_components_subset comps that)
    then obtain a where a: "a \<in> C" "a \<in> L" by auto
    have opeUC: "openin (subtopology euclidean U) C"
    proof (rule openin_trans)
      show "openin (subtopology euclidean (U-S)) C"
        by (simp add: \<open>locally connected U\<close> clo locally_diff_closed openin_components_locally_connected [OF _ C])
      show "openin (subtopology euclidean U) (U - S)"
        by (simp add: clo openin_diff)
    qed
    then obtain d where "C \<subseteq> U" "0 < d" and d: "cball a d \<inter> U \<subseteq> C"
      using openin_contains_cball by (metis \<open>a \<in> C\<close>)
    then have "ball a d \<inter> U \<subseteq> C"
      by auto
    obtain h k where homhk: "homeomorphism (S \<union> C) (S \<union> C) h k"
                 and subC: "{x. (~ (h x = x \<and> k x = x))} \<subseteq> C"
                 and bou: "bounded {x. (~ (h x = x \<and> k x = x))}"
                 and hin: "\<And>x. x \<in> C \<inter> K \<Longrightarrow> h x \<in> ball a d \<inter> U"
    proof (rule homeomorphism_grouping_points_exists_gen [of C "ball a d \<inter> U" "C \<inter> K" "S \<union> C"])
      show "openin (subtopology euclidean C) (ball a d \<inter> U)"
        by (metis Topology_Euclidean_Space.open_ball \<open>C \<subseteq> U\<close> \<open>ball a d \<inter> U \<subseteq> C\<close> inf.absorb_iff2 inf.orderE inf_assoc open_openin openin_subtopology)
      show "openin (subtopology euclidean (affine hull C)) C"
        by (metis \<open>a \<in> C\<close> \<open>openin (subtopology euclidean U) C\<close> affine_hull_eq affine_hull_openin all_not_in_conv \<open>affine U\<close>)
      show "ball a d \<inter> U \<noteq> {}"
        using \<open>0 < d\<close> \<open>C \<subseteq> U\<close> \<open>a \<in> C\<close> by force
      show "finite (C \<inter> K)"
        by (simp add: \<open>finite K\<close>)
      show "S \<union> C \<subseteq> affine hull C"
        by (metis \<open>C \<subseteq> U\<close> \<open>S \<subseteq> U\<close> \<open>a \<in> C\<close> opeUC affine_hull_eq affine_hull_openin all_not_in_conv assms(2) sup.bounded_iff)
      show "connected C"
        by (metis C in_components_connected)
    qed auto
    have a_BU: "a \<in> ball a d \<inter> U"
      using \<open>0 < d\<close> \<open>C \<subseteq> U\<close> \<open>a \<in> C\<close> by auto
    have "rel_frontier (cball a d \<inter> U) retract_of (affine hull (cball a d \<inter> U) - {a})"
      apply (rule rel_frontier_retract_of_punctured_affine_hull)
        apply (auto simp: \<open>convex U\<close> convex_Int)
      by (metis \<open>affine U\<close> convex_cball empty_iff interior_cball a_BU rel_interior_convex_Int_affine)
    moreover have "rel_frontier (cball a d \<inter> U) = frontier (cball a d) \<inter> U"
      apply (rule convex_affine_rel_frontier_Int)
      using a_BU by (force simp: \<open>affine U\<close>)+
    moreover have "affine hull (cball a d \<inter> U) = U"
      by (metis \<open>convex U\<close> a_BU affine_hull_convex_Int_nonempty_interior affine_hull_eq \<open>affine U\<close> equals0D inf.commute interior_cball)
    ultimately have "frontier (cball a d) \<inter> U retract_of (U - {a})"
      by metis
    then obtain r where contr: "continuous_on (U - {a}) r"
                    and rim: "r ` (U - {a}) \<subseteq> sphere a d"  "r ` (U - {a}) \<subseteq> U"
                    and req: "\<And>x. x \<in> sphere a d \<inter> U \<Longrightarrow> r x = x"
      using \<open>affine U\<close> by (auto simp: retract_of_def retraction_def hull_same)
    define j where "j \<equiv> \<lambda>x. if x \<in> ball a d then r x else x"
    have kj: "\<And>x. x \<in> S \<Longrightarrow> k (j x) = x"
      using \<open>C \<subseteq> U - S\<close> \<open>S \<subseteq> U\<close> \<open>ball a d \<inter> U \<subseteq> C\<close> j_def subC by auto
    have Uaeq: "U - {a} = (cball a d - {a}) \<inter> U \<union> (U - ball a d)"
      using \<open>0 < d\<close> by auto
    have jim: "j ` (S \<union> (C - {a})) \<subseteq> (S \<union> C) - ball a d"
    proof clarify
      fix y  assume "y \<in> S \<union> (C - {a})"
      then have "y \<in> U - {a}"
        using \<open>C \<subseteq> U - S\<close> \<open>S \<subseteq> U\<close> \<open>a \<in> C\<close> by auto
      then have "r y \<in> sphere a d"
        using rim by auto
      then show "j y \<in> S \<union> C - ball a d"
        apply (simp add: j_def)
        using \<open>r y \<in> sphere a d\<close> \<open>y \<in> U - {a}\<close> \<open>y \<in> S \<union> (C - {a})\<close> d rim by fastforce
    qed
    have contj: "continuous_on (U - {a}) j"
      unfolding j_def Uaeq
    proof (intro continuous_on_cases_local continuous_on_id, simp_all add: req closedin_closed Uaeq [symmetric])
      show "\<exists>T. closed T \<and> (cball a d - {a}) \<inter> U = (U - {a}) \<inter> T"
          apply (rule_tac x="(cball a d) \<inter> U" in exI)
        using affine_closed \<open>affine U\<close> by blast
      show "\<exists>T. closed T \<and> U - ball a d = (U - {a}) \<inter> T"
         apply (rule_tac x="U - ball a d" in exI)
        using \<open>0 < d\<close>  by (force simp: affine_closed \<open>affine U\<close> closed_Diff)
      show "continuous_on ((cball a d - {a}) \<inter> U) r"
        by (force intro: continuous_on_subset [OF contr])
    qed
    have fT: "x \<in> U - K \<Longrightarrow> f x \<in> T" for x
      using fim by blast
    show ?thesis
    proof (intro conjI exI)
      show "continuous_on (S \<union> (C - {a})) (f \<circ> k \<circ> j)"
      proof (intro continuous_on_compose)
        show "continuous_on (S \<union> (C - {a})) j"
          apply (rule continuous_on_subset [OF contj])
          using \<open>C \<subseteq> U - S\<close> \<open>S \<subseteq> U\<close> \<open>a \<in> C\<close> by force
        show "continuous_on (j ` (S \<union> (C - {a}))) k"
          apply (rule continuous_on_subset [OF homeomorphism_cont2 [OF homhk]])
          using jim \<open>C \<subseteq> U - S\<close> \<open>S \<subseteq> U\<close> \<open>ball a d \<inter> U \<subseteq> C\<close> j_def by fastforce
        show "continuous_on (k ` j ` (S \<union> (C - {a}))) f"
        proof (clarify intro!: continuous_on_subset [OF contf])
          fix y  assume "y \<in> S \<union> (C - {a})"
          have ky: "k y \<in> S \<union> C"
            using homeomorphism_image2 [OF homhk] \<open>y \<in> S \<union> (C - {a})\<close> by blast
          have jy: "j y \<in> S \<union> C - ball a d"
            using Un_iff \<open>y \<in> S \<union> (C - {a})\<close> jim by auto
          show "k (j y) \<in> U - K"
            apply safe
            using \<open>C \<subseteq> U\<close> \<open>S \<subseteq> U\<close>  homeomorphism_image2 [OF homhk] jy apply blast
            by (metis DiffD1 DiffD2 Int_iff Un_iff \<open>disjnt K S\<close> disjnt_def empty_iff hin homeomorphism_apply2 homeomorphism_image2 homhk imageI jy)
        qed
      qed
      have ST: "\<And>x. x \<in> S \<Longrightarrow> (f \<circ> k \<circ> j) x \<in> T"
        apply (simp add: kj)
        apply (metis DiffI \<open>S \<subseteq> U\<close> \<open>disjnt K S\<close> subsetD disjnt_iff fim image_subset_iff)
        done
      moreover have "(f \<circ> k \<circ> j) x \<in> T" if "x \<in> C" "x \<noteq> a" "x \<notin> S" for x
      proof -
        have rx: "r x \<in> sphere a d"
          using \<open>C \<subseteq> U\<close> rim that by fastforce
        have jj: "j x \<in> S \<union> C - ball a d"
          using jim that by blast
        have "k (j x) = j x \<longrightarrow> k (j x) \<in> C \<or> j x \<in> C"
          by (metis Diff_iff Int_iff Un_iff \<open>S \<subseteq> U\<close> subsetD d j_def jj rx sphere_cball that(1))
        then have "k (j x) \<in> C"
          using homeomorphism_apply2 [OF homhk, of "j x"]   \<open>C \<subseteq> U\<close> \<open>S \<subseteq> U\<close> a rx
          by (metis (mono_tags, lifting) Diff_iff subsetD jj mem_Collect_eq subC)
        with jj \<open>C \<subseteq> U\<close> show ?thesis
          apply safe
          using ST j_def apply fastforce
          apply (auto simp: not_less intro!: fT)
          by (metis DiffD1 DiffD2 Int_iff hin homeomorphism_apply2 [OF homhk] jj)
      qed
      ultimately show "(f \<circ> k \<circ> j) ` (S \<union> (C - {a})) \<subseteq> T"
        by force
      show "\<forall>x\<in>S. (f \<circ> k \<circ> j) x = f x" using kj by simp
    qed (auto simp: a)
  qed
  then obtain a h where
    ah: "\<And>C. \<lbrakk>C \<in> components (U - S); C \<inter> K \<noteq> {}\<rbrakk>
           \<Longrightarrow> a C \<in> C \<and> a C \<in> L \<and> continuous_on (S \<union> (C - {a C})) (h C) \<and>
               h C ` (S \<union> (C - {a C})) \<subseteq> T \<and> (\<forall>x \<in> S. h C x = f x)"
    using that by metis
  define F where "F \<equiv> {C \<in> components (U - S). C \<inter> K \<noteq> {}}"
  define G where "G \<equiv> {C \<in> components (U - S). C \<inter> K = {}}"
  define UF where "UF \<equiv> (\<Union>C\<in>F. C - {a C})"
  have "C0 \<in> F"
    by (auto simp: F_def C0)
  have "finite F"
  proof (subst finite_image_iff [of "\<lambda>C. C \<inter> K" F, symmetric])
    show "inj_on (\<lambda>C. C \<inter> K) F"
      unfolding F_def inj_on_def
      using components_nonoverlap by blast
    show "finite ((\<lambda>C. C \<inter> K) ` F)"
      unfolding F_def
      by (rule finite_subset [of _ "Pow K"]) (auto simp: \<open>finite K\<close>)
  qed
  obtain g where contg: "continuous_on (S \<union> UF) g"
             and gh: "\<And>x i. \<lbrakk>i \<in> F; x \<in> (S \<union> UF) \<inter> (S \<union> (i - {a i}))\<rbrakk>
                            \<Longrightarrow> g x = h i x"
  proof (rule pasting_lemma_exists_closed [OF \<open>finite F\<close>, of "S \<union> UF" "\<lambda>C. S \<union> (C - {a C})" h])
    show "S \<union> UF \<subseteq> (\<Union>C\<in>F. S \<union> (C - {a C}))"
      using \<open>C0 \<in> F\<close> by (force simp: UF_def)
    show "closedin (subtopology euclidean (S \<union> UF)) (S \<union> (C - {a C}))"
         if "C \<in> F" for C
    proof (rule closedin_closed_subset [of U "S \<union> C"])
      show "closedin (subtopology euclidean U) (S \<union> C)"
        apply (rule closedin_Un_complement_component [OF \<open>locally connected U\<close> clo])
        using F_def that by blast
    next
      have "x = a C'" if "C' \<in> F"  "x \<in> C'" "x \<notin> U" for x C'
      proof -
        have "\<forall>A. x \<in> \<Union>A \<or> C' \<notin> A"
          using \<open>x \<in> C'\<close> by blast
        with that show "x = a C'"
          by (metis (lifting) DiffD1 F_def Union_components mem_Collect_eq)
      qed
      then show "S \<union> UF \<subseteq> U"
        using \<open>S \<subseteq> U\<close> by (force simp: UF_def)
    next
      show "S \<union> (C - {a C}) = (S \<union> C) \<inter> (S \<union> UF)"
        using F_def UF_def components_nonoverlap that by auto
    qed
  next
    show "continuous_on (S \<union> (C' - {a C'})) (h C')" if "C' \<in> F" for C'
      using ah F_def that by blast
    show "\<And>i j x. \<lbrakk>i \<in> F; j \<in> F;
                   x \<in> (S \<union> UF) \<inter> (S \<union> (i - {a i})) \<inter> (S \<union> (j - {a j}))\<rbrakk>
                  \<Longrightarrow> h i x = h j x"
      using components_eq by (fastforce simp: components_eq F_def ah)
  qed blast
  have SU': "S \<union> \<Union>G \<union> (S \<union> UF) \<subseteq> U"
    using \<open>S \<subseteq> U\<close> in_components_subset by (auto simp: F_def G_def UF_def)
  have clo1: "closedin (subtopology euclidean (S \<union> \<Union>G \<union> (S \<union> UF))) (S \<union> \<Union>G)"
  proof (rule closedin_closed_subset [OF _ SU'])
    have *: "\<And>C. C \<in> F \<Longrightarrow> openin (subtopology euclidean U) C"
      unfolding F_def
      by clarify (metis (no_types, lifting) \<open>locally connected U\<close> clo closedin_def locally_diff_closed openin_components_locally_connected openin_trans topspace_euclidean_subtopology)
    show "closedin (subtopology euclidean U) (U - UF)"
      unfolding UF_def
      by (force intro: openin_delete *)
    show "S \<union> \<Union>G = (U - UF) \<inter> (S \<union> \<Union>G \<union> (S \<union> UF))"
      using \<open>S \<subseteq> U\<close> apply (auto simp: F_def G_def UF_def)
        apply (metis Diff_iff UnionI Union_components)
       apply (metis DiffD1 UnionI Union_components)
      by (metis (no_types, lifting) IntI components_nonoverlap empty_iff)
  qed
  have clo2: "closedin (subtopology euclidean (S \<union> \<Union>G \<union> (S \<union> UF))) (S \<union> UF)"
  proof (rule closedin_closed_subset [OF _ SU'])
    show "closedin (subtopology euclidean U) (\<Union>C\<in>F. S \<union> C)"
      apply (rule closedin_Union)
       apply (simp add: \<open>finite F\<close>)
      using F_def \<open>locally connected U\<close> clo closedin_Un_complement_component by blast
    show "S \<union> UF = (\<Union>C\<in>F. S \<union> C) \<inter> (S \<union> \<Union>G \<union> (S \<union> UF))"
      using \<open>S \<subseteq> U\<close> apply (auto simp: F_def G_def UF_def)
      using C0 apply blast
      by (metis components_nonoverlap disjnt_def disjnt_iff)
  qed
  have SUG: "S \<union> \<Union>G \<subseteq> U - K"
    using \<open>S \<subseteq> U\<close> K apply (auto simp: G_def disjnt_iff)
    by (meson Diff_iff subsetD in_components_subset)
  then have contf': "continuous_on (S \<union> \<Union>G) f"
    by (rule continuous_on_subset [OF contf])
  have contg': "continuous_on (S \<union> UF) g"
    apply (rule continuous_on_subset [OF contg])
    using \<open>S \<subseteq> U\<close> by (auto simp: F_def G_def)
  have  "\<And>x. \<lbrakk>S \<subseteq> U; x \<in> S\<rbrakk> \<Longrightarrow> f x = g x"
    by (subst gh) (auto simp: ah C0 intro: \<open>C0 \<in> F\<close>)
  then have f_eq_g: "\<And>x. x \<in> S \<union> UF \<and> x \<in> S \<union> \<Union>G \<Longrightarrow> f x = g x"
    using \<open>S \<subseteq> U\<close> apply (auto simp: F_def G_def UF_def dest: in_components_subset)
    using components_eq by blast
  have cont: "continuous_on (S \<union> \<Union>G \<union> (S \<union> UF)) (\<lambda>x. if x \<in> S \<union> \<Union>G then f x else g x)"
    by (blast intro: continuous_on_cases_local [OF clo1 clo2 contf' contg' f_eq_g, of "\<lambda>x. x \<in> S \<union> \<Union>G"])
  show ?thesis
  proof
    have UF: "\<Union>F - L \<subseteq> UF"
      unfolding F_def UF_def using ah by blast
    have "U - S - L = \<Union>(components (U - S)) - L"
      by simp
    also have "... = \<Union>F \<union> \<Union>G - L"
      unfolding F_def G_def by blast
    also have "... \<subseteq> UF \<union> \<Union>G"
      using UF by blast
    finally have "U - L \<subseteq> S \<union> \<Union>G \<union> (S \<union> UF)"
      by blast
    then show "continuous_on (U - L) (\<lambda>x. if x \<in> S \<union> \<Union>G then f x else g x)"
      by (rule continuous_on_subset [OF cont])
    have "((U - L) \<inter> {x. x \<notin> S \<and> (\<forall>xa\<in>G. x \<notin> xa)}) \<subseteq>  ((U - L) \<inter> (-S \<inter> UF))"
      using \<open>U - L \<subseteq> S \<union> \<Union>G \<union> (S \<union> UF)\<close> by auto
    moreover have "g ` ((U - L) \<inter> (-S \<inter> UF)) \<subseteq> T"
    proof -
      have "g x \<in> T" if "x \<in> U" "x \<notin> L" "x \<notin> S" "C \<in> F" "x \<in> C" "x \<noteq> a C" for x C
      proof (subst gh)
        show "x \<in> (S \<union> UF) \<inter> (S \<union> (C - {a C}))"
          using that by (auto simp: UF_def)
        show "h C x \<in> T"
          using ah that by (fastforce simp add: F_def)
      qed (rule that)
      then show ?thesis
        by (force simp: UF_def)
    qed
    ultimately have "g ` ((U - L) \<inter> {x. x \<notin> S \<and> (\<forall>xa\<in>G. x \<notin> xa)}) \<subseteq> T"
      using image_mono order_trans by blast
    moreover have "f ` ((U - L) \<inter> (S \<union> \<Union>G)) \<subseteq> T"
      using fim SUG by blast
    ultimately show "(\<lambda>x. if x \<in> S \<union> \<Union>G then f x else g x) ` (U - L) \<subseteq> T"
       by force
    show "\<And>x. x \<in> S \<Longrightarrow> (if x \<in> S \<union> \<Union>G then f x else g x) = f x"
      by (simp add: F_def G_def)
  qed
qed


lemma extend_map_affine_to_sphere2:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "compact S" "convex U" "bounded U" "affine T" "S \<subseteq> T"
      and affTU: "aff_dim T \<le> aff_dim U"
      and contf: "continuous_on S f"
      and fim: "f ` S \<subseteq> rel_frontier U"
      and ovlap: "\<And>C. C \<in> components(T - S) \<Longrightarrow> C \<inter> L \<noteq> {}"
    obtains K g where "finite K" "K \<subseteq> L" "K \<subseteq> T" "disjnt K S"
                      "continuous_on (T - K) g" "g ` (T - K) \<subseteq> rel_frontier U"
                      "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  obtain K g where K: "finite K" "K \<subseteq> T" "disjnt K S"
               and contg: "continuous_on (T - K) g"
               and gim: "g ` (T - K) \<subseteq> rel_frontier U"
               and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
     using assms extend_map_affine_to_sphere_cofinite_simple by metis
  have "(\<exists>y C. C \<in> components (T - S) \<and> x \<in> C \<and> y \<in> C \<and> y \<in> L)" if "x \<in> K" for x
  proof -
    have "x \<in> T-S"
      using \<open>K \<subseteq> T\<close> \<open>disjnt K S\<close> disjnt_def that by fastforce
    then obtain C where "C \<in> components(T - S)" "x \<in> C"
      by (metis UnionE Union_components)
    with ovlap [of C] show ?thesis
      by blast
  qed
  then obtain \<xi> where \<xi>: "\<And>x. x \<in> K \<Longrightarrow> \<exists>C. C \<in> components (T - S) \<and> x \<in> C \<and> \<xi> x \<in> C \<and> \<xi> x \<in> L"
    by metis
  obtain h where conth: "continuous_on (T - \<xi> ` K) h"
             and him: "h ` (T - \<xi> ` K) \<subseteq> rel_frontier U"
             and hg: "\<And>x. x \<in> S \<Longrightarrow> h x = g x"
  proof (rule extend_map_affine_to_sphere1 [OF \<open>finite K\<close> \<open>affine T\<close> contg gim, of S "\<xi> ` K"])
    show cloTS: "closedin (subtopology euclidean T) S"
      by (simp add: \<open>compact S\<close> \<open>S \<subseteq> T\<close> closed_subset compact_imp_closed)
    show "\<And>C. \<lbrakk>C \<in> components (T - S); C \<inter> K \<noteq> {}\<rbrakk> \<Longrightarrow> C \<inter> \<xi> ` K \<noteq> {}"
      using \<xi> components_eq by blast
  qed (use K in auto)
  show ?thesis
  proof
    show *: "\<xi> ` K \<subseteq> L"
      using \<xi> by blast
    show "finite (\<xi> ` K)"
      by (simp add: K)
    show "\<xi> ` K \<subseteq> T"
      by clarify (meson \<xi> Diff_iff contra_subsetD in_components_subset)
    show "continuous_on (T - \<xi> ` K) h"
      by (rule conth)
    show "disjnt (\<xi> ` K) S"
      using K
      apply (auto simp: disjnt_def)
      by (metis \<xi> DiffD2 UnionI Union_components)
  qed (simp_all add: him hg gf)
qed


proposition extend_map_affine_to_sphere_cofinite_gen:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes SUT: "compact S" "convex U" "bounded U" "affine T" "S \<subseteq> T"
      and aff: "aff_dim T \<le> aff_dim U"
      and contf: "continuous_on S f"
      and fim: "f ` S \<subseteq> rel_frontier U"
      and dis: "\<And>C. \<lbrakk>C \<in> components(T - S); bounded C\<rbrakk> \<Longrightarrow> C \<inter> L \<noteq> {}"
 obtains K g where "finite K" "K \<subseteq> L" "K \<subseteq> T" "disjnt K S" "continuous_on (T - K) g"
                   "g ` (T - K) \<subseteq> rel_frontier U"
                   "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof (cases "S = {}")
  case True
  show ?thesis
  proof (cases "rel_frontier U = {}")
    case True
    with aff have "aff_dim T \<le> 0"
      apply (simp add: rel_frontier_eq_empty)
      using affine_bounded_eq_lowdim \<open>bounded U\<close> order_trans by auto
    with aff_dim_geq [of T] consider "aff_dim T = -1" |  "aff_dim T = 0"
      by linarith
    then show ?thesis
    proof cases
      assume "aff_dim T = -1"
      then have "T = {}"
        by (simp add: aff_dim_empty)
      then show ?thesis
        by (rule_tac K="{}" in that) auto
    next
      assume "aff_dim T = 0"
      then obtain a where "T = {a}"
        using aff_dim_eq_0 by blast
      then have "a \<in> L"
        using dis [of "{a}"] \<open>S = {}\<close> by (auto simp: in_components_self)
      with \<open>S = {}\<close> \<open>T = {a}\<close> show ?thesis
        by (rule_tac K="{a}" and g=f in that) auto
    qed
  next
    case False
    then obtain y where "y \<in> rel_frontier U"
      by auto
    with \<open>S = {}\<close> show ?thesis
      by (rule_tac K="{}" and g="\<lambda>x. y" in that)  (auto simp: continuous_on_const)
  qed
next
  case False
  have "bounded S"
    by (simp add: assms compact_imp_bounded)
  then obtain b where b: "S \<subseteq> cbox (-b) b"
    using bounded_subset_cbox_symmetric by blast
  define LU where "LU \<equiv> L \<union> (\<Union> {C \<in> components (T - S). ~bounded C} - cbox (-(b+One)) (b+One))"
  obtain K g where "finite K" "K \<subseteq> LU" "K \<subseteq> T" "disjnt K S"
               and contg: "continuous_on (T - K) g"
               and gim: "g ` (T - K) \<subseteq> rel_frontier U"
               and gf:  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
  proof (rule extend_map_affine_to_sphere2 [OF SUT aff contf fim])
    show "C \<inter> LU \<noteq> {}" if "C \<in> components (T - S)" for C
    proof (cases "bounded C")
      case True
      with dis that show ?thesis
        unfolding LU_def by fastforce
    next
      case False
      then have "\<not> bounded (\<Union>{C \<in> components (T - S). \<not> bounded C})"
        by (metis (no_types, lifting) Sup_upper bounded_subset mem_Collect_eq that)
      then show ?thesis
        apply (clarsimp simp: LU_def Int_Un_distrib Diff_Int_distrib Int_UN_distrib)
        by (metis (no_types, lifting) False Sup_upper bounded_cbox bounded_subset inf.orderE mem_Collect_eq that)
    qed
  qed blast
  have *: False if "x \<in> cbox (- b - m *\<^sub>R One) (b + m *\<^sub>R One)"
                   "x \<notin> box (- b - n *\<^sub>R One) (b + n *\<^sub>R One)"
                   "0 \<le> m" "m < n" "n \<le> 1" for m n x
    using that by (auto simp: mem_box algebra_simps)
  have "disjoint_family_on (\<lambda>d. frontier (cbox (- b - d *\<^sub>R One) (b + d *\<^sub>R One))) {1 / 2..1}"
    by (auto simp: disjoint_family_on_def neq_iff frontier_def dest: *)
  then obtain d where d12: "1/2 \<le> d" "d \<le> 1"
                  and ddis: "disjnt K (frontier (cbox (-(b + d *\<^sub>R One)) (b + d *\<^sub>R One)))"
    using disjoint_family_elem_disjnt [of "{1/2..1::real}" K "\<lambda>d. frontier (cbox (-(b + d *\<^sub>R One)) (b + d *\<^sub>R One))"]
    by (auto simp: \<open>finite K\<close>)
  define c where "c \<equiv> b + d *\<^sub>R One"
  have cbsub: "cbox (-b) b \<subseteq> box (-c) c"
              "cbox (-b) b \<subseteq> cbox (-c) c"
              "cbox (-c) c \<subseteq> cbox (-(b+One)) (b+One)"
    using d12 by (simp_all add: subset_box c_def inner_diff_left inner_left_distrib)
  have clo_cT: "closed (cbox (- c) c \<inter> T)"
    using affine_closed \<open>affine T\<close> by blast
  have cT_ne: "cbox (- c) c \<inter> T \<noteq> {}"
    using \<open>S \<noteq> {}\<close> \<open>S \<subseteq> T\<close> b cbsub by fastforce
  have S_sub_cc: "S \<subseteq> cbox (- c) c"
    using \<open>cbox (- b) b \<subseteq> cbox (- c) c\<close> b by auto
  show ?thesis
  proof
    show "finite (K \<inter> cbox (-(b+One)) (b+One))"
      using \<open>finite K\<close> by blast
    show "K \<inter> cbox (- (b + One)) (b + One) \<subseteq> L"
      using \<open>K \<subseteq> LU\<close> by (auto simp: LU_def)
    show "K \<inter> cbox (- (b + One)) (b + One) \<subseteq> T"
      using \<open>K \<subseteq> T\<close> by auto
    show "disjnt (K \<inter> cbox (- (b + One)) (b + One)) S"
      using \<open>disjnt K S\<close>  by (simp add: disjnt_def disjoint_eq_subset_Compl inf.coboundedI1)
    have cloTK: "closest_point (cbox (- c) c \<inter> T) x \<in> T - K"
                if "x \<in> T" and Knot: "x \<in> K \<longrightarrow> x \<notin> cbox (- b - One) (b + One)" for x
    proof (cases "x \<in> cbox (- c) c")
      case True
      with \<open>x \<in> T\<close> show ?thesis
        using cbsub(3) Knot  by (force simp: closest_point_self)
    next
      case False
      have clo_in_rf: "closest_point (cbox (- c) c \<inter> T) x \<in> rel_frontier (cbox (- c) c \<inter> T)"
      proof (intro closest_point_in_rel_frontier [OF clo_cT cT_ne] DiffI notI)
        have "T \<inter> interior (cbox (- c) c) \<noteq> {}"
          using \<open>S \<noteq> {}\<close> \<open>S \<subseteq> T\<close> b cbsub(1) by fastforce
        then show "x \<in> affine hull (cbox (- c) c \<inter> T)"
          by (simp add: Int_commute affine_hull_affine_Int_nonempty_interior \<open>affine T\<close> hull_inc that(1))
      next
        show "False" if "x \<in> rel_interior (cbox (- c) c \<inter> T)"
        proof -
          have "interior (cbox (- c) c) \<inter> T \<noteq> {}"
            using \<open>S \<noteq> {}\<close> \<open>S \<subseteq> T\<close> b cbsub(1) by fastforce
          then have "affine hull (T \<inter> cbox (- c) c) = T"
            using affine_hull_convex_Int_nonempty_interior [of T "cbox (- c) c"]
            by (simp add: affine_imp_convex \<open>affine T\<close> inf_commute)
          then show ?thesis
            by (meson subsetD le_inf_iff rel_interior_subset that False)
        qed
      qed
      have "closest_point (cbox (- c) c \<inter> T) x \<notin> K"
      proof
        assume inK: "closest_point (cbox (- c) c \<inter> T) x \<in> K"
        have "\<And>x. x \<in> K \<Longrightarrow> x \<notin> frontier (cbox (- (b + d *\<^sub>R One)) (b + d *\<^sub>R One))"
          by (metis ddis disjnt_iff)
        then show False
          by (metis DiffI Int_iff \<open>affine T\<close> cT_ne c_def clo_cT clo_in_rf closest_point_in_set
                    convex_affine_rel_frontier_Int convex_box(1) empty_iff frontier_cbox inK interior_cbox)
      qed
      then show ?thesis
        using cT_ne clo_cT closest_point_in_set by blast
    qed
    show "continuous_on (T - K \<inter> cbox (- (b + One)) (b + One)) (g \<circ> closest_point (cbox (-c) c \<inter> T))"
      apply (intro continuous_on_compose continuous_on_closest_point continuous_on_subset [OF contg])
         apply (simp_all add: clo_cT affine_imp_convex \<open>affine T\<close> convex_Int cT_ne)
      using cloTK by blast
    have "g (closest_point (cbox (- c) c \<inter> T) x) \<in> rel_frontier U"
         if "x \<in> T" "x \<in> K \<longrightarrow> x \<notin> cbox (- b - One) (b + One)" for x
      apply (rule gim [THEN subsetD])
      using that cloTK by blast
    then show "(g \<circ> closest_point (cbox (- c) c \<inter> T)) ` (T - K \<inter> cbox (- (b + One)) (b + One))
               \<subseteq> rel_frontier U"
      by force
    show "\<And>x. x \<in> S \<Longrightarrow> (g \<circ> closest_point (cbox (- c) c \<inter> T)) x = f x"
      by simp (metis (mono_tags, lifting) IntI \<open>S \<subseteq> T\<close> cT_ne clo_cT closest_point_refl gf subsetD S_sub_cc)
  qed
qed


corollary extend_map_affine_to_sphere_cofinite:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes SUT: "compact S" "affine T" "S \<subseteq> T"
      and aff: "aff_dim T \<le> DIM('b)" and "0 \<le> r"
      and contf: "continuous_on S f"
      and fim: "f ` S \<subseteq> sphere a r"
      and dis: "\<And>C. \<lbrakk>C \<in> components(T - S); bounded C\<rbrakk> \<Longrightarrow> C \<inter> L \<noteq> {}"
  obtains K g where "finite K" "K \<subseteq> L" "K \<subseteq> T" "disjnt K S" "continuous_on (T - K) g"
                    "g ` (T - K) \<subseteq> sphere a r" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof (cases "r = 0")
  case True
  with fim show ?thesis
    by (rule_tac K="{}" and g = "\<lambda>x. a" in that) (auto simp: continuous_on_const)
next
  case False
  with assms have "0 < r" by auto
  then have "aff_dim T \<le> aff_dim (cball a r)"
    by (simp add: aff aff_dim_cball)
  then show ?thesis
    apply (rule extend_map_affine_to_sphere_cofinite_gen
            [OF \<open>compact S\<close> convex_cball bounded_cball \<open>affine T\<close> \<open>S \<subseteq> T\<close> _ contf])
    using fim apply (auto simp: assms False that dest: dis)
    done
qed

corollary extend_map_UNIV_to_sphere_cofinite:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes aff: "DIM('a) \<le> DIM('b)" and "0 \<le> r"
      and SUT: "compact S"
      and contf: "continuous_on S f"
      and fim: "f ` S \<subseteq> sphere a r"
      and dis: "\<And>C. \<lbrakk>C \<in> components(- S); bounded C\<rbrakk> \<Longrightarrow> C \<inter> L \<noteq> {}"
  obtains K g where "finite K" "K \<subseteq> L" "disjnt K S" "continuous_on (- K) g"
                    "g ` (- K) \<subseteq> sphere a r" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
apply (rule extend_map_affine_to_sphere_cofinite
        [OF \<open>compact S\<close> affine_UNIV subset_UNIV _ \<open>0 \<le> r\<close> contf fim dis])
 apply (auto simp: assms that Compl_eq_Diff_UNIV [symmetric])
done

corollary extend_map_UNIV_to_sphere_no_bounded_component:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes aff: "DIM('a) \<le> DIM('b)" and "0 \<le> r"
      and SUT: "compact S"
      and contf: "continuous_on S f"
      and fim: "f ` S \<subseteq> sphere a r"
      and dis: "\<And>C. C \<in> components(- S) \<Longrightarrow> \<not> bounded C"
  obtains g where "continuous_on UNIV g" "g ` UNIV \<subseteq> sphere a r" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
apply (rule extend_map_UNIV_to_sphere_cofinite [OF aff \<open>0 \<le> r\<close> \<open>compact S\<close> contf fim, of "{}"])
   apply (auto simp: that dest: dis)
done

theorem Borsuk_separation_theorem_gen:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S"
    shows "(\<forall>c \<in> components(- S). ~bounded c) \<longleftrightarrow>
           (\<forall>f. continuous_on S f \<and> f ` S \<subseteq> sphere (0::'a) 1
                \<longrightarrow> (\<exists>c. homotopic_with (\<lambda>x. True) S (sphere 0 1) f (\<lambda>x. c)))"
       (is "?lhs = ?rhs")
proof
  assume L [rule_format]: ?lhs
  show ?rhs
  proof clarify
    fix f :: "'a \<Rightarrow> 'a"
    assume contf: "continuous_on S f" and fim: "f ` S \<subseteq> sphere 0 1"
    obtain g where contg: "continuous_on UNIV g" and gim: "range g \<subseteq> sphere 0 1"
               and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
      by (rule extend_map_UNIV_to_sphere_no_bounded_component [OF _ _ \<open>compact S\<close> contf fim L]) auto
    then show "\<exists>c. homotopic_with (\<lambda>x. True) S (sphere 0 1) f (\<lambda>x. c)"
      using nullhomotopic_from_contractible [OF contg gim]
      by (metis assms compact_imp_closed contf empty_iff fim homotopic_with_equal nullhomotopic_into_sphere_extension)
  qed
next
  assume R [rule_format]: ?rhs
  show ?lhs
    unfolding components_def
  proof clarify
    fix a
    assume "a \<notin> S" and a: "bounded (connected_component_set (- S) a)"
    have cont: "continuous_on S (\<lambda>x. inverse(norm(x - a)) *\<^sub>R (x - a))"
      apply (intro continuous_intros)
      using \<open>a \<notin> S\<close> by auto
    have im: "(\<lambda>x. inverse(norm(x - a)) *\<^sub>R (x - a)) ` S \<subseteq> sphere 0 1"
      by clarsimp (metis \<open>a \<notin> S\<close> eq_iff_diff_eq_0 left_inverse norm_eq_zero)
    show False
      using R cont im Borsuk_map_essential_bounded_component [OF \<open>compact S\<close> \<open>a \<notin> S\<close>] a by blast
  qed
qed


corollary Borsuk_separation_theorem:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and 2: "2 \<le> DIM('a)"
    shows "connected(- S) \<longleftrightarrow>
           (\<forall>f. continuous_on S f \<and> f ` S \<subseteq> sphere (0::'a) 1
                \<longrightarrow> (\<exists>c. homotopic_with (\<lambda>x. True) S (sphere 0 1) f (\<lambda>x. c)))"
       (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof (cases "S = {}")
    case True
    then show ?thesis by auto
  next
    case False
    then have "(\<forall>c\<in>components (- S). \<not> bounded c)"
      by (metis L assms(1) bounded_empty cobounded_imp_unbounded compact_imp_bounded in_components_maximal order_refl)
    then show ?thesis
      by (simp add: Borsuk_separation_theorem_gen [OF \<open>compact S\<close>])
  qed
next
  assume R: ?rhs
  then show ?lhs
    apply (simp add: Borsuk_separation_theorem_gen [OF \<open>compact S\<close>, symmetric])
    apply (auto simp: components_def connected_iff_eq_connected_component_set)
    using connected_component_in apply fastforce
    using cobounded_unique_unbounded_component [OF _ 2, of "-S"] \<open>compact S\<close> compact_eq_bounded_closed by fastforce
qed


lemma homotopy_eqv_separation:
  fixes S :: "'a::euclidean_space set" and T :: "'a set"
  assumes "S homotopy_eqv T" and "compact S" and "compact T"
  shows "connected(- S) \<longleftrightarrow> connected(- T)"
proof -
  consider "DIM('a) = 1" | "2 \<le> DIM('a)"
    by (metis DIM_ge_Suc0 One_nat_def Suc_1 dual_order.antisym not_less_eq_eq)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using bounded_connected_Compl_1 compact_imp_bounded homotopy_eqv_empty1 homotopy_eqv_empty2 assms by metis
  next
    case 2
    with assms show ?thesis
      by (simp add: Borsuk_separation_theorem homotopy_eqv_cohomotopic_triviality_null)
  qed
qed

lemma Jordan_Brouwer_separation:
  fixes S :: "'a::euclidean_space set" and a::'a
  assumes hom: "S homeomorphic sphere a r" and "0 < r"
    shows "\<not> connected(- S)"
proof -
  have "- sphere a r \<inter> ball a r \<noteq> {}"
    using \<open>0 < r\<close> by (simp add: Int_absorb1 subset_eq)
  moreover
  have eq: "- sphere a r - ball a r = - cball a r"
    by auto
  have "- cball a r \<noteq> {}"
  proof -
    have "frontier (cball a r) \<noteq> {}"
      using \<open>0 < r\<close> by auto
    then show ?thesis
      by (metis frontier_complement frontier_empty)
  qed
  with eq have "- sphere a r - ball a r \<noteq> {}"
    by auto
  moreover
  have "connected (- S) = connected (- sphere a r)"
  proof (rule homotopy_eqv_separation)
    show "S homotopy_eqv sphere a r"
      using hom homeomorphic_imp_homotopy_eqv by blast
    show "compact (sphere a r)"
      by simp
    then show " compact S"
      using hom homeomorphic_compactness by blast
  qed
  ultimately show ?thesis
    using connected_Int_frontier [of "- sphere a r" "ball a r"] by (auto simp: \<open>0 < r\<close>)
qed


lemma Jordan_Brouwer_frontier:
  fixes S :: "'a::euclidean_space set" and a::'a
  assumes S: "S homeomorphic sphere a r" and T: "T \<in> components(- S)" and 2: "2 \<le> DIM('a)"
    shows "frontier T = S"
proof (cases r rule: linorder_cases)
  assume "r < 0"
  with S T show ?thesis by auto
next
  assume "r = 0"
  with S T card_eq_SucD obtain b where "S = {b}"
    by (auto simp: homeomorphic_finite [of "{a}" S])
  have "components (- {b}) = { -{b}}"
    using T \<open>S = {b}\<close> by (auto simp: components_eq_sing_iff connected_punctured_universe 2)
  with T show ?thesis
    by (metis \<open>S = {b}\<close> cball_trivial frontier_cball frontier_complement singletonD sphere_trivial)
next
  assume "r > 0"
  have "compact S"
    using homeomorphic_compactness compact_sphere S by blast
  show ?thesis
  proof (rule frontier_minimal_separating_closed)
    show "closed S"
      using \<open>compact S\<close> compact_eq_bounded_closed by blast
    show "\<not> connected (- S)"
      using Jordan_Brouwer_separation S \<open>0 < r\<close> by blast
    obtain f g where hom: "homeomorphism S (sphere a r) f g"
      using S by (auto simp: homeomorphic_def)
    show "connected (- T)" if "closed T" "T \<subset> S" for T
    proof -
      have "f ` T \<subseteq> sphere a r"
        using \<open>T \<subset> S\<close> hom homeomorphism_image1 by blast
      moreover have "f ` T \<noteq> sphere a r"
        using \<open>T \<subset> S\<close> hom
        by (metis homeomorphism_image2 homeomorphism_of_subsets order_refl psubsetE)
      ultimately have "f ` T \<subset> sphere a r" by blast
      then have "connected (- f ` T)"
        by (rule psubset_sphere_Compl_connected [OF _ \<open>0 < r\<close> 2])
      moreover have "compact T"
        using \<open>compact S\<close> bounded_subset compact_eq_bounded_closed that by blast
      moreover then have "compact (f ` T)"
        by (meson compact_continuous_image continuous_on_subset hom homeomorphism_def psubsetE \<open>T \<subset> S\<close>)
      moreover have "T homotopy_eqv f ` T"
        by (meson \<open>f ` T \<subseteq> sphere a r\<close> dual_order.strict_implies_order hom homeomorphic_def homeomorphic_imp_homotopy_eqv homeomorphism_of_subsets \<open>T \<subset> S\<close>)
      ultimately show ?thesis
        using homotopy_eqv_separation [of T "f`T"] by blast
    qed
  qed (rule T)
qed

lemma Jordan_Brouwer_nonseparation:
  fixes S :: "'a::euclidean_space set" and a::'a
  assumes S: "S homeomorphic sphere a r" and "T \<subset> S" and 2: "2 \<le> DIM('a)"
    shows "connected(- T)"
proof -
  have *: "connected(C \<union> (S - T))" if "C \<in> components(- S)" for C
  proof (rule connected_intermediate_closure)
    show "connected C"
      using in_components_connected that by auto
    have "S = frontier C"
      using "2" Jordan_Brouwer_frontier S that by blast
    with closure_subset show "C \<union> (S - T) \<subseteq> closure C"
      by (auto simp: frontier_def)
  qed auto
  have "components(- S) \<noteq> {}"
    by (metis S bounded_empty cobounded_imp_unbounded compact_eq_bounded_closed compact_sphere
              components_eq_empty homeomorphic_compactness)
  then have "- T = (\<Union>C \<in> components(- S). C \<union> (S - T))"
    using Union_components [of "-S"] \<open>T \<subset> S\<close> by auto
  then show ?thesis
    apply (rule ssubst)
    apply (rule connected_Union)
    using \<open>T \<subset> S\<close> apply (auto simp: *)
    done
qed

subsection\<open> Invariance of domain and corollaries\<close>

lemma invariance_of_domain_ball:
  fixes f :: "'a \<Rightarrow> 'a::euclidean_space"
  assumes contf: "continuous_on (cball a r) f" and "0 < r"
     and inj: "inj_on f (cball a r)"
   shows "open(f ` ball a r)"
proof (cases "DIM('a) = 1")
  case True
  obtain h::"'a\<Rightarrow>real" and k
        where "linear h" "linear k" "h ` UNIV = UNIV" "k ` UNIV = UNIV"
              "\<And>x. norm(h x) = norm x" "\<And>x. norm(k x) = norm x"
              "\<And>x. k(h x) = x" "\<And>x. h(k x) = x"
    apply (rule isomorphisms_UNIV_UNIV [where 'M='a and 'N=real])
      using True
       apply force
      by (metis UNIV_I UNIV_eq_I imageI)
    have cont: "continuous_on S h"  "continuous_on T k" for S T
      by (simp_all add: \<open>linear h\<close> \<open>linear k\<close> linear_continuous_on linear_linear)
    have "continuous_on (h ` cball a r) (h \<circ> f \<circ> k)"
      apply (intro continuous_on_compose cont continuous_on_subset [OF contf])
      apply (auto simp: \<open>\<And>x. k (h x) = x\<close>)
      done
    moreover have "is_interval (h ` cball a r)"
      by (simp add: is_interval_connected_1 \<open>linear h\<close> linear_continuous_on linear_linear connected_continuous_image)
    moreover have "inj_on (h \<circ> f \<circ> k) (h ` cball a r)"
      using inj by (simp add: inj_on_def) (metis \<open>\<And>x. k (h x) = x\<close>)
    ultimately have *: "\<And>T. \<lbrakk>open T; T \<subseteq> h ` cball a r\<rbrakk> \<Longrightarrow> open ((h \<circ> f \<circ> k) ` T)"
      using injective_eq_1d_open_map_UNIV by blast
    have "open ((h \<circ> f \<circ> k) ` (h ` ball a r))"
      by (rule *) (auto simp: \<open>linear h\<close> \<open>range h = UNIV\<close> open_surjective_linear_image)
    then have "open ((h \<circ> f) ` ball a r)"
      by (simp add: image_comp \<open>\<And>x. k (h x) = x\<close> cong: image_cong)
    then show ?thesis
      apply (simp add: image_comp [symmetric])
      apply (metis open_bijective_linear_image_eq \<open>linear h\<close> \<open>\<And>x. k (h x) = x\<close> \<open>range h = UNIV\<close> bijI inj_on_def)
      done
next
  case False
  then have 2: "DIM('a) \<ge> 2"
    by (metis DIM_ge_Suc0 One_nat_def Suc_1 antisym not_less_eq_eq)
  have fimsub: "f ` ball a r \<subseteq> - f ` sphere a r"
    using inj  by clarsimp (metis inj_onD less_eq_real_def mem_cball order_less_irrefl)
  have hom: "f ` sphere a r homeomorphic sphere a r"
    by (meson compact_sphere contf continuous_on_subset homeomorphic_compact homeomorphic_sym inj inj_on_subset sphere_cball)
  then have nconn: "\<not> connected (- f ` sphere a r)"
    by (rule Jordan_Brouwer_separation) (auto simp: \<open>0 < r\<close>)
  obtain C where C: "C \<in> components (- f ` sphere a r)" and "bounded C"
    apply (rule cobounded_has_bounded_component [OF _ nconn])
      apply (simp_all add: 2)
    by (meson compact_imp_bounded compact_continuous_image_eq compact_sphere contf inj sphere_cball)
  moreover have "f ` (ball a r) = C"
  proof
    have "C \<noteq> {}"
      by (rule in_components_nonempty [OF C])
    show "C \<subseteq> f ` ball a r"
    proof (rule ccontr)
      assume nonsub: "\<not> C \<subseteq> f ` ball a r"
      have "- f ` cball a r \<subseteq> C"
      proof (rule components_maximal [OF C])
        have "f ` cball a r homeomorphic cball a r"
          using compact_cball contf homeomorphic_compact homeomorphic_sym inj by blast
        then show "connected (- f ` cball a r)"
          by (auto intro: connected_complement_homeomorphic_convex_compact 2)
        show "- f ` cball a r \<subseteq> - f ` sphere a r"
          by auto
        then show "C \<inter> - f ` cball a r \<noteq> {}"
          using \<open>C \<noteq> {}\<close> in_components_subset [OF C] nonsub
          using image_iff by fastforce
      qed
      then have "bounded (- f ` cball a r)"
        using bounded_subset \<open>bounded C\<close> by auto
      then have "\<not> bounded (f ` cball a r)"
        using cobounded_imp_unbounded by blast
      then show "False"
        using compact_continuous_image [OF contf] compact_cball compact_imp_bounded by blast
    qed
    with \<open>C \<noteq> {}\<close> have "C \<inter> f ` ball a r \<noteq> {}"
      by (simp add: inf.absorb_iff1)
    then show "f ` ball a r \<subseteq> C"
      by (metis components_maximal [OF C _ fimsub] connected_continuous_image ball_subset_cball connected_ball contf continuous_on_subset)
  qed
  moreover have "open (- f ` sphere a r)"
    using hom compact_eq_bounded_closed compact_sphere homeomorphic_compactness by blast
  ultimately show ?thesis
    using open_components by blast
qed


text\<open>Proved by L. E. J. Brouwer (1912)\<close>
theorem invariance_of_domain:
  fixes f :: "'a \<Rightarrow> 'a::euclidean_space"
  assumes "continuous_on S f" "open S" "inj_on f S"
    shows "open(f ` S)"
  unfolding open_subopen [of "f`S"]
proof clarify
  fix a
  assume "a \<in> S"
  obtain \<delta> where "\<delta> > 0" and \<delta>: "cball a \<delta> \<subseteq> S"
    using \<open>open S\<close> \<open>a \<in> S\<close> open_contains_cball_eq by blast
  show "\<exists>T. open T \<and> f a \<in> T \<and> T \<subseteq> f ` S"
  proof (intro exI conjI)
    show "open (f ` (ball a \<delta>))"
      by (meson \<delta> \<open>0 < \<delta>\<close> assms continuous_on_subset inj_on_subset invariance_of_domain_ball)
    show "f a \<in> f ` ball a \<delta>"
      by (simp add: \<open>0 < \<delta>\<close>)
    show "f ` ball a \<delta> \<subseteq> f ` S"
      using \<delta> ball_subset_cball by blast
  qed
qed

lemma inv_of_domain_ss0:
  fixes f :: "'a \<Rightarrow> 'a::euclidean_space"
  assumes contf: "continuous_on U f" and injf: "inj_on f U" and fim: "f ` U \<subseteq> S"
      and "subspace S" and dimS: "dim S = DIM('b::euclidean_space)"
      and ope: "openin (subtopology euclidean S) U"
    shows "openin (subtopology euclidean S) (f ` U)"
proof -
  have "U \<subseteq> S"
    using ope openin_imp_subset by blast
  have "(UNIV::'b set) homeomorphic S"
    by (simp add: \<open>subspace S\<close> dimS dim_UNIV homeomorphic_subspaces)
  then obtain h k where homhk: "homeomorphism (UNIV::'b set) S h k"
    using homeomorphic_def by blast
  have homkh: "homeomorphism S (k ` S) k h"
    using homhk homeomorphism_image2 homeomorphism_sym by fastforce
  have "open ((k \<circ> f \<circ> h) ` k ` U)"
  proof (rule invariance_of_domain)
    show "continuous_on (k ` U) (k \<circ> f \<circ> h)"
    proof (intro continuous_intros)
      show "continuous_on (k ` U) h"
        by (meson continuous_on_subset [OF homeomorphism_cont1 [OF homhk]] top_greatest)
      show "continuous_on (h ` k ` U) f"
        apply (rule continuous_on_subset [OF contf], clarify)
        apply (metis homhk homeomorphism_def ope openin_imp_subset rev_subsetD)
        done
      show "continuous_on (f ` h ` k ` U) k"
        apply (rule continuous_on_subset [OF homeomorphism_cont2 [OF homhk]])
        using fim homhk homeomorphism_apply2 ope openin_subset by fastforce
    qed
    have ope_iff: "\<And>T. open T \<longleftrightarrow> openin (subtopology euclidean (k ` S)) T"
      using homhk homeomorphism_image2 open_openin by fastforce
    show "open (k ` U)"
      by (simp add: ope_iff homeomorphism_imp_open_map [OF homkh ope])
    show "inj_on (k \<circ> f \<circ> h) (k ` U)"
      apply (clarsimp simp: inj_on_def)
      by (metis subsetD fim homeomorphism_apply2 [OF homhk] image_subset_iff inj_on_eq_iff injf \<open>U \<subseteq> S\<close>)
  qed
  moreover
  have eq: "f ` U = h ` (k \<circ> f \<circ> h \<circ> k) ` U"
    apply (auto simp: image_comp [symmetric])
    apply (metis homkh \<open>U \<subseteq> S\<close> fim homeomorphism_image2 homeomorphism_of_subsets homhk imageI subset_UNIV)
    by (metis \<open>U \<subseteq> S\<close> subsetD fim homeomorphism_def homhk image_eqI)
  ultimately show ?thesis
    by (metis (no_types, hide_lams) homeomorphism_imp_open_map homhk image_comp open_openin subtopology_UNIV)
qed

lemma inv_of_domain_ss1:
  fixes f :: "'a \<Rightarrow> 'a::euclidean_space"
  assumes contf: "continuous_on U f" and injf: "inj_on f U" and fim: "f ` U \<subseteq> S"
      and "subspace S"
      and ope: "openin (subtopology euclidean S) U"
    shows "openin (subtopology euclidean S) (f ` U)"
proof -
  define S' where "S' \<equiv> {y. \<forall>x \<in> S. orthogonal x y}"
  have "subspace S'"
    by (simp add: S'_def subspace_orthogonal_to_vectors)
  define g where "g \<equiv> \<lambda>z::'a*'a. ((f \<circ> fst)z, snd z)"
  have "openin (subtopology euclidean (S \<times> S')) (g ` (U \<times> S'))"
  proof (rule inv_of_domain_ss0)
    show "continuous_on (U \<times> S') g"
      apply (simp add: g_def)
      apply (intro continuous_intros continuous_on_compose2 [OF contf continuous_on_fst], auto)
      done
    show "g ` (U \<times> S') \<subseteq> S \<times> S'"
      using fim  by (auto simp: g_def)
    show "inj_on g (U \<times> S')"
      using injf by (auto simp: g_def inj_on_def)
    show "subspace (S \<times> S')"
      by (simp add: \<open>subspace S'\<close> \<open>subspace S\<close> subspace_Times)
    show "openin (subtopology euclidean (S \<times> S')) (U \<times> S')"
      by (simp add: openin_Times [OF ope])
    have "dim (S \<times> S') = dim S + dim S'"
      by (simp add: \<open>subspace S'\<close> \<open>subspace S\<close> dim_Times)
    also have "... = DIM('a)"
      using dim_subspace_orthogonal_to_vectors [OF \<open>subspace S\<close> subspace_UNIV]
      by (simp add: add.commute S'_def)
    finally show "dim (S \<times> S') = DIM('a)" .
  qed
  moreover have "g ` (U \<times> S') = f ` U \<times> S'"
    by (auto simp: g_def image_iff)
  moreover have "0 \<in> S'"
    using \<open>subspace S'\<close> subspace_affine by blast
  ultimately show ?thesis
    by (auto simp: openin_Times_eq)
qed


corollary invariance_of_domain_subspaces:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (subtopology euclidean U) S"
      and "subspace U" "subspace V" and VU: "dim V \<le> dim U"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> V"
      and injf: "inj_on f S"
    shows "openin (subtopology euclidean V) (f ` S)"
proof -
  obtain V' where "subspace V'" "V' \<subseteq> U" "dim V' = dim V"
    using choose_subspace_of_subspace [OF VU]
    by (metis span_eq \<open>subspace U\<close>)
  then have "V homeomorphic V'"
    by (simp add: \<open>subspace V\<close> homeomorphic_subspaces)
  then obtain h k where homhk: "homeomorphism V V' h k"
    using homeomorphic_def by blast
  have eq: "f ` S = k ` (h \<circ> f) ` S"
  proof -
    have "k ` h ` f ` S = f ` S"
      by (meson fim homeomorphism_def homeomorphism_of_subsets homhk subset_refl)
    then show ?thesis
      by (simp add: image_comp)
  qed
  show ?thesis
    unfolding eq
  proof (rule homeomorphism_imp_open_map)
    show homkh: "homeomorphism V' V k h"
      by (simp add: homeomorphism_symD homhk)
    have hfV': "(h \<circ> f) ` S \<subseteq> V'"
      using fim homeomorphism_image1 homhk by fastforce
    moreover have "openin (subtopology euclidean U) ((h \<circ> f) ` S)"
    proof (rule inv_of_domain_ss1)
      show "continuous_on S (h \<circ> f)"
        by (meson contf continuous_on_compose continuous_on_subset fim homeomorphism_cont1 homhk)
      show "inj_on (h \<circ> f) S"
        apply (clarsimp simp: inj_on_def)
        by (metis fim homeomorphism_apply2 [OF homkh] image_subset_iff inj_onD injf)
      show "(h \<circ> f) ` S \<subseteq> U"
        using \<open>V' \<subseteq> U\<close> hfV' by auto
      qed (auto simp: assms)
    ultimately show "openin (subtopology euclidean V') ((h \<circ> f) ` S)"
      using openin_subset_trans \<open>V' \<subseteq> U\<close> by force
  qed
qed

corollary invariance_of_dimension_subspaces:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (subtopology euclidean U) S"
      and "subspace U" "subspace V"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> V"
      and injf: "inj_on f S" and "S \<noteq> {}"
    shows "dim U \<le> dim V"
proof -
  have "False" if "dim V < dim U"
  proof -
    obtain T where "subspace T" "T \<subseteq> U" "dim T = dim V"
      using choose_subspace_of_subspace [of "dim V" U]
      by (metis span_eq \<open>subspace U\<close> \<open>dim V < dim U\<close> linear not_le)
    then have "V homeomorphic T"
      by (simp add: \<open>subspace V\<close> homeomorphic_subspaces)
    then obtain h k where homhk: "homeomorphism V T h k"
      using homeomorphic_def  by blast
    have "continuous_on S (h \<circ> f)"
      by (meson contf continuous_on_compose continuous_on_subset fim homeomorphism_cont1 homhk)
    moreover have "(h \<circ> f) ` S \<subseteq> U"
      using \<open>T \<subseteq> U\<close> fim homeomorphism_image1 homhk by fastforce
    moreover have "inj_on (h \<circ> f) S"
      apply (clarsimp simp: inj_on_def)
      by (metis fim homeomorphism_apply1 homhk image_subset_iff inj_onD injf)
    ultimately have ope_hf: "openin (subtopology euclidean U) ((h \<circ> f) ` S)"
      using invariance_of_domain_subspaces [OF ope \<open>subspace U\<close> \<open>subspace U\<close>] by auto
    have "(h \<circ> f) ` S \<subseteq> T"
      using fim homeomorphism_image1 homhk by fastforce
    then show ?thesis
      by (metis dim_openin \<open>dim T = dim V\<close> ope_hf \<open>subspace U\<close> \<open>S \<noteq> {}\<close> dim_subset image_is_empty not_le that)
  qed
  then show ?thesis
    using not_less by blast
qed

corollary invariance_of_domain_affine_sets:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (subtopology euclidean U) S"
      and aff: "affine U" "affine V" "aff_dim V \<le> aff_dim U"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> V"
      and injf: "inj_on f S"
    shows "openin (subtopology euclidean V) (f ` S)"
proof (cases "S = {}")
  case True
  then show ?thesis by auto
next
  case False
  obtain a b where "a \<in> S" "a \<in> U" "b \<in> V"
    using False fim ope openin_contains_cball by fastforce
  have "openin (subtopology euclidean (op + (- b) ` V)) ((op + (- b) \<circ> f \<circ> op + a) ` op + (- a) ` S)"
  proof (rule invariance_of_domain_subspaces)
    show "openin (subtopology euclidean (op + (- a) ` U)) (op + (- a) ` S)"
      by (metis ope homeomorphism_imp_open_map homeomorphism_translation translation_galois)
    show "subspace (op + (- a) ` U)"
      by (simp add: \<open>a \<in> U\<close> affine_diffs_subspace \<open>affine U\<close>)
    show "subspace (op + (- b) ` V)"
      by (simp add: \<open>b \<in> V\<close> affine_diffs_subspace \<open>affine V\<close>)
    show "dim (op + (- b) ` V) \<le> dim (op + (- a) ` U)"
      by (metis \<open>a \<in> U\<close> \<open>b \<in> V\<close> aff_dim_eq_dim affine_hull_eq aff of_nat_le_iff)
    show "continuous_on (op + (- a) ` S) (op + (- b) \<circ> f \<circ> op + a)"
      by (metis contf continuous_on_compose homeomorphism_cont2 homeomorphism_translation translation_galois)
    show "(op + (- b) \<circ> f \<circ> op + a) ` op + (- a) ` S \<subseteq> op + (- b) ` V"
      using fim by auto
    show "inj_on (op + (- b) \<circ> f \<circ> op + a) (op + (- a) ` S)"
      by (auto simp: inj_on_def) (meson inj_onD injf)
  qed
  then show ?thesis
    by (metis (no_types, lifting) homeomorphism_imp_open_map homeomorphism_translation image_comp translation_galois)
qed

corollary invariance_of_dimension_affine_sets:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (subtopology euclidean U) S"
      and aff: "affine U" "affine V"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> V"
      and injf: "inj_on f S" and "S \<noteq> {}"
    shows "aff_dim U \<le> aff_dim V"
proof -
  obtain a b where "a \<in> S" "a \<in> U" "b \<in> V"
    using \<open>S \<noteq> {}\<close> fim ope openin_contains_cball by fastforce
  have "dim (op + (- a) ` U) \<le> dim (op + (- b) ` V)"
  proof (rule invariance_of_dimension_subspaces)
    show "openin (subtopology euclidean (op + (- a) ` U)) (op + (- a) ` S)"
      by (metis ope homeomorphism_imp_open_map homeomorphism_translation translation_galois)
    show "subspace (op + (- a) ` U)"
      by (simp add: \<open>a \<in> U\<close> affine_diffs_subspace \<open>affine U\<close>)
    show "subspace (op + (- b) ` V)"
      by (simp add: \<open>b \<in> V\<close> affine_diffs_subspace \<open>affine V\<close>)
    show "continuous_on (op + (- a) ` S) (op + (- b) \<circ> f \<circ> op + a)"
      by (metis contf continuous_on_compose homeomorphism_cont2 homeomorphism_translation translation_galois)
    show "(op + (- b) \<circ> f \<circ> op + a) ` op + (- a) ` S \<subseteq> op + (- b) ` V"
      using fim by auto
    show "inj_on (op + (- b) \<circ> f \<circ> op + a) (op + (- a) ` S)"
      by (auto simp: inj_on_def) (meson inj_onD injf)
  qed (use \<open>S \<noteq> {}\<close> in auto)
  then show ?thesis
    by (metis \<open>a \<in> U\<close> \<open>b \<in> V\<close> aff_dim_eq_dim affine_hull_eq aff of_nat_le_iff)
qed

corollary invariance_of_dimension:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and "open S"
      and injf: "inj_on f S" and "S \<noteq> {}"
    shows "DIM('a) \<le> DIM('b)"
  using invariance_of_dimension_subspaces [of UNIV S UNIV f] assms
  by auto


corollary continuous_injective_image_subspace_dim_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "subspace S" "subspace T"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> T"
      and injf: "inj_on f S"
    shows "dim S \<le> dim T"
  apply (rule invariance_of_dimension_subspaces [of S S _ f])
  using assms by (auto simp: subspace_affine)

lemma invariance_of_dimension_convex_domain:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "convex S"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> affine hull T"
      and injf: "inj_on f S"
    shows "aff_dim S \<le> aff_dim T"
proof (cases "S = {}")
  case True
  then show ?thesis by (simp add: aff_dim_geq)
next
  case False
  have "aff_dim (affine hull S) \<le> aff_dim (affine hull T)"
  proof (rule invariance_of_dimension_affine_sets)
    show "openin (subtopology euclidean (affine hull S)) (rel_interior S)"
      by (simp add: openin_rel_interior)
    show "continuous_on (rel_interior S) f"
      using contf continuous_on_subset rel_interior_subset by blast
    show "f ` rel_interior S \<subseteq> affine hull T"
      using fim rel_interior_subset by blast
    show "inj_on f (rel_interior S)"
      using inj_on_subset injf rel_interior_subset by blast
    show "rel_interior S \<noteq> {}"
      by (simp add: False \<open>convex S\<close> rel_interior_eq_empty)
  qed auto
  then show ?thesis
    by simp
qed


lemma homeomorphic_convex_sets_le:
  assumes "convex S" "S homeomorphic T"
  shows "aff_dim S \<le> aff_dim T"
proof -
  obtain h k where homhk: "homeomorphism S T h k"
    using homeomorphic_def assms  by blast
  show ?thesis
  proof (rule invariance_of_dimension_convex_domain [OF \<open>convex S\<close>])
    show "continuous_on S h"
      using homeomorphism_def homhk by blast
    show "h ` S \<subseteq> affine hull T"
      by (metis homeomorphism_def homhk hull_subset)
    show "inj_on h S"
      by (meson homeomorphism_apply1 homhk inj_on_inverseI)
  qed
qed

lemma homeomorphic_convex_sets:
  assumes "convex S" "convex T" "S homeomorphic T"
  shows "aff_dim S = aff_dim T"
  by (meson assms dual_order.antisym homeomorphic_convex_sets_le homeomorphic_sym)

lemma homeomorphic_convex_compact_sets_eq:
  assumes "convex S" "compact S" "convex T" "compact T"
  shows "S homeomorphic T \<longleftrightarrow> aff_dim S = aff_dim T"
  by (meson assms homeomorphic_convex_compact_sets homeomorphic_convex_sets)

lemma invariance_of_domain_gen:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "inj_on f S" "DIM('b) \<le> DIM('a)"
    shows "open(f ` S)"
  using invariance_of_domain_subspaces [of UNIV S UNIV f] assms by auto

lemma injective_into_1d_imp_open_map_UNIV:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "open T" "continuous_on S f" "inj_on f S" "T \<subseteq> S"
    shows "open (f ` T)"
  apply (rule invariance_of_domain_gen [OF \<open>open T\<close>])
  using assms apply (auto simp: elim: continuous_on_subset subset_inj_on)
  done

lemma continuous_on_inverse_open:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "DIM('b) \<le> DIM('a)" and gf: "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x"
    shows "continuous_on (f ` S) g"
proof (clarsimp simp add: continuous_openin_preimage_eq)
  fix T :: "'a set"
  assume "open T"
  have eq: "{x. x \<in> f ` S \<and> g x \<in> T} = f ` (S \<inter> T)"
    by (auto simp: gf)
  show "openin (subtopology euclidean (f ` S)) {x \<in> f ` S. g x \<in> T}"
    apply (subst eq)
    apply (rule open_openin_trans)
      apply (rule invariance_of_domain_gen)
    using assms
         apply auto
    using inj_on_inverseI apply auto[1]
    by (metis \<open>open T\<close> continuous_on_subset inj_onI inj_on_subset invariance_of_domain_gen openin_open openin_open_eq)
qed

lemma invariance_of_domain_homeomorphism:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "DIM('b) \<le> DIM('a)" "inj_on f S"
  obtains g where "homeomorphism S (f ` S) f g"
proof
  show "homeomorphism S (f ` S) f (inv_into S f)"
    by (simp add: assms continuous_on_inverse_open homeomorphism_def)
qed

corollary invariance_of_domain_homeomorphic:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "DIM('b) \<le> DIM('a)" "inj_on f S"
  shows "S homeomorphic (f ` S)"
  using invariance_of_domain_homeomorphism [OF assms]
  by (meson homeomorphic_def)

end
