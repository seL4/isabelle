section \<open>Extending Continous Maps, Invariance of Domain, etc\<close> (*FIX rename? *)

text\<open>Ported from HOL Light (moretop.ml) by L C Paulson\<close>

theory Further_Topology
  imports Weierstrass_Theorems Polytope Complex_Transcendental Equivalence_Lebesgue_Henstock_Integration Retracts
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
    have "\<And>u. \<lbrakk>u \<in> S; norm u *\<^sub>R f (u /\<^sub>R norm u) \<notin> T\<rbrakk> \<Longrightarrow> u = 0"
      by (metis (mono_tags, lifting) DiffI subS01 subspace_mul [OF \<open>subspace T\<close>] fim image_subset_iff inf_le2 singletonD)
    then have "g ` (S - {0}) \<subseteq> T"
      using g_def by blast
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
      then obtain u where u: "f u \<in> T" "x /\<^sub>R norm x = f u" "norm u = 1" "u \<in> S"
        using * [THEN subsetD, of "x /\<^sub>R norm x"] \<open>x \<noteq> 0\<close> by auto
      with that have [simp]: "norm x *\<^sub>R f u = x"
        by (metis divideR_right norm_eq_zero)
      moreover have "norm x *\<^sub>R u \<in> S - {0}"
        using \<open>subspace S\<close> subspace_scale that(2) u by auto
      with u show ?thesis
        by (simp add: image_eqI [where x="norm x *\<^sub>R u"])
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
    by (simp add: T'_def)
  have "\<exists>v1 v2. v1 \<in> span T \<and> (\<forall>w \<in> span T. orthogonal v2 w) \<and> x = v1 + v2" for x
    by (force intro: orthogonal_subspace_decomp_exists [of T x])
  then obtain p1 p2 where p1span: "p1 x \<in> span T"
                      and "\<And>w. w \<in> span T \<Longrightarrow> orthogonal (p2 x) w"
                      and eq: "p1 x + p2 x = x" for x
    by metis
  then have p1: "\<And>z. p1 z \<in> T" and ortho: "\<And>w. w \<in> T \<Longrightarrow> orthogonal (p2 x) w" for x
    using span_eq_iff \<open>subspace T\<close> by blast+
  then have p2: "\<And>z. p2 z \<in> T'"
    by (simp add: T'_def orthogonal_commute)
  have p12_eq: "\<And>x y. \<lbrakk>x \<in> T; y \<in> T'\<rbrakk> \<Longrightarrow> p1(x + y) = x \<and> p2(x + y) = y"
  proof (rule orthogonal_subspace_decomp_unique [OF eq p1span, where T=T'])
    show "\<And>x y. \<lbrakk>x \<in> T; y \<in> T'\<rbrakk> \<Longrightarrow> p2 (x + y) \<in> span T'"
      using span_eq_iff p2 \<open>subspace T'\<close> by blast
    show "\<And>a b. \<lbrakk>a \<in> T; b \<in> T'\<rbrakk> \<Longrightarrow> orthogonal a b"
      using T'_def by blast
  qed (auto simp: span_base)
  then have "\<And>c x. p1 (c *\<^sub>R x) = c *\<^sub>R p1 x \<and> p2 (c *\<^sub>R x) = c *\<^sub>R p2 x"
  proof -
    fix c :: real and x :: 'a
    have f1: "c *\<^sub>R x = c *\<^sub>R p1 x + c *\<^sub>R p2 x"
      by (metis eq pth_6)
    have f2: "c *\<^sub>R p2 x \<in> T'"
      by (simp add: \<open>subspace T'\<close> p2 subspace_scale)
    have "c *\<^sub>R p1 x \<in> T"
      by (metis (full_types) assms(2) p1span span_eq_iff subspace_scale)
    then show "p1 (c *\<^sub>R x) = c *\<^sub>R p1 x \<and> p2 (c *\<^sub>R x) = c *\<^sub>R p2 x"
      using f2 f1 p12_eq by presburger
  qed
  moreover have lin_add: "\<And>x y. p1 (x + y) = p1 x + p1 y \<and> p2 (x + y) = p2 x + p2 y"
  proof (rule orthogonal_subspace_decomp_unique [OF _ p1span, where T=T'])
    show "\<And>x y. p1 (x + y) + p2 (x + y) = p1 x + p1 y + (p2 x + p2 y)"
      by (simp add: add.assoc add.left_commute eq)
    show  "\<And>a b. \<lbrakk>a \<in> T; b \<in> T'\<rbrakk> \<Longrightarrow> orthogonal a b"
      using T'_def by blast
  qed (auto simp: p1span p2 span_base span_add)
  ultimately have "linear p1" "linear p2"
    by unfold_locales auto
  have "g differentiable_on p1 ` {x + y |x y. x \<in> S - {0} \<and> y \<in> T'}"
    using p12_eq \<open>S \<subseteq> T\<close>  by (force intro: differentiable_on_subset [OF gdiff])
  then have "(\<lambda>z. g (p1 z)) differentiable_on {x + y |x y. x \<in> S - {0} \<and> y \<in> T'}"
    by (rule differentiable_on_compose [OF linear_imp_differentiable_on [OF \<open>linear p1\<close>]])
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
      using \<open>S \<subseteq> T\<close> p12_eq  by (rule_tac x="s + t'" in image_eqI) auto
    then show "{x + y |x y. x \<in> g ` (S - {0}) \<and> y \<in> T'}
          \<subseteq> (\<lambda>x. g (p1 x) + p2 x) ` {x + y |x y. x \<in> S - {0} \<and> y \<in> T'}"
      by auto
  qed
  moreover have "- T' \<subseteq> {x + y |x y. x \<in> g ` (S - {0}) \<and> y \<in> T'}"
  proof clarsimp
    fix z assume "z \<notin> T'"
    show "\<exists>x y. z = x + y \<and> x \<in> g ` (S - {0}) \<and> y \<in> T'"
      by (metis Diff_iff \<open>z \<notin> T'\<close> add.left_neutral eq geq p1 p2 singletonD)
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
    shows "\<exists>c. homotopic_with_canon (\<lambda>x. True) (sphere 0 1 \<inter> S) (sphere 0 1 \<inter> T) f (\<lambda>x. c)"
proof -
  have [simp]: "\<And>x. \<lbrakk>norm x = 1; x \<in> S\<rbrakk> \<Longrightarrow> norm (f x) = 1"
    using fim by (simp add: image_subset_iff)
  have "compact (sphere 0 1 \<inter> S)"
    by (simp add: \<open>subspace S\<close> closed_subspace compact_Int_closed)
  then obtain g where pfg: "polynomial_function g" and gim: "g ` (sphere 0 1 \<inter> S) \<subseteq> T"
                and g12: "\<And>x. x \<in> sphere 0 1 \<inter> S \<Longrightarrow> norm(f x - g x) < 1/2"
    apply (rule Stone_Weierstrass_polynomial_function_subspace [OF _ contf _ \<open>subspace T\<close>, of "1/2"])
    using fim by auto
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
    unfolding h_def using gnz
    by (fastforce intro: derivative_intros diffg differentiable_on_compose [OF diffg])
  have homfg: "homotopic_with_canon (\<lambda>z. True) (sphere 0 1 \<inter> S) (T - {0}) f g"
  proof (rule homotopic_with_linear [OF contf])
    show "continuous_on (sphere 0 1 \<inter> S) g"
      using pfg by (simp add: differentiable_imp_continuous_on diffg)
  next
    have non0fg: "0 \<notin> closed_segment (f x) (g x)" if "norm x = 1" "x \<in> S" for x
    proof -
      have "f x \<in> sphere 0 1"
        using fim that by (simp add: image_subset_iff)
      moreover have "norm(f x - g x) < 1/2"
        using g12 that by auto
      ultimately show ?thesis
        by (auto simp: norm_minus_commute dest: segment_bound)
    qed
    show "closed_segment (f x) (g x) \<subseteq> T - {0}" if "x \<in> sphere 0 1 \<inter> S" for x
    proof -
      have "convex T"
        by (simp add: \<open>subspace T\<close> subspace_imp_convex)
      then have "convex hull {f x, g x} \<subseteq> T"
        by (metis IntD2 closed_segment_subset fim gim image_subset_iff segment_convex_hull that)
      then show ?thesis
        using that non0fg segment_convex_hull by fastforce
    qed
  qed
  obtain d where d: "d \<in> (sphere 0 1 \<inter> T) - h ` (sphere 0 1 \<inter> S)"
    using h spheremap_lemma1 [OF ST \<open>S \<subseteq> T\<close> diffh] by force
  then have non0hd: "0 \<notin> closed_segment (h x) (- d)" if "norm x = 1" "x \<in> S" for x
    using midpoint_between [of 0 "h x" "-d"] that h [of x]
    by (auto simp: between_mem_segment midpoint_def)
  have conth: "continuous_on (sphere 0 1 \<inter> S) h"
    using differentiable_imp_continuous_on diffh by blast
  have hom_hd: "homotopic_with_canon (\<lambda>z. True) (sphere 0 1 \<inter> S) (T - {0}) h (\<lambda>x. -d)"
  proof (rule homotopic_with_linear [OF conth continuous_on_const])
    fix x
    assume x: "x \<in> sphere 0 1 \<inter> S"
    have "convex hull {h x, - d} \<subseteq> T"
    proof (rule hull_minimal)
      show "{h x, - d} \<subseteq> T"
        using h d x by (force simp: subspace_neg [OF \<open>subspace T\<close>])
    qed (simp add: subspace_imp_convex [OF \<open>subspace T\<close>])
    with x segment_convex_hull show "closed_segment (h x) (- d) \<subseteq> T - {0}"
      by (auto simp add: subset_Diff_insert non0hd)
  qed
  have conT0: "continuous_on (T - {0}) (\<lambda>y. inverse(norm y) *\<^sub>R y)"
    by (intro continuous_intros) auto
  have sub0T: "(\<lambda>y. y /\<^sub>R norm y) ` (T - {0}) \<subseteq> sphere 0 1 \<inter> T"
    by (fastforce simp: assms(2) subspace_mul)
  obtain c where homhc: "homotopic_with_canon (\<lambda>z. True) (sphere 0 1 \<inter> S) (sphere 0 1 \<inter> T) h (\<lambda>x. c)"
  proof
    show "homotopic_with_canon (\<lambda>z. True) (sphere 0 1 \<inter> S) (sphere 0 1 \<inter> T) h (\<lambda>x. - d)"
      using d 
      by (force simp: h_def 
           intro: homotopic_with_eq homotopic_with_compose_continuous_left [OF hom_hd conT0 sub0T])
  qed
  have "homotopic_with_canon (\<lambda>x. True) (sphere 0 1 \<inter> S) (sphere 0 1 \<inter> T) f h"
    by (force simp: h_def 
           intro:  homotopic_with_eq homotopic_with_compose_continuous_left [OF homfg conT0 sub0T])
  then show ?thesis
    by (metis homotopic_with_trans [OF _ homhc])
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
      using span_eq_iff \<open>subspace U\<close> \<open>T \<subseteq> span U\<close> by blast
    show "aff_dim T = aff_dim S"
      using dimT \<open>subspace T\<close> affS aff_dim_subspace by fastforce
    show "rel_frontier S homeomorphic sphere 0 1 \<inter> T"
    proof -
      have "aff_dim (ball 0 1 \<inter> T) = aff_dim (T)"
        by (metis IntI interior_ball \<open>subspace T\<close> aff_dim_convex_Int_nonempty_interior centre_in_ball empty_iff inf_commute subspace_0 subspace_imp_convex zero_less_one)
      then have affS_eq: "aff_dim S = aff_dim (ball 0 1 \<inter> T)"
        using \<open>aff_dim T = aff_dim S\<close> by simp
      have "rel_frontier S homeomorphic rel_frontier(ball 0 1 \<inter> T)"
      proof (rule homeomorphic_rel_frontiers_convex_bounded_sets [OF \<open>convex S\<close> \<open>bounded S\<close>])
        show "convex (ball 0 1 \<inter> T)"
          by (simp add: \<open>subspace T\<close> convex_Int subspace_imp_convex)
        show "bounded (ball 0 1 \<inter> T)"
          by (simp add: bounded_Int)
        show "aff_dim S = aff_dim (ball 0 1 \<inter> T)"
          by (rule affS_eq)
      qed
      also have "... = frontier (ball 0 1) \<inter> T"
      proof (rule convex_affine_rel_frontier_Int [OF convex_ball])
        show "affine T"
          by (simp add: \<open>subspace T\<close> subspace_imp_affine)
        show "interior (ball 0 1) \<inter> T \<noteq> {}"
          using \<open>subspace T\<close> subspace_0 by force
      qed
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
  obtains c where "homotopic_with_canon (\<lambda>z. True) (rel_frontier S) (rel_frontier T) f (\<lambda>x. c)"
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
      using \<open>T \<noteq> {}\<close>  by (auto simp add: aff_dim_le_DIM)
    with homeomorphic_imp_homotopy_eqv
    have relT: "sphere 0 1 \<inter> T'  homotopy_eqv rel_frontier T"
      using homotopy_equivalent_space_sym by blast
    have "aff_dim S \<le> int (dim T')"
      using affT' \<open>subspace T'\<close> affST aff_dim_subspace by force
    with spheremap_lemma3 [OF \<open>bounded S\<close> \<open>convex S\<close> \<open>subspace T'\<close>] \<open>S \<noteq> {}\<close>
    obtain S':: "'a set" where "subspace S'" "S' \<subseteq> T'"
       and affS': "aff_dim S' = aff_dim S"
       and homT: "rel_frontier S homeomorphic sphere 0 1 \<inter> S'"
        by metis
    with homeomorphic_imp_homotopy_eqv
    have relS: "sphere 0 1 \<inter> S'  homotopy_eqv rel_frontier S"
      using homotopy_equivalent_space_sym by blast
    have dimST': "dim S' < dim T'"
      by (metis \<open>S' \<subseteq> T'\<close> \<open>subspace S'\<close> \<open>subspace T'\<close> affS' affST affT' less_irrefl not_le subspace_dim_equal)
    have "\<exists>c. homotopic_with_canon (\<lambda>z. True) (rel_frontier S) (rel_frontier T) f (\<lambda>x. c)"
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
   obtains c where "homotopic_with_canon (\<lambda>z. True) (sphere a r) (sphere b s) f (\<lambda>x. c)"
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
    with \<open>\<not> s \<le> 0\<close> have "r > 0" "s > 0" by auto
    show thesis
      apply (rule inessential_spheremap_lowdim_gen [of "cball a r" "cball b s" f])
      using  \<open>0 < r\<close> \<open>0 < s\<close> assms(1) that by (simp_all add: f aff_dim_cball)
  qed
qed



subsection\<open> Some technical lemmas about extending maps from cell complexes\<close>

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
    using fim gim feq geq
    apply (force simp: insert closed_Union contf contg inf_commute intro: fg)+
    done
qed

lemma extending_maps_Union:
  assumes fin: "finite \<F>"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>g. continuous_on S g \<and> g ` S \<subseteq> T \<and> (\<forall>x \<in> S \<inter> K. g x = h x)"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> closed S"
      and K: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>; \<not> X \<subseteq> Y; \<not> Y \<subseteq> X\<rbrakk> \<Longrightarrow> X \<inter> Y \<subseteq> K"
    shows "\<exists>g. continuous_on (\<Union>\<F>) g \<and> g ` (\<Union>\<F>) \<subseteq> T \<and> (\<forall>x \<in> \<Union>\<F> \<inter> K. g x = h x)"
apply (simp flip: Union_maximal_sets [OF fin])
apply (rule extending_maps_Union_aux)
apply (simp_all add: Union_maximal_sets [OF fin] assms)
by (metis K psubsetI)


lemma extend_map_lemma:
  assumes "finite \<F>" "\<G> \<subseteq> \<F>" "convex T" "bounded T"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and aff: "\<And>X. X \<in> \<F> - \<G> \<Longrightarrow> aff_dim X < aff_dim T"
      and face: "\<And>S T. \<lbrakk>S \<in> \<F>; T \<in> \<F>\<rbrakk> \<Longrightarrow> (S \<inter> T) face_of S"
      and contf: "continuous_on (\<Union>\<G>) f" and fim: "f ` (\<Union>\<G>) \<subseteq> rel_frontier T"
  obtains g where "continuous_on (\<Union>\<F>) g" "g ` (\<Union>\<F>) \<subseteq> rel_frontier T" "\<And>x. x \<in> \<Union>\<G> \<Longrightarrow> g x = f x"
proof (cases "\<F> - \<G> = {}")
  case True
  show ?thesis
  proof
    show "continuous_on (\<Union> \<F>) f"
      using True \<open>\<G> \<subseteq> \<F>\<close> contf by auto
    show "f ` \<Union> \<F> \<subseteq> rel_frontier T"
      using True fim by auto
  qed auto
next
  case False
  then have "0 \<le> aff_dim T"
    by (metis aff aff_dim_empty aff_dim_geq aff_dim_negative_iff all_not_in_conv not_less)
  then obtain i::nat where i: "int i = aff_dim T"
    by (metis nonneg_eq_int)
  have Union_empty_eq: "\<Union>{D. D = {} \<and> P D} = {}" for P :: "'a set \<Rightarrow> bool"
    by auto
  have face': "\<And>S T. \<lbrakk>S \<in> \<F>; T \<in> \<F>\<rbrakk> \<Longrightarrow> (S \<inter> T) face_of S \<and> (S \<inter> T) face_of T"
    by (metis face inf_commute)
  have extendf: "\<exists>g. continuous_on (\<Union>(\<G> \<union> {D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D < i})) g \<and>
                     g ` (\<Union> (\<G> \<union> {D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D < i})) \<subseteq> rel_frontier T \<and>
                     (\<forall>x \<in> \<Union>\<G>. g x = f x)"
       if "i \<le> aff_dim T" for i::nat
  using that
  proof (induction i)
    case 0
    show ?case
      using 0 contf fim by (auto simp add: Union_empty_eq)
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
      have "continuous_on D h"
        using True conth continuous_on_subset by blast
      moreover have "h ` D \<subseteq> rel_frontier T"
        using True him by blast
      ultimately show ?thesis
        by blast
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
          by clarify (metis \<open>D face_of C\<close> affD eq_iff face_of_trans facet_of_def zle_diff1_eq)
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
        then have *: "(\<exists>c. homotopic_with_canon (\<lambda>x. True) (rel_frontier D) (rel_frontier T) h (\<lambda>x. c)) =
                      (\<exists>g. continuous_on UNIV g \<and>  range g \<subseteq> rel_frontier T \<and>
                           (\<forall>x\<in>rel_frontier D. g x = h x))"
          by (simp add: assms rel_frontier_eq_empty him_relf nullhomotopic_into_rel_frontier_extension [OF closed_rel_frontier])
        have "(\<exists>c. homotopic_with_canon (\<lambda>x. True) (rel_frontier D) (rel_frontier T) h (\<lambda>x. c))"
          by (metis inessential_spheremap_lowdim_gen
                 [OF \<open>convex D\<close> \<open>bounded D\<close> \<open>convex T\<close> \<open>bounded T\<close> affD_lessT contDh him_relf])
        then obtain g where contg: "continuous_on UNIV g"
                        and gim: "range g \<subseteq> rel_frontier T"
                        and gh: "\<And>x. x \<in> rel_frontier D \<Longrightarrow> g x = h x"
          by (metis *)
        have "D \<inter> E \<subseteq> rel_frontier D"
             if "E \<in> \<G> \<union> {D. Bex \<F> ((face_of) D) \<and> aff_dim D < int p}" for E
        proof (rule face_of_subset_rel_frontier)
          show "D \<inter> E face_of D"
            using that
          proof safe
            assume "E \<in> \<G>"
            then show "D \<inter> E face_of D"
              by (meson \<open>C \<in> \<F>\<close> \<open>D face_of C\<close> assms(2) face' face_of_Int_subface face_of_refl_eq poly polytope_imp_convex subsetD)
          next
            fix x
            assume "aff_dim E < int p" "x \<in> \<F>" "E face_of x"
            then show "D \<inter> E face_of D"
              by (meson \<open>C \<in> \<F>\<close> \<open>D face_of C\<close> face' face_of_Int_subface that)
          qed
          show "D \<inter> E \<noteq> D"
            using that notDsub by auto
        qed
        moreover have "continuous_on D g"
          using contg continuous_on_subset by blast
        ultimately show ?thesis
          by (rule_tac x=g in exI) (use gh gim in fastforce)
      qed
    qed
    have intle: "i < 1 + int j \<longleftrightarrow> i \<le> int j" for i j
      by auto
    have "finite \<G>"
      using \<open>finite \<F>\<close> \<open>\<G> \<subseteq> \<F>\<close> rev_finite_subset by blast
    moreover have "finite (?Faces)"
    proof -
      have \<section>: "finite (\<Union> {{D. D face_of C} |C. C \<in> \<F>})"
        by (auto simp: \<open>finite \<F>\<close> finite_polytope_faces poly)
      show ?thesis
        by (auto intro: finite_subset [OF _ \<section>])
    qed
    ultimately have fin: "finite (\<G> \<union> ?Faces)"
      by simp
    have clo: "closed S" if "S \<in> \<G> \<union> ?Faces" for S
      using that \<open>\<G> \<subseteq> \<F>\<close> face_of_polytope_polytope poly polytope_imp_closed by blast
    have K: "X \<inter> Y \<subseteq> \<Union>(\<G> \<union> {D. \<exists>C\<in>\<F>. D face_of C \<and> aff_dim D < int p})"
                if "X \<in> \<G> \<union> ?Faces" "Y \<in> \<G> \<union> ?Faces" "\<not> Y \<subseteq> X" for X Y
    proof -
      have ff: "X \<inter> Y face_of X \<and> X \<inter> Y face_of Y"
        if XY: "X face_of D" "Y face_of E" and DE: "D \<in> \<F>" "E \<in> \<F>" for D E
        by (rule face_of_Int_subface [OF _ _ XY]) (auto simp: face' DE)
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
      by (rule exE [OF extending_maps_Union [OF fin extendh clo K]], blast+)
    then show ?case
      by (simp add: intle local.heq [symmetric], blast)
  qed
  have eq: "\<Union>(\<G> \<union> {D. \<exists>C \<in> \<F>. D face_of C \<and> aff_dim D < i}) = \<Union>\<F>"
  proof
    show "\<Union>(\<G> \<union> {D. \<exists>C\<in>\<F>. D face_of C \<and> aff_dim D < int i}) \<subseteq> \<Union>\<F>"
      using \<open>\<G> \<subseteq> \<F>\<close> face_of_imp_subset by fastforce
    show "\<Union>\<F> \<subseteq> \<Union>(\<G> \<union> {D. \<exists>C\<in>\<F>. D face_of C \<and> aff_dim D < i})"
    proof (rule Union_mono)
      show "\<F> \<subseteq> \<G> \<union> {D. \<exists>C\<in>\<F>. D face_of C \<and> aff_dim D < int i}"
        using face by (fastforce simp: aff i)
    qed
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
    have "continuous_on (X - insert a C) f"
      using contf by (force simp: elim: continuous_on_subset)
    moreover have "continuous_on (\<Union> \<F> - insert a C) g"
      using contg by (force simp: elim: continuous_on_subset)
    ultimately
    have "continuous_on (X - insert a C \<union> (\<Union>\<F> - insert a C)) (\<lambda>x. if x \<in> X then f x else g x)"
      apply (intro continuous_on_cases_local; simp add: closedin_closed)
        using \<open>closed X\<close> apply blast
        using \<open>closed (\<Union>\<F>)\<close> apply blast
        using fh gh insert.hyps pwX by fastforce
    then show "continuous_on (\<Union>(insert X \<F>) - insert a C) (\<lambda>a. if a \<in> X then f a else g a)"
      by (blast intro: continuous_on_subset)
    show "\<forall>x\<in>(\<Union>(insert X \<F>) - insert a C) \<inter> K. (if x \<in> X then f x else g x) = h x"
      using gh by (auto simp: fh)
    show "(\<lambda>a. if a \<in> X then f a else g a) ` (\<Union>(insert X \<F>) - insert a C) \<subseteq> T"
      using fim gim by auto force
  qed
qed


lemma extend_map_lemma_cofinite1:
assumes "finite \<F>"
    and \<F>: "\<And>X. X \<in> \<F> \<Longrightarrow> \<exists>a g. a \<notin> U \<and> continuous_on (X - {a}) g \<and> g ` (X - {a}) \<subseteq> T \<and> (\<forall>x \<in> X \<inter> K. g x = h x)"
    and clo: "\<And>X. X \<in> \<F> \<Longrightarrow> closed X"
    and K: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>; \<not> X \<subseteq> Y; \<not> Y \<subseteq> X\<rbrakk> \<Longrightarrow> X \<inter> Y \<subseteq> K"
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
    using extend_map_lemma_cofinite0 [OF fin pw, of U T h] by (fastforce intro!: clo \<F>)
  ultimately show ?thesis
    by (rule_tac C=C and g=g in that) auto
qed


lemma extend_map_lemma_cofinite:
  assumes "finite \<F>" "\<G> \<subseteq> \<F>" and T: "convex T" "bounded T"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and contf: "continuous_on (\<Union>\<G>) f" and fim: "f ` (\<Union>\<G>) \<subseteq> rel_frontier T"
      and face: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> (X \<inter> Y) face_of X"
      and aff: "\<And>X. X \<in> \<F> - \<G> \<Longrightarrow> aff_dim X \<le> aff_dim T"
  obtains C g where
     "finite C" "disjnt C (\<Union>\<G>)" "card C \<le> card \<F>" "continuous_on (\<Union>\<F> - C) g"
     "g ` (\<Union> \<F> - C) \<subseteq> rel_frontier T" "\<And>x. x \<in> \<Union>\<G> \<Longrightarrow> g x = f x"
proof -
  define \<H> where "\<H> \<equiv> \<G> \<union> {D. \<exists>C \<in> \<F> - \<G>. D face_of C \<and> aff_dim D < aff_dim T}"
  have "finite \<G>"
    using assms finite_subset by blast
  have *: "finite (\<Union>{{D. D face_of C} |C. C \<in> \<F>})"
    using finite_polytope_faces poly \<open>finite \<F>\<close> by force
  then have "finite \<H>"
    by (auto simp: \<H>_def \<open>finite \<G>\<close> intro: finite_subset [OF _ *])
  have face': "\<And>S T. \<lbrakk>S \<in> \<F>; T \<in> \<F>\<rbrakk> \<Longrightarrow> (S \<inter> T) face_of S \<and> (S \<inter> T) face_of T"
    by (metis face inf_commute)
  have *: "\<And>X Y. \<lbrakk>X \<in> \<H>; Y \<in> \<H>\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X"
    unfolding \<H>_def
    using subsetD [OF \<open>\<G> \<subseteq> \<F>\<close>] apply (auto simp add: face)
    apply (meson face' face_of_Int_subface face_of_refl_eq poly polytope_imp_convex)+
    done
  obtain h where conth: "continuous_on (\<Union>\<H>) h" and him: "h ` (\<Union>\<H>) \<subseteq> rel_frontier T"
             and hf: "\<And>x. x \<in> \<Union>\<G> \<Longrightarrow> h x = f x" 
  proof (rule extend_map_lemma [OF \<open>finite \<H>\<close> [unfolded \<H>_def] Un_upper1 T])
    show "\<And>X. \<lbrakk>X \<in> \<G> \<union> {D. \<exists>C\<in>\<F> - \<G>. D face_of C \<and> aff_dim D < aff_dim T}\<rbrakk> \<Longrightarrow> polytope X"
      using \<open>\<G> \<subseteq> \<F>\<close> face_of_polytope_polytope poly by fastforce
  qed (use * \<H>_def contf fim in auto)
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
    then have "h ` (D - {a}) \<subseteq> rel_frontier T" "continuous_on (D - {a}) h"
      using him by (blast intro!: \<open>a \<notin> \<Union>\<G>\<close> continuous_on_subset [OF conth])+
    then show ?thesis
      using a by blast
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
              using \<open>\<G> \<subseteq> \<F>\<close> face' that by auto
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
          proof (rule continuous_on_compose)
            show "continuous_on (D - {b}) r"
              by (meson Diff_mono continuous_on_subset contr hull_subset order_refl)
            show "continuous_on (r ` (D - {b})) h"
              by (simp add: Diff_mono hull_subset continuous_on_subset [OF conth rsub])
          qed
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
                have "D face_of D"
                  by (simp add: \<open>polyhedron D\<close> polyhedron_imp_convex face_of_refl)
                then show "D \<inter> A face_of D"
                  by (meson "2"(2) "2"(3) \<open>D \<in> \<F>\<close> face' face_of_Int_Int face_of_face)
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
    by (rule_tac C=C and g=g in that) (auto simp: disjnt_def hf [symmetric] \<H>_def intro!: gh)
qed

text\<open>The next two proofs are similar\<close>
theorem extend_map_cell_complex_to_sphere:
  assumes "finite \<F>" and S: "S \<subseteq> \<Union>\<F>" "closed S" and T: "convex T" "bounded T"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and aff: "\<And>X. X \<in> \<F> \<Longrightarrow> aff_dim X < aff_dim T"
      and face: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> (X \<inter> Y) face_of X"
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
             and faceG: "\<And>X Y. \<lbrakk>X \<in> \<G>; Y \<in> \<G>\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X"
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
        using \<open>X \<in> \<G>\<close> \<open>X \<subseteq> V\<close> \<open>x \<in> X\<close> hg by auto
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
      and face: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> (X \<inter> Y) face_of X"
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
             and faceG: "\<And>X Y. \<lbrakk>X \<in> \<G>; Y \<in> \<G>\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X"
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
        using Ssub hg that by blast
      also have "... = f x"
        by (simp add: gf that)
      finally show "h x = f x" .
    qed
    show "disjnt C S"
      using dis Ssub  by (meson disjnt_iff subset_eq)
  qed (intro \<open>finite C\<close>)
qed



subsection\<open> Special cases and corollaries involving spheres\<close>

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
      show "\<And>X Y. \<lbrakk>X \<in> {bbox \<inter> T}; Y \<in> {bbox \<inter> T}\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X"
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
    have cbsub: "cbox (-b) b \<subseteq> box (-c) c" "cbox (-b) b \<subseteq> cbox (-c) c"  "cbox (-c) c \<subseteq> bbox"
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
        by (subst convex_affine_rel_frontier_Int [OF _  \<open>affine T\<close> int_ne]) (auto simp: fro_def c_def)
      ultimately show ?thesis
        using dd  by (force simp: disjnt_def)
    qed
    then have cpt_subset: "closest_point (cbox (- c) c \<inter> T) ` (T - K) \<subseteq> \<Union>{bbox \<inter> T} - K"
      using closest_point_in_set [OF clo_cbT cpT_ne] cbsub(3) by force
    show ?thesis
    proof (intro conjI ballI exI)
      have "continuous_on (T - K) (closest_point (cbox (- c) c \<inter> T))"
      proof (rule continuous_on_closest_point)
        show "convex (cbox (- c) c \<inter> T)"
          by (simp add: affine_imp_convex convex_Int \<open>affine T\<close>)
        show "closed (cbox (- c) c \<inter> T)"
          using clo_cbT by blast
        show "cbox (- c) c \<inter> T \<noteq> {}"
          using \<open>S \<noteq> {}\<close> cbsub(2) b that by auto
      qed
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

lemma extend_map_affine_to_sphere1:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::topological_space"
  assumes "finite K" "affine U" and contf: "continuous_on (U - K) f"
      and fim: "f ` (U - K) \<subseteq> T"
      and comps: "\<And>C. \<lbrakk>C \<in> components(U - S); C \<inter> K \<noteq> {}\<rbrakk> \<Longrightarrow> C \<inter> L \<noteq> {}"
      and clo: "closedin (top_of_set U) S" and K: "disjnt K S" "K \<subseteq> U"
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
    have opeUC: "openin (top_of_set U) C"
    proof (rule openin_trans)
      show "openin (top_of_set (U-S)) C"
        by (simp add: \<open>locally connected U\<close> clo locally_diff_closed openin_components_locally_connected [OF _ C])
      show "openin (top_of_set U) (U - S)"
        by (simp add: clo openin_diff)
    qed
    then obtain d where "C \<subseteq> U" "0 < d" and d: "cball a d \<inter> U \<subseteq> C"
      using openin_contains_cball by (metis \<open>a \<in> C\<close>)
    then have "ball a d \<inter> U \<subseteq> C"
      by auto
    obtain h k where homhk: "homeomorphism (S \<union> C) (S \<union> C) h k"
                 and subC: "{x. (\<not> (h x = x \<and> k x = x))} \<subseteq> C"
                 and bou: "bounded {x. (\<not> (h x = x \<and> k x = x))}"
                 and hin: "\<And>x. x \<in> C \<inter> K \<Longrightarrow> h x \<in> ball a d \<inter> U"
    proof (rule homeomorphism_grouping_points_exists_gen [of C "ball a d \<inter> U" "C \<inter> K" "S \<union> C"])
      show "openin (top_of_set C) (ball a d \<inter> U)"
        by (metis open_ball \<open>C \<subseteq> U\<close> \<open>ball a d \<inter> U \<subseteq> C\<close> inf.absorb_iff2 inf.orderE inf_assoc open_openin openin_subtopology)
      show "openin (top_of_set (affine hull C)) C"
        by (metis \<open>a \<in> C\<close> \<open>openin (top_of_set U) C\<close> affine_hull_eq affine_hull_openin all_not_in_conv \<open>affine U\<close>)
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
    proof (rule rel_frontier_retract_of_punctured_affine_hull)
      show "bounded (cball a d \<inter> U)" "convex (cball a d \<inter> U)"
        by (auto simp: \<open>convex U\<close> convex_Int)
      show "a \<in> rel_interior (cball a d \<inter> U)"
        by (metis \<open>affine U\<close> convex_cball empty_iff interior_cball a_BU rel_interior_convex_Int_affine)
    qed
    moreover have "rel_frontier (cball a d \<inter> U) = frontier (cball a d) \<inter> U"
      by (metis a_BU \<open>affine U\<close> convex_affine_rel_frontier_Int convex_cball equals0D interior_cball)
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
        unfolding j_def
        using \<open>r y \<in> sphere a d\<close> \<open>y \<in> U - {a}\<close> \<open>y \<in> S \<union> (C - {a})\<close> d rim
        by (metis Diff_iff Int_iff Un_iff subsetD cball_diff_eq_sphere image_subset_iff)
    qed
    have contj: "continuous_on (U - {a}) j"
      unfolding j_def Uaeq
    proof (intro continuous_on_cases_local continuous_on_id, simp_all add: req closedin_closed Uaeq [symmetric])
      show "\<exists>T. closed T \<and> (cball a d - {a}) \<inter> U = (U - {a}) \<inter> T"
        using affine_closed \<open>affine U\<close> by (rule_tac x="(cball a d) \<inter> U" in exI) blast
      show "\<exists>T. closed T \<and> U - ball a d = (U - {a}) \<inter> T"
        using \<open>0 < d\<close> \<open>affine U\<close>
        by (rule_tac x="U - ball a d" in exI) (force simp: affine_closed)
      show "continuous_on ((cball a d - {a}) \<inter> U) r"
        by (force intro: continuous_on_subset [OF contr])
    qed
    have fT: "x \<in> U - K \<Longrightarrow> f x \<in> T" for x
      using fim by blast
    show ?thesis
    proof (intro conjI exI)
      show "continuous_on (S \<union> (C - {a})) (f \<circ> k \<circ> j)"
      proof (intro continuous_on_compose)
        have "S \<union> (C - {a}) \<subseteq> U - {a}"
          using \<open>C \<subseteq> U - S\<close> \<open>S \<subseteq> U\<close> \<open>a \<in> C\<close> by force
        then show "continuous_on (S \<union> (C - {a})) j"
          by (rule continuous_on_subset [OF contj])
        have "j ` (S \<union> (C - {a})) \<subseteq> S \<union> C"
          using jim \<open>C \<subseteq> U - S\<close> \<open>S \<subseteq> U\<close> \<open>ball a d \<inter> U \<subseteq> C\<close> j_def by blast
        then show "continuous_on (j ` (S \<union> (C - {a}))) k"
          by (rule continuous_on_subset [OF homeomorphism_cont2 [OF homhk]])
        show "continuous_on (k ` j ` (S \<union> (C - {a}))) f"
        proof (clarify intro!: continuous_on_subset [OF contf])
          fix y  assume "y \<in> S \<union> (C - {a})"
          have ky: "k y \<in> S \<union> C"
            using homeomorphism_image2 [OF homhk] \<open>y \<in> S \<union> (C - {a})\<close> by blast
          have jy: "j y \<in> S \<union> C - ball a d"
            using Un_iff \<open>y \<in> S \<union> (C - {a})\<close> jim by auto
          have "k (j y) \<in> U"
            using \<open>C \<subseteq> U\<close> \<open>S \<subseteq> U\<close>  homeomorphism_image2 [OF homhk] jy by blast
          moreover have "k (j y) \<notin> K"
            using K unfolding disjnt_iff
            by (metis DiffE Int_iff Un_iff hin homeomorphism_def homhk image_eqI jy)
          ultimately show "k (j y) \<in> U - K"
            by blast
        qed
      qed
      have ST: "\<And>x. x \<in> S \<Longrightarrow> (f \<circ> k \<circ> j) x \<in> T"
      proof (simp add: kj)
        show "\<And>x. x \<in> S \<Longrightarrow> f x \<in> T"
          using K unfolding disjnt_iff by (metis DiffI \<open>S \<subseteq> U\<close> subsetD fim image_subset_iff)
      qed
      moreover have "(f \<circ> k \<circ> j) x \<in> T" if "x \<in> C" "x \<noteq> a" "x \<notin> S" for x
      proof -
        have rx: "r x \<in> sphere a d"
          using \<open>C \<subseteq> U\<close> rim that by fastforce
        have jj: "j x \<in> S \<union> C - ball a d"
          using jim that by blast
        have "k (j x) = j x \<longrightarrow> k (j x) \<in> C \<or> j x \<in> C"
          by (metis Diff_iff Int_iff Un_iff \<open>S \<subseteq> U\<close> subsetD d j_def jj rx sphere_cball that(1))
        then have kj: "k (j x) \<in> C"
          using homeomorphism_apply2 [OF homhk, of "j x"]   \<open>C \<subseteq> U\<close> \<open>S \<subseteq> U\<close> a rx
          by (metis (mono_tags, lifting) Diff_iff subsetD jj mem_Collect_eq subC)
        then show ?thesis
          by (metis DiffE DiffI IntD1 IntI \<open>C \<subseteq> U\<close> comp_apply fT hin homeomorphism_apply2 homhk jj kj subset_eq)
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
  proof (rule pasting_lemma_exists_closed [OF \<open>finite F\<close>])
    let ?X = "top_of_set (S \<union> UF)"
    show "topspace ?X \<subseteq> (\<Union>C\<in>F. S \<union> (C - {a C}))"
      using \<open>C0 \<in> F\<close> by (force simp: UF_def)
    show "closedin (top_of_set (S \<union> UF)) (S \<union> (C - {a C}))"
         if "C \<in> F" for C
    proof (rule closedin_closed_subset [of U "S \<union> C"])
      have "C \<in> components (U - S)"
        using F_def that by blast
      then show "closedin (top_of_set U) (S \<union> C)"
        by (rule closedin_Un_complement_component [OF \<open>locally connected U\<close> clo])
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
    show "continuous_map (subtopology ?X (S \<union> (C' - {a C'}))) euclidean (h C')" if "C' \<in> F" for C'
    proof -
      have C': "C' \<in> components (U - S)" "C' \<inter> K \<noteq> {}"
        using F_def that by blast+
      show ?thesis
        using ah [OF C'] by (auto simp: F_def subtopology_subtopology intro: continuous_on_subset)
    qed
    show "\<And>i j x. \<lbrakk>i \<in> F; j \<in> F;
                   x \<in> topspace ?X \<inter> (S \<union> (i - {a i})) \<inter> (S \<union> (j - {a j}))\<rbrakk>
                  \<Longrightarrow> h i x = h j x"
      using components_eq by (fastforce simp: components_eq F_def ah)
  qed auto
  have SU': "S \<union> \<Union>G \<union> (S \<union> UF) \<subseteq> U"
    using \<open>S \<subseteq> U\<close> in_components_subset by (auto simp: F_def G_def UF_def)
  have clo1: "closedin (top_of_set (S \<union> \<Union>G \<union> (S \<union> UF))) (S \<union> \<Union>G)"
  proof (rule closedin_closed_subset [OF _ SU'])
    have *: "\<And>C. C \<in> F \<Longrightarrow> openin (top_of_set U) C"
      unfolding F_def
      by clarify (metis (no_types, lifting) \<open>locally connected U\<close> clo closedin_def locally_diff_closed openin_components_locally_connected openin_trans topspace_euclidean_subtopology)
    show "closedin (top_of_set U) (U - UF)"
      unfolding UF_def
      by (force intro: openin_delete *)
    show "S \<union> \<Union>G = (U - UF) \<inter> (S \<union> \<Union>G \<union> (S \<union> UF))"
      using \<open>S \<subseteq> U\<close> apply (auto simp: F_def G_def UF_def)
        apply (metis Diff_iff UnionI Union_components)
       apply (metis DiffD1 UnionI Union_components)
      by (metis (no_types, lifting) IntI components_nonoverlap empty_iff)
  qed
  have clo2: "closedin (top_of_set (S \<union> \<Union>G \<union> (S \<union> UF))) (S \<union> UF)"
  proof (rule closedin_closed_subset [OF _ SU'])
    show "closedin (top_of_set U) (\<Union>C\<in>F. S \<union> C)"
    proof (rule closedin_Union)
      show "\<And>T. T \<in> (\<union>) S ` F \<Longrightarrow> closedin (top_of_set U) T"
        using F_def \<open>locally connected U\<close> clo closedin_Un_complement_component by blast
    qed (simp add: \<open>finite F\<close>)
    show "S \<union> UF = (\<Union>C\<in>F. S \<union> C) \<inter> (S \<union> \<Union>G \<union> (S \<union> UF))"
      using \<open>S \<subseteq> U\<close> apply (auto simp: F_def G_def UF_def)
      using C0 apply blast
      by (metis components_nonoverlap disjoint_iff)
  qed
  have SUG: "S \<union> \<Union>G \<subseteq> U - K"
    using \<open>S \<subseteq> U\<close> K apply (auto simp: G_def disjnt_iff)
    by (meson Diff_iff subsetD in_components_subset)
  then have contf': "continuous_on (S \<union> \<Union>G) f"
    by (rule continuous_on_subset [OF contf])
  have contg': "continuous_on (S \<union> UF) g"
    by (simp add: contg)
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
    show cloTS: "closedin (top_of_set T) S"
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
      using K \<xi> in_components_subset by (fastforce simp: disjnt_def)
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
      using affine_bounded_eq_lowdim \<open>bounded U\<close> order_trans 
      by (auto simp add: rel_frontier_eq_empty)
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
      by (rule_tac K="{}" and g="\<lambda>x. y" in that)  (auto)
  qed
next
  case False
  have "bounded S"
    by (simp add: assms compact_imp_bounded)
  then obtain b where b: "S \<subseteq> cbox (-b) b"
    using bounded_subset_cbox_symmetric by blast
  define LU where "LU \<equiv> L \<union> (\<Union> {C \<in> components (T - S). \<not>bounded C} - cbox (-(b+One)) (b+One))"
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
      using cloTK
      apply (intro continuous_on_compose continuous_on_closest_point continuous_on_subset [OF contg])
      by (auto simp add: clo_cT affine_imp_convex \<open>affine T\<close> convex_Int cT_ne)
    have "g (closest_point (cbox (- c) c \<inter> T) x) \<in> rel_frontier U"
         if "x \<in> T" "x \<in> K \<longrightarrow> x \<notin> cbox (- b - One) (b + One)" for x
      using gim [THEN subsetD] that cloTK by blast
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
    by (rule_tac K="{}" and g = "\<lambda>x. a" in that) (auto)
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
  assumes "DIM('a) \<le> DIM('b)" and "0 \<le> r"
      and "compact S"
      and "continuous_on S f"
      and "f ` S \<subseteq> sphere a r"
      and "\<And>C. \<lbrakk>C \<in> components(- S); bounded C\<rbrakk> \<Longrightarrow> C \<inter> L \<noteq> {}"
  obtains K g where "finite K" "K \<subseteq> L" "disjnt K S" "continuous_on (- K) g"
                    "g ` (- K) \<subseteq> sphere a r" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
  using extend_map_affine_to_sphere_cofinite
        [OF \<open>compact S\<close> affine_UNIV subset_UNIV] assms
  by (metis Compl_eq_Diff_UNIV aff_dim_UNIV of_nat_le_iff)

corollary extend_map_UNIV_to_sphere_no_bounded_component:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes aff: "DIM('a) \<le> DIM('b)" and "0 \<le> r"
      and SUT: "compact S"
      and contf: "continuous_on S f"
      and fim: "f ` S \<subseteq> sphere a r"
      and dis: "\<And>C. C \<in> components(- S) \<Longrightarrow> \<not> bounded C"
  obtains g where "continuous_on UNIV g" "g ` UNIV \<subseteq> sphere a r" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
  apply (rule extend_map_UNIV_to_sphere_cofinite [OF aff \<open>0 \<le> r\<close> \<open>compact S\<close> contf fim, of "{}"])
   apply (auto dest: dis)
done

theorem Borsuk_separation_theorem_gen:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S"
    shows "(\<forall>c \<in> components(- S). \<not>bounded c) \<longleftrightarrow>
           (\<forall>f. continuous_on S f \<and> f ` S \<subseteq> sphere (0::'a) 1
                \<longrightarrow> (\<exists>c. homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) f (\<lambda>x. c)))"
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
    then obtain c where c: "homotopic_with_canon (\<lambda>h. True) UNIV (sphere 0 1) g (\<lambda>x. c)"
      using contractible_UNIV nullhomotopic_from_contractible by blast
    then show "\<exists>c. homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) f (\<lambda>x. c)"
      by (metis assms compact_imp_closed contf contg contractible_empty fim gf gim nullhomotopic_from_contractible nullhomotopic_into_sphere_extension)
  qed
next
  assume R [rule_format]: ?rhs
  show ?lhs
    unfolding components_def
  proof clarify
    fix a
    assume "a \<notin> S" and a: "bounded (connected_component_set (- S) a)"
    have "\<forall>x\<in>S. norm (x - a) \<noteq> 0"
      using \<open>a \<notin> S\<close> by auto
    then have cont: "continuous_on S (\<lambda>x. inverse(norm(x - a)) *\<^sub>R (x - a))"
      by (intro continuous_intros)
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
                \<longrightarrow> (\<exists>c. homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) f (\<lambda>x. c)))"
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

proposition Jordan_Brouwer_separation:
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


proposition Jordan_Brouwer_frontier:
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

proposition Jordan_Brouwer_nonseparation:
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
  moreover have "connected ..."
    using \<open>T \<subset> S\<close> by (intro connected_Union) (auto simp: *)
  ultimately show ?thesis
    by simp
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
      and kh: "\<And>x. k(h x) = x" and "\<And>x. h(k x) = x"
  proof (rule isomorphisms_UNIV_UNIV)
    show "DIM('a) = DIM(real)"
      using True by force
  qed (metis UNIV_I UNIV_eq_I imageI)
  have cont: "continuous_on S h"  "continuous_on T k" for S T
      by (simp_all add: \<open>linear h\<close> \<open>linear k\<close> linear_continuous_on linear_linear)
    have "continuous_on (h ` cball a r) (h \<circ> f \<circ> k)"
      by (intro continuous_on_compose cont continuous_on_subset [OF contf]) (auto simp: kh)
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
      unfolding image_comp [symmetric]
      by (metis open_bijective_linear_image_eq \<open>linear h\<close> kh \<open>range h = UNIV\<close> bijI inj_on_def)
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
  have "bounded (f ` sphere a r)"
    by (meson compact_imp_bounded compact_continuous_image_eq compact_sphere contf inj sphere_cball)
  then obtain C where C: "C \<in> components (- f ` sphere a r)" and "bounded C"
    using cobounded_has_bounded_component [OF _ nconn] "2" by auto
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
      and ope: "openin (top_of_set S) U"
    shows "openin (top_of_set S) (f ` U)"
proof -
  have "U \<subseteq> S"
    using ope openin_imp_subset by blast
  have "(UNIV::'b set) homeomorphic S"
    by (simp add: \<open>subspace S\<close> dimS homeomorphic_subspaces)
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
      have "h ` k ` U \<subseteq> U"
        by (metis \<open>U \<subseteq> S\<close> dual_order.eq_iff homeomorphism_image2 homeomorphism_of_subsets homkh)
      then show "continuous_on (h ` k ` U) f"
        by (rule continuous_on_subset [OF contf])
      have "f ` h ` k ` U \<subseteq> S"
        using \<open>h ` k ` U \<subseteq> U\<close> fim by blast
      then show "continuous_on (f ` h ` k ` U) k"
        by (rule continuous_on_subset [OF homeomorphism_cont2 [OF homhk]])
    qed
    have ope_iff: "\<And>T. open T \<longleftrightarrow> openin (top_of_set (k ` S)) T"
      using homhk homeomorphism_image2 open_openin by fastforce
    show "open (k ` U)"
      by (simp add: ope_iff homeomorphism_imp_open_map [OF homkh ope])
    show "inj_on (k \<circ> f \<circ> h) (k ` U)"
      apply (clarsimp simp: inj_on_def)
      by (metis \<open>U \<subseteq> S\<close> fim homeomorphism_apply2 homhk image_subset_iff inj_onD injf subsetD)
  qed
  moreover
  have eq: "f ` U = h ` (k \<circ> f \<circ> h \<circ> k) ` U"
    unfolding image_comp [symmetric] using \<open>U \<subseteq> S\<close> fim
    by (metis homeomorphism_image2 homeomorphism_of_subsets homkh subset_image_iff)
  ultimately show ?thesis
    by (metis (no_types, opaque_lifting) homeomorphism_imp_open_map homhk image_comp open_openin subtopology_UNIV)
qed

lemma inv_of_domain_ss1:
  fixes f :: "'a \<Rightarrow> 'a::euclidean_space"
  assumes contf: "continuous_on U f" and injf: "inj_on f U" and fim: "f ` U \<subseteq> S"
      and "subspace S"
      and ope: "openin (top_of_set S) U"
    shows "openin (top_of_set S) (f ` U)"
proof -
  define S' where "S' \<equiv> {y. \<forall>x \<in> S. orthogonal x y}"
  have "subspace S'"
    by (simp add: S'_def subspace_orthogonal_to_vectors)
  define g where "g \<equiv> \<lambda>z::'a*'a. ((f \<circ> fst)z, snd z)"
  have "openin (top_of_set (S \<times> S')) (g ` (U \<times> S'))"
  proof (rule inv_of_domain_ss0)
    show "continuous_on (U \<times> S') g"
      unfolding  g_def
      by (auto intro!: continuous_intros continuous_on_compose2 [OF contf continuous_on_fst])
    show "g ` (U \<times> S') \<subseteq> S \<times> S'"
      using fim  by (auto simp: g_def)
    show "inj_on g (U \<times> S')"
      using injf by (auto simp: g_def inj_on_def)
    show "subspace (S \<times> S')"
      by (simp add: \<open>subspace S'\<close> \<open>subspace S\<close> subspace_Times)
    show "openin (top_of_set (S \<times> S')) (U \<times> S')"
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
  assumes ope: "openin (top_of_set U) S"
      and "subspace U" "subspace V" and VU: "dim V \<le> dim U"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> V"
      and injf: "inj_on f S"
    shows "openin (top_of_set V) (f ` S)"
proof -
  obtain V' where "subspace V'" "V' \<subseteq> U" "dim V' = dim V"
    using choose_subspace_of_subspace [OF VU]
    by (metis span_eq_iff \<open>subspace U\<close>)
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
    moreover have "openin (top_of_set U) ((h \<circ> f) ` S)"
    proof (rule inv_of_domain_ss1)
      show "continuous_on S (h \<circ> f)"
        by (meson contf continuous_on_compose continuous_on_subset fim homeomorphism_cont1 homhk)
      show "inj_on (h \<circ> f) S"
        apply (clarsimp simp: inj_on_def)
        by (metis fim homeomorphism_apply2 [OF homkh] image_subset_iff inj_onD injf)
      show "(h \<circ> f) ` S \<subseteq> U"
        using \<open>V' \<subseteq> U\<close> hfV' by auto
      qed (auto simp: assms)
    ultimately show "openin (top_of_set V') ((h \<circ> f) ` S)"
      using openin_subset_trans \<open>V' \<subseteq> U\<close> by force
  qed
qed

corollary invariance_of_dimension_subspaces:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (top_of_set U) S"
      and "subspace U" "subspace V"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> V"
      and injf: "inj_on f S" and "S \<noteq> {}"
    shows "dim U \<le> dim V"
proof -
  have "False" if "dim V < dim U"
  proof -
    obtain T where "subspace T" "T \<subseteq> U" "dim T = dim V"
      using choose_subspace_of_subspace [of "dim V" U]
      by (metis \<open>dim V < dim U\<close> assms(2) order.strict_implies_order span_eq_iff)
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
    ultimately have ope_hf: "openin (top_of_set U) ((h \<circ> f) ` S)"
      using invariance_of_domain_subspaces [OF ope \<open>subspace U\<close> \<open>subspace U\<close>] by blast
    have "(h \<circ> f) ` S \<subseteq> T"
      using fim homeomorphism_image1 homhk by fastforce
    then have "dim ((h \<circ> f) ` S) \<le> dim T"
      by (rule dim_subset)
    also have "dim ((h \<circ> f) ` S) = dim U"
      using \<open>S \<noteq> {}\<close> \<open>subspace U\<close>
      by (blast intro: dim_openin ope_hf)
    finally show False
      using \<open>dim V < dim U\<close> \<open>dim T = dim V\<close> by simp
  qed
  then show ?thesis
    using not_less by blast
qed

corollary invariance_of_domain_affine_sets:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (top_of_set U) S"
      and aff: "affine U" "affine V" "aff_dim V \<le> aff_dim U"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> V"
      and injf: "inj_on f S"
    shows "openin (top_of_set V) (f ` S)"
proof (cases "S = {}")
  case True
  then show ?thesis by auto
next
  case False
  obtain a b where "a \<in> S" "a \<in> U" "b \<in> V"
    using False fim ope openin_contains_cball by fastforce
  have "openin (top_of_set ((+) (- b) ` V)) (((+) (- b) \<circ> f \<circ> (+) a) ` (+) (- a) ` S)"
  proof (rule invariance_of_domain_subspaces)
    show "openin (top_of_set ((+) (- a) ` U)) ((+) (- a) ` S)"
      by (metis ope homeomorphism_imp_open_map homeomorphism_translation translation_galois)
    show "subspace ((+) (- a) ` U)"
      by (simp add: \<open>a \<in> U\<close> affine_diffs_subspace_subtract \<open>affine U\<close> cong: image_cong_simp)
    show "subspace ((+) (- b) ` V)"
      by (simp add: \<open>b \<in> V\<close> affine_diffs_subspace_subtract \<open>affine V\<close> cong: image_cong_simp)
    show "dim ((+) (- b) ` V) \<le> dim ((+) (- a) ` U)"
      by (metis \<open>a \<in> U\<close> \<open>b \<in> V\<close> aff_dim_eq_dim affine_hull_eq aff of_nat_le_iff)
    show "continuous_on ((+) (- a) ` S) ((+) (- b) \<circ> f \<circ> (+) a)"
      by (metis contf continuous_on_compose homeomorphism_cont2 homeomorphism_translation translation_galois)
    show "((+) (- b) \<circ> f \<circ> (+) a) ` (+) (- a) ` S \<subseteq> (+) (- b) ` V"
      using fim by auto
    show "inj_on ((+) (- b) \<circ> f \<circ> (+) a) ((+) (- a) ` S)"
      by (auto simp: inj_on_def) (meson inj_onD injf)
  qed
  then show ?thesis
    by (metis (no_types, lifting) homeomorphism_imp_open_map homeomorphism_translation image_comp translation_galois)
qed

corollary invariance_of_dimension_affine_sets:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (top_of_set U) S"
      and aff: "affine U" "affine V"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> V"
      and injf: "inj_on f S" and "S \<noteq> {}"
    shows "aff_dim U \<le> aff_dim V"
proof -
  obtain a b where "a \<in> S" "a \<in> U" "b \<in> V"
    using \<open>S \<noteq> {}\<close> fim ope openin_contains_cball by fastforce
  have "dim ((+) (- a) ` U) \<le> dim ((+) (- b) ` V)"
  proof (rule invariance_of_dimension_subspaces)
    show "openin (top_of_set ((+) (- a) ` U)) ((+) (- a) ` S)"
      by (metis ope homeomorphism_imp_open_map homeomorphism_translation translation_galois)
    show "subspace ((+) (- a) ` U)"
      by (simp add: \<open>a \<in> U\<close> affine_diffs_subspace_subtract \<open>affine U\<close> cong: image_cong_simp)
    show "subspace ((+) (- b) ` V)"
      by (simp add: \<open>b \<in> V\<close> affine_diffs_subspace_subtract \<open>affine V\<close> cong: image_cong_simp)
    show "continuous_on ((+) (- a) ` S) ((+) (- b) \<circ> f \<circ> (+) a)"
      by (metis contf continuous_on_compose homeomorphism_cont2 homeomorphism_translation translation_galois)
    show "((+) (- b) \<circ> f \<circ> (+) a) ` (+) (- a) ` S \<subseteq> (+) (- b) ` V"
      using fim by auto
    show "inj_on ((+) (- b) \<circ> f \<circ> (+) a) ((+) (- a) ` S)"
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
  using invariance_of_dimension_subspaces [of S S _ f] assms by (auto simp: subspace_affine)

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
    show "openin (top_of_set (affine hull S)) (rel_interior S)"
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
  using assms by (auto simp: elim: continuous_on_subset subset_inj_on)

lemma continuous_on_inverse_open:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "DIM('b) \<le> DIM('a)" and gf: "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x"
    shows "continuous_on (f ` S) g"
proof (clarsimp simp add: continuous_openin_preimage_eq)
  fix T :: "'a set"
  assume "open T"
  have eq: "f ` S \<inter> g -` T = f ` (S \<inter> T)"
    by (auto simp: gf)
  have "open (f ` S)"
    by (rule invariance_of_domain_gen) (use assms inj_on_inverseI in auto)
  moreover have "open (f ` (S \<inter> T))"
    using assms
    by (metis \<open>open T\<close> continuous_on_subset inj_onI inj_on_subset invariance_of_domain_gen openin_open openin_open_eq)
  ultimately show "openin (top_of_set (f ` S)) (f ` S \<inter> g -` T)"
    unfolding eq by (auto intro: open_openin_trans)
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

lemma continuous_image_subset_interior:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "continuous_on S f" "inj_on f S" "DIM('b) \<le> DIM('a)"
  shows "f ` (interior S) \<subseteq> interior(f ` S)"
proof -
  have "open (f ` interior S)"
    using assms
    by (intro invariance_of_domain_gen) (auto simp: subset_inj_on interior_subset continuous_on_subset)
  then show ?thesis
    by (simp add: image_mono interior_maximal interior_subset)
qed

lemma homeomorphic_interiors_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" and dimeq: "DIM('a) = DIM('b)"
  shows "(interior S) homeomorphic (interior T)"
  using assms [unfolded homeomorphic_minimal]
  unfolding homeomorphic_def
proof (clarify elim!: ex_forward)
  fix f g
  assume S: "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" and T: "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
     and contf: "continuous_on S f" and contg: "continuous_on T g"
  then have fST: "f ` S = T" and gTS: "g ` T = S" and "inj_on f S" "inj_on g T"
    by (auto simp: inj_on_def intro: rev_image_eqI) metis+
  have fim: "f ` interior S \<subseteq> interior T"
    using continuous_image_subset_interior [OF contf \<open>inj_on f S\<close>] dimeq fST by simp
  have gim: "g ` interior T \<subseteq> interior S"
    using continuous_image_subset_interior [OF contg \<open>inj_on g T\<close>] dimeq gTS by simp
  show "homeomorphism (interior S) (interior T) f g"
    unfolding homeomorphism_def
  proof (intro conjI ballI)
    show "\<And>x. x \<in> interior S \<Longrightarrow> g (f x) = x"
      by (meson \<open>\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x\<close> subsetD interior_subset)
    have "interior T \<subseteq> f ` interior S"
    proof
      fix x assume "x \<in> interior T"
      then have "g x \<in> interior S"
        using gim by blast
      then show "x \<in> f ` interior S"
        by (metis T \<open>x \<in> interior T\<close> image_iff interior_subset subsetCE)
    qed
    then show "f ` interior S = interior T"
      using fim by blast
    show "continuous_on (interior S) f"
      by (metis interior_subset continuous_on_subset contf)
    show "\<And>y. y \<in> interior T \<Longrightarrow> f (g y) = y"
      by (meson T subsetD interior_subset)
    have "interior S \<subseteq> g ` interior T"
    proof
      fix x assume "x \<in> interior S"
      then have "f x \<in> interior T"
        using fim by blast
      then show "x \<in> g ` interior T"
        by (metis S \<open>x \<in> interior S\<close> image_iff interior_subset subsetCE)
    qed
    then show "g ` interior T = interior S"
      using gim by blast
    show "continuous_on (interior T) g"
      by (metis interior_subset continuous_on_subset contg)
  qed
qed

lemma homeomorphic_open_imp_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "open S" "S \<noteq> {}" "open T" "T \<noteq> {}"
  shows "DIM('a) = DIM('b)"
    using assms
    apply (simp add: homeomorphic_minimal)
    apply (rule order_antisym; metis inj_onI invariance_of_dimension)
    done

proposition homeomorphic_interiors:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "interior S = {} \<longleftrightarrow> interior T = {}"
    shows "(interior S) homeomorphic (interior T)"
proof (cases "interior T = {}")
  case True
  with assms show ?thesis by auto
next
  case False
  then have "DIM('a) = DIM('b)"
    using assms
    apply (simp add: homeomorphic_minimal)
    apply (rule order_antisym; metis continuous_on_subset inj_onI inj_on_subset interior_subset invariance_of_dimension open_interior)
    done
  then show ?thesis
    by (rule homeomorphic_interiors_same_dimension [OF \<open>S homeomorphic T\<close>])
qed

lemma homeomorphic_frontiers_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "closed S" "closed T" and dimeq: "DIM('a) = DIM('b)"
  shows "(frontier S) homeomorphic (frontier T)"
  using assms [unfolded homeomorphic_minimal]
  unfolding homeomorphic_def
proof (clarify elim!: ex_forward)
  fix f g
  assume S: "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" and T: "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
     and contf: "continuous_on S f" and contg: "continuous_on T g"
  then have fST: "f ` S = T" and gTS: "g ` T = S" and "inj_on f S" "inj_on g T"
    by (auto simp: inj_on_def intro: rev_image_eqI) metis+
  have "g ` interior T \<subseteq> interior S"
    using continuous_image_subset_interior [OF contg \<open>inj_on g T\<close>] dimeq gTS by simp
  then have fim: "f ` frontier S \<subseteq> frontier T"
    unfolding frontier_def
    using continuous_image_subset_interior assms(2) assms(3) S by auto
  have "f ` interior S \<subseteq> interior T"
    using continuous_image_subset_interior [OF contf \<open>inj_on f S\<close>] dimeq fST by simp
  then have gim: "g ` frontier T \<subseteq> frontier S"
    unfolding frontier_def
    using continuous_image_subset_interior T assms(2) assms(3) by auto
  show "homeomorphism (frontier S) (frontier T) f g"
    unfolding homeomorphism_def
  proof (intro conjI ballI)
    show gf: "\<And>x. x \<in> frontier S \<Longrightarrow> g (f x) = x"
      by (simp add: S assms(2) frontier_def)
    show fg: "\<And>y. y \<in> frontier T \<Longrightarrow> f (g y) = y"
      by (simp add: T assms(3) frontier_def)
    have "frontier T \<subseteq> f ` frontier S"
    proof
      fix x assume "x \<in> frontier T"
      then have "g x \<in> frontier S"
        using gim by blast
      then show "x \<in> f ` frontier S"
        by (metis fg \<open>x \<in> frontier T\<close> imageI)
    qed
    then show "f ` frontier S = frontier T"
      using fim by blast
    show "continuous_on (frontier S) f"
      by (metis Diff_subset assms(2) closure_eq contf continuous_on_subset frontier_def)
    have "frontier S \<subseteq> g ` frontier T"
    proof
      fix x assume "x \<in> frontier S"
      then have "f x \<in> frontier T"
        using fim by blast
      then show "x \<in> g ` frontier T"
        by (metis gf \<open>x \<in> frontier S\<close> imageI)
    qed
    then show "g ` frontier T = frontier S"
      using gim by blast
    show "continuous_on (frontier T) g"
      by (metis Diff_subset assms(3) closure_closed contg continuous_on_subset frontier_def)
  qed
qed

lemma homeomorphic_frontiers:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "closed S" "closed T"
          "interior S = {} \<longleftrightarrow> interior T = {}"
    shows "(frontier S) homeomorphic (frontier T)"
proof (cases "interior T = {}")
  case True
  then show ?thesis
    by (metis Diff_empty assms closure_eq frontier_def)
next
  case False
  then have "DIM('a) = DIM('b)"
    using assms homeomorphic_interiors homeomorphic_open_imp_same_dimension by blast
  then show ?thesis
    using assms homeomorphic_frontiers_same_dimension by blast
qed

lemma continuous_image_subset_rel_interior:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and injf: "inj_on f S" and fim: "f ` S \<subseteq> T"
      and TS: "aff_dim T \<le> aff_dim S"
  shows "f ` (rel_interior S) \<subseteq> rel_interior(f ` S)"
proof (rule rel_interior_maximal)
  show "f ` rel_interior S \<subseteq> f ` S"
    by(simp add: image_mono rel_interior_subset)
  show "openin (top_of_set (affine hull f ` S)) (f ` rel_interior S)"
  proof (rule invariance_of_domain_affine_sets)
    show "openin (top_of_set (affine hull S)) (rel_interior S)"
      by (simp add: openin_rel_interior)
    show "aff_dim (affine hull f ` S) \<le> aff_dim (affine hull S)"
      by (metis aff_dim_affine_hull aff_dim_subset fim TS order_trans)
    show "f ` rel_interior S \<subseteq> affine hull f ` S"
      by (meson \<open>f ` rel_interior S \<subseteq> f ` S\<close> hull_subset order_trans)
    show "continuous_on (rel_interior S) f"
      using contf continuous_on_subset rel_interior_subset by blast
    show "inj_on f (rel_interior S)"
      using inj_on_subset injf rel_interior_subset by blast
  qed auto
qed

lemma homeomorphic_rel_interiors_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" and aff: "aff_dim S = aff_dim T"
  shows "(rel_interior S) homeomorphic (rel_interior T)"
  using assms [unfolded homeomorphic_minimal]
  unfolding homeomorphic_def
proof (clarify elim!: ex_forward)
  fix f g
  assume S: "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" and T: "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
     and contf: "continuous_on S f" and contg: "continuous_on T g"
  then have fST: "f ` S = T" and gTS: "g ` T = S" and "inj_on f S" "inj_on g T"
    by (auto simp: inj_on_def intro: rev_image_eqI) metis+
  have fim: "f ` rel_interior S \<subseteq> rel_interior T"
    by (metis \<open>inj_on f S\<close> aff contf continuous_image_subset_rel_interior fST order_refl)
  have gim: "g ` rel_interior T \<subseteq> rel_interior S"
    by (metis \<open>inj_on g T\<close> aff contg continuous_image_subset_rel_interior gTS order_refl)
  show "homeomorphism (rel_interior S) (rel_interior T) f g"
    unfolding homeomorphism_def
  proof (intro conjI ballI)
    show gf: "\<And>x. x \<in> rel_interior S \<Longrightarrow> g (f x) = x"
      using S rel_interior_subset by blast
    show fg: "\<And>y. y \<in> rel_interior T \<Longrightarrow> f (g y) = y"
      using T mem_rel_interior_ball by blast
    have "rel_interior T \<subseteq> f ` rel_interior S"
    proof
      fix x assume "x \<in> rel_interior T"
      then have "g x \<in> rel_interior S"
        using gim by blast
      then show "x \<in> f ` rel_interior S"
        by (metis fg \<open>x \<in> rel_interior T\<close> imageI)
    qed
    moreover have "f ` rel_interior S \<subseteq> rel_interior T"
      by (metis \<open>inj_on f S\<close> aff contf continuous_image_subset_rel_interior fST order_refl)
    ultimately show "f ` rel_interior S = rel_interior T"
      by blast
    show "continuous_on (rel_interior S) f"
      using contf continuous_on_subset rel_interior_subset by blast
    have "rel_interior S \<subseteq> g ` rel_interior T"
    proof
      fix x assume "x \<in> rel_interior S"
      then have "f x \<in> rel_interior T"
        using fim by blast
      then show "x \<in> g ` rel_interior T"
        by (metis gf \<open>x \<in> rel_interior S\<close> imageI)
    qed
    then show "g ` rel_interior T = rel_interior S"
      using gim by blast
    show "continuous_on (rel_interior T) g"
      using contg continuous_on_subset rel_interior_subset by blast
  qed
qed


lemma homeomorphic_aff_dim_le:
  fixes S :: "'a::euclidean_space set" 
  assumes "S homeomorphic T" "rel_interior S \<noteq> {}"
    shows "aff_dim (affine hull S) \<le> aff_dim (affine hull T)"
proof -
  obtain f g
    where S: "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" and T: "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
      and contf: "continuous_on S f" and contg: "continuous_on T g"
    using assms [unfolded homeomorphic_minimal] by auto
  show ?thesis
  proof (rule invariance_of_dimension_affine_sets)
    show "continuous_on (rel_interior S) f"
      using contf continuous_on_subset rel_interior_subset by blast
    show "f ` rel_interior S \<subseteq> affine hull T"
      by (meson S hull_subset image_subsetI rel_interior_subset rev_subsetD)
    show "inj_on f (rel_interior S)"
      by (metis S inj_on_inverseI inj_on_subset rel_interior_subset)
  qed (simp_all add: openin_rel_interior assms)
qed

lemma homeomorphic_rel_interiors:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "rel_interior S = {} \<longleftrightarrow> rel_interior T = {}"
    shows "(rel_interior S) homeomorphic (rel_interior T)"
proof (cases "rel_interior T = {}")
  case True
  with assms show ?thesis by auto
next
  case False
  have "aff_dim (affine hull S) \<le> aff_dim (affine hull T)"
    using False assms homeomorphic_aff_dim_le by blast
  moreover have "aff_dim (affine hull T) \<le> aff_dim (affine hull S)"
    using False assms(1) homeomorphic_aff_dim_le homeomorphic_sym by auto
  ultimately have "aff_dim S = aff_dim T" by force
  then show ?thesis
    by (rule homeomorphic_rel_interiors_same_dimension [OF \<open>S homeomorphic T\<close>])
qed


lemma homeomorphic_rel_boundaries_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" and aff: "aff_dim S = aff_dim T"
  shows "(S - rel_interior S) homeomorphic (T - rel_interior T)"
  using assms [unfolded homeomorphic_minimal]
  unfolding homeomorphic_def
proof (clarify elim!: ex_forward)
  fix f g
  assume S: "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" and T: "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
     and contf: "continuous_on S f" and contg: "continuous_on T g"
  then have fST: "f ` S = T" and gTS: "g ` T = S" and "inj_on f S" "inj_on g T"
    by (auto simp: inj_on_def intro: rev_image_eqI) metis+
  have fim: "f ` rel_interior S \<subseteq> rel_interior T"
    by (metis \<open>inj_on f S\<close> aff contf continuous_image_subset_rel_interior fST order_refl)
  have gim: "g ` rel_interior T \<subseteq> rel_interior S"
    by (metis \<open>inj_on g T\<close> aff contg continuous_image_subset_rel_interior gTS order_refl)
  show "homeomorphism (S - rel_interior S) (T - rel_interior T) f g"
    unfolding homeomorphism_def
  proof (intro conjI ballI)
    show gf: "\<And>x. x \<in> S - rel_interior S \<Longrightarrow> g (f x) = x"
      using S rel_interior_subset by blast
    show fg: "\<And>y. y \<in> T - rel_interior T \<Longrightarrow> f (g y) = y"
      using T mem_rel_interior_ball by blast
    show "f ` (S - rel_interior S) = T - rel_interior T"
      using S fST fim gim by auto
    show "continuous_on (S - rel_interior S) f"
      using contf continuous_on_subset rel_interior_subset by blast
    show "g ` (T - rel_interior T) = S - rel_interior S"
      using T gTS gim fim by auto
    show "continuous_on (T - rel_interior T) g"
      using contg continuous_on_subset rel_interior_subset by blast
  qed
qed

lemma homeomorphic_rel_boundaries:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "rel_interior S = {} \<longleftrightarrow> rel_interior T = {}"
    shows "(S - rel_interior S) homeomorphic (T - rel_interior T)"
proof (cases "rel_interior T = {}")
  case True
  with assms show ?thesis by auto
next
  case False
  obtain f g
    where S: "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" and T: "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
      and contf: "continuous_on S f" and contg: "continuous_on T g"
    using  assms [unfolded homeomorphic_minimal] by auto
  have "aff_dim (affine hull S) \<le> aff_dim (affine hull T)"
    using False assms homeomorphic_aff_dim_le by blast
  moreover have "aff_dim (affine hull T) \<le> aff_dim (affine hull S)"
    by (meson False assms(1) homeomorphic_aff_dim_le homeomorphic_sym)
  ultimately have "aff_dim S = aff_dim T" by force
  then show ?thesis
    by (rule homeomorphic_rel_boundaries_same_dimension [OF \<open>S homeomorphic T\<close>])
qed

proposition uniformly_continuous_homeomorphism_UNIV_trivial:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes contf: "uniformly_continuous_on S f" and hom: "homeomorphism S UNIV f g"
  shows "S = UNIV"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (metis UNIV_I hom empty_iff homeomorphism_def image_eqI)
next
  case False
  have "inj g"
    by (metis UNIV_I hom homeomorphism_apply2 injI)
  then have "open (g ` UNIV)"
    by (blast intro: invariance_of_domain hom homeomorphism_cont2)
  then have "open S"
    using hom homeomorphism_image2 by blast
  moreover have "complete S"
    unfolding complete_def
  proof clarify
    fix \<sigma>
    assume \<sigma>: "\<forall>n. \<sigma> n \<in> S" and "Cauchy \<sigma>"
    have "Cauchy (f o \<sigma>)"
      using uniformly_continuous_imp_Cauchy_continuous \<open>Cauchy \<sigma>\<close> \<sigma> contf by blast
    then obtain l where "(f \<circ> \<sigma>) \<longlonglongrightarrow> l"
      by (auto simp: convergent_eq_Cauchy [symmetric])
    show "\<exists>l\<in>S. \<sigma> \<longlonglongrightarrow> l"
    proof
      show "g l \<in> S"
        using hom homeomorphism_image2 by blast
      have "(g \<circ> (f \<circ> \<sigma>)) \<longlonglongrightarrow> g l"
        by (meson UNIV_I \<open>(f \<circ> \<sigma>) \<longlonglongrightarrow> l\<close> continuous_on_sequentially hom homeomorphism_cont2)
      then show "\<sigma> \<longlonglongrightarrow> g l"
      proof -
        have "\<forall>n. \<sigma> n = (g \<circ> (f \<circ> \<sigma>)) n"
          by (metis (no_types) \<sigma> comp_eq_dest_lhs hom homeomorphism_apply1)
        then show ?thesis
          by (metis (no_types) LIMSEQ_iff \<open>(g \<circ> (f \<circ> \<sigma>)) \<longlonglongrightarrow> g l\<close>)
      qed
    qed
  qed
  then have "closed S"
    by (simp add: complete_eq_closed)
  ultimately show ?thesis
    using clopen [of S] False  by simp
qed

subsection\<open>Formulation of loop homotopy in terms of maps out of type complex\<close>

lemma homotopic_circlemaps_imp_homotopic_loops:
  assumes "homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f g"
   shows "homotopic_loops S (f \<circ> exp \<circ> (\<lambda>t. 2 * of_real pi * of_real t * \<i>))
                            (g \<circ> exp \<circ> (\<lambda>t. 2 * of_real pi * of_real t * \<i>))"
proof -
  have "homotopic_with_canon (\<lambda>f. True) {z. cmod z = 1} S f g"
    using assms by (auto simp: sphere_def)
  moreover have "continuous_on {0..1} (exp \<circ> (\<lambda>t. 2 * of_real pi * of_real t * \<i>))"
     by (intro continuous_intros)
  moreover have "(exp \<circ> (\<lambda>t. 2 * of_real pi * of_real t * \<i>)) ` {0..1} \<subseteq> {z. cmod z = 1}"
    by (auto simp: norm_mult)
  ultimately
  show ?thesis
    apply (simp add: homotopic_loops_def comp_assoc)
    apply (rule homotopic_with_compose_continuous_right)
      apply (auto simp: pathstart_def pathfinish_def)
    done
qed

lemma homotopic_loops_imp_homotopic_circlemaps:
  assumes "homotopic_loops S p q"
    shows "homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S
                          (p \<circ> (\<lambda>z. (Arg2pi z / (2 * pi))))
                          (q \<circ> (\<lambda>z. (Arg2pi z / (2 * pi))))"
proof -
  obtain h where conth: "continuous_on ({0..1::real} \<times> {0..1}) h"
             and him: "h ` ({0..1} \<times> {0..1}) \<subseteq> S"
             and h0: "(\<forall>x. h (0, x) = p x)"
             and h1: "(\<forall>x. h (1, x) = q x)"
             and h01: "(\<forall>t\<in>{0..1}. h (t, 1) = h (t, 0)) "
    using assms
    by (auto simp: homotopic_loops_def sphere_def homotopic_with_def pathstart_def pathfinish_def)
  define j where "j \<equiv> \<lambda>z. if 0 \<le> Im (snd z)
                          then h (fst z, Arg2pi (snd z) / (2 * pi))
                          else h (fst z, 1 - Arg2pi (cnj (snd z)) / (2 * pi))"
  have Arg2pi_eq: "1 - Arg2pi (cnj y) / (2 * pi) = Arg2pi y / (2 * pi) \<or> Arg2pi y = 0 \<and> Arg2pi (cnj y) = 0" if "cmod y = 1" for y
    using that Arg2pi_eq_0_pi Arg2pi_eq_pi by (force simp: Arg2pi_cnj field_split_simps)
  show ?thesis
  proof (simp add: homotopic_with; intro conjI ballI exI)
    show "continuous_on ({0..1} \<times> sphere 0 1) (\<lambda>w. h (fst w, Arg2pi (snd w) / (2 * pi)))"
    proof (rule continuous_on_eq)
      show j: "j x = h (fst x, Arg2pi (snd x) / (2 * pi))" if "x \<in> {0..1} \<times> sphere 0 1" for x
        using Arg2pi_eq that h01 by (force simp: j_def)
      have eq:  "S = S \<inter> (UNIV \<times> {z. 0 \<le> Im z}) \<union> S \<inter> (UNIV \<times> {z. Im z \<le> 0})" for S :: "(real*complex)set"
        by auto
      have c1: "continuous_on ({0..1} \<times> sphere 0 1 \<inter> UNIV \<times> {z. 0 \<le> Im z}) (\<lambda>x. h (fst x, Arg2pi (snd x) / (2 * pi)))"
        apply (intro continuous_intros continuous_on_compose2 [OF conth]  continuous_on_compose2 [OF continuous_on_upperhalf_Arg2pi])
            apply (auto simp: Arg2pi)
        apply (meson Arg2pi_lt_2pi linear not_le)
        done
      have c2: "continuous_on ({0..1} \<times> sphere 0 1 \<inter> UNIV \<times> {z. Im z \<le> 0}) (\<lambda>x. h (fst x, 1 - Arg2pi (cnj (snd x)) / (2 * pi)))"
        apply (intro continuous_intros continuous_on_compose2 [OF conth]  continuous_on_compose2 [OF continuous_on_upperhalf_Arg2pi])
            apply (auto simp: Arg2pi)
        apply (meson Arg2pi_lt_2pi linear not_le)
        done
      show "continuous_on ({0..1} \<times> sphere 0 1) j"
        apply (simp add: j_def)
        apply (subst eq)
        apply (rule continuous_on_cases_local)
        using Arg2pi_eq h01
        by (force simp add: eq [symmetric] closedin_closed_Int closed_Times closed_halfspace_Im_le closed_halfspace_Im_ge c1 c2)+
    qed
    have "(\<lambda>w. h (fst w, Arg2pi (snd w) / (2 * pi))) ` ({0..1} \<times> sphere 0 1) \<subseteq> h ` ({0..1} \<times> {0..1})"
      by (auto simp: Arg2pi_ge_0 Arg2pi_lt_2pi less_imp_le)
    also have "... \<subseteq> S"
      using him by blast
    finally show "(\<lambda>w. h (fst w, Arg2pi (snd w) / (2 * pi))) ` ({0..1} \<times> sphere 0 1) \<subseteq> S" .
  qed (auto simp: h0 h1)
qed

lemma simply_connected_homotopic_loops:
  "simply_connected S \<longleftrightarrow>
       (\<forall>p q. homotopic_loops S p p \<and> homotopic_loops S q q \<longrightarrow> homotopic_loops S p q)"
unfolding simply_connected_def using homotopic_loops_refl by metis


lemma simply_connected_eq_homotopic_circlemaps1:
  fixes f :: "complex \<Rightarrow> 'a::topological_space" and g :: "complex \<Rightarrow> 'a"
  assumes S: "simply_connected S"
      and contf: "continuous_on (sphere 0 1) f" and fim: "f ` (sphere 0 1) \<subseteq> S"
      and contg: "continuous_on (sphere 0 1) g" and gim: "g ` (sphere 0 1) \<subseteq> S"
    shows "homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f g"
proof -
  have "homotopic_loops S (f \<circ> exp \<circ> (\<lambda>t. of_real(2 * pi * t) * \<i>)) (g \<circ> exp \<circ> (\<lambda>t. of_real(2 * pi *  t) * \<i>))"
    apply (rule S [unfolded simply_connected_homotopic_loops, rule_format])
    apply (simp add: homotopic_circlemaps_imp_homotopic_loops contf fim contg gim)
    done
  then show ?thesis
    apply (rule homotopic_with_eq [OF homotopic_loops_imp_homotopic_circlemaps])
      apply (auto simp: o_def complex_norm_eq_1_exp mult.commute)
    done
qed

lemma simply_connected_eq_homotopic_circlemaps2a:
  fixes h :: "complex \<Rightarrow> 'a::topological_space"
  assumes conth: "continuous_on (sphere 0 1) h" and him: "h ` (sphere 0 1) \<subseteq> S"
      and hom: "\<And>f g::complex \<Rightarrow> 'a.
                \<lbrakk>continuous_on (sphere 0 1) f; f ` (sphere 0 1) \<subseteq> S;
                continuous_on (sphere 0 1) g; g ` (sphere 0 1) \<subseteq> S\<rbrakk>
                \<Longrightarrow> homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f g"
            shows "\<exists>a. homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S h (\<lambda>x. a)"
    apply (rule_tac x="h 1" in exI)
    apply (rule hom)
    using assms by (auto)

lemma simply_connected_eq_homotopic_circlemaps2b:
  fixes S :: "'a::real_normed_vector set"
  assumes "\<And>f g::complex \<Rightarrow> 'a.
                \<lbrakk>continuous_on (sphere 0 1) f; f ` (sphere 0 1) \<subseteq> S;
                continuous_on (sphere 0 1) g; g ` (sphere 0 1) \<subseteq> S\<rbrakk>
                \<Longrightarrow> homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f g"
  shows "path_connected S"
proof (clarsimp simp add: path_connected_eq_homotopic_points)
  fix a b
  assume "a \<in> S" "b \<in> S"
  then show "homotopic_loops S (linepath a a) (linepath b b)"
    using homotopic_circlemaps_imp_homotopic_loops [OF assms [of "\<lambda>x. a" "\<lambda>x. b"]]
    by (auto simp: o_def linepath_def)
qed

lemma simply_connected_eq_homotopic_circlemaps3:
  fixes h :: "complex \<Rightarrow> 'a::real_normed_vector"
  assumes "path_connected S"
      and hom: "\<And>f::complex \<Rightarrow> 'a.
                  \<lbrakk>continuous_on (sphere 0 1) f; f `(sphere 0 1) \<subseteq> S\<rbrakk>
                  \<Longrightarrow> \<exists>a. homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f (\<lambda>x. a)"
    shows "simply_connected S"
proof (clarsimp simp add: simply_connected_eq_contractible_loop_some assms)
  fix p
  assume p: "path p" "path_image p \<subseteq> S" "pathfinish p = pathstart p"
  then have "homotopic_loops S p p"
    by (simp add: homotopic_loops_refl)
  then obtain a where homp: "homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S (p \<circ> (\<lambda>z. Arg2pi z / (2 * pi))) (\<lambda>x. a)"
    by (metis homotopic_with_imp_subset2 homotopic_loops_imp_homotopic_circlemaps homotopic_with_imp_continuous hom)
  show "\<exists>a. a \<in> S \<and> homotopic_loops S p (linepath a a)"
  proof (intro exI conjI)
    show "a \<in> S"
      using homotopic_with_imp_subset2 [OF homp]
      by (metis dist_0_norm image_subset_iff mem_sphere norm_one)
    have teq: "\<And>t. \<lbrakk>0 \<le> t; t \<le> 1\<rbrakk>
               \<Longrightarrow> t = Arg2pi (exp (2 * of_real pi * of_real t * \<i>)) / (2 * pi) \<or> t=1 \<and> Arg2pi (exp (2 * of_real pi * of_real t * \<i>)) = 0"
      using Arg2pi_of_real [of 1] by (force simp: Arg2pi_exp)
    have "homotopic_loops S p (p \<circ> (\<lambda>z. Arg2pi z / (2 * pi)) \<circ> exp \<circ> (\<lambda>t. 2 * complex_of_real pi * complex_of_real t * \<i>))"
      using p teq by (fastforce simp: pathfinish_def pathstart_def intro: homotopic_loops_eq [OF p])
    then show "homotopic_loops S p (linepath a a)"
      by (simp add: linepath_refl  homotopic_loops_trans [OF _ homotopic_circlemaps_imp_homotopic_loops [OF homp, simplified K_record_comp]])
  qed
qed


proposition simply_connected_eq_homotopic_circlemaps:
  fixes S :: "'a::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
         (\<forall>f g::complex \<Rightarrow> 'a.
              continuous_on (sphere 0 1) f \<and> f ` (sphere 0 1) \<subseteq> S \<and>
              continuous_on (sphere 0 1) g \<and> g ` (sphere 0 1) \<subseteq> S
              \<longrightarrow> homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f g)"
  apply (rule iffI)
   apply (blast dest: simply_connected_eq_homotopic_circlemaps1)
  by (simp add: simply_connected_eq_homotopic_circlemaps2a simply_connected_eq_homotopic_circlemaps2b simply_connected_eq_homotopic_circlemaps3)

proposition simply_connected_eq_contractible_circlemap:
  fixes S :: "'a::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
         path_connected S \<and>
         (\<forall>f::complex \<Rightarrow> 'a.
              continuous_on (sphere 0 1) f \<and> f `(sphere 0 1) \<subseteq> S
              \<longrightarrow> (\<exists>a. homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f (\<lambda>x. a)))"
  apply (rule iffI)
   apply (simp add: simply_connected_eq_homotopic_circlemaps1 simply_connected_eq_homotopic_circlemaps2a simply_connected_eq_homotopic_circlemaps2b)
  using simply_connected_eq_homotopic_circlemaps3 by blast

corollary homotopy_eqv_simple_connectedness:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  shows "S homotopy_eqv T \<Longrightarrow> simply_connected S \<longleftrightarrow> simply_connected T"
  by (simp add: simply_connected_eq_homotopic_circlemaps homotopy_eqv_homotopic_triviality)


subsection\<open>Homeomorphism of simple closed curves to circles\<close>

proposition homeomorphic_simple_path_image_circle:
  fixes a :: complex and \<gamma> :: "real \<Rightarrow> 'a::t2_space"
  assumes "simple_path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>" and "0 < r"
  shows "(path_image \<gamma>) homeomorphic sphere a r"
proof -
  have "homotopic_loops (path_image \<gamma>) \<gamma> \<gamma>"
    by (simp add: assms homotopic_loops_refl simple_path_imp_path)
  then have hom: "homotopic_with_canon (\<lambda>h. True) (sphere 0 1) (path_image \<gamma>)
               (\<gamma> \<circ> (\<lambda>z. Arg2pi z / (2*pi))) (\<gamma> \<circ> (\<lambda>z. Arg2pi z / (2*pi)))"
    by (rule homotopic_loops_imp_homotopic_circlemaps)
  have "\<exists>g. homeomorphism (sphere 0 1) (path_image \<gamma>) (\<gamma> \<circ> (\<lambda>z. Arg2pi z / (2*pi))) g"
  proof (rule homeomorphism_compact)
    show "continuous_on (sphere 0 1) (\<gamma> \<circ> (\<lambda>z. Arg2pi z / (2*pi)))"
      using hom homotopic_with_imp_continuous by blast
    show "inj_on (\<gamma> \<circ> (\<lambda>z. Arg2pi z / (2*pi))) (sphere 0 1)"
    proof
      fix x y
      assume xy: "x \<in> sphere 0 1" "y \<in> sphere 0 1"
         and eq: "(\<gamma> \<circ> (\<lambda>z. Arg2pi z / (2*pi))) x = (\<gamma> \<circ> (\<lambda>z. Arg2pi z / (2*pi))) y"
      then have "(Arg2pi x / (2*pi)) = (Arg2pi y / (2*pi))"
      proof -
        have "(Arg2pi x / (2*pi)) \<in> {0..1}" "(Arg2pi y / (2*pi)) \<in> {0..1}"
          using Arg2pi_ge_0 Arg2pi_lt_2pi dual_order.strict_iff_order by fastforce+
        with eq show ?thesis
          using \<open>simple_path \<gamma>\<close> Arg2pi_lt_2pi unfolding simple_path_def o_def
          by (metis eq_divide_eq_1 not_less_iff_gr_or_eq)
      qed
      with xy show "x = y"
        by (metis is_Arg_def Arg2pi Arg2pi_0 dist_0_norm divide_cancel_right dual_order.strict_iff_order mem_sphere)
    qed
    have "\<And>z. cmod z = 1 \<Longrightarrow> \<exists>x\<in>{0..1}. \<gamma> (Arg2pi z / (2*pi)) = \<gamma> x"
       by (metis Arg2pi_ge_0 Arg2pi_lt_2pi atLeastAtMost_iff divide_less_eq_1 less_eq_real_def zero_less_mult_iff pi_gt_zero zero_le_divide_iff zero_less_numeral)
     moreover have "\<exists>z\<in>sphere 0 1. \<gamma> x = \<gamma> (Arg2pi z / (2*pi))" if "0 \<le> x" "x \<le> 1" for x
     proof (cases "x=1")
       case True
       with Arg2pi_of_real [of 1] loop show ?thesis
         by (rule_tac x=1 in bexI) (auto simp: pathfinish_def pathstart_def \<open>0 \<le> x\<close>)
     next
       case False
       then have *: "(Arg2pi (exp (\<i>*(2* of_real pi* of_real x))) / (2*pi)) = x"
         using that by (auto simp: Arg2pi_exp field_split_simps)
       show ?thesis
         by (rule_tac x="exp(\<i> * of_real(2*pi*x))" in bexI) (auto simp: *)
    qed
    ultimately show "(\<gamma> \<circ> (\<lambda>z. Arg2pi z / (2*pi))) ` sphere 0 1 = path_image \<gamma>"
      by (auto simp: path_image_def image_iff)
    qed auto
    then have "path_image \<gamma> homeomorphic sphere (0::complex) 1"
      using homeomorphic_def homeomorphic_sym by blast
  also have "... homeomorphic sphere a r"
    by (simp add: assms homeomorphic_spheres)
  finally show ?thesis .
qed

lemma homeomorphic_simple_path_images:
  fixes \<gamma>1 :: "real \<Rightarrow> 'a::t2_space" and \<gamma>2 :: "real \<Rightarrow> 'b::t2_space"
  assumes "simple_path \<gamma>1" and loop: "pathfinish \<gamma>1 = pathstart \<gamma>1"
  assumes "simple_path \<gamma>2" and loop: "pathfinish \<gamma>2 = pathstart \<gamma>2"
  shows "(path_image \<gamma>1) homeomorphic (path_image \<gamma>2)"
  by (meson assms homeomorphic_simple_path_image_circle homeomorphic_sym homeomorphic_trans loop pi_gt_zero)

subsection\<open>Dimension-based conditions for various homeomorphisms\<close>

lemma homeomorphic_subspaces_eq:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "subspace S" "subspace T"
  shows "S homeomorphic T \<longleftrightarrow> dim S = dim T"
proof
  assume "S homeomorphic T"
  then obtain f g where hom: "homeomorphism S T f g"
    using homeomorphic_def by blast
  show "dim S = dim T"
  proof (rule order_antisym)
    show "dim S \<le> dim T"
      by (metis assms dual_order.refl inj_onI homeomorphism_cont1 [OF hom] homeomorphism_apply1 [OF hom] homeomorphism_image1 [OF hom] continuous_injective_image_subspace_dim_le)
    show "dim T \<le> dim S"
      by (metis assms dual_order.refl inj_onI homeomorphism_cont2 [OF hom] homeomorphism_apply2 [OF hom] homeomorphism_image2 [OF hom] continuous_injective_image_subspace_dim_le)
  qed
next
  assume "dim S = dim T"
  then show "S homeomorphic T"
    by (simp add: assms homeomorphic_subspaces)
qed

lemma homeomorphic_affine_sets_eq:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "affine S" "affine T"
  shows "S homeomorphic T \<longleftrightarrow> aff_dim S = aff_dim T"
proof (cases "S = {} \<or> T = {}")
  case True
  then show ?thesis
    using assms homeomorphic_affine_sets by force
next
  case False
  then obtain a b where "a \<in> S" "b \<in> T"
    by blast
  then have "subspace ((+) (- a) ` S)" "subspace ((+) (- b) ` T)"
    using affine_diffs_subspace assms by blast+
  then show ?thesis
    by (metis affine_imp_convex assms homeomorphic_affine_sets homeomorphic_convex_sets)
qed

lemma homeomorphic_hyperplanes_eq:
  fixes a :: "'a::euclidean_space" and c :: "'b::euclidean_space"
  assumes "a \<noteq> 0" "c \<noteq> 0"
  shows "({x. a \<bullet> x = b} homeomorphic {x. c \<bullet> x = d} \<longleftrightarrow> DIM('a) = DIM('b))"
  apply (auto simp: homeomorphic_affine_sets_eq affine_hyperplane assms)
  by (metis DIM_positive Suc_pred)

lemma homeomorphic_UNIV_UNIV:
  shows "(UNIV::'a set) homeomorphic (UNIV::'b set) \<longleftrightarrow>
    DIM('a::euclidean_space) = DIM('b::euclidean_space)"
  by (simp add: homeomorphic_subspaces_eq)

lemma simply_connected_sphere_gen:
   assumes "convex S" "bounded S" and 3: "3 \<le> aff_dim S"
   shows "simply_connected(rel_frontier S)"
proof -
  have pa: "path_connected (rel_frontier S)"
    using assms by (simp add: path_connected_sphere_gen)
  show ?thesis
  proof (clarsimp simp add: simply_connected_eq_contractible_circlemap pa)
    fix f
    assume f: "continuous_on (sphere (0::complex) 1) f" "f ` sphere 0 1 \<subseteq> rel_frontier S"
    have eq: "sphere (0::complex) 1 = rel_frontier(cball 0 1)"
      by simp
    have "convex (cball (0::complex) 1)"
      by (rule convex_cball)
    then obtain c where "homotopic_with_canon (\<lambda>z. True) (sphere (0::complex) 1) (rel_frontier S) f (\<lambda>x. c)"
      apply (rule inessential_spheremap_lowdim_gen [OF _ bounded_cball \<open>convex S\<close> \<open>bounded S\<close>, where f=f])
      using f 3
         apply (auto simp: aff_dim_cball)
      done
    then show "\<exists>a. homotopic_with_canon (\<lambda>h. True) (sphere 0 1) (rel_frontier S) f (\<lambda>x. a)"
      by blast
  qed
qed

subsection\<open>more invariance of domain\<close>(*FIX ME title? *)

proposition invariance_of_domain_sphere_affine_set_gen:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and injf: "inj_on f S" and fim: "f ` S \<subseteq> T"
      and U: "bounded U" "convex U"
      and "affine T" and affTU: "aff_dim T < aff_dim U"
      and ope: "openin (top_of_set (rel_frontier U)) S"
   shows "openin (top_of_set T) (f ` S)"
proof (cases "rel_frontier U = {}")
  case True
  then show ?thesis
    using ope openin_subset by force
next
  case False
  obtain b c where b: "b \<in> rel_frontier U" and c: "c \<in> rel_frontier U" and "b \<noteq> c"
    using \<open>bounded U\<close> rel_frontier_not_sing [of U] subset_singletonD False  by fastforce
  obtain V :: "'a set" where "affine V" and affV: "aff_dim V = aff_dim U - 1"
  proof (rule choose_affine_subset [OF affine_UNIV])
    show "- 1 \<le> aff_dim U - 1"
      by (metis aff_dim_empty aff_dim_geq aff_dim_negative_iff affTU diff_0 diff_right_mono not_le)
    show "aff_dim U - 1 \<le> aff_dim (UNIV::'a set)"
      by (metis aff_dim_UNIV aff_dim_le_DIM le_cases not_le zle_diff1_eq)
  qed auto
  have SU: "S \<subseteq> rel_frontier U"
    using ope openin_imp_subset by auto
  have homb: "rel_frontier U - {b} homeomorphic V"
   and homc: "rel_frontier U - {c} homeomorphic V"
    using homeomorphic_punctured_sphere_affine_gen [of U _ V]
    by (simp_all add: \<open>affine V\<close> affV U b c)
  then obtain g h j k
           where gh: "homeomorphism (rel_frontier U - {b}) V g h"
             and jk: "homeomorphism (rel_frontier U - {c}) V j k"
    by (auto simp: homeomorphic_def)
  with SU have hgsub: "(h ` g ` (S - {b})) \<subseteq> S" and kjsub: "(k ` j ` (S - {c})) \<subseteq> S"
    by (simp_all add: homeomorphism_def subset_eq)
  have [simp]: "aff_dim T \<le> aff_dim V"
    by (simp add: affTU affV)
  have "openin (top_of_set T) ((f \<circ> h) ` g ` (S - {b}))"
  proof (rule invariance_of_domain_affine_sets [OF _ \<open>affine V\<close>])
    have "openin (top_of_set (rel_frontier U - {b})) (S - {b})"
      by (meson Diff_mono Diff_subset SU ope openin_delete openin_subset_trans order_refl)
    then show "openin (top_of_set V) (g ` (S - {b}))"
      by (rule homeomorphism_imp_open_map [OF gh])
    show "continuous_on (g ` (S - {b})) (f \<circ> h)"
    proof (rule continuous_on_compose)
      show "continuous_on (g ` (S - {b})) h"
        by (meson Diff_mono SU homeomorphism_def homeomorphism_of_subsets gh set_eq_subset)
    qed (use contf continuous_on_subset hgsub in blast)
    show "inj_on (f \<circ> h) (g ` (S - {b}))"
      using kjsub
      apply (clarsimp simp add: inj_on_def)
      by (metis SU b homeomorphism_def inj_onD injf insert_Diff insert_iff gh rev_subsetD)
    show "(f \<circ> h) ` g ` (S - {b}) \<subseteq> T"
      by (metis fim image_comp image_mono hgsub subset_trans)
  qed (auto simp: assms)
  moreover
  have "openin (top_of_set T) ((f \<circ> k) ` j ` (S - {c}))"
  proof (rule invariance_of_domain_affine_sets [OF _ \<open>affine V\<close>])
    show "openin (top_of_set V) (j ` (S - {c}))"
      by (meson Diff_mono Diff_subset SU ope openin_delete openin_subset_trans order_refl homeomorphism_imp_open_map [OF jk])
    show "continuous_on (j ` (S - {c})) (f \<circ> k)"
    proof (rule continuous_on_compose)
      show "continuous_on (j ` (S - {c})) k"
        by (meson Diff_mono SU homeomorphism_def homeomorphism_of_subsets jk set_eq_subset)
    qed (use contf continuous_on_subset kjsub in blast)
    show "inj_on (f \<circ> k) (j ` (S - {c}))"
      using kjsub
      apply (clarsimp simp add: inj_on_def)
      by (metis SU c homeomorphism_def inj_onD injf insert_Diff insert_iff jk rev_subsetD)
    show "(f \<circ> k) ` j ` (S - {c}) \<subseteq> T"
      by (metis fim image_comp image_mono kjsub subset_trans)
  qed (auto simp: assms)
  ultimately have "openin (top_of_set T) ((f \<circ> h) ` g ` (S - {b}) \<union> ((f \<circ> k) ` j ` (S - {c})))"
    by (rule openin_Un)
  moreover have "(f \<circ> h) ` g ` (S - {b}) = f ` (S - {b})"
  proof -
    have "h ` g ` (S - {b}) = (S - {b})"
    proof
      show "h ` g ` (S - {b}) \<subseteq> S - {b}"
        using homeomorphism_apply1 [OF gh] SU
        by (fastforce simp add: image_iff image_subset_iff)
      show "S - {b} \<subseteq> h ` g ` (S - {b})"
        apply clarify
        by  (metis SU subsetD homeomorphism_apply1 [OF gh] image_iff member_remove remove_def)
    qed
    then show ?thesis
      by (metis image_comp)
  qed
  moreover have "(f \<circ> k) ` j ` (S - {c}) = f ` (S - {c})"
  proof -
    have "k ` j ` (S - {c}) = (S - {c})"
    proof
      show "k ` j ` (S - {c}) \<subseteq> S - {c}"
        using homeomorphism_apply1 [OF jk] SU
        by (fastforce simp add: image_iff image_subset_iff)
      show "S - {c} \<subseteq> k ` j ` (S - {c})"
        apply clarify
        by  (metis SU subsetD homeomorphism_apply1 [OF jk] image_iff member_remove remove_def)
    qed
    then show ?thesis
      by (metis image_comp)
  qed
  moreover have "f ` (S - {b}) \<union> f ` (S - {c}) = f ` (S)"
    using \<open>b \<noteq> c\<close> by blast
  ultimately show ?thesis
    by simp
qed


lemma invariance_of_domain_sphere_affine_set:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and injf: "inj_on f S" and fim: "f ` S \<subseteq> T"
      and "r \<noteq> 0" "affine T" and affTU: "aff_dim T < DIM('a)"
      and ope: "openin (top_of_set (sphere a r)) S"
   shows "openin (top_of_set T) (f ` S)"
proof (cases "sphere a r = {}")
  case True
  then show ?thesis
    using ope openin_subset by force
next
  case False
  show ?thesis
  proof (rule invariance_of_domain_sphere_affine_set_gen [OF contf injf fim bounded_cball convex_cball \<open>affine T\<close>])
    show "aff_dim T < aff_dim (cball a r)"
      by (metis False affTU aff_dim_cball assms(4) linorder_cases sphere_empty)
    show "openin (top_of_set (rel_frontier (cball a r))) S"
      by (simp add: \<open>r \<noteq> 0\<close> ope)
  qed
qed

lemma no_embedding_sphere_lowdim:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on (sphere a r) f" and injf: "inj_on f (sphere a r)" and "r > 0"
   shows "DIM('a) \<le> DIM('b)"
proof -
  have "False" if "DIM('a) > DIM('b)"
  proof -
    have "compact (f ` sphere a r)"
      using compact_continuous_image
      by (simp add: compact_continuous_image contf)
    then have "\<not> open (f ` sphere a r)"
      using compact_open
      by (metis assms(3) image_is_empty not_less_iff_gr_or_eq sphere_eq_empty)
    then show False
      using invariance_of_domain_sphere_affine_set [OF contf injf subset_UNIV] \<open>r > 0\<close>
      by (metis aff_dim_UNIV affine_UNIV less_irrefl of_nat_less_iff open_openin openin_subtopology_self subtopology_UNIV that)
  qed
  then show ?thesis
    using not_less by blast
qed

lemma simply_connected_sphere:
  fixes a :: "'a::euclidean_space"
  assumes "3 \<le> DIM('a)"
    shows "simply_connected(sphere a r)"
proof (cases rule: linorder_cases [of r 0])
  case less
  then show ?thesis by simp
next
  case equal
  then show ?thesis  by (auto simp: convex_imp_simply_connected)
next
  case greater
  then show ?thesis
    using simply_connected_sphere_gen [of "cball a r"] assms
    by (simp add: aff_dim_cball)
qed

lemma simply_connected_sphere_eq:
  fixes a :: "'a::euclidean_space"
  shows "simply_connected(sphere a r) \<longleftrightarrow> 3 \<le> DIM('a) \<or> r \<le> 0"  (is "?lhs = ?rhs")
proof (cases "r \<le> 0")
  case True
  have "simply_connected (sphere a r)"
    using True less_eq_real_def by (auto intro: convex_imp_simply_connected)
  with True show ?thesis by auto
next
  case False
  show ?thesis
  proof
    assume L: ?lhs
    have "False" if "DIM('a) = 1 \<or> DIM('a) = 2"
      using that
    proof
      assume "DIM('a) = 1"
      with L show False
        using connected_sphere_eq simply_connected_imp_connected
        by (metis False Suc_1 not_less_eq_eq order_refl)
    next
      assume "DIM('a) = 2"
      then have "sphere a r homeomorphic sphere (0::complex) 1"
        by (metis DIM_complex False homeomorphic_spheres_gen not_less zero_less_one)
      then have "simply_connected(sphere (0::complex) 1)"
        using L homeomorphic_simply_connected_eq by blast
      then obtain a::complex where "homotopic_with_canon (\<lambda>h. True) (sphere 0 1) (sphere 0 1) id (\<lambda>x. a)"
        by (metis continuous_on_id' id_apply image_id subset_refl simply_connected_eq_contractible_circlemap)
      then show False
        using contractible_sphere contractible_def not_one_le_zero by blast
    qed
    with False show ?rhs
      apply simp
      by (metis DIM_ge_Suc0 le_antisym not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3)
  next
    assume ?rhs
    with False show ?lhs by (simp add: simply_connected_sphere)
  qed
qed


lemma simply_connected_punctured_universe_eq:
  fixes a :: "'a::euclidean_space"
  shows "simply_connected(- {a}) \<longleftrightarrow> 3 \<le> DIM('a)"
proof -
  have [simp]: "a \<in> rel_interior (cball a 1)"
    by (simp add: rel_interior_nonempty_interior)
  have [simp]: "affine hull cball a 1 - {a} = -{a}"
    by (metis Compl_eq_Diff_UNIV aff_dim_cball aff_dim_lt_full not_less_iff_gr_or_eq zero_less_one)
  have "sphere a 1 homotopy_eqv - {a}"
    using homotopy_eqv_rel_frontier_punctured_affine_hull [of "cball a 1" a] by auto
  then have "simply_connected(- {a}) \<longleftrightarrow> simply_connected(sphere a 1)"
    using homotopy_eqv_simple_connectedness by blast
  also have "...  \<longleftrightarrow> 3 \<le> DIM('a)"
    by (simp add: simply_connected_sphere_eq)
  finally show ?thesis .
qed

lemma not_simply_connected_circle:
  fixes a :: complex
  shows "0 < r \<Longrightarrow> \<not> simply_connected(sphere a r)"
by (simp add: simply_connected_sphere_eq)


proposition simply_connected_punctured_convex:
  fixes a :: "'a::euclidean_space"
  assumes "convex S" and 3: "3 \<le> aff_dim S"
    shows "simply_connected(S - {a})"
proof (cases "a \<in> rel_interior S")
  case True
  then obtain e where "a \<in> S" "0 < e" and e: "cball a e \<inter> affine hull S \<subseteq> S"
    by (auto simp: rel_interior_cball)
  have con: "convex (cball a e \<inter> affine hull S)"
    by (simp add: convex_Int)
  have bo: "bounded (cball a e \<inter> affine hull S)"
    by (simp add: bounded_Int)
  have "affine hull S \<inter> interior (cball a e) \<noteq> {}"
    using \<open>0 < e\<close> \<open>a \<in> S\<close> hull_subset by fastforce
  then have "3 \<le> aff_dim (affine hull S \<inter> cball a e)"
    by (simp add: 3 aff_dim_convex_Int_nonempty_interior [OF convex_affine_hull])
  also have "... = aff_dim (cball a e \<inter> affine hull S)"
    by (simp add: Int_commute)
  finally have "3 \<le> aff_dim (cball a e \<inter> affine hull S)" .
  moreover have "rel_frontier (cball a e \<inter> affine hull S) homotopy_eqv S - {a}"
  proof (rule homotopy_eqv_rel_frontier_punctured_convex)
    show "a \<in> rel_interior (cball a e \<inter> affine hull S)"
      by (meson IntI Int_mono \<open>a \<in> S\<close> \<open>0 < e\<close> e \<open>cball a e \<inter> affine hull S \<subseteq> S\<close> ball_subset_cball centre_in_cball dual_order.strict_implies_order hull_inc hull_mono mem_rel_interior_ball)
    have "closed (cball a e \<inter> affine hull S)"
      by blast
    then show "rel_frontier (cball a e \<inter> affine hull S) \<subseteq> S"
      by (metis Diff_subset closure_closed dual_order.trans e rel_frontier_def)
    show "S \<subseteq> affine hull (cball a e \<inter> affine hull S)"
      by (metis (no_types, lifting) IntI \<open>a \<in> S\<close> \<open>0 < e\<close> affine_hull_convex_Int_nonempty_interior centre_in_ball convex_affine_hull empty_iff hull_subset inf_commute interior_cball subsetCE subsetI)
    qed (auto simp: assms con bo)
  ultimately show ?thesis
    using homotopy_eqv_simple_connectedness simply_connected_sphere_gen [OF con bo]
    by blast
next
  case False
  then have "rel_interior S \<subseteq> S - {a}"
    by (simp add: False rel_interior_subset subset_Diff_insert)
  moreover have "S - {a} \<subseteq> closure S"
    by (meson Diff_subset closure_subset subset_trans)
  ultimately show ?thesis
    by (metis contractible_imp_simply_connected contractible_convex_tweak_boundary_points [OF \<open>convex S\<close>])
qed

corollary simply_connected_punctured_universe:
  fixes a :: "'a::euclidean_space"
  assumes "3 \<le> DIM('a)"
  shows "simply_connected(- {a})"
proof -
  have [simp]: "affine hull cball a 1 = UNIV"
    by (simp add: aff_dim_cball affine_hull_UNIV)
  have "a \<in> rel_interior (cball a 1)"
    by (simp add: rel_interior_interior)
  then
  have "simply_connected (rel_frontier (cball a 1)) = simply_connected (affine hull cball a 1 - {a})"
    using homotopy_eqv_rel_frontier_punctured_affine_hull homotopy_eqv_simple_connectedness by blast
  then show ?thesis
    using simply_connected_sphere [of a 1, OF assms] by (auto simp: Compl_eq_Diff_UNIV)
qed


subsection\<open>The power, squaring and exponential functions as covering maps\<close>

proposition covering_space_power_punctured_plane:
  assumes "0 < n"
    shows "covering_space (- {0}) (\<lambda>z::complex. z^n) (- {0})"
proof -
  consider "n = 1" | "2 \<le> n" using assms by linarith
  then obtain e where "0 < e"
                and e: "\<And>w z. cmod(w - z) < e * cmod z \<Longrightarrow> (w^n = z^n \<longleftrightarrow> w = z)"
  proof cases
    assume "n = 1" then show ?thesis
      by (rule_tac e=1 in that) auto
  next
    assume "2 \<le> n"
    have eq_if_pow_eq:
         "w = z" if lt: "cmod (w - z) < 2 * sin (pi / real n) * cmod z"
                 and eq: "w^n = z^n" for w z
    proof (cases "z = 0")
      case True with eq assms show ?thesis by (auto simp: power_0_left)
    next
      case False
      then have "z \<noteq> 0" by auto
      have "(w/z)^n = 1"
        by (metis False divide_self_if eq power_divide power_one)
      then obtain j where j: "w / z = exp (2 * of_real pi * \<i> * j / n)" and "j < n"
        using Suc_leI assms \<open>2 \<le> n\<close> complex_roots_unity [THEN eqset_imp_iff, of n "w/z"]
        by force
      have "cmod (w/z - 1) < 2 * sin (pi / real n)"
        using lt assms \<open>z \<noteq> 0\<close> by (simp add: field_split_simps norm_divide)
      then have "cmod (exp (\<i> * of_real (2 * pi * j / n)) - 1) < 2 * sin (pi / real n)"
        by (simp add: j field_simps)
      then have "2 * \<bar>sin((2 * pi * j / n) / 2)\<bar> < 2 * sin (pi / real n)"
        by (simp only: dist_exp_i_1)
      then have sin_less: "sin((pi * j / n)) < sin (pi / real n)"
        by (simp add: field_simps)
      then have "w / z = 1"
      proof (cases "j = 0")
        case True then show ?thesis by (auto simp: j)
      next
        case False
        then have "sin (pi / real n) \<le> sin((pi * j / n))"
        proof (cases "j / n \<le> 1/2")
          case True
          show ?thesis
            using \<open>j \<noteq> 0 \<close> \<open>j < n\<close> True
            by (intro sin_monotone_2pi_le) (auto simp: field_simps intro: order_trans [of _ 0])
        next
          case False
          then have seq: "sin(pi * j / n) = sin(pi * (n - j) / n)"
            using \<open>j < n\<close> by (simp add: algebra_simps diff_divide_distrib of_nat_diff)
          show ?thesis
            unfolding  seq
            using \<open>j < n\<close> False
            by (intro sin_monotone_2pi_le) (auto simp: field_simps intro: order_trans [of _ 0])
        qed
        with sin_less show ?thesis by force
      qed
      then show ?thesis by simp
    qed
    show ?thesis
    proof
      show "0 < 2 * sin (pi / real n)"
        by (force simp: \<open>2 \<le> n\<close> sin_pi_divide_n_gt_0)
    qed (meson eq_if_pow_eq)
  qed
  have zn1: "continuous_on (- {0}) (\<lambda>z::complex. z^n)"
    by (rule continuous_intros)+
  have zn2: "(\<lambda>z::complex. z^n) ` (- {0}) = - {0}"
    using assms by (auto simp: image_def elim: exists_complex_root_nonzero [where n = n])
  have zn3: "\<exists>T. z^n \<in> T \<and> open T \<and> 0 \<notin> T \<and>
               (\<exists>v. \<Union>v = -{0} \<inter> (\<lambda>z. z ^ n) -` T \<and>
                    (\<forall>u\<in>v. open u \<and> 0 \<notin> u) \<and>
                    pairwise disjnt v \<and>
                    (\<forall>u\<in>v. Ex (homeomorphism u T (\<lambda>z. z^n))))"
           if "z \<noteq> 0" for z::complex
  proof -
    define d where "d \<equiv> min (1/2) (e/4) * norm z"
    have "0 < d"
      by (simp add: d_def \<open>0 < e\<close> \<open>z \<noteq> 0\<close>)
    have iff_x_eq_y: "x^n = y^n \<longleftrightarrow> x = y"
         if eq: "w^n = z^n" and x: "x \<in> ball w d" and y: "y \<in> ball w d" for w x y
    proof -
      have [simp]: "norm z = norm w" using that
        by (simp add: assms power_eq_imp_eq_norm)
      show ?thesis
      proof (cases "w = 0")
        case True with \<open>z \<noteq> 0\<close> assms eq
        show ?thesis by (auto simp: power_0_left)
      next
        case False
        have "cmod (x - y) < 2*d"
          using x y
          by (simp add: dist_norm [symmetric]) (metis dist_commute mult_2 dist_triangle_less_add)
        also have "... \<le> 2 * e / 4 * norm w"
          using \<open>e > 0\<close> by (simp add: d_def min_mult_distrib_right)
        also have "... = e * (cmod w / 2)"
          by simp
        also have "... \<le> e * cmod y"
        proof (rule mult_left_mono)
          have "cmod (w - y) < cmod w / 2 \<Longrightarrow> cmod w / 2 \<le> cmod y"
            by (metis (no_types) dist_0_norm dist_norm norm_triangle_half_l not_le order_less_irrefl)
          then show "cmod w / 2 \<le> cmod y"
            using y by (simp add: dist_norm d_def min_mult_distrib_right)
        qed (use \<open>e > 0\<close> in auto)
        finally have "cmod (x - y) < e * cmod y" .
        then show ?thesis by (rule e)
      qed
    qed
    then have inj: "inj_on (\<lambda>w. w^n) (ball z d)"
      by (simp add: inj_on_def)
    have cont: "continuous_on (ball z d) (\<lambda>w. w ^ n)"
      by (intro continuous_intros)
    have noncon: "\<not> (\<lambda>w::complex. w^n) constant_on UNIV"
      by (metis UNIV_I assms constant_on_def power_one zero_neq_one zero_power)
    have im_eq: "(\<lambda>w. w^n) ` ball z' d = (\<lambda>w. w^n) ` ball z d"
                if z': "z'^n = z^n" for z'
    proof -
      have nz': "norm z' = norm z" using that assms power_eq_imp_eq_norm by blast
      have "(w \<in> (\<lambda>w. w^n) ` ball z' d) = (w \<in> (\<lambda>w. w^n) ` ball z d)" for w
      proof (cases "w=0")
        case True with assms show ?thesis
          by (simp add: image_def ball_def nz')
      next
        case False
        have "z' \<noteq> 0" using \<open>z \<noteq> 0\<close> nz' by force
        have 1: "(z*x / z')^n = x^n" if "x \<noteq> 0" for x
          using z' that by (simp add: field_simps \<open>z \<noteq> 0\<close>)
        have 2: "cmod (z - z * x / z') = cmod (z' - x)" if "x \<noteq> 0" for x
        proof -
          have "cmod (z - z * x / z') = cmod z * cmod (1 - x / z')"
            by (metis (no_types) ab_semigroup_mult_class.mult_ac(1) divide_complex_def mult.right_neutral norm_mult right_diff_distrib')
          also have "... = cmod z' * cmod (1 - x / z')"
            by (simp add: nz')
          also have "... = cmod (z' - x)"
            by (simp add: \<open>z' \<noteq> 0\<close> diff_divide_eq_iff norm_divide)
          finally show ?thesis .
        qed
        have 3: "(z'*x / z)^n = x^n" if "x \<noteq> 0" for x
          using z' that by (simp add: field_simps \<open>z \<noteq> 0\<close>)
        have 4: "cmod (z' - z' * x / z) = cmod (z - x)" if "x \<noteq> 0" for x
        proof -
          have "cmod (z * (1 - x * inverse z)) = cmod (z - x)"
            by (metis \<open>z \<noteq> 0\<close> diff_divide_distrib divide_complex_def divide_self_if nonzero_eq_divide_eq semiring_normalization_rules(7))
          then show ?thesis
            by (metis (no_types) mult.assoc divide_complex_def mult.right_neutral norm_mult nz' right_diff_distrib')
        qed
        show ?thesis
          by (simp add: set_eq_iff image_def ball_def) (metis 1 2 3 4 diff_zero dist_norm nz')
      qed
      then show ?thesis by blast
    qed

    have ex_ball: "\<exists>B. (\<exists>z'. B = ball z' d \<and> z'^n = z^n) \<and> x \<in> B"
                  if "x \<noteq> 0" and eq: "x^n = w^n" and dzw: "dist z w < d" for x w
    proof -
      have "w \<noteq> 0" by (metis assms power_eq_0_iff that(1) that(2))
      have [simp]: "cmod x = cmod w"
        using assms power_eq_imp_eq_norm eq by blast
      have [simp]: "cmod (x * z / w - x) = cmod (z - w)"
      proof -
        have "cmod (x * z / w - x) = cmod x * cmod (z / w - 1)"
          by (metis (no_types) mult.right_neutral norm_mult right_diff_distrib' times_divide_eq_right)
        also have "... = cmod w * cmod (z / w - 1)"
          by simp
        also have "... = cmod (z - w)"
          by (simp add: \<open>w \<noteq> 0\<close> divide_diff_eq_iff nonzero_norm_divide)
        finally show ?thesis .
      qed
      show ?thesis
      proof (intro exI conjI)
        show "(z / w * x) ^ n = z ^ n"
          by (metis \<open>w \<noteq> 0\<close> eq nonzero_eq_divide_eq power_mult_distrib)
        show "x \<in> ball (z / w * x) d"
          using \<open>d > 0\<close> that
          by (simp add: ball_eq_ball_iff \<open>z \<noteq> 0\<close> \<open>w \<noteq> 0\<close> field_simps) (simp add: dist_norm)
      qed auto
    qed

    show ?thesis
    proof (rule exI, intro conjI)
      show "z ^ n \<in> (\<lambda>w. w ^ n) ` ball z d"
        using \<open>d > 0\<close> by simp
      show "open ((\<lambda>w. w ^ n) ` ball z d)"
        by (rule invariance_of_domain [OF cont open_ball inj])
      show "0 \<notin> (\<lambda>w. w ^ n) ` ball z d"
        using \<open>z \<noteq> 0\<close> assms by (force simp: d_def)
      show "\<exists>v. \<Union>v = - {0} \<inter> (\<lambda>z. z ^ n) -` (\<lambda>w. w ^ n) ` ball z d \<and>
                (\<forall>u\<in>v. open u \<and> 0 \<notin> u) \<and>
                disjoint v \<and>
                (\<forall>u\<in>v. Ex (homeomorphism u ((\<lambda>w. w ^ n) ` ball z d) (\<lambda>z. z ^ n)))"
      proof (rule exI, intro ballI conjI)
        show "\<Union>{ball z' d |z'. z'^n = z^n} = - {0} \<inter> (\<lambda>z. z ^ n) -` (\<lambda>w. w ^ n) ` ball z d" (is "?l = ?r")
        proof 
          have "\<And>z'. cmod z' < d \<Longrightarrow> z' ^ n \<noteq> z ^ n"
            by (auto simp add: assms d_def power_eq_imp_eq_norm that)
          then show "?l \<subseteq> ?r"
            by auto (metis im_eq image_eqI mem_ball)
          show "?r \<subseteq> ?l"
            by auto (meson ex_ball)
        qed
        show "\<And>u. u \<in> {ball z' d |z'. z' ^ n = z ^ n} \<Longrightarrow> 0 \<notin> u"
          by (force simp add: assms d_def power_eq_imp_eq_norm that)

        show "disjoint {ball z' d |z'. z' ^ n = z ^ n}"
        proof (clarsimp simp add: pairwise_def disjnt_iff)
          fix \<xi> \<zeta> x
          assume "\<xi>^n = z^n" "\<zeta>^n = z^n" "ball \<xi> d \<noteq> ball \<zeta> d"
            and "dist \<xi> x < d" "dist \<zeta> x < d"
          then have "dist \<xi> \<zeta> < d+d"
            using dist_triangle_less_add by blast
          then have "cmod (\<xi> - \<zeta>) < 2*d"
            by (simp add: dist_norm)
          also have "... \<le> e * cmod z"
            using mult_right_mono \<open>0 < e\<close> that by (auto simp: d_def)
          finally have "cmod (\<xi> - \<zeta>) < e * cmod z" .
          with e have "\<xi> = \<zeta>"
            by (metis \<open>\<xi>^n = z^n\<close> \<open>\<zeta>^n = z^n\<close> assms power_eq_imp_eq_norm)
          then show "False"
            using \<open>ball \<xi> d \<noteq> ball \<zeta> d\<close> by blast
        qed
        show "Ex (homeomorphism u ((\<lambda>w. w ^ n) ` ball z d) (\<lambda>z. z ^ n))"
          if "u \<in> {ball z' d |z'. z' ^ n = z ^ n}" for u
        proof (rule invariance_of_domain_homeomorphism [of "u" "\<lambda>z. z^n"])
          show "open u"
            using that by auto
          show "continuous_on u (\<lambda>z. z ^ n)"
            by (intro continuous_intros)
          show "inj_on (\<lambda>z. z ^ n) u"
            using that by (auto simp: iff_x_eq_y inj_on_def)
          show "\<And>g. homeomorphism u ((\<lambda>z. z ^ n) ` u) (\<lambda>z. z ^ n) g \<Longrightarrow> Ex (homeomorphism u ((\<lambda>w. w ^ n) ` ball z d) (\<lambda>z. z ^ n))"
            using im_eq that by clarify metis
        qed auto
      qed auto
    qed
  qed
  show ?thesis
    using assms
    apply (simp add: covering_space_def zn1 zn2)
    apply (subst zn2 [symmetric])
    apply (simp add: openin_open_eq open_Compl zn3)
    done
qed

corollary covering_space_square_punctured_plane:
  "covering_space (- {0}) (\<lambda>z::complex. z^2) (- {0})"
  by (simp add: covering_space_power_punctured_plane)


proposition covering_space_exp_punctured_plane:
  "covering_space UNIV (\<lambda>z::complex. exp z) (- {0})"
proof (simp add: covering_space_def, intro conjI ballI)
  show "continuous_on UNIV (\<lambda>z::complex. exp z)"
    by (rule continuous_on_exp [OF continuous_on_id])
  show "range exp = - {0::complex}"
    by auto (metis exp_Ln range_eqI)
  show "\<exists>T. z \<in> T \<and> openin (top_of_set (- {0})) T \<and>
             (\<exists>v. \<Union>v = exp -` T \<and> (\<forall>u\<in>v. open u) \<and> disjoint v \<and>
                  (\<forall>u\<in>v. \<exists>q. homeomorphism u T exp q))"
        if "z \<in> - {0::complex}" for z
  proof -
    have "z \<noteq> 0"
      using that by auto
    have "ball (Ln z) 1 \<subseteq> ball (Ln z) pi"
      using pi_ge_two by (simp add: ball_subset_ball_iff)
    then have inj_exp: "inj_on exp (ball (Ln z) 1)"
      using inj_on_exp_pi inj_on_subset by blast
    define \<V> where "\<V> \<equiv> range (\<lambda>n. (\<lambda>x. x + of_real (2 * of_int n * pi) * \<i>) ` (ball(Ln z) 1))"
    show ?thesis
    proof (intro exI conjI)
      show "z \<in> exp ` (ball(Ln z) 1)"
        by (metis \<open>z \<noteq> 0\<close> centre_in_ball exp_Ln rev_image_eqI zero_less_one)
      have "open (- {0::complex})"
        by blast
      with inj_exp show "openin (top_of_set (- {0})) (exp ` ball (Ln z) 1)"
        by (auto simp: openin_open_eq invariance_of_domain continuous_on_exp [OF continuous_on_id])
      show "\<Union>\<V> = exp -` exp ` ball (Ln z) 1"
        by (force simp: \<V>_def Complex_Transcendental.exp_eq image_iff)
      show "\<forall>V\<in>\<V>. open V"
        by (auto simp: \<V>_def inj_on_def continuous_intros invariance_of_domain)
      have xy: "2 \<le> cmod (2 * of_int x * of_real pi * \<i> - 2 * of_int y * of_real pi * \<i>)"
               if "x < y" for x y
      proof -
        have "1 \<le> abs (x - y)"
          using that by linarith
        then have "1 \<le> cmod (of_int x - of_int y) * 1"
          by (metis mult.right_neutral norm_of_int of_int_1_le_iff of_int_abs of_int_diff)
        also have "... \<le> cmod (of_int x - of_int y) * of_real pi"
          using pi_ge_two
           by (intro mult_left_mono) auto
        also have "... \<le> cmod ((of_int x - of_int y) * of_real pi * \<i>)"
          by (simp add: norm_mult)
        also have "... \<le> cmod (of_int x * of_real pi * \<i> - of_int y * of_real pi * \<i>)"
          by (simp add: algebra_simps)
        finally have "1 \<le> cmod (of_int x * of_real pi * \<i> - of_int y * of_real pi * \<i>)" .
        then have "2 * 1 \<le> cmod (2 * (of_int x * of_real pi * \<i> - of_int y * of_real pi * \<i>))"
          by (metis mult_le_cancel_left_pos norm_mult_numeral1 zero_less_numeral)
        then show ?thesis
          by (simp add: algebra_simps)
      qed
      show "disjoint \<V>"
        apply (clarsimp simp add: \<V>_def pairwise_def disjnt_def add.commute [of _ "x*y" for x y]
                        ball_eq_ball_iff intro!: disjoint_ballI)
        apply (auto simp: dist_norm neq_iff)
        by (metis norm_minus_commute xy)+
      show "\<forall>u\<in>\<V>. \<exists>q. homeomorphism u (exp ` ball (Ln z) 1) exp q"
      proof
        fix u
        assume "u \<in> \<V>"
        then obtain n where n: "u = (\<lambda>x. x + of_real (2 * of_int n * pi) * \<i>) ` (ball(Ln z) 1)"
          by (auto simp: \<V>_def)
        have "compact (cball (Ln z) 1)"
          by simp
        moreover have "continuous_on (cball (Ln z) 1) exp"
          by (rule continuous_on_exp [OF continuous_on_id])
        moreover have "inj_on exp (cball (Ln z) 1)"
          apply (rule inj_on_subset [OF inj_on_exp_pi [of "Ln z"]])
          using pi_ge_two by (simp add: cball_subset_ball_iff)
        ultimately obtain \<gamma> where hom: "homeomorphism (cball (Ln z) 1) (exp ` cball (Ln z) 1) exp \<gamma>"
          using homeomorphism_compact  by blast
        have eq1: "exp ` u = exp ` ball (Ln z) 1"
          apply (auto simp: algebra_simps n)
          apply (rule_tac x = "_ + \<i> * (of_int n * (of_real pi * 2))" in image_eqI)
          apply (auto simp: image_iff)
          done
        have \<gamma>exp: "\<gamma> (exp x) + 2 * of_int n * of_real pi * \<i> = x" if "x \<in> u" for x
        proof -
          have "exp x = exp (x - 2 * of_int n * of_real pi * \<i>)"
            by (simp add: exp_eq)
          then have "\<gamma> (exp x) = \<gamma> (exp (x - 2 * of_int n * of_real pi * \<i>))"
            by simp
          also have "... = x - 2 * of_int n * of_real pi * \<i>"
            using \<open>x \<in> u\<close> by (auto simp: n intro: homeomorphism_apply1 [OF hom])
          finally show ?thesis
            by simp
        qed
        have exp2n: "exp (\<gamma> (exp x) + 2 * of_int n * complex_of_real pi * \<i>) = exp x"
                if "dist (Ln z) x < 1" for x
          using that by (auto simp: exp_eq homeomorphism_apply1 [OF hom])
        have "continuous_on (exp ` ball (Ln z) 1) \<gamma>"
          by (meson ball_subset_cball continuous_on_subset hom homeomorphism_cont2 image_mono)
        then have cont: "continuous_on (exp ` ball (Ln z) 1) (\<lambda>x. \<gamma> x + 2 * of_int n * complex_of_real pi * \<i>)"
          by (intro continuous_intros)
        show "\<exists>q. homeomorphism u (exp ` ball (Ln z) 1) exp q"
          apply (rule_tac x="(\<lambda>x. x + of_real(2 * n * pi) * \<i>) \<circ> \<gamma>" in exI)
          unfolding homeomorphism_def
          apply (intro conjI ballI eq1 continuous_on_exp [OF continuous_on_id])
             apply (auto simp: \<gamma>exp exp2n cont n)
           apply (force simp: image_iff homeomorphism_apply1 [OF hom])+
          done
      qed
    qed
  qed
qed


subsection\<open>Hence the Borsukian results about mappings into circles\<close>(*FIX ME title *)

lemma inessential_eq_continuous_logarithm:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  shows "(\<exists>a. homotopic_with_canon (\<lambda>h. True) S (-{0}) f (\<lambda>t. a)) \<longleftrightarrow>
         (\<exists>g. continuous_on S g \<and> (\<forall>x \<in> S. f x = exp(g x)))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs
    by (metis covering_space_lift_inessential_function covering_space_exp_punctured_plane)
next
  assume ?rhs
  then obtain g where contg: "continuous_on S g" and f: "\<And>x. x \<in> S \<Longrightarrow> f x = exp(g x)"
    by metis
  obtain a where "homotopic_with_canon (\<lambda>h. True) S (- {of_real 0}) (exp \<circ> g) (\<lambda>x. a)"
  proof (rule nullhomotopic_through_contractible [OF contg subset_UNIV _ _ contractible_UNIV])
    show "continuous_on (UNIV::complex set) exp"
      by (intro continuous_intros)
    show "range exp \<subseteq> - {0}"
      by auto
  qed force
  then have "homotopic_with_canon (\<lambda>h. True) S (- {0}) f (\<lambda>t. a)"
    using f homotopic_with_eq by fastforce
  then show ?lhs ..
qed

corollary inessential_imp_continuous_logarithm_circle:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes "homotopic_with_canon (\<lambda>h. True) S (sphere 0 1) f (\<lambda>t. a)"
  obtains g where "continuous_on S g" and "\<And>x. x \<in> S \<Longrightarrow> f x = exp(g x)"
proof -
  have "homotopic_with_canon (\<lambda>h. True) S (- {0}) f (\<lambda>t. a)"
    using assms homotopic_with_subset_right by fastforce
  then show ?thesis
    by (metis inessential_eq_continuous_logarithm that)
qed


lemma inessential_eq_continuous_logarithm_circle:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  shows "(\<exists>a. homotopic_with_canon (\<lambda>h. True) S (sphere 0 1) f (\<lambda>t. a)) \<longleftrightarrow>
         (\<exists>g. continuous_on S g \<and> (\<forall>x \<in> S. f x = exp(\<i> * of_real(g x))))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L: ?lhs
  then obtain g where contg: "continuous_on S g" and g: "\<And>x. x \<in> S \<Longrightarrow> f x = exp(g x)"
    using inessential_imp_continuous_logarithm_circle by blast
  have "f ` S \<subseteq> sphere 0 1"
    by (metis L homotopic_with_imp_subset1)
  then have "\<And>x. x \<in> S \<Longrightarrow> Re (g x) = 0"
    using g by auto
  then show ?rhs
    by (rule_tac x="Im \<circ> g" in exI) (auto simp: Euler g intro: contg continuous_intros)
next
  assume ?rhs
  then obtain g where contg: "continuous_on S g" and g: "\<And>x. x \<in> S \<Longrightarrow> f x = exp(\<i>* of_real(g x))"
    by metis
  obtain a where "homotopic_with_canon (\<lambda>h. True) S (sphere 0 1) ((exp \<circ> (\<lambda>z. \<i>*z)) \<circ> (of_real \<circ> g)) (\<lambda>x. a)"
  proof (rule nullhomotopic_through_contractible)
    show "continuous_on S (complex_of_real \<circ> g)"
      by (intro conjI contg continuous_intros)
    show "(complex_of_real \<circ> g) ` S \<subseteq> \<real>"
      by auto
    show "continuous_on \<real> (exp \<circ> (*)\<i>)"
      by (intro continuous_intros)
    show "(exp \<circ> (*)\<i>) ` \<real> \<subseteq> sphere 0 1"
      by (auto simp: complex_is_Real_iff)
  qed (auto simp: convex_Reals convex_imp_contractible)
  moreover have "\<And>x. x \<in> S \<Longrightarrow> (exp \<circ> (*)\<i> \<circ> (complex_of_real \<circ> g)) x = f x"
    by (simp add: g)
  ultimately have "homotopic_with_canon (\<lambda>h. True) S (sphere 0 1) f (\<lambda>t. a)"
    using homotopic_with_eq by force
  then show ?lhs ..
qed

proposition homotopic_with_sphere_times:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes hom: "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) f g" and conth: "continuous_on S h"
      and hin: "\<And>x. x \<in> S \<Longrightarrow> h x \<in> sphere 0 1"
    shows "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. f x * h x) (\<lambda>x. g x * h x)"
proof -
  obtain k where contk: "continuous_on ({0..1::real} \<times> S) k"
             and kim: "k ` ({0..1} \<times> S) \<subseteq> sphere 0 1"
             and k0:  "\<And>x. k(0, x) = f x"
             and k1: "\<And>x. k(1, x) = g x"
    using hom by (auto simp: homotopic_with_def)
  show ?thesis
    apply (simp add: homotopic_with)
    apply (rule_tac x="\<lambda>z. k z*(h \<circ> snd)z" in exI)
    using kim hin by (fastforce simp: conth norm_mult k0 k1 intro!: contk continuous_intros)+
qed

proposition homotopic_circlemaps_divide:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
    shows "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) f g \<longleftrightarrow>
           continuous_on S f \<and> f ` S \<subseteq> sphere 0 1 \<and>
           continuous_on S g \<and> g ` S \<subseteq> sphere 0 1 \<and>
           (\<exists>c. homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. f x / g x) (\<lambda>x. c))"
proof -
  have "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. f x / g x) (\<lambda>x. 1)"
       if "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. f x / g x) (\<lambda>x. c)" for c
  proof -
    have "S = {} \<or> path_component (sphere 0 1) 1 c"
      using homotopic_with_imp_subset2 [OF that] path_connected_sphere [of "0::complex" 1]
      by (auto simp: path_connected_component)
    then have "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. 1) (\<lambda>x. c)"
      by (simp add: homotopic_constant_maps)
    then show ?thesis
      using homotopic_with_symD homotopic_with_trans that by blast
  qed
  then have *: "(\<exists>c. homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. f x / g x) (\<lambda>x. c)) \<longleftrightarrow>
                homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. f x / g x) (\<lambda>x. 1)"
    by auto
  have "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) f g \<longleftrightarrow>
           continuous_on S f \<and> f ` S \<subseteq> sphere 0 1 \<and>
           continuous_on S g \<and> g ` S \<subseteq> sphere 0 1 \<and>
           homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. f x / g x) (\<lambda>x. 1)"
        (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume L: ?lhs
    have geq1 [simp]: "\<And>x. x \<in> S \<Longrightarrow> cmod (g x) = 1"
      using homotopic_with_imp_subset2 [OF L]
      by (simp add: image_subset_iff)
    have cont: "continuous_on S (inverse \<circ> g)"
    proof (rule continuous_intros)
      show "continuous_on S g"
        using homotopic_with_imp_continuous [OF L] by blast
      show "continuous_on (g ` S) inverse"
        by (rule continuous_on_subset [of "sphere 0 1", OF continuous_on_inverse]) auto
    qed
    have [simp]: "\<And>x. x \<in> S \<Longrightarrow> g x \<noteq> 0"
      using geq1 by fastforce
    have "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. f x / g x) (\<lambda>x. 1)"
      apply (rule homotopic_with_eq [OF homotopic_with_sphere_times [OF L cont]])
      by (auto simp: divide_inverse norm_inverse)
    with L show ?rhs
      by (auto simp: homotopic_with_imp_continuous dest: homotopic_with_imp_subset1 homotopic_with_imp_subset2)
  next
    assume ?rhs then show ?lhs
      by (elim conjE homotopic_with_eq [OF homotopic_with_sphere_times]; force)
  qed
  then show ?thesis
    by (simp add: *)
qed

subsection\<open>Upper and lower hemicontinuous functions\<close>

text\<open>And relation in the case of preimage map to open and closed maps, and fact that upper and lower
hemicontinuity together imply continuity in the sense of the Hausdorff metric (at points where the
function gives a bounded and nonempty set).\<close>


text\<open>Many similar proofs below.\<close>
lemma upper_hemicontinuous:
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x \<subseteq> T"
    shows "((\<forall>U. openin (top_of_set T) U
                 \<longrightarrow> openin (top_of_set S) {x \<in> S. f x \<subseteq> U}) \<longleftrightarrow>
            (\<forall>U. closedin (top_of_set T) U
                 \<longrightarrow> closedin (top_of_set S) {x \<in> S. f x \<inter> U \<noteq> {}}))"
          (is "?lhs = ?rhs")
proof (intro iffI allI impI)
  fix U
  assume * [rule_format]: ?lhs and "closedin (top_of_set T) U"
  then have "openin (top_of_set T) (T - U)"
    by (simp add: openin_diff)
  then have "openin (top_of_set S) {x \<in> S. f x \<subseteq> T - U}"
    using * [of "T-U"] by blast
  moreover have "S - {x \<in> S. f x \<subseteq> T - U} = {x \<in> S. f x \<inter> U \<noteq> {}}"
    using assms by blast
  ultimately show "closedin (top_of_set S) {x \<in> S. f x \<inter> U \<noteq> {}}"
    by (simp add: openin_closedin_eq)
next
  fix U
  assume * [rule_format]: ?rhs and "openin (top_of_set T) U"
  then have "closedin (top_of_set T) (T - U)"
    by (simp add: closedin_diff)
  then have "closedin (top_of_set S) {x \<in> S. f x \<inter> (T - U) \<noteq> {}}"
    using * [of "T-U"] by blast
  moreover have "{x \<in> S. f x \<inter> (T - U) \<noteq> {}} = S - {x \<in> S. f x \<subseteq> U}"
    using assms by auto
  ultimately show "openin (top_of_set S) {x \<in> S. f x \<subseteq> U}"
    by (simp add: openin_closedin_eq)
qed

lemma lower_hemicontinuous:
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x \<subseteq> T"
    shows "((\<forall>U. closedin (top_of_set T) U
                 \<longrightarrow> closedin (top_of_set S) {x \<in> S. f x \<subseteq> U}) \<longleftrightarrow>
            (\<forall>U. openin (top_of_set T) U
                 \<longrightarrow> openin (top_of_set S) {x \<in> S. f x \<inter> U \<noteq> {}}))"
          (is "?lhs = ?rhs")
proof (intro iffI allI impI)
  fix U
  assume * [rule_format]: ?lhs and "openin (top_of_set T) U"
  then have "closedin (top_of_set T) (T - U)"
    by (simp add: closedin_diff)
  then have "closedin (top_of_set S) {x \<in> S. f x \<subseteq> T-U}"
    using * [of "T-U"] by blast
  moreover have "{x \<in> S. f x \<subseteq> T-U} = S - {x \<in> S. f x \<inter> U \<noteq> {}}"
    using assms by auto
  ultimately show "openin (top_of_set S) {x \<in> S. f x \<inter> U \<noteq> {}}"
    by (simp add: openin_closedin_eq)
next
  fix U
  assume * [rule_format]: ?rhs and "closedin (top_of_set T) U"
  then have "openin (top_of_set T) (T - U)"
    by (simp add: openin_diff)
  then have "openin (top_of_set S) {x \<in> S. f x \<inter> (T - U) \<noteq> {}}"
    using * [of "T-U"] by blast
  moreover have "S - {x \<in> S. f x \<inter> (T - U) \<noteq> {}} = {x \<in> S. f x \<subseteq> U}"
    using assms by blast
  ultimately show "closedin (top_of_set S) {x \<in> S. f x \<subseteq> U}"
    by (simp add: openin_closedin_eq)
qed

lemma open_map_iff_lower_hemicontinuous_preimage:
  assumes "f ` S \<subseteq> T"
    shows "((\<forall>U. openin (top_of_set S) U
                 \<longrightarrow> openin (top_of_set T) (f ` U)) \<longleftrightarrow>
            (\<forall>U. closedin (top_of_set S) U
                 \<longrightarrow> closedin (top_of_set T) {y \<in> T. {x. x \<in> S \<and> f x = y} \<subseteq> U}))"
          (is "?lhs = ?rhs")
proof (intro iffI allI impI)
  fix U
  assume * [rule_format]: ?lhs and "closedin (top_of_set S) U"
  then have "openin (top_of_set S) (S - U)"
    by (simp add: openin_diff)
  then have "openin (top_of_set T) (f ` (S - U))"
    using * [of "S-U"] by blast
  moreover have "T - (f ` (S - U)) = {y \<in> T. {x \<in> S. f x = y} \<subseteq> U}"
    using assms by blast
  ultimately show "closedin (top_of_set T) {y \<in> T. {x \<in> S. f x = y} \<subseteq> U}"
    by (simp add: openin_closedin_eq)
next
  fix U
  assume * [rule_format]: ?rhs and opeSU: "openin (top_of_set S) U"
  then have "closedin (top_of_set S) (S - U)"
    by (simp add: closedin_diff)
  then have "closedin (top_of_set T) {y \<in> T. {x \<in> S. f x = y} \<subseteq> S - U}"
    using * [of "S-U"] by blast
  moreover have "{y \<in> T. {x \<in> S. f x = y} \<subseteq> S - U} = T - (f ` U)"
    using assms openin_imp_subset [OF opeSU] by auto
  ultimately show "openin (top_of_set T) (f ` U)"
    using assms openin_imp_subset [OF opeSU] by (force simp: openin_closedin_eq)
qed

lemma closed_map_iff_upper_hemicontinuous_preimage:
  assumes "f ` S \<subseteq> T"
    shows "((\<forall>U. closedin (top_of_set S) U
                 \<longrightarrow> closedin (top_of_set T) (f ` U)) \<longleftrightarrow>
            (\<forall>U. openin (top_of_set S) U
                 \<longrightarrow> openin (top_of_set T) {y \<in> T. {x. x \<in> S \<and> f x = y} \<subseteq> U}))"
          (is "?lhs = ?rhs")
proof (intro iffI allI impI)
  fix U
  assume * [rule_format]: ?lhs and opeSU: "openin (top_of_set S) U"
  then have "closedin (top_of_set S) (S - U)"
    by (simp add: closedin_diff)
  then have "closedin (top_of_set T) (f ` (S - U))"
    using * [of "S-U"] by blast
  moreover have "f ` (S - U) = T -  {y \<in> T. {x. x \<in> S \<and> f x = y} \<subseteq> U}"
    using assms openin_imp_subset [OF opeSU] by auto
  ultimately show "openin (top_of_set T)  {y \<in> T. {x. x \<in> S \<and> f x = y} \<subseteq> U}"
    using assms openin_imp_subset [OF opeSU] by (force simp: openin_closedin_eq)
next
  fix U
  assume * [rule_format]: ?rhs and cloSU: "closedin (top_of_set S) U"
  then have "openin (top_of_set S) (S - U)"
    by (simp add: openin_diff)
  then have "openin (top_of_set T) {y \<in> T. {x \<in> S. f x = y} \<subseteq> S - U}"
    using * [of "S-U"] by blast
  moreover have "(f ` U) = T - {y \<in> T. {x \<in> S. f x = y} \<subseteq> S - U}"
    using assms closedin_imp_subset [OF cloSU]  by auto
  ultimately show "closedin (top_of_set T) (f ` U)"
    by (simp add: openin_closedin_eq)
qed

proposition upper_lower_hemicontinuous_explicit:
  fixes T :: "('b::{real_normed_vector,heine_borel}) set"
  assumes fST: "\<And>x. x \<in> S \<Longrightarrow> f x \<subseteq> T"
      and ope: "\<And>U. openin (top_of_set T) U
                     \<Longrightarrow> openin (top_of_set S) {x \<in> S. f x \<subseteq> U}"
      and clo: "\<And>U. closedin (top_of_set T) U
                     \<Longrightarrow> closedin (top_of_set S) {x \<in> S. f x \<subseteq> U}"
      and "x \<in> S" "0 < e" and bofx: "bounded(f x)" and fx_ne: "f x \<noteq> {}"
  obtains d where "0 < d"
             "\<And>x'. \<lbrakk>x' \<in> S; dist x x' < d\<rbrakk>
                           \<Longrightarrow> (\<forall>y \<in> f x. \<exists>y'. y' \<in> f x' \<and> dist y y' < e) \<and>
                               (\<forall>y' \<in> f x'. \<exists>y. y \<in> f x \<and> dist y' y < e)"
proof -
  have "openin (top_of_set T) (T \<inter> (\<Union>a\<in>f x. \<Union>b\<in>ball 0 e. {a + b}))"
    by (auto simp: open_sums openin_open_Int)
  with ope have "openin (top_of_set S)
                    {u \<in> S. f u \<subseteq> T \<inter> (\<Union>a\<in>f x. \<Union>b\<in>ball 0 e. {a + b})}" by blast
  with \<open>0 < e\<close> \<open>x \<in> S\<close> obtain d1 where "d1 > 0" and
         d1: "\<And>x'. \<lbrakk>x' \<in> S; dist x' x < d1\<rbrakk> \<Longrightarrow> f x' \<subseteq> T \<and> f x' \<subseteq> (\<Union>a \<in> f x. \<Union>b \<in> ball 0 e. {a + b})"
    by (force simp: openin_euclidean_subtopology_iff dest: fST)
  have oo: "\<And>U. openin (top_of_set T) U \<Longrightarrow>
                 openin (top_of_set S) {x \<in> S. f x \<inter> U \<noteq> {}}"
    apply (rule lower_hemicontinuous [THEN iffD1, rule_format])
    using fST clo by auto
  have "compact (closure(f x))"
    by (simp add: bofx)
  moreover have "closure(f x) \<subseteq> (\<Union>a \<in> f x. ball a (e/2))"
    using \<open>0 < e\<close> by (force simp: closure_approachable simp del: divide_const_simps)
  ultimately obtain C where "C \<subseteq> f x" "finite C" "closure(f x) \<subseteq> (\<Union>a \<in> C. ball a (e/2))"
    apply (rule compactE, force)
    by (metis finite_subset_image)
  then have fx_cover: "f x \<subseteq> (\<Union>a \<in> C. ball a (e/2))"
    by (meson closure_subset order_trans)
  with fx_ne have "C \<noteq> {}"
    by blast
  have xin: "x \<in> (\<Inter>a \<in> C. {x \<in> S. f x \<inter> T \<inter> ball a (e/2) \<noteq> {}})"
    using \<open>x \<in> S\<close> \<open>0 < e\<close> fST \<open>C \<subseteq> f x\<close> by force
  have "openin (top_of_set S) {x \<in> S. f x \<inter> (T \<inter> ball a (e/2)) \<noteq> {}}" for a
    by (simp add: openin_open_Int oo)
  then have "openin (top_of_set S) (\<Inter>a \<in> C. {x \<in> S. f x \<inter> T \<inter> ball a (e/2) \<noteq> {}})"
    by (simp add: Int_assoc openin_INT2 [OF \<open>finite C\<close> \<open>C \<noteq> {}\<close>])
  with xin obtain d2 where "d2>0"
              and d2: "\<And>u v. \<lbrakk>u \<in> S; dist u x < d2; v \<in> C\<rbrakk> \<Longrightarrow> f u \<inter> T \<inter> ball v (e/2) \<noteq> {}"
    unfolding openin_euclidean_subtopology_iff using xin by fastforce
  show ?thesis
  proof (intro that conjI ballI)
    show "0 < min d1 d2"
      using \<open>0 < d1\<close> \<open>0 < d2\<close> by linarith
  next
    fix x' y
    assume "x' \<in> S" "dist x x' < min d1 d2" "y \<in> f x"
    then have dd2: "dist x' x < d2"
      by (auto simp: dist_commute)
    obtain a where "a \<in> C" "y \<in> ball a (e/2)"
      using fx_cover \<open>y \<in> f x\<close> by auto
    then show "\<exists>y'. y' \<in> f x' \<and> dist y y' < e"
      using d2 [OF \<open>x' \<in> S\<close> dd2] dist_triangle_half_r by fastforce
  next
    fix x' y'
    assume "x' \<in> S" "dist x x' < min d1 d2" "y' \<in> f x'"
    then have "dist x' x < d1"
      by (auto simp: dist_commute)
    then have "y' \<in> (\<Union>a\<in>f x. \<Union>b\<in>ball 0 e. {a + b})"
      using d1 [OF \<open>x' \<in> S\<close>] \<open>y' \<in> f x'\<close> by force
    then show "\<exists>y. y \<in> f x \<and> dist y' y < e"
      by clarsimp (metis add_diff_cancel_left' dist_norm)
  qed
qed


subsection\<open>Complex logs exist on various "well-behaved" sets\<close>

lemma continuous_logarithm_on_contractible:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes "continuous_on S f" "contractible S" "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "continuous_on S g" "\<And>x. x \<in> S \<Longrightarrow> f x = exp(g x)"
proof -
  obtain c where hom: "homotopic_with_canon (\<lambda>h. True) S (-{0}) f (\<lambda>x. c)"
    using nullhomotopic_from_contractible assms
    by (metis imageE subset_Compl_singleton)
  then show ?thesis
    by (metis inessential_eq_continuous_logarithm that)
qed

lemma continuous_logarithm_on_simply_connected:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes contf: "continuous_on S f" and S: "simply_connected S" "locally path_connected S"
      and f: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "continuous_on S g" "\<And>x. x \<in> S \<Longrightarrow> f x = exp(g x)"
  using covering_space_lift [OF covering_space_exp_punctured_plane S contf]
  by (metis (full_types) f imageE subset_Compl_singleton)

lemma continuous_logarithm_on_cball:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes "continuous_on (cball a r) f" and "\<And>z. z \<in> cball a r \<Longrightarrow> f z \<noteq> 0"
    obtains h where "continuous_on (cball a r) h" "\<And>z. z \<in> cball a r \<Longrightarrow> f z = exp(h z)"
  using assms continuous_logarithm_on_contractible convex_imp_contractible by blast

lemma continuous_logarithm_on_ball:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes "continuous_on (ball a r) f" and "\<And>z. z \<in> ball a r \<Longrightarrow> f z \<noteq> 0"
  obtains h where "continuous_on (ball a r) h" "\<And>z. z \<in> ball a r \<Longrightarrow> f z = exp(h z)"
  using assms continuous_logarithm_on_contractible convex_imp_contractible by blast

lemma continuous_sqrt_on_contractible:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes "continuous_on S f" "contractible S"
      and "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "continuous_on S g" "\<And>x. x \<in> S \<Longrightarrow> f x = (g x) ^ 2"
proof -
  obtain g where contg: "continuous_on S g" and feq: "\<And>x. x \<in> S \<Longrightarrow> f x = exp(g x)"
    using continuous_logarithm_on_contractible [OF assms] by blast
  show ?thesis
  proof
    show "continuous_on S (\<lambda>z. exp (g z / 2))"
      by (rule continuous_on_compose2 [of UNIV exp]; intro continuous_intros contg subset_UNIV) auto
    show "\<And>x. x \<in> S \<Longrightarrow> f x = (exp (g x / 2))\<^sup>2"
      by (metis exp_double feq nonzero_mult_div_cancel_left times_divide_eq_right zero_neq_numeral)
  qed
qed

lemma continuous_sqrt_on_simply_connected:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes contf: "continuous_on S f" and S: "simply_connected S" "locally path_connected S"
      and f: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "continuous_on S g" "\<And>x. x \<in> S \<Longrightarrow> f x = (g x) ^ 2"
proof -
  obtain g where contg: "continuous_on S g" and feq: "\<And>x. x \<in> S \<Longrightarrow> f x = exp(g x)"
    using continuous_logarithm_on_simply_connected [OF assms] by blast
  show ?thesis
  proof
    show "continuous_on S (\<lambda>z. exp (g z / 2))"
      by (rule continuous_on_compose2 [of UNIV exp]; intro continuous_intros contg subset_UNIV) auto
    show "\<And>x. x \<in> S \<Longrightarrow> f x = (exp (g x / 2))\<^sup>2"
      by (metis exp_double feq nonzero_mult_div_cancel_left times_divide_eq_right zero_neq_numeral)
  qed
qed


subsection\<open>Another simple case where sphere maps are nullhomotopic\<close>

lemma inessential_spheremap_2_aux:
  fixes f :: "'a::euclidean_space \<Rightarrow> complex"
  assumes 2: "2 < DIM('a)" and contf: "continuous_on (sphere a r) f" 
      and fim: "f `(sphere a r) \<subseteq> (sphere 0 1)" 
  obtains c where "homotopic_with_canon (\<lambda>z. True) (sphere a r) (sphere 0 1) f (\<lambda>x. c)"
proof -
  obtain g where contg: "continuous_on (sphere a r) g" 
             and feq: "\<And>x. x \<in> sphere a r \<Longrightarrow> f x = exp(g x)"
  proof (rule continuous_logarithm_on_simply_connected [OF contf])
    show "simply_connected (sphere a r)"
      using 2 by (simp add: simply_connected_sphere_eq)
    show "locally path_connected (sphere a r)"
      by (simp add: locally_path_connected_sphere)
    show "\<And>z.  z \<in> sphere a r \<Longrightarrow> f z \<noteq> 0"
      using fim by force
  qed auto
  have "\<exists>g. continuous_on (sphere a r) g \<and> (\<forall>x\<in>sphere a r. f x = exp (\<i> * complex_of_real (g x)))"
  proof (intro exI conjI)
    show "continuous_on (sphere a r) (Im \<circ> g)"
      by (intro contg continuous_intros continuous_on_compose)
    show "\<forall>x\<in>sphere a r. f x = exp (\<i> * complex_of_real ((Im \<circ> g) x))"
      using exp_eq_polar feq fim norm_exp_eq_Re by auto
  qed
  with inessential_eq_continuous_logarithm_circle that show ?thesis 
    by metis
qed

lemma inessential_spheremap_2:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes a2: "2 < DIM('a)" and b2: "DIM('b) = 2" 
      and contf: "continuous_on (sphere a r) f" and fim: "f `(sphere a r) \<subseteq> (sphere b s)"
  obtains c where "homotopic_with_canon (\<lambda>z. True) (sphere a r) (sphere b s) f (\<lambda>x. c)"
proof (cases "s \<le> 0")
  case True
  then show ?thesis
    using contf contractible_sphere fim nullhomotopic_into_contractible that by blast
next
  case False
  then have "sphere b s homeomorphic sphere (0::complex) 1"
    using assms by (simp add: homeomorphic_spheres_gen)
  then obtain h k where hk: "homeomorphism (sphere b s) (sphere (0::complex) 1) h k"
    by (auto simp: homeomorphic_def)
  then have conth: "continuous_on (sphere b s) h"
       and  contk: "continuous_on (sphere 0 1) k"
       and  him: "h ` sphere b s \<subseteq> sphere 0 1"
       and  kim: "k ` sphere 0 1 \<subseteq> sphere b s"
    by (simp_all add: homeomorphism_def)
  obtain c where "homotopic_with_canon (\<lambda>z. True) (sphere a r) (sphere 0 1) (h \<circ> f) (\<lambda>x. c)"
  proof (rule inessential_spheremap_2_aux [OF a2])
    show "continuous_on (sphere a r) (h \<circ> f)"
      by (meson continuous_on_compose [OF contf] conth continuous_on_subset fim)
    show "(h \<circ> f) ` sphere a r \<subseteq> sphere 0 1"
      using fim him by force
  qed auto
  then have "homotopic_with_canon (\<lambda>f. True) (sphere a r) (sphere b s) (k \<circ> (h \<circ> f)) (k \<circ> (\<lambda>x. c))"
    by (rule homotopic_with_compose_continuous_left [OF _ contk kim])
  then have "homotopic_with_canon (\<lambda>z. True) (sphere a r) (sphere b s) f (\<lambda>x. k c)"
    apply (rule homotopic_with_eq, auto)
    by (metis fim hk homeomorphism_def image_subset_iff mem_sphere)
  then show ?thesis
    by (metis that)
qed


subsection\<open>Holomorphic logarithms and square roots\<close>

lemma g_imp_holomorphic_log:
  assumes holf: "f holomorphic_on S"
      and contg: "continuous_on S g" and feq: "\<And>x. x \<in> S \<Longrightarrow> f x = exp (g x)"
      and fnz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "g holomorphic_on S" "\<And>z. z \<in> S \<Longrightarrow> f z = exp(g z)"
proof -
  have contf: "continuous_on S f"
    by (simp add: holf holomorphic_on_imp_continuous_on)
  have "g field_differentiable at z within S" if "f field_differentiable at z within S" "z \<in> S" for z
  proof -
    obtain f' where f': "((\<lambda>y. (f y - f z) / (y - z)) \<longlongrightarrow> f') (at z within S)"
      using \<open>f field_differentiable at z within S\<close> by (auto simp: field_differentiable_def has_field_derivative_iff)
    then have ee: "((\<lambda>x. (exp(g x) - exp(g z)) / (x - z)) \<longlongrightarrow> f') (at z within S)"
      by (simp add: feq \<open>z \<in> S\<close> Lim_transform_within [OF _ zero_less_one])
    have "(((\<lambda>y. if y = g z then exp (g z) else (exp y - exp (g z)) / (y - g z)) \<circ> g) \<longlongrightarrow> exp (g z))
          (at z within S)"
    proof (rule tendsto_compose_at)
      show "(g \<longlongrightarrow> g z) (at z within S)"
        using contg continuous_on \<open>z \<in> S\<close> by blast
      show "(\<lambda>y. if y = g z then exp (g z) else (exp y - exp (g z)) / (y - g z)) \<midarrow>g z\<rightarrow> exp (g z)"
        by (simp add: LIM_offset_zero_iff DERIV_D cong: if_cong Lim_cong_within)
      qed auto
    then have dd: "((\<lambda>x. if g x = g z then exp(g z) else (exp(g x) - exp(g z)) / (g x - g z)) \<longlongrightarrow> exp(g z)) (at z within S)"
      by (simp add: o_def)
    have "continuous (at z within S) g"
      using contg continuous_on_eq_continuous_within \<open>z \<in> S\<close> by blast
    then have "(\<forall>\<^sub>F x in at z within S. dist (g x) (g z) < 2*pi)"
      by (simp add: continuous_within tendsto_iff)
    then have "\<forall>\<^sub>F x in at z within S. exp (g x) = exp (g z) \<longrightarrow> g x \<noteq> g z \<longrightarrow> x = z"
      by (rule eventually_mono) (auto simp: exp_eq dist_norm norm_mult)
    then have "((\<lambda>y. (g y - g z) / (y - z)) \<longlongrightarrow> f' / exp (g z)) (at z within S)"
      by (auto intro!: Lim_transform_eventually [OF tendsto_divide [OF ee dd]])
    then show ?thesis
      by (auto simp: field_differentiable_def has_field_derivative_iff)
  qed
  then have "g holomorphic_on S"
    using holf holomorphic_on_def by auto
  then show ?thesis
    using feq that by auto
qed

lemma contractible_imp_holomorphic_log:
  assumes holf: "f holomorphic_on S"
      and S: "contractible S"
      and fnz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "g holomorphic_on S" "\<And>z. z \<in> S \<Longrightarrow> f z = exp(g z)"
proof -
  have contf: "continuous_on S f"
    by (simp add: holf holomorphic_on_imp_continuous_on)
  obtain g where contg: "continuous_on S g" and feq: "\<And>x. x \<in> S \<Longrightarrow> f x = exp (g x)"
    by (metis continuous_logarithm_on_contractible [OF contf S fnz])
  then show thesis
    using fnz g_imp_holomorphic_log holf that by blast
qed

lemma simply_connected_imp_holomorphic_log:
  assumes holf: "f holomorphic_on S"
      and S: "simply_connected S" "locally path_connected S"
      and fnz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "g holomorphic_on S" "\<And>z. z \<in> S \<Longrightarrow> f z = exp(g z)"
proof -
  have contf: "continuous_on S f"
    by (simp add: holf holomorphic_on_imp_continuous_on)
  obtain g where contg: "continuous_on S g" and feq: "\<And>x. x \<in> S \<Longrightarrow> f x = exp (g x)"
    by (metis continuous_logarithm_on_simply_connected [OF contf S fnz])
  then show thesis
    using fnz g_imp_holomorphic_log holf that by blast
qed

lemma contractible_imp_holomorphic_sqrt:
  assumes holf: "f holomorphic_on S"
      and S: "contractible S"
      and fnz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "g holomorphic_on S" "\<And>z. z \<in> S \<Longrightarrow> f z = g z ^ 2"
proof -
  obtain g where holg: "g holomorphic_on S" and feq: "\<And>z. z \<in> S \<Longrightarrow> f z = exp(g z)"
    using contractible_imp_holomorphic_log [OF assms] by blast
  show ?thesis
  proof
    show "exp \<circ> (\<lambda>z. z / 2) \<circ> g holomorphic_on S"
      by (intro holomorphic_on_compose holg holomorphic_intros) auto
    show "\<And>z. z \<in> S \<Longrightarrow> f z = ((exp \<circ> (\<lambda>z. z / 2) \<circ> g) z)\<^sup>2"
      by (simp add: feq flip: exp_double)
  qed
qed

lemma simply_connected_imp_holomorphic_sqrt:
  assumes holf: "f holomorphic_on S"
      and S: "simply_connected S" "locally path_connected S"
      and fnz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "g holomorphic_on S" "\<And>z. z \<in> S \<Longrightarrow> f z = g z ^ 2"
proof -
  obtain g where holg: "g holomorphic_on S" and feq: "\<And>z. z \<in> S \<Longrightarrow> f z = exp(g z)"
    using simply_connected_imp_holomorphic_log [OF assms] by blast
  show ?thesis
  proof
    show "exp \<circ> (\<lambda>z. z / 2) \<circ> g holomorphic_on S"
      by (intro holomorphic_on_compose holg holomorphic_intros) auto
    show "\<And>z. z \<in> S \<Longrightarrow> f z = ((exp \<circ> (\<lambda>z. z / 2) \<circ> g) z)\<^sup>2"
      by (simp add: feq flip: exp_double)
  qed
qed

text\<open> Related theorems about holomorphic inverse cosines.\<close>

lemma contractible_imp_holomorphic_arccos:
  assumes holf: "f holomorphic_on S" and S: "contractible S"
      and non1: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 1 \<and> f z \<noteq> -1"
  obtains g where "g holomorphic_on S" "\<And>z. z \<in> S \<Longrightarrow> f z = cos(g z)"
proof -
  have hol1f: "(\<lambda>z. 1 - f z ^ 2) holomorphic_on S"
    by (intro holomorphic_intros holf)
  obtain g where holg: "g holomorphic_on S" and eq: "\<And>z. z \<in> S \<Longrightarrow> 1 - (f z)\<^sup>2 = (g z)\<^sup>2"
    using contractible_imp_holomorphic_sqrt [OF hol1f S]
    by (metis eq_iff_diff_eq_0 non1 power2_eq_1_iff)
  have holfg: "(\<lambda>z. f z + \<i>*g z) holomorphic_on S"
    by (intro holf holg holomorphic_intros)
  have "\<And>z. z \<in> S \<Longrightarrow> f z + \<i>*g z \<noteq> 0"
    by (metis Arccos_body_lemma eq add.commute add.inverse_unique complex_i_mult_minus power2_csqrt power2_eq_iff)
  then obtain h where holh: "h holomorphic_on S" and fgeq: "\<And>z. z \<in> S \<Longrightarrow> f z + \<i>*g z = exp (h z)"
    using contractible_imp_holomorphic_log [OF holfg S] by metis
  show ?thesis
  proof
    show "(\<lambda>z. -\<i>*h z) holomorphic_on S"
      by (intro holh holomorphic_intros)
    show "f z = cos (- \<i>*h z)" if "z \<in> S" for z
    proof -
      have "(f z + \<i>*g z)*(f z - \<i>*g z) = 1"
        using that eq by (auto simp: algebra_simps power2_eq_square)
      then have "f z - \<i>*g z = inverse (f z + \<i>*g z)"
        using inverse_unique by force
      also have "... = exp (- h z)"
        by (simp add: exp_minus fgeq that)
      finally have "f z = exp (- h z) + \<i>*g z"
        by (simp add: diff_eq_eq)
      then show ?thesis
        apply (simp add: cos_exp_eq)
        by (metis fgeq add.assoc mult_2_right that)
    qed
  qed
qed


lemma contractible_imp_holomorphic_arccos_bounded:
  assumes holf: "f holomorphic_on S" and S: "contractible S" and "a \<in> S"
      and non1: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 1 \<and> f z \<noteq> -1"
  obtains g where "g holomorphic_on S" "norm(g a) \<le> pi + norm(f a)" "\<And>z. z \<in> S \<Longrightarrow> f z = cos(g z)"
proof -
  obtain g where holg: "g holomorphic_on S" and feq: "\<And>z. z \<in> S \<Longrightarrow> f z = cos (g z)"
    using contractible_imp_holomorphic_arccos [OF holf S non1] by blast
  obtain b where "cos b = f a" "norm b \<le> pi + norm (f a)"
    using cos_Arccos norm_Arccos_bounded by blast
  then have "cos b = cos (g a)"
    by (simp add: \<open>a \<in> S\<close> feq)
  then consider n where "n \<in> \<int>" "b = g a + of_real(2*n*pi)" | n where "n \<in> \<int>" "b = -g a + of_real(2*n*pi)"
    by (auto simp: complex_cos_eq)
  then show ?thesis
  proof cases
    case 1
    show ?thesis
    proof
      show "(\<lambda>z. g z + of_real(2*n*pi)) holomorphic_on S"
        by (intro holomorphic_intros holg)
      show "cmod (g a + of_real(2*n*pi)) \<le> pi + cmod (f a)"
        using "1" \<open>cmod b \<le> pi + cmod (f a)\<close> by blast
      show "\<And>z. z \<in> S \<Longrightarrow> f z = cos (g z + complex_of_real (2*n*pi))"
        by (metis \<open>n \<in> \<int>\<close> complex_cos_eq feq)
    qed
  next
    case 2
    show ?thesis
    proof
      show "(\<lambda>z. -g z + of_real(2*n*pi)) holomorphic_on S"
        by (intro holomorphic_intros holg)
      show "cmod (-g a + of_real(2*n*pi)) \<le> pi + cmod (f a)"
        using "2" \<open>cmod b \<le> pi + cmod (f a)\<close> by blast
      show "\<And>z. z \<in> S \<Longrightarrow> f z = cos (-g z + complex_of_real (2*n*pi))"
        by (metis \<open>n \<in> \<int>\<close> complex_cos_eq feq)
    qed
  qed
qed


subsection\<open>The "Borsukian" property of sets\<close>

text\<open>This doesn't have a standard name. Kuratowski uses ``contractible with respect to \<open>[S\<^sup>1]\<close>''
 while Whyburn uses ``property b''. It's closely related to unicoherence.\<close>

definition\<^marker>\<open>tag important\<close> Borsukian where
    "Borsukian S \<equiv>
        \<forall>f. continuous_on S f \<and> f ` S \<subseteq> (- {0::complex})
            \<longrightarrow> (\<exists>a. homotopic_with_canon (\<lambda>h. True) S (- {0}) f (\<lambda>x. a))"

lemma Borsukian_retraction_gen:
  assumes "Borsukian S" "continuous_on S h" "h ` S = T"
          "continuous_on T k"  "k ` T \<subseteq> S"  "\<And>y. y \<in> T \<Longrightarrow> h(k y) = y"
    shows "Borsukian T"
proof -
  interpret R: Retracts S h T k
    using assms by (simp add: Retracts.intro)
  show ?thesis
    using assms
    apply (clarsimp simp add: Borsukian_def)
    apply (rule R.cohomotopically_trivial_retraction_null_gen [OF TrueI TrueI refl, of "-{0}"], auto)
    done
qed

lemma retract_of_Borsukian: "\<lbrakk>Borsukian T; S retract_of T\<rbrakk> \<Longrightarrow> Borsukian S"
  apply (auto simp: retract_of_def retraction_def)
  apply (erule (1) Borsukian_retraction_gen)
  apply (meson retraction retraction_def)
    apply (auto)
    done

lemma homeomorphic_Borsukian: "\<lbrakk>Borsukian S; S homeomorphic T\<rbrakk> \<Longrightarrow> Borsukian T"
  using Borsukian_retraction_gen order_refl
  by (fastforce simp add: homeomorphism_def homeomorphic_def)

lemma homeomorphic_Borsukian_eq:
   "S homeomorphic T \<Longrightarrow> Borsukian S \<longleftrightarrow> Borsukian T"
  by (meson homeomorphic_Borsukian homeomorphic_sym)

lemma Borsukian_translation:
  fixes S :: "'a::real_normed_vector set"
  shows "Borsukian (image (\<lambda>x. a + x) S) \<longleftrightarrow> Borsukian S"
  using homeomorphic_Borsukian_eq homeomorphic_translation by blast

lemma Borsukian_injective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
    shows "Borsukian(f ` S) \<longleftrightarrow> Borsukian S"
  using assms homeomorphic_Borsukian_eq linear_homeomorphic_image by blast

lemma homotopy_eqv_Borsukianness:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
   assumes "S homotopy_eqv T"
     shows "(Borsukian S \<longleftrightarrow> Borsukian T)"
  by (meson Borsukian_def assms homotopy_eqv_cohomotopic_triviality_null)

lemma Borsukian_alt:
  fixes S :: "'a::real_normed_vector set"
  shows
   "Borsukian S \<longleftrightarrow>
        (\<forall>f g. continuous_on S f \<and> f ` S \<subseteq> -{0} \<and>
               continuous_on S g \<and> g ` S \<subseteq> -{0}
               \<longrightarrow> homotopic_with_canon (\<lambda>h. True) S (- {0::complex}) f g)"
  unfolding Borsukian_def homotopic_triviality
  by (simp add: path_connected_punctured_universe)

lemma Borsukian_continuous_logarithm:
  fixes S :: "'a::real_normed_vector set"
  shows "Borsukian S \<longleftrightarrow>
            (\<forall>f. continuous_on S f \<and> f ` S \<subseteq> (- {0::complex})
                 \<longrightarrow> (\<exists>g. continuous_on S g \<and> (\<forall>x \<in> S. f x = exp(g x))))"
  by (simp add: Borsukian_def inessential_eq_continuous_logarithm)

lemma Borsukian_continuous_logarithm_circle:
  fixes S :: "'a::real_normed_vector set"
  shows "Borsukian S \<longleftrightarrow>
             (\<forall>f. continuous_on S f \<and> f ` S \<subseteq> sphere (0::complex) 1
                  \<longrightarrow> (\<exists>g. continuous_on S g \<and> (\<forall>x \<in> S. f x = exp(g x))))"
   (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (force simp: Borsukian_continuous_logarithm)
next
  assume RHS [rule_format]: ?rhs
  show ?lhs
  proof (clarsimp simp: Borsukian_continuous_logarithm)
    fix f :: "'a \<Rightarrow> complex"
    assume contf: "continuous_on S f" and 0: "0 \<notin> f ` S"
    then have "continuous_on S (\<lambda>x. f x / complex_of_real (cmod (f x)))"
      by (intro continuous_intros) auto
    moreover have "(\<lambda>x. f x / complex_of_real (cmod (f x))) ` S \<subseteq> sphere 0 1"
      using 0 by (auto simp: norm_divide)
    ultimately obtain g where contg: "continuous_on S g"
                  and fg: "\<forall>x \<in> S. f x / complex_of_real (cmod (f x)) = exp(g x)"
      using RHS [of "\<lambda>x. f x / of_real(norm(f x))"] by auto
    show "\<exists>g. continuous_on S g \<and> (\<forall>x\<in>S. f x = exp (g x))"
    proof (intro exI ballI conjI)
      show "continuous_on S (\<lambda>x. (Ln \<circ> of_real \<circ> norm \<circ> f)x + g x)"
        by (intro continuous_intros contf contg conjI) (use "0" in auto)
      show "f x = exp ((Ln \<circ> complex_of_real \<circ> cmod \<circ> f) x + g x)" if "x \<in> S" for x
        using 0 that
        apply (simp add: exp_add)
        by (metis div_by_0 exp_Ln exp_not_eq_zero fg mult.commute nonzero_eq_divide_eq)
    qed
  qed
qed


lemma Borsukian_continuous_logarithm_circle_real:
  fixes S :: "'a::real_normed_vector set"
  shows "Borsukian S \<longleftrightarrow>
         (\<forall>f. continuous_on S f \<and> f ` S \<subseteq> sphere (0::complex) 1
              \<longrightarrow> (\<exists>g. continuous_on S (complex_of_real \<circ> g) \<and> (\<forall>x \<in> S. f x = exp(\<i> * of_real(g x)))))"
   (is "?lhs = ?rhs")
proof
  assume LHS: ?lhs
  show ?rhs
  proof (clarify)
    fix f :: "'a \<Rightarrow> complex"
    assume "continuous_on S f" and f01: "f ` S \<subseteq> sphere 0 1"
    then obtain g where contg: "continuous_on S g" and "\<And>x. x \<in> S \<Longrightarrow> f x = exp(g x)"
      using LHS by (auto simp: Borsukian_continuous_logarithm_circle)
    then have "\<forall>x\<in>S. f x = exp (\<i> * complex_of_real ((Im \<circ> g) x))"
      using f01 exp_eq_polar norm_exp_eq_Re by auto
    then show "\<exists>g. continuous_on S (complex_of_real \<circ> g) \<and> (\<forall>x\<in>S. f x = exp (\<i> * complex_of_real (g x)))"
      by (rule_tac x="Im \<circ> g" in exI) (force intro: continuous_intros contg)
  qed
next
  assume RHS [rule_format]: ?rhs
  show ?lhs
  proof (clarsimp simp: Borsukian_continuous_logarithm_circle)
    fix f :: "'a \<Rightarrow> complex"
    assume "continuous_on S f" and f01: "f ` S \<subseteq> sphere 0 1"
    then obtain g where contg: "continuous_on S (complex_of_real \<circ> g)" and "\<And>x. x \<in> S \<Longrightarrow> f x =  exp(\<i> * of_real(g x))"
      by (metis RHS)
    then show "\<exists>g. continuous_on S g \<and> (\<forall>x\<in>S. f x = exp (g x))"
      by (rule_tac x="\<lambda>x. \<i>* of_real(g x)" in exI) (auto simp: continuous_intros contg)
  qed
qed

lemma Borsukian_circle:
  fixes S :: "'a::real_normed_vector set"
  shows "Borsukian S \<longleftrightarrow>
         (\<forall>f. continuous_on S f \<and> f ` S \<subseteq> sphere (0::complex) 1
              \<longrightarrow> (\<exists>a. homotopic_with_canon (\<lambda>h. True) S (sphere (0::complex) 1) f (\<lambda>x. a)))"
by (simp add: inessential_eq_continuous_logarithm_circle Borsukian_continuous_logarithm_circle_real)

lemma contractible_imp_Borsukian: "contractible S \<Longrightarrow> Borsukian S"
  by (meson Borsukian_def nullhomotopic_from_contractible)

lemma simply_connected_imp_Borsukian:
  fixes S :: "'a::real_normed_vector set"
  shows  "\<lbrakk>simply_connected S; locally path_connected S\<rbrakk> \<Longrightarrow> Borsukian S"
  by (metis (no_types, lifting) Borsukian_continuous_logarithm continuous_logarithm_on_simply_connected image_eqI subset_Compl_singleton)

lemma starlike_imp_Borsukian:
  fixes S :: "'a::real_normed_vector set"
  shows "starlike S \<Longrightarrow> Borsukian S"
  by (simp add: contractible_imp_Borsukian starlike_imp_contractible)

lemma Borsukian_empty: "Borsukian {}"
  by (auto simp: contractible_imp_Borsukian)

lemma Borsukian_UNIV: "Borsukian (UNIV :: 'a::real_normed_vector set)"
  by (auto simp: contractible_imp_Borsukian)

lemma convex_imp_Borsukian:
  fixes S :: "'a::real_normed_vector set"
  shows "convex S \<Longrightarrow> Borsukian S"
  by (meson Borsukian_def convex_imp_contractible nullhomotopic_from_contractible)

proposition Borsukian_sphere:
  fixes a :: "'a::euclidean_space"
  shows "3 \<le> DIM('a) \<Longrightarrow> Borsukian (sphere a r)"
  using ENR_sphere 
  by (blast intro: simply_connected_imp_Borsukian ENR_imp_locally_path_connected simply_connected_sphere)

lemma Borsukian_Un_lemma:
  fixes S :: "'a::real_normed_vector set"
  assumes BS: "Borsukian S" and BT: "Borsukian T" and ST: "connected(S \<inter> T)"
    and *:  "\<And>f g::'a \<Rightarrow> complex. 
                 \<lbrakk>continuous_on S f; continuous_on T g; \<And>x. x \<in> S \<and> x \<in> T \<Longrightarrow> f x = g x\<rbrakk>
           \<Longrightarrow> continuous_on (S \<union> T) (\<lambda>x. if x \<in> S then f x else g x)"
  shows "Borsukian(S \<union> T)"
proof (clarsimp simp add: Borsukian_continuous_logarithm)
  fix f :: "'a \<Rightarrow> complex"
  assume contf: "continuous_on (S \<union> T) f" and 0: "0 \<notin> f ` (S \<union> T)"
  then have contfS: "continuous_on S f" and contfT: "continuous_on T f"
    using continuous_on_subset by auto
  have "\<lbrakk>continuous_on S f; f ` S \<subseteq> -{0}\<rbrakk> \<Longrightarrow> \<exists>g. continuous_on S g \<and> (\<forall>x \<in> S. f x = exp(g x))"
    using BS by (auto simp: Borsukian_continuous_logarithm)
  then obtain g where contg: "continuous_on S g" and fg: "\<And>x. x \<in> S \<Longrightarrow> f x = exp(g x)"
    using "0" contfS by blast
  have "\<lbrakk>continuous_on T f; f ` T \<subseteq> -{0}\<rbrakk> \<Longrightarrow> \<exists>g. continuous_on T g \<and> (\<forall>x \<in> T. f x = exp(g x))"
    using BT by (auto simp: Borsukian_continuous_logarithm)
  then obtain h where conth: "continuous_on T h" and fh: "\<And>x. x \<in> T \<Longrightarrow> f x = exp(h x)"
    using "0" contfT by blast
  show "\<exists>g. continuous_on (S \<union> T) g \<and> (\<forall>x\<in>S \<union> T. f x = exp (g x))"
  proof (cases "S \<inter> T = {}")
    case True
    show ?thesis
    proof (intro exI conjI)
      show "continuous_on (S \<union> T) (\<lambda>x. if x \<in> S then g x else h x)"
        using True * [OF contg conth]
        by (meson disjoint_iff)
      show "\<forall>x\<in>S \<union> T. f x = exp (if x \<in> S then g x else h x)"
        using fg fh by auto
    qed
  next
    case False
    have "(\<lambda>x. g x - h x) constant_on S \<inter> T"
    proof (rule continuous_discrete_range_constant [OF ST])
      show "continuous_on (S \<inter> T) (\<lambda>x. g x - h x)"
      proof (intro continuous_intros)
        show "continuous_on (S \<inter> T) g"
          by (meson contg continuous_on_subset inf_le1)
        show "continuous_on (S \<inter> T) h"
          by (meson conth continuous_on_subset inf_sup_ord(2))
      qed
      show "\<exists>e>0. \<forall>y. y \<in> S \<inter> T \<and> g y - h y \<noteq> g x - h x \<longrightarrow> e \<le> cmod (g y - h y - (g x - h x))"
           if "x \<in> S \<inter> T" for x
      proof -
        have "g y - g x = h y - h x"
              if "y \<in> S" "y \<in> T" "cmod (g y - g x - (h y - h x)) < 2 * pi" for y
        proof (rule exp_complex_eqI)
          have "\<bar>Im (g y - g x) - Im (h y - h x)\<bar> \<le> cmod (g y - g x - (h y - h x))"
            by (metis abs_Im_le_cmod minus_complex.simps(2))
          then show "\<bar>Im (g y - g x) - Im (h y - h x)\<bar> < 2 * pi"
            using that by linarith
          have "exp (g x) = exp (h x)" "exp (g y) = exp (h y)"
            using fg fh that \<open>x \<in> S \<inter> T\<close> by fastforce+
          then show "exp (g y - g x) = exp (h y - h x)"
            by (simp add: exp_diff)
        qed
        then show ?thesis
          by (rule_tac x="2*pi" in exI) (fastforce simp add: algebra_simps)
      qed
    qed 
    then obtain a where a: "\<And>x. x \<in> S \<inter> T \<Longrightarrow> g x - h x = a"
      by (auto simp: constant_on_def)
    with False have "exp a = 1"
      by (metis IntI disjoint_iff_not_equal divide_self_if exp_diff exp_not_eq_zero fg fh)
    with a show ?thesis
      apply (rule_tac x="\<lambda>x. if x \<in> S then g x else a + h x" in exI)
      apply (intro * contg conth continuous_intros conjI)
       apply (auto simp: algebra_simps fg fh exp_add)
      done
  qed
qed

proposition Borsukian_open_Un:
  fixes S :: "'a::real_normed_vector set"
  assumes opeS: "openin (top_of_set (S \<union> T)) S"
      and opeT: "openin (top_of_set (S \<union> T)) T"
      and BS: "Borsukian S" and BT: "Borsukian T" and ST: "connected(S \<inter> T)"
    shows "Borsukian(S \<union> T)"
  by (force intro: Borsukian_Un_lemma [OF BS BT ST] continuous_on_cases_local_open [OF opeS opeT])

lemma Borsukian_closed_Un:
  fixes S :: "'a::real_normed_vector set"
  assumes cloS: "closedin (top_of_set (S \<union> T)) S"
      and cloT: "closedin (top_of_set (S \<union> T)) T"
      and BS: "Borsukian S" and BT: "Borsukian T" and ST: "connected(S \<inter> T)"
    shows "Borsukian(S \<union> T)"
  by (force intro: Borsukian_Un_lemma [OF BS BT ST] continuous_on_cases_local [OF cloS cloT])

lemma Borsukian_separation_compact:
  fixes S :: "complex set"
  assumes "compact S"
    shows "Borsukian S \<longleftrightarrow> connected(- S)"
  by (simp add: Borsuk_separation_theorem Borsukian_circle assms)

lemma Borsukian_monotone_image_compact:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "Borsukian S" and contf: "continuous_on S f" and fim: "f ` S = T"
      and "compact S" and conn: "\<And>y. y \<in> T \<Longrightarrow> connected {x. x \<in> S \<and> f x = y}"
    shows "Borsukian T"
proof (clarsimp simp add: Borsukian_continuous_logarithm)
  fix g :: "'b \<Rightarrow> complex"
  assume contg: "continuous_on T g" and 0: "0 \<notin> g ` T"
  have "continuous_on S (g \<circ> f)"
    using contf contg continuous_on_compose fim by blast
  moreover have "(g \<circ> f) ` S \<subseteq> -{0}"
    using fim 0 by auto
  ultimately obtain h where conth: "continuous_on S h" and gfh: "\<And>x. x \<in> S \<Longrightarrow> (g \<circ> f) x = exp(h x)"
    using \<open>Borsukian S\<close> by (auto simp: Borsukian_continuous_logarithm)
  have "\<And>y. \<exists>x. y \<in> T \<longrightarrow> x \<in> S \<and> f x = y"
    using fim by auto
  then obtain f' where f': "\<And>y. y \<in> T \<longrightarrow> f' y \<in> S \<and> f (f' y) = y"
    by metis
  have *: "(\<lambda>x. h x - h(f' y)) constant_on {x. x \<in> S \<and> f x = y}" if "y \<in> T" for y
  proof (rule continuous_discrete_range_constant [OF conn [OF that], of "\<lambda>x. h x - h (f' y)"], simp_all add: algebra_simps)
    show "continuous_on {x \<in> S. f x = y} (\<lambda>x. h x - h (f' y))"
      by (intro continuous_intros continuous_on_subset [OF conth]) auto
    show "\<exists>e>0. \<forall>u. u \<in> S \<and> f u = y \<and> h u \<noteq> h x \<longrightarrow> e \<le> cmod (h u - h x)"
      if x: "x \<in> S \<and> f x = y" for x
    proof -
      have "h u = h x" if "u \<in> S" "f u = y" "cmod (h u - h x) < 2 * pi" for u
      proof (rule exp_complex_eqI)
        have "\<bar>Im (h u) - Im (h x)\<bar> \<le> cmod (h u - h x)"
          by (metis abs_Im_le_cmod minus_complex.simps(2))
        then show "\<bar>Im (h u) - Im (h x)\<bar> < 2 * pi"
          using that by linarith
        show "exp (h u) = exp (h x)"
          by (simp add: gfh [symmetric] x that)
      qed
      then show ?thesis
        by (rule_tac x="2*pi" in exI) (fastforce simp add: algebra_simps)
    qed
  qed 
  show "\<exists>h. continuous_on T h \<and> (\<forall>x\<in>T. g x = exp (h x))"
  proof (intro exI conjI)
    show "continuous_on T (h \<circ> f')"
    proof (rule continuous_from_closed_graph [of "h ` S"])
      show "compact (h ` S)"
        by (simp add: \<open>compact S\<close> compact_continuous_image conth)
      show "(h \<circ> f') ` T \<subseteq> h ` S"
        by (auto simp: f')
      have "h x = h (f' (f x))" if "x \<in> S" for x
        using * [of "f x"] fim that unfolding constant_on_def by clarsimp (metis f' imageI right_minus_eq)
      moreover have "\<And>x. x \<in> T \<Longrightarrow> \<exists>u. u \<in> S \<and> x = f u \<and> h (f' x) = h u"
        using f' by fastforce
      ultimately
      have eq: "((\<lambda>x. (x, (h \<circ> f') x)) ` T) =
                {p. \<exists>x. x \<in> S \<and> (x, p) \<in> (S \<times> UNIV) \<inter> ((\<lambda>z. snd z - ((f \<circ> fst) z, (h \<circ> fst) z)) -` {0})}"
        using fim by (auto simp: image_iff)
      moreover have "closed \<dots>"
        apply (intro closed_compact_projection [OF \<open>compact S\<close>] continuous_closed_preimage
                     continuous_intros continuous_on_subset [OF contf] continuous_on_subset [OF conth])
        by (auto simp: \<open>compact S\<close> closed_Times compact_imp_closed)
      ultimately show "closed ((\<lambda>x. (x, (h \<circ> f') x)) ` T)"
        by simp
    qed
  qed (use f' gfh in fastforce)
qed


lemma Borsukian_open_map_image_compact:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "Borsukian S" and contf: "continuous_on S f" and fim: "f ` S = T" and "compact S"
      and ope: "\<And>U. openin (top_of_set S) U
                     \<Longrightarrow> openin (top_of_set T) (f ` U)"
    shows "Borsukian T"
proof (clarsimp simp add: Borsukian_continuous_logarithm_circle_real)
  fix g :: "'b \<Rightarrow> complex"
  assume contg: "continuous_on T g" and gim: "g ` T \<subseteq> sphere 0 1"
  have "continuous_on S (g \<circ> f)"
    using contf contg continuous_on_compose fim by blast
  moreover have "(g \<circ> f) ` S \<subseteq> sphere 0 1"
    using fim gim by auto
  ultimately obtain h where cont_cxh: "continuous_on S (complex_of_real \<circ> h)"
                       and gfh: "\<And>x. x \<in> S \<Longrightarrow> (g \<circ> f) x = exp(\<i> * of_real(h x))"
    using \<open>Borsukian S\<close> Borsukian_continuous_logarithm_circle_real  by metis
  then have conth: "continuous_on S h"
    by simp
  have "\<exists>x. x \<in> S \<and> f x = y \<and> (\<forall>x' \<in> S. f x' = y \<longrightarrow> h x \<le> h x')" if "y \<in> T" for y
  proof -
    have 1: "compact (h ` {x \<in> S. f x = y})"
    proof (rule compact_continuous_image)
      show "continuous_on {x \<in> S. f x = y} h"
        by (rule continuous_on_subset [OF conth]) auto
      have "compact (S \<inter> f -` {y})"
        by (rule proper_map_from_compact [OF contf _ \<open>compact S\<close>, of T]) (simp_all add: fim that)
      then show "compact {x \<in> S. f x = y}" 
        by (auto simp: vimage_def Int_def)
    qed
    have 2: "h ` {x \<in> S. f x = y} \<noteq> {}"
      using fim that by auto
    have "\<exists>s \<in> h ` {x \<in> S. f x = y}. \<forall>t \<in> h ` {x \<in> S. f x = y}. s \<le> t"
      using compact_attains_inf [OF 1 2] by blast
    then show ?thesis by auto
  qed
  then obtain k where kTS: "\<And>y. y \<in> T \<Longrightarrow> k y \<in> S"
                  and fk:  "\<And>y. y \<in> T \<Longrightarrow> f (k y) = y "
                  and hle: "\<And>x' y. \<lbrakk>y \<in> T; x' \<in> S; f x' = y\<rbrakk> \<Longrightarrow> h (k y) \<le> h x'"
    by metis
  have "continuous_on T (h \<circ> k)"
  proof (clarsimp simp add: continuous_on_iff)
    fix y and e::real
    assume "y \<in> T" "0 < e"
    moreover have "uniformly_continuous_on S (complex_of_real \<circ> h)"
      using \<open>compact S\<close> cont_cxh compact_uniformly_continuous by blast
    ultimately obtain d where "0 < d"
                  and d: "\<And>x x'. \<lbrakk>x\<in>S; x'\<in>S; dist x' x < d\<rbrakk> \<Longrightarrow> dist (h x') (h x) < e"
      by (force simp: uniformly_continuous_on_def)
    obtain \<delta> where "0 < \<delta>" and \<delta>:
      "\<And>x'. \<lbrakk>x' \<in> T; dist y x' < \<delta>\<rbrakk>
               \<Longrightarrow> (\<forall>v \<in> {z \<in> S. f z = y}. \<exists>v'. v' \<in> {z \<in> S. f z = x'} \<and> dist v v' < d) \<and>
                   (\<forall>v' \<in> {z \<in> S. f z = x'}. \<exists>v. v \<in> {z \<in> S. f z = y} \<and> dist v' v < d)"
    proof (rule upper_lower_hemicontinuous_explicit [of T "\<lambda>y. {z \<in> S. f z = y}" S])
      show "\<And>U. openin (top_of_set S) U
                 \<Longrightarrow> openin (top_of_set T) {x \<in> T. {z \<in> S. f z = x} \<subseteq> U}"
        using closed_map_iff_upper_hemicontinuous_preimage [OF fim [THEN equalityD1]]
        by (simp add: Abstract_Topology_2.continuous_imp_closed_map \<open>compact S\<close> contf fim)
      show "\<And>U. closedin (top_of_set S) U \<Longrightarrow>
                 closedin (top_of_set T) {x \<in> T. {z \<in> S. f z = x} \<subseteq> U}"
        using  ope open_map_iff_lower_hemicontinuous_preimage [OF fim [THEN equalityD1]]
        by meson
      show "bounded {z \<in> S. f z = y}"
        by (metis (no_types, lifting) compact_imp_bounded [OF \<open>compact S\<close>] bounded_subset mem_Collect_eq subsetI)
    qed (use \<open>y \<in> T\<close> \<open>0 < d\<close> fk kTS in \<open>force+\<close>)
    have "dist (h (k y')) (h (k y)) < e" if "y' \<in> T" "dist y y' < \<delta>" for y'
    proof -
      have k1: "k y \<in> S" "f (k y) = y" and k2: "k y' \<in> S" "f (k y') = y'"
        by (auto simp: \<open>y \<in> T\<close> \<open>y' \<in> T\<close> kTS fk)
      have 1: "\<And>v. \<lbrakk>v \<in> S; f v = y\<rbrakk> \<Longrightarrow> \<exists>v'. v' \<in> {z \<in> S. f z = y'} \<and> dist v v' < d"
       and 2: "\<And>v'. \<lbrakk>v' \<in> S; f v' = y'\<rbrakk> \<Longrightarrow> \<exists>v. v \<in> {z \<in> S. f z = y} \<and> dist v' v < d"
        using \<delta> [OF that] by auto
      then obtain w' w where "w' \<in> S" "f w' = y'" "dist (k y) w' < d"
        and "w \<in> S" "f w = y" "dist (k y') w < d"
        using 1 [OF k1] 2 [OF k2] by auto
      then show ?thesis
        using d [of w "k y'"] d [of w' "k y"] k1 k2 \<open>y' \<in> T\<close>  \<open>y \<in> T\<close> hle
        by (fastforce simp: dist_norm abs_diff_less_iff algebra_simps)
    qed
    then show "\<exists>d>0. \<forall>x'\<in>T. dist x' y < d \<longrightarrow> dist (h (k x')) (h (k y)) < e"
      using  \<open>0 < \<delta>\<close> by (auto simp: dist_commute)
  qed
  then show "\<exists>h. continuous_on T h \<and> (\<forall>x\<in>T. g x = exp (\<i> * complex_of_real (h x)))"
    using fk gfh kTS by force
qed


text\<open>If two points are separated by a closed set, there's a minimal one.\<close>
proposition closed_irreducible_separator:
  fixes a :: "'a::real_normed_vector"
  assumes "closed S" and ab: "\<not> connected_component (- S) a b"
  obtains T where "T \<subseteq> S" "closed T" "T \<noteq> {}" "\<not> connected_component (- T) a b"
                  "\<And>U. U \<subset> T \<Longrightarrow> connected_component (- U) a b"
proof (cases "a \<in> S \<or> b \<in> S")
  case True
  then show ?thesis
  proof
    assume *: "a \<in> S"
    show ?thesis
    proof
      show "{a} \<subseteq> S"
        using * by blast
      show "\<not> connected_component (- {a}) a b"
        using connected_component_in by auto
      show "\<And>U. U \<subset> {a} \<Longrightarrow> connected_component (- U) a b"
        by (metis connected_component_UNIV UNIV_I compl_bot_eq connected_component_eq_eq less_le_not_le subset_singletonD)
    qed auto
  next
    assume *: "b \<in> S"
    show ?thesis
    proof
      show "{b} \<subseteq> S"
        using * by blast
      show "\<not> connected_component (- {b}) a b"
        using connected_component_in by auto
      show "\<And>U. U \<subset> {b} \<Longrightarrow> connected_component (- U) a b"
        by (metis connected_component_UNIV UNIV_I compl_bot_eq connected_component_eq_eq less_le_not_le subset_singletonD)
    qed auto
  qed
next
  case False
  define A where "A \<equiv> connected_component_set (- S) a"
  define B where "B \<equiv> connected_component_set (- (closure A)) b"
  have "a \<in> A"
    using False A_def by auto
  have "b \<in> B"
    unfolding A_def B_def closure_Un_frontier
    using ab False \<open>closed S\<close> frontier_complement frontier_of_connected_component_subset frontier_subset_closed by force
  have "frontier B \<subseteq> frontier (connected_component_set (- closure A) b)"
    using B_def by blast
  also have frsub: "... \<subseteq> frontier A"
  proof -
    have "\<And>A. closure (- closure (- A)) \<subseteq> closure A"
      by (metis (no_types) closure_mono closure_subset compl_le_compl_iff double_compl)
    then show ?thesis
      by (metis (no_types) closure_closure double_compl frontier_closures frontier_of_connected_component_subset le_inf_iff subset_trans)
  qed
  finally have frBA: "frontier B \<subseteq> frontier A" .
  show ?thesis
  proof
    show "frontier B \<subseteq> S"
    proof -
      have "frontier S \<subseteq> S"
        by (simp add: \<open>closed S\<close> frontier_subset_closed)
      then show ?thesis
        using frsub frontier_complement frontier_of_connected_component_subset
        unfolding A_def B_def by blast
    qed
    show "closed (frontier B)"
      by simp
    show "\<not> connected_component (- frontier B) a b"
      unfolding connected_component_def
    proof clarify
      fix T
      assume "connected T" and TB: "T \<subseteq> - frontier B" and "a \<in> T" and "b \<in> T"
      have "a \<notin> B"
        by (metis A_def B_def ComplD \<open>a \<in> A\<close> assms(1) closed_open connected_component_subset in_closure_connected_component subsetD)
      have "T \<inter> B \<noteq> {}"
        using \<open>b \<in> B\<close> \<open>b \<in> T\<close> by blast
      moreover have "T - B \<noteq> {}"
        using \<open>a \<notin> B\<close> \<open>a \<in> T\<close> by blast
      ultimately show "False"
        using connected_Int_frontier [of T B] TB \<open>connected T\<close> by blast
    qed
    moreover have "connected_component (- frontier B) a b" if "frontier B = {}"
      using connected_component_eq_UNIV that by auto
    ultimately show "frontier B \<noteq> {}"
      by blast
    show "connected_component (- U) a b" if "U \<subset> frontier B" for U
    proof -
      obtain p where Usub: "U \<subseteq> frontier B" and p: "p \<in> frontier B" "p \<notin> U"
        using \<open>U \<subset> frontier B\<close> by blast
      show ?thesis
        unfolding connected_component_def
      proof (intro exI conjI)
        have "connected ((insert p A) \<union> (insert p B))"
        proof (rule connected_Un)
          show "connected (insert p A)"
            by (metis A_def IntD1 frBA \<open>p \<in> frontier B\<close> closure_insert closure_subset connected_connected_component connected_intermediate_closure frontier_closures insert_absorb subsetCE subset_insertI)
          show "connected (insert p B)"
            by (metis B_def IntD1 \<open>p \<in> frontier B\<close> closure_insert closure_subset connected_connected_component connected_intermediate_closure frontier_closures insert_absorb subset_insertI)
        qed blast
        then show "connected (insert p (B \<union> A))"
          by (simp add: sup.commute)
        have "A \<subseteq> - U"
          using A_def Usub \<open>frontier B \<subseteq> S\<close> connected_component_subset by fastforce
        moreover have "B \<subseteq> - U"
          using B_def Usub connected_component_subset frBA frontier_closures by fastforce
        ultimately show "insert p (B \<union> A) \<subseteq> - U"
          using p by auto
      qed (auto simp: \<open>a \<in> A\<close> \<open>b \<in> B\<close>)
    qed
  qed
qed

lemma frontier_minimal_separating_closed_pointwise:
  fixes S :: "'a::real_normed_vector set"
  assumes S: "closed S" "a \<notin> S" and nconn: "\<not> connected_component (- S) a b"
      and conn: "\<And>T. \<lbrakk>closed T; T \<subset> S\<rbrakk> \<Longrightarrow> connected_component (- T) a b"
    shows "frontier(connected_component_set (- S) a) = S" (is "?F = S")
proof -
  have "?F \<subseteq> S"
    by (simp add: S componentsI frontier_of_components_closed_complement)
  moreover have False if "?F \<subset> S"
  proof -
    have "connected_component (- ?F) a b"
      by (simp add: conn that)
    then obtain T where "connected T" "T \<subseteq> -?F" "a \<in> T" "b \<in> T"
      by (auto simp: connected_component_def)
    moreover have "T \<inter> ?F \<noteq> {}"
    proof (rule connected_Int_frontier [OF \<open>connected T\<close>])
      show "T \<inter> connected_component_set (- S) a \<noteq> {}"
        using \<open>a \<notin> S\<close> \<open>a \<in> T\<close> by fastforce
      show "T - connected_component_set (- S) a \<noteq> {}"
        using \<open>b \<in> T\<close> nconn by blast
    qed
    ultimately show ?thesis
      by blast
  qed
  ultimately show ?thesis
    by blast
qed


subsection\<open>Unicoherence (closed)\<close>

definition\<^marker>\<open>tag important\<close> unicoherent where
  "unicoherent U \<equiv>
  \<forall>S T. connected S \<and> connected T \<and> S \<union> T = U \<and>
        closedin (top_of_set U) S \<and> closedin (top_of_set U) T
        \<longrightarrow> connected (S \<inter> T)"

lemma unicoherentI [intro?]:
  assumes "\<And>S T. \<lbrakk>connected S; connected T; U = S \<union> T; closedin (top_of_set U) S; closedin (top_of_set U) T\<rbrakk>
          \<Longrightarrow> connected (S \<inter> T)"
  shows "unicoherent U"
  using assms unfolding unicoherent_def by blast

lemma unicoherentD:
  assumes "unicoherent U" "connected S" "connected T" "U = S \<union> T" "closedin (top_of_set U) S" "closedin (top_of_set U) T"
  shows "connected (S \<inter> T)"
  using assms unfolding unicoherent_def by blast

proposition homeomorphic_unicoherent:
  assumes ST: "S homeomorphic T" and S: "unicoherent S"
  shows "unicoherent T"
proof -
  obtain f g where gf: "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x" and fim: "T = f ` S" and gfim: "g ` f ` S = S"
    and contf: "continuous_on S f" and contg: "continuous_on (f ` S) g"
    using ST by (auto simp: homeomorphic_def homeomorphism_def)
  show ?thesis
  proof
    fix U V
    assume "connected U" "connected V" and T: "T = U \<union> V"
      and cloU: "closedin (top_of_set T) U"
      and cloV: "closedin (top_of_set T) V"
    have "f ` (g ` U \<inter> g ` V) \<subseteq> U" "f ` (g ` U \<inter> g ` V) \<subseteq> V"
      using gf fim T by auto (metis UnCI image_iff)+
    moreover have "U \<inter> V \<subseteq> f ` (g ` U \<inter> g ` V)"
      using gf fim by (force simp: image_iff T)
    ultimately have "U \<inter> V = f ` (g ` U \<inter> g ` V)" by blast
    moreover have "connected (f ` (g ` U \<inter> g ` V))"
    proof (rule connected_continuous_image)
      show "continuous_on (g ` U \<inter> g ` V) f"
        using T fim gfim by (metis Un_upper1 contf continuous_on_subset image_mono inf_le1) 
      show "connected (g ` U \<inter> g ` V)"
      proof (intro conjI unicoherentD [OF S])
        show "connected (g ` U)" "connected (g ` V)"
          using \<open>connected U\<close> cloU \<open>connected V\<close> cloV
          by (metis Topological_Spaces.connected_continuous_image closedin_imp_subset contg continuous_on_subset fim)+
        show "S = g ` U \<union> g ` V"
          using T fim gfim by auto
        have hom: "homeomorphism T S g f"
          by (simp add: contf contg fim gf gfim homeomorphism_def)
        have "closedin (top_of_set T) U" "closedin (top_of_set T) V"
          by (simp_all add: cloU cloV)
        then show "closedin (top_of_set S) (g ` U)"
                  "closedin (top_of_set S) (g ` V)"
          by (blast intro: homeomorphism_imp_closed_map [OF hom])+
      qed
    qed
    ultimately show "connected (U \<inter> V)" by metis
  qed
qed


lemma homeomorphic_unicoherent_eq:
   "S homeomorphic T \<Longrightarrow> (unicoherent S \<longleftrightarrow> unicoherent T)"
  by (meson homeomorphic_sym homeomorphic_unicoherent)

lemma unicoherent_translation:
  fixes S :: "'a::real_normed_vector set"
  shows
   "unicoherent (image (\<lambda>x. a + x) S) \<longleftrightarrow> unicoherent S"
  using homeomorphic_translation homeomorphic_unicoherent_eq by blast

lemma unicoherent_injective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
  shows "(unicoherent(f ` S) \<longleftrightarrow> unicoherent S)"
  using assms homeomorphic_unicoherent_eq linear_homeomorphic_image by blast


lemma Borsukian_imp_unicoherent:
  fixes U :: "'a::euclidean_space set"
  assumes "Borsukian U"  shows "unicoherent U"
  unfolding unicoherent_def
proof clarify
  fix S T
  assume "connected S" "connected T" "U = S \<union> T"
     and cloS: "closedin (top_of_set (S \<union> T)) S"
     and cloT: "closedin (top_of_set (S \<union> T)) T"
  show "connected (S \<inter> T)"
    unfolding connected_closedin_eq
  proof clarify
    fix V W
    assume "closedin (top_of_set (S \<inter> T)) V"
       and "closedin (top_of_set (S \<inter> T)) W"
       and VW: "V \<union> W = S \<inter> T" "V \<inter> W = {}" and "V \<noteq> {}" "W \<noteq> {}"
    then have cloV: "closedin (top_of_set U) V" and cloW: "closedin (top_of_set U) W"
      using \<open>U = S \<union> T\<close> cloS cloT closedin_trans by blast+
    obtain q where contq: "continuous_on U q"
         and q01: "\<And>x. x \<in> U \<Longrightarrow> q x \<in> {0..1::real}"
         and qV: "\<And>x. x \<in> V \<Longrightarrow> q x = 0" and qW: "\<And>x. x \<in> W \<Longrightarrow> q x = 1"
      by (rule Urysohn_local [OF cloV cloW \<open>V \<inter> W = {}\<close>, of 0 1])
         (fastforce simp: closed_segment_eq_real_ivl)
    let ?h = "\<lambda>x. if x \<in> S then exp(pi * \<i> * q x) else 1 / exp(pi * \<i> * q x)"
    have eqST: "exp(pi * \<i> * q x) = 1 / exp(pi * \<i> * q x)" if "x \<in> S \<inter> T" for x
    proof -
      have "x \<in> V \<union> W"
        using that \<open>V \<union> W = S \<inter> T\<close> by blast
      with qV qW show ?thesis by force
    qed
    obtain g where contg: "continuous_on U g"
      and circle: "g ` U \<subseteq> sphere 0 1"
      and S: "\<And>x. x \<in> S \<Longrightarrow> g x = exp(pi * \<i> * q x)"
      and T: "\<And>x. x \<in> T \<Longrightarrow> g x = 1 / exp(pi * \<i> * q x)"
    proof
      show "continuous_on U ?h"
        unfolding \<open>U = S \<union> T\<close>
      proof (rule continuous_on_cases_local [OF cloS cloT])
        show "continuous_on S (\<lambda>x. exp (pi * \<i> * q x))"
        proof (intro continuous_intros)
          show "continuous_on S q"
            using \<open>U = S \<union> T\<close> continuous_on_subset contq by blast
        qed
        show "continuous_on T (\<lambda>x. 1 / exp (pi * \<i> * q x))"
        proof (intro continuous_intros)
          show "continuous_on T q"
            using \<open>U = S \<union> T\<close> continuous_on_subset contq by auto
        qed auto
      qed (use eqST in auto)
    qed (use eqST in \<open>auto simp: norm_divide\<close>)
    then obtain h where conth: "continuous_on U h" and heq: "\<And>x. x \<in> U \<Longrightarrow> g x = exp (h x)"
      by (metis Borsukian_continuous_logarithm_circle assms)
    obtain v w where "v \<in> V" "w \<in> W"
      using \<open>V \<noteq> {}\<close> \<open>W \<noteq> {}\<close> by blast
    then have vw: "v \<in> S \<inter> T" "w \<in> S \<inter> T"
      using VW by auto
    have iff: "2 * pi \<le> cmod (2 * of_int m * of_real pi * \<i> - 2 * of_int n * of_real pi * \<i>)
          \<longleftrightarrow> 1 \<le> abs (m - n)" for m n
    proof -
      have "2 * pi \<le> cmod (2 * of_int m * of_real pi * \<i> - 2 * of_int n * of_real pi * \<i>)
            \<longleftrightarrow> 2 * pi \<le> cmod ((2 * pi * \<i>) * (of_int m - of_int n))"
        by (simp add: algebra_simps)
      also have "... \<longleftrightarrow> 2 * pi \<le> 2 * pi * cmod (of_int m - of_int n)"
        by (simp add: norm_mult)
      also have "... \<longleftrightarrow> 1 \<le> abs (m - n)"
        by simp (metis norm_of_int of_int_1_le_iff of_int_abs of_int_diff)
      finally show ?thesis .
    qed
    have *: "\<exists>n::int. h x - (pi * \<i> * q x) = (of_int(2*n) * pi) * \<i>" if "x \<in> S" for x
      using that S \<open>U = S \<union> T\<close> heq exp_eq [symmetric] by (simp add: algebra_simps)
    moreover have "(\<lambda>x. h x - (pi * \<i> * q x)) constant_on S"
    proof (rule continuous_discrete_range_constant [OF \<open>connected S\<close>])
      have "continuous_on S h" "continuous_on S q"
        using \<open>U = S \<union> T\<close> continuous_on_subset conth contq by blast+
      then show "continuous_on S (\<lambda>x. h x - (pi * \<i> * q x))"
        by (intro continuous_intros)
      have "2*pi \<le> cmod (h y - (pi * \<i> * q y) - (h x - (pi * \<i> * q x)))"
        if "x \<in> S" "y \<in> S" and ne: "h y - (pi * \<i> * q y) \<noteq> h x - (pi * \<i> * q x)" for x y
        using * [OF \<open>x \<in> S\<close>] * [OF \<open>y \<in> S\<close>] ne by (auto simp: iff)
      then show "\<And>x. x \<in> S \<Longrightarrow>
         \<exists>e>0. \<forall>y. y \<in> S \<and> h y - (pi * \<i> * q y) \<noteq> h x - (pi * \<i> * q x) \<longrightarrow>
                   e \<le> cmod (h y - (pi * \<i> * q y) - (h x - (pi * \<i> * q x)))"
        by (rule_tac x="2*pi" in exI) auto
    qed
    ultimately
    obtain m where m: "\<And>x. x \<in> S \<Longrightarrow> h x - (pi * \<i> * q x) = (of_int(2*m) * pi) * \<i>"
      using vw by (force simp: constant_on_def)
    have *: "\<exists>n::int. h x = - (pi * \<i> * q x) + (of_int(2*n) * pi) * \<i>" if "x \<in> T" for x
      unfolding exp_eq [symmetric]
      using that T \<open>U = S \<union> T\<close> by (simp add: exp_minus field_simps  heq [symmetric])
    moreover have "(\<lambda>x. h x + (pi * \<i> * q x)) constant_on T"
    proof (rule continuous_discrete_range_constant [OF \<open>connected T\<close>])
      have "continuous_on T h" "continuous_on T q"
        using \<open>U = S \<union> T\<close> continuous_on_subset conth contq by blast+
      then show "continuous_on T (\<lambda>x. h x + (pi * \<i> * q x))"
        by (intro continuous_intros)
      have "2*pi \<le> cmod (h y + (pi * \<i> * q y) - (h x + (pi * \<i> * q x)))"
        if "x \<in> T" "y \<in> T" and ne: "h y + (pi * \<i> * q y) \<noteq> h x + (pi * \<i> * q x)" for x y
        using * [OF \<open>x \<in> T\<close>] * [OF \<open>y \<in> T\<close>] ne by (auto simp: iff)
      then show "\<And>x. x \<in> T \<Longrightarrow>
         \<exists>e>0. \<forall>y. y \<in> T \<and> h y + (pi * \<i> * q y) \<noteq> h x + (pi * \<i> * q x) \<longrightarrow>
                   e \<le> cmod (h y + (pi * \<i> * q y) - (h x + (pi * \<i> * q x)))"
        by (rule_tac x="2*pi" in exI) auto
    qed
    ultimately
    obtain n where n: "\<And>x. x \<in> T \<Longrightarrow> h x + (pi * \<i> * q x) = (of_int(2*n) * pi) * \<i>"
      using vw by (force simp: constant_on_def)
    show "False"
      using m [of v] m [of w] n [of v] n [of w] vw
      by (auto simp: algebra_simps \<open>v \<in> V\<close> \<open>w \<in> W\<close> qV qW)
  qed
qed


corollary contractible_imp_unicoherent:
  fixes U :: "'a::euclidean_space set"
  assumes "contractible U"  shows "unicoherent U"
  by (simp add: Borsukian_imp_unicoherent assms contractible_imp_Borsukian)

corollary convex_imp_unicoherent:
  fixes U :: "'a::euclidean_space set"
  assumes "convex U"  shows "unicoherent U"
  by (simp add: Borsukian_imp_unicoherent assms convex_imp_Borsukian)

text\<open>If the type class constraint can be relaxed, I don't know how!\<close>
corollary unicoherent_UNIV: "unicoherent (UNIV :: 'a :: euclidean_space set)"
  by (simp add: convex_imp_unicoherent)


lemma unicoherent_monotone_image_compact:
  fixes T :: "'b :: t2_space set"
  assumes S: "unicoherent S" "compact S" and contf: "continuous_on S f" and fim: "f ` S = T"
  and conn: "\<And>y. y \<in> T \<Longrightarrow> connected (S \<inter> f -` {y})"
  shows "unicoherent T"
proof
  fix U V
  assume UV: "connected U" "connected V" "T = U \<union> V"
     and cloU: "closedin (top_of_set T) U"
     and cloV: "closedin (top_of_set T) V"
  moreover have "compact T"
    using \<open>compact S\<close> compact_continuous_image contf fim by blast
  ultimately have "closed U" "closed V"
    by (auto simp: closedin_closed_eq compact_imp_closed)
  let ?SUV = "(S \<inter> f -` U) \<inter> (S \<inter> f -` V)"
  have UV_eq: "f ` ?SUV = U \<inter> V"
    using \<open>T = U \<union> V\<close> fim by force+
  have "connected (f ` ?SUV)"
  proof (rule connected_continuous_image)
    show "continuous_on ?SUV f"
      by (meson contf continuous_on_subset inf_le1)
    show "connected ?SUV"
    proof (rule unicoherentD [OF \<open>unicoherent S\<close>, of "S \<inter> f -` U" "S \<inter> f -` V"])
      have "\<And>C. closedin (top_of_set S) C \<Longrightarrow> closedin (top_of_set T) (f ` C)"
        by (metis \<open>compact S\<close> closed_subset closedin_compact closedin_imp_subset compact_continuous_image compact_imp_closed contf continuous_on_subset fim image_mono)
      then show "connected (S \<inter> f -` U)" "connected (S \<inter> f -` V)"
        using UV by (auto simp: conn intro: connected_closed_monotone_preimage [OF contf fim])
      show "S = (S \<inter> f -` U) \<union> (S \<inter> f -` V)"
        using UV fim by blast
      show "closedin (top_of_set S) (S \<inter> f -` U)"
            "closedin (top_of_set S) (S \<inter> f -` V)"
        by (auto simp: continuous_on_imp_closedin cloU cloV contf fim)
    qed
  qed
  with UV_eq show "connected (U \<inter> V)"
    by simp
qed


subsection\<open>Several common variants of unicoherence\<close>

lemma connected_frontier_simple:
  fixes S :: "'a :: euclidean_space set"
  assumes "connected S" "connected(- S)" shows "connected(frontier S)"
  unfolding frontier_closures
  by (rule unicoherentD [OF unicoherent_UNIV]; simp add: assms connected_imp_connected_closure flip: closure_Un)

lemma connected_frontier_component_complement:
  fixes S :: "'a :: euclidean_space set"
  assumes "connected S" "C \<in> components(- S)" shows "connected(frontier C)"
  by (meson assms component_complement_connected connected_frontier_simple in_components_connected)

lemma connected_frontier_disjoint:
  fixes S :: "'a :: euclidean_space set"
  assumes "connected S" "connected T" "disjnt S T" and ST: "frontier S \<subseteq> frontier T"
  shows "connected(frontier S)"
proof (cases "S = UNIV")
  case True then show ?thesis
    by simp
next
  case False
  then have "-S \<noteq> {}"
    by blast
  then obtain C where C: "C \<in> components(- S)" and "T \<subseteq> C"
    by (metis ComplI disjnt_iff subsetI exists_component_superset \<open>disjnt S T\<close> \<open>connected T\<close>)
  moreover have "frontier S = frontier C"
  proof -
    have "frontier C \<subseteq> frontier S"
      using C frontier_complement frontier_of_components_subset by blast
    moreover have "x \<in> frontier C" if "x \<in> frontier S" for x
    proof -
      have "x \<in> closure C"
        using that unfolding frontier_def
        by (metis (no_types) Diff_eq ST \<open>T \<subseteq> C\<close> closure_mono contra_subsetD frontier_def le_inf_iff that)
      moreover have "x \<notin> interior C"
        using that unfolding frontier_def
        by (metis C Compl_eq_Diff_UNIV Diff_iff subsetD in_components_subset interior_diff interior_mono)
      ultimately show ?thesis
        by (auto simp: frontier_def)
    qed
    ultimately show ?thesis
      by blast
  qed
  ultimately show ?thesis
    using \<open>connected S\<close> connected_frontier_component_complement by auto
qed


subsection\<open>Some separation results\<close>

lemma separation_by_component_closed_pointwise:
  fixes S :: "'a :: euclidean_space set"
  assumes "closed S" "\<not> connected_component (- S) a b"
  obtains C where "C \<in> components S" "\<not> connected_component(- C) a b"
proof (cases "a \<in> S \<or> b \<in> S")
  case True
  then show ?thesis
    using connected_component_in componentsI that by fastforce
next
  case False
  obtain T where "T \<subseteq> S" "closed T" "T \<noteq> {}"
             and nab: "\<not> connected_component (- T) a b"
             and conn: "\<And>U. U \<subset> T \<Longrightarrow> connected_component (- U) a b"
    using closed_irreducible_separator [OF assms] by metis
  moreover have "connected T"
  proof -
    have ab: "frontier(connected_component_set (- T) a) = T" "frontier(connected_component_set (- T) b) = T"
      using frontier_minimal_separating_closed_pointwise
      by (metis False \<open>T \<subseteq> S\<close> \<open>closed T\<close> connected_component_sym conn connected_component_eq_empty connected_component_intermediate_subset empty_subsetI nab)+
    have "connected (frontier (connected_component_set (- T) a))"
    proof (rule connected_frontier_disjoint)
      show "disjnt (connected_component_set (- T) a) (connected_component_set (- T) b)"
        unfolding disjnt_iff
        by (metis connected_component_eq connected_component_eq_empty connected_component_idemp mem_Collect_eq nab)
      show "frontier (connected_component_set (- T) a) \<subseteq> frontier (connected_component_set (- T) b)"
        by (simp add: ab)
    qed auto
    with ab \<open>closed T\<close> show ?thesis
      by simp
  qed
  ultimately obtain C where "C \<in> components S" "T \<subseteq> C"
    using exists_component_superset [of T S] by blast
  then show ?thesis
    by (meson Compl_anti_mono connected_component_of_subset nab that)
qed


lemma separation_by_component_closed:
  fixes S :: "'a :: euclidean_space set"
  assumes "closed S" "\<not> connected(- S)"
  obtains C where "C \<in> components S" "\<not> connected(- C)"
proof -
  obtain x y where "closed S" "x \<notin> S" "y \<notin> S" and "\<not> connected_component (- S) x y"
    using assms by (auto simp: connected_iff_connected_component)
  then obtain C where "C \<in> components S" "\<not> connected_component(- C) x y"
    using separation_by_component_closed_pointwise by metis
  then show "thesis"
    by (metis Compl_iff \<open>x \<notin> S\<close> \<open>y \<notin> S\<close> connected_component_eq_self in_components_subset mem_Collect_eq subsetD that)
qed

lemma separation_by_Un_closed_pointwise:
  fixes S :: "'a :: euclidean_space set"
  assumes ST: "closed S" "closed T" "S \<inter> T = {}"
      and conS: "connected_component (- S) a b" and conT: "connected_component (- T) a b"
    shows "connected_component (- (S \<union> T)) a b"
proof (rule ccontr)
  have "a \<notin> S" "b \<notin> S" "a \<notin> T" "b \<notin> T"
    using conS conT connected_component_in by auto
  assume "\<not> connected_component (- (S \<union> T)) a b"
  then obtain C where "C \<in> components (S \<union> T)" and C: "\<not> connected_component(- C) a b"
    using separation_by_component_closed_pointwise assms by blast
  then have "C \<subseteq> S \<or> C \<subseteq> T"
  proof -
    have "connected C" "C \<subseteq> S \<union> T"
      using \<open>C \<in> components (S \<union> T)\<close> in_components_subset by (blast elim: componentsE)+
    moreover then have "C \<inter> T = {} \<or> C \<inter> S = {}"
      by (metis Int_empty_right ST inf.commute connected_closed)
    ultimately show ?thesis
      by blast
  qed
  then show False
    by (meson Compl_anti_mono C conS conT connected_component_of_subset)
qed

lemma separation_by_Un_closed:
  fixes S :: "'a :: euclidean_space set"
  assumes ST: "closed S" "closed T" "S \<inter> T = {}" and conS: "connected(- S)" and conT: "connected(- T)"
  shows "connected(- (S \<union> T))"
  using assms separation_by_Un_closed_pointwise
  by (fastforce simp add: connected_iff_connected_component)

lemma open_unicoherent_UNIV:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" "open T" "connected S" "connected T" "S \<union> T = UNIV"
  shows "connected(S \<inter> T)"
proof -
  have "connected(- (-S \<union> -T))"
    by (metis closed_Compl compl_sup compl_top_eq double_compl separation_by_Un_closed assms)
  then show ?thesis
    by simp
qed

lemma separation_by_component_open_aux:
  fixes S :: "'a :: euclidean_space set"
  assumes ST: "closed S" "closed T" "S \<inter> T = {}"
      and "S \<noteq> {}" "T \<noteq> {}"
  obtains C where "C \<in> components(-(S \<union> T))" "C \<noteq> {}" "frontier C \<inter> S \<noteq> {}" "frontier C \<inter> T \<noteq> {}"
proof (rule ccontr)
  let ?S = "S \<union> \<Union>{C \<in> components(- (S \<union> T)). frontier C \<subseteq> S}"
  let ?T = "T \<union> \<Union>{C \<in> components(- (S \<union> T)). frontier C \<subseteq> T}"
  assume "\<not> thesis"
  with that have *: "frontier C \<inter> S = {} \<or> frontier C \<inter> T = {}"
            if C: "C \<in> components (- (S \<union> T))" "C \<noteq> {}" for C
    using C by blast
  have "\<exists>A B::'a set. closed A \<and> closed B \<and> UNIV \<subseteq> A \<union> B \<and> A \<inter> B = {} \<and> A \<noteq> {} \<and> B \<noteq> {}"
  proof (intro exI conjI)
    have "frontier (\<Union>{C \<in> components (- S \<inter> - T). frontier C \<subseteq> S}) \<subseteq> S"
      using subset_trans [OF frontier_Union_subset_closure]
      by (metis (no_types, lifting) SUP_least \<open>closed S\<close> closure_minimal mem_Collect_eq)
    then have "frontier ?S \<subseteq> S"
      by (simp add: frontier_subset_eq assms  subset_trans [OF frontier_Un_subset])
    then show "closed ?S"
      using frontier_subset_eq by fastforce
    have "frontier (\<Union>{C \<in> components (- S \<inter> - T). frontier C \<subseteq> T}) \<subseteq> T"
      using subset_trans [OF frontier_Union_subset_closure]
      by (metis (no_types, lifting) SUP_least \<open>closed T\<close> closure_minimal mem_Collect_eq)
    then have "frontier ?T \<subseteq> T"
      by (simp add: frontier_subset_eq assms  subset_trans [OF frontier_Un_subset])
    then show "closed ?T"
      using frontier_subset_eq by fastforce
    have "UNIV \<subseteq> (S \<union> T) \<union> \<Union>(components(- (S \<union> T)))"
      using Union_components by blast
    also have "...  \<subseteq> ?S \<union> ?T"
    proof -
      have "C \<in> components (-(S \<union> T)) \<and> frontier C \<subseteq> S \<or>
            C \<in> components (-(S \<union> T)) \<and> frontier C \<subseteq> T"
        if "C \<in> components (- (S \<union> T))" "C \<noteq> {}" for C
        using * [OF that] that
        by clarify (metis (no_types, lifting) UnE \<open>closed S\<close> \<open>closed T\<close> closed_Un disjoint_iff_not_equal frontier_of_components_closed_complement subsetCE)
      then show ?thesis
        by blast
    qed
    finally show "UNIV \<subseteq> ?S \<union> ?T" .
    have "\<Union>{C \<in> components (- (S \<union> T)). frontier C \<subseteq> S} \<union>
          \<Union>{C \<in> components (- (S \<union> T)). frontier C \<subseteq> T} \<subseteq> - (S \<union> T)"
      using in_components_subset by fastforce
    moreover have "\<Union>{C \<in> components (- (S \<union> T)). frontier C \<subseteq> S} \<inter>
                   \<Union>{C \<in> components (- (S \<union> T)). frontier C \<subseteq> T} = {}"
    proof -
      have "C \<inter> C' = {}" if "C \<in> components (- (S \<union> T))" "frontier C \<subseteq> S"
                            "C' \<in> components (- (S \<union> T))" "frontier C' \<subseteq> T" for C C'
      proof -
        have NUN: "- S \<inter> - T \<noteq> UNIV"
          using \<open>T \<noteq> {}\<close> by blast
        have "C \<noteq> C'"
        proof
          assume "C = C'"
          with that have "frontier C' \<subseteq> S \<inter> T"
            by simp
          also have "... = {}"
            using \<open>S \<inter> T = {}\<close> by blast
          finally have "C' = {} \<or> C' = UNIV"
            using frontier_eq_empty by auto
          then show False
            using \<open>C = C'\<close> NUN that by (force simp: dest: in_components_nonempty in_components_subset)
        qed
        with that show ?thesis
          by (simp add: components_nonoverlap [of _ "-(S \<union> T)"])
      qed
      then show ?thesis
        by blast
    qed
    ultimately show "?S \<inter> ?T = {}"
      using ST by blast
    show "?S \<noteq> {}" "?T \<noteq> {}"
      using \<open>S \<noteq> {}\<close> \<open>T \<noteq> {}\<close> by blast+
  qed
    then show False
      by (metis Compl_disjoint connected_UNIV compl_bot_eq compl_unique connected_closedD inf_sup_absorb sup_compl_top_left1 top.extremum_uniqueI)
qed


proposition separation_by_component_open:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" and non: "\<not> connected(- S)"
  obtains C where "C \<in> components S" "\<not> connected(- C)"
proof -
  obtain T U
    where "closed T" "closed U" and TU: "T \<union> U = - S" "T \<inter> U = {}" "T \<noteq> {}" "U \<noteq> {}"
    using assms by (auto simp: connected_closed_set closed_def)
  then obtain C where C: "C \<in> components(-(T \<union> U))" "C \<noteq> {}"
          and "frontier C \<inter> T \<noteq> {}" "frontier C \<inter> U \<noteq> {}"
    using separation_by_component_open_aux [OF \<open>closed T\<close> \<open>closed U\<close> \<open>T \<inter> U = {}\<close>] by force
  show "thesis"
  proof
    show "C \<in> components S"
      using C(1) TU(1) by auto
    show "\<not> connected (- C)"
    proof
      assume "connected (- C)"
      then have "connected (frontier C)"
        using connected_frontier_simple [of C] \<open>C \<in> components S\<close> in_components_connected by blast
      then show False
        unfolding connected_closed
        by (metis C(1) TU(2) \<open>closed T\<close> \<open>closed U\<close> \<open>frontier C \<inter> T \<noteq> {}\<close> \<open>frontier C \<inter> U \<noteq> {}\<close> closed_Un frontier_of_components_closed_complement inf_bot_right inf_commute)
    qed
  qed
qed

lemma separation_by_Un_open:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" "open T" "S \<inter> T = {}" and cS: "connected(-S)" and cT: "connected(-T)"
    shows "connected(- (S \<union> T))"
  using assms unicoherent_UNIV unfolding unicoherent_def by force


lemma nonseparation_by_component_eq:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S \<or> closed S"
  shows "((\<forall>C \<in> components S. connected(-C)) \<longleftrightarrow> connected(- S))" (is "?lhs = ?rhs")
proof
  assume ?lhs with assms show ?rhs
    by (meson separation_by_component_closed separation_by_component_open)
next
  assume ?rhs with assms show ?lhs
    using component_complement_connected by force
qed


text\<open>Another interesting equivalent of an inessential mapping into C-{0}\<close>
proposition inessential_eq_extensible:
  fixes f :: "'a::euclidean_space \<Rightarrow> complex"
  assumes "closed S"
  shows "(\<exists>a. homotopic_with_canon (\<lambda>h. True) S (-{0}) f (\<lambda>t. a)) \<longleftrightarrow>
         (\<exists>g. continuous_on UNIV g \<and> (\<forall>x \<in> S. g x = f x) \<and> (\<forall>x. g x \<noteq> 0))"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain a where a: "homotopic_with_canon (\<lambda>h. True) S (-{0}) f (\<lambda>t. a)" ..
  show ?rhs
  proof (cases "S = {}")
    case True
    with a show ?thesis by force
  next
    case False
    have anr: "ANR (-{0::complex})"
      by (simp add: ANR_delete open_Compl open_imp_ANR)
    obtain g where contg: "continuous_on UNIV g" and gim: "g ` UNIV \<subseteq> -{0}"
                   and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    proof (rule Borsuk_homotopy_extension_homotopic [OF _ _ continuous_on_const _ homotopic_with_symD [OF a]])
      show "closedin (top_of_set UNIV) S"
        using assms by auto
      show "range (\<lambda>t. a) \<subseteq> - {0}"
        using a homotopic_with_imp_subset2 False by blast
    qed (use anr that in \<open>force+\<close>)
    then show ?thesis
      by force
  qed
next
  assume ?rhs
  then obtain g where contg: "continuous_on UNIV g"
          and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x" and non0: "\<And>x. g x \<noteq> 0"
    by metis
  obtain h k::"'a\<Rightarrow>'a" where hk: "homeomorphism (ball 0 1) UNIV h k"
    using homeomorphic_ball01_UNIV homeomorphic_def by blast
  then have "continuous_on (ball 0 1) (g \<circ> h)"
    by (meson contg continuous_on_compose continuous_on_subset homeomorphism_cont1 top_greatest)
  then obtain j where contj: "continuous_on (ball 0 1) j"
                  and j: "\<And>z. z \<in> ball 0 1 \<Longrightarrow> exp(j z) = (g \<circ> h) z"
    by (metis (mono_tags, opaque_lifting) continuous_logarithm_on_ball comp_apply non0)
  have [simp]: "\<And>x. x \<in> S \<Longrightarrow> h (k x) = x"
    using hk homeomorphism_apply2 by blast
  have "\<exists>\<zeta>. continuous_on S \<zeta>\<and> (\<forall>x\<in>S. f x = exp (\<zeta> x))"
  proof (intro exI conjI ballI)
    show "continuous_on S (j \<circ> k)"
    proof (rule continuous_on_compose)
      show "continuous_on S k"
        by (meson continuous_on_subset hk homeomorphism_cont2 top_greatest)
      show "continuous_on (k ` S) j"
        by (auto intro: continuous_on_subset [OF contj] simp flip: homeomorphism_image2 [OF hk])
    qed
    show "f x = exp ((j \<circ> k) x)" if "x \<in> S" for x
    proof -
      have "f x = (g \<circ> h) (k x)"
        by (simp add: gf that)
      also have "... = exp (j (k x))"
        by (metis rangeI homeomorphism_image2 [OF hk] j)
      finally show ?thesis by simp
    qed
  qed
  then show ?lhs
    by (simp add: inessential_eq_continuous_logarithm)
qed

lemma inessential_on_clopen_Union:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes T: "path_connected T"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> closedin (top_of_set (\<Union>\<F>)) S"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set (\<Union>\<F>)) S"
      and hom: "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>a. homotopic_with_canon (\<lambda>x. True) S T f (\<lambda>x. a)"
  obtains a where "homotopic_with_canon (\<lambda>x. True) (\<Union>\<F>) T f (\<lambda>x. a)"
proof (cases "\<Union>\<F> = {}")
  case True
  with that show ?thesis
    by force
next
  case False
  then obtain C where "C \<in> \<F>" "C \<noteq> {}"
    by blast
  then obtain a where clo: "closedin (top_of_set (\<Union>\<F>)) C"
    and ope: "openin (top_of_set (\<Union>\<F>)) C"
    and "homotopic_with_canon (\<lambda>x. True) C T f (\<lambda>x. a)"
    using assms by blast
  with \<open>C \<noteq> {}\<close> have "f ` C \<subseteq> T" "a \<in> T"
    using homotopic_with_imp_subset1 homotopic_with_imp_subset2 by blast+
  have "homotopic_with_canon (\<lambda>x. True) (\<Union>\<F>) T f (\<lambda>x. a)"
  proof (rule homotopic_on_clopen_Union)
    show "\<And>S. S \<in> \<F> \<Longrightarrow> closedin (top_of_set (\<Union>\<F>)) S"
         "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set (\<Union>\<F>)) S"
      by (simp_all add: assms)
    show "homotopic_with_canon (\<lambda>x. True) S T f (\<lambda>x. a)" if "S \<in> \<F>" for S
    proof (cases "S = {}")
      case True
      then show ?thesis
        by auto
    next
      case False
      then obtain b where "b \<in> S"
        by blast
      obtain c where c: "homotopic_with_canon (\<lambda>x. True) S T f (\<lambda>x. c)"
        using \<open>S \<in> \<F>\<close> hom by blast
      then have "c \<in> T"
        using \<open>b \<in> S\<close> homotopic_with_imp_subset2 by blast
      then have "homotopic_with_canon (\<lambda>x. True) S T (\<lambda>x. a) (\<lambda>x. c)"
        using T \<open>a \<in> T\<close> homotopic_constant_maps path_connected_component
        by (simp add: homotopic_constant_maps path_connected_component)
      then show ?thesis
        using c homotopic_with_symD homotopic_with_trans by blast
    qed
  qed
  then show ?thesis ..
qed

proposition Janiszewski_dual:
  fixes S :: "complex set"
  assumes
   "compact S" "compact T" "connected S" "connected T" "connected(- (S \<union> T))"
 shows "connected(S \<inter> T)"
proof -
  have ST: "compact (S \<union> T)"
    by (simp add: assms compact_Un)
  with Borsukian_imp_unicoherent [of "S \<union> T"] ST assms
  show ?thesis
    by (auto simp: closed_subset compact_imp_closed Borsukian_separation_compact unicoherent_def)
qed

end
