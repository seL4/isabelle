(*  Title:      HOL/Multivariate_Analysis/Homeomorphism.thy
    Author: LC Paulson (ported from HOL Light)
*)

section \<open>Homeomorphism Theorems\<close>

theory Homeomorphism
imports Path_Connected
begin

subsection \<open>Homeomorphism of all convex compact sets with nonempty interior\<close>

proposition ray_to_rel_frontier:
  fixes a :: "'a::real_inner"
  assumes "bounded S"
      and a: "a \<in> rel_interior S"
      and aff: "(a + l) \<in> affine hull S"
      and "l \<noteq> 0"
  obtains d where "0 < d" "(a + d *\<^sub>R l) \<in> rel_frontier S"
           "\<And>e. \<lbrakk>0 \<le> e; e < d\<rbrakk> \<Longrightarrow> (a + e *\<^sub>R l) \<in> rel_interior S"
proof -
  have aaff: "a \<in> affine hull S"
    by (meson a hull_subset rel_interior_subset rev_subsetD)
  let ?D = "{d. 0 < d \<and> a + d *\<^sub>R l \<notin> rel_interior S}"
  obtain B where "B > 0" and B: "S \<subseteq> ball a B"
    using bounded_subset_ballD [OF \<open>bounded S\<close>] by blast
  have "a + (B / norm l) *\<^sub>R l \<notin> ball a B"
    by (simp add: dist_norm \<open>l \<noteq> 0\<close>)
  with B have "a + (B / norm l) *\<^sub>R l \<notin> rel_interior S"
    using rel_interior_subset subsetCE by blast
  with \<open>B > 0\<close> \<open>l \<noteq> 0\<close> have nonMT: "?D \<noteq> {}"
    using divide_pos_pos zero_less_norm_iff by fastforce
  have bdd: "bdd_below ?D"
    by (metis (no_types, lifting) bdd_belowI le_less mem_Collect_eq)
  have relin_Ex: "\<And>x. x \<in> rel_interior S \<Longrightarrow>
                    \<exists>e>0. \<forall>x'\<in>affine hull S. dist x' x < e \<longrightarrow> x' \<in> rel_interior S"
    using openin_rel_interior [of S] by (simp add: openin_euclidean_subtopology_iff)
  define d where "d = Inf ?D"
  obtain \<epsilon> where "0 < \<epsilon>" and \<epsilon>: "\<And>\<eta>. \<lbrakk>0 \<le> \<eta>; \<eta> < \<epsilon>\<rbrakk> \<Longrightarrow> (a + \<eta> *\<^sub>R l) \<in> rel_interior S"
  proof -
    obtain e where "e>0"
            and e: "\<And>x'. x' \<in> affine hull S \<Longrightarrow> dist x' a < e \<Longrightarrow> x' \<in> rel_interior S"
      using relin_Ex a by blast
    show thesis
    proof (rule_tac \<epsilon> = "e / norm l" in that)
      show "0 < e / norm l" by (simp add: \<open>0 < e\<close> \<open>l \<noteq> 0\<close>)
    next
      show "a + \<eta> *\<^sub>R l \<in> rel_interior S" if "0 \<le> \<eta>" "\<eta> < e / norm l" for \<eta>
      proof (rule e)
        show "a + \<eta> *\<^sub>R l \<in> affine hull S"
          by (metis (no_types) add_diff_cancel_left' aff affine_affine_hull mem_affine_3_minus aaff)
        show "dist (a + \<eta> *\<^sub>R l) a < e"
          using that by (simp add: \<open>l \<noteq> 0\<close> dist_norm pos_less_divide_eq)
      qed
    qed
  qed
  have inint: "\<And>e. \<lbrakk>0 \<le> e; e < d\<rbrakk> \<Longrightarrow> a + e *\<^sub>R l \<in> rel_interior S"
    unfolding d_def using cInf_lower [OF _ bdd]
    by (metis (no_types, lifting) a add.right_neutral le_less mem_Collect_eq not_less real_vector.scale_zero_left)
  have "\<epsilon> \<le> d"
    unfolding d_def
    apply (rule cInf_greatest [OF nonMT])
    using \<epsilon> dual_order.strict_implies_order le_less_linear by blast
  with \<open>0 < \<epsilon>\<close> have "0 < d" by simp
  have "a + d *\<^sub>R l \<notin> rel_interior S"
  proof
    assume adl: "a + d *\<^sub>R l \<in> rel_interior S"
    obtain e where "e > 0"
             and e: "\<And>x'. x' \<in> affine hull S \<Longrightarrow> dist x' (a + d *\<^sub>R l) < e \<Longrightarrow> x' \<in> rel_interior S"
      using relin_Ex adl by blast
    have "d + e / norm l \<le> Inf {d. 0 < d \<and> a + d *\<^sub>R l \<notin> rel_interior S}"
    proof (rule cInf_greatest [OF nonMT], clarsimp)
      fix x::real
      assume "0 < x" and nonrel: "a + x *\<^sub>R l \<notin> rel_interior S"
      show "d + e / norm l \<le> x"
      proof (cases "x < d")
        case True with inint nonrel \<open>0 < x\<close>
          show ?thesis by auto
      next
        case False
          then have dle: "x < d + e / norm l \<Longrightarrow> dist (a + x *\<^sub>R l) (a + d *\<^sub>R l) < e"
            by (simp add: field_simps \<open>l \<noteq> 0\<close>)
          have ain: "a + x *\<^sub>R l \<in> affine hull S"
            by (metis add_diff_cancel_left' aff affine_affine_hull mem_affine_3_minus aaff)
          show ?thesis
            using e [OF ain] nonrel dle by force
      qed
    qed
    then show False
      using \<open>0 < e\<close> \<open>l \<noteq> 0\<close> by (simp add: d_def [symmetric] divide_simps)
  qed
  moreover have "a + d *\<^sub>R l \<in> closure S"
  proof (clarsimp simp: closure_approachable)
    fix \<eta>::real assume "0 < \<eta>"
    have 1: "a + (d - min d (\<eta> / 2 / norm l)) *\<^sub>R l \<in> S"
      apply (rule subsetD [OF rel_interior_subset inint])
      using \<open>l \<noteq> 0\<close> \<open>0 < d\<close> \<open>0 < \<eta>\<close> by auto
    have "norm l * min d (\<eta> / (norm l * 2)) \<le> norm l * (\<eta> / (norm l * 2))"
      by (metis min_def mult_left_mono norm_ge_zero order_refl)
    also have "... < \<eta>"
      using \<open>l \<noteq> 0\<close> \<open>0 < \<eta>\<close> by (simp add: divide_simps)
    finally have 2: "norm l * min d (\<eta> / (norm l * 2)) < \<eta>" .
    show "\<exists>y\<in>S. dist y (a + d *\<^sub>R l) < \<eta>"
      apply (rule_tac x="a + (d - min d (\<eta> / 2 / norm l)) *\<^sub>R l" in bexI)
      using 1 2 \<open>0 < d\<close> \<open>0 < \<eta>\<close> apply (auto simp: algebra_simps)
      done
  qed
  ultimately have infront: "a + d *\<^sub>R l \<in> rel_frontier S"
    by (simp add: rel_frontier_def)
  show ?thesis
    by (rule that [OF \<open>0 < d\<close> infront inint])
qed

corollary ray_to_frontier:
  fixes a :: "'a::euclidean_space"
  assumes "bounded S"
      and a: "a \<in> interior S"
      and "l \<noteq> 0"
  obtains d where "0 < d" "(a + d *\<^sub>R l) \<in> frontier S"
           "\<And>e. \<lbrakk>0 \<le> e; e < d\<rbrakk> \<Longrightarrow> (a + e *\<^sub>R l) \<in> interior S"
proof -
  have "interior S = rel_interior S"
    using a rel_interior_nonempty_interior by auto
  then have "a \<in> rel_interior S"
    using a by simp
  then show ?thesis
    apply (rule ray_to_rel_frontier [OF \<open>bounded S\<close> _ _ \<open>l \<noteq> 0\<close>])
     using a affine_hull_nonempty_interior apply blast
    by (simp add: \<open>interior S = rel_interior S\<close> frontier_def rel_frontier_def that)
qed

proposition
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and 0: "0 \<in> rel_interior S"
      and star: "\<And>x. x \<in> S \<Longrightarrow> open_segment 0 x \<subseteq> rel_interior S"
    shows starlike_compact_projective1_0:
            "S - rel_interior S homeomorphic sphere 0 1 \<inter> affine hull S"
            (is "?SMINUS homeomorphic ?SPHER")
      and starlike_compact_projective2_0:
            "S homeomorphic cball 0 1 \<inter> affine hull S"
            (is "S homeomorphic ?CBALL")
proof -
  have starI: "(u *\<^sub>R x) \<in> rel_interior S" if "x \<in> S" "0 \<le> u" "u < 1" for x u
  proof (cases "x=0 \<or> u=0")
    case True with 0 show ?thesis by force
  next
    case False with that show ?thesis
      by (auto simp: in_segment intro: star [THEN subsetD])
  qed
  have "0 \<in> S"  using assms rel_interior_subset by auto
  define proj where "proj \<equiv> \<lambda>x::'a. x /\<^sub>R norm x"
  have eqI: "x = y" if "proj x = proj y" "norm x = norm y" for x y
    using that  by (force simp: proj_def)
  then have iff_eq: "\<And>x y. (proj x = proj y \<and> norm x = norm y) \<longleftrightarrow> x = y"
    by blast
  have projI: "x \<in> affine hull S \<Longrightarrow> proj x \<in> affine hull S" for x
    by (metis \<open>0 \<in> S\<close> affine_hull_span_0 hull_inc span_mul proj_def)
  have nproj1 [simp]: "x \<noteq> 0 \<Longrightarrow> norm(proj x) = 1" for x
    by (simp add: proj_def)
  have proj0_iff [simp]: "proj x = 0 \<longleftrightarrow> x = 0" for x
    by (simp add: proj_def)
  have cont_proj: "continuous_on (UNIV - {0}) proj"
    unfolding proj_def by (rule continuous_intros | force)+
  have proj_spherI: "\<And>x. \<lbrakk>x \<in> affine hull S; x \<noteq> 0\<rbrakk> \<Longrightarrow> proj x \<in> ?SPHER"
    by (simp add: projI)
  have "bounded S" "closed S"
    using \<open>compact S\<close> compact_eq_bounded_closed by blast+
  have inj_on_proj: "inj_on proj (S - rel_interior S)"
  proof
    fix x y
    assume x: "x \<in> S - rel_interior S"
       and y: "y \<in> S - rel_interior S" and eq: "proj x = proj y"
    then have xynot: "x \<noteq> 0" "y \<noteq> 0" "x \<in> S" "y \<in> S" "x \<notin> rel_interior S" "y \<notin> rel_interior S"
      using 0 by auto
    consider "norm x = norm y" | "norm x < norm y" | "norm x > norm y" by linarith
    then show "x = y"
    proof cases
      assume "norm x = norm y"
        with iff_eq eq show "x = y" by blast
    next
      assume *: "norm x < norm y"
      have "x /\<^sub>R norm x = norm x *\<^sub>R (x /\<^sub>R norm x) /\<^sub>R norm (norm x *\<^sub>R (x /\<^sub>R norm x))"
        by force
      then have "proj ((norm x / norm y) *\<^sub>R y) = proj x"
        by (metis (no_types) divide_inverse local.proj_def eq scaleR_scaleR)
      then have [simp]: "(norm x / norm y) *\<^sub>R y = x"
        by (rule eqI) (simp add: \<open>y \<noteq> 0\<close>)
      have no: "0 \<le> norm x / norm y" "norm x / norm y < 1"
        using * by (auto simp: divide_simps)
      then show "x = y"
        using starI [OF \<open>y \<in> S\<close> no] xynot by auto
    next
      assume *: "norm x > norm y"
      have "y /\<^sub>R norm y = norm y *\<^sub>R (y /\<^sub>R norm y) /\<^sub>R norm (norm y *\<^sub>R (y /\<^sub>R norm y))"
        by force
      then have "proj ((norm y / norm x) *\<^sub>R x) = proj y"
        by (metis (no_types) divide_inverse local.proj_def eq scaleR_scaleR)
      then have [simp]: "(norm y / norm x) *\<^sub>R x = y"
        by (rule eqI) (simp add: \<open>x \<noteq> 0\<close>)
      have no: "0 \<le> norm y / norm x" "norm y / norm x < 1"
        using * by (auto simp: divide_simps)
      then show "x = y"
        using starI [OF \<open>x \<in> S\<close> no] xynot by auto
    qed
  qed
  have "\<exists>surf. homeomorphism (S - rel_interior S) ?SPHER proj surf"
  proof (rule homeomorphism_compact)
    show "compact (S - rel_interior S)"
       using \<open>compact S\<close> compact_rel_boundary by blast
    show "continuous_on (S - rel_interior S) proj"
      using 0 by (blast intro: continuous_on_subset [OF cont_proj])
    show "proj ` (S - rel_interior S) = ?SPHER"
    proof
      show "proj ` (S - rel_interior S) \<subseteq> ?SPHER"
        using 0 by (force simp: hull_inc projI intro: nproj1)
      show "?SPHER \<subseteq> proj ` (S - rel_interior S)"
      proof (clarsimp simp: proj_def)
        fix x
        assume "x \<in> affine hull S" and nox: "norm x = 1"
        then have "x \<noteq> 0" by auto
        obtain d where "0 < d" and dx: "(d *\<^sub>R x) \<in> rel_frontier S"
                   and ri: "\<And>e. \<lbrakk>0 \<le> e; e < d\<rbrakk> \<Longrightarrow> (e *\<^sub>R x) \<in> rel_interior S"
          using ray_to_rel_frontier [OF \<open>bounded S\<close> 0] \<open>x \<in> affine hull S\<close> \<open>x \<noteq> 0\<close> by auto
        show "x \<in> (\<lambda>x. x /\<^sub>R norm x) ` (S - rel_interior S)"
          apply (rule_tac x="d *\<^sub>R x" in image_eqI)
          using \<open>0 < d\<close>
          using dx \<open>closed S\<close> apply (auto simp: rel_frontier_def divide_simps nox)
          done
      qed
    qed
  qed (rule inj_on_proj)
  then obtain surf where surf: "homeomorphism (S - rel_interior S) ?SPHER proj surf"
    by blast
  then have cont_surf: "continuous_on (proj ` (S - rel_interior S)) surf"
    by (auto simp: homeomorphism_def)
  have surf_nz: "\<And>x. x \<in> ?SPHER \<Longrightarrow> surf x \<noteq> 0"
    by (metis "0" DiffE homeomorphism_def imageI surf)
  have cont_nosp: "continuous_on (?SPHER) (\<lambda>x. norm x *\<^sub>R ((surf o proj) x))"
    apply (rule continuous_intros)+
    apply (rule continuous_on_subset [OF cont_proj], force)
    apply (rule continuous_on_subset [OF cont_surf])
    apply (force simp: homeomorphism_image1 [OF surf] dest: proj_spherI)
    done
  have surfpS: "\<And>x. \<lbrakk>norm x = 1; x \<in> affine hull S\<rbrakk> \<Longrightarrow> surf (proj x) \<in> S"
    by (metis (full_types) DiffE \<open>0 \<in> S\<close> homeomorphism_def image_eqI norm_zero proj_spherI real_vector.scale_zero_left scaleR_one surf)
  have *: "\<exists>y. norm y = 1 \<and> y \<in> affine hull S \<and> x = surf (proj y)"
          if "x \<in> S" "x \<notin> rel_interior S" for x
  proof -
    have "proj x \<in> ?SPHER"
      by (metis (full_types) "0" hull_inc proj_spherI that)
    moreover have "surf (proj x) = x"
      by (metis Diff_iff homeomorphism_def surf that)
    ultimately show ?thesis
      by (metis \<open>\<And>x. x \<in> ?SPHER \<Longrightarrow> surf x \<noteq> 0\<close> hull_inc inverse_1 local.proj_def norm_sgn projI scaleR_one sgn_div_norm that(1))
  qed
  have surfp_notin: "\<And>x. \<lbrakk>norm x = 1; x \<in> affine hull S\<rbrakk> \<Longrightarrow> surf (proj x) \<notin> rel_interior S"
    by (metis (full_types) DiffE one_neq_zero homeomorphism_def image_eqI norm_zero proj_spherI surf)
  have no_sp_im: "(\<lambda>x. norm x *\<^sub>R surf (proj x)) ` (?SPHER) = S - rel_interior S"
    by (auto simp: surfpS image_def Bex_def surfp_notin *)
  have inj_spher: "inj_on (\<lambda>x. norm x *\<^sub>R surf (proj x)) ?SPHER"
  proof
    fix x y
    assume xy: "x \<in> ?SPHER" "y \<in> ?SPHER"
       and eq: " norm x *\<^sub>R surf (proj x) = norm y *\<^sub>R surf (proj y)"
    then have "norm x = 1" "norm y = 1" "x \<in> affine hull S" "y \<in> affine hull S"
      using 0 by auto
    with eq show "x = y"
      by (simp add: proj_def) (metis surf xy homeomorphism_def)
  qed
  have co01: "compact ?SPHER"
    by (simp add: closed_affine_hull compact_Int_closed)
  show "?SMINUS homeomorphic ?SPHER"
    apply (subst homeomorphic_sym)
    apply (rule homeomorphic_compact [OF co01 cont_nosp [unfolded o_def] no_sp_im inj_spher])
    done
  have proj_scaleR: "\<And>a x. 0 < a \<Longrightarrow> proj (a *\<^sub>R x) = proj x"
    by (simp add: proj_def)
  have cont_sp0: "continuous_on (affine hull S - {0}) (surf o proj)"
    apply (rule continuous_on_compose [OF continuous_on_subset [OF cont_proj]], force)
    apply (rule continuous_on_subset [OF cont_surf])
    using homeomorphism_image1 proj_spherI surf by fastforce
  obtain B where "B>0" and B: "\<And>x. x \<in> S \<Longrightarrow> norm x \<le> B"
    by (metis compact_imp_bounded \<open>compact S\<close> bounded_pos_less less_eq_real_def)
  have cont_nosp: "continuous (at x within ?CBALL) (\<lambda>x. norm x *\<^sub>R surf (proj x))"
         if "norm x \<le> 1" "x \<in> affine hull S" for x
  proof (cases "x=0")
    case True
    show ?thesis using True
      apply (simp add: continuous_within)
      apply (rule lim_null_scaleR_bounded [where B=B])
      apply (simp_all add: tendsto_norm_zero eventually_at)
      apply (rule_tac x=B in exI)
      using B surfpS proj_def projI apply (auto simp: \<open>B > 0\<close>)
      done
  next
    case False
    then have "\<forall>\<^sub>F x in at x. (x \<in> affine hull S - {0}) = (x \<in> affine hull S)"
      apply (simp add: eventually_at)
      apply (rule_tac x="norm x" in exI)
      apply (auto simp: False)
      done
    with cont_sp0 have *: "continuous (at x within affine hull S) (\<lambda>x. surf (proj x))"
      apply (simp add: continuous_on_eq_continuous_within)
      apply (drule_tac x=x in bspec, force simp: False that)
      apply (simp add: continuous_within Lim_transform_within_set)
      done
    show ?thesis
      apply (rule continuous_within_subset [where s = "affine hull S", OF _ Int_lower2])
      apply (rule continuous_intros *)+
      done
  qed
  have cont_nosp2: "continuous_on ?CBALL (\<lambda>x. norm x *\<^sub>R ((surf o proj) x))"
    by (simp add: continuous_on_eq_continuous_within cont_nosp)
  have "norm y *\<^sub>R surf (proj y) \<in> S"  if "y \<in> cball 0 1" and yaff: "y \<in> affine hull S" for y
  proof (cases "y=0")
    case True then show ?thesis
      by (simp add: \<open>0 \<in> S\<close>)
  next
    case False
    then have "norm y *\<^sub>R surf (proj y) = norm y *\<^sub>R surf (proj (y /\<^sub>R norm y))"
      by (simp add: proj_def)
    have "norm y \<le> 1" using that by simp
    have "surf (proj (y /\<^sub>R norm y)) \<in> S"
      apply (rule surfpS)
      using proj_def projI yaff
      by (auto simp: False)
    then have "surf (proj y) \<in> S"
      by (simp add: False proj_def)
    then show "norm y *\<^sub>R surf (proj y) \<in> S"
      by (metis dual_order.antisym le_less_linear norm_ge_zero rel_interior_subset scaleR_one
                starI subset_eq \<open>norm y \<le> 1\<close>)
  qed
  moreover have "x \<in> (\<lambda>x. norm x *\<^sub>R surf (proj x)) ` (?CBALL)" if "x \<in> S" for x
  proof (cases "x=0")
    case True with that hull_inc  show ?thesis by fastforce
  next
    case False
    then have psp: "proj (surf (proj x)) = proj x"
      by (metis homeomorphism_def hull_inc proj_spherI surf that)
    have nxx: "norm x *\<^sub>R proj x = x"
      by (simp add: False local.proj_def)
    have affineI: "(1 / norm (surf (proj x))) *\<^sub>R x \<in> affine hull S"
      by (metis \<open>0 \<in> S\<close> affine_hull_span_0 hull_inc span_clauses(4) that)
    have sproj_nz: "surf (proj x) \<noteq> 0"
      by (metis False proj0_iff psp)
    then have "proj x = proj (proj x)"
      by (metis False nxx proj_scaleR zero_less_norm_iff)
    moreover have scaleproj: "\<And>a r. r *\<^sub>R proj a = (r / norm a) *\<^sub>R a"
      by (simp add: divide_inverse local.proj_def)
    ultimately have "(norm (surf (proj x)) / norm x) *\<^sub>R x \<notin> rel_interior S"
      by (metis (no_types) sproj_nz divide_self_if hull_inc norm_eq_zero nproj1 projI psp scaleR_one surfp_notin that)
    then have "(norm (surf (proj x)) / norm x) \<ge> 1"
      using starI [OF that] by (meson starI [OF that] le_less_linear norm_ge_zero zero_le_divide_iff)
    then have nole: "norm x \<le> norm (surf (proj x))"
      by (simp add: le_divide_eq_1)
    show ?thesis
      apply (rule_tac x="inverse(norm(surf (proj x))) *\<^sub>R x" in image_eqI)
      apply (metis (no_types, hide_lams) mult.commute scaleproj abs_inverse abs_norm_cancel divide_inverse norm_scaleR nxx positive_imp_inverse_positive proj_scaleR psp sproj_nz zero_less_norm_iff)
      apply (auto simp: divide_simps nole affineI)
      done
  qed
  ultimately have im_cball: "(\<lambda>x. norm x *\<^sub>R surf (proj x)) ` ?CBALL = S"
    by blast
  have inj_cball: "inj_on (\<lambda>x. norm x *\<^sub>R surf (proj x)) ?CBALL"
  proof
    fix x y
    assume "x \<in> ?CBALL" "y \<in> ?CBALL"
       and eq: "norm x *\<^sub>R surf (proj x) = norm y *\<^sub>R surf (proj y)"
    then have x: "x \<in> affine hull S" and y: "y \<in> affine hull S"
      using 0 by auto
    show "x = y"
    proof (cases "x=0 \<or> y=0")
      case True then show "x = y" using eq proj_spherI surf_nz x y by force
    next
      case False
      with x y have speq: "surf (proj x) = surf (proj y)"
        by (metis eq homeomorphism_apply2 proj_scaleR proj_spherI surf zero_less_norm_iff)
      then have "norm x = norm y"
        by (metis \<open>x \<in> affine hull S\<close> \<open>y \<in> affine hull S\<close> eq proj_spherI real_vector.scale_cancel_right surf_nz)
      moreover have "proj x = proj y"
        by (metis (no_types) False speq homeomorphism_apply2 proj_spherI surf x y)
      ultimately show "x = y"
        using eq eqI by blast
    qed
  qed
  have co01: "compact ?CBALL"
    by (simp add: closed_affine_hull compact_Int_closed)
  show "S homeomorphic ?CBALL"
    apply (subst homeomorphic_sym)
    apply (rule homeomorphic_compact [OF co01 cont_nosp2 [unfolded o_def] im_cball inj_cball])
    done
qed

corollary
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and a: "a \<in> rel_interior S"
      and star: "\<And>x. x \<in> S \<Longrightarrow> open_segment a x \<subseteq> rel_interior S"
    shows starlike_compact_projective1:
            "S - rel_interior S homeomorphic sphere a 1 \<inter> affine hull S"
      and starlike_compact_projective2:
            "S homeomorphic cball a 1 \<inter> affine hull S"
proof -
  have 1: "compact (op+ (-a) ` S)" by (meson assms compact_translation)
  have 2: "0 \<in> rel_interior (op+ (-a) ` S)"
    by (simp add: a rel_interior_translation)
  have 3: "open_segment 0 x \<subseteq> rel_interior (op+ (-a) ` S)" if "x \<in> (op+ (-a) ` S)" for x
  proof -
    have "x+a \<in> S" using that by auto
    then have "open_segment a (x+a) \<subseteq> rel_interior S" by (metis star)
    then show ?thesis using open_segment_translation
      using rel_interior_translation by fastforce
  qed
  have "S - rel_interior S homeomorphic (op+ (-a) ` S) - rel_interior (op+ (-a) ` S)"
    by (metis rel_interior_translation translation_diff homeomorphic_translation)
  also have "... homeomorphic sphere 0 1 \<inter> affine hull (op+ (-a) ` S)"
    by (rule starlike_compact_projective1_0 [OF 1 2 3])
  also have "... = op+ (-a) ` (sphere a 1 \<inter> affine hull S)"
    by (metis affine_hull_translation left_minus sphere_translation translation_Int)
  also have "... homeomorphic sphere a 1 \<inter> affine hull S"
    using homeomorphic_translation homeomorphic_sym by blast
  finally show "S - rel_interior S homeomorphic sphere a 1 \<inter> affine hull S" .

  have "S homeomorphic (op+ (-a) ` S)"
    by (metis homeomorphic_translation)
  also have "... homeomorphic cball 0 1 \<inter> affine hull (op+ (-a) ` S)"
    by (rule starlike_compact_projective2_0 [OF 1 2 3])
  also have "... = op+ (-a) ` (cball a 1 \<inter> affine hull S)"
    by (metis affine_hull_translation left_minus cball_translation translation_Int)
  also have "... homeomorphic cball a 1 \<inter> affine hull S"
    using homeomorphic_translation homeomorphic_sym by blast
  finally show "S homeomorphic cball a 1 \<inter> affine hull S" .
qed

corollary starlike_compact_projective_special:
  assumes "compact S"
    and cb01: "cball (0::'a::euclidean_space) 1 \<subseteq> S"
    and scale: "\<And>x u. \<lbrakk>x \<in> S; 0 \<le> u; u < 1\<rbrakk> \<Longrightarrow> u *\<^sub>R x \<in> S - frontier S"
  shows "S homeomorphic (cball (0::'a::euclidean_space) 1)"
proof -
  have "ball 0 1 \<subseteq> interior S"
    using cb01 interior_cball interior_mono by blast
  then have 0: "0 \<in> rel_interior S"
    by (meson centre_in_ball subsetD interior_subset_rel_interior le_numeral_extra(2) not_le)
  have [simp]: "affine hull S = UNIV"
    using \<open>ball 0 1 \<subseteq> interior S\<close> by (auto intro!: affine_hull_nonempty_interior)
  have star: "open_segment 0 x \<subseteq> rel_interior S" if "x \<in> S" for x
  proof 
    fix p assume "p \<in> open_segment 0 x"
    then obtain u where "x \<noteq> 0" and u: "0 \<le> u" "u < 1" and p: "u *\<^sub>R x = p"
      by (auto simp: in_segment) 
    then show "p \<in> rel_interior S"
      using scale [OF that u] closure_subset frontier_def interior_subset_rel_interior by fastforce
  qed
  show ?thesis
    using starlike_compact_projective2_0 [OF \<open>compact S\<close> 0 star] by simp
qed

lemma homeomorphic_convex_lemma:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "convex S" "compact S" "convex T" "compact T"
      and affeq: "aff_dim S = aff_dim T"
    shows "(S - rel_interior S) homeomorphic (T - rel_interior T) \<and>
           S homeomorphic T"
proof (cases "rel_interior S = {} \<or> rel_interior T = {}")
  case True
    then show ?thesis
      by (metis Diff_empty affeq \<open>convex S\<close> \<open>convex T\<close> aff_dim_empty homeomorphic_empty rel_interior_eq_empty aff_dim_empty)
next
  case False
  then obtain a b where a: "a \<in> rel_interior S" and b: "b \<in> rel_interior T" by auto
  have starS: "\<And>x. x \<in> S \<Longrightarrow> open_segment a x \<subseteq> rel_interior S"
    using rel_interior_closure_convex_segment
          a \<open>convex S\<close> closure_subset subsetCE by blast
  have starT: "\<And>x. x \<in> T \<Longrightarrow> open_segment b x \<subseteq> rel_interior T"
    using rel_interior_closure_convex_segment
          b \<open>convex T\<close> closure_subset subsetCE by blast
  let ?aS = "op+ (-a) ` S" and ?bT = "op+ (-b) ` T"
  have 0: "0 \<in> affine hull ?aS" "0 \<in> affine hull ?bT"
    by (metis a b subsetD hull_inc image_eqI left_minus rel_interior_subset)+
  have subs: "subspace (span ?aS)" "subspace (span ?bT)"
    by (rule subspace_span)+
  moreover
  have "dim (span (op + (- a) ` S)) = dim (span (op + (- b) ` T))"
    by (metis 0 aff_dim_translation_eq aff_dim_zero affeq dim_span nat_int)
  ultimately obtain f g where "linear f" "linear g"
                and fim: "f ` span ?aS = span ?bT"
                and gim: "g ` span ?bT = span ?aS"
                and fno: "\<And>x. x \<in> span ?aS \<Longrightarrow> norm(f x) = norm x"
                and gno: "\<And>x. x \<in> span ?bT \<Longrightarrow> norm(g x) = norm x"
                and gf: "\<And>x. x \<in> span ?aS \<Longrightarrow> g(f x) = x"
                and fg: "\<And>x. x \<in> span ?bT \<Longrightarrow> f(g x) = x"
    by (rule isometries_subspaces) blast
  have [simp]: "continuous_on A f" for A
    using \<open>linear f\<close> linear_conv_bounded_linear linear_continuous_on by blast
  have [simp]: "continuous_on B g" for B
    using \<open>linear g\<close> linear_conv_bounded_linear linear_continuous_on by blast
  have eqspanS: "affine hull ?aS = span ?aS"
    by (metis a affine_hull_span_0 subsetD hull_inc image_eqI left_minus rel_interior_subset)
  have eqspanT: "affine hull ?bT = span ?bT"
    by (metis b affine_hull_span_0 subsetD hull_inc image_eqI left_minus rel_interior_subset)
  have "S homeomorphic cball a 1 \<inter> affine hull S"
    by (rule starlike_compact_projective2 [OF \<open>compact S\<close> a starS])
  also have "... homeomorphic op+ (-a) ` (cball a 1 \<inter> affine hull S)"
    by (metis homeomorphic_translation)
  also have "... = cball 0 1 \<inter> op+ (-a) ` (affine hull S)"
    by (auto simp: dist_norm)
  also have "... = cball 0 1 \<inter> span ?aS"
    using eqspanS affine_hull_translation by blast
  also have "... homeomorphic cball 0 1 \<inter> span ?bT"
    proof (rule homeomorphicI [where f=f and g=g])
      show fim1: "f ` (cball 0 1 \<inter> span ?aS) = cball 0 1 \<inter> span ?bT"
        apply (rule subset_antisym)
         using fim fno apply (force simp:, clarify)
        by (metis IntI fg gim gno image_eqI mem_cball_0)
      show "g ` (cball 0 1 \<inter> span ?bT) = cball 0 1 \<inter> span ?aS"
        apply (rule subset_antisym)
         using gim gno apply (force simp:, clarify)
        by (metis IntI fim1 gf image_eqI)
    qed (auto simp: fg gf)
  also have "... = cball 0 1 \<inter> op+ (-b) ` (affine hull T)"
    using eqspanT affine_hull_translation by blast
  also have "... = op+ (-b) ` (cball b 1 \<inter> affine hull T)"
    by (auto simp: dist_norm)
  also have "... homeomorphic (cball b 1 \<inter> affine hull T)"
    by (metis homeomorphic_translation homeomorphic_sym)
  also have "... homeomorphic T"
    by (metis starlike_compact_projective2 [OF \<open>compact T\<close> b starT] homeomorphic_sym)
  finally have 1: "S homeomorphic T" .

  have "S - rel_interior S homeomorphic sphere a 1 \<inter> affine hull S"
    by (rule starlike_compact_projective1 [OF \<open>compact S\<close> a starS])
  also have "... homeomorphic op+ (-a) ` (sphere a 1 \<inter> affine hull S)"
    by (metis homeomorphic_translation)
  also have "... = sphere 0 1 \<inter> op+ (-a) ` (affine hull S)"
    by (auto simp: dist_norm)
  also have "... = sphere 0 1 \<inter> span ?aS"
    using eqspanS affine_hull_translation by blast
  also have "... homeomorphic sphere 0 1 \<inter> span ?bT"
    proof (rule homeomorphicI [where f=f and g=g])
      show fim1: "f ` (sphere 0 1 \<inter> span ?aS) = sphere 0 1 \<inter> span ?bT"
        apply (rule subset_antisym)
        using fim fno apply (force simp:, clarify)
        by (metis IntI fg gim gno image_eqI mem_sphere_0)
      show "g ` (sphere 0 1 \<inter> span ?bT) = sphere 0 1 \<inter> span ?aS"
        apply (rule subset_antisym)
        using gim gno apply (force simp:, clarify)
        by (metis IntI fim1 gf image_eqI)
    qed (auto simp: fg gf)
  also have "... = sphere 0 1 \<inter> op+ (-b) ` (affine hull T)"
    using eqspanT affine_hull_translation by blast
  also have "... = op+ (-b) ` (sphere b 1 \<inter> affine hull T)"
    by (auto simp: dist_norm)
  also have "... homeomorphic (sphere b 1 \<inter> affine hull T)"
    by (metis homeomorphic_translation homeomorphic_sym)
  also have "... homeomorphic T - rel_interior T"
    by (metis starlike_compact_projective1 [OF \<open>compact T\<close> b starT] homeomorphic_sym)
  finally have 2: "S - rel_interior S homeomorphic T - rel_interior T" .
  show ?thesis
    using 1 2 by blast
qed

lemma homeomorphic_convex_compact_sets:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "convex S" "compact S" "convex T" "compact T"
      and affeq: "aff_dim S = aff_dim T"
    shows "S homeomorphic T"
using homeomorphic_convex_lemma [OF assms] assms
by (auto simp: rel_frontier_def)

lemma homeomorphic_rel_frontiers_convex_bounded_sets:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "convex S" "bounded S" "convex T" "bounded T"
      and affeq: "aff_dim S = aff_dim T"
    shows  "rel_frontier S homeomorphic rel_frontier T"
using assms homeomorphic_convex_lemma [of "closure S" "closure T"]
by (simp add: rel_frontier_def convex_rel_interior_closure)


subsection\<open>Homeomorphisms between punctured spheres and affine sets\<close>
text\<open>Including the famous stereoscopic projection of the 3-D sphere to the complex plane\<close>

text\<open>The special case with centre 0 and radius 1\<close>
lemma homeomorphic_punctured_affine_sphere_affine_01:
  assumes "b \<in> sphere 0 1" "affine T" "0 \<in> T" "b \<in> T" "affine p"
      and affT: "aff_dim T = aff_dim p + 1"
    shows "(sphere 0 1 \<inter> T) - {b} homeomorphic p"
proof -
  have [simp]: "norm b = 1" "b\<bullet>b = 1"
    using assms by (auto simp: norm_eq_1)
  have [simp]: "T \<inter> {v. b\<bullet>v = 0} \<noteq> {}"
    using \<open>0 \<in> T\<close> by auto
  have [simp]: "\<not> T \<subseteq> {v. b\<bullet>v = 0}"
    using \<open>norm b = 1\<close> \<open>b \<in> T\<close> by auto
  define f where "f \<equiv> \<lambda>x. 2 *\<^sub>R b + (2 / (1 - b\<bullet>x)) *\<^sub>R (x - b)"
  define g where "g \<equiv> \<lambda>y. b + (4 / (norm y ^ 2 + 4)) *\<^sub>R (y - 2 *\<^sub>R b)"
  have [simp]: "\<And>x. \<lbrakk>x \<in> T; b\<bullet>x = 0\<rbrakk> \<Longrightarrow> f (g x) = x"
    unfolding f_def g_def by (simp add: algebra_simps divide_simps add_nonneg_eq_0_iff)
  have no: "\<And>x. \<lbrakk>norm x = 1; b\<bullet>x \<noteq> 1\<rbrakk> \<Longrightarrow> (norm (f x))\<^sup>2 = 4 * (1 + b\<bullet>x) / (1 - b\<bullet>x)"
    apply (simp add: dot_square_norm [symmetric])
    apply (simp add: f_def vector_add_divide_simps divide_simps norm_eq_1)
    apply (simp add: algebra_simps inner_commute)
    done
  have [simp]: "\<And>u::real. 8 + u * (u * 8) = u * 16 \<longleftrightarrow> u=1"
    by algebra
  have [simp]: "\<And>x. \<lbrakk>norm x = 1; b \<bullet> x \<noteq> 1\<rbrakk> \<Longrightarrow> g (f x) = x"
    unfolding g_def no by (auto simp: f_def divide_simps)
  have [simp]: "\<And>x. \<lbrakk>x \<in> T; b \<bullet> x = 0\<rbrakk> \<Longrightarrow> norm (g x) = 1"
    unfolding g_def
    apply (rule power2_eq_imp_eq)
    apply (simp_all add: dot_square_norm [symmetric] divide_simps vector_add_divide_simps)
    apply (simp add: algebra_simps inner_commute)
    done
  have [simp]: "\<And>x. \<lbrakk>x \<in> T; b \<bullet> x = 0\<rbrakk> \<Longrightarrow> b \<bullet> g x \<noteq> 1"
    unfolding g_def
    apply (simp_all add: dot_square_norm [symmetric] divide_simps vector_add_divide_simps add_nonneg_eq_0_iff)
    apply (auto simp: algebra_simps)
    done
  have "subspace T"
    by (simp add: assms subspace_affine)
  have [simp]: "\<And>x. \<lbrakk>x \<in> T; b \<bullet> x = 0\<rbrakk> \<Longrightarrow> g x \<in> T"
    unfolding g_def
    by (blast intro: \<open>subspace T\<close> \<open>b \<in> T\<close> subspace_add subspace_mul subspace_diff)
  have "f ` {x. norm x = 1 \<and> b\<bullet>x \<noteq> 1} \<subseteq> {x. b\<bullet>x = 0}"
    unfolding f_def using \<open>norm b = 1\<close> norm_eq_1
    by (force simp: field_simps inner_add_right inner_diff_right)
  moreover have "f ` T \<subseteq> T"
    unfolding f_def using assms
    apply (auto simp: field_simps inner_add_right inner_diff_right)
    by (metis add_0 diff_zero mem_affine_3_minus)
  moreover have "{x. b\<bullet>x = 0} \<inter> T \<subseteq> f ` ({x. norm x = 1 \<and> b\<bullet>x \<noteq> 1} \<inter> T)"
    apply clarify
    apply (rule_tac x = "g x" in image_eqI, auto)
    done
  ultimately have imf: "f ` ({x. norm x = 1 \<and> b\<bullet>x \<noteq> 1} \<inter> T) = {x. b\<bullet>x = 0} \<inter> T"
    by blast
  have no4: "\<And>y. b\<bullet>y = 0 \<Longrightarrow> norm ((y\<bullet>y + 4) *\<^sub>R b + 4 *\<^sub>R (y - 2 *\<^sub>R b)) = y\<bullet>y + 4"
    apply (rule power2_eq_imp_eq)
    apply (simp_all add: dot_square_norm [symmetric])
    apply (auto simp: power2_eq_square algebra_simps inner_commute)
    done
  have [simp]: "\<And>x. \<lbrakk>norm x = 1; b \<bullet> x \<noteq> 1\<rbrakk> \<Longrightarrow> b \<bullet> f x = 0"
    by (simp add: f_def algebra_simps divide_simps)
  have [simp]: "\<And>x. \<lbrakk>x \<in> T; norm x = 1; b \<bullet> x \<noteq> 1\<rbrakk> \<Longrightarrow> f x \<in> T"
    unfolding f_def
    by (blast intro: \<open>subspace T\<close> \<open>b \<in> T\<close> subspace_add subspace_mul subspace_diff)
  have "g ` {x. b\<bullet>x = 0} \<subseteq> {x. norm x = 1 \<and> b\<bullet>x \<noteq> 1}"
    unfolding g_def
    apply (clarsimp simp: no4 vector_add_divide_simps divide_simps add_nonneg_eq_0_iff dot_square_norm [symmetric])
    apply (auto simp: algebra_simps)
    done
  moreover have "g ` T \<subseteq> T"
    unfolding g_def
    by (blast intro: \<open>subspace T\<close> \<open>b \<in> T\<close> subspace_add subspace_mul subspace_diff)
  moreover have "{x. norm x = 1 \<and> b\<bullet>x \<noteq> 1} \<inter> T \<subseteq> g ` ({x. b\<bullet>x = 0} \<inter> T)"
    apply clarify
    apply (rule_tac x = "f x" in image_eqI, auto)
    done
  ultimately have img: "g ` ({x. b\<bullet>x = 0} \<inter> T) = {x. norm x = 1 \<and> b\<bullet>x \<noteq> 1} \<inter> T"
    by blast
  have aff: "affine ({x. b\<bullet>x = 0} \<inter> T)"
    by (blast intro: affine_hyperplane assms)
  have contf: "continuous_on ({x. norm x = 1 \<and> b\<bullet>x \<noteq> 1} \<inter> T) f"
    unfolding f_def by (rule continuous_intros | force)+
  have contg: "continuous_on ({x. b\<bullet>x = 0} \<inter> T) g"
    unfolding g_def by (rule continuous_intros | force simp: add_nonneg_eq_0_iff)+
  have "(sphere 0 1 \<inter> T) - {b} = {x. norm x = 1 \<and> (b\<bullet>x \<noteq> 1)} \<inter> T"
    using  \<open>norm b = 1\<close> by (auto simp: norm_eq_1) (metis vector_eq  \<open>b\<bullet>b = 1\<close>)
  also have "... homeomorphic {x. b\<bullet>x = 0} \<inter> T"
    by (rule homeomorphicI [OF imf img contf contg]) auto
  also have "... homeomorphic p"
    apply (rule homeomorphic_affine_sets [OF aff \<open>affine p\<close>])
    apply (simp add: Int_commute aff_dim_affine_Int_hyperplane [OF \<open>affine T\<close>] affT)
    done
  finally show ?thesis .
qed

theorem homeomorphic_punctured_affine_sphere_affine:
  fixes a :: "'a :: euclidean_space"
  assumes "0 < r" "b \<in> sphere a r" "affine T" "a \<in> T" "b \<in> T" "affine p"
      and aff: "aff_dim T = aff_dim p + 1"
    shows "((sphere a r \<inter> T) - {b}) homeomorphic p"
proof -
  have "a \<noteq> b" using assms by auto
  then have inj: "inj (\<lambda>x::'a. x /\<^sub>R norm (a - b))"
    by (simp add: inj_on_def)
  have "((sphere a r \<inter> T) - {b}) homeomorphic
        op+ (-a) ` ((sphere a r \<inter> T) - {b})"
    by (rule homeomorphic_translation)
  also have "... homeomorphic op *\<^sub>R (inverse r) ` op + (- a) ` (sphere a r \<inter> T - {b})"
    by (metis \<open>0 < r\<close> homeomorphic_scaling inverse_inverse_eq inverse_zero less_irrefl)
  also have "... = sphere 0 1 \<inter> (op *\<^sub>R (inverse r) ` op + (- a) ` T) - {(b - a) /\<^sub>R r}"
    using assms by (auto simp: dist_norm norm_minus_commute divide_simps)
  also have "... homeomorphic p"
    apply (rule homeomorphic_punctured_affine_sphere_affine_01)
    using assms
    apply (auto simp: dist_norm norm_minus_commute affine_scaling affine_translation [symmetric] aff_dim_translation_eq inj)
    done
  finally show ?thesis .
qed

proposition homeomorphic_punctured_sphere_affine_gen:
  fixes a :: "'a :: euclidean_space"
  assumes "convex S" "bounded S" and a: "a \<in> rel_frontier S"
      and "affine T" and affS: "aff_dim S = aff_dim T + 1"
    shows "rel_frontier S - {a} homeomorphic T"
proof -
  have "S \<noteq> {}" using assms by auto
  obtain U :: "'a set" where "affine U" and affdS: "aff_dim U = aff_dim S"
    using choose_affine_subset [OF affine_UNIV aff_dim_geq]
    by (meson aff_dim_affine_hull affine_affine_hull)
  have "convex U"
    by (simp add: affine_imp_convex \<open>affine U\<close>)
  have "U \<noteq> {}"
    by (metis \<open>S \<noteq> {}\<close> \<open>aff_dim U = aff_dim S\<close> aff_dim_empty)
  then obtain z where "z \<in> U"
    by auto
  then have bne: "ball z 1 \<inter> U \<noteq> {}" by force
  have [simp]: "aff_dim(ball z 1 \<inter> U) = aff_dim U"
    using aff_dim_convex_Int_open [OF \<open>convex U\<close> open_ball] bne
    by (fastforce simp add: Int_commute)
  have "rel_frontier S homeomorphic rel_frontier (ball z 1 \<inter> U)"
    apply (rule homeomorphic_rel_frontiers_convex_bounded_sets)
    apply (auto simp: \<open>affine U\<close> affine_imp_convex convex_Int affdS assms)
    done
  also have "... = sphere z 1 \<inter> U"
    using convex_affine_rel_frontier_Int [of "ball z 1" U]
    by (simp add: \<open>affine U\<close> bne)
  finally obtain h k where him: "h ` rel_frontier S = sphere z 1 \<inter> U"
                    and kim: "k ` (sphere z 1 \<inter> U) = rel_frontier S"
                    and hcon: "continuous_on (rel_frontier S) h"
                    and kcon: "continuous_on (sphere z 1 \<inter> U) k"
                    and kh:  "\<And>x. x \<in> rel_frontier S \<Longrightarrow> k(h(x)) = x"
                    and hk:  "\<And>y. y \<in> sphere z 1 \<inter> U \<Longrightarrow> h(k(y)) = y"
    unfolding homeomorphic_def homeomorphism_def by auto
  have "rel_frontier S - {a} homeomorphic (sphere z 1 \<inter> U) - {h a}"
  proof (rule homeomorphicI [where f=h and g=k])
    show h: "h ` (rel_frontier S - {a}) = sphere z 1 \<inter> U - {h a}"
      using him a kh by auto metis
    show "k ` (sphere z 1 \<inter> U - {h a}) = rel_frontier S - {a}"
      by (force simp: h [symmetric] image_comp o_def kh)
  qed (auto intro: continuous_on_subset hcon kcon simp: kh hk)
  also have "... homeomorphic T"
    apply (rule homeomorphic_punctured_affine_sphere_affine)
    using a him
    by (auto simp: affS affdS \<open>affine T\<close>  \<open>affine U\<close> \<open>z \<in> U\<close>)
  finally show ?thesis .
qed


lemma homeomorphic_punctured_sphere_affine:
  fixes a :: "'a :: euclidean_space"
  assumes "0 < r" and b: "b \<in> sphere a r"
      and "affine T" and affS: "aff_dim T + 1 = DIM('a)"
    shows "(sphere a r - {b}) homeomorphic T"
using homeomorphic_punctured_sphere_affine_gen [of "cball a r" b T]
  assms aff_dim_cball by force

corollary homeomorphic_punctured_sphere_hyperplane:
  fixes a :: "'a :: euclidean_space"
  assumes "0 < r" and b: "b \<in> sphere a r"
      and "c \<noteq> 0"
    shows "(sphere a r - {b}) homeomorphic {x::'a. c \<bullet> x = d}"
apply (rule homeomorphic_punctured_sphere_affine)
using assms
apply (auto simp: affine_hyperplane of_nat_diff)
done


text\<open> When dealing with AR, ANR and ANR later, it's useful to know that every set
  is homeomorphic to a closed subset of a convex set, and
  if the set is locally compact we can take the convex set to be the universe.\<close>

proposition homeomorphic_closedin_convex:
  fixes S :: "'m::euclidean_space set"
  assumes "aff_dim S < DIM('n)"
  obtains U and T :: "'n::euclidean_space set"
     where "convex U" "U \<noteq> {}" "closedin (subtopology euclidean U) T"
           "S homeomorphic T"
proof (cases "S = {}")
  case True then show ?thesis
    by (rule_tac U=UNIV and T="{}" in that) auto
next
  case False
  then obtain a where "a \<in> S" by auto
  obtain i::'n where i: "i \<in> Basis" "i \<noteq> 0"
    using SOME_Basis Basis_zero by force
  have "0 \<in> affine hull (op + (- a) ` S)"
    by (simp add: \<open>a \<in> S\<close> hull_inc)
  then have "dim (op + (- a) ` S) = aff_dim (op + (- a) ` S)"
    by (simp add: aff_dim_zero)
  also have "... < DIM('n)"
    by (simp add: aff_dim_translation_eq assms)
  finally have dd: "dim (op + (- a) ` S) < DIM('n)"
    by linarith
  obtain T where "subspace T" and Tsub: "T \<subseteq> {x. i \<bullet> x = 0}"
             and dimT: "dim T = dim (op + (- a) ` S)"
    apply (rule choose_subspace_of_subspace [of "dim (op + (- a) ` S)" "{x::'n. i \<bullet> x = 0}"])
     apply (simp add: dim_hyperplane [OF \<open>i \<noteq> 0\<close>])
     apply (metis DIM_positive Suc_pred dd not_le not_less_eq_eq)
    apply (metis span_eq subspace_hyperplane)
    done
  have "subspace (span (op + (- a) ` S))"
    using subspace_span by blast
  then obtain h k where "linear h" "linear k"
               and heq: "h ` span (op + (- a) ` S) = T"
               and keq:"k ` T = span (op + (- a) ` S)"
               and hinv [simp]:  "\<And>x. x \<in> span (op + (- a) ` S) \<Longrightarrow> k(h x) = x"
               and kinv [simp]:  "\<And>x. x \<in> T \<Longrightarrow> h(k x) = x"
    apply (rule isometries_subspaces [OF _ \<open>subspace T\<close>])
    apply (auto simp: dimT)
    done
  have hcont: "continuous_on A h" and kcont: "continuous_on B k" for A B
    using \<open>linear h\<close> \<open>linear k\<close> linear_continuous_on linear_conv_bounded_linear by blast+
  have ihhhh[simp]: "\<And>x. x \<in> S \<Longrightarrow> i \<bullet> h (x - a) = 0"
    using Tsub [THEN subsetD] heq span_inc by fastforce
  have "sphere 0 1 - {i} homeomorphic {x. i \<bullet> x = 0}"
    apply (rule homeomorphic_punctured_sphere_affine)
    using i
    apply (auto simp: affine_hyperplane)
    by (metis DIM_positive Suc_eq_plus1 add.left_neutral diff_add_cancel not_le not_less_eq_eq of_nat_1 of_nat_diff)
  then obtain f g where fg: "homeomorphism (sphere 0 1 - {i}) {x. i \<bullet> x = 0} f g"
    by (force simp: homeomorphic_def)
  have "h ` op + (- a) ` S \<subseteq> T"
    using heq span_clauses(1) span_linear_image by blast
  then have "g ` h ` op + (- a) ` S \<subseteq> g ` {x. i \<bullet> x = 0}"
    using Tsub by (simp add: image_mono)
  also have "... \<subseteq> sphere 0 1 - {i}"
    by (simp add: fg [unfolded homeomorphism_def])
  finally have gh_sub_sph: "(g \<circ> h) ` op + (- a) ` S \<subseteq> sphere 0 1 - {i}"
    by (metis image_comp)
  then have gh_sub_cb: "(g \<circ> h) ` op + (- a) ` S \<subseteq> cball 0 1"
    by (metis Diff_subset order_trans sphere_cball)
  have [simp]: "\<And>u. u \<in> S \<Longrightarrow> norm (g (h (u - a))) = 1"
    using gh_sub_sph [THEN subsetD] by (auto simp: o_def)
  have ghcont: "continuous_on (op + (- a) ` S) (\<lambda>x. g (h x))"
    apply (rule continuous_on_compose2 [OF homeomorphism_cont2 [OF fg] hcont], force)
    done
  have kfcont: "continuous_on ((g \<circ> h \<circ> op + (- a)) ` S) (\<lambda>x. k (f x))"
    apply (rule continuous_on_compose2 [OF kcont])
    using homeomorphism_cont1 [OF fg] gh_sub_sph apply (force intro: continuous_on_subset, blast)
    done
  have "S homeomorphic op + (- a) ` S"
    by (simp add: homeomorphic_translation)
  also have Shom: "\<dots> homeomorphic (g \<circ> h) ` op + (- a) ` S"
    apply (simp add: homeomorphic_def homeomorphism_def)
    apply (rule_tac x="g \<circ> h" in exI)
    apply (rule_tac x="k \<circ> f" in exI)
    apply (auto simp: ghcont kfcont span_clauses(1) homeomorphism_apply2 [OF fg] image_comp)
    apply (force simp: o_def homeomorphism_apply2 [OF fg] span_clauses(1))
    done
  finally have Shom: "S homeomorphic (g \<circ> h) ` op + (- a) ` S" .
  show ?thesis
    apply (rule_tac U = "ball 0 1 \<union> image (g o h) (op + (- a) ` S)"
                and T = "image (g o h) (op + (- a) ` S)"
                    in that)
    apply (rule convex_intermediate_ball [of 0 1], force)
    using gh_sub_cb apply force
    apply force
    apply (simp add: closedin_closed)
    apply (rule_tac x="sphere 0 1" in exI)
    apply (auto simp: Shom)
    done
qed

subsection\<open>Locally compact sets in an open set\<close>

text\<open> Locally compact sets are closed in an open set and are homeomorphic
  to an absolutely closed set if we have one more dimension to play with.\<close>

lemma locally_compact_open_Int_closure:
  fixes S :: "'a :: metric_space set"
  assumes "locally compact S"
  obtains T where "open T" "S = T \<inter> closure S"
proof -
  have "\<forall>x\<in>S. \<exists>T v u. u = S \<inter> T \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> S \<and> open T \<and> compact v"
    by (metis assms locally_compact openin_open)
  then obtain t v where
        tv: "\<And>x. x \<in> S
             \<Longrightarrow> v x \<subseteq> S \<and> open (t x) \<and> compact (v x) \<and> (\<exists>u. x \<in> u \<and> u \<subseteq> v x \<and> u = S \<inter> t x)"
    by metis
  then have o: "open (UNION S t)"
    by blast
  have "S = \<Union> (v ` S)"
    using tv by blast
  also have "... = UNION S t \<inter> closure S"
  proof
    show "UNION S v \<subseteq> UNION S t \<inter> closure S"
      apply safe
       apply (metis Int_iff subsetD UN_iff tv)
      apply (simp add: closure_def rev_subsetD tv)
      done
    have "t x \<inter> closure S \<subseteq> v x" if "x \<in> S" for x
    proof -
      have "t x \<inter> closure S \<subseteq> closure (t x \<inter> S)"
        by (simp add: open_Int_closure_subset that tv)
      also have "... \<subseteq> v x"
        by (metis Int_commute closure_minimal compact_imp_closed that tv)
      finally show ?thesis .
    qed
    then show "UNION S t \<inter> closure S \<subseteq> UNION S v"
      by blast
  qed
  finally have e: "S = UNION S t \<inter> closure S" .
  show ?thesis
    by (rule that [OF o e])
qed


lemma locally_compact_closedin_open:
    fixes S :: "'a :: metric_space set"
    assumes "locally compact S"
    obtains T where "open T" "closedin (subtopology euclidean T) S"
  by (metis locally_compact_open_Int_closure [OF assms] closed_closure closedin_closed_Int)


lemma locally_compact_homeomorphism_projection_closed:
  assumes "locally compact S"
  obtains T and f :: "'a \<Rightarrow> 'a :: euclidean_space \<times> 'b :: euclidean_space"
    where "closed T" "homeomorphism S T f fst"
proof (cases "closed S")
  case True
    then show ?thesis
      apply (rule_tac T = "S \<times> {0}" and f = "\<lambda>x. (x, 0)" in that)
      apply (auto simp: closed_Times homeomorphism_def continuous_intros)
      done
next
  case False
    obtain U where "open U" and US: "U \<inter> closure S = S"
      by (metis locally_compact_open_Int_closure [OF assms])
    with False have Ucomp: "-U \<noteq> {}"
      using closure_eq by auto
    have [simp]: "closure (- U) = -U"
      by (simp add: \<open>open U\<close> closed_Compl)
    define f :: "'a \<Rightarrow> 'a \<times> 'b" where "f \<equiv> \<lambda>x. (x, One /\<^sub>R setdist {x} (- U))"
    have "continuous_on U (\<lambda>x. (x, One /\<^sub>R setdist {x} (- U)))"
      apply (intro continuous_intros continuous_on_setdist)
      by (simp add: Ucomp setdist_eq_0_sing_1)
    then have homU: "homeomorphism U (f`U) f fst"
      by (auto simp: f_def homeomorphism_def image_iff continuous_intros)
    have cloS: "closedin (subtopology euclidean U) S"
      by (metis US closed_closure closedin_closed_Int)
    have cont: "isCont ((\<lambda>x. setdist {x} (- U)) o fst) z" for z :: "'a \<times> 'b"
      by (rule isCont_o continuous_intros continuous_at_setdist)+
    have setdist1D: "setdist {a} (- U) *\<^sub>R b = One \<Longrightarrow> setdist {a} (- U) \<noteq> 0" for a::'a and b::'b
      by force
    have *: "r *\<^sub>R b = One \<Longrightarrow> b = (1 / r) *\<^sub>R One" for r and b::'b
      by (metis One_non_0 nonzero_divide_eq_eq real_vector.scale_eq_0_iff real_vector.scale_scale scaleR_one)
    have "f ` U = {z. (setdist {fst z} (- U) *\<^sub>R snd z) \<in> {One}}"
      apply (auto simp: f_def setdist_eq_0_sing_1 field_simps Ucomp)
      apply (rule_tac x=a in image_eqI)
      apply (auto simp: * setdist_eq_0_sing_1 dest: setdist1D)
      done
    then have clfU: "closed (f ` U)"
      apply (rule ssubst)
      apply (rule continuous_closed_preimage_univ)
      apply (auto intro: continuous_intros cont [unfolded o_def])
      done
    have "closed (f ` S)"
       apply (rule closedin_closed_trans [OF _ clfU])
       apply (rule homeomorphism_imp_closed_map [OF homU cloS])
       done
    then show ?thesis
      apply (rule that)
      apply (rule homeomorphism_of_subsets [OF homU])
      using US apply auto
      done
qed

lemma locally_compact_closed_Int_open:
  fixes S :: "'a :: euclidean_space set"
  shows
    "locally compact S \<longleftrightarrow> (\<exists>U u. closed U \<and> open u \<and> S = U \<inter> u)"
by (metis closed_closure closed_imp_locally_compact inf_commute locally_compact_Int locally_compact_open_Int_closure open_imp_locally_compact)


proposition locally_compact_homeomorphic_closed:
  fixes S :: "'a::euclidean_space set"
  assumes "locally compact S" and dimlt: "DIM('a) < DIM('b)"
  obtains T :: "'b::euclidean_space set" where "closed T" "S homeomorphic T"
proof -
  obtain U:: "('a*real)set" and h
    where "closed U" and homU: "homeomorphism S U h fst"
    using locally_compact_homeomorphism_projection_closed assms by metis
  let ?BP = "Basis :: ('a*real) set"
  have "DIM('a * real) \<le> DIM('b)"
    by (simp add: Suc_leI dimlt)
  then obtain basf :: "'a*real \<Rightarrow> 'b" where surbf: "basf ` ?BP \<subseteq> Basis" and injbf: "inj_on basf Basis"
    by (metis finite_Basis card_le_inj)
  define basg:: "'b \<Rightarrow> 'a * real" where
    "basg \<equiv> \<lambda>i. inv_into Basis basf i"
  have bgf[simp]: "basg (basf i) = i" if "i \<in> Basis" for i
    using inv_into_f_f injbf that by (force simp: basg_def)
  define f :: "'a*real \<Rightarrow> 'b" where "f \<equiv> \<lambda>u. \<Sum>j\<in>Basis. (u \<bullet> basg j) *\<^sub>R j"
  have "linear f"
    unfolding f_def
    apply (intro linear_compose_setsum linearI ballI)
    apply (auto simp: algebra_simps)
    done
  define g :: "'b \<Rightarrow> 'a*real" where "g \<equiv> \<lambda>z. (\<Sum>i\<in>Basis. (z \<bullet> basf i) *\<^sub>R i)"
  have "linear g"
    unfolding g_def
    apply (intro linear_compose_setsum linearI ballI)
    apply (auto simp: algebra_simps)
    done
  have *: "(\<Sum>a \<in> Basis. a \<bullet> basf b * (x \<bullet> basg a)) = x \<bullet> b" if "b \<in> Basis" for x b
    using surbf that by auto
  have gf[simp]: "g (f x) = x" for x
    apply (rule euclidean_eqI)
    apply (simp add: f_def g_def inner_setsum_left scaleR_setsum_left algebra_simps)
    apply (simp add: Groups_Big.setsum_right_distrib [symmetric] *)
    done
  then have "inj f" by (metis injI)
  have gfU: "g ` f ` U = U"
    by (rule set_eqI) (auto simp: image_def)
  have "S homeomorphic U"
    using homU homeomorphic_def by blast
  also have "... homeomorphic f ` U"
    apply (rule homeomorphicI [OF refl gfU])
       apply (meson \<open>inj f\<close> \<open>linear f\<close> homeomorphism_cont2 linear_homeomorphism_image)
      using \<open>linear g\<close> linear_continuous_on linear_conv_bounded_linear apply blast
     apply auto
     done
  finally show ?thesis
    apply (rule_tac T = "f ` U" in that)
    apply (rule closed_injective_linear_image [OF \<open>closed U\<close> \<open>linear f\<close> \<open>inj f\<close>], assumption)
    done
qed


lemma homeomorphic_convex_compact_lemma:
  fixes s :: "'a::euclidean_space set"
  assumes "convex s"
    and "compact s"
    and "cball 0 1 \<subseteq> s"
  shows "s homeomorphic (cball (0::'a) 1)"
proof (rule starlike_compact_projective_special[OF assms(2-3)])
  fix x u
  assume "x \<in> s" and "0 \<le> u" and "u < (1::real)"
  have "open (ball (u *\<^sub>R x) (1 - u))"
    by (rule open_ball)
  moreover have "u *\<^sub>R x \<in> ball (u *\<^sub>R x) (1 - u)"
    unfolding centre_in_ball using \<open>u < 1\<close> by simp
  moreover have "ball (u *\<^sub>R x) (1 - u) \<subseteq> s"
  proof
    fix y
    assume "y \<in> ball (u *\<^sub>R x) (1 - u)"
    then have "dist (u *\<^sub>R x) y < 1 - u"
      unfolding mem_ball .
    with \<open>u < 1\<close> have "inverse (1 - u) *\<^sub>R (y - u *\<^sub>R x) \<in> cball 0 1"
      by (simp add: dist_norm inverse_eq_divide norm_minus_commute)
    with assms(3) have "inverse (1 - u) *\<^sub>R (y - u *\<^sub>R x) \<in> s" ..
    with assms(1) have "(1 - u) *\<^sub>R ((y - u *\<^sub>R x) /\<^sub>R (1 - u)) + u *\<^sub>R x \<in> s"
      using \<open>x \<in> s\<close> \<open>0 \<le> u\<close> \<open>u < 1\<close> [THEN less_imp_le] by (rule convexD_alt)
    then show "y \<in> s" using \<open>u < 1\<close>
      by simp
  qed
  ultimately have "u *\<^sub>R x \<in> interior s" ..
  then show "u *\<^sub>R x \<in> s - frontier s"
    using frontier_def and interior_subset by auto
qed

proposition homeomorphic_convex_compact_cball:
  fixes e :: real
    and s :: "'a::euclidean_space set"
  assumes "convex s"
    and "compact s"
    and "interior s \<noteq> {}"
    and "e > 0"
  shows "s homeomorphic (cball (b::'a) e)"
proof -
  obtain a where "a \<in> interior s"
    using assms(3) by auto
  then obtain d where "d > 0" and d: "cball a d \<subseteq> s"
    unfolding mem_interior_cball by auto
  let ?d = "inverse d" and ?n = "0::'a"
  have "cball ?n 1 \<subseteq> (\<lambda>x. inverse d *\<^sub>R (x - a)) ` s"
    apply rule
    apply (rule_tac x="d *\<^sub>R x + a" in image_eqI)
    defer
    apply (rule d[unfolded subset_eq, rule_format])
    using \<open>d > 0\<close>
    unfolding mem_cball dist_norm
    apply (auto simp add: mult_right_le_one_le)
    done
  then have "(\<lambda>x. inverse d *\<^sub>R (x - a)) ` s homeomorphic cball ?n 1"
    using homeomorphic_convex_compact_lemma[of "(\<lambda>x. ?d *\<^sub>R -a + ?d *\<^sub>R x) ` s",
      OF convex_affinity compact_affinity]
    using assms(1,2)
    by (auto simp add: scaleR_right_diff_distrib)
  then show ?thesis
    apply (rule_tac homeomorphic_trans[OF _ homeomorphic_balls(2)[of 1 _ ?n]])
    apply (rule homeomorphic_trans[OF homeomorphic_affinity[of "?d" s "?d *\<^sub>R -a"]])
    using \<open>d>0\<close> \<open>e>0\<close>
    apply (auto simp add: scaleR_right_diff_distrib)
    done
qed

corollary homeomorphic_convex_compact:
  fixes s :: "'a::euclidean_space set"
    and t :: "'a set"
  assumes "convex s" "compact s" "interior s \<noteq> {}"
    and "convex t" "compact t" "interior t \<noteq> {}"
  shows "s homeomorphic t"
  using assms
  by (meson zero_less_one homeomorphic_trans homeomorphic_convex_compact_cball homeomorphic_sym)

subsection\<open>Covering spaces and lifting results for them\<close>

definition covering_space
           :: "'a::topological_space set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b::topological_space set \<Rightarrow> bool"
  where
  "covering_space c p s \<equiv>
       continuous_on c p \<and> p ` c = s \<and>
       (\<forall>x \<in> s. \<exists>t. x \<in> t \<and> openin (subtopology euclidean s) t \<and>
                    (\<exists>v. \<Union>v = {x. x \<in> c \<and> p x \<in> t} \<and>
                        (\<forall>u \<in> v. openin (subtopology euclidean c) u) \<and>
                        pairwise disjnt v \<and>
                        (\<forall>u \<in> v. \<exists>q. homeomorphism u t p q)))"

lemma covering_space_imp_continuous: "covering_space c p s \<Longrightarrow> continuous_on c p"
  by (simp add: covering_space_def)

lemma covering_space_imp_surjective: "covering_space c p s \<Longrightarrow> p ` c = s"
  by (simp add: covering_space_def)

lemma homeomorphism_imp_covering_space: "homeomorphism s t f g \<Longrightarrow> covering_space s f t"
  apply (simp add: homeomorphism_def covering_space_def, clarify)
  apply (rule_tac x=t in exI, simp)
  apply (rule_tac x="{s}" in exI, auto)
  done

lemma covering_space_local_homeomorphism:
  assumes "covering_space c p s" "x \<in> c"
  obtains t u q where "x \<in> t" "openin (subtopology euclidean c) t"
                      "p x \<in> u" "openin (subtopology euclidean s) u"
                      "homeomorphism t u p q"
using assms
apply (simp add: covering_space_def, clarify)
apply (drule_tac x="p x" in bspec, force)
by (metis (no_types, lifting) Union_iff mem_Collect_eq)


lemma covering_space_local_homeomorphism_alt:
  assumes p: "covering_space c p s" and "y \<in> s"
  obtains x t u q where "p x = y"
                        "x \<in> t" "openin (subtopology euclidean c) t"
                        "y \<in> u" "openin (subtopology euclidean s) u"
                          "homeomorphism t u p q"
proof -
  obtain x where "p x = y" "x \<in> c"
    using assms covering_space_imp_surjective by blast
  show ?thesis
    apply (rule covering_space_local_homeomorphism [OF p \<open>x \<in> c\<close>])
    using that \<open>p x = y\<close> by blast
qed

proposition covering_space_open_map:
  fixes s :: "'a :: metric_space set" and t :: "'b :: metric_space set"
  assumes p: "covering_space c p s" and t: "openin (subtopology euclidean c) t"
    shows "openin (subtopology euclidean s) (p ` t)"
proof -
  have pce: "p ` c = s"
   and covs:
       "\<And>x. x \<in> s \<Longrightarrow>
            \<exists>X VS. x \<in> X \<and> openin (subtopology euclidean s) X \<and>
                  \<Union>VS = {x. x \<in> c \<and> p x \<in> X} \<and>
                  (\<forall>u \<in> VS. openin (subtopology euclidean c) u) \<and>
                  pairwise disjnt VS \<and>
                  (\<forall>u \<in> VS. \<exists>q. homeomorphism u X p q)"
    using p by (auto simp: covering_space_def)
  have "t \<subseteq> c"  by (metis openin_euclidean_subtopology_iff t)
  have "\<exists>T. openin (subtopology euclidean s) T \<and> y \<in> T \<and> T \<subseteq> p ` t"
          if "y \<in> p ` t" for y
  proof -
    have "y \<in> s" using \<open>t \<subseteq> c\<close> pce that by blast
    obtain U VS where "y \<in> U" and U: "openin (subtopology euclidean s) U"
                  and VS: "\<Union>VS = {x. x \<in> c \<and> p x \<in> U}"
                  and openVS: "\<forall>V \<in> VS. openin (subtopology euclidean c) V"
                  and homVS: "\<And>V. V \<in> VS \<Longrightarrow> \<exists>q. homeomorphism V U p q"
      using covs [OF \<open>y \<in> s\<close>] by auto
    obtain x where "x \<in> c" "p x \<in> U" "x \<in> t" "p x = y"
      apply simp
      using t [unfolded openin_euclidean_subtopology_iff] \<open>y \<in> U\<close> \<open>y \<in> p ` t\<close> by blast
    with VS obtain V where "x \<in> V" "V \<in> VS" by auto
    then obtain q where q: "homeomorphism V U p q" using homVS by blast
    then have ptV: "p ` (t \<inter> V) = U \<inter> {z. q z \<in> (t \<inter> V)}"
      using VS \<open>V \<in> VS\<close> by (auto simp: homeomorphism_def)
    have ocv: "openin (subtopology euclidean c) V"
      by (simp add: \<open>V \<in> VS\<close> openVS)
    have "openin (subtopology euclidean U) {z \<in> U. q z \<in> t \<inter> V}"
      apply (rule continuous_on_open [THEN iffD1, rule_format])
       using homeomorphism_def q apply blast
      using openin_subtopology_Int_subset [of c] q t unfolding homeomorphism_def
      by (metis inf.absorb_iff2 Int_commute ocv openin_euclidean_subtopology_iff)
    then have os: "openin (subtopology euclidean s) (U \<inter> {z. q z \<in> t \<inter> V})"
      using openin_trans [of U] by (simp add: Collect_conj_eq U)
    show ?thesis
      apply (rule_tac x = "p ` (t \<inter> V)" in exI)
      apply (rule conjI)
      apply (simp only: ptV os)
      using \<open>p x = y\<close> \<open>x \<in> V\<close> \<open>x \<in> t\<close> apply blast
      done
  qed
  with openin_subopen show ?thesis by blast
qed

lemma covering_space_lift_unique_gen:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  fixes g1 :: "'a \<Rightarrow> 'c::real_normed_vector"
  assumes cov: "covering_space c p s"
      and eq: "g1 a = g2 a"
      and f: "continuous_on t f"  "f ` t \<subseteq> s"
      and g1: "continuous_on t g1"  "g1 ` t \<subseteq> c"
      and fg1: "\<And>x. x \<in> t \<Longrightarrow> f x = p(g1 x)"
      and g2: "continuous_on t g2"  "g2 ` t \<subseteq> c"
      and fg2: "\<And>x. x \<in> t \<Longrightarrow> f x = p(g2 x)"
      and u_compt: "u \<in> components t" and "a \<in> u" "x \<in> u"
    shows "g1 x = g2 x"
proof -
  have "u \<subseteq> t" by (rule in_components_subset [OF u_compt])
  def G12 \<equiv> "{x \<in> u. g1 x - g2 x = 0}"
  have "connected u" by (rule in_components_connected [OF u_compt])
  have contu: "continuous_on u g1" "continuous_on u g2"
       using \<open>u \<subseteq> t\<close> continuous_on_subset g1 g2 by blast+
  have o12: "openin (subtopology euclidean u) G12"
  unfolding G12_def
  proof (subst openin_subopen, clarify)
    fix z
    assume z: "z \<in> u" "g1 z - g2 z = 0"
    obtain v w q where "g1 z \<in> v" and ocv: "openin (subtopology euclidean c) v"
                   and "p (g1 z) \<in> w" and osw: "openin (subtopology euclidean s) w"
                   and hom: "homeomorphism v w p q"
      apply (rule_tac x = "g1 z" in covering_space_local_homeomorphism [OF cov])
       using \<open>u \<subseteq> t\<close> \<open>z \<in> u\<close> g1(2) apply blast+
      done
    have "g2 z \<in> v" using \<open>g1 z \<in> v\<close> z by auto
    have gg: "{x \<in> u. g x \<in> v} = {x \<in> u. g x \<in> (v \<inter> g ` u)}" for g
      by auto
    have "openin (subtopology euclidean (g1 ` u)) (v \<inter> g1 ` u)"
      using ocv \<open>u \<subseteq> t\<close> g1 by (fastforce simp add: openin_open)
    then have 1: "openin (subtopology euclidean u) {x \<in> u. g1 x \<in> v}"
      unfolding gg by (blast intro: contu continuous_on_open [THEN iffD1, rule_format])
    have "openin (subtopology euclidean (g2 ` u)) (v \<inter> g2 ` u)"
      using ocv \<open>u \<subseteq> t\<close> g2 by (fastforce simp add: openin_open)
    then have 2: "openin (subtopology euclidean u) {x \<in> u. g2 x \<in> v}"
      unfolding gg by (blast intro: contu continuous_on_open [THEN iffD1, rule_format])
    show "\<exists>T. openin (subtopology euclidean u) T \<and>
              z \<in> T \<and> T \<subseteq> {z \<in> u. g1 z - g2 z = 0}"
      using z
      apply (rule_tac x = "{x. x \<in> u \<and> g1 x \<in> v} \<inter> {x. x \<in> u \<and> g2 x \<in> v}" in exI)
      apply (intro conjI)
      apply (rule openin_Int [OF 1 2])
      using \<open>g1 z \<in> v\<close>  \<open>g2 z \<in> v\<close>  apply (force simp:, clarify)
      apply (metis \<open>u \<subseteq> t\<close> subsetD eq_iff_diff_eq_0 fg1 fg2 hom homeomorphism_def)
      done
  qed
  have c12: "closedin (subtopology euclidean u) G12"
    unfolding G12_def
    by (intro continuous_intros continuous_closedin_preimage_constant contu)
  have "G12 = {} \<or> G12 = u"
    by (intro connected_clopen [THEN iffD1, rule_format] \<open>connected u\<close> conjI o12 c12)
  with eq \<open>a \<in> u\<close> have "\<And>x. x \<in> u \<Longrightarrow> g1 x - g2 x = 0" by (auto simp: G12_def)
  then show ?thesis
    using \<open>x \<in> u\<close> by force
qed

proposition covering_space_lift_unique:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  fixes g1 :: "'a \<Rightarrow> 'c::real_normed_vector"
  assumes "covering_space c p s"
          "g1 a = g2 a"
          "continuous_on t f"  "f ` t \<subseteq> s"
          "continuous_on t g1"  "g1 ` t \<subseteq> c"  "\<And>x. x \<in> t \<Longrightarrow> f x = p(g1 x)"
          "continuous_on t g2"  "g2 ` t \<subseteq> c"  "\<And>x. x \<in> t \<Longrightarrow> f x = p(g2 x)"
          "connected t"  "a \<in> t"   "x \<in> t"
   shows "g1 x = g2 x"
using covering_space_lift_unique_gen [of c p s] in_components_self assms ex_in_conv by blast

end
