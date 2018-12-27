(*  Title:      HOL/Analysis/Homeomorphism.thy
    Author: LC Paulson (ported from HOL Light)
*)

section%important \<open>Homeomorphism Theorems\<close>

theory Homeomorphism
imports Path_Connected
begin

lemma%unimportant homeomorphic_spheres':
  fixes a ::"'a::euclidean_space" and b ::"'b::euclidean_space"
  assumes "0 < \<delta>" and dimeq: "DIM('a) = DIM('b)"
  shows "(sphere a \<delta>) homeomorphic (sphere b \<delta>)"
proof -
  obtain f :: "'a\<Rightarrow>'b" and g where "linear f" "linear g"
     and fg: "\<And>x. norm(f x) = norm x" "\<And>y. norm(g y) = norm y" "\<And>x. g(f x) = x" "\<And>y. f(g y) = y"
    by (blast intro: isomorphisms_UNIV_UNIV [OF dimeq])
  then have "continuous_on UNIV f" "continuous_on UNIV g"
    using linear_continuous_on linear_linear by blast+
  then show ?thesis
    unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + f(x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + g(x - b)" in exI)
    using assms
    apply (force intro: continuous_intros
                  continuous_on_compose2 [of _ f] continuous_on_compose2 [of _ g] simp: dist_commute dist_norm fg)
    done
qed

lemma%unimportant homeomorphic_spheres_gen:
    fixes a :: "'a::euclidean_space" and b :: "'b::euclidean_space"
  assumes "0 < r" "0 < s" "DIM('a::euclidean_space) = DIM('b::euclidean_space)"
  shows "(sphere a r homeomorphic sphere b s)"
  apply (rule homeomorphic_trans [OF homeomorphic_spheres homeomorphic_spheres'])
  using assms  apply auto
  done

subsection%important \<open>Homeomorphism of all convex compact sets with nonempty interior\<close>

proposition%important ray_to_rel_frontier:
  fixes a :: "'a::real_inner"
  assumes "bounded S"
      and a: "a \<in> rel_interior S"
      and aff: "(a + l) \<in> affine hull S"
      and "l \<noteq> 0"
  obtains d where "0 < d" "(a + d *\<^sub>R l) \<in> rel_frontier S"
           "\<And>e. \<lbrakk>0 \<le> e; e < d\<rbrakk> \<Longrightarrow> (a + e *\<^sub>R l) \<in> rel_interior S"
proof%unimportant -
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

corollary%important ray_to_frontier:
  fixes a :: "'a::euclidean_space"
  assumes "bounded S"
      and a: "a \<in> interior S"
      and "l \<noteq> 0"
  obtains d where "0 < d" "(a + d *\<^sub>R l) \<in> frontier S"
           "\<And>e. \<lbrakk>0 \<le> e; e < d\<rbrakk> \<Longrightarrow> (a + e *\<^sub>R l) \<in> interior S"
proof%unimportant -
  have "interior S = rel_interior S"
    using a rel_interior_nonempty_interior by auto
  then have "a \<in> rel_interior S"
    using a by simp
  then show ?thesis
    apply (rule ray_to_rel_frontier [OF \<open>bounded S\<close> _ _ \<open>l \<noteq> 0\<close>])
     using a affine_hull_nonempty_interior apply blast
    by (simp add: \<open>interior S = rel_interior S\<close> frontier_def rel_frontier_def that)
qed


lemma%unimportant segment_to_rel_frontier_aux:
  fixes x :: "'a::euclidean_space"
  assumes "convex S" "bounded S" and x: "x \<in> rel_interior S" and y: "y \<in> S" and xy: "x \<noteq> y"
  obtains z where "z \<in> rel_frontier S" "y \<in> closed_segment x z"
                   "open_segment x z \<subseteq> rel_interior S"
proof -
  have "x + (y - x) \<in> affine hull S"
    using hull_inc [OF y] by auto
  then obtain d where "0 < d" and df: "(x + d *\<^sub>R (y-x)) \<in> rel_frontier S"
                  and di: "\<And>e. \<lbrakk>0 \<le> e; e < d\<rbrakk> \<Longrightarrow> (x + e *\<^sub>R (y-x)) \<in> rel_interior S"
    by (rule ray_to_rel_frontier [OF \<open>bounded S\<close> x]) (use xy in auto)
  show ?thesis
  proof
    show "x + d *\<^sub>R (y - x) \<in> rel_frontier S"
      by (simp add: df)
  next
    have "open_segment x y \<subseteq> rel_interior S"
      using rel_interior_closure_convex_segment [OF \<open>convex S\<close> x] closure_subset y by blast
    moreover have "x + d *\<^sub>R (y - x) \<in> open_segment x y" if "d < 1"
      using xy
      apply (auto simp: in_segment)
      apply (rule_tac x="d" in exI)
      using \<open>0 < d\<close> that apply (auto simp: divide_simps algebra_simps)
      done
    ultimately have "1 \<le> d"
      using df rel_frontier_def by fastforce
    moreover have "x = (1 / d) *\<^sub>R x + ((d - 1) / d) *\<^sub>R x"
      by (metis \<open>0 < d\<close> add.commute add_divide_distrib diff_add_cancel divide_self_if less_irrefl scaleR_add_left scaleR_one)
    ultimately show "y \<in> closed_segment x (x + d *\<^sub>R (y - x))"
      apply (auto simp: in_segment)
      apply (rule_tac x="1/d" in exI)
      apply (auto simp: divide_simps algebra_simps)
      done
  next
    show "open_segment x (x + d *\<^sub>R (y - x)) \<subseteq> rel_interior S"
      apply (rule rel_interior_closure_convex_segment [OF \<open>convex S\<close> x])
      using df rel_frontier_def by auto
  qed
qed

lemma%unimportant segment_to_rel_frontier:
  fixes x :: "'a::euclidean_space"
  assumes S: "convex S" "bounded S" and x: "x \<in> rel_interior S"
      and y: "y \<in> S" and xy: "\<not>(x = y \<and> S = {x})"
  obtains z where "z \<in> rel_frontier S" "y \<in> closed_segment x z"
                  "open_segment x z \<subseteq> rel_interior S"
proof (cases "x=y")
  case True
  with xy have "S \<noteq> {x}"
    by blast
  with True show ?thesis
    by (metis Set.set_insert all_not_in_conv ends_in_segment(1) insert_iff segment_to_rel_frontier_aux[OF S x] that y)
next
  case False
  then show ?thesis
    using segment_to_rel_frontier_aux [OF S x y] that by blast
qed

proposition%important rel_frontier_not_sing:
  fixes a :: "'a::euclidean_space"
  assumes "bounded S"
    shows "rel_frontier S \<noteq> {a}"
proof%unimportant (cases "S = {}")
  case True  then show ?thesis  by simp
next
  case False
  then obtain z where "z \<in> S"
    by blast
  then show ?thesis
  proof (cases "S = {z}")
    case True then show ?thesis  by simp
  next
    case False
    then obtain w where "w \<in> S" "w \<noteq> z"
      using \<open>z \<in> S\<close> by blast
    show ?thesis
    proof
      assume "rel_frontier S = {a}"
      then consider "w \<notin> rel_frontier S" | "z \<notin> rel_frontier S"
        using \<open>w \<noteq> z\<close> by auto
      then show False
      proof cases
        case 1
        then have w: "w \<in> rel_interior S"
          using \<open>w \<in> S\<close> closure_subset rel_frontier_def by fastforce
        have "w + (w - z) \<in> affine hull S"
          by (metis \<open>w \<in> S\<close> \<open>z \<in> S\<close> affine_affine_hull hull_inc mem_affine_3_minus scaleR_one)
        then obtain e where "0 < e" "(w + e *\<^sub>R (w - z)) \<in> rel_frontier S"
          using \<open>w \<noteq> z\<close>  \<open>z \<in> S\<close> by (metis assms ray_to_rel_frontier right_minus_eq w)
        moreover obtain d where "0 < d" "(w + d *\<^sub>R (z - w)) \<in> rel_frontier S"
          using ray_to_rel_frontier [OF \<open>bounded S\<close> w, of "1 *\<^sub>R (z - w)"]  \<open>w \<noteq> z\<close>  \<open>z \<in> S\<close>
          by (metis add.commute add.right_neutral diff_add_cancel hull_inc scaleR_one)
        ultimately have "d *\<^sub>R (z - w) = e *\<^sub>R (w - z)"
          using \<open>rel_frontier S = {a}\<close> by force
        moreover have "e \<noteq> -d "
          using \<open>0 < e\<close> \<open>0 < d\<close> by force
        ultimately show False
          by (metis (no_types, lifting) \<open>w \<noteq> z\<close> eq_iff_diff_eq_0 minus_diff_eq real_vector.scale_cancel_right real_vector.scale_minus_right scaleR_left.minus)
      next
        case 2
        then have z: "z \<in> rel_interior S"
          using \<open>z \<in> S\<close> closure_subset rel_frontier_def by fastforce
        have "z + (z - w) \<in> affine hull S"
          by (metis \<open>z \<in> S\<close> \<open>w \<in> S\<close> affine_affine_hull hull_inc mem_affine_3_minus scaleR_one)
        then obtain e where "0 < e" "(z + e *\<^sub>R (z - w)) \<in> rel_frontier S"
          using \<open>w \<noteq> z\<close>  \<open>w \<in> S\<close> by (metis assms ray_to_rel_frontier right_minus_eq z)
        moreover obtain d where "0 < d" "(z + d *\<^sub>R (w - z)) \<in> rel_frontier S"
          using ray_to_rel_frontier [OF \<open>bounded S\<close> z, of "1 *\<^sub>R (w - z)"]  \<open>w \<noteq> z\<close>  \<open>w \<in> S\<close>
          by (metis add.commute add.right_neutral diff_add_cancel hull_inc scaleR_one)
        ultimately have "d *\<^sub>R (w - z) = e *\<^sub>R (z - w)"
          using \<open>rel_frontier S = {a}\<close> by force
        moreover have "e \<noteq> -d "
          using \<open>0 < e\<close> \<open>0 < d\<close> by force
        ultimately show False
          by (metis (no_types, lifting) \<open>w \<noteq> z\<close> eq_iff_diff_eq_0 minus_diff_eq real_vector.scale_cancel_right real_vector.scale_minus_right scaleR_left.minus)
      qed
    qed
  qed
qed

proposition%important
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and 0: "0 \<in> rel_interior S"
      and star: "\<And>x. x \<in> S \<Longrightarrow> open_segment 0 x \<subseteq> rel_interior S"
    shows starlike_compact_projective1_0:
            "S - rel_interior S homeomorphic sphere 0 1 \<inter> affine hull S"
            (is "?SMINUS homeomorphic ?SPHER")
      and starlike_compact_projective2_0:
            "S homeomorphic cball 0 1 \<inter> affine hull S"
            (is "S homeomorphic ?CBALL")
proof%unimportant -
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

corollary%important
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and a: "a \<in> rel_interior S"
      and star: "\<And>x. x \<in> S \<Longrightarrow> open_segment a x \<subseteq> rel_interior S"
    shows starlike_compact_projective1:
            "S - rel_interior S homeomorphic sphere a 1 \<inter> affine hull S"
      and starlike_compact_projective2:
            "S homeomorphic cball a 1 \<inter> affine hull S"
proof%unimportant -
  have 1: "compact ((+) (-a) ` S)" by (meson assms compact_translation)
  have 2: "0 \<in> rel_interior ((+) (-a) ` S)"
    by (simp add: a rel_interior_translation)
  have 3: "open_segment 0 x \<subseteq> rel_interior ((+) (-a) ` S)" if "x \<in> ((+) (-a) ` S)" for x
  proof -
    have "x+a \<in> S" using that by auto
    then have "open_segment a (x+a) \<subseteq> rel_interior S" by (metis star)
    then show ?thesis using open_segment_translation
      using rel_interior_translation by fastforce
  qed
  have "S - rel_interior S homeomorphic ((+) (-a) ` S) - rel_interior ((+) (-a) ` S)"
    by (metis rel_interior_translation translation_diff homeomorphic_translation)
  also have "... homeomorphic sphere 0 1 \<inter> affine hull ((+) (-a) ` S)"
    by (rule starlike_compact_projective1_0 [OF 1 2 3])
  also have "... = (+) (-a) ` (sphere a 1 \<inter> affine hull S)"
    by (metis affine_hull_translation left_minus sphere_translation translation_Int)
  also have "... homeomorphic sphere a 1 \<inter> affine hull S"
    using homeomorphic_translation homeomorphic_sym by blast
  finally show "S - rel_interior S homeomorphic sphere a 1 \<inter> affine hull S" .

  have "S homeomorphic ((+) (-a) ` S)"
    by (metis homeomorphic_translation)
  also have "... homeomorphic cball 0 1 \<inter> affine hull ((+) (-a) ` S)"
    by (rule starlike_compact_projective2_0 [OF 1 2 3])
  also have "... = (+) (-a) ` (cball a 1 \<inter> affine hull S)"
    by (metis affine_hull_translation left_minus cball_translation translation_Int)
  also have "... homeomorphic cball a 1 \<inter> affine hull S"
    using homeomorphic_translation homeomorphic_sym by blast
  finally show "S homeomorphic cball a 1 \<inter> affine hull S" .
qed

corollary%important starlike_compact_projective_special:
  assumes "compact S"
    and cb01: "cball (0::'a::euclidean_space) 1 \<subseteq> S"
    and scale: "\<And>x u. \<lbrakk>x \<in> S; 0 \<le> u; u < 1\<rbrakk> \<Longrightarrow> u *\<^sub>R x \<in> S - frontier S"
  shows "S homeomorphic (cball (0::'a::euclidean_space) 1)"
proof%unimportant -
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

lemma%important homeomorphic_convex_lemma:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "convex S" "compact S" "convex T" "compact T"
      and affeq: "aff_dim S = aff_dim T"
    shows "(S - rel_interior S) homeomorphic (T - rel_interior T) \<and>
           S homeomorphic T"
proof%unimportant (cases "rel_interior S = {} \<or> rel_interior T = {}")
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
  let ?aS = "(+) (-a) ` S" and ?bT = "(+) (-b) ` T"
  have 0: "0 \<in> affine hull ?aS" "0 \<in> affine hull ?bT"
    by (metis a b subsetD hull_inc image_eqI left_minus rel_interior_subset)+
  have subs: "subspace (span ?aS)" "subspace (span ?bT)"
    by (rule subspace_span)+
  moreover
  have "dim (span ((+) (- a) ` S)) = dim (span ((+) (- b) ` T))"
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
  also have "... homeomorphic (+) (-a) ` (cball a 1 \<inter> affine hull S)"
    by (metis homeomorphic_translation)
  also have "... = cball 0 1 \<inter> (+) (-a) ` (affine hull S)"
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
  also have "... = cball 0 1 \<inter> (+) (-b) ` (affine hull T)"
    using eqspanT affine_hull_translation by blast
  also have "... = (+) (-b) ` (cball b 1 \<inter> affine hull T)"
    by (auto simp: dist_norm)
  also have "... homeomorphic (cball b 1 \<inter> affine hull T)"
    by (metis homeomorphic_translation homeomorphic_sym)
  also have "... homeomorphic T"
    by (metis starlike_compact_projective2 [OF \<open>compact T\<close> b starT] homeomorphic_sym)
  finally have 1: "S homeomorphic T" .

  have "S - rel_interior S homeomorphic sphere a 1 \<inter> affine hull S"
    by (rule starlike_compact_projective1 [OF \<open>compact S\<close> a starS])
  also have "... homeomorphic (+) (-a) ` (sphere a 1 \<inter> affine hull S)"
    by (metis homeomorphic_translation)
  also have "... = sphere 0 1 \<inter> (+) (-a) ` (affine hull S)"
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
  also have "... = sphere 0 1 \<inter> (+) (-b) ` (affine hull T)"
    using eqspanT affine_hull_translation by blast
  also have "... = (+) (-b) ` (sphere b 1 \<inter> affine hull T)"
    by (auto simp: dist_norm)
  also have "... homeomorphic (sphere b 1 \<inter> affine hull T)"
    by (metis homeomorphic_translation homeomorphic_sym)
  also have "... homeomorphic T - rel_interior T"
    by (metis starlike_compact_projective1 [OF \<open>compact T\<close> b starT] homeomorphic_sym)
  finally have 2: "S - rel_interior S homeomorphic T - rel_interior T" .
  show ?thesis
    using 1 2 by blast
qed

lemma%unimportant homeomorphic_convex_compact_sets:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "convex S" "compact S" "convex T" "compact T"
      and affeq: "aff_dim S = aff_dim T"
    shows "S homeomorphic T"
using homeomorphic_convex_lemma [OF assms] assms
by (auto simp: rel_frontier_def)

lemma%unimportant homeomorphic_rel_frontiers_convex_bounded_sets:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "convex S" "bounded S" "convex T" "bounded T"
      and affeq: "aff_dim S = aff_dim T"
    shows  "rel_frontier S homeomorphic rel_frontier T"
using assms homeomorphic_convex_lemma [of "closure S" "closure T"]
by (simp add: rel_frontier_def convex_rel_interior_closure)


subsection%important\<open>Homeomorphisms between punctured spheres and affine sets\<close>
text\<open>Including the famous stereoscopic projection of the 3-D sphere to the complex plane\<close>

text\<open>The special case with centre 0 and radius 1\<close>
lemma%unimportant homeomorphic_punctured_affine_sphere_affine_01:
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

theorem%important homeomorphic_punctured_affine_sphere_affine:
  fixes a :: "'a :: euclidean_space"
  assumes "0 < r" "b \<in> sphere a r" "affine T" "a \<in> T" "b \<in> T" "affine p"
      and aff: "aff_dim T = aff_dim p + 1"
    shows "(sphere a r \<inter> T) - {b} homeomorphic p"
proof%unimportant -
  have "a \<noteq> b" using assms by auto
  then have inj: "inj (\<lambda>x::'a. x /\<^sub>R norm (a - b))"
    by (simp add: inj_on_def)
  have "((sphere a r \<inter> T) - {b}) homeomorphic
        (+) (-a) ` ((sphere a r \<inter> T) - {b})"
    by (rule homeomorphic_translation)
  also have "... homeomorphic (*\<^sub>R) (inverse r) ` (+) (- a) ` (sphere a r \<inter> T - {b})"
    by (metis \<open>0 < r\<close> homeomorphic_scaling inverse_inverse_eq inverse_zero less_irrefl)
  also have "... = sphere 0 1 \<inter> ((*\<^sub>R) (inverse r) ` (+) (- a) ` T) - {(b - a) /\<^sub>R r}"
    using assms by (auto simp: dist_norm norm_minus_commute divide_simps)
  also have "... homeomorphic p"
    apply (rule homeomorphic_punctured_affine_sphere_affine_01)
    using assms
    apply (auto simp: dist_norm norm_minus_commute affine_scaling affine_translation [symmetric] aff_dim_translation_eq inj)
    done
  finally show ?thesis .
qed

corollary%important homeomorphic_punctured_sphere_affine:
  fixes a :: "'a :: euclidean_space"
  assumes "0 < r" and b: "b \<in> sphere a r"
      and "affine T" and affS: "aff_dim T + 1 = DIM('a)"
    shows "(sphere a r - {b}) homeomorphic T"
  using%unimportant homeomorphic_punctured_affine_sphere_affine [of r b a UNIV T] assms by%unimportant auto

corollary%important homeomorphic_punctured_sphere_hyperplane:
  fixes a :: "'a :: euclidean_space"
  assumes "0 < r" and b: "b \<in> sphere a r"
      and "c \<noteq> 0"
    shows "(sphere a r - {b}) homeomorphic {x::'a. c \<bullet> x = d}"
apply (rule homeomorphic_punctured_sphere_affine)
using assms
apply (auto simp: affine_hyperplane of_nat_diff)
done

proposition%important homeomorphic_punctured_sphere_affine_gen:
  fixes a :: "'a :: euclidean_space"
  assumes "convex S" "bounded S" and a: "a \<in> rel_frontier S"
      and "affine T" and affS: "aff_dim S = aff_dim T + 1"
    shows "rel_frontier S - {a} homeomorphic T"
proof%unimportant -
  obtain U :: "'a set" where "affine U" "convex U" and affdS: "aff_dim U = aff_dim S"
    using choose_affine_subset [OF affine_UNIV aff_dim_geq]
    by (meson aff_dim_affine_hull affine_affine_hull affine_imp_convex)
  have "S \<noteq> {}" using assms by auto
  then obtain z where "z \<in> U"
    by (metis aff_dim_negative_iff equals0I affdS)
  then have bne: "ball z 1 \<inter> U \<noteq> {}" by force
  then have [simp]: "aff_dim(ball z 1 \<inter> U) = aff_dim U"
    using aff_dim_convex_Int_open [OF \<open>convex U\<close> open_ball]
    by (fastforce simp add: Int_commute)
  have "rel_frontier S homeomorphic rel_frontier (ball z 1 \<inter> U)"
    by (rule homeomorphic_rel_frontiers_convex_bounded_sets)
       (auto simp: \<open>affine U\<close> affine_imp_convex convex_Int affdS assms)
  also have "... = sphere z 1 \<inter> U"
    using convex_affine_rel_frontier_Int [of "ball z 1" U]
    by (simp add: \<open>affine U\<close> bne)
  finally have "rel_frontier S homeomorphic sphere z 1 \<inter> U" . 
  then obtain h k where him: "h ` rel_frontier S = sphere z 1 \<inter> U"
                    and kim: "k ` (sphere z 1 \<inter> U) = rel_frontier S"
                    and hcon: "continuous_on (rel_frontier S) h"
                    and kcon: "continuous_on (sphere z 1 \<inter> U) k"
                    and kh:  "\<And>x. x \<in> rel_frontier S \<Longrightarrow> k(h(x)) = x"
                    and hk:  "\<And>y. y \<in> sphere z 1 \<inter> U \<Longrightarrow> h(k(y)) = y"
    unfolding homeomorphic_def homeomorphism_def by auto
  have "rel_frontier S - {a} homeomorphic (sphere z 1 \<inter> U) - {h a}"
  proof (rule homeomorphicI)
    show h: "h ` (rel_frontier S - {a}) = sphere z 1 \<inter> U - {h a}"
      using him a kh by auto metis
    show "k ` (sphere z 1 \<inter> U - {h a}) = rel_frontier S - {a}"
      by (force simp: h [symmetric] image_comp o_def kh)
  qed (auto intro: continuous_on_subset hcon kcon simp: kh hk)
  also have "... homeomorphic T"
    by (rule homeomorphic_punctured_affine_sphere_affine)
       (use a him in \<open>auto simp: affS affdS \<open>affine T\<close> \<open>affine U\<close> \<open>z \<in> U\<close>\<close>)
  finally show ?thesis .
qed


text\<open> When dealing with AR, ANR and ANR later, it's useful to know that every set
  is homeomorphic to a closed subset of a convex set, and
  if the set is locally compact we can take the convex set to be the universe.\<close>

proposition%important homeomorphic_closedin_convex:
  fixes S :: "'m::euclidean_space set"
  assumes "aff_dim S < DIM('n)"
  obtains U and T :: "'n::euclidean_space set"
     where "convex U" "U \<noteq> {}" "closedin (subtopology euclidean U) T"
           "S homeomorphic T"
proof%unimportant (cases "S = {}")
  case True then show ?thesis
    by (rule_tac U=UNIV and T="{}" in that) auto
next
  case False
  then obtain a where "a \<in> S" by auto
  obtain i::'n where i: "i \<in> Basis" "i \<noteq> 0"
    using SOME_Basis Basis_zero by force
  have "0 \<in> affine hull ((+) (- a) ` S)"
    by (simp add: \<open>a \<in> S\<close> hull_inc)
  then have "dim ((+) (- a) ` S) = aff_dim ((+) (- a) ` S)"
    by (simp add: aff_dim_zero)
  also have "... < DIM('n)"
    by (simp add: aff_dim_translation_eq assms)
  finally have dd: "dim ((+) (- a) ` S) < DIM('n)"
    by linarith
  obtain T where "subspace T" and Tsub: "T \<subseteq> {x. i \<bullet> x = 0}"
             and dimT: "dim T = dim ((+) (- a) ` S)"
    apply (rule choose_subspace_of_subspace [of "dim ((+) (- a) ` S)" "{x::'n. i \<bullet> x = 0}"])
     apply (simp add: dim_hyperplane [OF \<open>i \<noteq> 0\<close>])
     apply (metis DIM_positive Suc_pred dd not_le not_less_eq_eq)
    apply (metis span_eq_iff subspace_hyperplane)
    done
  have "subspace (span ((+) (- a) ` S))"
    using subspace_span by blast
  then obtain h k where "linear h" "linear k"
               and heq: "h ` span ((+) (- a) ` S) = T"
               and keq:"k ` T = span ((+) (- a) ` S)"
               and hinv [simp]:  "\<And>x. x \<in> span ((+) (- a) ` S) \<Longrightarrow> k(h x) = x"
               and kinv [simp]:  "\<And>x. x \<in> T \<Longrightarrow> h(k x) = x"
    apply (rule isometries_subspaces [OF _ \<open>subspace T\<close>])
    apply (auto simp: dimT)
    done
  have hcont: "continuous_on A h" and kcont: "continuous_on B k" for A B
    using \<open>linear h\<close> \<open>linear k\<close> linear_continuous_on linear_conv_bounded_linear by blast+
  have ihhhh[simp]: "\<And>x. x \<in> S \<Longrightarrow> i \<bullet> h (x - a) = 0"
    using Tsub [THEN subsetD] heq span_superset by fastforce
  have "sphere 0 1 - {i} homeomorphic {x. i \<bullet> x = 0}"
    apply (rule homeomorphic_punctured_sphere_affine)
    using i
    apply (auto simp: affine_hyperplane)
    by (metis DIM_positive Suc_eq_plus1 add.left_neutral diff_add_cancel not_le not_less_eq_eq of_nat_1 of_nat_diff)
  then obtain f g where fg: "homeomorphism (sphere 0 1 - {i}) {x. i \<bullet> x = 0} f g"
    by (force simp: homeomorphic_def)
  have "h ` (+) (- a) ` S \<subseteq> T"
    using heq span_superset span_linear_image by blast
  then have "g ` h ` (+) (- a) ` S \<subseteq> g ` {x. i \<bullet> x = 0}"
    using Tsub by (simp add: image_mono)
  also have "... \<subseteq> sphere 0 1 - {i}"
    by (simp add: fg [unfolded homeomorphism_def])
  finally have gh_sub_sph: "(g \<circ> h) ` (+) (- a) ` S \<subseteq> sphere 0 1 - {i}"
    by (metis image_comp)
  then have gh_sub_cb: "(g \<circ> h) ` (+) (- a) ` S \<subseteq> cball 0 1"
    by (metis Diff_subset order_trans sphere_cball)
  have [simp]: "\<And>u. u \<in> S \<Longrightarrow> norm (g (h (u - a))) = 1"
    using gh_sub_sph [THEN subsetD] by (auto simp: o_def)
  have ghcont: "continuous_on ((+) (- a) ` S) (\<lambda>x. g (h x))"
    apply (rule continuous_on_compose2 [OF homeomorphism_cont2 [OF fg] hcont], force)
    done
  have kfcont: "continuous_on ((g \<circ> h \<circ> (+) (- a)) ` S) (\<lambda>x. k (f x))"
    apply (rule continuous_on_compose2 [OF kcont])
    using homeomorphism_cont1 [OF fg] gh_sub_sph apply (force intro: continuous_on_subset, blast)
    done
  have "S homeomorphic (+) (- a) ` S"
    by (simp add: homeomorphic_translation)
  also have Shom: "\<dots> homeomorphic (g \<circ> h) ` (+) (- a) ` S"
    apply (simp add: homeomorphic_def homeomorphism_def)
    apply (rule_tac x="g \<circ> h" in exI)
    apply (rule_tac x="k \<circ> f" in exI)
    apply (auto simp: ghcont kfcont span_base homeomorphism_apply2 [OF fg] image_comp)
    apply (force simp: o_def homeomorphism_apply2 [OF fg] span_base)
    done
  finally have Shom: "S homeomorphic (g \<circ> h) ` (+) (- a) ` S" .
  show ?thesis
    apply (rule_tac U = "ball 0 1 \<union> image (g o h) ((+) (- a) ` S)"
                and T = "image (g o h) ((+) (- a) ` S)"
                    in that)
    apply (rule convex_intermediate_ball [of 0 1], force)
    using gh_sub_cb apply force
    apply force
    apply (simp add: closedin_closed)
    apply (rule_tac x="sphere 0 1" in exI)
    apply (auto simp: Shom)
    done
qed

subsection%important\<open>Locally compact sets in an open set\<close>

text\<open> Locally compact sets are closed in an open set and are homeomorphic
  to an absolutely closed set if we have one more dimension to play with.\<close>

lemma%important locally_compact_open_Int_closure:
  fixes S :: "'a :: metric_space set"
  assumes "locally compact S"
  obtains T where "open T" "S = T \<inter> closure S"
proof%unimportant -
  have "\<forall>x\<in>S. \<exists>T v u. u = S \<inter> T \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> S \<and> open T \<and> compact v"
    by (metis assms locally_compact openin_open)
  then obtain t v where
        tv: "\<And>x. x \<in> S
             \<Longrightarrow> v x \<subseteq> S \<and> open (t x) \<and> compact (v x) \<and> (\<exists>u. x \<in> u \<and> u \<subseteq> v x \<and> u = S \<inter> t x)"
    by metis
  then have o: "open (\<Union>(t ` S))"
    by blast
  have "S = \<Union> (v ` S)"
    using tv by blast
  also have "... = \<Union>(t ` S) \<inter> closure S"
  proof
    show "\<Union>(v ` S) \<subseteq> \<Union>(t ` S) \<inter> closure S"
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
    then show "\<Union>(t ` S) \<inter> closure S \<subseteq> \<Union>(v ` S)"
      by blast
  qed
  finally have e: "S = \<Union>(t ` S) \<inter> closure S" .
  show ?thesis
    by (rule that [OF o e])
qed


lemma%unimportant locally_compact_closedin_open:
    fixes S :: "'a :: metric_space set"
    assumes "locally compact S"
    obtains T where "open T" "closedin (subtopology euclidean T) S"
  by (metis locally_compact_open_Int_closure [OF assms] closed_closure closedin_closed_Int)


lemma%unimportant locally_compact_homeomorphism_projection_closed:
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
      by (rule continuous_at_compose continuous_intros continuous_at_setdist)+
    have setdist1D: "setdist {a} (- U) *\<^sub>R b = One \<Longrightarrow> setdist {a} (- U) \<noteq> 0" for a::'a and b::'b
      by force
    have *: "r *\<^sub>R b = One \<Longrightarrow> b = (1 / r) *\<^sub>R One" for r and b::'b
      by (metis One_non_0 nonzero_divide_eq_eq real_vector.scale_eq_0_iff real_vector.scale_scale scaleR_one)
    have "f ` U = (\<lambda>z. (setdist {fst z} (- U) *\<^sub>R snd z)) -` {One}"
      apply (auto simp: f_def setdist_eq_0_sing_1 field_simps Ucomp)
      apply (rule_tac x=a in image_eqI)
      apply (auto simp: * setdist_eq_0_sing_1 dest: setdist1D)
      done
    then have clfU: "closed (f ` U)"
      apply (rule ssubst)
      apply (rule continuous_closed_vimage)
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

lemma%unimportant locally_compact_closed_Int_open:
  fixes S :: "'a :: euclidean_space set"
  shows
    "locally compact S \<longleftrightarrow> (\<exists>U u. closed U \<and> open u \<and> S = U \<inter> u)"
by (metis closed_closure closed_imp_locally_compact inf_commute locally_compact_Int locally_compact_open_Int_closure open_imp_locally_compact)


lemma%unimportant lowerdim_embeddings:
  assumes  "DIM('a) < DIM('b)"
  obtains f :: "'a::euclidean_space*real \<Rightarrow> 'b::euclidean_space" 
      and g :: "'b \<Rightarrow> 'a*real"
      and j :: 'b
  where "linear f" "linear g" "\<And>z. g (f z) = z" "j \<in> Basis" "\<And>x. f(x,0) \<bullet> j = 0"
proof -
  let ?B = "Basis :: ('a*real) set"
  have b01: "(0,1) \<in> ?B"
    by (simp add: Basis_prod_def)
  have "DIM('a * real) \<le> DIM('b)"
    by (simp add: Suc_leI assms)
  then obtain basf :: "'a*real \<Rightarrow> 'b" where sbf: "basf ` ?B \<subseteq> Basis" and injbf: "inj_on basf Basis"
    by (metis finite_Basis card_le_inj)
  define basg:: "'b \<Rightarrow> 'a * real" where
    "basg \<equiv> \<lambda>i. if i \<in> basf ` Basis then inv_into Basis basf i else (0,1)"
  have bgf[simp]: "basg (basf i) = i" if "i \<in> Basis" for i
    using inv_into_f_f injbf that by (force simp: basg_def)
  have sbg: "basg ` Basis \<subseteq> ?B" 
    by (force simp: basg_def injbf b01)
  define f :: "'a*real \<Rightarrow> 'b" where "f \<equiv> \<lambda>u. \<Sum>j\<in>Basis. (u \<bullet> basg j) *\<^sub>R j"
  define g :: "'b \<Rightarrow> 'a*real" where "g \<equiv> \<lambda>z. (\<Sum>i\<in>Basis. (z \<bullet> basf i) *\<^sub>R i)" 
  show ?thesis
  proof
    show "linear f"
      unfolding f_def
      by (intro linear_compose_sum linearI ballI) (auto simp: algebra_simps)
    show "linear g"
      unfolding g_def
      by (intro linear_compose_sum linearI ballI) (auto simp: algebra_simps)
    have *: "(\<Sum>a \<in> Basis. a \<bullet> basf b * (x \<bullet> basg a)) = x \<bullet> b" if "b \<in> Basis" for x b
      using sbf that by auto
    show gf: "g (f x) = x" for x
      apply (rule euclidean_eqI)
      apply (simp add: f_def g_def inner_sum_left scaleR_sum_left algebra_simps)
      apply (simp add: Groups_Big.sum_distrib_left [symmetric] *)
      done
    show "basf(0,1) \<in> Basis"
      using b01 sbf by auto
    then show "f(x,0) \<bullet> basf(0,1) = 0" for x
      apply (simp add: f_def inner_sum_left)
      apply (rule comm_monoid_add_class.sum.neutral)
      using b01 inner_not_same_Basis by fastforce
  qed
qed

proposition%important locally_compact_homeomorphic_closed:
  fixes S :: "'a::euclidean_space set"
  assumes "locally compact S" and dimlt: "DIM('a) < DIM('b)"
  obtains T :: "'b::euclidean_space set" where "closed T" "S homeomorphic T"
proof%unimportant -
  obtain U:: "('a*real)set" and h
    where "closed U" and homU: "homeomorphism S U h fst"
    using locally_compact_homeomorphism_projection_closed assms by metis
  obtain f :: "'a*real \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a*real"
    where "linear f" "linear g" and gf [simp]: "\<And>z. g (f z) = z"
    using lowerdim_embeddings [OF dimlt] by metis 
  then have "inj f"
    by (metis injI)
  have gfU: "g ` f ` U = U"
    by (simp add: image_comp o_def)
  have "S homeomorphic U"
    using homU homeomorphic_def by blast
  also have "... homeomorphic f ` U"
    apply (rule homeomorphicI [OF refl gfU])
       apply (meson \<open>inj f\<close> \<open>linear f\<close> homeomorphism_cont2 linear_homeomorphism_image)
    using \<open>linear g\<close> linear_continuous_on linear_conv_bounded_linear apply blast
    apply (auto simp: o_def)
    done
  finally show ?thesis
    apply (rule_tac T = "f ` U" in that)
    apply (rule closed_injective_linear_image [OF \<open>closed U\<close> \<open>linear f\<close> \<open>inj f\<close>], assumption)
    done
qed


lemma%important homeomorphic_convex_compact_lemma:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S"
    and "compact S"
    and "cball 0 1 \<subseteq> S"
  shows "S homeomorphic (cball (0::'a) 1)"
proof%unimportant (rule starlike_compact_projective_special[OF assms(2-3)])
  fix x u
  assume "x \<in> S" and "0 \<le> u" and "u < (1::real)"
  have "open (ball (u *\<^sub>R x) (1 - u))"
    by (rule open_ball)
  moreover have "u *\<^sub>R x \<in> ball (u *\<^sub>R x) (1 - u)"
    unfolding centre_in_ball using \<open>u < 1\<close> by simp
  moreover have "ball (u *\<^sub>R x) (1 - u) \<subseteq> S"
  proof
    fix y
    assume "y \<in> ball (u *\<^sub>R x) (1 - u)"
    then have "dist (u *\<^sub>R x) y < 1 - u"
      unfolding mem_ball .
    with \<open>u < 1\<close> have "inverse (1 - u) *\<^sub>R (y - u *\<^sub>R x) \<in> cball 0 1"
      by (simp add: dist_norm inverse_eq_divide norm_minus_commute)
    with assms(3) have "inverse (1 - u) *\<^sub>R (y - u *\<^sub>R x) \<in> S" ..
    with assms(1) have "(1 - u) *\<^sub>R ((y - u *\<^sub>R x) /\<^sub>R (1 - u)) + u *\<^sub>R x \<in> S"
      using \<open>x \<in> S\<close> \<open>0 \<le> u\<close> \<open>u < 1\<close> [THEN less_imp_le] by (rule convexD_alt)
    then show "y \<in> S" using \<open>u < 1\<close>
      by simp
  qed
  ultimately have "u *\<^sub>R x \<in> interior S" ..
  then show "u *\<^sub>R x \<in> S - frontier S"
    using frontier_def and interior_subset by auto
qed

proposition%important homeomorphic_convex_compact_cball:
  fixes e :: real
    and S :: "'a::euclidean_space set"
  assumes "convex S"
    and "compact S"
    and "interior S \<noteq> {}"
    and "e > 0"
  shows "S homeomorphic (cball (b::'a) e)"
proof%unimportant -
  obtain a where "a \<in> interior S"
    using assms(3) by auto
  then obtain d where "d > 0" and d: "cball a d \<subseteq> S"
    unfolding mem_interior_cball by auto
  let ?d = "inverse d" and ?n = "0::'a"
  have "cball ?n 1 \<subseteq> (\<lambda>x. inverse d *\<^sub>R (x - a)) ` S"
    apply rule
    apply (rule_tac x="d *\<^sub>R x + a" in image_eqI)
    defer
    apply (rule d[unfolded subset_eq, rule_format])
    using \<open>d > 0\<close>
    unfolding mem_cball dist_norm
    apply (auto simp add: mult_right_le_one_le)
    done
  then have "(\<lambda>x. inverse d *\<^sub>R (x - a)) ` S homeomorphic cball ?n 1"
    using homeomorphic_convex_compact_lemma[of "(\<lambda>x. ?d *\<^sub>R -a + ?d *\<^sub>R x) ` S",
      OF convex_affinity compact_affinity]
    using assms(1,2)
    by (auto simp add: scaleR_right_diff_distrib)
  then show ?thesis
    apply (rule_tac homeomorphic_trans[OF _ homeomorphic_balls(2)[of 1 _ ?n]])
    apply (rule homeomorphic_trans[OF homeomorphic_affinity[of "?d" S "?d *\<^sub>R -a"]])
    using \<open>d>0\<close> \<open>e>0\<close>
    apply (auto simp add: scaleR_right_diff_distrib)
    done
qed

corollary%important homeomorphic_convex_compact:
  fixes S :: "'a::euclidean_space set"
    and T :: "'a set"
  assumes "convex S" "compact S" "interior S \<noteq> {}"
    and "convex T" "compact T" "interior T \<noteq> {}"
  shows "S homeomorphic T"
  using assms
  by (meson zero_less_one homeomorphic_trans homeomorphic_convex_compact_cball homeomorphic_sym)

subsection%important\<open>Covering spaces and lifting results for them\<close>

definition%important covering_space
           :: "'a::topological_space set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b::topological_space set \<Rightarrow> bool"
  where
  "covering_space c p S \<equiv>
       continuous_on c p \<and> p ` c = S \<and>
       (\<forall>x \<in> S. \<exists>T. x \<in> T \<and> openin (subtopology euclidean S) T \<and>
                    (\<exists>v. \<Union>v = c \<inter> p -` T \<and>
                        (\<forall>u \<in> v. openin (subtopology euclidean c) u) \<and>
                        pairwise disjnt v \<and>
                        (\<forall>u \<in> v. \<exists>q. homeomorphism u T p q)))"

lemma%unimportant covering_space_imp_continuous: "covering_space c p S \<Longrightarrow> continuous_on c p"
  by (simp add: covering_space_def)

lemma%unimportant covering_space_imp_surjective: "covering_space c p S \<Longrightarrow> p ` c = S"
  by (simp add: covering_space_def)

lemma%unimportant homeomorphism_imp_covering_space: "homeomorphism S T f g \<Longrightarrow> covering_space S f T"
  apply (simp add: homeomorphism_def covering_space_def, clarify)
  apply (rule_tac x=T in exI, simp)
  apply (rule_tac x="{S}" in exI, auto)
  done

lemma%unimportant covering_space_local_homeomorphism:
  assumes "covering_space c p S" "x \<in> c"
  obtains T u q where "x \<in> T" "openin (subtopology euclidean c) T"
                      "p x \<in> u" "openin (subtopology euclidean S) u"
                      "homeomorphism T u p q"
using assms
apply (simp add: covering_space_def, clarify)
  apply (drule_tac x="p x" in bspec, force)
  by (metis IntI UnionE vimage_eq) 


lemma%important covering_space_local_homeomorphism_alt:
  assumes p: "covering_space c p S" and "y \<in> S"
  obtains x T U q where "p x = y"
                        "x \<in> T" "openin (subtopology euclidean c) T"
                        "y \<in> U" "openin (subtopology euclidean S) U"
                          "homeomorphism T U p q"
proof%unimportant -
  obtain x where "p x = y" "x \<in> c"
    using assms covering_space_imp_surjective by blast
  show ?thesis
    apply (rule covering_space_local_homeomorphism [OF p \<open>x \<in> c\<close>])
    using that \<open>p x = y\<close> by blast
qed

proposition%important covering_space_open_map:
  fixes S :: "'a :: metric_space set" and T :: "'b :: metric_space set"
  assumes p: "covering_space c p S" and T: "openin (subtopology euclidean c) T"
    shows "openin (subtopology euclidean S) (p ` T)"
proof%unimportant -
  have pce: "p ` c = S"
   and covs:
       "\<And>x. x \<in> S \<Longrightarrow>
            \<exists>X VS. x \<in> X \<and> openin (subtopology euclidean S) X \<and>
                  \<Union>VS = c \<inter> p -` X \<and>
                  (\<forall>u \<in> VS. openin (subtopology euclidean c) u) \<and>
                  pairwise disjnt VS \<and>
                  (\<forall>u \<in> VS. \<exists>q. homeomorphism u X p q)"
    using p by (auto simp: covering_space_def)
  have "T \<subseteq> c"  by (metis openin_euclidean_subtopology_iff T)
  have "\<exists>X. openin (subtopology euclidean S) X \<and> y \<in> X \<and> X \<subseteq> p ` T"
          if "y \<in> p ` T" for y
  proof -
    have "y \<in> S" using \<open>T \<subseteq> c\<close> pce that by blast
    obtain U VS where "y \<in> U" and U: "openin (subtopology euclidean S) U"
                  and VS: "\<Union>VS = c \<inter> p -` U"
                  and openVS: "\<forall>V \<in> VS. openin (subtopology euclidean c) V"
                  and homVS: "\<And>V. V \<in> VS \<Longrightarrow> \<exists>q. homeomorphism V U p q"
      using covs [OF \<open>y \<in> S\<close>] by auto
    obtain x where "x \<in> c" "p x \<in> U" "x \<in> T" "p x = y"
      apply simp
      using T [unfolded openin_euclidean_subtopology_iff] \<open>y \<in> U\<close> \<open>y \<in> p ` T\<close> by blast
    with VS obtain V where "x \<in> V" "V \<in> VS" by auto
    then obtain q where q: "homeomorphism V U p q" using homVS by blast
    then have ptV: "p ` (T \<inter> V) = U \<inter> q -` (T \<inter> V)"
      using VS \<open>V \<in> VS\<close> by (auto simp: homeomorphism_def)
    have ocv: "openin (subtopology euclidean c) V"
      by (simp add: \<open>V \<in> VS\<close> openVS)
    have "openin (subtopology euclidean U) (U \<inter> q -` (T \<inter> V))"
      apply (rule continuous_on_open [THEN iffD1, rule_format])
       using homeomorphism_def q apply blast
      using openin_subtopology_Int_subset [of c] q T unfolding homeomorphism_def
      by (metis inf.absorb_iff2 Int_commute ocv openin_euclidean_subtopology_iff)
    then have os: "openin (subtopology euclidean S) (U \<inter> q -` (T \<inter> V))"
      using openin_trans [of U] by (simp add: Collect_conj_eq U)
    show ?thesis
      apply (rule_tac x = "p ` (T \<inter> V)" in exI)
      apply (rule conjI)
      apply (simp only: ptV os)
      using \<open>p x = y\<close> \<open>x \<in> V\<close> \<open>x \<in> T\<close> apply blast
      done
  qed
  with openin_subopen show ?thesis by blast
qed

lemma%important covering_space_lift_unique_gen:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  fixes g1 :: "'a \<Rightarrow> 'c::real_normed_vector"
  assumes cov: "covering_space c p S"
      and eq: "g1 a = g2 a"
      and f: "continuous_on T f"  "f ` T \<subseteq> S"
      and g1: "continuous_on T g1"  "g1 ` T \<subseteq> c"
      and fg1: "\<And>x. x \<in> T \<Longrightarrow> f x = p(g1 x)"
      and g2: "continuous_on T g2"  "g2 ` T \<subseteq> c"
      and fg2: "\<And>x. x \<in> T \<Longrightarrow> f x = p(g2 x)"
      and u_compt: "U \<in> components T" and "a \<in> U" "x \<in> U"
    shows "g1 x = g2 x"
proof%unimportant -
  have "U \<subseteq> T" by (rule in_components_subset [OF u_compt])
  define G12 where "G12 \<equiv> {x \<in> U. g1 x - g2 x = 0}"
  have "connected U" by (rule in_components_connected [OF u_compt])
  have contu: "continuous_on U g1" "continuous_on U g2"
       using \<open>U \<subseteq> T\<close> continuous_on_subset g1 g2 by blast+
  have o12: "openin (subtopology euclidean U) G12"
  unfolding G12_def
  proof (subst openin_subopen, clarify)
    fix z
    assume z: "z \<in> U" "g1 z - g2 z = 0"
    obtain v w q where "g1 z \<in> v" and ocv: "openin (subtopology euclidean c) v"
                   and "p (g1 z) \<in> w" and osw: "openin (subtopology euclidean S) w"
                   and hom: "homeomorphism v w p q"
      apply (rule_tac x = "g1 z" in covering_space_local_homeomorphism [OF cov])
       using \<open>U \<subseteq> T\<close> \<open>z \<in> U\<close> g1(2) apply blast+
      done
    have "g2 z \<in> v" using \<open>g1 z \<in> v\<close> z by auto
    have gg: "U \<inter> g -` v = U \<inter> g -` (v \<inter> g ` U)" for g
      by auto
    have "openin (subtopology euclidean (g1 ` U)) (v \<inter> g1 ` U)"
      using ocv \<open>U \<subseteq> T\<close> g1 by (fastforce simp add: openin_open)
    then have 1: "openin (subtopology euclidean U) (U \<inter> g1 -` v)"
      unfolding gg by (blast intro: contu continuous_on_open [THEN iffD1, rule_format])
    have "openin (subtopology euclidean (g2 ` U)) (v \<inter> g2 ` U)"
      using ocv \<open>U \<subseteq> T\<close> g2 by (fastforce simp add: openin_open)
    then have 2: "openin (subtopology euclidean U) (U \<inter> g2 -` v)"
      unfolding gg by (blast intro: contu continuous_on_open [THEN iffD1, rule_format])
    show "\<exists>T. openin (subtopology euclidean U) T \<and> z \<in> T \<and> T \<subseteq> {z \<in> U. g1 z - g2 z = 0}"
      using z
      apply (rule_tac x = "(U \<inter> g1 -` v) \<inter> (U \<inter> g2 -` v)" in exI)
      apply (intro conjI)
      apply (rule openin_Int [OF 1 2])
      using \<open>g1 z \<in> v\<close>  \<open>g2 z \<in> v\<close>  apply (force simp:, clarify)
      apply (metis \<open>U \<subseteq> T\<close> subsetD eq_iff_diff_eq_0 fg1 fg2 hom homeomorphism_def)
      done
  qed
  have c12: "closedin (subtopology euclidean U) G12"
    unfolding G12_def
    by (intro continuous_intros continuous_closedin_preimage_constant contu)
  have "G12 = {} \<or> G12 = U"
    by (intro connected_clopen [THEN iffD1, rule_format] \<open>connected U\<close> conjI o12 c12)
  with eq \<open>a \<in> U\<close> have "\<And>x. x \<in> U \<Longrightarrow> g1 x - g2 x = 0" by (auto simp: G12_def)
  then show ?thesis
    using \<open>x \<in> U\<close> by force
qed

proposition%important covering_space_lift_unique:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  fixes g1 :: "'a \<Rightarrow> 'c::real_normed_vector"
  assumes "covering_space c p S"
          "g1 a = g2 a"
          "continuous_on T f"  "f ` T \<subseteq> S"
          "continuous_on T g1"  "g1 ` T \<subseteq> c"  "\<And>x. x \<in> T \<Longrightarrow> f x = p(g1 x)"
          "continuous_on T g2"  "g2 ` T \<subseteq> c"  "\<And>x. x \<in> T \<Longrightarrow> f x = p(g2 x)"
          "connected T"  "a \<in> T"   "x \<in> T"
   shows "g1 x = g2 x"
  using%unimportant covering_space_lift_unique_gen [of c p S] in_components_self assms ex_in_conv
  by%unimportant blast

lemma%unimportant covering_space_locally:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes loc: "locally \<phi> C" and cov: "covering_space C p S"
      and pim: "\<And>T. \<lbrakk>T \<subseteq> C; \<phi> T\<rbrakk> \<Longrightarrow> \<psi>(p ` T)"
    shows "locally \<psi> S"
proof -
  have "locally \<psi> (p ` C)"
    apply (rule locally_open_map_image [OF loc])
    using cov covering_space_imp_continuous apply blast
    using cov covering_space_imp_surjective covering_space_open_map apply blast
    by (simp add: pim)
  then show ?thesis
    using covering_space_imp_surjective [OF cov] by metis
qed


proposition%important covering_space_locally_eq:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes cov: "covering_space C p S"
      and pim: "\<And>T. \<lbrakk>T \<subseteq> C; \<phi> T\<rbrakk> \<Longrightarrow> \<psi>(p ` T)"
      and qim: "\<And>q U. \<lbrakk>U \<subseteq> S; continuous_on U q; \<psi> U\<rbrakk> \<Longrightarrow> \<phi>(q ` U)"
    shows "locally \<psi> S \<longleftrightarrow> locally \<phi> C"
         (is "?lhs = ?rhs")
proof%unimportant
  assume L: ?lhs
  show ?rhs
  proof (rule locallyI)
    fix V x
    assume V: "openin (subtopology euclidean C) V" and "x \<in> V"
    have "p x \<in> p ` C"
      by (metis IntE V \<open>x \<in> V\<close> imageI openin_open)
    then obtain T \<V> where "p x \<in> T"
                      and opeT: "openin (subtopology euclidean S) T"
                      and veq: "\<Union>\<V> = C \<inter> p -` T"
                      and ope: "\<forall>U\<in>\<V>. openin (subtopology euclidean C) U"
                      and hom: "\<forall>U\<in>\<V>. \<exists>q. homeomorphism U T p q"
      using cov unfolding covering_space_def by (blast intro: that)
    have "x \<in> \<Union>\<V>"
      using V veq \<open>p x \<in> T\<close> \<open>x \<in> V\<close> openin_imp_subset by fastforce
    then obtain U where "x \<in> U" "U \<in> \<V>"
      by blast
    then obtain q where opeU: "openin (subtopology euclidean C) U" and q: "homeomorphism U T p q"
      using ope hom by blast
    with V have "openin (subtopology euclidean C) (U \<inter> V)"
      by blast
    then have UV: "openin (subtopology euclidean S) (p ` (U \<inter> V))"
      using cov covering_space_open_map by blast
    obtain W W' where opeW: "openin (subtopology euclidean S) W" and "\<psi> W'" "p x \<in> W" "W \<subseteq> W'" and W'sub: "W' \<subseteq> p ` (U \<inter> V)"
      using locallyE [OF L UV] \<open>x \<in> U\<close> \<open>x \<in> V\<close> by blast
    then have "W \<subseteq> T"
      by (metis Int_lower1 q homeomorphism_image1 image_Int_subset order_trans)
    show "\<exists>U Z. openin (subtopology euclidean C) U \<and>
                 \<phi> Z \<and> x \<in> U \<and> U \<subseteq> Z \<and> Z \<subseteq> V"
    proof (intro exI conjI)
      have "openin (subtopology euclidean T) W"
        by (meson opeW opeT openin_imp_subset openin_subset_trans \<open>W \<subseteq> T\<close>)
      then have "openin (subtopology euclidean U) (q ` W)"
        by (meson homeomorphism_imp_open_map homeomorphism_symD q)
      then show "openin (subtopology euclidean C) (q ` W)"
        using opeU openin_trans by blast
      show "\<phi> (q ` W')"
        by (metis (mono_tags, lifting) Int_subset_iff UV W'sub \<open>\<psi> W'\<close> continuous_on_subset dual_order.trans homeomorphism_def image_Int_subset openin_imp_subset q qim)
      show "x \<in> q ` W"
        by (metis \<open>p x \<in> W\<close> \<open>x \<in> U\<close> homeomorphism_def imageI q)
      show "q ` W \<subseteq> q ` W'"
        using \<open>W \<subseteq> W'\<close> by blast
      have "W' \<subseteq> p ` V"
        using W'sub by blast
      then show "q ` W' \<subseteq> V"
        using W'sub homeomorphism_apply1 [OF q] by auto
      qed
  qed
next
  assume ?rhs
  then show ?lhs
    using cov covering_space_locally pim by blast
qed

lemma%unimportant covering_space_locally_compact_eq:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "covering_space C p S"
  shows "locally compact S \<longleftrightarrow> locally compact C"
  apply (rule covering_space_locally_eq [OF assms])
   apply (meson assms compact_continuous_image continuous_on_subset covering_space_imp_continuous)
  using compact_continuous_image by blast

lemma%unimportant covering_space_locally_connected_eq:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "covering_space C p S"
    shows "locally connected S \<longleftrightarrow> locally connected C"
  apply (rule covering_space_locally_eq [OF assms])
   apply (meson connected_continuous_image assms continuous_on_subset covering_space_imp_continuous)
  using connected_continuous_image by blast

lemma%unimportant covering_space_locally_path_connected_eq:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "covering_space C p S"
    shows "locally path_connected S \<longleftrightarrow> locally path_connected C"
  apply (rule covering_space_locally_eq [OF assms])
   apply (meson path_connected_continuous_image assms continuous_on_subset covering_space_imp_continuous)
  using path_connected_continuous_image by blast


lemma%unimportant covering_space_locally_compact:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "locally compact C" "covering_space C p S"
  shows "locally compact S"
  using assms covering_space_locally_compact_eq by blast


lemma%unimportant covering_space_locally_connected:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "locally connected C" "covering_space C p S"
  shows "locally connected S"
  using assms covering_space_locally_connected_eq by blast

lemma%unimportant covering_space_locally_path_connected:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "locally path_connected C" "covering_space C p S"
  shows "locally path_connected S"
  using assms covering_space_locally_path_connected_eq by blast

proposition%important covering_space_lift_homotopy:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and h :: "real \<times> 'c::real_normed_vector \<Rightarrow> 'b"
  assumes cov: "covering_space C p S"
      and conth: "continuous_on ({0..1} \<times> U) h"
      and him: "h ` ({0..1} \<times> U) \<subseteq> S"
      and heq: "\<And>y. y \<in> U \<Longrightarrow> h (0,y) = p(f y)"
      and contf: "continuous_on U f" and fim: "f ` U \<subseteq> C"
    obtains k where "continuous_on ({0..1} \<times> U) k"
                    "k ` ({0..1} \<times> U) \<subseteq> C"
                    "\<And>y. y \<in> U \<Longrightarrow> k(0, y) = f y"
                    "\<And>z. z \<in> {0..1} \<times> U \<Longrightarrow> h z = p(k z)"
proof%unimportant -
  have "\<exists>V k. openin (subtopology euclidean U) V \<and> y \<in> V \<and>
              continuous_on ({0..1} \<times> V) k \<and> k ` ({0..1} \<times> V) \<subseteq> C \<and>
              (\<forall>z \<in> V. k(0, z) = f z) \<and> (\<forall>z \<in> {0..1} \<times> V. h z = p(k z))"
        if "y \<in> U" for y
  proof -
    obtain UU where UU: "\<And>s. s \<in> S \<Longrightarrow> s \<in> (UU s) \<and> openin (subtopology euclidean S) (UU s) \<and>
                                        (\<exists>\<V>. \<Union>\<V> = C \<inter> p -` UU s \<and>
                                            (\<forall>U \<in> \<V>. openin (subtopology euclidean C) U) \<and>
                                            pairwise disjnt \<V> \<and>
                                            (\<forall>U \<in> \<V>. \<exists>q. homeomorphism U (UU s) p q))"
      using cov unfolding covering_space_def by (metis (mono_tags))
    then have ope: "\<And>s. s \<in> S \<Longrightarrow> s \<in> (UU s) \<and> openin (subtopology euclidean S) (UU s)"
      by blast
    have "\<exists>k n i. open k \<and> open n \<and>
                  t \<in> k \<and> y \<in> n \<and> i \<in> S \<and> h ` (({0..1} \<inter> k) \<times> (U \<inter> n)) \<subseteq> UU i" if "t \<in> {0..1}" for t
    proof -
      have hinS: "h (t, y) \<in> S"
        using \<open>y \<in> U\<close> him that by blast
      then have "(t,y) \<in> ({0..1} \<times> U) \<inter> h -` UU(h(t, y))"
        using \<open>y \<in> U\<close> \<open>t \<in> {0..1}\<close>  by (auto simp: ope)
      moreover have ope_01U: "openin (subtopology euclidean ({0..1} \<times> U)) (({0..1} \<times> U) \<inter> h -` UU(h(t, y)))"
        using hinS ope continuous_on_open_gen [OF him] conth by blast
      ultimately obtain V W where opeV: "open V" and "t \<in> {0..1} \<inter> V" "t \<in> {0..1} \<inter> V"
                              and opeW: "open W" and "y \<in> U" "y \<in> W"
                              and VW: "({0..1} \<inter> V) \<times> (U \<inter> W)  \<subseteq> (({0..1} \<times> U) \<inter> h -` UU(h(t, y)))"
        by (rule Times_in_interior_subtopology) (auto simp: openin_open)
      then show ?thesis
        using hinS by blast
    qed
    then obtain K NN X where
              K: "\<And>t. t \<in> {0..1} \<Longrightarrow> open (K t)"
          and NN: "\<And>t. t \<in> {0..1} \<Longrightarrow> open (NN t)"
          and inUS: "\<And>t. t \<in> {0..1} \<Longrightarrow> t \<in> K t \<and> y \<in> NN t \<and> X t \<in> S"
          and him: "\<And>t. t \<in> {0..1} \<Longrightarrow> h ` (({0..1} \<inter> K t) \<times> (U \<inter> NN t)) \<subseteq> UU (X t)"
    by (metis (mono_tags))
    obtain \<T> where "\<T> \<subseteq> ((\<lambda>i. K i \<times> NN i)) ` {0..1}" "finite \<T>" "{0::real..1} \<times> {y} \<subseteq> \<Union>\<T>"
    proof (rule compactE)
      show "compact ({0::real..1} \<times> {y})"
        by (simp add: compact_Times)
      show "{0..1} \<times> {y} \<subseteq> (\<Union>i\<in>{0..1}. K i \<times> NN i)"
        using K inUS by auto
      show "\<And>B. B \<in> (\<lambda>i. K i \<times> NN i) ` {0..1} \<Longrightarrow> open B"
        using K NN by (auto simp: open_Times)
    qed blast
    then obtain tk where "tk \<subseteq> {0..1}" "finite tk"
                     and tk: "{0::real..1} \<times> {y} \<subseteq> (\<Union>i \<in> tk. K i \<times> NN i)"
      by (metis (no_types, lifting) finite_subset_image)
    then have "tk \<noteq> {}"
      by auto
    define n where "n = \<Inter>(NN ` tk)"
    have "y \<in> n" "open n"
      using inUS NN \<open>tk \<subseteq> {0..1}\<close> \<open>finite tk\<close>
      by (auto simp: n_def open_INT subset_iff)
    obtain \<delta> where "0 < \<delta>" and \<delta>: "\<And>T. \<lbrakk>T \<subseteq> {0..1}; diameter T < \<delta>\<rbrakk> \<Longrightarrow> \<exists>B\<in>K ` tk. T \<subseteq> B"
    proof (rule Lebesgue_number_lemma [of "{0..1}" "K ` tk"])
      show "K ` tk \<noteq> {}"
        using \<open>tk \<noteq> {}\<close> by auto
      show "{0..1} \<subseteq> \<Union>(K ` tk)"
        using tk by auto
      show "\<And>B. B \<in> K ` tk \<Longrightarrow> open B"
        using \<open>tk \<subseteq> {0..1}\<close> K by auto
    qed auto
    obtain N::nat where N: "N > 1 / \<delta>"
      using reals_Archimedean2 by blast
    then have "N > 0"
      using \<open>0 < \<delta>\<close> order.asym by force
    have *: "\<exists>V k. openin (subtopology euclidean U) V \<and> y \<in> V \<and>
                   continuous_on ({0..of_nat n / N} \<times> V) k \<and>
                   k ` ({0..of_nat n / N} \<times> V) \<subseteq> C \<and>
                   (\<forall>z\<in>V. k (0, z) = f z) \<and>
                   (\<forall>z\<in>{0..of_nat n / N} \<times> V. h z = p (k z))" if "n \<le> N" for n
      using that
    proof (induction n)
      case 0
      show ?case
        apply (rule_tac x=U in exI)
        apply (rule_tac x="f \<circ> snd" in exI)
        apply (intro conjI \<open>y \<in> U\<close> continuous_intros continuous_on_subset [OF contf])
        using fim  apply (auto simp: heq)
        done
    next
      case (Suc n)
      then obtain V k where opeUV: "openin (subtopology euclidean U) V"
                        and "y \<in> V"
                        and contk: "continuous_on ({0..real n / real N} \<times> V) k"
                        and kim: "k ` ({0..real n / real N} \<times> V) \<subseteq> C"
                        and keq: "\<And>z. z \<in> V \<Longrightarrow> k (0, z) = f z"
                        and heq: "\<And>z. z \<in> {0..real n / real N} \<times> V \<Longrightarrow> h z = p (k z)"
        using Suc_leD by auto
      have "n \<le> N"
        using Suc.prems by auto
      obtain t where "t \<in> tk" and t: "{real n / real N .. (1 + real n) / real N} \<subseteq> K t"
      proof (rule bexE [OF \<delta>])
        show "{real n / real N .. (1 + real n) / real N} \<subseteq> {0..1}"
          using Suc.prems by (auto simp: divide_simps algebra_simps)
        show diameter_less: "diameter {real n / real N .. (1 + real n) / real N} < \<delta>"
          using \<open>0 < \<delta>\<close> N by (auto simp: divide_simps algebra_simps)
      qed blast
      have t01: "t \<in> {0..1}"
        using \<open>t \<in> tk\<close> \<open>tk \<subseteq> {0..1}\<close> by blast
      obtain \<V> where \<V>: "\<Union>\<V> = C \<inter> p -` UU (X t)"
                 and opeC: "\<And>U. U \<in> \<V> \<Longrightarrow> openin (subtopology euclidean C) U"
                 and "pairwise disjnt \<V>"
                 and homuu: "\<And>U. U \<in> \<V> \<Longrightarrow> \<exists>q. homeomorphism U (UU (X t)) p q"
        using inUS [OF t01] UU by meson
      have n_div_N_in: "real n / real N \<in> {real n / real N .. (1 + real n) / real N}"
        using N by (auto simp: divide_simps algebra_simps)
      with t have nN_in_kkt: "real n / real N \<in> K t"
        by blast
      have "k (real n / real N, y) \<in> C \<inter> p -` UU (X t)"
      proof (simp, rule conjI)
        show "k (real n / real N, y) \<in> C"
          using \<open>y \<in> V\<close> kim keq by force
        have "p (k (real n / real N, y)) = h (real n / real N, y)"
          by (simp add: \<open>y \<in> V\<close> heq)
        also have "... \<in> h ` (({0..1} \<inter> K t) \<times> (U \<inter> NN t))"
          apply (rule imageI)
           using \<open>y \<in> V\<close> t01 \<open>n \<le> N\<close>
          apply (simp add: nN_in_kkt \<open>y \<in> U\<close> inUS divide_simps)
          done
        also have "... \<subseteq> UU (X t)"
          using him t01 by blast
        finally show "p (k (real n / real N, y)) \<in> UU (X t)" .
      qed
      with \<V> have "k (real n / real N, y) \<in> \<Union>\<V>"
        by blast
      then obtain W where W: "k (real n / real N, y) \<in> W" and "W \<in> \<V>"
        by blast
      then obtain p' where opeC': "openin (subtopology euclidean C) W"
                       and hom': "homeomorphism W (UU (X t)) p p'"
        using homuu opeC by blast
      then have "W \<subseteq> C"
        using openin_imp_subset by blast
      define W' where "W' = UU(X t)"
      have opeVW: "openin (subtopology euclidean V) (V \<inter> (k \<circ> Pair (n / N)) -` W)"
        apply (rule continuous_openin_preimage [OF _ _ opeC'])
         apply (intro continuous_intros continuous_on_subset [OF contk])
        using kim apply (auto simp: \<open>y \<in> V\<close> W)
        done
      obtain N' where opeUN': "openin (subtopology euclidean U) N'"
                  and "y \<in> N'" and kimw: "k ` ({(real n / real N)} \<times> N') \<subseteq> W"
        apply (rule_tac N' = "(V \<inter> (k \<circ> Pair (n / N)) -` W)" in that)
        apply (fastforce simp:  \<open>y \<in> V\<close> W intro!: openin_trans [OF opeVW opeUV])+
        done
      obtain Q Q' where opeUQ: "openin (subtopology euclidean U) Q"
                    and cloUQ': "closedin (subtopology euclidean U) Q'"
                    and "y \<in> Q" "Q \<subseteq> Q'"
                    and Q': "Q' \<subseteq> (U \<inter> NN(t)) \<inter> N' \<inter> V"
      proof -
        obtain VO VX where "open VO" "open VX" and VO: "V = U \<inter> VO" and VX: "N' = U \<inter> VX"
          using opeUV opeUN' by (auto simp: openin_open)
        then have "open (NN(t) \<inter> VO \<inter> VX)"
          using NN t01 by blast
        then obtain e where "e > 0" and e: "cball y e \<subseteq> NN(t) \<inter> VO \<inter> VX"
          by (metis Int_iff \<open>N' = U \<inter> VX\<close> \<open>V = U \<inter> VO\<close> \<open>y \<in> N'\<close> \<open>y \<in> V\<close> inUS open_contains_cball t01)
        show ?thesis
        proof
          show "openin (subtopology euclidean U) (U \<inter> ball y e)"
            by blast
          show "closedin (subtopology euclidean U) (U \<inter> cball y e)"
            using e by (auto simp: closedin_closed)
        qed (use \<open>y \<in> U\<close> \<open>e > 0\<close> VO VX e in auto)
      qed
      then have "y \<in> Q'" "Q \<subseteq> (U \<inter> NN(t)) \<inter> N' \<inter> V"
        by blast+
      have neq: "{0..real n / real N} \<union> {real n / real N..(1 + real n) / real N} = {0..(1 + real n) / real N}"
        apply (auto simp: divide_simps)
        by (metis mult_zero_left of_nat_0_le_iff of_nat_0_less_iff order_trans real_mult_le_cancel_iff1)
      then have neqQ': "{0..real n / real N} \<times> Q' \<union> {real n / real N..(1 + real n) / real N} \<times> Q' = {0..(1 + real n) / real N} \<times> Q'"
        by blast
      have cont: "continuous_on ({0..(1 + real n) / real N} \<times> Q')
        (\<lambda>x. if x \<in> {0..real n / real N} \<times> Q' then k x else (p' \<circ> h) x)"
        unfolding neqQ' [symmetric]
      proof (rule continuous_on_cases_local, simp_all add: neqQ' del: comp_apply)
        show "closedin (subtopology euclidean ({0..(1 + real n) / real N} \<times> Q'))
                       ({0..real n / real N} \<times> Q')"
          apply (simp add: closedin_closed)
          apply (rule_tac x="{0 .. real n / real N} \<times> UNIV" in exI)
          using n_div_N_in apply (auto simp: closed_Times)
          done
        show "closedin (subtopology euclidean ({0..(1 + real n) / real N} \<times> Q'))
                       ({real n / real N..(1 + real n) / real N} \<times> Q')"
          apply (simp add: closedin_closed)
          apply (rule_tac x="{real n / real N .. (1 + real n) / real N} \<times> UNIV" in exI)
          apply (auto simp: closed_Times)
          by (meson divide_nonneg_nonneg of_nat_0_le_iff order_trans)
        show "continuous_on ({0..real n / real N} \<times> Q') k"
          apply (rule continuous_on_subset [OF contk])
          using Q' by auto
        have "continuous_on ({real n / real N..(1 + real n) / real N} \<times> Q') h"
        proof (rule continuous_on_subset [OF conth])
          show "{real n / real N..(1 + real n) / real N} \<times> Q' \<subseteq> {0..1} \<times> U"
            using \<open>N > 0\<close>
            apply auto
              apply (meson divide_nonneg_nonneg of_nat_0_le_iff order_trans)
            using Suc.prems order_trans apply fastforce
            apply (metis IntE  cloUQ' closedin_closed)
            done
        qed
        moreover have "continuous_on (h ` ({real n / real N..(1 + real n) / real N} \<times> Q')) p'"
        proof (rule continuous_on_subset [OF homeomorphism_cont2 [OF hom']])
          have "h ` ({real n / real N..(1 + real n) / real N} \<times> Q') \<subseteq> h ` (({0..1} \<inter> K t) \<times> (U \<inter> NN t))"
            apply (rule image_mono)
            using \<open>0 < \<delta>\<close> \<open>N > 0\<close> Suc.prems apply auto
              apply (meson divide_nonneg_nonneg of_nat_0_le_iff order_trans)
            using Suc.prems order_trans apply fastforce
            using t Q' apply auto
            done
          with him show "h ` ({real n / real N..(1 + real n) / real N} \<times> Q') \<subseteq> UU (X t)"
            using t01 by blast
        qed
        ultimately show "continuous_on ({real n / real N..(1 + real n) / real N} \<times> Q') (p' \<circ> h)"
          by (rule continuous_on_compose)
        have "k (real n / real N, b) = p' (h (real n / real N, b))" if "b \<in> Q'" for b
        proof -
          have "k (real n / real N, b) \<in> W"
            using that Q' kimw  by force
          then have "k (real n / real N, b) = p' (p (k (real n / real N, b)))"
            by (simp add:  homeomorphism_apply1 [OF hom'])
          then show ?thesis
            using Q' that by (force simp: heq)
        qed
        then show "\<And>x. x \<in> {real n / real N..(1 + real n) / real N} \<times> Q' \<and>
                  x \<in> {0..real n / real N} \<times> Q' \<Longrightarrow> k x = (p' \<circ> h) x"
          by auto
      qed
      have h_in_UU: "h (x, y) \<in> UU (X t)" if "y \<in> Q" "\<not> x \<le> real n / real N" "0 \<le> x" "x \<le> (1 + real n) / real N" for x y
      proof -
        have "x \<le> 1"
          using Suc.prems that order_trans by force
        moreover have "x \<in> K t"
          by (meson atLeastAtMost_iff le_less not_le subset_eq t that)
        moreover have "y \<in> U"
          using \<open>y \<in> Q\<close> opeUQ openin_imp_subset by blast
        moreover have "y \<in> NN t"
          using Q' \<open>Q \<subseteq> Q'\<close> \<open>y \<in> Q\<close> by auto
        ultimately have "(x, y) \<in> (({0..1} \<inter> K t) \<times> (U \<inter> NN t))"
          using that by auto
        then have "h (x, y) \<in> h ` (({0..1} \<inter> K t) \<times> (U \<inter> NN t))"
          by blast
        also have "... \<subseteq> UU (X t)"
          by (metis him t01)
        finally show ?thesis .
      qed
      let ?k = "(\<lambda>x. if x \<in> {0..real n / real N} \<times> Q' then k x else (p' \<circ> h) x)"
      show ?case
      proof (intro exI conjI)
        show "continuous_on ({0..real (Suc n) / real N} \<times> Q) ?k"
          apply (rule continuous_on_subset [OF cont])
          using \<open>Q \<subseteq> Q'\<close> by auto
        have "\<And>a b. \<lbrakk>a \<le> real n / real N; b \<in> Q'; 0 \<le> a\<rbrakk> \<Longrightarrow> k (a, b) \<in> C"
          using kim Q' by force
        moreover have "\<And>a b. \<lbrakk>b \<in> Q; 0 \<le> a; a \<le> (1 + real n) / real N; \<not> a \<le> real n / real N\<rbrakk> \<Longrightarrow> p' (h (a, b)) \<in> C"
          apply (rule \<open>W \<subseteq> C\<close> [THEN subsetD])
          using homeomorphism_image2 [OF hom', symmetric]  h_in_UU  Q' \<open>Q \<subseteq> Q'\<close> \<open>W \<subseteq> C\<close>
          apply auto
          done
        ultimately show "?k ` ({0..real (Suc n) / real N} \<times> Q) \<subseteq> C"
          using Q' \<open>Q \<subseteq> Q'\<close> by force
        show "\<forall>z\<in>Q. ?k (0, z) = f z"
          using Q' keq  \<open>Q \<subseteq> Q'\<close> by auto
        show "\<forall>z \<in> {0..real (Suc n) / real N} \<times> Q. h z = p(?k z)"
          using \<open>Q \<subseteq> U \<inter> NN t \<inter> N' \<inter> V\<close> heq apply clarsimp
          using h_in_UU Q' \<open>Q \<subseteq> Q'\<close> apply (auto simp: homeomorphism_apply2 [OF hom', symmetric])
          done
        qed (auto simp: \<open>y \<in> Q\<close> opeUQ)
    qed
    show ?thesis
      using*[OF order_refl] N \<open>0 < \<delta>\<close> by (simp add: split: if_split_asm)
  qed
  then obtain V fs where opeV: "\<And>y. y \<in> U \<Longrightarrow> openin (subtopology euclidean U) (V y)"
          and V: "\<And>y. y \<in> U \<Longrightarrow> y \<in> V y"
          and contfs: "\<And>y. y \<in> U \<Longrightarrow> continuous_on ({0..1} \<times> V y) (fs y)"
          and *: "\<And>y. y \<in> U \<Longrightarrow> (fs y) ` ({0..1} \<times> V y) \<subseteq> C \<and>
                            (\<forall>z \<in> V y. fs y (0, z) = f z) \<and>
                            (\<forall>z \<in> {0..1} \<times> V y. h z = p(fs y z))"
    by (metis (mono_tags))
  then have VU: "\<And>y. y \<in> U \<Longrightarrow> V y \<subseteq> U"
    by (meson openin_imp_subset)
  obtain k where contk: "continuous_on ({0..1} \<times> U) k"
             and k: "\<And>x i. \<lbrakk>i \<in> U; x \<in> {0..1} \<times> U \<inter> {0..1} \<times> V i\<rbrakk> \<Longrightarrow> k x = fs i x"
  proof (rule pasting_lemma_exists)
    show "{0..1} \<times> U \<subseteq> (\<Union>i\<in>U. {0..1} \<times> V i)"
      apply auto
      using V by blast
    show "\<And>i. i \<in> U \<Longrightarrow> openin (subtopology euclidean ({0..1} \<times> U)) ({0..1} \<times> V i)"
      by (simp add: opeV openin_Times)
    show "\<And>i. i \<in> U \<Longrightarrow> continuous_on ({0..1} \<times> V i) (fs i)"
      using contfs by blast
    show "fs i x = fs j x"  if "i \<in> U" "j \<in> U" and x: "x \<in> {0..1} \<times> U \<inter> {0..1} \<times> V i \<inter> {0..1} \<times> V j"
         for i j x
    proof -
      obtain u y where "x = (u, y)" "y \<in> V i" "y \<in> V j" "0 \<le> u" "u \<le> 1"
        using x by auto
      show ?thesis
      proof (rule covering_space_lift_unique [OF cov, of _ "(0,y)" _ "{0..1} \<times> {y}" h])
        show "fs i (0, y) = fs j (0, y)"
          using*V by (simp add: \<open>y \<in> V i\<close> \<open>y \<in> V j\<close> that)
        show conth_y: "continuous_on ({0..1} \<times> {y}) h"
          apply (rule continuous_on_subset [OF conth])
          using VU \<open>y \<in> V j\<close> that by auto
        show "h ` ({0..1} \<times> {y}) \<subseteq> S"
          using \<open>y \<in> V i\<close> assms(3) VU that by fastforce
        show "continuous_on ({0..1} \<times> {y}) (fs i)"
          using continuous_on_subset [OF contfs] \<open>i \<in> U\<close>
          by (simp add: \<open>y \<in> V i\<close> subset_iff)
        show "fs i ` ({0..1} \<times> {y}) \<subseteq> C"
          using "*" \<open>y \<in> V i\<close> \<open>i \<in> U\<close> by fastforce
        show "\<And>x. x \<in> {0..1} \<times> {y} \<Longrightarrow> h x = p (fs i x)"
          using "*" \<open>y \<in> V i\<close> \<open>i \<in> U\<close> by blast
        show "continuous_on ({0..1} \<times> {y}) (fs j)"
          using continuous_on_subset [OF contfs] \<open>j \<in> U\<close>
          by (simp add: \<open>y \<in> V j\<close> subset_iff)
        show "fs j ` ({0..1} \<times> {y}) \<subseteq> C"
          using "*" \<open>y \<in> V j\<close> \<open>j \<in> U\<close> by fastforce
        show "\<And>x. x \<in> {0..1} \<times> {y} \<Longrightarrow> h x = p (fs j x)"
          using "*" \<open>y \<in> V j\<close> \<open>j \<in> U\<close> by blast
        show "connected ({0..1::real} \<times> {y})"
          using connected_Icc connected_Times connected_sing by blast
        show "(0, y) \<in> {0..1::real} \<times> {y}"
          by force
        show "x \<in> {0..1} \<times> {y}"
          using \<open>x = (u, y)\<close> x by blast
      qed
    qed
  qed blast
  show ?thesis
  proof
    show "k ` ({0..1} \<times> U) \<subseteq> C"
      using V*k VU by fastforce
    show "\<And>y. y \<in> U \<Longrightarrow> k (0, y) = f y"
      by (simp add: V*k)
    show "\<And>z. z \<in> {0..1} \<times> U \<Longrightarrow> h z = p (k z)"
      using V*k by auto
  qed (auto simp: contk)
qed

corollary%important covering_space_lift_homotopy_alt:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and h :: "'c::real_normed_vector \<times> real \<Rightarrow> 'b"
  assumes cov: "covering_space C p S"
      and conth: "continuous_on (U \<times> {0..1}) h"
      and him: "h ` (U \<times> {0..1}) \<subseteq> S"
      and heq: "\<And>y. y \<in> U \<Longrightarrow> h (y,0) = p(f y)"
      and contf: "continuous_on U f" and fim: "f ` U \<subseteq> C"
  obtains k where "continuous_on (U \<times> {0..1}) k"
                  "k ` (U \<times> {0..1}) \<subseteq> C"
                  "\<And>y. y \<in> U \<Longrightarrow> k(y, 0) = f y"
                  "\<And>z. z \<in> U \<times> {0..1} \<Longrightarrow> h z = p(k z)"
proof%unimportant -
  have "continuous_on ({0..1} \<times> U) (h \<circ> (\<lambda>z. (snd z, fst z)))"
    by (intro continuous_intros continuous_on_subset [OF conth]) auto
  then obtain k where contk: "continuous_on ({0..1} \<times> U) k"
                  and kim:  "k ` ({0..1} \<times> U) \<subseteq> C"
                  and k0: "\<And>y. y \<in> U \<Longrightarrow> k(0, y) = f y"
                  and heqp: "\<And>z. z \<in> {0..1} \<times> U \<Longrightarrow> (h \<circ> (\<lambda>z. Pair (snd z) (fst z))) z = p(k z)"
    apply (rule covering_space_lift_homotopy [OF cov _ _ _ contf fim])
    using him  by (auto simp: contf heq)
  show ?thesis
    apply (rule_tac k="k \<circ> (\<lambda>z. Pair (snd z) (fst z))" in that)
       apply (intro continuous_intros continuous_on_subset [OF contk])
    using kim heqp apply (auto simp: k0)
    done
qed

corollary%important covering_space_lift_homotopic_function:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" and g:: "'c::real_normed_vector \<Rightarrow> 'a"
  assumes cov: "covering_space C p S"
      and contg: "continuous_on U g"
      and gim: "g ` U \<subseteq> C"
      and pgeq: "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
      and hom: "homotopic_with (\<lambda>x. True) U S f f'"
    obtains g' where "continuous_on U g'" "image g' U \<subseteq> C" "\<And>y. y \<in> U \<Longrightarrow> p(g' y) = f' y"
proof%unimportant -
  obtain h where conth: "continuous_on ({0..1::real} \<times> U) h"
             and him: "h ` ({0..1} \<times> U) \<subseteq> S"
             and h0:  "\<And>x. h(0, x) = f x"
             and h1: "\<And>x. h(1, x) = f' x"
    using hom by (auto simp: homotopic_with_def)
  have "\<And>y. y \<in> U \<Longrightarrow> h (0, y) = p (g y)"
    by (simp add: h0 pgeq)
  then obtain k where contk: "continuous_on ({0..1} \<times> U) k"
                  and kim: "k ` ({0..1} \<times> U) \<subseteq> C"
                  and k0: "\<And>y. y \<in> U \<Longrightarrow> k(0, y) = g y"
                  and heq: "\<And>z. z \<in> {0..1} \<times> U \<Longrightarrow> h z = p(k z)"
    using covering_space_lift_homotopy [OF cov conth him _ contg gim] by metis
  show ?thesis
  proof
    show "continuous_on U (k \<circ> Pair 1)"
      by (meson contk atLeastAtMost_iff continuous_on_o_Pair order_refl zero_le_one)
    show "(k \<circ> Pair 1) ` U \<subseteq> C"
      using kim by auto
    show "\<And>y. y \<in> U \<Longrightarrow> p ((k \<circ> Pair 1) y) = f' y"
      by (auto simp: h1 heq [symmetric])
  qed
qed

corollary%important covering_space_lift_inessential_function:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" and U :: "'c::real_normed_vector set"
  assumes cov: "covering_space C p S"
      and hom: "homotopic_with (\<lambda>x. True) U S f (\<lambda>x. a)"
  obtains g where "continuous_on U g" "g ` U \<subseteq> C" "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
proof%unimportant (cases "U = {}")
  case True
  then show ?thesis
    using that continuous_on_empty by blast
next
  case False
  then obtain b where b: "b \<in> C" "p b = a"
    using covering_space_imp_surjective [OF cov] homotopic_with_imp_subset2 [OF hom]
    by auto
  then have gim: "(\<lambda>y. b) ` U \<subseteq> C"
    by blast
  show ?thesis
    apply (rule covering_space_lift_homotopic_function
                  [OF cov continuous_on_const gim _ homotopic_with_symD [OF hom]])
    using b that apply auto
    done
qed

subsection%important\<open> Lifting of general functions to covering space\<close>

proposition%important covering_space_lift_path_strong:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and f :: "'c::real_normed_vector \<Rightarrow> 'b"
  assumes cov: "covering_space C p S" and "a \<in> C"
      and "path g" and pag: "path_image g \<subseteq> S" and pas: "pathstart g = p a"
    obtains h where "path h" "path_image h \<subseteq> C" "pathstart h = a"
                and "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h t) = g t"
proof%unimportant -
  obtain k:: "real \<times> 'c \<Rightarrow> 'a"
    where contk: "continuous_on ({0..1} \<times> {undefined}) k"
      and kim: "k ` ({0..1} \<times> {undefined}) \<subseteq> C"
      and k0:  "k (0, undefined) = a"
      and pk: "\<And>z. z \<in> {0..1} \<times> {undefined} \<Longrightarrow> p(k z) = (g \<circ> fst) z"
  proof (rule covering_space_lift_homotopy [OF cov, of "{undefined}" "g \<circ> fst"])
    show "continuous_on ({0..1::real} \<times> {undefined::'c}) (g \<circ> fst)"
      apply (intro continuous_intros)
      using \<open>path g\<close> by (simp add: path_def)
    show "(g \<circ> fst) ` ({0..1} \<times> {undefined}) \<subseteq> S"
      using pag by (auto simp: path_image_def)
    show "(g \<circ> fst) (0, y) = p a" if "y \<in> {undefined}" for y::'c
      by (metis comp_def fst_conv pas pathstart_def)
  qed (use assms in auto)
  show ?thesis
  proof
    show "path (k \<circ> (\<lambda>t. Pair t undefined))"
      unfolding path_def
      by (intro continuous_on_compose continuous_intros continuous_on_subset [OF contk]) auto
    show "path_image (k \<circ> (\<lambda>t. (t, undefined))) \<subseteq> C"
      using kim by (auto simp: path_image_def)
    show "pathstart (k \<circ> (\<lambda>t. (t, undefined))) = a"
      by (auto simp: pathstart_def k0)
    show "\<And>t. t \<in> {0..1} \<Longrightarrow> p ((k \<circ> (\<lambda>t. (t, undefined))) t) = g t"
      by (auto simp: pk)
  qed
qed

corollary%important covering_space_lift_path:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes cov: "covering_space C p S" and "path g" and pig: "path_image g \<subseteq> S"
  obtains h where "path h" "path_image h \<subseteq> C" "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h t) = g t"
proof%unimportant -
  obtain a where "a \<in> C" "pathstart g = p a"
    by (metis pig cov covering_space_imp_surjective imageE pathstart_in_path_image subsetCE)
  show ?thesis
    using covering_space_lift_path_strong [OF cov \<open>a \<in> C\<close> \<open>path g\<close> pig]
    by (metis \<open>pathstart g = p a\<close> that)
qed

  
proposition%important covering_space_lift_homotopic_paths:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes cov: "covering_space C p S"
      and "path g1" and pig1: "path_image g1 \<subseteq> S"
      and "path g2" and pig2: "path_image g2 \<subseteq> S"
      and hom: "homotopic_paths S g1 g2"
      and "path h1" and pih1: "path_image h1 \<subseteq> C" and ph1: "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h1 t) = g1 t"
      and "path h2" and pih2: "path_image h2 \<subseteq> C" and ph2: "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h2 t) = g2 t"
      and h1h2: "pathstart h1 = pathstart h2"
    shows "homotopic_paths C h1 h2"
proof%unimportant -
  obtain h :: "real \<times> real \<Rightarrow> 'b"
     where conth: "continuous_on ({0..1} \<times> {0..1}) h"
       and him: "h ` ({0..1} \<times> {0..1}) \<subseteq> S"
       and h0: "\<And>x. h (0, x) = g1 x" and h1: "\<And>x. h (1, x) = g2 x"
       and heq0: "\<And>t. t \<in> {0..1} \<Longrightarrow> h (t, 0) = g1 0"
       and heq1: "\<And>t. t \<in> {0..1} \<Longrightarrow> h (t, 1) = g1 1"
    using hom by (auto simp: homotopic_paths_def homotopic_with_def pathstart_def pathfinish_def)
  obtain k where contk: "continuous_on ({0..1} \<times> {0..1}) k"
             and kim: "k ` ({0..1} \<times> {0..1}) \<subseteq> C"
             and kh2: "\<And>y. y \<in> {0..1} \<Longrightarrow> k (y, 0) = h2 0"
             and hpk: "\<And>z. z \<in> {0..1} \<times> {0..1} \<Longrightarrow> h z = p (k z)"
    apply (rule covering_space_lift_homotopy_alt [OF cov conth him, of "\<lambda>x. h2 0"])
    using h1h2 ph1 ph2 apply (force simp: heq0 pathstart_def pathfinish_def)
    using path_image_def pih2 continuous_on_const by fastforce+
  have contg1: "continuous_on {0..1} g1" and contg2: "continuous_on {0..1} g2"
    using \<open>path g1\<close> \<open>path g2\<close> path_def by blast+
  have g1im: "g1 ` {0..1} \<subseteq> S" and g2im: "g2 ` {0..1} \<subseteq> S"
    using path_image_def pig1 pig2 by auto
  have conth1: "continuous_on {0..1} h1" and conth2: "continuous_on {0..1} h2"
    using \<open>path h1\<close> \<open>path h2\<close> path_def by blast+
  have h1im: "h1 ` {0..1} \<subseteq> C" and h2im: "h2 ` {0..1} \<subseteq> C"
    using path_image_def pih1 pih2 by auto
  show ?thesis
    unfolding homotopic_paths pathstart_def pathfinish_def
  proof (intro exI conjI ballI)
    show keqh1: "k(0, x) = h1 x" if "x \<in> {0..1}" for x
    proof (rule covering_space_lift_unique [OF cov _ contg1 g1im])
      show "k (0,0) = h1 0"
        by (metis atLeastAtMost_iff h1h2 kh2 order_refl pathstart_def zero_le_one)
      show "continuous_on {0..1} (\<lambda>a. k (0, a))"
        by (intro continuous_intros continuous_on_compose2 [OF contk]) auto
      show "\<And>x. x \<in> {0..1} \<Longrightarrow> g1 x = p (k (0, x))"
        by (metis atLeastAtMost_iff h0 hpk zero_le_one mem_Sigma_iff order_refl)
    qed (use conth1 h1im kim that in \<open>auto simp: ph1\<close>)
    show "k(1, x) = h2 x" if "x \<in> {0..1}" for x
    proof (rule covering_space_lift_unique [OF cov _ contg2 g2im])
      show "k (1,0) = h2 0"
        by (metis atLeastAtMost_iff kh2 order_refl zero_le_one)
      show "continuous_on {0..1} (\<lambda>a. k (1, a))"
        by (intro continuous_intros continuous_on_compose2 [OF contk]) auto
      show "\<And>x. x \<in> {0..1} \<Longrightarrow> g2 x = p (k (1, x))"
        by (metis atLeastAtMost_iff h1 hpk mem_Sigma_iff order_refl zero_le_one)
    qed (use conth2 h2im kim that in \<open>auto simp: ph2\<close>)
    show "\<And>t. t \<in> {0..1} \<Longrightarrow> (k \<circ> Pair t) 0 = h1 0"
      by (metis comp_apply h1h2 kh2 pathstart_def)
    show "(k \<circ> Pair t) 1 = h1 1" if "t \<in> {0..1}" for t
    proof (rule covering_space_lift_unique
           [OF cov, of "\<lambda>a. (k \<circ> Pair a) 1" 0 "\<lambda>a. h1 1" "{0..1}"  "\<lambda>x. g1 1"])
      show "(k \<circ> Pair 0) 1 = h1 1"
        using keqh1 by auto
      show "continuous_on {0..1} (\<lambda>a. (k \<circ> Pair a) 1)"
        apply simp
        by (intro continuous_intros continuous_on_compose2 [OF contk]) auto
      show "\<And>x. x \<in> {0..1} \<Longrightarrow> g1 1 = p ((k \<circ> Pair x) 1)"
        using heq1 hpk by auto
    qed (use contk kim g1im h1im that in \<open>auto simp: ph1 continuous_on_const\<close>)
  qed (use contk kim in auto)
qed


corollary%important covering_space_monodromy:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes cov: "covering_space C p S"
      and "path g1" and pig1: "path_image g1 \<subseteq> S"
      and "path g2" and pig2: "path_image g2 \<subseteq> S"
      and hom: "homotopic_paths S g1 g2"
      and "path h1" and pih1: "path_image h1 \<subseteq> C" and ph1: "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h1 t) = g1 t"
      and "path h2" and pih2: "path_image h2 \<subseteq> C" and ph2: "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h2 t) = g2 t"
      and h1h2: "pathstart h1 = pathstart h2"
    shows "pathfinish h1 = pathfinish h2"
  using%unimportant covering_space_lift_homotopic_paths [OF assms] homotopic_paths_imp_pathfinish
  by%unimportant blast


corollary%important covering_space_lift_homotopic_path:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes cov: "covering_space C p S"
      and hom: "homotopic_paths S f f'"
      and "path g" and pig: "path_image g \<subseteq> C"
      and a: "pathstart g = a" and b: "pathfinish g = b"
      and pgeq: "\<And>t. t \<in> {0..1} \<Longrightarrow> p(g t) = f t"
  obtains g' where "path g'" "path_image g' \<subseteq> C"
                   "pathstart g' = a" "pathfinish g' = b" "\<And>t. t \<in> {0..1} \<Longrightarrow> p(g' t) = f' t"
proof%unimportant (rule covering_space_lift_path_strong [OF cov, of a f'])
  show "a \<in> C"
    using a pig by auto
  show "path f'" "path_image f' \<subseteq> S"
    using hom homotopic_paths_imp_path homotopic_paths_imp_subset by blast+
  show "pathstart f' = p a"
    by (metis a atLeastAtMost_iff hom homotopic_paths_imp_pathstart order_refl pathstart_def pgeq zero_le_one)
qed (metis (mono_tags, lifting) assms cov covering_space_monodromy hom homotopic_paths_imp_path homotopic_paths_imp_subset pgeq pig)


proposition%important covering_space_lift_general:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and f :: "'c::real_normed_vector \<Rightarrow> 'b"
  assumes cov: "covering_space C p S" and "a \<in> C" "z \<in> U"
      and U: "path_connected U" "locally path_connected U"
      and contf: "continuous_on U f" and fim: "f ` U \<subseteq> S"
      and feq: "f z = p a"
      and hom: "\<And>r. \<lbrakk>path r; path_image r \<subseteq> U; pathstart r = z; pathfinish r = z\<rbrakk>
                     \<Longrightarrow> \<exists>q. path q \<and> path_image q \<subseteq> C \<and>
                             pathstart q = a \<and> pathfinish q = a \<and>
                             homotopic_paths S (f \<circ> r) (p \<circ> q)"
  obtains g where "continuous_on U g" "g ` U \<subseteq> C" "g z = a" "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
proof%unimportant -
  have *: "\<exists>g h. path g \<and> path_image g \<subseteq> U \<and>
                 pathstart g = z \<and> pathfinish g = y \<and>
                 path h \<and> path_image h \<subseteq> C \<and> pathstart h = a \<and>
                 (\<forall>t \<in> {0..1}. p(h t) = f(g t))"
          if "y \<in> U" for y
  proof -
    obtain g where "path g" "path_image g \<subseteq> U" and pastg: "pathstart g = z"
               and pafig: "pathfinish g = y"
      using U \<open>z \<in> U\<close> \<open>y \<in> U\<close> by (force simp: path_connected_def)
    obtain h where "path h" "path_image h \<subseteq> C" "pathstart h = a"
               and "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h t) = (f \<circ> g) t"
    proof (rule covering_space_lift_path_strong [OF cov \<open>a \<in> C\<close>])
      show "path (f \<circ> g)"
        using \<open>path g\<close> \<open>path_image g \<subseteq> U\<close> contf continuous_on_subset path_continuous_image by blast
      show "path_image (f \<circ> g) \<subseteq> S"
        by (metis \<open>path_image g \<subseteq> U\<close> fim image_mono path_image_compose subset_trans)
      show "pathstart (f \<circ> g) = p a"
        by (simp add: feq pastg pathstart_compose)
    qed auto
    then show ?thesis
      by (metis \<open>path g\<close> \<open>path_image g \<subseteq> U\<close> comp_apply pafig pastg)
  qed
  have "\<exists>l. \<forall>g h. path g \<and> path_image g \<subseteq> U \<and> pathstart g = z \<and> pathfinish g = y \<and>
                  path h \<and> path_image h \<subseteq> C \<and> pathstart h = a \<and>
                  (\<forall>t \<in> {0..1}. p(h t) = f(g t))  \<longrightarrow> pathfinish h = l" for y
  proof -
    have "pathfinish h = pathfinish h'"
         if g: "path g" "path_image g \<subseteq> U" "pathstart g = z" "pathfinish g = y"
            and h: "path h" "path_image h \<subseteq> C" "pathstart h = a"
            and phg: "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h t) = f(g t)"
            and g': "path g'" "path_image g' \<subseteq> U" "pathstart g' = z" "pathfinish g' = y"
            and h': "path h'" "path_image h' \<subseteq> C" "pathstart h' = a"
            and phg': "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h' t) = f(g' t)"
         for g h g' h'
    proof -
      obtain q where "path q" and piq: "path_image q \<subseteq> C" and pastq: "pathstart q = a" and pafiq: "pathfinish q = a"
                 and homS: "homotopic_paths S (f \<circ> g +++ reversepath g') (p \<circ> q)"
        using g g' hom [of "g +++ reversepath g'"] by (auto simp:  subset_path_image_join)
              have papq: "path (p \<circ> q)"
                using homS homotopic_paths_imp_path by blast
              have pipq: "path_image (p \<circ> q) \<subseteq> S"
                using homS homotopic_paths_imp_subset by blast
      obtain q' where "path q'" "path_image q' \<subseteq> C"
                and "pathstart q' = pathstart q" "pathfinish q' = pathfinish q"
                and pq'_eq: "\<And>t. t \<in> {0..1} \<Longrightarrow> p (q' t) = (f \<circ> g +++ reversepath g') t"
        using covering_space_lift_homotopic_path [OF cov homotopic_paths_sym [OF homS] \<open>path q\<close> piq refl refl]
        by auto
      have "q' t = (h \<circ> (*\<^sub>R) 2) t" if "0 \<le> t" "t \<le> 1/2" for t
      proof (rule covering_space_lift_unique [OF cov, of q' 0 "h \<circ> (*\<^sub>R) 2" "{0..1/2}" "f \<circ> g \<circ> (*\<^sub>R) 2" t])
        show "q' 0 = (h \<circ> (*\<^sub>R) 2) 0"
          by (metis \<open>pathstart q' = pathstart q\<close> comp_def g h pastq pathstart_def pth_4(2))
        show "continuous_on {0..1/2} (f \<circ> g \<circ> (*\<^sub>R) 2)"
          apply (intro continuous_intros continuous_on_compose continuous_on_path [OF \<open>path g\<close>] continuous_on_subset [OF contf])
          using g(2) path_image_def by fastforce+
        show "(f \<circ> g \<circ> (*\<^sub>R) 2) ` {0..1/2} \<subseteq> S"
          using g(2) path_image_def fim by fastforce
        show "(h \<circ> (*\<^sub>R) 2) ` {0..1/2} \<subseteq> C"
          using h path_image_def by fastforce
        show "q' ` {0..1/2} \<subseteq> C"
          using \<open>path_image q' \<subseteq> C\<close> path_image_def by fastforce
        show "\<And>x. x \<in> {0..1/2} \<Longrightarrow> (f \<circ> g \<circ> (*\<^sub>R) 2) x = p (q' x)"
          by (auto simp: joinpaths_def pq'_eq)
        show "\<And>x. x \<in> {0..1/2} \<Longrightarrow> (f \<circ> g \<circ> (*\<^sub>R) 2) x = p ((h \<circ> (*\<^sub>R) 2) x)"
          by (simp add: phg)
        show "continuous_on {0..1/2} q'"
          by (simp add: continuous_on_path \<open>path q'\<close>)
        show "continuous_on {0..1/2} (h \<circ> (*\<^sub>R) 2)"
          apply (intro continuous_intros continuous_on_compose continuous_on_path [OF \<open>path h\<close>], force)
          done
      qed (use that in auto)
      moreover have "q' t = (reversepath h' \<circ> (\<lambda>t. 2 *\<^sub>R t - 1)) t" if "1/2 < t" "t \<le> 1" for t
      proof (rule covering_space_lift_unique [OF cov, of q' 1 "reversepath h' \<circ> (\<lambda>t. 2 *\<^sub>R t - 1)" "{1/2<..1}" "f \<circ> reversepath g' \<circ> (\<lambda>t. 2 *\<^sub>R t - 1)" t])
        show "q' 1 = (reversepath h' \<circ> (\<lambda>t. 2 *\<^sub>R t - 1)) 1"
          using h' \<open>pathfinish q' = pathfinish q\<close> pafiq
          by (simp add: pathstart_def pathfinish_def reversepath_def)
        show "continuous_on {1/2<..1} (f \<circ> reversepath g' \<circ> (\<lambda>t. 2 *\<^sub>R t - 1))"
          apply (intro continuous_intros continuous_on_compose continuous_on_path \<open>path g'\<close> continuous_on_subset [OF contf])
          using g' apply simp_all
          by (auto simp: path_image_def reversepath_def)
        show "(f \<circ> reversepath g' \<circ> (\<lambda>t. 2 *\<^sub>R t - 1)) ` {1/2<..1} \<subseteq> S"
          using g'(2) path_image_def fim by (auto simp: image_subset_iff path_image_def reversepath_def)
        show "q' ` {1/2<..1} \<subseteq> C"
          using \<open>path_image q' \<subseteq> C\<close> path_image_def by fastforce
        show "(reversepath h' \<circ> (\<lambda>t. 2 *\<^sub>R t - 1)) ` {1/2<..1} \<subseteq> C"
          using h' by (simp add: path_image_def reversepath_def subset_eq)
        show "\<And>x. x \<in> {1/2<..1} \<Longrightarrow> (f \<circ> reversepath g' \<circ> (\<lambda>t. 2 *\<^sub>R t - 1)) x = p (q' x)"
          by (auto simp: joinpaths_def pq'_eq)
        show "\<And>x. x \<in> {1/2<..1} \<Longrightarrow>
                  (f \<circ> reversepath g' \<circ> (\<lambda>t. 2 *\<^sub>R t - 1)) x = p ((reversepath h' \<circ> (\<lambda>t. 2 *\<^sub>R t - 1)) x)"
          by (simp add: phg' reversepath_def)
        show "continuous_on {1/2<..1} q'"
          by (auto intro: continuous_on_path [OF \<open>path q'\<close>])
        show "continuous_on {1/2<..1} (reversepath h' \<circ> (\<lambda>t. 2 *\<^sub>R t - 1))"
          apply (intro continuous_intros continuous_on_compose continuous_on_path \<open>path h'\<close>)
          using h' apply auto
          done
      qed (use that in auto)
      ultimately have "q' t = (h +++ reversepath h') t" if "0 \<le> t" "t \<le> 1" for t
        using that by (simp add: joinpaths_def)
      then have "path(h +++ reversepath h')"
        by (auto intro: path_eq [OF \<open>path q'\<close>])
      then show ?thesis
        by (auto simp: \<open>path h\<close> \<open>path h'\<close>)
    qed
    then show ?thesis by metis
  qed
  then obtain l :: "'c \<Rightarrow> 'a"
          where l: "\<And>y g h. \<lbrakk>path g; path_image g \<subseteq> U; pathstart g = z; pathfinish g = y;
                             path h; path_image h \<subseteq> C; pathstart h = a;
                             \<And>t. t \<in> {0..1} \<Longrightarrow> p(h t) = f(g t)\<rbrakk> \<Longrightarrow> pathfinish h = l y"
    by metis
  show ?thesis
  proof
    show pleq: "p (l y) = f y" if "y \<in> U" for y
      using*[OF \<open>y \<in> U\<close>]  by (metis l atLeastAtMost_iff order_refl pathfinish_def zero_le_one)
    show "l z = a"
      using l [of "linepath z z" z "linepath a a"] by (auto simp: assms)
    show LC: "l ` U \<subseteq> C"
      by (clarify dest!: *) (metis (full_types) l pathfinish_in_path_image subsetCE)
    have "\<exists>T. openin (subtopology euclidean U) T \<and> y \<in> T \<and> T \<subseteq> U \<inter> l -` X"
         if X: "openin (subtopology euclidean C) X" and "y \<in> U" "l y \<in> X" for X y
    proof -
      have "X \<subseteq> C"
        using X openin_euclidean_subtopology_iff by blast
      have "f y \<in> S"
        using fim \<open>y \<in> U\<close> by blast
      then obtain W \<V>
              where WV: "f y \<in> W \<and> openin (subtopology euclidean S) W \<and>
                         (\<Union>\<V> = C \<inter> p -` W \<and>
                          (\<forall>U \<in> \<V>. openin (subtopology euclidean C) U) \<and>
                          pairwise disjnt \<V> \<and>
                          (\<forall>U \<in> \<V>. \<exists>q. homeomorphism U W p q))"
        using cov by (force simp: covering_space_def)
      then have "l y \<in> \<Union>\<V>"
        using \<open>X \<subseteq> C\<close> pleq that by auto
      then obtain W' where "l y \<in> W'" and "W' \<in> \<V>"
        by blast
      with WV obtain p' where opeCW': "openin (subtopology euclidean C) W'"
                          and homUW': "homeomorphism W' W p p'"
        by blast
      then have contp': "continuous_on W p'" and p'im: "p' ` W \<subseteq> W'"
        using homUW' homeomorphism_image2 homeomorphism_cont2 by fastforce+
      obtain V where "y \<in> V" "y \<in> U" and fimW: "f ` V \<subseteq> W" "V \<subseteq> U"
                 and "path_connected V" and opeUV: "openin (subtopology euclidean U) V"
      proof -
        have "openin (subtopology euclidean U) (U \<inter> f -` W)"
          using WV contf continuous_on_open_gen fim by auto
        then show ?thesis
          using U WV
          apply (auto simp: locally_path_connected)
          apply (drule_tac x="U \<inter> f -` W" in spec)
          apply (drule_tac x=y in spec)
          apply (auto simp: \<open>y \<in> U\<close> intro: that)
          done
      qed
      have "W' \<subseteq> C" "W \<subseteq> S"
        using opeCW' WV openin_imp_subset by auto
      have p'im: "p' ` W \<subseteq> W'"
        using homUW' homeomorphism_image2 by fastforce
      show ?thesis
      proof (intro exI conjI)
        have "openin (subtopology euclidean S) (W \<inter> p' -` (W' \<inter> X))"
        proof (rule openin_trans)
          show "openin (subtopology euclidean W) (W \<inter> p' -` (W' \<inter> X))"
            apply (rule continuous_openin_preimage [OF contp' p'im])
            using X \<open>W' \<subseteq> C\<close> apply (auto simp: openin_open)
            done
          show "openin (subtopology euclidean S) W"
            using WV by blast
        qed
        then show "openin (subtopology euclidean U) (V \<inter> (U \<inter> (f -` (W \<inter> (p' -` (W' \<inter> X))))))"
          by (blast intro: opeUV openin_subtopology_self continuous_openin_preimage [OF contf fim])
         have "p' (f y) \<in> X"
          using \<open>l y \<in> W'\<close> homeomorphism_apply1 [OF homUW'] pleq \<open>y \<in> U\<close> \<open>l y \<in> X\<close> by fastforce
        then show "y \<in> V \<inter> (U \<inter> f -` (W \<inter> p' -` (W' \<inter> X)))"
          using \<open>y \<in> U\<close> \<open>y \<in> V\<close> WV p'im by auto
        show "V \<inter> (U \<inter> f -` (W \<inter> p' -` (W' \<inter> X))) \<subseteq> U \<inter> l -` X"
        proof (intro subsetI IntI; clarify)
          fix y'
          assume y': "y' \<in> V" "y' \<in> U" "f y' \<in> W" "p' (f y') \<in> W'" "p' (f y') \<in> X"
          then obtain \<gamma> where "path \<gamma>" "path_image \<gamma> \<subseteq> V" "pathstart \<gamma> = y" "pathfinish \<gamma> = y'"
            by (meson \<open>path_connected V\<close> \<open>y \<in> V\<close> path_connected_def)
          obtain pp qq where "path pp" "path_image pp \<subseteq> U"
                             "pathstart pp = z" "pathfinish pp = y"
                             "path qq" "path_image qq \<subseteq> C" "pathstart qq = a"
                         and pqqeq: "\<And>t. t \<in> {0..1} \<Longrightarrow> p(qq t) = f(pp t)"
            using*[OF \<open>y \<in> U\<close>] by blast
          have finW: "\<And>x. \<lbrakk>0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> f (\<gamma> x) \<in> W"
            using \<open>path_image \<gamma> \<subseteq> V\<close> by (auto simp: image_subset_iff path_image_def fimW [THEN subsetD])
          have "pathfinish (qq +++ (p' \<circ> f \<circ> \<gamma>)) = l y'"
          proof (rule l [of "pp +++ \<gamma>" y' "qq +++ (p' \<circ> f \<circ> \<gamma>)"])
            show "path (pp +++ \<gamma>)"
              by (simp add: \<open>path \<gamma>\<close> \<open>path pp\<close> \<open>pathfinish pp = y\<close> \<open>pathstart \<gamma> = y\<close>)
            show "path_image (pp +++ \<gamma>) \<subseteq> U"
              using \<open>V \<subseteq> U\<close> \<open>path_image \<gamma> \<subseteq> V\<close> \<open>path_image pp \<subseteq> U\<close> not_in_path_image_join by blast
            show "pathstart (pp +++ \<gamma>) = z"
              by (simp add: \<open>pathstart pp = z\<close>)
            show "pathfinish (pp +++ \<gamma>) = y'"
              by (simp add: \<open>pathfinish \<gamma> = y'\<close>)
            have paqq: "pathfinish qq = pathstart (p' \<circ> f \<circ> \<gamma>)"
              apply (simp add: \<open>pathstart \<gamma> = y\<close> pathstart_compose)
              apply (metis (mono_tags, lifting) \<open>l y \<in> W'\<close> \<open>path pp\<close> \<open>path qq\<close> \<open>path_image pp \<subseteq> U\<close> \<open>path_image qq \<subseteq> C\<close>
                           \<open>pathfinish pp = y\<close> \<open>pathstart pp = z\<close> \<open>pathstart qq = a\<close>
                           homeomorphism_apply1 [OF homUW'] l pleq pqqeq \<open>y \<in> U\<close>)
              done
            have "continuous_on (path_image \<gamma>) (p' \<circ> f)"
            proof (rule continuous_on_compose)
              show "continuous_on (path_image \<gamma>) f"
                using \<open>path_image \<gamma> \<subseteq> V\<close> \<open>V \<subseteq> U\<close> contf continuous_on_subset by blast
              show "continuous_on (f ` path_image \<gamma>) p'"
                apply (rule continuous_on_subset [OF contp'])
                apply (auto simp: path_image_def pathfinish_def pathstart_def finW)
                done
            qed
            then show "path (qq +++ (p' \<circ> f \<circ> \<gamma>))"
              using \<open>path \<gamma>\<close> \<open>path qq\<close> paqq path_continuous_image path_join_imp by blast
            show "path_image (qq +++ (p' \<circ> f \<circ> \<gamma>)) \<subseteq> C"
              apply (rule subset_path_image_join)
               apply (simp add: \<open>path_image qq \<subseteq> C\<close>)
              by (metis \<open>W' \<subseteq> C\<close> \<open>path_image \<gamma> \<subseteq> V\<close> dual_order.trans fimW(1) image_comp image_mono p'im path_image_compose)
            show "pathstart (qq +++ (p' \<circ> f \<circ> \<gamma>)) = a"
              by (simp add: \<open>pathstart qq = a\<close>)
            show "p ((qq +++ (p' \<circ> f \<circ> \<gamma>)) \<xi>) = f ((pp +++ \<gamma>) \<xi>)" if \<xi>: "\<xi> \<in> {0..1}" for \<xi>
            proof (simp add: joinpaths_def, safe)
              show "p (qq (2*\<xi>)) = f (pp (2*\<xi>))" if "\<xi>*2 \<le> 1"
                using \<open>\<xi> \<in> {0..1}\<close> pqqeq that by auto
              show "p (p' (f (\<gamma> (2*\<xi> - 1)))) = f (\<gamma> (2*\<xi> - 1))" if "\<not> \<xi>*2 \<le> 1"
                apply (rule homeomorphism_apply2 [OF homUW' finW])
                using that \<xi> by auto
            qed
          qed
          with \<open>pathfinish \<gamma> = y'\<close>  \<open>p' (f y') \<in> X\<close> show "y' \<in> l -` X"
            unfolding pathfinish_join by (simp add: pathfinish_def)
        qed
      qed
    qed
    then show "continuous_on U l"
      by (metis IntD1 IntD2 vimage_eq openin_subopen continuous_on_open_gen [OF LC])
  qed
qed


corollary%important covering_space_lift_stronger:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and f :: "'c::real_normed_vector \<Rightarrow> 'b"
  assumes cov: "covering_space C p S" "a \<in> C" "z \<in> U"
      and U: "path_connected U" "locally path_connected U"
      and contf: "continuous_on U f" and fim: "f ` U \<subseteq> S"
      and feq: "f z = p a"
      and hom: "\<And>r. \<lbrakk>path r; path_image r \<subseteq> U; pathstart r = z; pathfinish r = z\<rbrakk>
                     \<Longrightarrow> \<exists>b. homotopic_paths S (f \<circ> r) (linepath b b)"
  obtains g where "continuous_on U g" "g ` U \<subseteq> C" "g z = a" "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
proof%unimportant (rule covering_space_lift_general [OF cov U contf fim feq])
  fix r
  assume "path r" "path_image r \<subseteq> U" "pathstart r = z" "pathfinish r = z"
  then obtain b where b: "homotopic_paths S (f \<circ> r) (linepath b b)"
    using hom by blast
  then have "f (pathstart r) = b"
    by (metis homotopic_paths_imp_pathstart pathstart_compose pathstart_linepath)
  then have "homotopic_paths S (f \<circ> r) (linepath (f z) (f z))"
    by (simp add: b \<open>pathstart r = z\<close>)
  then have "homotopic_paths S (f \<circ> r) (p \<circ> linepath a a)"
    by (simp add: o_def feq linepath_def)
  then show "\<exists>q. path q \<and>
                  path_image q \<subseteq> C \<and>
                  pathstart q = a \<and> pathfinish q = a \<and> homotopic_paths S (f \<circ> r) (p \<circ> q)"
    by (force simp: \<open>a \<in> C\<close>)
qed auto

corollary%important covering_space_lift_strong:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and f :: "'c::real_normed_vector \<Rightarrow> 'b"
  assumes cov: "covering_space C p S" "a \<in> C" "z \<in> U"
      and scU: "simply_connected U" and lpcU: "locally path_connected U"
      and contf: "continuous_on U f" and fim: "f ` U \<subseteq> S"
      and feq: "f z = p a"
  obtains g where "continuous_on U g" "g ` U \<subseteq> C" "g z = a" "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
proof%unimportant (rule covering_space_lift_stronger [OF cov _ lpcU contf fim feq])
  show "path_connected U"
    using scU simply_connected_eq_contractible_loop_some by blast
  fix r
  assume r: "path r" "path_image r \<subseteq> U" "pathstart r = z" "pathfinish r = z"
  have "linepath (f z) (f z) = f \<circ> linepath z z"
    by (simp add: o_def linepath_def)
  then have "homotopic_paths S (f \<circ> r) (linepath (f z) (f z))"
    by (metis r contf fim homotopic_paths_continuous_image scU simply_connected_eq_contractible_path)
  then show "\<exists>b. homotopic_paths S (f \<circ> r) (linepath b b)"
    by blast
qed blast

corollary%important covering_space_lift:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and f :: "'c::real_normed_vector \<Rightarrow> 'b"
  assumes cov: "covering_space C p S"
      and U: "simply_connected U"  "locally path_connected U"
      and contf: "continuous_on U f" and fim: "f ` U \<subseteq> S"
    obtains g where "continuous_on U g" "g ` U \<subseteq> C" "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
proof%unimportant (cases "U = {}")
  case True
  with that show ?thesis by auto
next
  case False
  then obtain z where "z \<in> U" by blast
  then obtain a where "a \<in> C" "f z = p a"
    by (metis cov covering_space_imp_surjective fim image_iff image_subset_iff)
  then show ?thesis
    by (metis that covering_space_lift_strong [OF cov _ \<open>z \<in> U\<close> U contf fim])
qed

end
