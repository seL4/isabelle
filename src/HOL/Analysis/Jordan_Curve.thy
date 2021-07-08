(*  Title:      HOL/Analysis/Jordan_Curve.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section \<open>The Jordan Curve Theorem and Applications\<close>

theory Jordan_Curve
  imports Arcwise_Connected Further_Topology
begin

subsection\<open>Janiszewski's theorem\<close>

lemma Janiszewski_weak:
  fixes a b::complex
  assumes "compact S" "compact T" and conST: "connected(S \<inter> T)"
      and ccS: "connected_component (- S) a b" and ccT: "connected_component (- T) a b"
    shows "connected_component (- (S \<union> T)) a b"
proof -
  have [simp]: "a \<notin> S" "a \<notin> T" "b \<notin> S" "b \<notin> T"
    by (meson ComplD ccS ccT connected_component_in)+
  have clo: "closedin (top_of_set (S \<union> T)) S" "closedin (top_of_set (S \<union> T)) T"
    by (simp_all add: assms closed_subset compact_imp_closed)
  obtain g where contg: "continuous_on S g"
             and g: "\<And>x. x \<in> S \<Longrightarrow> exp (\<i>* of_real (g x)) = (x - a) /\<^sub>R cmod (x - a) / ((x - b) /\<^sub>R cmod (x - b))"
    using ccS \<open>compact S\<close>
    apply (simp add: Borsuk_maps_homotopic_in_connected_component_eq [symmetric])
    apply (subst (asm) homotopic_circlemaps_divide)
    apply (auto simp: inessential_eq_continuous_logarithm_circle)
    done
  obtain h where conth: "continuous_on T h"
             and h: "\<And>x. x \<in> T \<Longrightarrow> exp (\<i>* of_real (h x)) = (x - a) /\<^sub>R cmod (x - a) / ((x - b) /\<^sub>R cmod (x - b))"
    using ccT \<open>compact T\<close>
    apply (simp add: Borsuk_maps_homotopic_in_connected_component_eq [symmetric])
    apply (subst (asm) homotopic_circlemaps_divide)
    apply (auto simp: inessential_eq_continuous_logarithm_circle)
    done
  have "continuous_on (S \<union> T) (\<lambda>x. (x - a) /\<^sub>R cmod (x - a))" "continuous_on (S \<union> T) (\<lambda>x. (x - b) /\<^sub>R cmod (x - b))"
    by (intro continuous_intros; force)+
  moreover have "(\<lambda>x. (x - a) /\<^sub>R cmod (x - a)) ` (S \<union> T) \<subseteq> sphere 0 1" "(\<lambda>x. (x - b) /\<^sub>R cmod (x - b)) ` (S \<union> T) \<subseteq> sphere 0 1"
    by (auto simp: divide_simps)
  moreover have "\<exists>g. continuous_on (S \<union> T) g \<and>
                     (\<forall>x\<in>S \<union> T. (x - a) /\<^sub>R cmod (x - a) / ((x - b) /\<^sub>R cmod (x - b)) = exp (\<i>*complex_of_real (g x)))"
  proof (cases "S \<inter> T = {}")
    case True
    have "continuous_on (S \<union> T) (\<lambda>x. if x \<in> S then g x else h x)"
      apply (rule continuous_on_cases_local [OF clo contg conth])
      using True by auto
    then show ?thesis
      by (rule_tac x="(\<lambda>x. if x \<in> S then g x else h x)" in exI) (auto simp: g h)
  next
    case False
    have diffpi: "\<exists>n. g x = h x + 2* of_int n*pi" if "x \<in> S \<inter> T" for x
    proof -
      have "exp (\<i>* of_real (g x)) = exp (\<i>* of_real (h x))"
        using that by (simp add: g h)
      then obtain n where "complex_of_real (g x) = complex_of_real (h x) + 2* of_int n*complex_of_real pi"
        apply (auto simp: exp_eq)
        by (metis complex_i_not_zero distrib_left mult.commute mult_cancel_left)
      then show ?thesis
        apply (rule_tac x=n in exI)
        using of_real_eq_iff by fastforce
    qed
    have contgh: "continuous_on (S \<inter> T) (\<lambda>x. g x - h x)"
      by (intro continuous_intros continuous_on_subset [OF contg] continuous_on_subset [OF conth]) auto
    moreover have disc:
          "\<exists>e>0. \<forall>y. y \<in> S \<inter> T \<and> g y - h y \<noteq> g x - h x \<longrightarrow> e \<le> norm ((g y - h y) - (g x - h x))"
          if "x \<in> S \<inter> T" for x
    proof -
      obtain nx where nx: "g x = h x + 2* of_int nx*pi"
        using \<open>x \<in> S \<inter> T\<close> diffpi by blast
      have "2*pi \<le> norm (g y - h y - (g x - h x))" if y: "y \<in> S \<inter> T" and neq: "g y - h y \<noteq> g x - h x" for y
      proof -
        obtain ny where ny: "g y = h y + 2* of_int ny*pi"
          using \<open>y \<in> S \<inter> T\<close> diffpi by blast
        { assume "nx \<noteq> ny"
          then have "1 \<le> \<bar>real_of_int ny - real_of_int nx\<bar>"
            by linarith
          then have "(2*pi)*1 \<le> (2*pi)*\<bar>real_of_int ny - real_of_int nx\<bar>"
            by simp
          also have "... = \<bar>2*real_of_int ny*pi - 2*real_of_int nx*pi\<bar>"
            by (simp add: algebra_simps abs_if)
          finally have "2*pi \<le> \<bar>2*real_of_int ny*pi - 2*real_of_int nx*pi\<bar>" by simp
        }
        with neq show ?thesis
          by (simp add: nx ny)
      qed
      then show ?thesis
        by (rule_tac x="2*pi" in exI) auto
    qed
    ultimately have "(\<lambda>x. g x - h x) constant_on S \<inter> T"
      using continuous_discrete_range_constant [OF conST contgh] by blast
    then obtain z where z: "\<And>x. x \<in> S \<inter> T \<Longrightarrow> g x - h x = z"
      by (auto simp: constant_on_def)
    obtain w where "exp(\<i> * of_real(h w)) = exp (\<i> * of_real(z + h w))"
      using disc z False
      by auto (metis diff_add_cancel g h of_real_add)
    then have [simp]: "exp (\<i>* of_real z) = 1"
      by (metis cis_conv_exp cis_mult exp_not_eq_zero mult_cancel_right1)
    show ?thesis
    proof (intro exI conjI)
      show "continuous_on (S \<union> T) (\<lambda>x. if x \<in> S then g x else z + h x)"
        apply (intro continuous_intros continuous_on_cases_local [OF clo contg] conth)
        using z by fastforce
    qed (auto simp: g h algebra_simps exp_add)
  qed
  ultimately have *: "homotopic_with_canon (\<lambda>x. True) (S \<union> T) (sphere 0 1)
                          (\<lambda>x. (x - a) /\<^sub>R cmod (x - a))  (\<lambda>x. (x - b) /\<^sub>R cmod (x - b))"
    by (subst homotopic_circlemaps_divide) (auto simp: inessential_eq_continuous_logarithm_circle)
  show ?thesis
    apply (rule Borsuk_maps_homotopic_in_connected_component_eq [THEN iffD1])
    using assms by (auto simp: *)
qed


theorem Janiszewski:
  fixes a b :: complex
  assumes "compact S" "closed T" and conST: "connected (S \<inter> T)"
      and ccS: "connected_component (- S) a b" and ccT: "connected_component (- T) a b"
    shows "connected_component (- (S \<union> T)) a b"
proof -
  have "path_component(- T) a b"
    by (simp add: \<open>closed T\<close> ccT open_Compl open_path_connected_component)
  then obtain g where g: "path g" "path_image g \<subseteq> - T" "pathstart g = a" "pathfinish g = b"
    by (auto simp: path_component_def)
  obtain C where C: "compact C" "connected C" "a \<in> C" "b \<in> C" "C \<inter> T = {}"
  proof
    show "compact (path_image g)"
      by (simp add: \<open>path g\<close> compact_path_image)
    show "connected (path_image g)"
      by (simp add: \<open>path g\<close> connected_path_image)
  qed (use g in auto)
  obtain r where "0 < r" and r: "C \<union> S \<subseteq> ball 0 r"
    by (metis \<open>compact C\<close> \<open>compact S\<close> bounded_Un compact_imp_bounded bounded_subset_ballD)
  have "connected_component (- (S \<union> (T \<inter> cball 0 r \<union> sphere 0 r))) a b"
  proof (rule Janiszewski_weak [OF \<open>compact S\<close>])
    show comT': "compact ((T \<inter> cball 0 r) \<union> sphere 0 r)"
      by (simp add: \<open>closed T\<close> closed_Int_compact compact_Un)
    have "S \<inter> (T \<inter> cball 0 r \<union> sphere 0 r) = S \<inter> T"
      using r by auto
    with conST show "connected (S \<inter> (T \<inter> cball 0 r \<union> sphere 0 r))"
      by simp
    show "connected_component (- (T \<inter> cball 0 r \<union> sphere 0 r)) a b"
      using conST C r
      apply (simp add: connected_component_def)
      apply (rule_tac x=C in exI)
      by auto
  qed (simp add: ccS)
  then obtain U where U: "connected U" "U \<subseteq> - S" "U \<subseteq> - T \<union> - cball 0 r" "U \<subseteq> - sphere 0 r" "a \<in> U" "b \<in> U"
    by (auto simp: connected_component_def)
  show ?thesis
    unfolding connected_component_def
  proof (intro exI conjI)
    show "U \<subseteq> - (S \<union> T)"
      using U r \<open>0 < r\<close> \<open>a \<in> C\<close> connected_Int_frontier [of U "cball 0 r"]
      apply simp
      by (metis ball_subset_cball compl_inf disjoint_eq_subset_Compl disjoint_iff_not_equal inf.orderE inf_sup_aci(3) subsetCE)
  qed (auto simp: U)
qed

lemma Janiszewski_connected:
  fixes S :: "complex set"
  assumes ST: "compact S" "closed T" "connected(S \<inter> T)"
      and notST: "connected (- S)" "connected (- T)"
    shows "connected(- (S \<union> T))"
using Janiszewski [OF ST]
by (metis IntD1 IntD2 notST compl_sup connected_iff_connected_component)


subsection\<open>The Jordan Curve theorem\<close>

lemma exists_double_arc:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "simple_path g" "pathfinish g = pathstart g" "a \<in> path_image g" "b \<in> path_image g" "a \<noteq> b"
  obtains u d where "arc u" "arc d" "pathstart u = a" "pathfinish u = b"
                    "pathstart d = b" "pathfinish d = a"
                    "(path_image u) \<inter> (path_image d) = {a,b}"
                    "(path_image u) \<union> (path_image d) = path_image g"
proof -
  obtain u where u: "0 \<le> u" "u \<le> 1" "g u = a"
    using assms by (auto simp: path_image_def)
  define h where "h \<equiv> shiftpath u g"
  have "simple_path h"
    using \<open>simple_path g\<close> simple_path_shiftpath \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> assms(2) h_def by blast
  have "pathstart h = g u"
    by (simp add: \<open>u \<le> 1\<close> h_def pathstart_shiftpath)
  have "pathfinish h = g u"
    by (simp add: \<open>0 \<le> u\<close> assms h_def pathfinish_shiftpath)
  have pihg: "path_image h = path_image g"
    by (simp add: \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> assms h_def path_image_shiftpath)
  then obtain v where v: "0 \<le> v" "v \<le> 1" "h v = b"
    using assms by (metis (mono_tags, lifting) atLeastAtMost_iff imageE path_image_def)
  show ?thesis
  proof
    show "arc (subpath 0 v h)"
      by (metis (no_types) \<open>pathstart h = g u\<close> \<open>simple_path h\<close> arc_simple_path_subpath \<open>a \<noteq> b\<close> atLeastAtMost_iff zero_le_one order_refl pathstart_def u(3) v)
    show "arc (subpath v 1 h)"
      by (metis (no_types) \<open>pathfinish h = g u\<close> \<open>simple_path h\<close> arc_simple_path_subpath \<open>a \<noteq> b\<close> atLeastAtMost_iff zero_le_one order_refl pathfinish_def u(3) v)
    show "pathstart (subpath 0 v h) = a"
      by (metis \<open>pathstart h = g u\<close> pathstart_def pathstart_subpath u(3))
    show "pathfinish (subpath 0 v h) = b"  "pathstart (subpath v 1 h) = b"
      by (simp_all add: v(3))
    show "pathfinish (subpath v 1 h) = a"
      by (metis \<open>pathfinish h = g u\<close> pathfinish_def pathfinish_subpath u(3))
    show "path_image (subpath 0 v h) \<inter> path_image (subpath v 1 h) = {a, b}"
    proof
      show "path_image (subpath 0 v h) \<inter> path_image (subpath v 1 h) \<subseteq> {a, b}"
        using v  \<open>pathfinish (subpath v 1 h) = a\<close> \<open>simple_path h\<close>
          apply (auto simp: simple_path_def path_image_subpath image_iff Ball_def)
        by (metis (full_types) less_eq_real_def less_irrefl less_le_trans)
      show "{a, b} \<subseteq> path_image (subpath 0 v h) \<inter> path_image (subpath v 1 h)"
        using v \<open>pathstart (subpath 0 v h) = a\<close> \<open>pathfinish (subpath v 1 h) = a\<close>
        apply (auto simp: path_image_subpath image_iff)
        by (metis atLeastAtMost_iff order_refl)
    qed
    show "path_image (subpath 0 v h) \<union> path_image (subpath v 1 h) = path_image g"
      using v apply (simp add: path_image_subpath pihg [symmetric])
      using path_image_def by fastforce
  qed
qed


theorem\<^marker>\<open>tag unimportant\<close> Jordan_curve:
  fixes c :: "real \<Rightarrow> complex"
  assumes "simple_path c" and loop: "pathfinish c = pathstart c"
  obtains inner outer where
                "inner \<noteq> {}" "open inner" "connected inner"
                "outer \<noteq> {}" "open outer" "connected outer"
                "bounded inner" "\<not> bounded outer" "inner \<inter> outer = {}"
                "inner \<union> outer = - path_image c"
                "frontier inner = path_image c"
                "frontier outer = path_image c"
proof -
  have "path c"
    by (simp add: assms simple_path_imp_path)
  have hom: "(path_image c) homeomorphic (sphere(0::complex) 1)"
    by (simp add: assms homeomorphic_simple_path_image_circle)
  with Jordan_Brouwer_separation have "\<not> connected (- (path_image c))"
    by fastforce
  then obtain inner where inner: "inner \<in> components (- path_image c)" and "bounded inner"
    using cobounded_has_bounded_component [of "- (path_image c)"]
    using \<open>\<not> connected (- path_image c)\<close> \<open>simple_path c\<close> bounded_simple_path_image by force
  obtain outer where outer: "outer \<in> components (- path_image c)" and "\<not> bounded outer"
    using cobounded_unbounded_components [of "- (path_image c)"]
    using \<open>path c\<close> bounded_path_image by auto
  show ?thesis
  proof
    show "inner \<noteq> {}"
      using inner in_components_nonempty by auto
    show "open inner"
      by (meson \<open>simple_path c\<close> compact_imp_closed compact_simple_path_image inner open_Compl open_components)
    show "connected inner"
      using in_components_connected inner by blast
    show "outer \<noteq> {}"
      using outer in_components_nonempty by auto
    show "open outer"
      by (meson \<open>simple_path c\<close> compact_imp_closed compact_simple_path_image outer open_Compl open_components)
    show "connected outer"
      using in_components_connected outer by blast
    show "inner \<inter> outer = {}"
      by (meson \<open>\<not> bounded outer\<close> \<open>bounded inner\<close> \<open>connected outer\<close> bounded_subset components_maximal in_components_subset inner outer)
    show fro_inner: "frontier inner = path_image c"
      by (simp add: Jordan_Brouwer_frontier [OF hom inner])
    show fro_outer: "frontier outer = path_image c"
      by (simp add: Jordan_Brouwer_frontier [OF hom outer])
    have False if m: "middle \<in> components (- path_image c)" and "middle \<noteq> inner" "middle \<noteq> outer" for middle
    proof -
      have "frontier middle = path_image c"
        by (simp add: Jordan_Brouwer_frontier [OF hom] that)
      have middle: "open middle" "connected middle" "middle \<noteq> {}"
        apply (meson \<open>simple_path c\<close> compact_imp_closed compact_simple_path_image m open_Compl open_components)
        using in_components_connected in_components_nonempty m by blast+
      obtain a0 b0 where "a0 \<in> path_image c" "b0 \<in> path_image c" "a0 \<noteq> b0"
        using simple_path_image_uncountable [OF \<open>simple_path c\<close>]
        by (metis Diff_cancel countable_Diff_eq countable_empty insert_iff subsetI subset_singleton_iff)
      obtain a b g where ab: "a \<in> path_image c" "b \<in> path_image c" "a \<noteq> b"
                     and "arc g" "pathstart g = a" "pathfinish g = b"
                     and pag_sub: "path_image g - {a,b} \<subseteq> middle"
      proof (rule dense_accessible_frontier_point_pairs [OF \<open>open middle\<close> \<open>connected middle\<close>, of "path_image c \<inter> ball a0 (dist a0 b0)" "path_image c \<inter> ball b0 (dist a0 b0)"])
        show "openin (top_of_set (frontier middle)) (path_image c \<inter> ball a0 (dist a0 b0))"
             "openin (top_of_set (frontier middle)) (path_image c \<inter> ball b0 (dist a0 b0))"
          by (simp_all add: \<open>frontier middle = path_image c\<close> openin_open_Int)
        show "path_image c \<inter> ball a0 (dist a0 b0) \<noteq> path_image c \<inter> ball b0 (dist a0 b0)"
          using \<open>a0 \<noteq> b0\<close> \<open>b0 \<in> path_image c\<close> by auto
        show "path_image c \<inter> ball a0 (dist a0 b0) \<noteq> {}"
          using \<open>a0 \<in> path_image c\<close> \<open>a0 \<noteq> b0\<close> by auto
        show "path_image c \<inter> ball b0 (dist a0 b0) \<noteq> {}"
          using \<open>b0 \<in> path_image c\<close> \<open>a0 \<noteq> b0\<close> by auto
      qed (use arc_distinct_ends arc_imp_simple_path simple_path_endless that in fastforce)
      obtain u d where "arc u" "arc d"
                   and "pathstart u = a" "pathfinish u = b" "pathstart d = b" "pathfinish d = a"
                   and ud_ab: "(path_image u) \<inter> (path_image d) = {a,b}"
                   and ud_Un: "(path_image u) \<union> (path_image d) = path_image c"
        using exists_double_arc [OF assms ab] by blast
      obtain x y where "x \<in> inner" "y \<in> outer"
        using \<open>inner \<noteq> {}\<close> \<open>outer \<noteq> {}\<close> by auto
      have "inner \<inter> middle = {}" "middle \<inter> outer = {}"
        using components_nonoverlap inner outer m that by blast+
      have "connected_component (- (path_image u \<union> path_image g \<union> (path_image d \<union> path_image g))) x y"
      proof (rule Janiszewski)
        show "compact (path_image u \<union> path_image g)"
          by (simp add: \<open>arc g\<close> \<open>arc u\<close> compact_Un compact_arc_image)
        show "closed (path_image d \<union> path_image g)"
          by (simp add: \<open>arc d\<close> \<open>arc g\<close> closed_Un closed_arc_image)
        show "connected ((path_image u \<union> path_image g) \<inter> (path_image d \<union> path_image g))"
          by (metis Un_Diff_cancel \<open>arc g\<close> \<open>path_image u \<inter> path_image d = {a, b}\<close> \<open>pathfinish g = b\<close> \<open>pathstart g = a\<close> connected_arc_image insert_Diff1 pathfinish_in_path_image pathstart_in_path_image sup_bot.right_neutral sup_commute sup_inf_distrib1)
        show "connected_component (- (path_image u \<union> path_image g)) x y"
          unfolding connected_component_def
        proof (intro exI conjI)
          have "connected ((inner \<union> (path_image c - path_image u)) \<union> (outer \<union> (path_image c - path_image u)))"
          proof (rule connected_Un)
            show "connected (inner \<union> (path_image c - path_image u))"
              apply (rule connected_intermediate_closure [OF \<open>connected inner\<close>])
              using fro_inner [symmetric]  apply (auto simp: closure_subset frontier_def)
              done
            show "connected (outer \<union> (path_image c - path_image u))"
              apply (rule connected_intermediate_closure [OF \<open>connected outer\<close>])
              using fro_outer [symmetric]  apply (auto simp: closure_subset frontier_def)
              done
            have "(inner \<inter> outer) \<union> (path_image c - path_image u) \<noteq> {}"
              by (metis \<open>arc d\<close>  ud_ab Diff_Int Diff_cancel Un_Diff \<open>inner \<inter> outer = {}\<close> \<open>pathfinish d = a\<close> \<open>pathstart d = b\<close> arc_simple_path insert_commute nonempty_simple_path_endless sup_bot_left ud_Un)
            then show "(inner \<union> (path_image c - path_image u)) \<inter> (outer \<union> (path_image c - path_image u)) \<noteq> {}"
              by auto
          qed
          then show "connected (inner \<union> outer \<union> (path_image c - path_image u))"
            by (metis sup.right_idem sup_assoc sup_commute)
          have "inner \<subseteq> - path_image u" "outer \<subseteq> - path_image u"
            using in_components_subset inner outer ud_Un by auto
          moreover have "inner \<subseteq> - path_image g" "outer \<subseteq> - path_image g"
            using \<open>inner \<inter> middle = {}\<close> \<open>inner \<subseteq> - path_image u\<close>
            using \<open>middle \<inter> outer = {}\<close> \<open>outer \<subseteq> - path_image u\<close> pag_sub ud_ab by fastforce+
          moreover have "path_image c - path_image u \<subseteq> - path_image g"
            using in_components_subset m pag_sub ud_ab by fastforce
          ultimately show "inner \<union> outer \<union> (path_image c - path_image u) \<subseteq> - (path_image u \<union> path_image g)"
            by force
          show "x \<in> inner \<union> outer \<union> (path_image c - path_image u)"
            by (auto simp: \<open>x \<in> inner\<close>)
          show "y \<in> inner \<union> outer \<union> (path_image c - path_image u)"
            by (auto simp: \<open>y \<in> outer\<close>)
        qed
        show "connected_component (- (path_image d \<union> path_image g)) x y"
          unfolding connected_component_def
        proof (intro exI conjI)
          have "connected ((inner \<union> (path_image c - path_image d)) \<union> (outer \<union> (path_image c - path_image d)))"
          proof (rule connected_Un)
            show "connected (inner \<union> (path_image c - path_image d))"
              apply (rule connected_intermediate_closure [OF \<open>connected inner\<close>])
              using fro_inner [symmetric]  apply (auto simp: closure_subset frontier_def)
              done
            show "connected (outer \<union> (path_image c - path_image d))"
              apply (rule connected_intermediate_closure [OF \<open>connected outer\<close>])
              using fro_outer [symmetric]  apply (auto simp: closure_subset frontier_def)
              done
            have "(inner \<inter> outer) \<union> (path_image c - path_image d) \<noteq> {}"
              using \<open>arc u\<close> \<open>pathfinish u = b\<close> \<open>pathstart u = a\<close> arc_imp_simple_path nonempty_simple_path_endless ud_Un ud_ab by fastforce
            then show "(inner \<union> (path_image c - path_image d)) \<inter> (outer \<union> (path_image c - path_image d)) \<noteq> {}"
              by auto
          qed
          then show "connected (inner \<union> outer \<union> (path_image c - path_image d))"
            by (metis sup.right_idem sup_assoc sup_commute)
          have "inner \<subseteq> - path_image d" "outer \<subseteq> - path_image d"
            using in_components_subset inner outer ud_Un by auto
          moreover have "inner \<subseteq> - path_image g" "outer \<subseteq> - path_image g"
            using \<open>inner \<inter> middle = {}\<close> \<open>inner \<subseteq> - path_image d\<close>
            using \<open>middle \<inter> outer = {}\<close> \<open>outer \<subseteq> - path_image d\<close> pag_sub ud_ab by fastforce+
          moreover have "path_image c - path_image d \<subseteq> - path_image g"
            using in_components_subset m pag_sub ud_ab by fastforce
          ultimately show "inner \<union> outer \<union> (path_image c - path_image d) \<subseteq> - (path_image d \<union> path_image g)"
            by force
          show "x \<in> inner \<union> outer \<union> (path_image c - path_image d)"
            by (auto simp: \<open>x \<in> inner\<close>)
          show "y \<in> inner \<union> outer \<union> (path_image c - path_image d)"
            by (auto simp: \<open>y \<in> outer\<close>)
        qed
      qed
      then have "connected_component (- (path_image u \<union> path_image d \<union> path_image g)) x y"
        by (simp add: Un_ac)
      moreover have "\<not>(connected_component (- (path_image c)) x y)"
        by (metis (no_types, lifting) \<open>\<not> bounded outer\<close> \<open>bounded inner\<close> \<open>x \<in> inner\<close> \<open>y \<in> outer\<close> componentsE connected_component_eq inner mem_Collect_eq outer)
      ultimately show False
        by (auto simp: ud_Un [symmetric] connected_component_def)
    qed
    then have "components (- path_image c) = {inner,outer}"
      using inner outer by blast
    then have "Union (components (- path_image c)) = inner \<union> outer"
      by simp
    then show "inner \<union> outer = - path_image c"
      by auto
  qed (auto simp: \<open>bounded inner\<close> \<open>\<not> bounded outer\<close>)
qed


corollary\<^marker>\<open>tag unimportant\<close> Jordan_disconnected:
  fixes c :: "real \<Rightarrow> complex"
  assumes "simple_path c" "pathfinish c = pathstart c"
    shows "\<not> connected(- path_image c)"
using Jordan_curve [OF assms]
  by (metis Jordan_Brouwer_separation assms homeomorphic_simple_path_image_circle zero_less_one)


corollary Jordan_inside_outside:
  fixes c :: "real \<Rightarrow> complex"
  assumes "simple_path c" "pathfinish c = pathstart c"
    shows "inside(path_image c) \<noteq> {} \<and>
          open(inside(path_image c)) \<and>
          connected(inside(path_image c)) \<and>
          outside(path_image c) \<noteq> {} \<and>
          open(outside(path_image c)) \<and>
          connected(outside(path_image c)) \<and>
          bounded(inside(path_image c)) \<and>
          \<not> bounded(outside(path_image c)) \<and>
          inside(path_image c) \<inter> outside(path_image c) = {} \<and>
          inside(path_image c) \<union> outside(path_image c) =
          - path_image c \<and>
          frontier(inside(path_image c)) = path_image c \<and>
          frontier(outside(path_image c)) = path_image c"
proof -
  obtain inner outer
    where *: "inner \<noteq> {}" "open inner" "connected inner"
             "outer \<noteq> {}" "open outer" "connected outer"
             "bounded inner" "\<not> bounded outer" "inner \<inter> outer = {}"
             "inner \<union> outer = - path_image c"
             "frontier inner = path_image c"
             "frontier outer = path_image c"
    using Jordan_curve [OF assms] by blast
  then have inner: "inside(path_image c) = inner"
    by (metis dual_order.antisym inside_subset interior_eq interior_inside_frontier)
  have outer: "outside(path_image c) = outer"
    using \<open>inner \<union> outer = - path_image c\<close> \<open>inside (path_image c) = inner\<close>
          outside_inside \<open>inner \<inter> outer = {}\<close> by auto
  show ?thesis
    using * by (auto simp: inner outer)
qed

subsubsection\<open>Triple-curve or "theta-curve" theorem\<close>

text\<open>Proof that there is no fourth component taken from
     Kuratowski's Topology vol 2, para 61, II.\<close>

theorem split_inside_simple_closed_curve:
  fixes c :: "real \<Rightarrow> complex"
  assumes "simple_path c1" and c1: "pathstart c1 = a" "pathfinish c1 = b"
      and "simple_path c2" and c2: "pathstart c2 = a" "pathfinish c2 = b"
      and "simple_path c"  and c: "pathstart c = a" "pathfinish c = b"
      and "a \<noteq> b"
      and c1c2: "path_image c1 \<inter> path_image c2 = {a,b}"
      and c1c: "path_image c1 \<inter> path_image c = {a,b}"
      and c2c: "path_image c2 \<inter> path_image c = {a,b}"
      and ne_12: "path_image c \<inter> inside(path_image c1 \<union> path_image c2) \<noteq> {}"
  obtains "inside(path_image c1 \<union> path_image c) \<inter> inside(path_image c2 \<union> path_image c) = {}"
          "inside(path_image c1 \<union> path_image c) \<union> inside(path_image c2 \<union> path_image c) \<union>
           (path_image c - {a,b}) = inside(path_image c1 \<union> path_image c2)"
proof -
  let ?\<Theta> = "path_image c"  let ?\<Theta>1 = "path_image c1"  let ?\<Theta>2 = "path_image c2"
  have sp: "simple_path (c1 +++ reversepath c2)" "simple_path (c1 +++ reversepath c)" "simple_path (c2 +++ reversepath c)"
    using assms by (auto simp: simple_path_join_loop_eq arc_simple_path simple_path_reversepath)
  then have op_in12: "open (inside (?\<Theta>1 \<union> ?\<Theta>2))"
     and op_out12: "open (outside (?\<Theta>1 \<union> ?\<Theta>2))"
     and op_in1c: "open (inside (?\<Theta>1 \<union> ?\<Theta>))"
     and op_in2c: "open (inside (?\<Theta>2 \<union> ?\<Theta>))"
     and op_out1c: "open (outside (?\<Theta>1 \<union> ?\<Theta>))"
     and op_out2c: "open (outside (?\<Theta>2 \<union> ?\<Theta>))"
     and co_in1c: "connected (inside (?\<Theta>1 \<union> ?\<Theta>))"
     and co_in2c: "connected (inside (?\<Theta>2 \<union> ?\<Theta>))"
     and co_out12c: "connected (outside (?\<Theta>1 \<union> ?\<Theta>2))"
     and co_out1c: "connected (outside (?\<Theta>1 \<union> ?\<Theta>))"
     and co_out2c: "connected (outside (?\<Theta>2 \<union> ?\<Theta>))"
     and pa_c: "?\<Theta> - {pathstart c, pathfinish c} \<subseteq> - ?\<Theta>1"
               "?\<Theta> - {pathstart c, pathfinish c} \<subseteq> - ?\<Theta>2"
     and pa_c1: "?\<Theta>1 - {pathstart c1, pathfinish c1} \<subseteq> - ?\<Theta>2"
                "?\<Theta>1 - {pathstart c1, pathfinish c1} \<subseteq> - ?\<Theta>"
     and pa_c2: "?\<Theta>2 - {pathstart c2, pathfinish c2} \<subseteq> - ?\<Theta>1"
                "?\<Theta>2 - {pathstart c2, pathfinish c2} \<subseteq> - ?\<Theta>"
     and co_c: "connected(?\<Theta> - {pathstart c,pathfinish c})"
     and co_c1: "connected(?\<Theta>1 - {pathstart c1,pathfinish c1})"
     and co_c2: "connected(?\<Theta>2 - {pathstart c2,pathfinish c2})"
     and fr_in: "frontier(inside(?\<Theta>1 \<union> ?\<Theta>2)) = ?\<Theta>1 \<union> ?\<Theta>2"
              "frontier(inside(?\<Theta>2 \<union> ?\<Theta>)) = ?\<Theta>2 \<union> ?\<Theta>"
              "frontier(inside(?\<Theta>1 \<union> ?\<Theta>)) = ?\<Theta>1 \<union> ?\<Theta>"
     and fr_out: "frontier(outside(?\<Theta>1 \<union> ?\<Theta>2)) = ?\<Theta>1 \<union> ?\<Theta>2"
              "frontier(outside(?\<Theta>2 \<union> ?\<Theta>)) = ?\<Theta>2 \<union> ?\<Theta>"
              "frontier(outside(?\<Theta>1 \<union> ?\<Theta>)) = ?\<Theta>1 \<union> ?\<Theta>"
    using Jordan_inside_outside [of "c1 +++ reversepath c2"]
    using Jordan_inside_outside [of "c1 +++ reversepath c"]
    using Jordan_inside_outside [of "c2 +++ reversepath c"] assms
              apply (simp_all add: path_image_join closed_Un closed_simple_path_image open_inside open_outside)
      apply (blast elim: | metis connected_simple_path_endless)+
    done
  have inout_12: "inside (?\<Theta>1 \<union> ?\<Theta>2) \<inter> (?\<Theta> - {pathstart c, pathfinish c}) \<noteq> {}"
    by (metis (no_types, lifting) c c1c ne_12 Diff_Int_distrib Diff_empty Int_empty_right Int_left_commute inf_sup_absorb inf_sup_aci(1) inside_no_overlap)
  have pi_disjoint:  "?\<Theta> \<inter> outside(?\<Theta>1 \<union> ?\<Theta>2) = {}"
  proof (rule ccontr)
    assume "?\<Theta> \<inter> outside (?\<Theta>1 \<union> ?\<Theta>2) \<noteq> {}"
    then show False
      using connectedD [OF co_c, of "inside(?\<Theta>1 \<union> ?\<Theta>2)" "outside(?\<Theta>1 \<union> ?\<Theta>2)"]
      using c c1c2 pa_c op_in12 op_out12 inout_12
      apply auto
      apply (metis Un_Diff_cancel2 Un_iff compl_sup disjoint_insert(1) inf_commute inf_compl_bot_left2 inside_Un_outside mk_disjoint_insert sup_inf_absorb)
      done
  qed
  have out_sub12: "outside(?\<Theta>1 \<union> ?\<Theta>2) \<subseteq> outside(?\<Theta>1 \<union> ?\<Theta>)" "outside(?\<Theta>1 \<union> ?\<Theta>2) \<subseteq> outside(?\<Theta>2 \<union> ?\<Theta>)"
    by (metis Un_commute pi_disjoint outside_Un_outside_Un)+
  have pa1_disj_in2: "?\<Theta>1 \<inter> inside (?\<Theta>2 \<union> ?\<Theta>) = {}"
  proof (rule ccontr)
    assume ne: "?\<Theta>1 \<inter> inside (?\<Theta>2 \<union> ?\<Theta>) \<noteq> {}"
    have 1: "inside (?\<Theta> \<union> ?\<Theta>2) \<inter> ?\<Theta> = {}"
      by (metis (no_types) Diff_Int_distrib Diff_cancel inf_sup_absorb inf_sup_aci(3) inside_no_overlap)
    have 2: "outside (?\<Theta> \<union> ?\<Theta>2) \<inter> ?\<Theta> = {}"
      by (metis (no_types) Int_empty_right Int_left_commute inf_sup_absorb outside_no_overlap)
    have "outside (?\<Theta>2 \<union> ?\<Theta>) \<subseteq> outside (?\<Theta>1 \<union> ?\<Theta>2)"
      apply (subst Un_commute, rule outside_Un_outside_Un)
      using connectedD [OF co_c1, of "inside(?\<Theta>2 \<union> ?\<Theta>)" "outside(?\<Theta>2 \<union> ?\<Theta>)"]
        pa_c1 op_in2c op_out2c ne c1 c2c 1 2 by (auto simp: inf_sup_aci)
    with out_sub12
    have "outside(?\<Theta>1 \<union> ?\<Theta>2) = outside(?\<Theta>2 \<union> ?\<Theta>)" by blast
    then have "frontier(outside(?\<Theta>1 \<union> ?\<Theta>2)) = frontier(outside(?\<Theta>2 \<union> ?\<Theta>))"
      by simp
    then show False
      using inout_12 pi_disjoint c c1c c2c fr_out by auto
  qed
  have pa2_disj_in1: "?\<Theta>2 \<inter> inside(?\<Theta>1 \<union> ?\<Theta>) = {}"
  proof (rule ccontr)
    assume ne: "?\<Theta>2 \<inter> inside (?\<Theta>1 \<union> ?\<Theta>) \<noteq> {}"
    have 1: "inside (?\<Theta> \<union> ?\<Theta>1) \<inter> ?\<Theta> = {}"
      by (metis (no_types) Diff_Int_distrib Diff_cancel inf_sup_absorb inf_sup_aci(3) inside_no_overlap)
    have 2: "outside (?\<Theta> \<union> ?\<Theta>1) \<inter> ?\<Theta> = {}"
      by (metis (no_types) Int_empty_right Int_left_commute inf_sup_absorb outside_no_overlap)
    have "outside (?\<Theta>1 \<union> ?\<Theta>) \<subseteq> outside (?\<Theta>1 \<union> ?\<Theta>2)"
      apply (rule outside_Un_outside_Un)
      using connectedD [OF co_c2, of "inside(?\<Theta>1 \<union> ?\<Theta>)" "outside(?\<Theta>1 \<union> ?\<Theta>)"]
        pa_c2 op_in1c op_out1c ne c2 c1c 1 2 by (auto simp: inf_sup_aci)
    with out_sub12
    have "outside(?\<Theta>1 \<union> ?\<Theta>2) = outside(?\<Theta>1 \<union> ?\<Theta>)"
      by blast
    then have "frontier(outside(?\<Theta>1 \<union> ?\<Theta>2)) = frontier(outside(?\<Theta>1 \<union> ?\<Theta>))"
      by simp
    then show False
      using inout_12 pi_disjoint c c1c c2c fr_out by auto
  qed
  have in_sub_in1: "inside(?\<Theta>1 \<union> ?\<Theta>) \<subseteq> inside(?\<Theta>1 \<union> ?\<Theta>2)"
    using pa2_disj_in1 out_sub12 by (auto simp: inside_outside)
  have in_sub_in2: "inside(?\<Theta>2 \<union> ?\<Theta>) \<subseteq> inside(?\<Theta>1 \<union> ?\<Theta>2)"
    using pa1_disj_in2 out_sub12 by (auto simp: inside_outside)
  have in_sub_out12: "inside(?\<Theta>1 \<union> ?\<Theta>) \<subseteq> outside(?\<Theta>2 \<union> ?\<Theta>)"
  proof
    fix x
    assume x: "x \<in> inside (?\<Theta>1 \<union> ?\<Theta>)"
    then have xnot: "x \<notin> ?\<Theta>"
      by (simp add: inside_def)
    obtain z where zim: "z \<in> ?\<Theta>1" and zout: "z \<in> outside(?\<Theta>2 \<union> ?\<Theta>)"
      apply (auto simp: outside_inside)
      using nonempty_simple_path_endless [OF \<open>simple_path c1\<close>]
      by (metis Diff_Diff_Int Diff_iff ex_in_conv c1 c1c c1c2 pa1_disj_in2)
    obtain e where "e > 0" and e: "ball z e \<subseteq> outside(?\<Theta>2 \<union> ?\<Theta>)"
      using zout op_out2c open_contains_ball_eq by blast
    have "z \<in> frontier (inside (?\<Theta>1 \<union> ?\<Theta>))"
      using zim by (auto simp: fr_in)
    then obtain w where w1: "w \<in> inside (?\<Theta>1 \<union> ?\<Theta>)" and dwz: "dist w z < e"
      using zim \<open>e > 0\<close> by (auto simp: frontier_def closure_approachable)
    then have w2: "w \<in> outside (?\<Theta>2 \<union> ?\<Theta>)"
      by (metis e dist_commute mem_ball subsetCE)
    then have "connected_component (- ?\<Theta>2 \<inter> - ?\<Theta>) z w"
      apply (simp add: connected_component_def)
      apply (rule_tac x = "outside(?\<Theta>2 \<union> ?\<Theta>)" in exI)
      using zout apply (auto simp: co_out2c)
       apply (simp_all add: outside_inside)
      done
    moreover have "connected_component (- ?\<Theta>2 \<inter> - ?\<Theta>) w x"
      unfolding connected_component_def
      using pa2_disj_in1 co_in1c x w1 union_with_outside by fastforce
    ultimately have eq: "connected_component_set (- ?\<Theta>2 \<inter> - ?\<Theta>) x =
                         connected_component_set (- ?\<Theta>2 \<inter> - ?\<Theta>) z"
      by (metis (mono_tags, lifting) connected_component_eq mem_Collect_eq)
    show "x \<in> outside (?\<Theta>2 \<union> ?\<Theta>)"
      using zout x pa2_disj_in1 by (auto simp: outside_def eq xnot)
  qed
  have in_sub_out21: "inside(?\<Theta>2 \<union> ?\<Theta>) \<subseteq> outside(?\<Theta>1 \<union> ?\<Theta>)"
  proof
    fix x
    assume x: "x \<in> inside (?\<Theta>2 \<union> ?\<Theta>)"
    then have xnot: "x \<notin> ?\<Theta>"
      by (simp add: inside_def)
    obtain z where zim: "z \<in> ?\<Theta>2" and zout: "z \<in> outside(?\<Theta>1 \<union> ?\<Theta>)"
      apply (auto simp: outside_inside)
      using nonempty_simple_path_endless [OF \<open>simple_path c2\<close>]
      by (metis (no_types, opaque_lifting) Diff_Diff_Int Diff_iff c1c2 c2 c2c ex_in_conv pa2_disj_in1)
    obtain e where "e > 0" and e: "ball z e \<subseteq> outside(?\<Theta>1 \<union> ?\<Theta>)"
      using zout op_out1c open_contains_ball_eq by blast
    have "z \<in> frontier (inside (?\<Theta>2 \<union> ?\<Theta>))"
      using zim by (auto simp: fr_in)
    then obtain w where w2: "w \<in> inside (?\<Theta>2 \<union> ?\<Theta>)" and dwz: "dist w z < e"
      using zim \<open>e > 0\<close> by (auto simp: frontier_def closure_approachable)
    then have w1: "w \<in> outside (?\<Theta>1 \<union> ?\<Theta>)"
      by (metis e dist_commute mem_ball subsetCE)
    then have "connected_component (- ?\<Theta>1 \<inter> - ?\<Theta>) z w"
      apply (simp add: connected_component_def)
      apply (rule_tac x = "outside(?\<Theta>1 \<union> ?\<Theta>)" in exI)
      using zout apply (auto simp: co_out1c)
       apply (simp_all add: outside_inside)
      done
    moreover have "connected_component (- ?\<Theta>1 \<inter> - ?\<Theta>) w x"
      unfolding connected_component_def
      using pa1_disj_in2 co_in2c x w2 union_with_outside by fastforce
    ultimately have eq: "connected_component_set (- ?\<Theta>1 \<inter> - ?\<Theta>) x =
                           connected_component_set (- ?\<Theta>1 \<inter> - ?\<Theta>) z"
      by (metis (no_types, lifting) connected_component_eq mem_Collect_eq)
    show "x \<in> outside (?\<Theta>1 \<union> ?\<Theta>)"
      using zout x pa1_disj_in2 by (auto simp: outside_def eq xnot)
  qed
  show ?thesis
  proof
    show "inside (?\<Theta>1 \<union> ?\<Theta>) \<inter> inside (?\<Theta>2 \<union> ?\<Theta>) = {}"
      by (metis Int_Un_distrib in_sub_out12 bot_eq_sup_iff disjoint_eq_subset_Compl outside_inside)
    have *: "outside (?\<Theta>1 \<union> ?\<Theta>) \<inter> outside (?\<Theta>2 \<union> ?\<Theta>) \<subseteq> outside (?\<Theta>1 \<union> ?\<Theta>2)"
    proof (rule components_maximal)
      show out_in: "outside (?\<Theta>1 \<union> ?\<Theta>2) \<in> components (- (?\<Theta>1 \<union> ?\<Theta>2))"
        apply (simp only: outside_in_components co_out12c)
        by (metis bounded_empty fr_out(1) frontier_empty unbounded_outside)
      have conn_U: "connected (- (closure (inside (?\<Theta>1 \<union> ?\<Theta>)) \<union> closure (inside (?\<Theta>2 \<union> ?\<Theta>))))"
      proof (rule Janiszewski_connected, simp_all)
        show "bounded (inside (?\<Theta>1 \<union> ?\<Theta>))"
          by (simp add: \<open>simple_path c1\<close> \<open>simple_path c\<close> bounded_inside bounded_simple_path_image)
        have if1: "- (inside (?\<Theta>1 \<union> ?\<Theta>) \<union> frontier (inside (?\<Theta>1 \<union> ?\<Theta>))) = - ?\<Theta>1 \<inter> - ?\<Theta> \<inter> - inside (?\<Theta>1 \<union> ?\<Theta>)"
          by (metis (no_types, lifting) Int_commute Jordan_inside_outside c c1 compl_sup path_image_join path_image_reversepath pathfinish_join pathfinish_reversepath pathstart_join pathstart_reversepath sp(2) closure_Un_frontier fr_out(3))
        then show "connected (- closure (inside (?\<Theta>1 \<union> ?\<Theta>)))"
          by (metis Compl_Un outside_inside co_out1c closure_Un_frontier)
        have if2: "- (inside (?\<Theta>2 \<union> ?\<Theta>) \<union> frontier (inside (?\<Theta>2 \<union> ?\<Theta>))) = - ?\<Theta>2 \<inter> - ?\<Theta> \<inter> - inside (?\<Theta>2 \<union> ?\<Theta>)"
          by (metis (no_types, lifting) Int_commute Jordan_inside_outside c c2 compl_sup path_image_join path_image_reversepath pathfinish_join pathfinish_reversepath pathstart_join pathstart_reversepath sp(3) closure_Un_frontier fr_out(2))
        then show "connected (- closure (inside (?\<Theta>2 \<union> ?\<Theta>)))"
          by (metis Compl_Un outside_inside co_out2c closure_Un_frontier)
        have "connected(?\<Theta>)"
          by (metis \<open>simple_path c\<close> connected_simple_path_image)
        moreover
        have "closure (inside (?\<Theta>1 \<union> ?\<Theta>)) \<inter> closure (inside (?\<Theta>2 \<union> ?\<Theta>)) = ?\<Theta>"
          (is "?lhs = ?rhs")
        proof
          show "?lhs \<subseteq> ?rhs"
          proof clarify
            fix x
            assume x: "x \<in> closure (inside (?\<Theta>1 \<union> ?\<Theta>))" "x \<in> closure (inside (?\<Theta>2 \<union> ?\<Theta>))"
            then have "x \<notin> inside (?\<Theta>1 \<union> ?\<Theta>)"
              by (meson closure_iff_nhds_not_empty in_sub_out12 inside_Int_outside op_in1c)
            with fr_in x show "x \<in> ?\<Theta>"
              by (metis c1c c1c2 closure_Un_frontier pa1_disj_in2 Int_iff Un_iff insert_disjoint(2) insert_subset subsetI subset_antisym)
          qed
          show "?rhs \<subseteq> ?lhs"
            using if1 if2 closure_Un_frontier by fastforce
        qed
        ultimately
        show "connected (closure (inside (?\<Theta>1 \<union> ?\<Theta>)) \<inter> closure (inside (?\<Theta>2 \<union> ?\<Theta>)))"
          by auto
      qed
      show "connected (outside (?\<Theta>1 \<union> ?\<Theta>) \<inter> outside (?\<Theta>2 \<union> ?\<Theta>))"
        using fr_in conn_U  by (simp add: closure_Un_frontier outside_inside Un_commute)
      show "outside (?\<Theta>1 \<union> ?\<Theta>) \<inter> outside (?\<Theta>2 \<union> ?\<Theta>) \<subseteq> - (?\<Theta>1 \<union> ?\<Theta>2)"
        by clarify (metis Diff_Compl Diff_iff Un_iff inf_sup_absorb outside_inside)
      show "outside (?\<Theta>1 \<union> ?\<Theta>2) \<inter>
            (outside (?\<Theta>1 \<union> ?\<Theta>) \<inter> outside (?\<Theta>2 \<union> ?\<Theta>)) \<noteq> {}"
        by (metis Int_assoc out_in inf.orderE out_sub12(1) out_sub12(2) outside_in_components)
    qed
    show "inside (?\<Theta>1 \<union> ?\<Theta>) \<union> inside (?\<Theta>2 \<union> ?\<Theta>) \<union> (?\<Theta> - {a, b}) = inside (?\<Theta>1 \<union> ?\<Theta>2)"
      (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
        apply (simp add: in_sub_in1 in_sub_in2)
        using c1c c2c inside_outside pi_disjoint by fastforce
      have "inside (?\<Theta>1 \<union> ?\<Theta>2) \<subseteq> inside (?\<Theta>1 \<union> ?\<Theta>) \<union> inside (?\<Theta>2 \<union> ?\<Theta>) \<union> (?\<Theta>)"
        using Compl_anti_mono [OF *] by (force simp: inside_outside)
      moreover have "inside (?\<Theta>1 \<union> ?\<Theta>2) \<subseteq> -{a,b}"
        using c1 union_with_outside by fastforce
      ultimately show "?rhs \<subseteq> ?lhs" by auto
    qed
  qed
qed

end
