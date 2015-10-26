(*  Title:      HOL/Multivariate_Analysis/Path_Connected.thy
    Author:     Robert Himmelmann, TU Muenchen, and LCP with material from HOL Light
*)

section \<open>Continuous paths and path-connected sets\<close>

theory Path_Connected
imports Convex_Euclidean_Space
begin

(*FIXME move up?*)
lemma image_affinity_interval:
  fixes c :: "'a::ordered_real_vector"
  shows "((\<lambda>x. m *\<^sub>R x + c) ` {a..b}) = (if {a..b}={} then {}
            else if 0 <= m then {m *\<^sub>R a + c .. m  *\<^sub>R b + c}
            else {m *\<^sub>R b + c .. m *\<^sub>R a + c})"
  apply (case_tac "m=0", force)
  apply (auto simp: scaleR_left_mono)
  apply (rule_tac x="inverse m *\<^sub>R (x-c)" in rev_image_eqI, auto simp: pos_le_divideR_eq le_diff_eq scaleR_left_mono_neg)
  apply (metis diff_le_eq inverse_inverse_eq order.not_eq_order_implies_strict pos_le_divideR_eq positive_imp_inverse_positive)
  apply (rule_tac x="inverse m *\<^sub>R (x-c)" in rev_image_eqI, auto simp: not_le neg_le_divideR_eq diff_le_eq)
  using le_diff_eq scaleR_le_cancel_left_neg
  apply fastforce
  done

subsection \<open>Paths and Arcs\<close>

definition path :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "path g \<longleftrightarrow> continuous_on {0..1} g"

definition pathstart :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> 'a"
  where "pathstart g = g 0"

definition pathfinish :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> 'a"
  where "pathfinish g = g 1"

definition path_image :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> 'a set"
  where "path_image g = g ` {0 .. 1}"

definition reversepath :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> real \<Rightarrow> 'a"
  where "reversepath g = (\<lambda>x. g(1 - x))"

definition joinpaths :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a"
    (infixr "+++" 75)
  where "g1 +++ g2 = (\<lambda>x. if x \<le> 1/2 then g1 (2 * x) else g2 (2 * x - 1))"

definition simple_path :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "simple_path g \<longleftrightarrow>
     path g \<and> (\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. g x = g y \<longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0)"

definition arc :: "(real \<Rightarrow> 'a :: topological_space) \<Rightarrow> bool"
  where "arc g \<longleftrightarrow> path g \<and> inj_on g {0..1}"


subsection\<open>Invariance theorems\<close>

lemma path_eq: "path p \<Longrightarrow> (\<And>t. t \<in> {0..1} \<Longrightarrow> p t = q t) \<Longrightarrow> path q"
  using continuous_on_eq path_def by blast

lemma path_continuous_image: "path g \<Longrightarrow> continuous_on (path_image g) f \<Longrightarrow> path(f o g)"
  unfolding path_def path_image_def
  using continuous_on_compose by blast

lemma path_translation_eq:
  fixes g :: "real \<Rightarrow> 'a :: real_normed_vector"
  shows "path((\<lambda>x. a + x) o g) = path g"
proof -
  have g: "g = (\<lambda>x. -a + x) o ((\<lambda>x. a + x) o g)"
    by (rule ext) simp
  show ?thesis
    unfolding path_def
    apply safe
    apply (subst g)
    apply (rule continuous_on_compose)
    apply (auto intro: continuous_intros)
    done
qed

lemma path_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
   assumes "linear f" "inj f"
     shows "path(f o g) = path g"
proof -
  from linear_injective_left_inverse [OF assms]
  obtain h where h: "linear h" "h \<circ> f = id"
    by blast
  then have g: "g = h o (f o g)"
    by (metis comp_assoc id_comp)
  show ?thesis
    unfolding path_def
    using h assms
    by (metis g continuous_on_compose linear_continuous_on linear_conv_bounded_linear)
qed

lemma pathstart_translation: "pathstart((\<lambda>x. a + x) o g) = a + pathstart g"
  by (simp add: pathstart_def)

lemma pathstart_linear_image_eq: "linear f \<Longrightarrow> pathstart(f o g) = f(pathstart g)"
  by (simp add: pathstart_def)

lemma pathfinish_translation: "pathfinish((\<lambda>x. a + x) o g) = a + pathfinish g"
  by (simp add: pathfinish_def)

lemma pathfinish_linear_image: "linear f \<Longrightarrow> pathfinish(f o g) = f(pathfinish g)"
  by (simp add: pathfinish_def)

lemma path_image_translation: "path_image((\<lambda>x. a + x) o g) = (\<lambda>x. a + x) ` (path_image g)"
  by (simp add: image_comp path_image_def)

lemma path_image_linear_image: "linear f \<Longrightarrow> path_image(f o g) = f ` (path_image g)"
  by (simp add: image_comp path_image_def)

lemma reversepath_translation: "reversepath((\<lambda>x. a + x) o g) = (\<lambda>x. a + x) o reversepath g"
  by (rule ext) (simp add: reversepath_def)

lemma reversepath_linear_image: "linear f \<Longrightarrow> reversepath(f o g) = f o reversepath g"
  by (rule ext) (simp add: reversepath_def)

lemma joinpaths_translation:
    "((\<lambda>x. a + x) o g1) +++ ((\<lambda>x. a + x) o g2) = (\<lambda>x. a + x) o (g1 +++ g2)"
  by (rule ext) (simp add: joinpaths_def)

lemma joinpaths_linear_image: "linear f \<Longrightarrow> (f o g1) +++ (f o g2) = f o (g1 +++ g2)"
  by (rule ext) (simp add: joinpaths_def)

lemma simple_path_translation_eq:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  shows "simple_path((\<lambda>x. a + x) o g) = simple_path g"
  by (simp add: simple_path_def path_translation_eq)

lemma simple_path_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
    shows "simple_path(f o g) = simple_path g"
  using assms inj_on_eq_iff [of f]
  by (auto simp: path_linear_image_eq simple_path_def path_translation_eq)

lemma arc_translation_eq:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  shows "arc((\<lambda>x. a + x) o g) = arc g"
  by (auto simp: arc_def inj_on_def path_translation_eq)

lemma arc_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
   assumes "linear f" "inj f"
     shows  "arc(f o g) = arc g"
  using assms inj_on_eq_iff [of f]
  by (auto simp: arc_def inj_on_def path_linear_image_eq)

subsection\<open>Basic lemmas about paths\<close>

lemma arc_imp_simple_path: "arc g \<Longrightarrow> simple_path g"
  by (simp add: arc_def inj_on_def simple_path_def)

lemma arc_imp_path: "arc g \<Longrightarrow> path g"
  using arc_def by blast

lemma simple_path_imp_path: "simple_path g \<Longrightarrow> path g"
  using simple_path_def by blast

lemma simple_path_cases: "simple_path g \<Longrightarrow> arc g \<or> pathfinish g = pathstart g"
  unfolding simple_path_def arc_def inj_on_def pathfinish_def pathstart_def
  by (force)

lemma simple_path_imp_arc: "simple_path g \<Longrightarrow> pathfinish g \<noteq> pathstart g \<Longrightarrow> arc g"
  using simple_path_cases by auto

lemma arc_distinct_ends: "arc g \<Longrightarrow> pathfinish g \<noteq> pathstart g"
  unfolding arc_def inj_on_def pathfinish_def pathstart_def
  by fastforce

lemma arc_simple_path: "arc g \<longleftrightarrow> simple_path g \<and> pathfinish g \<noteq> pathstart g"
  using arc_distinct_ends arc_imp_simple_path simple_path_cases by blast

lemma simple_path_eq_arc: "pathfinish g \<noteq> pathstart g \<Longrightarrow> (simple_path g = arc g)"
  by (simp add: arc_simple_path)

lemma path_image_nonempty [simp]: "path_image g \<noteq> {}"
  unfolding path_image_def image_is_empty box_eq_empty
  by auto

lemma pathstart_in_path_image[intro]: "pathstart g \<in> path_image g"
  unfolding pathstart_def path_image_def
  by auto

lemma pathfinish_in_path_image[intro]: "pathfinish g \<in> path_image g"
  unfolding pathfinish_def path_image_def
  by auto

lemma connected_path_image[intro]: "path g \<Longrightarrow> connected (path_image g)"
  unfolding path_def path_image_def
  using connected_continuous_image connected_Icc by blast

lemma compact_path_image[intro]: "path g \<Longrightarrow> compact (path_image g)"
  unfolding path_def path_image_def
  using compact_continuous_image connected_Icc by blast

lemma reversepath_reversepath[simp]: "reversepath (reversepath g) = g"
  unfolding reversepath_def
  by auto

lemma pathstart_reversepath[simp]: "pathstart (reversepath g) = pathfinish g"
  unfolding pathstart_def reversepath_def pathfinish_def
  by auto

lemma pathfinish_reversepath[simp]: "pathfinish (reversepath g) = pathstart g"
  unfolding pathstart_def reversepath_def pathfinish_def
  by auto

lemma pathstart_join[simp]: "pathstart (g1 +++ g2) = pathstart g1"
  unfolding pathstart_def joinpaths_def pathfinish_def
  by auto

lemma pathfinish_join[simp]: "pathfinish (g1 +++ g2) = pathfinish g2"
  unfolding pathstart_def joinpaths_def pathfinish_def
  by auto

lemma path_image_reversepath[simp]: "path_image (reversepath g) = path_image g"
proof -
  have *: "\<And>g. path_image (reversepath g) \<subseteq> path_image g"
    unfolding path_image_def subset_eq reversepath_def Ball_def image_iff
    by force
  show ?thesis
    using *[of g] *[of "reversepath g"]
    unfolding reversepath_reversepath
    by auto
qed

lemma path_reversepath [simp]: "path (reversepath g) \<longleftrightarrow> path g"
proof -
  have *: "\<And>g. path g \<Longrightarrow> path (reversepath g)"
    unfolding path_def reversepath_def
    apply (rule continuous_on_compose[unfolded o_def, of _ "\<lambda>x. 1 - x"])
    apply (intro continuous_intros)
    apply (rule continuous_on_subset[of "{0..1}"])
    apply assumption
    apply auto
    done
  show ?thesis
    using *[of "reversepath g"] *[of g]
    unfolding reversepath_reversepath
    by (rule iffI)
qed

lemma arc_reversepath:
  assumes "arc g" shows "arc(reversepath g)"
proof -
  have injg: "inj_on g {0..1}"
    using assms
    by (simp add: arc_def)
  have **: "\<And>x y::real. 1-x = 1-y \<Longrightarrow> x = y"
    by simp
  show ?thesis
    apply (auto simp: arc_def inj_on_def path_reversepath)
    apply (simp add: arc_imp_path assms)
    apply (rule **)
    apply (rule inj_onD [OF injg])
    apply (auto simp: reversepath_def)
    done
qed

lemma simple_path_reversepath: "simple_path g \<Longrightarrow> simple_path (reversepath g)"
  apply (simp add: simple_path_def)
  apply (force simp: reversepath_def)
  done

lemmas reversepath_simps =
  path_reversepath path_image_reversepath pathstart_reversepath pathfinish_reversepath

lemma path_join[simp]:
  assumes "pathfinish g1 = pathstart g2"
  shows "path (g1 +++ g2) \<longleftrightarrow> path g1 \<and> path g2"
  unfolding path_def pathfinish_def pathstart_def
proof safe
  assume cont: "continuous_on {0..1} (g1 +++ g2)"
  have g1: "continuous_on {0..1} g1 \<longleftrightarrow> continuous_on {0..1} ((g1 +++ g2) \<circ> (\<lambda>x. x / 2))"
    by (intro continuous_on_cong refl) (auto simp: joinpaths_def)
  have g2: "continuous_on {0..1} g2 \<longleftrightarrow> continuous_on {0..1} ((g1 +++ g2) \<circ> (\<lambda>x. x / 2 + 1/2))"
    using assms
    by (intro continuous_on_cong refl) (auto simp: joinpaths_def pathfinish_def pathstart_def)
  show "continuous_on {0..1} g1" and "continuous_on {0..1} g2"
    unfolding g1 g2
    by (auto intro!: continuous_intros continuous_on_subset[OF cont] simp del: o_apply)
next
  assume g1g2: "continuous_on {0..1} g1" "continuous_on {0..1} g2"
  have 01: "{0 .. 1} = {0..1/2} \<union> {1/2 .. 1::real}"
    by auto
  {
    fix x :: real
    assume "0 \<le> x" and "x \<le> 1"
    then have "x \<in> (\<lambda>x. x * 2) ` {0..1 / 2}"
      by (intro image_eqI[where x="x/2"]) auto
  }
  note 1 = this
  {
    fix x :: real
    assume "0 \<le> x" and "x \<le> 1"
    then have "x \<in> (\<lambda>x. x * 2 - 1) ` {1 / 2..1}"
      by (intro image_eqI[where x="x/2 + 1/2"]) auto
  }
  note 2 = this
  show "continuous_on {0..1} (g1 +++ g2)"
    using assms
    unfolding joinpaths_def 01
    apply (intro continuous_on_cases closed_atLeastAtMost g1g2[THEN continuous_on_compose2] continuous_intros)
    apply (auto simp: field_simps pathfinish_def pathstart_def intro!: 1 2)
    done
qed

section \<open>Path Images\<close>

lemma bounded_path_image: "path g \<Longrightarrow> bounded(path_image g)"
  by (simp add: compact_imp_bounded compact_path_image)

lemma closed_path_image:
  fixes g :: "real \<Rightarrow> 'a::t2_space"
  shows "path g \<Longrightarrow> closed(path_image g)"
  by (metis compact_path_image compact_imp_closed)

lemma connected_simple_path_image: "simple_path g \<Longrightarrow> connected(path_image g)"
  by (metis connected_path_image simple_path_imp_path)

lemma compact_simple_path_image: "simple_path g \<Longrightarrow> compact(path_image g)"
  by (metis compact_path_image simple_path_imp_path)

lemma bounded_simple_path_image: "simple_path g \<Longrightarrow> bounded(path_image g)"
  by (metis bounded_path_image simple_path_imp_path)

lemma closed_simple_path_image:
  fixes g :: "real \<Rightarrow> 'a::t2_space"
  shows "simple_path g \<Longrightarrow> closed(path_image g)"
  by (metis closed_path_image simple_path_imp_path)

lemma connected_arc_image: "arc g \<Longrightarrow> connected(path_image g)"
  by (metis connected_path_image arc_imp_path)

lemma compact_arc_image: "arc g \<Longrightarrow> compact(path_image g)"
  by (metis compact_path_image arc_imp_path)

lemma bounded_arc_image: "arc g \<Longrightarrow> bounded(path_image g)"
  by (metis bounded_path_image arc_imp_path)

lemma closed_arc_image:
  fixes g :: "real \<Rightarrow> 'a::t2_space"
  shows "arc g \<Longrightarrow> closed(path_image g)"
  by (metis closed_path_image arc_imp_path)

lemma path_image_join_subset: "path_image (g1 +++ g2) \<subseteq> path_image g1 \<union> path_image g2"
  unfolding path_image_def joinpaths_def
  by auto

lemma subset_path_image_join:
  assumes "path_image g1 \<subseteq> s"
    and "path_image g2 \<subseteq> s"
  shows "path_image (g1 +++ g2) \<subseteq> s"
  using path_image_join_subset[of g1 g2] and assms
  by auto

lemma path_image_join:
    "pathfinish g1 = pathstart g2 \<Longrightarrow> path_image(g1 +++ g2) = path_image g1 \<union> path_image g2"
  apply (rule subset_antisym [OF path_image_join_subset])
  apply (auto simp: pathfinish_def pathstart_def path_image_def joinpaths_def image_def)
  apply (drule sym)
  apply (rule_tac x="xa/2" in bexI, auto)
  apply (rule ccontr)
  apply (drule_tac x="(xa+1)/2" in bspec)
  apply (auto simp: field_simps)
  apply (drule_tac x="1/2" in bspec, auto)
  done

lemma not_in_path_image_join:
  assumes "x \<notin> path_image g1"
    and "x \<notin> path_image g2"
  shows "x \<notin> path_image (g1 +++ g2)"
  using assms and path_image_join_subset[of g1 g2]
  by auto

lemma pathstart_compose: "pathstart(f o p) = f(pathstart p)"
  by (simp add: pathstart_def)

lemma pathfinish_compose: "pathfinish(f o p) = f(pathfinish p)"
  by (simp add: pathfinish_def)

lemma path_image_compose: "path_image (f o p) = f ` (path_image p)"
  by (simp add: image_comp path_image_def)

lemma path_compose_join: "f o (p +++ q) = (f o p) +++ (f o q)"
  by (rule ext) (simp add: joinpaths_def)

lemma path_compose_reversepath: "f o reversepath p = reversepath(f o p)"
  by (rule ext) (simp add: reversepath_def)

lemma join_paths_eq:
  "(\<And>t. t \<in> {0..1} \<Longrightarrow> p t = p' t) \<Longrightarrow>
   (\<And>t. t \<in> {0..1} \<Longrightarrow> q t = q' t)
   \<Longrightarrow>  t \<in> {0..1} \<Longrightarrow> (p +++ q) t = (p' +++ q') t"
  by (auto simp: joinpaths_def)

lemma simple_path_inj_on: "simple_path g \<Longrightarrow> inj_on g {0<..<1}"
  by (auto simp: simple_path_def path_image_def inj_on_def less_eq_real_def Ball_def)


subsection\<open>Simple paths with the endpoints removed\<close>

lemma simple_path_endless:
    "simple_path c \<Longrightarrow> path_image c - {pathstart c,pathfinish c} = c ` {0<..<1}"
  apply (auto simp: simple_path_def path_image_def pathstart_def pathfinish_def Ball_def Bex_def image_def)
  apply (metis eq_iff le_less_linear)
  apply (metis leD linear)
  using less_eq_real_def zero_le_one apply blast
  using less_eq_real_def zero_le_one apply blast
  done

lemma connected_simple_path_endless:
    "simple_path c \<Longrightarrow> connected(path_image c - {pathstart c,pathfinish c})"
apply (simp add: simple_path_endless)
apply (rule connected_continuous_image)
apply (meson continuous_on_subset greaterThanLessThan_subseteq_atLeastAtMost_iff le_numeral_extra(3) le_numeral_extra(4) path_def simple_path_imp_path)
by auto

lemma nonempty_simple_path_endless:
    "simple_path c \<Longrightarrow> path_image c - {pathstart c,pathfinish c} \<noteq> {}"
  by (simp add: simple_path_endless)


subsection\<open>The operations on paths\<close>

lemma path_image_subset_reversepath: "path_image(reversepath g) \<le> path_image g"
  by (auto simp: path_image_def reversepath_def)

lemma continuous_on_op_minus: "continuous_on (s::real set) (op - x)"
  by (rule continuous_intros | simp)+

lemma path_imp_reversepath: "path g \<Longrightarrow> path(reversepath g)"
  apply (auto simp: path_def reversepath_def)
  using continuous_on_compose [of "{0..1}" "\<lambda>x. 1 - x" g]
  apply (auto simp: continuous_on_op_minus)
  done

lemma half_bounded_equal: "1 \<le> x * 2 \<Longrightarrow> x * 2 \<le> 1 \<longleftrightarrow> x = (1/2::real)"
  by simp

lemma continuous_on_joinpaths:
  assumes "continuous_on {0..1} g1" "continuous_on {0..1} g2" "pathfinish g1 = pathstart g2"
    shows "continuous_on {0..1} (g1 +++ g2)"
proof -
  have *: "{0..1::real} = {0..1/2} \<union> {1/2..1}"
    by auto
  have gg: "g2 0 = g1 1"
    by (metis assms(3) pathfinish_def pathstart_def)
  have 1: "continuous_on {0..1/2} (g1 +++ g2)"
    apply (rule continuous_on_eq [of _ "g1 o (\<lambda>x. 2*x)"])
    apply (rule continuous_intros | simp add: joinpaths_def assms)+
    done
  have "continuous_on {1/2..1} (g2 o (\<lambda>x. 2*x-1))"
    apply (rule continuous_on_subset [of "{1/2..1}"])
    apply (rule continuous_intros | simp add: image_affinity_atLeastAtMost_diff assms)+
    done
  then have 2: "continuous_on {1/2..1} (g1 +++ g2)"
    apply (rule continuous_on_eq [of "{1/2..1}" "g2 o (\<lambda>x. 2*x-1)"])
    apply (rule assms continuous_intros | simp add: joinpaths_def mult.commute half_bounded_equal gg)+
    done
  show ?thesis
    apply (subst *)
    apply (rule continuous_on_union)
    using 1 2
    apply auto
    done
qed

lemma path_join_imp: "\<lbrakk>path g1; path g2; pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow> path(g1 +++ g2)"
  by (simp add: path_join)

lemmas join_paths_simps = path_join path_image_join pathstart_join pathfinish_join

lemma simple_path_join_loop:
  assumes "arc g1" "arc g2"
          "pathfinish g1 = pathstart g2"  "pathfinish g2 = pathstart g1"
          "path_image g1 \<inter> path_image g2 \<subseteq> {pathstart g1, pathstart g2}"
  shows "simple_path(g1 +++ g2)"
proof -
  have injg1: "inj_on g1 {0..1}"
    using assms
    by (simp add: arc_def)
  have injg2: "inj_on g2 {0..1}"
    using assms
    by (simp add: arc_def)
  have g12: "g1 1 = g2 0"
   and g21: "g2 1 = g1 0"
   and sb:  "g1 ` {0..1} \<inter> g2 ` {0..1} \<subseteq> {g1 0, g2 0}"
    using assms
    by (simp_all add: arc_def pathfinish_def pathstart_def path_image_def)
  { fix x and y::real
    assume xyI: "x = 1 \<longrightarrow> y \<noteq> 0"
       and xy: "x \<le> 1" "0 \<le> y" " y * 2 \<le> 1" "\<not> x * 2 \<le> 1" "g2 (2 * x - 1) = g1 (2 * y)"
    have g1im: "g1 (2 * y) \<in> g1 ` {0..1} \<inter> g2 ` {0..1}"
      using xy
      apply simp
      apply (rule_tac x="2 * x - 1" in image_eqI, auto)
      done
    have False
      using subsetD [OF sb g1im] xy
      apply auto
      apply (drule inj_onD [OF injg1])
      using g21 [symmetric] xyI
      apply (auto dest: inj_onD [OF injg2])
      done
   } note * = this
  { fix x and y::real
    assume xy: "y \<le> 1" "0 \<le> x" "\<not> y * 2 \<le> 1" "x * 2 \<le> 1" "g1 (2 * x) = g2 (2 * y - 1)"
    have g1im: "g1 (2 * x) \<in> g1 ` {0..1} \<inter> g2 ` {0..1}"
      using xy
      apply simp
      apply (rule_tac x="2 * x" in image_eqI, auto)
      done
    have "x = 0 \<and> y = 1"
      using subsetD [OF sb g1im] xy
      apply auto
      apply (force dest: inj_onD [OF injg1])
      using  g21 [symmetric]
      apply (auto dest: inj_onD [OF injg2])
      done
   } note ** = this
  show ?thesis
    using assms
    apply (simp add: arc_def simple_path_def path_join, clarify)
    apply (simp add: joinpaths_def split: split_if_asm)
    apply (force dest: inj_onD [OF injg1])
    apply (metis *)
    apply (metis **)
    apply (force dest: inj_onD [OF injg2])
    done
qed

lemma arc_join:
  assumes "arc g1" "arc g2"
          "pathfinish g1 = pathstart g2"
          "path_image g1 \<inter> path_image g2 \<subseteq> {pathstart g2}"
    shows "arc(g1 +++ g2)"
proof -
  have injg1: "inj_on g1 {0..1}"
    using assms
    by (simp add: arc_def)
  have injg2: "inj_on g2 {0..1}"
    using assms
    by (simp add: arc_def)
  have g11: "g1 1 = g2 0"
   and sb:  "g1 ` {0..1} \<inter> g2 ` {0..1} \<subseteq> {g2 0}"
    using assms
    by (simp_all add: arc_def pathfinish_def pathstart_def path_image_def)
  { fix x and y::real
    assume xy: "x \<le> 1" "0 \<le> y" " y * 2 \<le> 1" "\<not> x * 2 \<le> 1" "g2 (2 * x - 1) = g1 (2 * y)"
    have g1im: "g1 (2 * y) \<in> g1 ` {0..1} \<inter> g2 ` {0..1}"
      using xy
      apply simp
      apply (rule_tac x="2 * x - 1" in image_eqI, auto)
      done
    have False
      using subsetD [OF sb g1im] xy
      by (auto dest: inj_onD [OF injg2])
   } note * = this
  show ?thesis
    apply (simp add: arc_def inj_on_def)
    apply (clarsimp simp add: arc_imp_path assms path_join)
    apply (simp add: joinpaths_def split: split_if_asm)
    apply (force dest: inj_onD [OF injg1])
    apply (metis *)
    apply (metis *)
    apply (force dest: inj_onD [OF injg2])
    done
qed

lemma reversepath_joinpaths:
    "pathfinish g1 = pathstart g2 \<Longrightarrow> reversepath(g1 +++ g2) = reversepath g2 +++ reversepath g1"
  unfolding reversepath_def pathfinish_def pathstart_def joinpaths_def
  by (rule ext) (auto simp: mult.commute)


section\<open>Choosing a subpath of an existing path\<close>

definition subpath :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a::real_normed_vector"
  where "subpath a b g \<equiv> \<lambda>x. g((b - a) * x + a)"

lemma path_image_subpath_gen [simp]:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector"
  shows "path_image(subpath u v g) = g ` (closed_segment u v)"
  apply (simp add: closed_segment_real_eq path_image_def subpath_def)
  apply (subst o_def [of g, symmetric])
  apply (simp add: image_comp [symmetric])
  done

lemma path_image_subpath [simp]:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector"
  shows "path_image(subpath u v g) = (if u \<le> v then g ` {u..v} else g ` {v..u})"
  by (simp add: closed_segment_eq_real_ivl)

lemma path_subpath [simp]:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "path g" "u \<in> {0..1}" "v \<in> {0..1}"
    shows "path(subpath u v g)"
proof -
  have "continuous_on {0..1} (g o (\<lambda>x. ((v-u) * x+ u)))"
    apply (rule continuous_intros | simp)+
    apply (simp add: image_affinity_atLeastAtMost [where c=u])
    using assms
    apply (auto simp: path_def continuous_on_subset)
    done
  then show ?thesis
    by (simp add: path_def subpath_def)
qed

lemma pathstart_subpath [simp]: "pathstart(subpath u v g) = g(u)"
  by (simp add: pathstart_def subpath_def)

lemma pathfinish_subpath [simp]: "pathfinish(subpath u v g) = g(v)"
  by (simp add: pathfinish_def subpath_def)

lemma subpath_trivial [simp]: "subpath 0 1 g = g"
  by (simp add: subpath_def)

lemma subpath_reversepath: "subpath 1 0 g = reversepath g"
  by (simp add: reversepath_def subpath_def)

lemma reversepath_subpath: "reversepath(subpath u v g) = subpath v u g"
  by (simp add: reversepath_def subpath_def algebra_simps)

lemma subpath_translation: "subpath u v ((\<lambda>x. a + x) o g) = (\<lambda>x. a + x) o subpath u v g"
  by (rule ext) (simp add: subpath_def)

lemma subpath_linear_image: "linear f \<Longrightarrow> subpath u v (f o g) = f o subpath u v g"
  by (rule ext) (simp add: subpath_def)

lemma affine_ineq:
  fixes x :: "'a::linordered_idom"
  assumes "x \<le> 1" "v < u"
    shows "v + x * u \<le> u + x * v"
proof -
  have "(1-x)*(u-v) \<ge> 0"
    using assms by auto
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma simple_path_subpath_eq:
  "simple_path(subpath u v g) \<longleftrightarrow>
     path(subpath u v g) \<and> u\<noteq>v \<and>
     (\<forall>x y. x \<in> closed_segment u v \<and> y \<in> closed_segment u v \<and> g x = g y
                \<longrightarrow> x = y \<or> x = u \<and> y = v \<or> x = v \<and> y = u)"
    (is "?lhs = ?rhs")
proof (rule iffI)
  assume ?lhs
  then have p: "path (\<lambda>x. g ((v - u) * x + u))"
        and sim: "(\<And>x y. \<lbrakk>x\<in>{0..1}; y\<in>{0..1}; g ((v - u) * x + u) = g ((v - u) * y + u)\<rbrakk>
                  \<Longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0)"
    by (auto simp: simple_path_def subpath_def)
  { fix x y
    assume "x \<in> closed_segment u v" "y \<in> closed_segment u v" "g x = g y"
    then have "x = y \<or> x = u \<and> y = v \<or> x = v \<and> y = u"
    using sim [of "(x-u)/(v-u)" "(y-u)/(v-u)"] p
    by (auto simp: closed_segment_real_eq image_affinity_atLeastAtMost divide_simps
       split: split_if_asm)
  } moreover
  have "path(subpath u v g) \<and> u\<noteq>v"
    using sim [of "1/3" "2/3"] p
    by (auto simp: subpath_def)
  ultimately show ?rhs
    by metis
next
  assume ?rhs
  then
  have d1: "\<And>x y. \<lbrakk>g x = g y; u \<le> x; x \<le> v; u \<le> y; y \<le> v\<rbrakk> \<Longrightarrow> x = y \<or> x = u \<and> y = v \<or> x = v \<and> y = u"
   and d2: "\<And>x y. \<lbrakk>g x = g y; v \<le> x; x \<le> u; v \<le> y; y \<le> u\<rbrakk> \<Longrightarrow> x = y \<or> x = u \<and> y = v \<or> x = v \<and> y = u"
   and ne: "u < v \<or> v < u"
   and psp: "path (subpath u v g)"
    by (auto simp: closed_segment_real_eq image_affinity_atLeastAtMost)
  have [simp]: "\<And>x. u + x * v = v + x * u \<longleftrightarrow> u=v \<or> x=1"
    by algebra
  show ?lhs using psp ne
    unfolding simple_path_def subpath_def
    by (fastforce simp add: algebra_simps affine_ineq mult_left_mono crossproduct_eq dest: d1 d2)
qed

lemma arc_subpath_eq:
  "arc(subpath u v g) \<longleftrightarrow> path(subpath u v g) \<and> u\<noteq>v \<and> inj_on g (closed_segment u v)"
    (is "?lhs = ?rhs")
proof (rule iffI)
  assume ?lhs
  then have p: "path (\<lambda>x. g ((v - u) * x + u))"
        and sim: "(\<And>x y. \<lbrakk>x\<in>{0..1}; y\<in>{0..1}; g ((v - u) * x + u) = g ((v - u) * y + u)\<rbrakk>
                  \<Longrightarrow> x = y)"
    by (auto simp: arc_def inj_on_def subpath_def)
  { fix x y
    assume "x \<in> closed_segment u v" "y \<in> closed_segment u v" "g x = g y"
    then have "x = y"
    using sim [of "(x-u)/(v-u)" "(y-u)/(v-u)"] p
    by (force simp add: inj_on_def closed_segment_real_eq image_affinity_atLeastAtMost divide_simps
       split: split_if_asm)
  } moreover
  have "path(subpath u v g) \<and> u\<noteq>v"
    using sim [of "1/3" "2/3"] p
    by (auto simp: subpath_def)
  ultimately show ?rhs
    unfolding inj_on_def
    by metis
next
  assume ?rhs
  then
  have d1: "\<And>x y. \<lbrakk>g x = g y; u \<le> x; x \<le> v; u \<le> y; y \<le> v\<rbrakk> \<Longrightarrow> x = y"
   and d2: "\<And>x y. \<lbrakk>g x = g y; v \<le> x; x \<le> u; v \<le> y; y \<le> u\<rbrakk> \<Longrightarrow> x = y"
   and ne: "u < v \<or> v < u"
   and psp: "path (subpath u v g)"
    by (auto simp: inj_on_def closed_segment_real_eq image_affinity_atLeastAtMost)
  show ?lhs using psp ne
    unfolding arc_def subpath_def inj_on_def
    by (auto simp: algebra_simps affine_ineq mult_left_mono crossproduct_eq dest: d1 d2)
qed


lemma simple_path_subpath:
  assumes "simple_path g" "u \<in> {0..1}" "v \<in> {0..1}" "u \<noteq> v"
  shows "simple_path(subpath u v g)"
  using assms
  apply (simp add: simple_path_subpath_eq simple_path_imp_path)
  apply (simp add: simple_path_def closed_segment_real_eq image_affinity_atLeastAtMost, fastforce)
  done

lemma arc_simple_path_subpath:
    "\<lbrakk>simple_path g; u \<in> {0..1}; v \<in> {0..1}; g u \<noteq> g v\<rbrakk> \<Longrightarrow> arc(subpath u v g)"
  by (force intro: simple_path_subpath simple_path_imp_arc)

lemma arc_subpath_arc:
    "\<lbrakk>arc g; u \<in> {0..1}; v \<in> {0..1}; u \<noteq> v\<rbrakk> \<Longrightarrow> arc(subpath u v g)"
  by (meson arc_def arc_imp_simple_path arc_simple_path_subpath inj_onD)

lemma arc_simple_path_subpath_interior:
    "\<lbrakk>simple_path g; u \<in> {0..1}; v \<in> {0..1}; u \<noteq> v; \<bar>u-v\<bar> < 1\<rbrakk> \<Longrightarrow> arc(subpath u v g)"
    apply (rule arc_simple_path_subpath)
    apply (force simp: simple_path_def)+
    done

lemma path_image_subpath_subset:
    "\<lbrakk>path g; u \<in> {0..1}; v \<in> {0..1}\<rbrakk> \<Longrightarrow> path_image(subpath u v g) \<subseteq> path_image g"
  apply (simp add: closed_segment_real_eq image_affinity_atLeastAtMost)
  apply (auto simp: path_image_def)
  done

lemma join_subpaths_middle: "subpath (0) ((1 / 2)) p +++ subpath ((1 / 2)) 1 p = p"
  by (rule ext) (simp add: joinpaths_def subpath_def divide_simps)

subsection\<open>There is a subpath to the frontier\<close>

lemma subpath_to_frontier_explicit:
    fixes S :: "'a::metric_space set"
    assumes g: "path g" and "pathfinish g \<notin> S"
    obtains u where "0 \<le> u" "u \<le> 1"
                "\<And>x. 0 \<le> x \<and> x < u \<Longrightarrow> g x \<in> interior S"
                "(g u \<notin> interior S)" "(u = 0 \<or> g u \<in> closure S)"
proof -
  have gcon: "continuous_on {0..1} g"     using g by (simp add: path_def)
  then have com: "compact ({0..1} \<inter> {u. g u \<in> closure (- S)})"
    apply (simp add: Int_commute [of "{0..1}"] compact_eq_bounded_closed closed_vimage_Int [unfolded vimage_def])
    using compact_eq_bounded_closed apply fastforce
    done
  have "1 \<in> {u. g u \<in> closure (- S)}"
    using assms by (simp add: pathfinish_def closure_def)
  then have dis: "{0..1} \<inter> {u. g u \<in> closure (- S)} \<noteq> {}"
    using atLeastAtMost_iff zero_le_one by blast
  then obtain u where "0 \<le> u" "u \<le> 1" and gu: "g u \<in> closure (- S)"
                  and umin: "\<And>t. \<lbrakk>0 \<le> t; t \<le> 1; g t \<in> closure (- S)\<rbrakk> \<Longrightarrow> u \<le> t"
    using compact_attains_inf [OF com dis] by fastforce
  then have umin': "\<And>t. \<lbrakk>0 \<le> t; t \<le> 1; t < u\<rbrakk> \<Longrightarrow>  g t \<in> S"
    using closure_def by fastforce
  { assume "u \<noteq> 0"
    then have "u > 0" using `0 \<le> u` by auto
    { fix e::real assume "e > 0"
      obtain d where "d>0" and d: "\<And>x'. \<lbrakk>x' \<in> {0..1}; dist x' u < d\<rbrakk> \<Longrightarrow> dist (g x') (g u) < e"
        using continuous_onD [OF gcon _ `e > 0`] `0 \<le> _` `_ \<le> 1` atLeastAtMost_iff by auto
      have *: "dist (max 0 (u - d / 2)) u < d"
        using `0 \<le> u` `u \<le> 1` `d > 0` by (simp add: dist_real_def)
      have "\<exists>y\<in>S. dist y (g u) < e"
        using `0 < u` `u \<le> 1` `d > 0`
        by (force intro: d [OF _ *] umin')
    }
    then have "g u \<in> closure S"
      by (simp add: frontier_def closure_approachable)
  }
  then show ?thesis
    apply (rule_tac u=u in that)
    apply (auto simp: `0 \<le> u` `u \<le> 1` gu interior_closure umin)
    using `_ \<le> 1` interior_closure umin apply fastforce
    done
qed

lemma subpath_to_frontier_strong:
    assumes g: "path g" and "pathfinish g \<notin> S"
    obtains u where "0 \<le> u" "u \<le> 1" "g u \<notin> interior S"
                    "u = 0 \<or> (\<forall>x. 0 \<le> x \<and> x < 1 \<longrightarrow> subpath 0 u g x \<in> interior S)  \<and>  g u \<in> closure S"
proof -
  obtain u where "0 \<le> u" "u \<le> 1"
             and gxin: "\<And>x. 0 \<le> x \<and> x < u \<Longrightarrow> g x \<in> interior S"
             and gunot: "(g u \<notin> interior S)" and u0: "(u = 0 \<or> g u \<in> closure S)"
    using subpath_to_frontier_explicit [OF assms] by blast
  show ?thesis
    apply (rule that [OF `0 \<le> u` `u \<le> 1`])
    apply (simp add: gunot)
    using `0 \<le> u` u0 by (force simp: subpath_def gxin)
qed

lemma subpath_to_frontier:
    assumes g: "path g" and g0: "pathstart g \<in> closure S" and g1: "pathfinish g \<notin> S"
    obtains u where "0 \<le> u" "u \<le> 1" "g u \<in> frontier S" "(path_image(subpath 0 u g) - {g u}) \<subseteq> interior S"
proof -
  obtain u where "0 \<le> u" "u \<le> 1"
             and notin: "g u \<notin> interior S"
             and disj: "u = 0 \<or>
                        (\<forall>x. 0 \<le> x \<and> x < 1 \<longrightarrow> subpath 0 u g x \<in> interior S) \<and> g u \<in> closure S"
    using subpath_to_frontier_strong [OF g g1] by blast
  show ?thesis
    apply (rule that [OF `0 \<le> u` `u \<le> 1`])
    apply (metis DiffI disj frontier_def g0 notin pathstart_def)
    using `0 \<le> u` g0 disj
    apply (simp add:)
    apply (auto simp: closed_segment_eq_real_ivl pathstart_def pathfinish_def subpath_def)
    apply (rename_tac y)
    apply (drule_tac x="y/u" in spec)
    apply (auto split: split_if_asm)
    done
qed

lemma exists_path_subpath_to_frontier:
    fixes S :: "'a::real_normed_vector set"
    assumes "path g" "pathstart g \<in> closure S" "pathfinish g \<notin> S"
    obtains h where "path h" "pathstart h = pathstart g" "path_image h \<subseteq> path_image g"
                    "path_image h - {pathfinish h} \<subseteq> interior S"
                    "pathfinish h \<in> frontier S"
proof -
  obtain u where u: "0 \<le> u" "u \<le> 1" "g u \<in> frontier S" "(path_image(subpath 0 u g) - {g u}) \<subseteq> interior S"
    using subpath_to_frontier [OF assms] by blast
  show ?thesis
    apply (rule that [of "subpath 0 u g"])
    using assms u
    apply simp_all
    apply (simp add: pathstart_def)
    apply (force simp: closed_segment_eq_real_ivl path_image_def)
    done
qed

lemma exists_path_subpath_to_frontier_closed:
    fixes S :: "'a::real_normed_vector set"
    assumes S: "closed S" and g: "path g" and g0: "pathstart g \<in> S" and g1: "pathfinish g \<notin> S"
    obtains h where "path h" "pathstart h = pathstart g" "path_image h \<subseteq> path_image g \<inter> S"
                    "pathfinish h \<in> frontier S"
proof -
  obtain h where h: "path h" "pathstart h = pathstart g" "path_image h \<subseteq> path_image g"
                    "path_image h - {pathfinish h} \<subseteq> interior S"
                    "pathfinish h \<in> frontier S"
    using exists_path_subpath_to_frontier [OF g _ g1] closure_closed [OF S] g0 by auto
  show ?thesis
    apply (rule that [OF `path h`])
    using assms h
    apply auto
    apply (metis diff_single_insert frontier_subset_eq insert_iff interior_subset subset_iff)
    done
qed

subsection \<open>Reparametrizing a closed curve to start at some chosen point\<close>

definition shiftpath :: "real \<Rightarrow> (real \<Rightarrow> 'a::topological_space) \<Rightarrow> real \<Rightarrow> 'a"
  where "shiftpath a f = (\<lambda>x. if (a + x) \<le> 1 then f (a + x) else f (a + x - 1))"

lemma pathstart_shiftpath: "a \<le> 1 \<Longrightarrow> pathstart (shiftpath a g) = g a"
  unfolding pathstart_def shiftpath_def by auto

lemma pathfinish_shiftpath:
  assumes "0 \<le> a"
    and "pathfinish g = pathstart g"
  shows "pathfinish (shiftpath a g) = g a"
  using assms
  unfolding pathstart_def pathfinish_def shiftpath_def
  by auto

lemma endpoints_shiftpath:
  assumes "pathfinish g = pathstart g"
    and "a \<in> {0 .. 1}"
  shows "pathfinish (shiftpath a g) = g a"
    and "pathstart (shiftpath a g) = g a"
  using assms
  by (auto intro!: pathfinish_shiftpath pathstart_shiftpath)

lemma closed_shiftpath:
  assumes "pathfinish g = pathstart g"
    and "a \<in> {0..1}"
  shows "pathfinish (shiftpath a g) = pathstart (shiftpath a g)"
  using endpoints_shiftpath[OF assms]
  by auto

lemma path_shiftpath:
  assumes "path g"
    and "pathfinish g = pathstart g"
    and "a \<in> {0..1}"
  shows "path (shiftpath a g)"
proof -
  have *: "{0 .. 1} = {0 .. 1-a} \<union> {1-a .. 1}"
    using assms(3) by auto
  have **: "\<And>x. x + a = 1 \<Longrightarrow> g (x + a - 1) = g (x + a)"
    using assms(2)[unfolded pathfinish_def pathstart_def]
    by auto
  show ?thesis
    unfolding path_def shiftpath_def *
    apply (rule continuous_on_union)
    apply (rule closed_real_atLeastAtMost)+
    apply (rule continuous_on_eq[of _ "g \<circ> (\<lambda>x. a + x)"])
    prefer 3
    apply (rule continuous_on_eq[of _ "g \<circ> (\<lambda>x. a - 1 + x)"])
    prefer 3
    apply (rule continuous_intros)+
    prefer 2
    apply (rule continuous_intros)+
    apply (rule_tac[1-2] continuous_on_subset[OF assms(1)[unfolded path_def]])
    using assms(3) and **
    apply auto
    apply (auto simp add: field_simps)
    done
qed

lemma shiftpath_shiftpath:
  assumes "pathfinish g = pathstart g"
    and "a \<in> {0..1}"
    and "x \<in> {0..1}"
  shows "shiftpath (1 - a) (shiftpath a g) x = g x"
  using assms
  unfolding pathfinish_def pathstart_def shiftpath_def
  by auto

lemma path_image_shiftpath:
  assumes "a \<in> {0..1}"
    and "pathfinish g = pathstart g"
  shows "path_image (shiftpath a g) = path_image g"
proof -
  { fix x
    assume as: "g 1 = g 0" "x \<in> {0..1::real}" " \<forall>y\<in>{0..1} \<inter> {x. \<not> a + x \<le> 1}. g x \<noteq> g (a + y - 1)"
    then have "\<exists>y\<in>{0..1} \<inter> {x. a + x \<le> 1}. g x = g (a + y)"
    proof (cases "a \<le> x")
      case False
      then show ?thesis
        apply (rule_tac x="1 + x - a" in bexI)
        using as(1,2) and as(3)[THEN bspec[where x="1 + x - a"]] and assms(1)
        apply (auto simp add: field_simps atomize_not)
        done
    next
      case True
      then show ?thesis
        using as(1-2) and assms(1)
        apply (rule_tac x="x - a" in bexI)
        apply (auto simp add: field_simps)
        done
    qed
  }
  then show ?thesis
    using assms
    unfolding shiftpath_def path_image_def pathfinish_def pathstart_def
    by (auto simp add: image_iff)
qed


subsection \<open>Special case of straight-line paths\<close>

definition linepath :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a"
  where "linepath a b = (\<lambda>x. (1 - x) *\<^sub>R a + x *\<^sub>R b)"

lemma pathstart_linepath[simp]: "pathstart (linepath a b) = a"
  unfolding pathstart_def linepath_def
  by auto

lemma pathfinish_linepath[simp]: "pathfinish (linepath a b) = b"
  unfolding pathfinish_def linepath_def
  by auto

lemma continuous_linepath_at[intro]: "continuous (at x) (linepath a b)"
  unfolding linepath_def
  by (intro continuous_intros)

lemma continuous_on_linepath[intro]: "continuous_on s (linepath a b)"
  using continuous_linepath_at
  by (auto intro!: continuous_at_imp_continuous_on)

lemma path_linepath[intro]: "path (linepath a b)"
  unfolding path_def
  by (rule continuous_on_linepath)

lemma path_image_linepath[simp]: "path_image (linepath a b) = closed_segment a b"
  unfolding path_image_def segment linepath_def
  by auto

lemma reversepath_linepath[simp]: "reversepath (linepath a b) = linepath b a"
  unfolding reversepath_def linepath_def
  by auto

lemma arc_linepath:
  assumes "a \<noteq> b"
  shows "arc (linepath a b)"
proof -
  {
    fix x y :: "real"
    assume "x *\<^sub>R b + y *\<^sub>R a = x *\<^sub>R a + y *\<^sub>R b"
    then have "(x - y) *\<^sub>R a = (x - y) *\<^sub>R b"
      by (simp add: algebra_simps)
    with assms have "x = y"
      by simp
  }
  then show ?thesis
    unfolding arc_def inj_on_def
    by (simp add:  path_linepath) (force simp: algebra_simps linepath_def)
qed

lemma simple_path_linepath[intro]: "a \<noteq> b \<Longrightarrow> simple_path (linepath a b)"
  by (simp add: arc_imp_simple_path arc_linepath)


subsection \<open>Bounding a point away from a path\<close>

lemma not_on_path_ball:
  fixes g :: "real \<Rightarrow> 'a::heine_borel"
  assumes "path g"
    and "z \<notin> path_image g"
  shows "\<exists>e > 0. ball z e \<inter> path_image g = {}"
proof -
  obtain a where "a \<in> path_image g" "\<forall>y \<in> path_image g. dist z a \<le> dist z y"
    using distance_attains_inf[OF _ path_image_nonempty, of g z]
    using compact_path_image[THEN compact_imp_closed, OF assms(1)] by auto
  then show ?thesis
    apply (rule_tac x="dist z a" in exI)
    using assms(2)
    apply (auto intro!: dist_pos_lt)
    done
qed

lemma not_on_path_cball:
  fixes g :: "real \<Rightarrow> 'a::heine_borel"
  assumes "path g"
    and "z \<notin> path_image g"
  shows "\<exists>e>0. cball z e \<inter> (path_image g) = {}"
proof -
  obtain e where "ball z e \<inter> path_image g = {}" "e > 0"
    using not_on_path_ball[OF assms] by auto
  moreover have "cball z (e/2) \<subseteq> ball z e"
    using \<open>e > 0\<close> by auto
  ultimately show ?thesis
    apply (rule_tac x="e/2" in exI)
    apply auto
    done
qed


section \<open>Path component, considered as a "joinability" relation (from Tom Hales)\<close>

definition "path_component s x y \<longleftrightarrow>
  (\<exists>g. path g \<and> path_image g \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y)"

abbreviation
   "path_component_set s x \<equiv> Collect (path_component s x)"

lemmas path_defs = path_def pathstart_def pathfinish_def path_image_def path_component_def

lemma path_component_mem:
  assumes "path_component s x y"
  shows "x \<in> s" and "y \<in> s"
  using assms
  unfolding path_defs
  by auto

lemma path_component_refl:
  assumes "x \<in> s"
  shows "path_component s x x"
  unfolding path_defs
  apply (rule_tac x="\<lambda>u. x" in exI)
  using assms
  apply (auto intro!: continuous_intros)
  done

lemma path_component_refl_eq: "path_component s x x \<longleftrightarrow> x \<in> s"
  by (auto intro!: path_component_mem path_component_refl)

lemma path_component_sym: "path_component s x y \<Longrightarrow> path_component s y x"
  using assms
  unfolding path_component_def
  apply (erule exE)
  apply (rule_tac x="reversepath g" in exI)
  apply auto
  done

lemma path_component_trans:
  assumes "path_component s x y" and "path_component s y z"
  shows "path_component s x z"
  using assms
  unfolding path_component_def
  apply (elim exE)
  apply (rule_tac x="g +++ ga" in exI)
  apply (auto simp add: path_image_join)
  done

lemma path_component_of_subset: "s \<subseteq> t \<Longrightarrow> path_component s x y \<Longrightarrow> path_component t x y"
  unfolding path_component_def by auto

lemma path_connected_linepath:
    fixes s :: "'a::real_normed_vector set"
    shows "closed_segment a b \<subseteq> s \<Longrightarrow> path_component s a b"
  apply (simp add: path_component_def)
  apply (rule_tac x="linepath a b" in exI, auto)
  done


text \<open>Can also consider it as a set, as the name suggests.\<close>

lemma path_component_set:
  "path_component_set s x =
    {y. (\<exists>g. path g \<and> path_image g \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y)}"
  by (auto simp: path_component_def)

lemma path_component_subset: "path_component_set s x \<subseteq> s"
  by (auto simp add: path_component_mem(2))

lemma path_component_eq_empty: "path_component_set s x = {} \<longleftrightarrow> x \<notin> s"
  using path_component_mem path_component_refl_eq
    by fastforce

lemma path_component_mono:
     "s \<subseteq> t \<Longrightarrow> (path_component_set s x) \<subseteq> (path_component_set t x)"
  by (simp add: Collect_mono path_component_of_subset)

lemma path_component_eq:
   "y \<in> path_component_set s x \<Longrightarrow> path_component_set s y = path_component_set s x"
by (metis (no_types, lifting) Collect_cong mem_Collect_eq path_component_sym path_component_trans)

subsection \<open>Path connectedness of a space\<close>

definition "path_connected s \<longleftrightarrow>
  (\<forall>x\<in>s. \<forall>y\<in>s. \<exists>g. path g \<and> path_image g \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y)"

lemma path_connected_component: "path_connected s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. path_component s x y)"
  unfolding path_connected_def path_component_def by auto

lemma path_connected_component_set: "path_connected s \<longleftrightarrow> (\<forall>x\<in>s. path_component_set s x = s)"
  unfolding path_connected_component path_component_subset 
  using path_component_mem by blast

lemma path_component_maximal:
     "\<lbrakk>x \<in> t; path_connected t; t \<subseteq> s\<rbrakk> \<Longrightarrow> t \<subseteq> (path_component_set s x)"
  by (metis path_component_mono path_connected_component_set)

subsection \<open>Some useful lemmas about path-connectedness\<close>

lemma convex_imp_path_connected:
  fixes s :: "'a::real_normed_vector set"
  assumes "convex s"
  shows "path_connected s"
  unfolding path_connected_def
  apply rule
  apply rule
  apply (rule_tac x = "linepath x y" in exI)
  unfolding path_image_linepath
  using assms [unfolded convex_contains_segment]
  apply auto
  done

lemma path_connected_imp_connected:
  assumes "path_connected s"
  shows "connected s"
  unfolding connected_def not_ex
  apply rule
  apply rule
  apply (rule ccontr)
  unfolding not_not
  apply (elim conjE)
proof -
  fix e1 e2
  assume as: "open e1" "open e2" "s \<subseteq> e1 \<union> e2" "e1 \<inter> e2 \<inter> s = {}" "e1 \<inter> s \<noteq> {}" "e2 \<inter> s \<noteq> {}"
  then obtain x1 x2 where obt:"x1 \<in> e1 \<inter> s" "x2 \<in> e2 \<inter> s"
    by auto
  then obtain g where g: "path g" "path_image g \<subseteq> s" "pathstart g = x1" "pathfinish g = x2"
    using assms[unfolded path_connected_def,rule_format,of x1 x2] by auto
  have *: "connected {0..1::real}"
    by (auto intro!: convex_connected convex_real_interval)
  have "{0..1} \<subseteq> {x \<in> {0..1}. g x \<in> e1} \<union> {x \<in> {0..1}. g x \<in> e2}"
    using as(3) g(2)[unfolded path_defs] by blast
  moreover have "{x \<in> {0..1}. g x \<in> e1} \<inter> {x \<in> {0..1}. g x \<in> e2} = {}"
    using as(4) g(2)[unfolded path_defs]
    unfolding subset_eq
    by auto
  moreover have "{x \<in> {0..1}. g x \<in> e1} \<noteq> {} \<and> {x \<in> {0..1}. g x \<in> e2} \<noteq> {}"
    using g(3,4)[unfolded path_defs]
    using obt
    by (simp add: ex_in_conv [symmetric], metis zero_le_one order_refl)
  ultimately show False
    using *[unfolded connected_local not_ex, rule_format,
      of "{x\<in>{0..1}. g x \<in> e1}" "{x\<in>{0..1}. g x \<in> e2}"]
    using continuous_openin_preimage[OF g(1)[unfolded path_def] as(1)]
    using continuous_openin_preimage[OF g(1)[unfolded path_def] as(2)]
    by auto
qed

lemma open_path_component:
  fixes s :: "'a::real_normed_vector set"
  assumes "open s"
  shows "open (path_component_set s x)"
  unfolding open_contains_ball
proof
  fix y
  assume as: "y \<in> path_component_set s x"
  then have "y \<in> s"
    apply -
    apply (rule path_component_mem(2))
    unfolding mem_Collect_eq
    apply auto
    done
  then obtain e where e: "e > 0" "ball y e \<subseteq> s"
    using assms[unfolded open_contains_ball]
    by auto
  show "\<exists>e > 0. ball y e \<subseteq> path_component_set s x"
    apply (rule_tac x=e in exI)
    apply (rule,rule \<open>e>0\<close>)
    apply rule
    unfolding mem_ball mem_Collect_eq
  proof -
    fix z
    assume "dist y z < e"
    then show "path_component s x z"
      apply (rule_tac path_component_trans[of _ _ y])
      defer
      apply (rule path_component_of_subset[OF e(2)])
      apply (rule convex_imp_path_connected[OF convex_ball, unfolded path_connected_component, rule_format])
      using \<open>e > 0\<close> as
      apply auto
      done
  qed
qed

lemma open_non_path_component:
  fixes s :: "'a::real_normed_vector set"
  assumes "open s"
  shows "open (s - path_component_set s x)"
  unfolding open_contains_ball
proof
  fix y
  assume as: "y \<in> s - path_component_set s x"
  then obtain e where e: "e > 0" "ball y e \<subseteq> s"
    using assms [unfolded open_contains_ball]
    by auto
  show "\<exists>e>0. ball y e \<subseteq> s - path_component_set s x"
    apply (rule_tac x=e in exI)
    apply rule
    apply (rule \<open>e>0\<close>)
    apply rule
    apply rule
    defer
  proof (rule ccontr)
    fix z
    assume "z \<in> ball y e" "\<not> z \<notin> path_component_set s x"
    then have "y \<in> path_component_set s x"
      unfolding not_not mem_Collect_eq using \<open>e>0\<close>
      apply -
      apply (rule path_component_trans, assumption)
      apply (rule path_component_of_subset[OF e(2)])
      apply (rule convex_imp_path_connected[OF convex_ball, unfolded path_connected_component, rule_format])
      apply auto
      done
    then show False
      using as by auto
  qed (insert e(2), auto)
qed

lemma connected_open_path_connected:
  fixes s :: "'a::real_normed_vector set"
  assumes "open s"
    and "connected s"
  shows "path_connected s"
  unfolding path_connected_component_set
proof (rule, rule, rule path_component_subset, rule)
  fix x y
  assume "x \<in> s" and "y \<in> s"
  show "y \<in> path_component_set s x"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    moreover have "path_component_set s x \<inter> s \<noteq> {}"
      using \<open>x \<in> s\<close> path_component_eq_empty path_component_subset[of s x]
      by auto
    ultimately
    show False
      using \<open>y \<in> s\<close> open_non_path_component[OF assms(1)] open_path_component[OF assms(1)]
      using assms(2)[unfolded connected_def not_ex, rule_format,
        of "path_component_set s x" "s - path_component_set s x"]
      by auto
  qed
qed

lemma path_connected_continuous_image:
  assumes "continuous_on s f"
    and "path_connected s"
  shows "path_connected (f ` s)"
  unfolding path_connected_def
proof (rule, rule)
  fix x' y'
  assume "x' \<in> f ` s" "y' \<in> f ` s"
  then obtain x y where x: "x \<in> s" and y: "y \<in> s" and x': "x' = f x" and y': "y' = f y"
    by auto
  from x y obtain g where "path g \<and> path_image g \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y"
    using assms(2)[unfolded path_connected_def] by fast
  then show "\<exists>g. path g \<and> path_image g \<subseteq> f ` s \<and> pathstart g = x' \<and> pathfinish g = y'"
    unfolding x' y'
    apply (rule_tac x="f \<circ> g" in exI)
    unfolding path_defs
    apply (intro conjI continuous_on_compose continuous_on_subset[OF assms(1)])
    apply auto
    done
qed

lemma path_connected_segment:
    fixes a :: "'a::real_normed_vector"
    shows "path_connected (closed_segment a b)"
  by (simp add: convex_imp_path_connected)

lemma path_connected_open_segment:
    fixes a :: "'a::real_normed_vector"
    shows "path_connected (open_segment a b)"
  by (simp add: convex_imp_path_connected)

lemma homeomorphic_path_connectedness:
  "s homeomorphic t \<Longrightarrow> path_connected s \<longleftrightarrow> path_connected t"
  unfolding homeomorphic_def homeomorphism_def
  apply (erule exE|erule conjE)+
  apply rule
  apply (drule_tac f=f in path_connected_continuous_image)
  prefer 3
  apply (drule_tac f=g in path_connected_continuous_image)
  apply auto
  done

lemma path_connected_empty: "path_connected {}"
  unfolding path_connected_def by auto

lemma path_connected_singleton: "path_connected {a}"
  unfolding path_connected_def pathstart_def pathfinish_def path_image_def
  apply clarify
  apply (rule_tac x="\<lambda>x. a" in exI)
  apply (simp add: image_constant_conv)
  apply (simp add: path_def continuous_on_const)
  done

lemma path_connected_Un:
  assumes "path_connected s"
    and "path_connected t"
    and "s \<inter> t \<noteq> {}"
  shows "path_connected (s \<union> t)"
  unfolding path_connected_component
proof (rule, rule)
  fix x y
  assume as: "x \<in> s \<union> t" "y \<in> s \<union> t"
  from assms(3) obtain z where "z \<in> s \<inter> t"
    by auto
  then show "path_component (s \<union> t) x y"
    using as and assms(1-2)[unfolded path_connected_component]
    apply -
    apply (erule_tac[!] UnE)+
    apply (rule_tac[2-3] path_component_trans[of _ _ z])
    apply (auto simp add:path_component_of_subset [OF Un_upper1] path_component_of_subset[OF Un_upper2])
    done
qed

lemma path_connected_UNION:
  assumes "\<And>i. i \<in> A \<Longrightarrow> path_connected (S i)"
    and "\<And>i. i \<in> A \<Longrightarrow> z \<in> S i"
  shows "path_connected (\<Union>i\<in>A. S i)"
  unfolding path_connected_component
proof clarify
  fix x i y j
  assume *: "i \<in> A" "x \<in> S i" "j \<in> A" "y \<in> S j"
  then have "path_component (S i) x z" and "path_component (S j) z y"
    using assms by (simp_all add: path_connected_component)
  then have "path_component (\<Union>i\<in>A. S i) x z" and "path_component (\<Union>i\<in>A. S i) z y"
    using *(1,3) by (auto elim!: path_component_of_subset [rotated])
  then show "path_component (\<Union>i\<in>A. S i) x y"
    by (rule path_component_trans)
qed

lemma path_component_path_image_pathstart:
  assumes p: "path p" and x: "x \<in> path_image p"
  shows "path_component (path_image p) (pathstart p) x"
using x
proof (clarsimp simp add: path_image_def)
  fix y
  assume "x = p y" and y: "0 \<le> y" "y \<le> 1"
  show "path_component (p ` {0..1}) (pathstart p) (p y)"
  proof (cases "y=0")
    case True then show ?thesis
      by (simp add: path_component_refl_eq pathstart_def)
  next
    case False have "continuous_on {0..1} (p o (op*y))"
      apply (rule continuous_intros)+
      using p [unfolded path_def] y
      apply (auto simp: mult_le_one intro: continuous_on_subset [of _ p])
      done
    then have "path (\<lambda>u. p (y * u))"
      by (simp add: path_def)
    then show ?thesis
      apply (simp add: path_component_def)
      apply (rule_tac x = "\<lambda>u. p (y * u)" in exI)
      apply (intro conjI)
      using y False
      apply (auto simp: mult_le_one pathstart_def pathfinish_def path_image_def)
      done
  qed
qed

lemma path_connected_path_image: "path p \<Longrightarrow> path_connected(path_image p)"
  unfolding path_connected_component
  by (meson path_component_path_image_pathstart path_component_sym path_component_trans)

lemma path_connected_path_component:
   "path_connected (path_component_set s x)"
proof -
  { fix y z
    assume pa: "path_component s x y" "path_component s x z"
    then have pae: "path_component_set s x = path_component_set s y"
      using path_component_eq by auto
    have yz: "path_component s y z"
      using pa path_component_sym path_component_trans by blast
    then have "\<exists>g. path g \<and> path_image g \<subseteq> path_component_set s x \<and> pathstart g = y \<and> pathfinish g = z"
      apply (simp add: path_component_def, clarify)
      apply (rule_tac x=g in exI)
      by (simp add: pae path_component_maximal path_connected_path_image pathstart_in_path_image)
  }
  then show ?thesis
    by (simp add: path_connected_def)
qed

lemma path_component: "path_component s x y \<longleftrightarrow> (\<exists>t. path_connected t \<and> t \<subseteq> s \<and> x \<in> t \<and> y \<in> t)"
  apply (intro iffI)
  apply (metis path_connected_path_image path_defs(5) pathfinish_in_path_image pathstart_in_path_image)
  using path_component_of_subset path_connected_component by blast

lemma path_component_path_component [simp]:
   "path_component_set (path_component_set s x) x = path_component_set s x"
proof (cases "x \<in> s")
  case True show ?thesis
    apply (rule subset_antisym)
    apply (simp add: path_component_subset)
    by (simp add: True path_component_maximal path_component_refl path_connected_path_component)
next
  case False then show ?thesis
    by (metis False empty_iff path_component_eq_empty)
qed

lemma path_component_subset_connected_component:
   "(path_component_set s x) \<subseteq> (connected_component_set s x)"
proof (cases "x \<in> s")
  case True show ?thesis
    apply (rule connected_component_maximal)
    apply (auto simp: True path_component_subset path_component_refl path_connected_imp_connected path_connected_path_component)
    done
next
  case False then show ?thesis
    using path_component_eq_empty by auto
qed

subsection \<open>Sphere is path-connected\<close>

lemma path_connected_punctured_universe:
  assumes "2 \<le> DIM('a::euclidean_space)"
  shows "path_connected (- {a::'a})"
proof -
  let ?A = "{x::'a. \<exists>i\<in>Basis. x \<bullet> i < a \<bullet> i}"
  let ?B = "{x::'a. \<exists>i\<in>Basis. a \<bullet> i < x \<bullet> i}"

  have A: "path_connected ?A"
    unfolding Collect_bex_eq
  proof (rule path_connected_UNION)
    fix i :: 'a
    assume "i \<in> Basis"
    then show "(\<Sum>i\<in>Basis. (a \<bullet> i - 1)*\<^sub>R i) \<in> {x::'a. x \<bullet> i < a \<bullet> i}"
      by simp
    show "path_connected {x. x \<bullet> i < a \<bullet> i}"
      using convex_imp_path_connected [OF convex_halfspace_lt, of i "a \<bullet> i"]
      by (simp add: inner_commute)
  qed
  have B: "path_connected ?B"
    unfolding Collect_bex_eq
  proof (rule path_connected_UNION)
    fix i :: 'a
    assume "i \<in> Basis"
    then show "(\<Sum>i\<in>Basis. (a \<bullet> i + 1) *\<^sub>R i) \<in> {x::'a. a \<bullet> i < x \<bullet> i}"
      by simp
    show "path_connected {x. a \<bullet> i < x \<bullet> i}"
      using convex_imp_path_connected [OF convex_halfspace_gt, of "a \<bullet> i" i]
      by (simp add: inner_commute)
  qed
  obtain S :: "'a set" where "S \<subseteq> Basis" and "card S = Suc (Suc 0)"
    using ex_card[OF assms]
    by auto
  then obtain b0 b1 :: 'a where "b0 \<in> Basis" and "b1 \<in> Basis" and "b0 \<noteq> b1"
    unfolding card_Suc_eq by auto
  then have "a + b0 - b1 \<in> ?A \<inter> ?B"
    by (auto simp: inner_simps inner_Basis)
  then have "?A \<inter> ?B \<noteq> {}"
    by fast
  with A B have "path_connected (?A \<union> ?B)"
    by (rule path_connected_Un)
  also have "?A \<union> ?B = {x. \<exists>i\<in>Basis. x \<bullet> i \<noteq> a \<bullet> i}"
    unfolding neq_iff bex_disj_distrib Collect_disj_eq ..
  also have "\<dots> = {x. x \<noteq> a}"
    unfolding euclidean_eq_iff [where 'a='a]
    by (simp add: Bex_def)
  also have "\<dots> = - {a}"
    by auto
  finally show ?thesis .
qed

lemma path_connected_sphere:
  assumes "2 \<le> DIM('a::euclidean_space)"
  shows "path_connected {x::'a. norm (x - a) = r}"
proof (rule linorder_cases [of r 0])
  assume "r < 0"
  then have "{x::'a. norm(x - a) = r} = {}"
    by auto
  then show ?thesis
    using path_connected_empty by simp
next
  assume "r = 0"
  then show ?thesis
    using path_connected_singleton by simp
next
  assume r: "0 < r"
  have *: "{x::'a. norm(x - a) = r} = (\<lambda>x. a + r *\<^sub>R x) ` {x. norm x = 1}"
    apply (rule set_eqI)
    apply rule
    unfolding image_iff
    apply (rule_tac x="(1/r) *\<^sub>R (x - a)" in bexI)
    unfolding mem_Collect_eq norm_scaleR
    using r
    apply (auto simp add: scaleR_right_diff_distrib)
    done
  have **: "{x::'a. norm x = 1} = (\<lambda>x. (1/norm x) *\<^sub>R x) ` (- {0})"
    apply (rule set_eqI)
    apply rule
    unfolding image_iff
    apply (rule_tac x=x in bexI)
    unfolding mem_Collect_eq
    apply (auto split: split_if_asm)
    done
  have "continuous_on (- {0}) (\<lambda>x::'a. 1 / norm x)"
    by (auto intro!: continuous_intros)
  then show ?thesis
    unfolding * **
    using path_connected_punctured_universe[OF assms]
    by (auto intro!: path_connected_continuous_image continuous_intros)
qed

corollary connected_sphere: "2 \<le> DIM('a::euclidean_space) \<Longrightarrow> connected {x::'a. norm (x - a) = r}"
  using path_connected_sphere path_connected_imp_connected
  by auto

corollary path_connected_complement_bounded_convex:
    fixes s :: "'a :: euclidean_space set"
    assumes "bounded s" "convex s" and 2: "2 \<le> DIM('a)"
    shows "path_connected (- s)"
proof (cases "s={}")
  case True then show ?thesis
    using convex_imp_path_connected by auto
next
  case False
  then obtain a where "a \<in> s" by auto
  { fix x y assume "x \<notin> s" "y \<notin> s"
    then have "x \<noteq> a" "y \<noteq> a" using `a \<in> s` by auto
    then have bxy: "bounded(insert x (insert y s))"
      by (simp add: `bounded s`)
    then obtain B::real where B: "0 < B" and Bx: "norm (a - x) < B" and By: "norm (a - y) < B"
                          and "s \<subseteq> ball a B"
      using bounded_subset_ballD [OF bxy, of a] by (auto simp: dist_norm)
    def C == "B / norm(x - a)"
    { fix u
      assume u: "(1 - u) *\<^sub>R x + u *\<^sub>R (a + C *\<^sub>R (x - a)) \<in> s" and "0 \<le> u" "u \<le> 1"
      have CC: "1 \<le> 1 + (C - 1) * u"
        using `x \<noteq> a` `0 \<le> u`
        apply (simp add: C_def divide_simps norm_minus_commute)
        by (metis Bx diff_le_iff(1) less_eq_real_def mult_nonneg_nonneg)
      have *: "\<And>v. (1 - u) *\<^sub>R x + u *\<^sub>R (a + v *\<^sub>R (x - a)) = a + (1 + (v - 1) * u) *\<^sub>R (x - a)"
        by (simp add: algebra_simps)
      have "a + ((1 / (1 + C * u - u)) *\<^sub>R x + ((u / (1 + C * u - u)) *\<^sub>R a + (C * u / (1 + C * u - u)) *\<^sub>R x)) =
            (1 + (u / (1 + C * u - u))) *\<^sub>R a + ((1 / (1 + C * u - u)) + (C * u / (1 + C * u - u))) *\<^sub>R x"
        by (simp add: algebra_simps)
      also have "... = (1 + (u / (1 + C * u - u))) *\<^sub>R a + (1 + (u / (1 + C * u - u))) *\<^sub>R x"
        using CC by (simp add: field_simps)
      also have "... = x + (1 + (u / (1 + C * u - u))) *\<^sub>R a + (u / (1 + C * u - u)) *\<^sub>R x"
        by (simp add: algebra_simps)
      also have "... = x + ((1 / (1 + C * u - u)) *\<^sub>R a +
              ((u / (1 + C * u - u)) *\<^sub>R x + (C * u / (1 + C * u - u)) *\<^sub>R a))"
        using CC by (simp add: field_simps) (simp add: add_divide_distrib scaleR_add_left)
      finally have xeq: "(1 - 1 / (1 + (C - 1) * u)) *\<^sub>R a + (1 / (1 + (C - 1) * u)) *\<^sub>R (a + (1 + (C - 1) * u) *\<^sub>R (x - a)) = x"
        by (simp add: algebra_simps)
      have False
        using `convex s`
        apply (simp add: convex_alt)
        apply (drule_tac x=a in bspec)
         apply (rule  `a \<in> s`)
        apply (drule_tac x="a + (1 + (C - 1) * u) *\<^sub>R (x - a)" in bspec)
         using u apply (simp add: *)
        apply (drule_tac x="1 / (1 + (C - 1) * u)" in spec)
        using `x \<noteq> a` `x \<notin> s` `0 \<le> u` CC
        apply (auto simp: xeq)
        done
    }
    then have pcx: "path_component (- s) x (a + C *\<^sub>R (x - a))"
      by (force simp: closed_segment_def intro!: path_connected_linepath)
    def D == "B / norm(y - a)"  --{*massive duplication with the proof above*}
    { fix u
      assume u: "(1 - u) *\<^sub>R y + u *\<^sub>R (a + D *\<^sub>R (y - a)) \<in> s" and "0 \<le> u" "u \<le> 1"
      have DD: "1 \<le> 1 + (D - 1) * u"
        using `y \<noteq> a` `0 \<le> u`
        apply (simp add: D_def divide_simps norm_minus_commute)
        by (metis By diff_le_iff(1) less_eq_real_def mult_nonneg_nonneg)
      have *: "\<And>v. (1 - u) *\<^sub>R y + u *\<^sub>R (a + v *\<^sub>R (y - a)) = a + (1 + (v - 1) * u) *\<^sub>R (y - a)"
        by (simp add: algebra_simps)
      have "a + ((1 / (1 + D * u - u)) *\<^sub>R y + ((u / (1 + D * u - u)) *\<^sub>R a + (D * u / (1 + D * u - u)) *\<^sub>R y)) =
            (1 + (u / (1 + D * u - u))) *\<^sub>R a + ((1 / (1 + D * u - u)) + (D * u / (1 + D * u - u))) *\<^sub>R y"
        by (simp add: algebra_simps)
      also have "... = (1 + (u / (1 + D * u - u))) *\<^sub>R a + (1 + (u / (1 + D * u - u))) *\<^sub>R y"
        using DD by (simp add: field_simps)
      also have "... = y + (1 + (u / (1 + D * u - u))) *\<^sub>R a + (u / (1 + D * u - u)) *\<^sub>R y"
        by (simp add: algebra_simps)
      also have "... = y + ((1 / (1 + D * u - u)) *\<^sub>R a +
              ((u / (1 + D * u - u)) *\<^sub>R y + (D * u / (1 + D * u - u)) *\<^sub>R a))"
        using DD by (simp add: field_simps) (simp add: add_divide_distrib scaleR_add_left)
      finally have xeq: "(1 - 1 / (1 + (D - 1) * u)) *\<^sub>R a + (1 / (1 + (D - 1) * u)) *\<^sub>R (a + (1 + (D - 1) * u) *\<^sub>R (y - a)) = y"
        by (simp add: algebra_simps)
      have False
        using `convex s`
        apply (simp add: convex_alt)
        apply (drule_tac x=a in bspec)
         apply (rule  `a \<in> s`)
        apply (drule_tac x="a + (1 + (D - 1) * u) *\<^sub>R (y - a)" in bspec)
         using u apply (simp add: *)
        apply (drule_tac x="1 / (1 + (D - 1) * u)" in spec)
        using `y \<noteq> a` `y \<notin> s` `0 \<le> u` DD
        apply (auto simp: xeq)
        done
    }
    then have pdy: "path_component (- s) y (a + D *\<^sub>R (y - a))"
      by (force simp: closed_segment_def intro!: path_connected_linepath)
    have pyx: "path_component (- s) (a + D *\<^sub>R (y - a)) (a + C *\<^sub>R (x - a))"
      apply (rule path_component_of_subset [of "{x. norm(x - a) = B}"])
       using `s \<subseteq> ball a B`
       apply (force simp: ball_def dist_norm norm_minus_commute)
      apply (rule path_connected_sphere [OF 2, of a B, simplified path_connected_component, rule_format])
      using `x \<noteq> a`  using `y \<noteq> a`  B apply (auto simp: C_def D_def)
      done
    have "path_component (- s) x y"
      by (metis path_component_trans path_component_sym pcx pdy pyx)
  }
  then show ?thesis
    by (auto simp: path_connected_component)
qed


lemma connected_complement_bounded_convex:
    fixes s :: "'a :: euclidean_space set"
    assumes "bounded s" "convex s" "2 \<le> DIM('a)"
      shows  "connected (- s)"
  using path_connected_complement_bounded_convex [OF assms] path_connected_imp_connected by blast

lemma connected_diff_ball:
    fixes s :: "'a :: euclidean_space set"
    assumes "connected s" "cball a r \<subseteq> s" "2 \<le> DIM('a)"
      shows "connected (s - ball a r)"
  apply (rule connected_diff_open_from_closed [OF ball_subset_cball])
  using assms connected_sphere
  apply (auto simp: cball_diff_eq_sphere dist_norm)
  done

subsection\<open>Relations between components and path components\<close>

lemma open_connected_component:
  fixes s :: "'a::real_normed_vector set"
  shows "open s \<Longrightarrow> open (connected_component_set s x)"
    apply (simp add: open_contains_ball, clarify)
    apply (rename_tac y)
    apply (drule_tac x=y in bspec)
     apply (simp add: connected_component_in, clarify)
    apply (rule_tac x=e in exI)
    by (metis mem_Collect_eq connected_component_eq connected_component_maximal centre_in_ball connected_ball)

corollary open_components:
    fixes s :: "'a::real_normed_vector set"
    shows "\<lbrakk>open u; s \<in> components u\<rbrakk> \<Longrightarrow> open s"
  by (simp add: components_iff) (metis open_connected_component)

lemma in_closure_connected_component:
  fixes s :: "'a::real_normed_vector set"
  assumes x: "x \<in> s" and s: "open s"
  shows "x \<in> closure (connected_component_set s y) \<longleftrightarrow>  x \<in> connected_component_set s y"
proof -
  { assume "x \<in> closure (connected_component_set s y)"
    moreover have "x \<in> connected_component_set s x"
      using x by simp
    ultimately have "x \<in> connected_component_set s y"
      using s by (meson Compl_disjoint closure_iff_nhds_not_empty connected_component_disjoint disjoint_eq_subset_Compl open_connected_component)
  }
  then show ?thesis
    by (auto simp: closure_def)
qed

subsection\<open>Existence of unbounded components\<close>

lemma cobounded_unbounded_component:
    fixes s :: "'a :: euclidean_space set"
    assumes "bounded (-s)"
      shows "\<exists>x. x \<in> s \<and> ~ bounded (connected_component_set s x)"
proof -
  obtain i::'a where i: "i \<in> Basis"
    using nonempty_Basis by blast
  obtain B where B: "B>0" "-s \<subseteq> ball 0 B"
    using bounded_subset_ballD [OF assms, of 0] by auto
  then have *: "\<And>x. B \<le> norm x \<Longrightarrow> x \<in> s"
    by (force simp add: ball_def dist_norm)
  have unbounded_inner: "~ bounded {x. inner i x \<ge> B}"
    apply (auto simp: bounded_def dist_norm)
    apply (rule_tac x="x + (max B e + 1 + \<bar>i \<bullet> x\<bar>) *\<^sub>R i" in exI)
    apply simp
    using i
    apply (auto simp: algebra_simps)
    done
  have **: "{x. B \<le> i \<bullet> x} \<subseteq> connected_component_set s (B *\<^sub>R i)"
    apply (rule connected_component_maximal)
    apply (auto simp: i intro: convex_connected convex_halfspace_ge [of B])
    apply (rule *)
    apply (rule order_trans [OF _ Basis_le_norm [OF i]])
    by (simp add: inner_commute)
  have "B *\<^sub>R i \<in> s"
    by (rule *) (simp add: norm_Basis [OF i])
  then show ?thesis
    apply (rule_tac x="B *\<^sub>R i" in exI, clarify)
    apply (frule bounded_subset [of _ "{x. B \<le> i \<bullet> x}", OF _ **])
    using unbounded_inner apply blast
    done
qed

lemma cobounded_unique_unbounded_component:
    fixes s :: "'a :: euclidean_space set"
    assumes bs: "bounded (-s)" and "2 \<le> DIM('a)"
        and bo: "~ bounded(connected_component_set s x)"
                "~ bounded(connected_component_set s y)"
      shows "connected_component_set s x = connected_component_set s y"
proof -
  obtain i::'a where i: "i \<in> Basis"
    using nonempty_Basis by blast
  obtain B where B: "B>0" "-s \<subseteq> ball 0 B"
    using bounded_subset_ballD [OF bs, of 0] by auto
  then have *: "\<And>x. B \<le> norm x \<Longrightarrow> x \<in> s"
    by (force simp add: ball_def dist_norm)
  have ccb: "connected (- ball 0 B :: 'a set)"
    using assms by (auto intro: connected_complement_bounded_convex)
  obtain x' where x': "connected_component s x x'" "norm x' > B"
    using bo [unfolded bounded_def dist_norm, simplified, rule_format]
    by (metis diff_zero norm_minus_commute not_less)
  obtain y' where y': "connected_component s y y'" "norm y' > B"
    using bo [unfolded bounded_def dist_norm, simplified, rule_format]
    by (metis diff_zero norm_minus_commute not_less)
  have x'y': "connected_component s x' y'"
    apply (simp add: connected_component_def)
    apply (rule_tac x="- ball 0 B" in exI)
    using x' y'
    apply (auto simp: ccb dist_norm *)
    done
  show ?thesis
    apply (rule connected_component_eq)
    using x' y' x'y'
    by (metis (no_types, lifting) connected_component_eq_empty connected_component_eq_eq connected_component_idemp connected_component_in)
qed

lemma cobounded_unbounded_components:
    fixes s :: "'a :: euclidean_space set"
    shows "bounded (-s) \<Longrightarrow> \<exists>c. c \<in> components s \<and> ~bounded c"
  by (metis cobounded_unbounded_component components_def imageI)

lemma cobounded_unique_unbounded_components:
    fixes s :: "'a :: euclidean_space set"
    shows  "\<lbrakk>bounded (- s); c \<in> components s; \<not> bounded c; c' \<in> components s; \<not> bounded c'; 2 \<le> DIM('a)\<rbrakk> \<Longrightarrow> c' = c"
  unfolding components_iff
  by (metis cobounded_unique_unbounded_component)

lemma cobounded_has_bounded_component:
    fixes s :: "'a :: euclidean_space set"
    shows "\<lbrakk>bounded (- s); ~connected s; 2 \<le> DIM('a)\<rbrakk> \<Longrightarrow> \<exists>c. c \<in> components s \<and> bounded c"
  by (meson cobounded_unique_unbounded_components connected_eq_connected_components_eq)


section\<open>The "inside" and "outside" of a set\<close>

text\<open>The inside comprises the points in a bounded connected component of the set's complement.
  The outside comprises the points in unbounded connected component of the complement.\<close>

definition inside where
  "inside s \<equiv> {x. (x \<notin> s) \<and> bounded(connected_component_set ( - s) x)}"

definition outside where
  "outside s \<equiv> -s \<inter> {x. ~ bounded(connected_component_set (- s) x)}"

lemma outside: "outside s = {x. ~ bounded(connected_component_set (- s) x)}"
  by (auto simp: outside_def) (metis Compl_iff bounded_empty connected_component_eq_empty)

lemma inside_no_overlap [simp]: "inside s \<inter> s = {}"
  by (auto simp: inside_def)

lemma outside_no_overlap [simp]:
   "outside s \<inter> s = {}"
  by (auto simp: outside_def)

lemma inside_inter_outside [simp]: "inside s \<inter> outside s = {}"
  by (auto simp: inside_def outside_def)

lemma inside_union_outside [simp]: "inside s \<union> outside s = (- s)"
  by (auto simp: inside_def outside_def)

lemma inside_eq_outside:
   "inside s = outside s \<longleftrightarrow> s = UNIV"
  by (auto simp: inside_def outside_def)

lemma inside_outside: "inside s = (- (s \<union> outside s))"
  by (force simp add: inside_def outside)

lemma outside_inside: "outside s = (- (s \<union> inside s))"
  by (auto simp: inside_outside) (metis IntI equals0D outside_no_overlap)

lemma union_with_inside: "s \<union> inside s = - outside s"
  by (auto simp: inside_outside) (simp add: outside_inside)

lemma union_with_outside: "s \<union> outside s = - inside s"
  by (simp add: inside_outside)

lemma outside_mono: "s \<subseteq> t \<Longrightarrow> outside t \<subseteq> outside s"
  by (auto simp: outside bounded_subset connected_component_mono)

lemma inside_mono: "s \<subseteq> t \<Longrightarrow> inside s - t \<subseteq> inside t"
  by (auto simp: inside_def bounded_subset connected_component_mono)

lemma segment_bound_lemma:
  fixes u::real
  assumes "x \<ge> B" "y \<ge> B" "0 \<le> u" "u \<le> 1"
  shows "(1 - u) * x + u * y \<ge> B"
proof -
  obtain dx dy where "dx \<ge> 0" "dy \<ge> 0" "x = B + dx" "y = B + dy"
    using assms by auto (metis add.commute diff_add_cancel)
  with `0 \<le> u` `u \<le> 1` show ?thesis
    by (simp add: add_increasing2 mult_left_le field_simps)
qed

lemma cobounded_outside:
  fixes s :: "'a :: real_normed_vector set"
  assumes "bounded s" shows "bounded (- outside s)"
proof -
  obtain B where B: "B>0" "s \<subseteq> ball 0 B"
    using bounded_subset_ballD [OF assms, of 0] by auto
  { fix x::'a and C::real
    assume Bno: "B \<le> norm x" and C: "0 < C"
    have "\<exists>y. connected_component (- s) x y \<and> norm y > C"
    proof (cases "x = 0")
      case True with B Bno show ?thesis by force
    next
      case False with B C show ?thesis
        apply (rule_tac x="((B+C)/norm x) *\<^sub>R x" in exI)
        apply (simp add: connected_component_def)
        apply (rule_tac x="closed_segment x (((B+C)/norm x) *\<^sub>R x)" in exI)
        apply simp
        apply (rule_tac y="- ball 0 B" in order_trans)
         prefer 2 apply force
        apply (simp add: closed_segment_def ball_def dist_norm, clarify)
        apply (simp add: real_vector_class.scaleR_add_left [symmetric] divide_simps)
        using segment_bound_lemma [of B "norm x" "B+C" ] Bno
        by (meson le_add_same_cancel1 less_eq_real_def not_le)
    qed
  }
  then show ?thesis
    apply (simp add: outside_def assms)
    apply (rule bounded_subset [OF bounded_ball [of 0 B]])
    apply (force simp add: dist_norm not_less bounded_pos)
    done
qed

lemma unbounded_outside:
    fixes s :: "'a::{real_normed_vector, perfect_space} set"
    shows "bounded s \<Longrightarrow> ~ bounded(outside s)"
  using cobounded_imp_unbounded cobounded_outside by blast

lemma bounded_inside:
    fixes s :: "'a::{real_normed_vector, perfect_space} set"
    shows "bounded s \<Longrightarrow> bounded(inside s)"
  by (simp add: bounded_Int cobounded_outside inside_outside)

lemma connected_outside:
    fixes s :: "'a::euclidean_space set"
    assumes "bounded s" "2 \<le> DIM('a)"
      shows "connected(outside s)"
  apply (simp add: connected_iff_connected_component, clarify)
  apply (simp add: outside)
  apply (rule_tac s="connected_component_set (- s) x" in connected_component_of_subset)
  apply (metis (no_types) assms cobounded_unbounded_component cobounded_unique_unbounded_component connected_component_eq_eq connected_component_idemp double_complement mem_Collect_eq)
  apply clarify
  apply (metis connected_component_eq_eq connected_component_in)
  done

lemma outside_connected_component_lt:
    "outside s = {x. \<forall>B. \<exists>y. B < norm(y) \<and> connected_component (- s) x y}"
apply (auto simp: outside bounded_def dist_norm)
apply (metis diff_0 norm_minus_cancel not_less)
by (metis less_diff_eq norm_minus_commute norm_triangle_ineq2 order.trans pinf(6))

lemma outside_connected_component_le:
   "outside s =
            {x. \<forall>B. \<exists>y. B \<le> norm(y) \<and>
                         connected_component (- s) x y}"
apply (simp add: outside_connected_component_lt)
apply (simp add: Set.set_eq_iff)
by (meson gt_ex leD le_less_linear less_imp_le order.trans)

lemma not_outside_connected_component_lt:
    fixes s :: "'a::euclidean_space set"
    assumes s: "bounded s" and "2 \<le> DIM('a)"
      shows "- (outside s) = {x. \<forall>B. \<exists>y. B < norm(y) \<and> ~ (connected_component (- s) x y)}"
proof -
  obtain B::real where B: "0 < B" and Bno: "\<And>x. x \<in> s \<Longrightarrow> norm x \<le> B"
    using s [simplified bounded_pos] by auto
  { fix y::'a and z::'a
    assume yz: "B < norm z" "B < norm y"
    have "connected_component (- cball 0 B) y z"
      apply (rule connected_componentI [OF _ subset_refl])
      apply (rule connected_complement_bounded_convex)
      using assms yz
      by (auto simp: dist_norm)
    then have "connected_component (- s) y z"
      apply (rule connected_component_of_subset)
      apply (metis Bno Compl_anti_mono mem_cball_0 subset_iff)
      done
  } note cyz = this
  show ?thesis
    apply (auto simp: outside)
    apply (metis Compl_iff bounded_iff cobounded_imp_unbounded mem_Collect_eq not_le)
    apply (simp add: bounded_pos)
    by (metis B connected_component_trans cyz not_le)
qed

lemma not_outside_connected_component_le:
    fixes s :: "'a::euclidean_space set"
    assumes s: "bounded s"  "2 \<le> DIM('a)"
      shows "- (outside s) = {x. \<forall>B. \<exists>y. B \<le> norm(y) \<and> ~ (connected_component (- s) x y)}"
apply (auto intro: less_imp_le simp: not_outside_connected_component_lt [OF assms])
by (meson gt_ex less_le_trans)

lemma inside_connected_component_lt:
    fixes s :: "'a::euclidean_space set"
    assumes s: "bounded s"  "2 \<le> DIM('a)"
      shows "inside s = {x. (x \<notin> s) \<and> (\<forall>B. \<exists>y. B < norm(y) \<and> ~(connected_component (- s) x y))}"
  by (auto simp: inside_outside not_outside_connected_component_lt [OF assms])

lemma inside_connected_component_le:
    fixes s :: "'a::euclidean_space set"
    assumes s: "bounded s"  "2 \<le> DIM('a)"
      shows "inside s = {x. (x \<notin> s) \<and> (\<forall>B. \<exists>y. B \<le> norm(y) \<and> ~(connected_component (- s) x y))}"
  by (auto simp: inside_outside not_outside_connected_component_le [OF assms])

lemma inside_subset:
  assumes "connected u" and "~bounded u" and "t \<union> u = - s"
  shows "inside s \<subseteq> t"
apply (auto simp: inside_def)
by (metis bounded_subset [of "connected_component_set (- s) _"] connected_component_maximal
       Compl_iff Un_iff assms subsetI)

lemma frontier_interiors: "frontier s = - interior(s) - interior(-s)"
  by (simp add: Int_commute frontier_def interior_closure)

lemma connected_inter_frontier:
     "\<lbrakk>connected s; s \<inter> t \<noteq> {}; s - t \<noteq> {}\<rbrakk> \<Longrightarrow> (s \<inter> frontier t \<noteq> {})"
  apply (simp add: frontier_interiors connected_open_in, safe)
  apply (drule_tac x="s \<inter> interior t" in spec, safe)
   apply (drule_tac [2] x="s \<inter> interior (-t)" in spec)
   apply (auto simp: disjoint_eq_subset_Compl dest: interior_subset [THEN subsetD])
  done

lemma connected_component_UNIV:
    fixes x :: "'a::real_normed_vector"
    shows "connected_component_set UNIV x = UNIV"
using connected_iff_eq_connected_component_set [of "UNIV::'a set"] connected_UNIV
by auto

lemma connected_component_eq_UNIV:
    fixes x :: "'a::real_normed_vector"
    shows "connected_component_set s x = UNIV \<longleftrightarrow> s = UNIV"
  using connected_component_in connected_component_UNIV by blast

lemma components_univ [simp]: "components UNIV = {UNIV :: 'a::real_normed_vector set}"
  by (auto simp: components_eq_sing_iff)

lemma interior_inside_frontier:
    fixes s :: "'a::real_normed_vector set"
    assumes "bounded s"
      shows "interior s \<subseteq> inside (frontier s)"
proof -
  { fix x y
    assume x: "x \<in> interior s" and y: "y \<notin> s"
       and cc: "connected_component (- frontier s) x y"
    have "connected_component_set (- frontier s) x \<inter> frontier s \<noteq> {}"
      apply (rule connected_inter_frontier, simp)
      apply (metis IntI cc connected_component_in connected_component_refl empty_iff interiorE mem_Collect_eq set_rev_mp x)
      using  y cc
      by blast
    then have "bounded (connected_component_set (- frontier s) x)"
      using connected_component_in by auto
  }
  then show ?thesis
    apply (auto simp: inside_def frontier_def)
    apply (rule classical)
    apply (rule bounded_subset [OF assms], blast)
    done
qed

lemma inside_empty [simp]: "inside {} = ({} :: 'a :: {real_normed_vector, perfect_space} set)"
  by (simp add: inside_def connected_component_UNIV)

lemma outside_empty [simp]: "outside {} = (UNIV :: 'a :: {real_normed_vector, perfect_space} set)"
using inside_empty inside_union_outside by blast

lemma inside_same_component:
   "\<lbrakk>connected_component (- s) x y; x \<in> inside s\<rbrakk> \<Longrightarrow> y \<in> inside s"
  using connected_component_eq connected_component_in
  by (fastforce simp add: inside_def)

lemma outside_same_component:
   "\<lbrakk>connected_component (- s) x y; x \<in> outside s\<rbrakk> \<Longrightarrow> y \<in> outside s"
  using connected_component_eq connected_component_in
  by (fastforce simp add: outside_def)

lemma convex_in_outside:
  fixes s :: "'a :: {real_normed_vector, perfect_space} set"
  assumes s: "convex s" and z: "z \<notin> s"
    shows "z \<in> outside s"
proof (cases "s={}")
  case True then show ?thesis by simp
next
  case False then obtain a where "a \<in> s" by blast
  with z have zna: "z \<noteq> a" by auto
  { assume "bounded (connected_component_set (- s) z)"
    with bounded_pos_less obtain B where "B>0" and B: "\<And>x. connected_component (- s) z x \<Longrightarrow> norm x < B"
      by (metis mem_Collect_eq)
    def C \<equiv> "((B + 1 + norm z) / norm (z-a))"
    have "C > 0"
      using `0 < B` zna by (simp add: C_def divide_simps add_strict_increasing)
    have "\<bar>norm (z + C *\<^sub>R (z-a)) - norm (C *\<^sub>R (z-a))\<bar> \<le> norm z"
      by (metis add_diff_cancel norm_triangle_ineq3)
    moreover have "norm (C *\<^sub>R (z-a)) > norm z + B"
      using zna `B>0` by (simp add: C_def le_max_iff_disj field_simps)
    ultimately have C: "norm (z + C *\<^sub>R (z-a)) > B" by linarith
    { fix u::real
      assume u: "0\<le>u" "u\<le>1" and ins: "(1 - u) *\<^sub>R z + u *\<^sub>R (z + C *\<^sub>R (z - a)) \<in> s"
      then have Cpos: "1 + u * C > 0"
        by (meson `0 < C` add_pos_nonneg less_eq_real_def zero_le_mult_iff zero_less_one)
      then have *: "(1 / (1 + u * C)) *\<^sub>R z + (u * C / (1 + u * C)) *\<^sub>R z = z"
        by (simp add: scaleR_add_left [symmetric] divide_simps)
      then have False
        using convexD_alt [OF s `a \<in> s` ins, of "1/(u*C + 1)"] `C>0` `z \<notin> s` Cpos u
        by (simp add: * divide_simps algebra_simps)
    } note contra = this
    have "connected_component (- s) z (z + C *\<^sub>R (z-a))"
      apply (rule connected_componentI [OF connected_segment [of z "z + C *\<^sub>R (z-a)"]])
      apply (simp add: closed_segment_def)
      using contra
      apply auto
      done
    then have False
      using zna B [of "z + C *\<^sub>R (z-a)"] C
      by (auto simp: divide_simps max_mult_distrib_right)
  }
  then show ?thesis
    by (auto simp: outside_def z)
qed

lemma outside_convex:
  fixes s :: "'a :: {real_normed_vector, perfect_space} set"
  assumes "convex s"
    shows "outside s = - s"
  by (metis ComplD assms convex_in_outside equalityI inside_union_outside subsetI sup.cobounded2)

lemma inside_convex:
  fixes s :: "'a :: {real_normed_vector, perfect_space} set"
  shows "convex s \<Longrightarrow> inside s = {}"
  by (simp add: inside_outside outside_convex)

lemma outside_subset_convex:
  fixes s :: "'a :: {real_normed_vector, perfect_space} set"
  shows "\<lbrakk>convex t; s \<subseteq> t\<rbrakk> \<Longrightarrow> - t \<subseteq> outside s"
  using outside_convex outside_mono by blast

lemma outside_frontier_misses_closure:
    fixes s :: "'a::real_normed_vector set"
    assumes "bounded s"
    shows  "outside(frontier s) \<subseteq> - closure s"
  unfolding outside_inside Lattices.boolean_algebra_class.compl_le_compl_iff
proof -
  { assume "interior s \<subseteq> inside (frontier s)"
    hence "interior s \<union> inside (frontier s) = inside (frontier s)"
      by (simp add: subset_Un_eq)
    then have "closure s \<subseteq> frontier s \<union> inside (frontier s)"
      using frontier_def by auto
  }
  then show "closure s \<subseteq> frontier s \<union> inside (frontier s)"
    using interior_inside_frontier [OF assms] by blast
qed

lemma outside_frontier_eq_complement_closure:
  fixes s :: "'a :: {real_normed_vector, perfect_space} set"
    assumes "bounded s" "convex s"
      shows "outside(frontier s) = - closure s"
by (metis Diff_subset assms convex_closure frontier_def outside_frontier_misses_closure
          outside_subset_convex subset_antisym)

lemma inside_frontier_eq_interior:
     fixes s :: "'a :: {real_normed_vector, perfect_space} set"
     shows "\<lbrakk>bounded s; convex s\<rbrakk> \<Longrightarrow> inside(frontier s) = interior s"
  apply (simp add: inside_outside outside_frontier_eq_complement_closure)
  using closure_subset interior_subset
  apply (auto simp add: frontier_def)
  done

lemma open_inside:
    fixes s :: "'a::real_normed_vector set"
    assumes "closed s"
      shows "open (inside s)"
proof -
  { fix x assume x: "x \<in> inside s"
    have "open (connected_component_set (- s) x)"
      using assms open_connected_component by blast
    then obtain e where e: "e>0" and e: "\<And>y. dist y x < e \<longrightarrow> connected_component (- s) x y"
      using dist_not_less_zero
      apply (simp add: open_dist)
      by (metis (no_types, lifting) Compl_iff connected_component_refl_eq inside_def mem_Collect_eq x)
    then have "\<exists>e>0. ball x e \<subseteq> inside s"
      by (metis e dist_commute inside_same_component mem_ball subsetI x)
  }
  then show ?thesis
    by (simp add: open_contains_ball)
qed

lemma open_outside:
    fixes s :: "'a::real_normed_vector set"
    assumes "closed s"
      shows "open (outside s)"
proof -
  { fix x assume x: "x \<in> outside s"
    have "open (connected_component_set (- s) x)"
      using assms open_connected_component by blast
    then obtain e where e: "e>0" and e: "\<And>y. dist y x < e \<longrightarrow> connected_component (- s) x y"
      using dist_not_less_zero
      apply (simp add: open_dist)
      by (metis Int_iff outside_def connected_component_refl_eq  x)
    then have "\<exists>e>0. ball x e \<subseteq> outside s"
      by (metis e dist_commute outside_same_component mem_ball subsetI x)
  }
  then show ?thesis
    by (simp add: open_contains_ball)
qed

lemma closure_inside_subset:
    fixes s :: "'a::real_normed_vector set"
    assumes "closed s"
      shows "closure(inside s) \<subseteq> s \<union> inside s"
by (metis assms closure_minimal open_closed open_outside sup.cobounded2 union_with_inside)

lemma frontier_inside_subset:
    fixes s :: "'a::real_normed_vector set"
    assumes "closed s"
      shows "frontier(inside s) \<subseteq> s"
proof -
  have "closure (inside s) \<inter> - inside s = closure (inside s) - interior (inside s)"
    by (metis (no_types) Diff_Compl assms closure_closed interior_closure open_closed open_inside)
  moreover have "- inside s \<inter> - outside s = s"
    by (metis (no_types) compl_sup double_compl inside_union_outside)
  moreover have "closure (inside s) \<subseteq> - outside s"
    by (metis (no_types) assms closure_inside_subset union_with_inside)
  ultimately have "closure (inside s) - interior (inside s) \<subseteq> s"
    by blast
  then show ?thesis
    by (simp add: frontier_def open_inside interior_open)
qed

lemma closure_outside_subset:
    fixes s :: "'a::real_normed_vector set"
    assumes "closed s"
      shows "closure(outside s) \<subseteq> s \<union> outside s"
  apply (rule closure_minimal, simp)
  by (metis assms closed_open inside_outside open_inside)

lemma frontier_outside_subset:
    fixes s :: "'a::real_normed_vector set"
    assumes "closed s"
      shows "frontier(outside s) \<subseteq> s"
  apply (simp add: frontier_def open_outside interior_open)
  by (metis Diff_subset_conv assms closure_outside_subset interior_eq open_outside sup.commute)

lemma inside_complement_unbounded_connected_empty:
     "\<lbrakk>connected (- s); \<not> bounded (- s)\<rbrakk> \<Longrightarrow> inside s = {}"
  apply (simp add: inside_def)
  by (meson Compl_iff bounded_subset connected_component_maximal order_refl)

lemma inside_bounded_complement_connected_empty:
    fixes s :: "'a::{real_normed_vector, perfect_space} set"
    shows "\<lbrakk>connected (- s); bounded s\<rbrakk> \<Longrightarrow> inside s = {}"
  by (metis inside_complement_unbounded_connected_empty cobounded_imp_unbounded)

lemma inside_inside:
    assumes "s \<subseteq> inside t"
    shows "inside s - t \<subseteq> inside t"
unfolding inside_def
proof clarify
  fix x
  assume x: "x \<notin> t" "x \<notin> s" and bo: "bounded (connected_component_set (- s) x)"
  show "bounded (connected_component_set (- t) x)"
  proof (cases "s \<inter> connected_component_set (- t) x = {}")
    case True show ?thesis
      apply (rule bounded_subset [OF bo])
      apply (rule connected_component_maximal)
      using x True apply auto
      done
  next
    case False then show ?thesis
      using assms [unfolded inside_def] x
      apply (simp add: disjoint_iff_not_equal, clarify)
      apply (drule subsetD, assumption, auto)
      by (metis (no_types, hide_lams) ComplI connected_component_eq_eq)
  qed
qed

lemma inside_inside_subset: "inside(inside s) \<subseteq> s"
  using inside_inside union_with_outside by fastforce

lemma inside_outside_intersect_connected:
      "\<lbrakk>connected t; inside s \<inter> t \<noteq> {}; outside s \<inter> t \<noteq> {}\<rbrakk> \<Longrightarrow> s \<inter> t \<noteq> {}"
  apply (simp add: inside_def outside_def ex_in_conv [symmetric] disjoint_eq_subset_Compl, clarify)
  by (metis (no_types, hide_lams) Compl_anti_mono connected_component_eq connected_component_maximal contra_subsetD double_compl)

lemma outside_bounded_nonempty:
  fixes s :: "'a :: {real_normed_vector, perfect_space} set"
    assumes "bounded s" shows "outside s \<noteq> {}"
  by (metis (no_types, lifting) Collect_empty_eq Collect_mem_eq Compl_eq_Diff_UNIV Diff_cancel
                   Diff_disjoint UNIV_I assms ball_eq_empty bounded_diff cobounded_outside convex_ball
                   double_complement order_refl outside_convex outside_def)

lemma outside_compact_in_open:
    fixes s :: "'a :: {real_normed_vector,perfect_space} set"
    assumes s: "compact s" and t: "open t" and "s \<subseteq> t" "t \<noteq> {}"
      shows "outside s \<inter> t \<noteq> {}"
proof -
  have "outside s \<noteq> {}"
    by (simp add: compact_imp_bounded outside_bounded_nonempty s)
  with assms obtain a b where a: "a \<in> outside s" and b: "b \<in> t" by auto
  show ?thesis
  proof (cases "a \<in> t")
    case True with a show ?thesis by blast
  next
    case False
      have front: "frontier t \<subseteq> - s"
        using `s \<subseteq> t` frontier_disjoint_eq t by auto
      { fix \<gamma>
        assume "path \<gamma>" and pimg_sbs: "path_image \<gamma> - {pathfinish \<gamma>} \<subseteq> interior (- t)"
           and pf: "pathfinish \<gamma> \<in> frontier t" and ps: "pathstart \<gamma> = a"
        def c \<equiv> "pathfinish \<gamma>"
        have "c \<in> -s" unfolding c_def using front pf by blast
        moreover have "open (-s)" using s compact_imp_closed by blast
        ultimately obtain \<epsilon>::real where "\<epsilon> > 0" and \<epsilon>: "cball c \<epsilon> \<subseteq> -s"
          using open_contains_cball[of "-s"] s by blast
        then obtain d where "d \<in> t" and d: "dist d c < \<epsilon>"
          using closure_approachable [of c t] pf unfolding c_def
          by (metis Diff_iff frontier_def)
        then have "d \<in> -s" using \<epsilon>
          using dist_commute by (metis contra_subsetD mem_cball not_le not_less_iff_gr_or_eq)
        have pimg_sbs_cos: "path_image \<gamma> \<subseteq> -s"
          using pimg_sbs apply (auto simp: path_image_def)
          apply (drule subsetD)
          using `c \<in> - s` `s \<subseteq> t` interior_subset apply (auto simp: c_def)
          done
        have "closed_segment c d \<le> cball c \<epsilon>"
          apply (simp add: segment_convex_hull)
          apply (rule hull_minimal)
          using  `\<epsilon> > 0` d apply (auto simp: dist_commute)
          done
        with \<epsilon> have "closed_segment c d \<subseteq> -s" by blast
        moreover have con_gcd: "connected (path_image \<gamma> \<union> closed_segment c d)"
          by (rule connected_Un) (auto simp: c_def `path \<gamma>` connected_path_image)
        ultimately have "connected_component (- s) a d"
          unfolding connected_component_def using pimg_sbs_cos ps by blast
        then have "outside s \<inter> t \<noteq> {}"
          using outside_same_component [OF _ a]  by (metis IntI `d \<in> t` empty_iff)
      } note * = this
      have pal: "pathstart (linepath a b) \<in> closure (- t)"
        by (auto simp: False closure_def)
      show ?thesis
        by (rule exists_path_subpath_to_frontier [OF path_linepath pal _ *]) (auto simp: b)
  qed
qed

lemma inside_inside_compact_connected:
    fixes s :: "'a :: euclidean_space set"
    assumes s: "closed s" and t: "compact t" and "connected t" "s \<subseteq> inside t"
      shows "inside s \<subseteq> inside t"
proof (cases "inside t = {}")
  case True with assms show ?thesis by auto
next
  case False
  consider "DIM('a) = 1" | "DIM('a) \<ge> 2"
    using antisym not_less_eq_eq by fastforce
  then show ?thesis
  proof cases
    case 1 then show ?thesis
             using connected_convex_1_gen assms False inside_convex by blast
  next
    case 2
    have coms: "compact s"
      using assms apply (simp add: s compact_eq_bounded_closed)
       by (meson bounded_inside bounded_subset compact_imp_bounded)
    then have bst: "bounded (s \<union> t)"
      by (simp add: compact_imp_bounded t)
    then obtain r where "0 < r" and r: "s \<union> t \<subseteq> ball 0 r"
      using bounded_subset_ballD by blast
    have outst: "outside s \<inter> outside t \<noteq> {}"
    proof -
      have "- ball 0 r \<subseteq> outside s"
        apply (rule outside_subset_convex)
        using r by auto
      moreover have "- ball 0 r \<subseteq> outside t"
        apply (rule outside_subset_convex)
        using r by auto
      ultimately show ?thesis
        by (metis Compl_subset_Compl_iff Int_subset_iff bounded_ball inf.orderE outside_bounded_nonempty outside_no_overlap)
    qed
    have "s \<inter> t = {}" using assms
      by (metis disjoint_iff_not_equal inside_no_overlap subsetCE)
    moreover have "outside s \<inter> inside t \<noteq> {}"
      by (meson False assms(4) compact_eq_bounded_closed coms open_inside outside_compact_in_open t)
    ultimately have "inside s \<inter> t = {}"
      using inside_outside_intersect_connected [OF `connected t`, of s]
      by (metis "2" compact_eq_bounded_closed coms connected_outside inf.commute inside_outside_intersect_connected outst)
    then show ?thesis
      using inside_inside [OF `s \<subseteq> inside t`] by blast
  qed
qed

lemma connected_with_inside:
    fixes s :: "'a :: real_normed_vector set"
    assumes s: "closed s" and cons: "connected s"
      shows "connected(s \<union> inside s)"
proof (cases "s \<union> inside s = UNIV")
  case True with assms show ?thesis by auto
next
  case False
  then obtain b where b: "b \<notin> s" "b \<notin> inside s" by blast
  have *: "\<exists>y t. y \<in> s \<and> connected t \<and> a \<in> t \<and> y \<in> t \<and> t \<subseteq> (s \<union> inside s)" if "a \<in> (s \<union> inside s)" for a
  using that proof
    assume "a \<in> s" then show ?thesis
      apply (rule_tac x=a in exI)
      apply (rule_tac x="{a}" in exI)
      apply (simp add:)
      done
  next
    assume a: "a \<in> inside s"
    show ?thesis
      apply (rule exists_path_subpath_to_frontier [OF path_linepath [of a b], of "inside s"])
      using a apply (simp add: closure_def)
      apply (simp add: b)
      apply (rule_tac x="pathfinish h" in exI)
      apply (rule_tac x="path_image h" in exI)
      apply (simp add: pathfinish_in_path_image connected_path_image, auto)
      using frontier_inside_subset s apply fastforce
      by (metis (no_types, lifting) frontier_inside_subset insertE insert_Diff interior_eq open_inside pathfinish_in_path_image s subsetCE)
  qed
  show ?thesis
    apply (simp add: connected_iff_connected_component)
    apply (simp add: connected_component_def)
    apply (clarify dest!: *)
    apply (rename_tac u u' t t')
    apply (rule_tac x="(s \<union> t \<union> t')" in exI)
    apply (auto simp: intro!: connected_Un cons)
    done
qed

text\<open>The proof is virtually the same as that above.\<close>
lemma connected_with_outside:
    fixes s :: "'a :: real_normed_vector set"
    assumes s: "closed s" and cons: "connected s"
      shows "connected(s \<union> outside s)"
proof (cases "s \<union> outside s = UNIV")
  case True with assms show ?thesis by auto
next
  case False
  then obtain b where b: "b \<notin> s" "b \<notin> outside s" by blast
  have *: "\<exists>y t. y \<in> s \<and> connected t \<and> a \<in> t \<and> y \<in> t \<and> t \<subseteq> (s \<union> outside s)" if "a \<in> (s \<union> outside s)" for a
  using that proof
    assume "a \<in> s" then show ?thesis
      apply (rule_tac x=a in exI)
      apply (rule_tac x="{a}" in exI)
      apply (simp add:)
      done
  next
    assume a: "a \<in> outside s"
    show ?thesis
      apply (rule exists_path_subpath_to_frontier [OF path_linepath [of a b], of "outside s"])
      using a apply (simp add: closure_def)
      apply (simp add: b)
      apply (rule_tac x="pathfinish h" in exI)
      apply (rule_tac x="path_image h" in exI)
      apply (simp add: pathfinish_in_path_image connected_path_image, auto)
      using frontier_outside_subset s apply fastforce
      by (metis (no_types, lifting) frontier_outside_subset insertE insert_Diff interior_eq open_outside pathfinish_in_path_image s subsetCE)
  qed
  show ?thesis
    apply (simp add: connected_iff_connected_component)
    apply (simp add: connected_component_def)
    apply (clarify dest!: *)
    apply (rename_tac u u' t t')
    apply (rule_tac x="(s \<union> t \<union> t')" in exI)
    apply (auto simp: intro!: connected_Un cons)
    done
qed

lemma inside_inside_eq_empty [simp]:
    fixes s :: "'a :: {real_normed_vector, perfect_space} set"
    assumes s: "closed s" and cons: "connected s"
      shows "inside (inside s) = {}"
  by (metis (no_types) unbounded_outside connected_with_outside [OF assms] bounded_Un
           inside_complement_unbounded_connected_empty unbounded_outside union_with_outside)

lemma inside_in_components:
     "inside s \<in> components (- s) \<longleftrightarrow> connected(inside s) \<and> inside s \<noteq> {}"
  apply (simp add: in_components_maximal)
  apply (auto intro: inside_same_component connected_componentI)
  apply (metis IntI empty_iff inside_no_overlap)
  done

text\<open>The proof is virtually the same as that above.\<close>
lemma outside_in_components:
     "outside s \<in> components (- s) \<longleftrightarrow> connected(outside s) \<and> outside s \<noteq> {}"
  apply (simp add: in_components_maximal)
  apply (auto intro: outside_same_component connected_componentI)
  apply (metis IntI empty_iff outside_no_overlap)
  done

lemma bounded_unique_outside:
    fixes s :: "'a :: euclidean_space set"
    shows "\<lbrakk>bounded s; DIM('a) \<ge> 2\<rbrakk> \<Longrightarrow> (c \<in> components (- s) \<and> ~bounded c \<longleftrightarrow> c = outside s)"
  apply (rule iffI)
  apply (metis cobounded_unique_unbounded_components connected_outside double_compl outside_bounded_nonempty outside_in_components unbounded_outside)
  by (simp add: connected_outside outside_bounded_nonempty outside_in_components unbounded_outside)

end
