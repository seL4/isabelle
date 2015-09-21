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


subsection\<open>Choosing a subpath of an existing path\<close>

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


subsection \<open>Path component, considered as a "joinability" relation (from Tom Hales)\<close>

definition "path_component s x y \<longleftrightarrow>
  (\<exists>g. path g \<and> path_image g \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y)"

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
  assumes "path_component s x y"
    and "path_component s y z"
  shows "path_component s x z"
  using assms
  unfolding path_component_def
  apply (elim exE)
  apply (rule_tac x="g +++ ga" in exI)
  apply (auto simp add: path_image_join)
  done

lemma path_component_of_subset: "s \<subseteq> t \<Longrightarrow> path_component s x y \<Longrightarrow> path_component t x y"
  unfolding path_component_def by auto


text \<open>Can also consider it as a set, as the name suggests.\<close>

lemma path_component_set:
  "{y. path_component s x y} =
    {y. (\<exists>g. path g \<and> path_image g \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y)}"
  unfolding mem_Collect_eq path_component_def
  apply auto
  done

lemma path_component_subset: "{y. path_component s x y} \<subseteq> s"
  by (auto simp add: path_component_mem(2))

lemma path_component_eq_empty: "{y. path_component s x y} = {} \<longleftrightarrow> x \<notin> s"
  using path_component_mem path_component_refl_eq
    by fastforce

subsection \<open>Path connectedness of a space\<close>

definition "path_connected s \<longleftrightarrow>
  (\<forall>x\<in>s. \<forall>y\<in>s. \<exists>g. path g \<and> path_image g \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y)"

lemma path_connected_component: "path_connected s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. path_component s x y)"
  unfolding path_connected_def path_component_def by auto

lemma path_connected_component_set: "path_connected s \<longleftrightarrow> (\<forall>x\<in>s. {y. path_component s x y} = s)"
  unfolding path_connected_component path_component_subset
  apply auto
  using path_component_mem(2) by blast

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
    using continuous_open_in_preimage[OF g(1)[unfolded path_def] as(1)]
    using continuous_open_in_preimage[OF g(1)[unfolded path_def] as(2)]
    by auto
qed

lemma open_path_component:
  fixes s :: "'a::real_normed_vector set"
  assumes "open s"
  shows "open {y. path_component s x y}"
  unfolding open_contains_ball
proof
  fix y
  assume as: "y \<in> {y. path_component s x y}"
  then have "y \<in> s"
    apply -
    apply (rule path_component_mem(2))
    unfolding mem_Collect_eq
    apply auto
    done
  then obtain e where e: "e > 0" "ball y e \<subseteq> s"
    using assms[unfolded open_contains_ball]
    by auto
  show "\<exists>e > 0. ball y e \<subseteq> {y. path_component s x y}"
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
  shows "open (s - {y. path_component s x y})"
  unfolding open_contains_ball
proof
  fix y
  assume as: "y \<in> s - {y. path_component s x y}"
  then obtain e where e: "e > 0" "ball y e \<subseteq> s"
    using assms [unfolded open_contains_ball]
    by auto
  show "\<exists>e>0. ball y e \<subseteq> s - {y. path_component s x y}"
    apply (rule_tac x=e in exI)
    apply rule
    apply (rule \<open>e>0\<close>)
    apply rule
    apply rule
    defer
  proof (rule ccontr)
    fix z
    assume "z \<in> ball y e" "\<not> z \<notin> {y. path_component s x y}"
    then have "y \<in> {y. path_component s x y}"
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
  show "y \<in> {y. path_component s x y}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    moreover have "{y. path_component s x y} \<inter> s \<noteq> {}"
      using \<open>x \<in> s\<close> path_component_eq_empty path_component_subset[of s x]
      by auto
    ultimately
    show False
      using \<open>y \<in> s\<close> open_non_path_component[OF assms(1)] open_path_component[OF assms(1)]
      using assms(2)[unfolded connected_def not_ex, rule_format,
        of"{y. path_component s x y}" "s - {y. path_component s x y}"]
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


subsection \<open>Sphere is path-connected\<close>

lemma path_connected_punctured_universe:
  assumes "2 \<le> DIM('a::euclidean_space)"
  shows "path_connected ((UNIV::'a set) - {a})"
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
  also have "\<dots> = UNIV - {a}"
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
  have **: "{x::'a. norm x = 1} = (\<lambda>x. (1/norm x) *\<^sub>R x) ` (UNIV - {0})"
    apply (rule set_eqI)
    apply rule
    unfolding image_iff
    apply (rule_tac x=x in bexI)
    unfolding mem_Collect_eq
    apply (auto split: split_if_asm)
    done
  have "continuous_on (UNIV - {0}) (\<lambda>x::'a. 1 / norm x)"
    by (auto intro!: continuous_intros)
  then show ?thesis
    unfolding * **
    using path_connected_punctured_universe[OF assms]
    by (auto intro!: path_connected_continuous_image continuous_intros)
qed

lemma connected_sphere: "2 \<le> DIM('a::euclidean_space) \<Longrightarrow> connected {x::'a. norm (x - a) = r}"
  using path_connected_sphere path_connected_imp_connected
  by auto

end
