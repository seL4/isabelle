(*  Title:      HOL/Analysis/Path_Connected.thy
    Authors:    LC Paulson and Robert Himmelmann (TU Muenchen), based on material from HOL Light
*)

section \<open>Path-Connectedness\<close>

theory Path_Connected
imports
  Starlike
  T1_Spaces
begin

subsection \<open>Paths and Arcs\<close>

definition\<^marker>\<open>tag important\<close> path :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "path g \<longleftrightarrow> continuous_on {0..1} g"

definition\<^marker>\<open>tag important\<close> pathstart :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> 'a"
  where "pathstart g = g 0"

definition\<^marker>\<open>tag important\<close> pathfinish :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> 'a"
  where "pathfinish g = g 1"

definition\<^marker>\<open>tag important\<close> path_image :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> 'a set"
  where "path_image g = g ` {0 .. 1}"

definition\<^marker>\<open>tag important\<close> reversepath :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> real \<Rightarrow> 'a"
  where "reversepath g = (\<lambda>x. g(1 - x))"

definition\<^marker>\<open>tag important\<close> joinpaths :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a"
    (infixr "+++" 75)
  where "g1 +++ g2 = (\<lambda>x. if x \<le> 1/2 then g1 (2 * x) else g2 (2 * x - 1))"

definition\<^marker>\<open>tag important\<close> simple_path :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "simple_path g \<longleftrightarrow>
     path g \<and> (\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. g x = g y \<longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0)"

definition\<^marker>\<open>tag important\<close> arc :: "(real \<Rightarrow> 'a :: topological_space) \<Rightarrow> bool"
  where "arc g \<longleftrightarrow> path g \<and> inj_on g {0..1}"


subsection\<^marker>\<open>tag unimportant\<close>\<open>Invariance theorems\<close>

lemma path_eq: "path p \<Longrightarrow> (\<And>t. t \<in> {0..1} \<Longrightarrow> p t = q t) \<Longrightarrow> path q"
  using continuous_on_eq path_def by blast

lemma path_continuous_image: "path g \<Longrightarrow> continuous_on (path_image g) f \<Longrightarrow> path(f \<circ> g)"
  unfolding path_def path_image_def
  using continuous_on_compose by blast

lemma continuous_on_translation_eq:
  fixes g :: "'a :: real_normed_vector \<Rightarrow> 'b :: real_normed_vector"
  shows "continuous_on A ((+) a \<circ> g) = continuous_on A g"
proof -
  have g: "g = (\<lambda>x. -a + x) \<circ> ((\<lambda>x. a + x) \<circ> g)"
    by (rule ext) simp
  show ?thesis
    by (metis (no_types, hide_lams) g continuous_on_compose homeomorphism_def homeomorphism_translation)
qed

lemma path_translation_eq:
  fixes g :: "real \<Rightarrow> 'a :: real_normed_vector"
  shows "path((\<lambda>x. a + x) \<circ> g) = path g"
  using continuous_on_translation_eq path_def by blast

lemma path_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
   assumes "linear f" "inj f"
     shows "path(f \<circ> g) = path g"
proof -
  from linear_injective_left_inverse [OF assms]
  obtain h where h: "linear h" "h \<circ> f = id"
    by blast
  then have g: "g = h \<circ> (f \<circ> g)"
    by (metis comp_assoc id_comp)
  show ?thesis
    unfolding path_def
    using h assms
    by (metis g continuous_on_compose linear_continuous_on linear_conv_bounded_linear)
qed

lemma pathstart_translation: "pathstart((\<lambda>x. a + x) \<circ> g) = a + pathstart g"
  by (simp add: pathstart_def)

lemma pathstart_linear_image_eq: "linear f \<Longrightarrow> pathstart(f \<circ> g) = f(pathstart g)"
  by (simp add: pathstart_def)

lemma pathfinish_translation: "pathfinish((\<lambda>x. a + x) \<circ> g) = a + pathfinish g"
  by (simp add: pathfinish_def)

lemma pathfinish_linear_image: "linear f \<Longrightarrow> pathfinish(f \<circ> g) = f(pathfinish g)"
  by (simp add: pathfinish_def)

lemma path_image_translation: "path_image((\<lambda>x. a + x) \<circ> g) = (\<lambda>x. a + x) ` (path_image g)"
  by (simp add: image_comp path_image_def)

lemma path_image_linear_image: "linear f \<Longrightarrow> path_image(f \<circ> g) = f ` (path_image g)"
  by (simp add: image_comp path_image_def)

lemma reversepath_translation: "reversepath((\<lambda>x. a + x) \<circ> g) = (\<lambda>x. a + x) \<circ> reversepath g"
  by (rule ext) (simp add: reversepath_def)

lemma reversepath_linear_image: "linear f \<Longrightarrow> reversepath(f \<circ> g) = f \<circ> reversepath g"
  by (rule ext) (simp add: reversepath_def)

lemma joinpaths_translation:
    "((\<lambda>x. a + x) \<circ> g1) +++ ((\<lambda>x. a + x) \<circ> g2) = (\<lambda>x. a + x) \<circ> (g1 +++ g2)"
  by (rule ext) (simp add: joinpaths_def)

lemma joinpaths_linear_image: "linear f \<Longrightarrow> (f \<circ> g1) +++ (f \<circ> g2) = f \<circ> (g1 +++ g2)"
  by (rule ext) (simp add: joinpaths_def)

lemma simple_path_translation_eq:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  shows "simple_path((\<lambda>x. a + x) \<circ> g) = simple_path g"
  by (simp add: simple_path_def path_translation_eq)

lemma simple_path_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
    shows "simple_path(f \<circ> g) = simple_path g"
  using assms inj_on_eq_iff [of f]
  by (auto simp: path_linear_image_eq simple_path_def path_translation_eq)

lemma arc_translation_eq:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  shows "arc((\<lambda>x. a + x) \<circ> g) = arc g"
  by (auto simp: arc_def inj_on_def path_translation_eq)

lemma arc_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
   assumes "linear f" "inj f"
     shows  "arc(f \<circ> g) = arc g"
  using assms inj_on_eq_iff [of f]
  by (auto simp: arc_def inj_on_def path_linear_image_eq)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Basic lemmas about paths\<close>

lemma pathin_iff_path_real [simp]: "pathin euclideanreal g \<longleftrightarrow> path g"
  by (simp add: pathin_def path_def)

lemma continuous_on_path: "path f \<Longrightarrow> t \<subseteq> {0..1} \<Longrightarrow> continuous_on t f"
  using continuous_on_subset path_def by blast

lemma arc_imp_simple_path: "arc g \<Longrightarrow> simple_path g"
  by (simp add: arc_def inj_on_def simple_path_def)

lemma arc_imp_path: "arc g \<Longrightarrow> path g"
  using arc_def by blast

lemma arc_imp_inj_on: "arc g \<Longrightarrow> inj_on g {0..1}"
  by (auto simp: arc_def)

lemma simple_path_imp_path: "simple_path g \<Longrightarrow> path g"
  using simple_path_def by blast

lemma simple_path_cases: "simple_path g \<Longrightarrow> arc g \<or> pathfinish g = pathstart g"
  unfolding simple_path_def arc_def inj_on_def pathfinish_def pathstart_def
  by force

lemma simple_path_imp_arc: "simple_path g \<Longrightarrow> pathfinish g \<noteq> pathstart g \<Longrightarrow> arc g"
  using simple_path_cases by auto

lemma arc_distinct_ends: "arc g \<Longrightarrow> pathfinish g \<noteq> pathstart g"
  unfolding arc_def inj_on_def pathfinish_def pathstart_def
  by fastforce

lemma arc_simple_path: "arc g \<longleftrightarrow> simple_path g \<and> pathfinish g \<noteq> pathstart g"
  using arc_distinct_ends arc_imp_simple_path simple_path_cases by blast

lemma simple_path_eq_arc: "pathfinish g \<noteq> pathstart g \<Longrightarrow> (simple_path g = arc g)"
  by (simp add: arc_simple_path)

lemma path_image_const [simp]: "path_image (\<lambda>t. a) = {a}"
  by (force simp: path_image_def)

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

lemma reversepath_o: "reversepath g = g \<circ> (-)1"
  by (auto simp: reversepath_def)

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
    apply (auto intro: continuous_intros continuous_on_subset[of "{0..1}"])
    done
  show ?thesis
    using "*" by force
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
    using assms  by (clarsimp simp: arc_def intro!: inj_onI) (simp add: inj_onD reversepath_def **)
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


subsection\<^marker>\<open>tag unimportant\<close> \<open>Path Images\<close>

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
  assumes "pathfinish g1 = pathstart g2"
  shows "path_image(g1 +++ g2) = path_image g1 \<union> path_image g2"
proof -
  have "path_image g1 \<subseteq> path_image (g1 +++ g2)"
  proof (clarsimp simp: path_image_def joinpaths_def)
    fix u::real
    assume "0 \<le> u" "u \<le> 1"
    then show "g1 u \<in> (\<lambda>x. g1 (2 * x)) ` ({0..1} \<inter> {x. x * 2 \<le> 1})"
      by (rule_tac x="u/2" in image_eqI) auto
  qed
  moreover 
  have \<section>: "g2 u \<in> (\<lambda>x. g2 (2 * x - 1)) ` ({0..1} \<inter> {x. \<not> x * 2 \<le> 1})" 
    if "0 < u" "u \<le> 1" for u
    using that assms
    by (rule_tac x="(u+1)/2" in image_eqI) (auto simp: field_simps pathfinish_def pathstart_def)
  have "g2 0 \<in> (\<lambda>x. g1 (2 * x)) ` ({0..1} \<inter> {x. x * 2 \<le> 1})"
    using assms
    by (rule_tac x="1/2" in image_eqI) (auto simp: pathfinish_def pathstart_def)
  then have "path_image g2 \<subseteq> path_image (g1 +++ g2)"
    by (auto simp: path_image_def joinpaths_def intro!: \<section>)
  ultimately show ?thesis
    using path_image_join_subset by blast
qed

lemma not_in_path_image_join:
  assumes "x \<notin> path_image g1"
    and "x \<notin> path_image g2"
  shows "x \<notin> path_image (g1 +++ g2)"
  using assms and path_image_join_subset[of g1 g2]
  by auto

lemma pathstart_compose: "pathstart(f \<circ> p) = f(pathstart p)"
  by (simp add: pathstart_def)

lemma pathfinish_compose: "pathfinish(f \<circ> p) = f(pathfinish p)"
  by (simp add: pathfinish_def)

lemma path_image_compose: "path_image (f \<circ> p) = f ` (path_image p)"
  by (simp add: image_comp path_image_def)

lemma path_compose_join: "f \<circ> (p +++ q) = (f \<circ> p) +++ (f \<circ> q)"
  by (rule ext) (simp add: joinpaths_def)

lemma path_compose_reversepath: "f \<circ> reversepath p = reversepath(f \<circ> p)"
  by (rule ext) (simp add: reversepath_def)

lemma joinpaths_eq:
  "(\<And>t. t \<in> {0..1} \<Longrightarrow> p t = p' t) \<Longrightarrow>
   (\<And>t. t \<in> {0..1} \<Longrightarrow> q t = q' t)
   \<Longrightarrow>  t \<in> {0..1} \<Longrightarrow> (p +++ q) t = (p' +++ q') t"
  by (auto simp: joinpaths_def)

lemma simple_path_inj_on: "simple_path g \<Longrightarrow> inj_on g {0<..<1}"
  by (auto simp: simple_path_def path_image_def inj_on_def less_eq_real_def Ball_def)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Simple paths with the endpoints removed\<close>

lemma simple_path_endless:
  assumes "simple_path c"
  shows "path_image c - {pathstart c,pathfinish c} = c ` {0<..<1}" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    using less_eq_real_def by (auto simp: path_image_def pathstart_def pathfinish_def)
  show "?rhs \<subseteq> ?lhs"
    using assms 
    apply (auto simp: simple_path_def path_image_def pathstart_def pathfinish_def Ball_def)
    using less_eq_real_def zero_le_one by blast+
qed

lemma connected_simple_path_endless:
  assumes "simple_path c"
  shows "connected(path_image c - {pathstart c,pathfinish c})"
proof -
  have "continuous_on {0<..<1} c"
    using assms by (simp add: simple_path_def continuous_on_path path_def subset_iff)
  then have "connected (c ` {0<..<1})"
    using connected_Ioo connected_continuous_image by blast
  then show ?thesis
    using assms by (simp add: simple_path_endless)
qed

lemma nonempty_simple_path_endless:
    "simple_path c \<Longrightarrow> path_image c - {pathstart c,pathfinish c} \<noteq> {}"
  by (simp add: simple_path_endless)


subsection\<^marker>\<open>tag unimportant\<close>\<open>The operations on paths\<close>

lemma path_image_subset_reversepath: "path_image(reversepath g) \<le> path_image g"
  by simp

lemma path_imp_reversepath: "path g \<Longrightarrow> path(reversepath g)"
  by simp

lemma half_bounded_equal: "1 \<le> x * 2 \<Longrightarrow> x * 2 \<le> 1 \<longleftrightarrow> x = (1/2::real)"
  by simp

lemma continuous_on_joinpaths:
  assumes "continuous_on {0..1} g1" "continuous_on {0..1} g2" "pathfinish g1 = pathstart g2"
    shows "continuous_on {0..1} (g1 +++ g2)"
proof -
  have "{0..1::real} = {0..1/2} \<union> {1/2..1}"
    by auto
  then show ?thesis
    using assms by (metis path_def path_join)
qed

lemma path_join_imp: "\<lbrakk>path g1; path g2; pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow> path(g1 +++ g2)"
  by simp

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
    assume g2_eq: "g2 (2 * x - 1) = g1 (2 * y)"
      and xyI: "x \<noteq> 1 \<or> y \<noteq> 0"
      and xy: "x \<le> 1" "0 \<le> y" " y * 2 \<le> 1" "\<not> x * 2 \<le> 1" 
    then consider "g1 (2 * y) = g1 0" | "g1 (2 * y) = g2 0"
      using sb by force
    then have False
    proof cases
      case 1
      then have "y = 0"
        using xy g2_eq by (auto dest!: inj_onD [OF injg1])
      then show ?thesis
        using xy g2_eq xyI by (auto dest: inj_onD [OF injg2] simp flip: g21)
    next
      case 2
      then have "2*x = 1"
        using g2_eq g12 inj_onD [OF injg2] atLeastAtMost_iff xy(1) xy(4) by fastforce
      with xy show False by auto
    qed
  } note * = this
  { fix x and y::real
    assume xy: "g1 (2 * x) = g2 (2 * y - 1)" "y \<le> 1" "0 \<le> x" "\<not> y * 2 \<le> 1" "x * 2 \<le> 1" 
    then have "x = 0 \<and> y = 1"
      using * xy by force
   } note ** = this
  show ?thesis
    using assms
    apply (simp add: arc_def simple_path_def)
    apply (auto simp: joinpaths_def split: if_split_asm 
                dest!: * ** dest: inj_onD [OF injg1] inj_onD [OF injg2])
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
    assume xy: "g2 (2 * x - 1) = g1 (2 * y)" "x \<le> 1" "0 \<le> y" " y * 2 \<le> 1" "\<not> x * 2 \<le> 1"
    then have "g1 (2 * y) = g2 0"
      using sb by force
    then have False
      using xy inj_onD injg2 by fastforce
   } note * = this
  show ?thesis
    using assms
    apply (simp add: arc_def inj_on_def)
    apply (auto simp: joinpaths_def arc_imp_path split: if_split_asm 
                dest: * *[OF sym] inj_onD [OF injg1] inj_onD [OF injg2])
    done
qed

lemma reversepath_joinpaths:
    "pathfinish g1 = pathstart g2 \<Longrightarrow> reversepath(g1 +++ g2) = reversepath g2 +++ reversepath g1"
  unfolding reversepath_def pathfinish_def pathstart_def joinpaths_def
  by (rule ext) (auto simp: mult.commute)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Some reversed and "if and only if" versions of joining theorems\<close>

lemma path_join_path_ends:
  fixes g1 :: "real \<Rightarrow> 'a::metric_space"
  assumes "path(g1 +++ g2)" "path g2"
    shows "pathfinish g1 = pathstart g2"
proof (rule ccontr)
  define e where "e = dist (g1 1) (g2 0)"
  assume Neg: "pathfinish g1 \<noteq> pathstart g2"
  then have "0 < dist (pathfinish g1) (pathstart g2)"
    by auto
  then have "e > 0"
    by (metis e_def pathfinish_def pathstart_def)
  then have "\<forall>e>0. \<exists>d>0. \<forall>x'\<in>{0..1}. dist x' 0 < d \<longrightarrow> dist (g2 x') (g2 0) < e"
    using \<open>path g2\<close> atLeastAtMost_iff zero_le_one unfolding path_def continuous_on_iff
    by blast
  then obtain d1 where "d1 > 0"
       and d1: "\<And>x'. \<lbrakk>x'\<in>{0..1}; norm x' < d1\<rbrakk> \<Longrightarrow> dist (g2 x') (g2 0) < e/2"
    by (metis \<open>0 < e\<close> half_gt_zero_iff norm_conv_dist)
  obtain d2 where "d2 > 0"
       and d2: "\<And>x'. \<lbrakk>x'\<in>{0..1}; dist x' (1/2) < d2\<rbrakk>
                      \<Longrightarrow> dist ((g1 +++ g2) x') (g1 1) < e/2"
    using assms(1) \<open>e > 0\<close> unfolding path_def continuous_on_iff
    apply (drule_tac x="1/2" in bspec, simp)
    apply (drule_tac x="e/2" in spec, force simp: joinpaths_def)
    done
  have int01_1: "min (1/2) (min d1 d2) / 2 \<in> {0..1}"
    using \<open>d1 > 0\<close> \<open>d2 > 0\<close> by (simp add: min_def)
  have dist1: "norm (min (1 / 2) (min d1 d2) / 2) < d1"
    using \<open>d1 > 0\<close> \<open>d2 > 0\<close> by (simp add: min_def dist_norm)
  have int01_2: "1/2 + min (1/2) (min d1 d2) / 4 \<in> {0..1}"
    using \<open>d1 > 0\<close> \<open>d2 > 0\<close> by (simp add: min_def)
  have dist2: "dist (1 / 2 + min (1 / 2) (min d1 d2) / 4) (1 / 2) < d2"
    using \<open>d1 > 0\<close> \<open>d2 > 0\<close> by (simp add: min_def dist_norm)
  have [simp]: "\<not> min (1 / 2) (min d1 d2) \<le> 0"
    using \<open>d1 > 0\<close> \<open>d2 > 0\<close> by (simp add: min_def)
  have "dist (g2 (min (1 / 2) (min d1 d2) / 2)) (g1 1) < e/2"
       "dist (g2 (min (1 / 2) (min d1 d2) / 2)) (g2 0) < e/2"
    using d1 [OF int01_1 dist1] d2 [OF int01_2 dist2] by (simp_all add: joinpaths_def)
  then have "dist (g1 1) (g2 0) < e/2 + e/2"
    using dist_triangle_half_r e_def by blast
  then show False
    by (simp add: e_def [symmetric])
qed

lemma path_join_eq [simp]:
  fixes g1 :: "real \<Rightarrow> 'a::metric_space"
  assumes "path g1" "path g2"
    shows "path(g1 +++ g2) \<longleftrightarrow> pathfinish g1 = pathstart g2"
  using assms by (metis path_join_path_ends path_join_imp)

lemma simple_path_joinE:
  assumes "simple_path(g1 +++ g2)" and "pathfinish g1 = pathstart g2"
  obtains "arc g1" "arc g2"
          "path_image g1 \<inter> path_image g2 \<subseteq> {pathstart g1, pathstart g2}"
proof -
  have *: "\<And>x y. \<lbrakk>0 \<le> x; x \<le> 1; 0 \<le> y; y \<le> 1; (g1 +++ g2) x = (g1 +++ g2) y\<rbrakk>
               \<Longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
    using assms by (simp add: simple_path_def)
  have "path g1"
    using assms path_join simple_path_imp_path by blast
  moreover have "inj_on g1 {0..1}"
  proof (clarsimp simp: inj_on_def)
    fix x y
    assume "g1 x = g1 y" "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1"
    then show "x = y"
      using * [of "x/2" "y/2"] by (simp add: joinpaths_def split_ifs)
  qed
  ultimately have "arc g1"
    using assms  by (simp add: arc_def)
  have [simp]: "g2 0 = g1 1"
    using assms by (metis pathfinish_def pathstart_def)
  have "path g2"
    using assms path_join simple_path_imp_path by blast
  moreover have "inj_on g2 {0..1}"
  proof (clarsimp simp: inj_on_def)
    fix x y
    assume "g2 x = g2 y" "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1"
    then show "x = y"
      using * [of "(x + 1) / 2" "(y + 1) / 2"]
      by (force simp: joinpaths_def split_ifs field_split_simps)
  qed
  ultimately have "arc g2"
    using assms  by (simp add: arc_def)
  have "g2 y = g1 0 \<or> g2 y = g1 1"
       if "g1 x = g2 y" "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1" for x y
      using * [of "x / 2" "(y + 1) / 2"] that
      by (auto simp: joinpaths_def split_ifs field_split_simps)
  then have "path_image g1 \<inter> path_image g2 \<subseteq> {pathstart g1, pathstart g2}"
    by (fastforce simp: pathstart_def pathfinish_def path_image_def)
  with \<open>arc g1\<close> \<open>arc g2\<close> show ?thesis using that by blast
qed

lemma simple_path_join_loop_eq:
  assumes "pathfinish g2 = pathstart g1" "pathfinish g1 = pathstart g2"
    shows "simple_path(g1 +++ g2) \<longleftrightarrow>
             arc g1 \<and> arc g2 \<and> path_image g1 \<inter> path_image g2 \<subseteq> {pathstart g1, pathstart g2}"
by (metis assms simple_path_joinE simple_path_join_loop)

lemma arc_join_eq:
  assumes "pathfinish g1 = pathstart g2"
    shows "arc(g1 +++ g2) \<longleftrightarrow>
           arc g1 \<and> arc g2 \<and> path_image g1 \<inter> path_image g2 \<subseteq> {pathstart g2}"
           (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "simple_path(g1 +++ g2)" by (rule arc_imp_simple_path)
  then have *: "\<And>x y. \<lbrakk>0 \<le> x; x \<le> 1; 0 \<le> y; y \<le> 1; (g1 +++ g2) x = (g1 +++ g2) y\<rbrakk>
               \<Longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
    using assms by (simp add: simple_path_def)
  have False if "g1 0 = g2 u" "0 \<le> u" "u \<le> 1" for u
    using * [of 0 "(u + 1) / 2"] that assms arc_distinct_ends [OF \<open>?lhs\<close>]
    by (auto simp: joinpaths_def pathstart_def pathfinish_def split_ifs field_split_simps)
  then have n1: "pathstart g1 \<notin> path_image g2"
    unfolding pathstart_def path_image_def
    using atLeastAtMost_iff by blast
  show ?rhs using \<open>?lhs\<close>
    using \<open>simple_path (g1 +++ g2)\<close> assms n1 simple_path_joinE by auto
next
  assume ?rhs then show ?lhs
    using assms
    by (fastforce simp: pathfinish_def pathstart_def intro!: arc_join)
qed

lemma arc_join_eq_alt:
        "pathfinish g1 = pathstart g2
        \<Longrightarrow> (arc(g1 +++ g2) \<longleftrightarrow>
             arc g1 \<and> arc g2 \<and>
             path_image g1 \<inter> path_image g2 = {pathstart g2})"
using pathfinish_in_path_image by (fastforce simp: arc_join_eq)


subsection\<^marker>\<open>tag unimportant\<close>\<open>The joining of paths is associative\<close>

lemma path_assoc:
    "\<lbrakk>pathfinish p = pathstart q; pathfinish q = pathstart r\<rbrakk>
     \<Longrightarrow> path(p +++ (q +++ r)) \<longleftrightarrow> path((p +++ q) +++ r)"
by simp

lemma simple_path_assoc:
  assumes "pathfinish p = pathstart q" "pathfinish q = pathstart r"
    shows "simple_path (p +++ (q +++ r)) \<longleftrightarrow> simple_path ((p +++ q) +++ r)"
proof (cases "pathstart p = pathfinish r")
  case True show ?thesis
  proof
    assume "simple_path (p +++ q +++ r)"
    with assms True show "simple_path ((p +++ q) +++ r)"
      by (fastforce simp add: simple_path_join_loop_eq arc_join_eq path_image_join
                    dest: arc_distinct_ends [of r])
  next
    assume 0: "simple_path ((p +++ q) +++ r)"
    with assms True have q: "pathfinish r \<notin> path_image q"
      using arc_distinct_ends
      by (fastforce simp add: simple_path_join_loop_eq arc_join_eq path_image_join)
    have "pathstart r \<notin> path_image p"
      using assms
      by (metis 0 IntI arc_distinct_ends arc_join_eq_alt empty_iff insert_iff
              pathfinish_in_path_image pathfinish_join simple_path_joinE)
    with assms 0 q True show "simple_path (p +++ q +++ r)"
      by (auto simp: simple_path_join_loop_eq arc_join_eq path_image_join
               dest!: subsetD [OF _ IntI])
  qed
next
  case False
  { fix x :: 'a
    assume a: "path_image p \<inter> path_image q \<subseteq> {pathstart q}"
              "(path_image p \<union> path_image q) \<inter> path_image r \<subseteq> {pathstart r}"
              "x \<in> path_image p" "x \<in> path_image r"
    have "pathstart r \<in> path_image q"
      by (metis assms(2) pathfinish_in_path_image)
    with a have "x = pathstart q"
      by blast
  }
  with False assms show ?thesis
    by (auto simp: simple_path_eq_arc simple_path_join_loop_eq arc_join_eq path_image_join)
qed

lemma arc_assoc:
     "\<lbrakk>pathfinish p = pathstart q; pathfinish q = pathstart r\<rbrakk>
      \<Longrightarrow> arc(p +++ (q +++ r)) \<longleftrightarrow> arc((p +++ q) +++ r)"
by (simp add: arc_simple_path simple_path_assoc)

subsubsection\<^marker>\<open>tag unimportant\<close>\<open>Symmetry and loops\<close>

lemma path_sym:
    "\<lbrakk>pathfinish p = pathstart q; pathfinish q = pathstart p\<rbrakk> \<Longrightarrow> path(p +++ q) \<longleftrightarrow> path(q +++ p)"
  by auto

lemma simple_path_sym:
    "\<lbrakk>pathfinish p = pathstart q; pathfinish q = pathstart p\<rbrakk>
     \<Longrightarrow> simple_path(p +++ q) \<longleftrightarrow> simple_path(q +++ p)"
by (metis (full_types) inf_commute insert_commute simple_path_joinE simple_path_join_loop)

lemma path_image_sym:
    "\<lbrakk>pathfinish p = pathstart q; pathfinish q = pathstart p\<rbrakk>
     \<Longrightarrow> path_image(p +++ q) = path_image(q +++ p)"
by (simp add: path_image_join sup_commute)


subsection\<open>Subpath\<close>

definition\<^marker>\<open>tag important\<close> subpath :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a::real_normed_vector"
  where "subpath a b g \<equiv> \<lambda>x. g((b - a) * x + a)"

lemma path_image_subpath_gen:
  fixes g :: "_ \<Rightarrow> 'a::real_normed_vector"
  shows "path_image(subpath u v g) = g ` (closed_segment u v)"
  by (auto simp add: closed_segment_real_eq path_image_def subpath_def)

lemma path_image_subpath:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector"
  shows "path_image(subpath u v g) = (if u \<le> v then g ` {u..v} else g ` {v..u})"
  by (simp add: path_image_subpath_gen closed_segment_eq_real_ivl)

lemma path_image_subpath_commute:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector"
  shows "path_image(subpath u v g) = path_image(subpath v u g)"
  by (simp add: path_image_subpath_gen closed_segment_eq_real_ivl)

lemma path_subpath [simp]:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "path g" "u \<in> {0..1}" "v \<in> {0..1}"
    shows "path(subpath u v g)"
proof -
  have "continuous_on {0..1} (g \<circ> (\<lambda>x. ((v-u) * x+ u)))"
    using assms
    apply (intro continuous_intros; simp add: image_affinity_atLeastAtMost [where c=u])
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

lemma subpath_translation: "subpath u v ((\<lambda>x. a + x) \<circ> g) = (\<lambda>x. a + x) \<circ> subpath u v g"
  by (rule ext) (simp add: subpath_def)

lemma subpath_image: "subpath u v (f \<circ> g) = f \<circ> subpath u v g"
  by (rule ext) (simp add: subpath_def)

lemma affine_ineq:
  fixes x :: "'a::linordered_idom"
  assumes "x \<le> 1" "v \<le> u"
    shows "v + x * u \<le> u + x * v"
proof -
  have "(1-x)*(u-v) \<ge> 0"
    using assms by auto
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma sum_le_prod1:
  fixes a::real shows "\<lbrakk>a \<le> 1; b \<le> 1\<rbrakk> \<Longrightarrow> a + b \<le> 1 + a * b"
by (metis add.commute affine_ineq mult.right_neutral)

lemma simple_path_subpath_eq:
  "simple_path(subpath u v g) \<longleftrightarrow>
     path(subpath u v g) \<and> u\<noteq>v \<and>
     (\<forall>x y. x \<in> closed_segment u v \<and> y \<in> closed_segment u v \<and> g x = g y
                \<longrightarrow> x = y \<or> x = u \<and> y = v \<or> x = v \<and> y = u)"
    (is "?lhs = ?rhs")
proof 
  assume ?lhs
  then have p: "path (\<lambda>x. g ((v - u) * x + u))"
        and sim: "(\<And>x y. \<lbrakk>x\<in>{0..1}; y\<in>{0..1}; g ((v - u) * x + u) = g ((v - u) * y + u)\<rbrakk>
                  \<Longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0)"
    by (auto simp: simple_path_def subpath_def)
  { fix x y
    assume "x \<in> closed_segment u v" "y \<in> closed_segment u v" "g x = g y"
    then have "x = y \<or> x = u \<and> y = v \<or> x = v \<and> y = u"
      using sim [of "(x-u)/(v-u)" "(y-u)/(v-u)"] p
      by (auto split: if_split_asm simp add: closed_segment_real_eq image_affinity_atLeastAtMost)
        (simp_all add: field_split_simps)
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
proof 
  assume ?lhs
  then have p: "path (\<lambda>x. g ((v - u) * x + u))"
        and sim: "(\<And>x y. \<lbrakk>x\<in>{0..1}; y\<in>{0..1}; g ((v - u) * x + u) = g ((v - u) * y + u)\<rbrakk>
                  \<Longrightarrow> x = y)"
    by (auto simp: arc_def inj_on_def subpath_def)
  { fix x y
    assume "x \<in> closed_segment u v" "y \<in> closed_segment u v" "g x = g y"
    then have "x = y"
      using sim [of "(x-u)/(v-u)" "(y-u)/(v-u)"] p
      by (cases "v = u")
        (simp_all split: if_split_asm add: inj_on_def closed_segment_real_eq image_affinity_atLeastAtMost,
           simp add: field_simps)
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
  by (force simp: simple_path_def intro: arc_simple_path_subpath)

lemma path_image_subpath_subset:
    "\<lbrakk>u \<in> {0..1}; v \<in> {0..1}\<rbrakk> \<Longrightarrow> path_image(subpath u v g) \<subseteq> path_image g"
  by (metis atLeastAtMost_iff atLeastatMost_subset_iff path_image_def path_image_subpath subset_image_iff)

lemma join_subpaths_middle: "subpath (0) ((1 / 2)) p +++ subpath ((1 / 2)) 1 p = p"
  by (rule ext) (simp add: joinpaths_def subpath_def field_split_simps)


subsection\<^marker>\<open>tag unimportant\<close>\<open>There is a subpath to the frontier\<close>

lemma subpath_to_frontier_explicit:
    fixes S :: "'a::metric_space set"
    assumes g: "path g" and "pathfinish g \<notin> S"
    obtains u where "0 \<le> u" "u \<le> 1"
                "\<And>x. 0 \<le> x \<and> x < u \<Longrightarrow> g x \<in> interior S"
                "(g u \<notin> interior S)" "(u = 0 \<or> g u \<in> closure S)"
proof -
  have gcon: "continuous_on {0..1} g"     
    using g by (simp add: path_def)
  moreover have "bounded ({u. g u \<in> closure (- S)} \<inter> {0..1})"
    using compact_eq_bounded_closed by fastforce
  ultimately have com: "compact ({0..1} \<inter> {u. g u \<in> closure (- S)})"
    using closed_vimage_Int
    by (metis (full_types) Int_commute closed_atLeastAtMost closed_closure compact_eq_bounded_closed vimage_def)
  have "1 \<in> {u. g u \<in> closure (- S)}"
    using assms by (simp add: pathfinish_def closure_def)
  then have dis: "{0..1} \<inter> {u. g u \<in> closure (- S)} \<noteq> {}"
    using atLeastAtMost_iff zero_le_one by blast
  then obtain u where "0 \<le> u" "u \<le> 1" and gu: "g u \<in> closure (- S)"
                  and umin: "\<And>t. \<lbrakk>0 \<le> t; t \<le> 1; g t \<in> closure (- S)\<rbrakk> \<Longrightarrow> u \<le> t"
    using compact_attains_inf [OF com dis] by fastforce
  then have umin': "\<And>t. \<lbrakk>0 \<le> t; t \<le> 1; t < u\<rbrakk> \<Longrightarrow>  g t \<in> S"
    using closure_def by fastforce
  have \<section>: "g u \<in> closure S" if "u \<noteq> 0"
  proof -
    have "u > 0" using that \<open>0 \<le> u\<close> by auto
    { fix e::real assume "e > 0"
      obtain d where "d>0" and d: "\<And>x'. \<lbrakk>x' \<in> {0..1}; dist x' u \<le> d\<rbrakk> \<Longrightarrow> dist (g x') (g u) < e"
        using continuous_onE [OF gcon _ \<open>e > 0\<close>] \<open>0 \<le> _\<close> \<open>_ \<le> 1\<close> atLeastAtMost_iff by auto
      have *: "dist (max 0 (u - d / 2)) u \<le> d"
        using \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> \<open>d > 0\<close> by (simp add: dist_real_def)
      have "\<exists>y\<in>S. dist y (g u) < e"
        using \<open>0 < u\<close> \<open>u \<le> 1\<close> \<open>d > 0\<close>
        by (force intro: d [OF _ *] umin')
    }
    then show ?thesis
      by (simp add: frontier_def closure_approachable)
  qed
  show ?thesis
  proof
    show "\<And>x. 0 \<le> x \<and> x < u \<Longrightarrow> g x \<in> interior S"
      using \<open>u \<le> 1\<close> interior_closure umin by fastforce
    show "g u \<notin> interior S"
      by (simp add: gu interior_closure)
  qed (use \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> \<section> in auto)
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
  proof
    show "g u \<notin> interior S"
      using gunot by blast
  qed (use \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> u0 in \<open>(force simp: subpath_def gxin)+\<close>)
qed

lemma subpath_to_frontier:
    assumes g: "path g" and g0: "pathstart g \<in> closure S" and g1: "pathfinish g \<notin> S"
    obtains u where "0 \<le> u" "u \<le> 1" "g u \<in> frontier S" "path_image(subpath 0 u g) - {g u} \<subseteq> interior S"
proof -
  obtain u where "0 \<le> u" "u \<le> 1"
             and notin: "g u \<notin> interior S"
             and disj: "u = 0 \<or>
                        (\<forall>x. 0 \<le> x \<and> x < 1 \<longrightarrow> subpath 0 u g x \<in> interior S) \<and> g u \<in> closure S"
                       (is "_ \<or> ?P")
    using subpath_to_frontier_strong [OF g g1] by blast
  show ?thesis
  proof
    show "g u \<in> frontier S"
      by (metis DiffI disj frontier_def g0 notin pathstart_def)
    show "path_image (subpath 0 u g) - {g u} \<subseteq> interior S"
      using disj
    proof
      assume "u = 0"
      then show ?thesis
        by (simp add: path_image_subpath)
    next
      assume P: ?P
      show ?thesis
      proof (clarsimp simp add: path_image_subpath_gen)
        fix y
        assume y: "y \<in> closed_segment 0 u" "g y \<notin> interior S"
        with \<open>0 \<le> u\<close> have "0 \<le> y" "y \<le> u" 
          by (auto simp: closed_segment_eq_real_ivl split: if_split_asm)
        then have "y=u \<or> subpath 0 u g (y/u) \<in> interior S"
          using P less_eq_real_def by force
        then show "g y = g u"
          using y by (auto simp: subpath_def split: if_split_asm)
      qed
    qed
  qed (use \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> in auto)
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
  proof
    show "path_image (subpath 0 u g) \<subseteq> path_image g"
      by (simp add: path_image_subpath_subset u)
    show "pathstart (subpath 0 u g) = pathstart g"
      by (metis pathstart_def pathstart_subpath)
  qed (use assms u in \<open>auto simp: path_image_subpath\<close>)
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
  proof
    show "path_image h \<subseteq> path_image g \<inter> S"
      using assms h interior_subset [of S] by (auto simp: frontier_def)
  qed (use h in auto)
qed


subsection \<open>Shift Path to Start at Some Given Point\<close>

definition\<^marker>\<open>tag important\<close> shiftpath :: "real \<Rightarrow> (real \<Rightarrow> 'a::topological_space) \<Rightarrow> real \<Rightarrow> 'a"
  where "shiftpath a f = (\<lambda>x. if (a + x) \<le> 1 then f (a + x) else f (a + x - 1))"

lemma shiftpath_alt_def: "shiftpath a f = (\<lambda>x. if x \<le> 1-a then f (a + x) else f (a + x - 1))"
  by (auto simp: shiftpath_def)

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
  proof (rule continuous_on_closed_Un)
    have contg: "continuous_on {0..1} g"
      using \<open>path g\<close> path_def by blast
    show "continuous_on {0..1-a} (\<lambda>x. if a + x \<le> 1 then g (a + x) else g (a + x - 1))"
    proof (rule continuous_on_eq)
      show "continuous_on {0..1-a} (g \<circ> (+) a)"
        by (intro continuous_intros continuous_on_subset [OF contg]) (use \<open>a \<in> {0..1}\<close> in auto)
    qed auto
    show "continuous_on {1-a..1} (\<lambda>x. if a + x \<le> 1 then g (a + x) else g (a + x - 1))"
    proof (rule continuous_on_eq)
      show "continuous_on {1-a..1} (g \<circ> (+) (a - 1))"
        by (intro continuous_intros continuous_on_subset [OF contg]) (use \<open>a \<in> {0..1}\<close> in auto)
    qed (auto simp:  "**" add.commute add_diff_eq)
  qed auto
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
  assumes a: "a \<in> {0..1}"
    and "pathfinish g = pathstart g"
  shows "path_image (shiftpath a g) = path_image g"
proof -
  { fix x
    assume g: "g 1 = g 0" "x \<in> {0..1::real}" and gne: "\<And>y. y\<in>{0..1} \<inter> {x. \<not> a + x \<le> 1} \<Longrightarrow> g x \<noteq> g (a + y - 1)"
    then have "\<exists>y\<in>{0..1} \<inter> {x. a + x \<le> 1}. g x = g (a + y)"
    proof (cases "a \<le> x")
      case False
      then show ?thesis
        apply (rule_tac x="1 + x - a" in bexI)
        using g gne[of "1 + x - a"] a by (force simp: field_simps)+
    next
      case True
      then show ?thesis
        using g a  by (rule_tac x="x - a" in bexI) (auto simp: field_simps)
    qed
  }
  then show ?thesis
    using assms
    unfolding shiftpath_def path_image_def pathfinish_def pathstart_def
    by (auto simp: image_iff)
qed

lemma simple_path_shiftpath:
  assumes "simple_path g" "pathfinish g = pathstart g" and a: "0 \<le> a" "a \<le> 1"
    shows "simple_path (shiftpath a g)"
  unfolding simple_path_def
proof (intro conjI impI ballI)
  show "path (shiftpath a g)"
    by (simp add: assms path_shiftpath simple_path_imp_path)
  have *: "\<And>x y. \<lbrakk>g x = g y; x \<in> {0..1}; y \<in> {0..1}\<rbrakk> \<Longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
    using assms by (simp add:  simple_path_def)
  show "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
    if "x \<in> {0..1}" "y \<in> {0..1}" "shiftpath a g x = shiftpath a g y" for x y
    using that a unfolding shiftpath_def
    by (force split: if_split_asm dest!: *)
qed


subsection \<open>Straight-Line Paths\<close>

definition\<^marker>\<open>tag important\<close> linepath :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a"
  where "linepath a b = (\<lambda>x. (1 - x) *\<^sub>R a + x *\<^sub>R b)"

lemma pathstart_linepath[simp]: "pathstart (linepath a b) = a"
  unfolding pathstart_def linepath_def
  by auto

lemma pathfinish_linepath[simp]: "pathfinish (linepath a b) = b"
  unfolding pathfinish_def linepath_def
  by auto

lemma linepath_inner: "linepath a b x \<bullet> v = linepath (a \<bullet> v) (b \<bullet> v) x"
  by (simp add: linepath_def algebra_simps)

lemma Re_linepath': "Re (linepath a b x) = linepath (Re a) (Re b) x"
  by (simp add: linepath_def)

lemma Im_linepath': "Im (linepath a b x) = linepath (Im a) (Im b) x"
  by (simp add: linepath_def)

lemma linepath_0': "linepath a b 0 = a"
  by (simp add: linepath_def)

lemma linepath_1': "linepath a b 1 = b"
  by (simp add: linepath_def)

lemma continuous_linepath_at[intro]: "continuous (at x) (linepath a b)"
  unfolding linepath_def
  by (intro continuous_intros)

lemma continuous_on_linepath [intro,continuous_intros]: "continuous_on s (linepath a b)"
  using continuous_linepath_at
  by (auto intro!: continuous_at_imp_continuous_on)

lemma path_linepath[iff]: "path (linepath a b)"
  unfolding path_def
  by (rule continuous_on_linepath)

lemma path_image_linepath[simp]: "path_image (linepath a b) = closed_segment a b"
  unfolding path_image_def segment linepath_def
  by auto

lemma reversepath_linepath[simp]: "reversepath (linepath a b) = linepath b a"
  unfolding reversepath_def linepath_def
  by auto

lemma linepath_0 [simp]: "linepath 0 b x = x *\<^sub>R b"
  by (simp add: linepath_def)

lemma linepath_cnj: "cnj (linepath a b x) = linepath (cnj a) (cnj b) x"
  by (simp add: linepath_def)

lemma arc_linepath:
  assumes "a \<noteq> b" shows [simp]: "arc (linepath a b)"
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
    by (fastforce simp: algebra_simps linepath_def)
qed

lemma simple_path_linepath[intro]: "a \<noteq> b \<Longrightarrow> simple_path (linepath a b)"
  by (simp add: arc_imp_simple_path)

lemma linepath_trivial [simp]: "linepath a a x = a"
  by (simp add: linepath_def real_vector.scale_left_diff_distrib)

lemma linepath_refl: "linepath a a = (\<lambda>x. a)"
  by auto

lemma subpath_refl: "subpath a a g = linepath (g a) (g a)"
  by (simp add: subpath_def linepath_def algebra_simps)

lemma linepath_of_real: "(linepath (of_real a) (of_real b) x) = of_real ((1 - x)*a + x*b)"
  by (simp add: scaleR_conv_of_real linepath_def)

lemma of_real_linepath: "of_real (linepath a b x) = linepath (of_real a) (of_real b) x"
  by (metis linepath_of_real mult.right_neutral of_real_def real_scaleR_def)

lemma inj_on_linepath:
  assumes "a \<noteq> b" shows "inj_on (linepath a b) {0..1}"
proof (clarsimp simp: inj_on_def linepath_def)
  fix x y
  assume "(1 - x) *\<^sub>R a + x *\<^sub>R b = (1 - y) *\<^sub>R a + y *\<^sub>R b" "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1"
  then have "x *\<^sub>R (a - b) = y *\<^sub>R (a - b)"
    by (auto simp: algebra_simps)
  then show "x=y"
    using assms by auto
qed

lemma linepath_le_1:
  fixes a::"'a::linordered_idom" shows "\<lbrakk>a \<le> 1; b \<le> 1; 0 \<le> u; u \<le> 1\<rbrakk> \<Longrightarrow> (1 - u) * a + u * b \<le> 1"
  using mult_left_le [of a "1-u"] mult_left_le [of b u] by auto

lemma linepath_in_path:
  shows "x \<in> {0..1} \<Longrightarrow> linepath a b x \<in> closed_segment a b"
  by (auto simp: segment linepath_def)

lemma linepath_image_01: "linepath a b ` {0..1} = closed_segment a b"
  by (auto simp: segment linepath_def)

lemma linepath_in_convex_hull:
  fixes x::real
  assumes a: "a \<in> convex hull S"
    and b: "b \<in> convex hull S"
    and x: "0\<le>x" "x\<le>1"
  shows "linepath a b x \<in> convex hull S"
proof -
  have "linepath a b x \<in> closed_segment a b"
    using x by (auto simp flip: linepath_image_01)
  then show ?thesis
    using a b convex_contains_segment by blast
qed

lemma Re_linepath: "Re(linepath (of_real a) (of_real b) x) = (1 - x)*a + x*b"
  by (simp add: linepath_def)

lemma Im_linepath: "Im(linepath (of_real a) (of_real b) x) = 0"
  by (simp add: linepath_def)

lemma bounded_linear_linepath:
  assumes "bounded_linear f"
  shows   "f (linepath a b x) = linepath (f a) (f b) x"
proof -
  interpret f: bounded_linear f by fact
  show ?thesis by (simp add: linepath_def f.add f.scale)
qed

lemma bounded_linear_linepath':
  assumes "bounded_linear f"
  shows   "f \<circ> linepath a b = linepath (f a) (f b)"
  using bounded_linear_linepath[OF assms] by (simp add: fun_eq_iff)

lemma linepath_cnj': "cnj \<circ> linepath a b = linepath (cnj a) (cnj b)"
  by (simp add: linepath_def fun_eq_iff)

lemma differentiable_linepath [intro]: "linepath a b differentiable at x within A"
  by (auto simp: linepath_def)

lemma has_vector_derivative_linepath_within:
    "(linepath a b has_vector_derivative (b - a)) (at x within S)"
  by (force intro: derivative_eq_intros simp add: linepath_def has_vector_derivative_def algebra_simps)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Segments via convex hulls\<close>

lemma segments_subset_convex_hull:
    "closed_segment a b \<subseteq> (convex hull {a,b,c})"
    "closed_segment a c \<subseteq> (convex hull {a,b,c})"
    "closed_segment b c \<subseteq> (convex hull {a,b,c})"
    "closed_segment b a \<subseteq> (convex hull {a,b,c})"
    "closed_segment c a \<subseteq> (convex hull {a,b,c})"
    "closed_segment c b \<subseteq> (convex hull {a,b,c})"
by (auto simp: segment_convex_hull linepath_of_real  elim!: rev_subsetD [OF _ hull_mono])

lemma midpoints_in_convex_hull:
  assumes "x \<in> convex hull s" "y \<in> convex hull s"
    shows "midpoint x y \<in> convex hull s"
proof -
  have "(1 - inverse(2)) *\<^sub>R x + inverse(2) *\<^sub>R y \<in> convex hull s"
    by (rule convexD_alt) (use assms in auto)
  then show ?thesis
    by (simp add: midpoint_def algebra_simps)
qed

lemma not_in_interior_convex_hull_3:
  fixes a :: "complex"
  shows "a \<notin> interior(convex hull {a,b,c})"
        "b \<notin> interior(convex hull {a,b,c})"
        "c \<notin> interior(convex hull {a,b,c})"
  by (auto simp: card_insert_le_m1 not_in_interior_convex_hull)

lemma midpoint_in_closed_segment [simp]: "midpoint a b \<in> closed_segment a b"
  using midpoints_in_convex_hull segment_convex_hull by blast

lemma midpoint_in_open_segment [simp]: "midpoint a b \<in> open_segment a b \<longleftrightarrow> a \<noteq> b"
  by (simp add: open_segment_def)

lemma continuous_IVT_local_extremum:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes contf: "continuous_on (closed_segment a b) f"
      and "a \<noteq> b" "f a = f b"
  obtains z where "z \<in> open_segment a b"
                  "(\<forall>w \<in> closed_segment a b. (f w) \<le> (f z)) \<or>
                   (\<forall>w \<in> closed_segment a b. (f z) \<le> (f w))"
proof -
  obtain c where "c \<in> closed_segment a b" and c: "\<And>y. y \<in> closed_segment a b \<Longrightarrow> f y \<le> f c"
    using continuous_attains_sup [of "closed_segment a b" f] contf by auto
  obtain d where "d \<in> closed_segment a b" and d: "\<And>y. y \<in> closed_segment a b \<Longrightarrow> f d \<le> f y"
    using continuous_attains_inf [of "closed_segment a b" f] contf by auto
  show ?thesis
  proof (cases "c \<in> open_segment a b \<or> d \<in> open_segment a b")
    case True
    then show ?thesis
      using c d that by blast
  next
    case False
    then have "(c = a \<or> c = b) \<and> (d = a \<or> d = b)"
      by (simp add: \<open>c \<in> closed_segment a b\<close> \<open>d \<in> closed_segment a b\<close> open_segment_def)
    with \<open>a \<noteq> b\<close> \<open>f a = f b\<close> c d show ?thesis
      by (rule_tac z = "midpoint a b" in that) (fastforce+)
  qed
qed

text\<open>An injective map into R is also an open map w.r.T. the universe, and conversely. \<close>
proposition injective_eq_1d_open_map_UNIV:
  fixes f :: "real \<Rightarrow> real"
  assumes contf: "continuous_on S f" and S: "is_interval S"
    shows "inj_on f S \<longleftrightarrow> (\<forall>T. open T \<and> T \<subseteq> S \<longrightarrow> open(f ` T))"
          (is "?lhs = ?rhs")
proof safe
  fix T
  assume injf: ?lhs and "open T" and "T \<subseteq> S"
  have "\<exists>U. open U \<and> f x \<in> U \<and> U \<subseteq> f ` T" if "x \<in> T" for x
  proof -
    obtain \<delta> where "\<delta> > 0" and \<delta>: "cball x \<delta> \<subseteq> T"
      using \<open>open T\<close> \<open>x \<in> T\<close> open_contains_cball_eq by blast
    show ?thesis
    proof (intro exI conjI)
      have "closed_segment (x-\<delta>) (x+\<delta>) = {x-\<delta>..x+\<delta>}"
        using \<open>0 < \<delta>\<close> by (auto simp: closed_segment_eq_real_ivl)
      also have "\<dots> \<subseteq> S"
        using \<delta> \<open>T \<subseteq> S\<close> by (auto simp: dist_norm subset_eq)
      finally have "f ` (open_segment (x-\<delta>) (x+\<delta>)) = open_segment (f (x-\<delta>)) (f (x+\<delta>))"
        using continuous_injective_image_open_segment_1
        by (metis continuous_on_subset [OF contf] inj_on_subset [OF injf])
      then show "open (f ` {x-\<delta><..<x+\<delta>})"
        using \<open>0 < \<delta>\<close> by (simp add: open_segment_eq_real_ivl)
      show "f x \<in> f ` {x - \<delta><..<x + \<delta>}"
        by (auto simp: \<open>\<delta> > 0\<close>)
      show "f ` {x - \<delta><..<x + \<delta>} \<subseteq> f ` T"
        using \<delta> by (auto simp: dist_norm subset_iff)
    qed
  qed
  with open_subopen show "open (f ` T)"
    by blast
next
  assume R: ?rhs
  have False if xy: "x \<in> S" "y \<in> S" and "f x = f y" "x \<noteq> y" for x y
  proof -
    have "open (f ` open_segment x y)"
      using R
      by (metis S convex_contains_open_segment is_interval_convex open_greaterThanLessThan open_segment_eq_real_ivl xy)
    moreover
    have "continuous_on (closed_segment x y) f"
      by (meson S closed_segment_subset contf continuous_on_subset is_interval_convex that)
    then obtain \<xi> where "\<xi> \<in> open_segment x y"
                    and \<xi>: "(\<forall>w \<in> closed_segment x y. (f w) \<le> (f \<xi>)) \<or>
                            (\<forall>w \<in> closed_segment x y. (f \<xi>) \<le> (f w))"
      using continuous_IVT_local_extremum [of x y f] \<open>f x = f y\<close> \<open>x \<noteq> y\<close> by blast
    ultimately obtain e where "e>0" and e: "\<And>u. dist u (f \<xi>) < e \<Longrightarrow> u \<in> f ` open_segment x y"
      using open_dist by (metis image_eqI)
    have fin: "f \<xi> + (e/2) \<in> f ` open_segment x y" "f \<xi> - (e/2) \<in> f ` open_segment x y"
      using e [of "f \<xi> + (e/2)"] e [of "f \<xi> - (e/2)"] \<open>e > 0\<close> by (auto simp: dist_norm)
    show ?thesis
      using \<xi> \<open>0 < e\<close> fin open_closed_segment by fastforce
  qed
  then show ?lhs
    by (force simp: inj_on_def)
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Bounding a point away from a path\<close>

lemma not_on_path_ball:
  fixes g :: "real \<Rightarrow> 'a::heine_borel"
  assumes "path g"
    and z: "z \<notin> path_image g"
  shows "\<exists>e > 0. ball z e \<inter> path_image g = {}"
proof -
  have "closed (path_image g)"
    by (simp add: \<open>path g\<close> closed_path_image)
  then obtain a where "a \<in> path_image g" "\<forall>y \<in> path_image g. dist z a \<le> dist z y"
    by (auto intro: distance_attains_inf[OF _ path_image_nonempty, of g z])
  then show ?thesis
    by (rule_tac x="dist z a" in exI) (use dist_commute z in auto)
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
    by (rule_tac x="e/2" in exI) auto
qed

subsection \<open>Path component\<close>

text \<open>Original formalization by Tom Hales\<close>

definition\<^marker>\<open>tag important\<close> "path_component S x y \<equiv>
  (\<exists>g. path g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y)"

abbreviation\<^marker>\<open>tag important\<close>
  "path_component_set S x \<equiv> Collect (path_component S x)"

lemmas path_defs = path_def pathstart_def pathfinish_def path_image_def path_component_def

lemma path_component_mem:
  assumes "path_component S x y"
  shows "x \<in> S" and "y \<in> S"
  using assms
  unfolding path_defs
  by auto

lemma path_component_refl:
  assumes "x \<in> S"
  shows "path_component S x x"
  using assms
  unfolding path_defs
  by (metis (full_types) assms continuous_on_const image_subset_iff path_image_def)

lemma path_component_refl_eq: "path_component S x x \<longleftrightarrow> x \<in> S"
  by (auto intro!: path_component_mem path_component_refl)

lemma path_component_sym: "path_component S x y \<Longrightarrow> path_component S y x"
  unfolding path_component_def
  by (metis (no_types) path_image_reversepath path_reversepath pathfinish_reversepath pathstart_reversepath)

lemma path_component_trans:
  assumes "path_component S x y" and "path_component S y z"
  shows "path_component S x z"
  using assms
  unfolding path_component_def
  by (metis path_join pathfinish_join pathstart_join subset_path_image_join)

lemma path_component_of_subset: "S \<subseteq> T \<Longrightarrow> path_component S x y \<Longrightarrow> path_component T x y"
  unfolding path_component_def by auto

lemma path_component_linepath:
    fixes S :: "'a::real_normed_vector set"
    shows "closed_segment a b \<subseteq> S \<Longrightarrow> path_component S a b"
  unfolding path_component_def
  by (rule_tac x="linepath a b" in exI, auto)

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Path components as sets\<close>

lemma path_component_set:
  "path_component_set S x =
    {y. (\<exists>g. path g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y)}"
  by (auto simp: path_component_def)

lemma path_component_subset: "path_component_set S x \<subseteq> S"
  by (auto simp: path_component_mem(2))

lemma path_component_eq_empty: "path_component_set S x = {} \<longleftrightarrow> x \<notin> S"
  using path_component_mem path_component_refl_eq
    by fastforce

lemma path_component_mono:
     "S \<subseteq> T \<Longrightarrow> (path_component_set S x) \<subseteq> (path_component_set T x)"
  by (simp add: Collect_mono path_component_of_subset)

lemma path_component_eq:
   "y \<in> path_component_set S x \<Longrightarrow> path_component_set S y = path_component_set S x"
by (metis (no_types, lifting) Collect_cong mem_Collect_eq path_component_sym path_component_trans)


subsection \<open>Path connectedness of a space\<close>

definition\<^marker>\<open>tag important\<close> "path_connected S \<longleftrightarrow>
  (\<forall>x\<in>S. \<forall>y\<in>S. \<exists>g. path g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y)"

lemma path_connectedin_iff_path_connected_real [simp]:
     "path_connectedin euclideanreal S \<longleftrightarrow> path_connected S"
  by (simp add: path_connectedin path_connected_def path_defs)

lemma path_connected_component: "path_connected S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. path_component S x y)"
  unfolding path_connected_def path_component_def by auto

lemma path_connected_component_set: "path_connected S \<longleftrightarrow> (\<forall>x\<in>S. path_component_set S x = S)"
  unfolding path_connected_component path_component_subset
  using path_component_mem by blast

lemma path_component_maximal:
     "\<lbrakk>x \<in> T; path_connected T; T \<subseteq> S\<rbrakk> \<Longrightarrow> T \<subseteq> (path_component_set S x)"
  by (metis path_component_mono path_connected_component_set)

lemma convex_imp_path_connected:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S"
  shows "path_connected S"
  unfolding path_connected_def
  using assms convex_contains_segment by fastforce

lemma path_connected_UNIV [iff]: "path_connected (UNIV :: 'a::real_normed_vector set)"
  by (simp add: convex_imp_path_connected)

lemma path_component_UNIV: "path_component_set UNIV x = (UNIV :: 'a::real_normed_vector set)"
  using path_connected_component_set by auto

lemma path_connected_imp_connected:
  assumes "path_connected S"
  shows "connected S"
proof (rule connectedI)
  fix e1 e2
  assume as: "open e1" "open e2" "S \<subseteq> e1 \<union> e2" "e1 \<inter> e2 \<inter> S = {}" "e1 \<inter> S \<noteq> {}" "e2 \<inter> S \<noteq> {}"
  then obtain x1 x2 where obt:"x1 \<in> e1 \<inter> S" "x2 \<in> e2 \<inter> S"
    by auto
  then obtain g where g: "path g" "path_image g \<subseteq> S" "pathstart g = x1" "pathfinish g = x2"
    using assms[unfolded path_connected_def,rule_format,of x1 x2] by auto
  have *: "connected {0..1::real}"
    by (auto intro!: convex_connected)
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
      of "{0..1} \<inter> g -` e1" "{0..1} \<inter> g -` e2"]
    using continuous_openin_preimage_gen[OF g(1)[unfolded path_def] as(1)]
    using continuous_openin_preimage_gen[OF g(1)[unfolded path_def] as(2)]
    by auto
qed

lemma open_path_component:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open (path_component_set S x)"
  unfolding open_contains_ball
proof
  fix y
  assume as: "y \<in> path_component_set S x"
  then have "y \<in> S"
    by (simp add: path_component_mem(2))
  then obtain e where e: "e > 0" "ball y e \<subseteq> S"
    using assms openE by blast
have "\<And>u. dist y u < e \<Longrightarrow> path_component S x u"
      by (metis (full_types) as centre_in_ball convex_ball convex_imp_path_connected e mem_Collect_eq mem_ball path_component_eq path_component_of_subset path_connected_component)
  then show "\<exists>e > 0. ball y e \<subseteq> path_component_set S x"
    using \<open>e>0\<close> by auto
qed

lemma open_non_path_component:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open (S - path_component_set S x)"
  unfolding open_contains_ball
proof
  fix y
  assume y: "y \<in> S - path_component_set S x"
  then obtain e where e: "e > 0" "ball y e \<subseteq> S"
    using assms openE by auto
  show "\<exists>e>0. ball y e \<subseteq> S - path_component_set S x"
  proof (intro exI conjI subsetI DiffI notI)
    show "\<And>x. x \<in> ball y e \<Longrightarrow> x \<in> S"
      using e by blast
    show False if "z \<in> ball y e" "z \<in> path_component_set S x" for z
    proof -
      have "y \<in> path_component_set S z"
        by (meson assms convex_ball convex_imp_path_connected e open_contains_ball_eq open_path_component path_component_maximal that(1))
      then have "y \<in> path_component_set S x"
        using path_component_eq that(2) by blast
      then show False
        using y by blast
    qed
  qed (use e in auto)
qed

lemma connected_open_path_connected:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
    and "connected S"
  shows "path_connected S"
  unfolding path_connected_component_set
proof (rule, rule, rule path_component_subset, rule)
  fix x y
  assume "x \<in> S" and "y \<in> S"
  show "y \<in> path_component_set S x"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    moreover have "path_component_set S x \<inter> S \<noteq> {}"
      using \<open>x \<in> S\<close> path_component_eq_empty path_component_subset[of S x]
      by auto
    ultimately
    show False
      using \<open>y \<in> S\<close> open_non_path_component[OF assms(1)] open_path_component[OF assms(1)]
      using assms(2)[unfolded connected_def not_ex, rule_format,
        of "path_component_set S x" "S - path_component_set S x"]
      by auto
  qed
qed

lemma path_connected_continuous_image:
  assumes contf: "continuous_on S f"
    and "path_connected S"
  shows "path_connected (f ` S)"
  unfolding path_connected_def
proof (rule, rule)
  fix x' y'
  assume "x' \<in> f ` S" "y' \<in> f ` S"
  then obtain x y where x: "x \<in> S" and y: "y \<in> S" and x': "x' = f x" and y': "y' = f y"
    by auto
  from x y obtain g where "path g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y"
    using assms(2)[unfolded path_connected_def] by fast
  then show "\<exists>g. path g \<and> path_image g \<subseteq> f ` S \<and> pathstart g = x' \<and> pathfinish g = y'"
    unfolding x' y' path_defs
    by (fastforce intro: continuous_on_compose continuous_on_subset[OF contf])
qed

lemma path_connected_translationI:
  fixes a :: "'a :: topological_group_add"
  assumes "path_connected S" shows "path_connected ((\<lambda>x. a + x) ` S)"
  by (intro path_connected_continuous_image assms continuous_intros)

lemma path_connected_translation:
  fixes a :: "'a :: topological_group_add"
  shows "path_connected ((\<lambda>x. a + x) ` S) = path_connected S"
proof -
  have "\<forall>x y. (+) (x::'a) ` (+) (0 - x) ` y = y"
    by (simp add: image_image)
  then show ?thesis
    by (metis (no_types) path_connected_translationI)
qed

lemma path_connected_segment [simp]:
    fixes a :: "'a::real_normed_vector"
    shows "path_connected (closed_segment a b)"
  by (simp add: convex_imp_path_connected)

lemma path_connected_open_segment [simp]:
    fixes a :: "'a::real_normed_vector"
    shows "path_connected (open_segment a b)"
  by (simp add: convex_imp_path_connected)

lemma homeomorphic_path_connectedness:
  "S homeomorphic T \<Longrightarrow> path_connected S \<longleftrightarrow> path_connected T"
  unfolding homeomorphic_def homeomorphism_def by (metis path_connected_continuous_image)

lemma path_connected_empty [simp]: "path_connected {}"
  unfolding path_connected_def by auto

lemma path_connected_singleton [simp]: "path_connected {a}"
  unfolding path_connected_def pathstart_def pathfinish_def path_image_def
  using path_def by fastforce

lemma path_connected_Un:
  assumes "path_connected S"
    and "path_connected T"
    and "S \<inter> T \<noteq> {}"
  shows "path_connected (S \<union> T)"
  unfolding path_connected_component
proof (intro ballI)
  fix x y
  assume x: "x \<in> S \<union> T" and y: "y \<in> S \<union> T"
  from assms obtain z where z: "z \<in> S" "z \<in> T"
    by auto
  show "path_component (S \<union> T) x y"
    using x y
  proof safe
    assume "x \<in> S" "y \<in> S"
    then show "path_component (S \<union> T) x y"
      by (meson Un_upper1 \<open>path_connected S\<close> path_component_of_subset path_connected_component)
  next
    assume "x \<in> S" "y \<in> T"
    then show "path_component (S \<union> T) x y"
      by (metis z assms(1-2) le_sup_iff order_refl path_component_of_subset path_component_trans path_connected_component)
  next
  assume "x \<in> T" "y \<in> S"
    then show "path_component (S \<union> T) x y"
      by (metis z assms(1-2) le_sup_iff order_refl path_component_of_subset path_component_trans path_connected_component)
  next
    assume "x \<in> T" "y \<in> T"
    then show "path_component (S \<union> T) x y"
      by (metis Un_upper1 assms(2) path_component_of_subset path_connected_component sup_commute)
  qed
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
proof -
  obtain y where x: "x = p y" and y: "0 \<le> y" "y \<le> 1"
    using x by (auto simp: path_image_def)
  show ?thesis
    unfolding path_component_def 
  proof (intro exI conjI)
    have "continuous_on ((*) y ` {0..1}) p"
      by (simp add: continuous_on_path image_mult_atLeastAtMost_if p y)
    then have "continuous_on {0..1} (p \<circ> ((*) y))"
      using continuous_on_compose continuous_on_mult_const by blast
    then show "path (\<lambda>u. p (y * u))"
      by (simp add: path_def)
    show "path_image (\<lambda>u. p (y * u)) \<subseteq> path_image p"
      using y mult_le_one by (fastforce simp: path_image_def image_iff)
  qed (auto simp: pathstart_def pathfinish_def x)
qed

lemma path_connected_path_image: "path p \<Longrightarrow> path_connected(path_image p)"
  unfolding path_connected_component
  by (meson path_component_path_image_pathstart path_component_sym path_component_trans)

lemma path_connected_path_component [simp]:
   "path_connected (path_component_set s x)"
proof -
  { fix y z
    assume pa: "path_component s x y" "path_component s x z"
    then have pae: "path_component_set s x = path_component_set s y"
      using path_component_eq by auto
    have yz: "path_component s y z"
      using pa path_component_sym path_component_trans by blast
    then have "\<exists>g. path g \<and> path_image g \<subseteq> path_component_set s x \<and> pathstart g = y \<and> pathfinish g = z"
      apply (simp add: path_component_def)
      by (metis pae path_component_maximal path_connected_path_image pathstart_in_path_image)
  }
  then show ?thesis
    by (simp add: path_connected_def)
qed

lemma path_component: "path_component S x y \<longleftrightarrow> (\<exists>t. path_connected t \<and> t \<subseteq> S \<and> x \<in> t \<and> y \<in> t)"
  apply (intro iffI)
  apply (metis path_connected_path_image path_defs(5) pathfinish_in_path_image pathstart_in_path_image)
  using path_component_of_subset path_connected_component by blast

lemma path_component_path_component [simp]:
   "path_component_set (path_component_set S x) x = path_component_set S x"
proof (cases "x \<in> S")
  case True show ?thesis
    by (metis True mem_Collect_eq path_component_refl path_connected_component_set path_connected_path_component)
next
  case False then show ?thesis
    by (metis False empty_iff path_component_eq_empty)
qed

lemma path_component_subset_connected_component:
   "(path_component_set S x) \<subseteq> (connected_component_set S x)"
proof (cases "x \<in> S")
  case True show ?thesis
    by (simp add: True connected_component_maximal path_component_refl path_component_subset path_connected_imp_connected)
next
  case False then show ?thesis
    using path_component_eq_empty by auto
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Lemmas about path-connectedness\<close>

lemma path_connected_linear_image:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "path_connected S" "bounded_linear f"
    shows "path_connected(f ` S)"
by (auto simp: linear_continuous_on assms path_connected_continuous_image)

lemma is_interval_path_connected: "is_interval S \<Longrightarrow> path_connected S"
  by (simp add: convex_imp_path_connected is_interval_convex)

lemma path_connected_Ioi[simp]: "path_connected {a<..}" for a :: real
  by (simp add: convex_imp_path_connected)

lemma path_connected_Ici[simp]: "path_connected {a..}" for a :: real
  by (simp add: convex_imp_path_connected)

lemma path_connected_Iio[simp]: "path_connected {..<a}" for a :: real
  by (simp add: convex_imp_path_connected)

lemma path_connected_Iic[simp]: "path_connected {..a}" for a :: real
  by (simp add: convex_imp_path_connected)

lemma path_connected_Ioo[simp]: "path_connected {a<..<b}" for a b :: real
  by (simp add: convex_imp_path_connected)

lemma path_connected_Ioc[simp]: "path_connected {a<..b}" for a b :: real
  by (simp add: convex_imp_path_connected)

lemma path_connected_Ico[simp]: "path_connected {a..<b}" for a b :: real
  by (simp add: convex_imp_path_connected)

lemma path_connectedin_path_image:
  assumes "pathin X g" shows "path_connectedin X (g ` ({0..1}))"
  unfolding pathin_def
proof (rule path_connectedin_continuous_map_image)
  show "continuous_map (subtopology euclideanreal {0..1}) X g"
    using assms pathin_def by blast
qed (auto simp: is_interval_1 is_interval_path_connected)

lemma path_connected_space_subconnected:
     "path_connected_space X \<longleftrightarrow>
      (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. \<exists>S. path_connectedin X S \<and> x \<in> S \<and> y \<in> S)"
  by (metis path_connectedin path_connectedin_topspace path_connected_space_def)


lemma connectedin_path_image: "pathin X g \<Longrightarrow> connectedin X (g ` ({0..1}))"
  by (simp add: path_connectedin_imp_connectedin path_connectedin_path_image)

lemma compactin_path_image: "pathin X g \<Longrightarrow> compactin X (g ` ({0..1}))"
  unfolding pathin_def
  by (rule image_compactin [of "top_of_set {0..1}"]) auto

lemma linear_homeomorphism_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
  obtains g where "homeomorphism (f ` S) S g f"
proof -
  obtain g where "linear g" "g \<circ> f = id"
    using assms linear_injective_left_inverse by blast
  then have "homeomorphism (f ` S) S g f"
    using assms unfolding homeomorphism_def
    by (auto simp: eq_id_iff [symmetric] image_comp linear_conv_bounded_linear linear_continuous_on)
  then show thesis ..
qed

lemma linear_homeomorphic_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
    shows "S homeomorphic f ` S"
by (meson homeomorphic_def homeomorphic_sym linear_homeomorphism_image [OF assms])

lemma path_connected_Times:
  assumes "path_connected s" "path_connected t"
    shows "path_connected (s \<times> t)"
proof (simp add: path_connected_def Sigma_def, clarify)
  fix x1 y1 x2 y2
  assume "x1 \<in> s" "y1 \<in> t" "x2 \<in> s" "y2 \<in> t"
  obtain g where "path g" and g: "path_image g \<subseteq> s" and gs: "pathstart g = x1" and gf: "pathfinish g = x2"
    using \<open>x1 \<in> s\<close> \<open>x2 \<in> s\<close> assms by (force simp: path_connected_def)
  obtain h where "path h" and h: "path_image h \<subseteq> t" and hs: "pathstart h = y1" and hf: "pathfinish h = y2"
    using \<open>y1 \<in> t\<close> \<open>y2 \<in> t\<close> assms by (force simp: path_connected_def)
  have "path (\<lambda>z. (x1, h z))"
    using \<open>path h\<close>
    unfolding path_def
    by (intro continuous_intros continuous_on_compose2 [where g = "Pair _"]; force)
  moreover have "path (\<lambda>z. (g z, y2))"
    using \<open>path g\<close>
    unfolding path_def
    by (intro continuous_intros continuous_on_compose2 [where g = "Pair _"]; force)
  ultimately have 1: "path ((\<lambda>z. (x1, h z)) +++ (\<lambda>z. (g z, y2)))"
    by (metis hf gs path_join_imp pathstart_def pathfinish_def)
  have "path_image ((\<lambda>z. (x1, h z)) +++ (\<lambda>z. (g z, y2))) \<subseteq> path_image (\<lambda>z. (x1, h z)) \<union> path_image (\<lambda>z. (g z, y2))"
    by (rule Path_Connected.path_image_join_subset)
  also have "\<dots> \<subseteq> (\<Union>x\<in>s. \<Union>x1\<in>t. {(x, x1)})"
    using g h \<open>x1 \<in> s\<close> \<open>y2 \<in> t\<close> by (force simp: path_image_def)
  finally have 2: "path_image ((\<lambda>z. (x1, h z)) +++ (\<lambda>z. (g z, y2))) \<subseteq> (\<Union>x\<in>s. \<Union>x1\<in>t. {(x, x1)})" .
  show "\<exists>g. path g \<and> path_image g \<subseteq> (\<Union>x\<in>s. \<Union>x1\<in>t. {(x, x1)}) \<and>
            pathstart g = (x1, y1) \<and> pathfinish g = (x2, y2)"
    using 1 2 gf hs
    by (metis (no_types, lifting) pathfinish_def pathfinish_join pathstart_def pathstart_join)
qed

lemma is_interval_path_connected_1:
  fixes s :: "real set"
  shows "is_interval s \<longleftrightarrow> path_connected s"
using is_interval_connected_1 is_interval_path_connected path_connected_imp_connected by blast


subsection\<^marker>\<open>tag unimportant\<close>\<open>Path components\<close>

lemma Union_path_component [simp]:
   "Union {path_component_set S x |x. x \<in> S} = S"
apply (rule subset_antisym)
using path_component_subset apply force
using path_component_refl by auto

lemma path_component_disjoint:
   "disjnt (path_component_set S a) (path_component_set S b) \<longleftrightarrow>
    (a \<notin> path_component_set S b)"
  unfolding disjnt_iff
  using path_component_sym path_component_trans by blast

lemma path_component_eq_eq:
   "path_component S x = path_component S y \<longleftrightarrow>
        (x \<notin> S) \<and> (y \<notin> S) \<or> x \<in> S \<and> y \<in> S \<and> path_component S x y"
    (is "?lhs = ?rhs")
proof 
  assume ?lhs then show ?rhs
    by (metis (no_types) path_component_mem(1) path_component_refl)
next
  assume ?rhs then show ?lhs
  proof
    assume "x \<notin> S \<and> y \<notin> S" then show ?lhs
      by (metis Collect_empty_eq_bot path_component_eq_empty)
  next
    assume S: "x \<in> S \<and> y \<in> S \<and> path_component S x y" show ?lhs
      by (rule ext) (metis S path_component_trans path_component_sym)
  qed
qed

lemma path_component_unique:
  assumes "x \<in> c" "c \<subseteq> S" "path_connected c"
          "\<And>c'. \<lbrakk>x \<in> c'; c' \<subseteq> S; path_connected c'\<rbrakk> \<Longrightarrow> c' \<subseteq> c"
   shows "path_component_set S x = c"
    (is "?lhs = ?rhs")
proof 
  show "?lhs \<subseteq> ?rhs"
    using assms
    by (metis mem_Collect_eq path_component_refl path_component_subset path_connected_path_component subsetD)
qed (simp add: assms path_component_maximal)

lemma path_component_intermediate_subset:
   "path_component_set u a \<subseteq> t \<and> t \<subseteq> u
        \<Longrightarrow> path_component_set t a = path_component_set u a"
by (metis (no_types) path_component_mono path_component_path_component subset_antisym)

lemma complement_path_component_Union:
  fixes x :: "'a :: topological_space"
  shows "S - path_component_set S x =
         \<Union>({path_component_set S y| y. y \<in> S} - {path_component_set S x})"
proof -
  have *: "(\<And>x. x \<in> S - {a} \<Longrightarrow> disjnt a x) \<Longrightarrow> \<Union>S - a = \<Union>(S - {a})"
    for a::"'a set" and S
    by (auto simp: disjnt_def)
  have "\<And>y. y \<in> {path_component_set S x |x. x \<in> S} - {path_component_set S x}
            \<Longrightarrow> disjnt (path_component_set S x) y"
    using path_component_disjoint path_component_eq by fastforce
  then have "\<Union>{path_component_set S x |x. x \<in> S} - path_component_set S x =
             \<Union>({path_component_set S y |y. y \<in> S} - {path_component_set S x})"
    by (meson *)
  then show ?thesis by simp
qed


subsection\<open>Path components\<close>

definition path_component_of
  where "path_component_of X x y \<equiv> \<exists>g. pathin X g \<and> g 0 = x \<and> g 1 = y"

abbreviation path_component_of_set
  where "path_component_of_set X x \<equiv> Collect (path_component_of X x)"

definition path_components_of :: "'a topology \<Rightarrow> 'a set set"
  where "path_components_of X \<equiv> path_component_of_set X ` topspace X"

lemma pathin_canon_iff: "pathin (top_of_set T) g \<longleftrightarrow> path g \<and> g ` {0..1} \<subseteq> T"
  by (simp add: path_def pathin_def)

lemma path_component_of_canon_iff [simp]:
  "path_component_of (top_of_set T) a b \<longleftrightarrow> path_component T a b"
  by (simp add: path_component_of_def pathin_canon_iff path_defs)

lemma path_component_in_topspace:
   "path_component_of X x y \<Longrightarrow> x \<in> topspace X \<and> y \<in> topspace X"
  by (auto simp: path_component_of_def pathin_def continuous_map_def)

lemma path_component_of_refl:
   "path_component_of X x x \<longleftrightarrow> x \<in> topspace X"
  by (metis path_component_in_topspace path_component_of_def pathin_const)

lemma path_component_of_sym:
  assumes "path_component_of X x y"
  shows "path_component_of X y x"
  using assms
  apply (clarsimp simp: path_component_of_def pathin_def)
  apply (rule_tac x="g \<circ> (\<lambda>t. 1 - t)" in exI)
  apply (auto intro!: continuous_map_compose simp: continuous_map_in_subtopology continuous_on_op_minus)
  done

lemma path_component_of_sym_iff:
   "path_component_of X x y \<longleftrightarrow> path_component_of X y x"
  by (metis path_component_of_sym)

lemma continuous_map_cases_le:
  assumes contp: "continuous_map X euclideanreal p"
    and contq: "continuous_map X euclideanreal q"
    and contf: "continuous_map (subtopology X {x. x \<in> topspace X \<and> p x \<le> q x}) Y f"
    and contg: "continuous_map (subtopology X {x. x \<in> topspace X \<and> q x \<le> p x}) Y g"
    and fg: "\<And>x. \<lbrakk>x \<in> topspace X; p x = q x\<rbrakk> \<Longrightarrow> f x = g x"
  shows "continuous_map X Y (\<lambda>x. if p x \<le> q x then f x else g x)"
proof -
  have "continuous_map X Y (\<lambda>x. if q x - p x \<in> {0..} then f x else g x)"
  proof (rule continuous_map_cases_function)
    show "continuous_map X euclideanreal (\<lambda>x. q x - p x)"
      by (intro contp contq continuous_intros)
    show "continuous_map (subtopology X {x \<in> topspace X. q x - p x \<in> euclideanreal closure_of {0..}}) Y f"
      by (simp add: contf)
    show "continuous_map (subtopology X {x \<in> topspace X. q x - p x \<in> euclideanreal closure_of (topspace euclideanreal - {0..})}) Y g"
      by (simp add: contg flip: Compl_eq_Diff_UNIV)
  qed (auto simp: fg)
  then show ?thesis
    by simp
qed

lemma continuous_map_cases_lt:
  assumes contp: "continuous_map X euclideanreal p"
    and contq: "continuous_map X euclideanreal q"
    and contf: "continuous_map (subtopology X {x. x \<in> topspace X \<and> p x \<le> q x}) Y f"
    and contg: "continuous_map (subtopology X {x. x \<in> topspace X \<and> q x \<le> p x}) Y g"
    and fg: "\<And>x. \<lbrakk>x \<in> topspace X; p x = q x\<rbrakk> \<Longrightarrow> f x = g x"
  shows "continuous_map X Y (\<lambda>x. if p x < q x then f x else g x)"
proof -
  have "continuous_map X Y (\<lambda>x. if q x - p x \<in> {0<..} then f x else g x)"
  proof (rule continuous_map_cases_function)
    show "continuous_map X euclideanreal (\<lambda>x. q x - p x)"
      by (intro contp contq continuous_intros)
    show "continuous_map (subtopology X {x \<in> topspace X. q x - p x \<in> euclideanreal closure_of {0<..}}) Y f"
      by (simp add: contf)
    show "continuous_map (subtopology X {x \<in> topspace X. q x - p x \<in> euclideanreal closure_of (topspace euclideanreal - {0<..})}) Y g"
      by (simp add: contg flip: Compl_eq_Diff_UNIV)
  qed (auto simp: fg)
  then show ?thesis
    by simp
qed

lemma path_component_of_trans:
  assumes "path_component_of X x y" and "path_component_of X y z"
  shows "path_component_of X x z"
  unfolding path_component_of_def pathin_def
proof -
  let ?T01 = "top_of_set {0..1::real}"
  obtain g1 g2 where g1: "continuous_map ?T01 X g1" "x = g1 0" "y = g1 1"
    and g2: "continuous_map ?T01 X g2" "g2 0 = g1 1" "z = g2 1"
    using assms unfolding path_component_of_def pathin_def by blast
  let ?g = "\<lambda>x. if x \<le> 1/2 then (g1 \<circ> (\<lambda>t. 2 * t)) x else (g2 \<circ> (\<lambda>t. 2 * t -1)) x"
  show "\<exists>g. continuous_map ?T01 X g \<and> g 0 = x \<and> g 1 = z"
  proof (intro exI conjI)
    show "continuous_map (subtopology euclideanreal {0..1}) X ?g"
    proof (intro continuous_map_cases_le continuous_map_compose, force, force)
      show "continuous_map (subtopology ?T01 {x \<in> topspace ?T01. x \<le> 1/2}) ?T01 ((*) 2)"
        by (auto simp: continuous_map_in_subtopology continuous_map_from_subtopology)
      have "continuous_map
             (subtopology (top_of_set {0..1}) {x. 0 \<le> x \<and> x \<le> 1 \<and> 1 \<le> x * 2})
             euclideanreal (\<lambda>t. 2 * t - 1)"
        by (intro continuous_intros) (force intro: continuous_map_from_subtopology)
      then show "continuous_map (subtopology ?T01 {x \<in> topspace ?T01. 1/2 \<le> x}) ?T01 (\<lambda>t. 2 * t - 1)"
        by (force simp: continuous_map_in_subtopology)
      show "(g1 \<circ> (*) 2) x = (g2 \<circ> (\<lambda>t. 2 * t - 1)) x" if "x \<in> topspace ?T01" "x = 1/2" for x
        using that by (simp add: g2(2) mult.commute continuous_map_from_subtopology)
    qed (auto simp: g1 g2)
  qed (auto simp: g1 g2)
qed

lemma path_component_of_mono:
   "\<lbrakk>path_component_of (subtopology X S) x y; S \<subseteq> T\<rbrakk> \<Longrightarrow> path_component_of (subtopology X T) x y"
  unfolding path_component_of_def
  by (metis subsetD pathin_subtopology)

lemma path_component_of:
  "path_component_of X x y \<longleftrightarrow> (\<exists>T. path_connectedin X T \<and> x \<in> T \<and> y \<in> T)"
    (is "?lhs = ?rhs")
proof 
  assume ?lhs then show ?rhs
    by (metis atLeastAtMost_iff image_eqI order_refl path_component_of_def path_connectedin_path_image zero_le_one)
next
  assume ?rhs then show ?lhs
    by (metis path_component_of_def path_connectedin)
qed

lemma path_component_of_set:
   "path_component_of X x y \<longleftrightarrow> (\<exists>g. pathin X g \<and> g 0 = x \<and> g 1 = y)"
  by (auto simp: path_component_of_def)

lemma path_component_of_subset_topspace:
   "Collect(path_component_of X x) \<subseteq> topspace X"
  using path_component_in_topspace by fastforce

lemma path_component_of_eq_empty:
   "Collect(path_component_of X x) = {} \<longleftrightarrow> (x \<notin> topspace X)"
  using path_component_in_topspace path_component_of_refl by fastforce

lemma path_connected_space_iff_path_component:
   "path_connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. path_component_of X x y)"
  by (simp add: path_component_of path_connected_space_subconnected)

lemma path_connected_space_imp_path_component_of:
   "\<lbrakk>path_connected_space X; a \<in> topspace X; b \<in> topspace X\<rbrakk>
        \<Longrightarrow> path_component_of X a b"
  by (simp add: path_connected_space_iff_path_component)

lemma path_connected_space_path_component_set:
   "path_connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. Collect(path_component_of X x) = topspace X)"
  using path_component_of_subset_topspace path_connected_space_iff_path_component by fastforce

lemma path_component_of_maximal:
   "\<lbrakk>path_connectedin X s; x \<in> s\<rbrakk> \<Longrightarrow> s \<subseteq> Collect(path_component_of X x)"
  using path_component_of by fastforce

lemma path_component_of_equiv:
   "path_component_of X x y \<longleftrightarrow> x \<in> topspace X \<and> y \<in> topspace X \<and> path_component_of X x = path_component_of X y"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (simp add: fun_eq_iff path_component_in_topspace)
    apply (meson path_component_of_sym path_component_of_trans)
    done
qed (simp add: path_component_of_refl)

lemma path_component_of_disjoint:
     "disjnt (Collect (path_component_of X x)) (Collect (path_component_of X y)) \<longleftrightarrow>
      ~(path_component_of X x y)"
  by (force simp: disjnt_def path_component_of_eq_empty path_component_of_equiv)

lemma path_component_of_eq:
   "path_component_of X x = path_component_of X y \<longleftrightarrow>
        (x \<notin> topspace X) \<and> (y \<notin> topspace X) \<or>
        x \<in> topspace X \<and> y \<in> topspace X \<and> path_component_of X x y"
  by (metis Collect_empty_eq_bot path_component_of_eq_empty path_component_of_equiv)

lemma path_component_of_aux:
  "path_component_of X x y
        \<Longrightarrow> path_component_of (subtopology X (Collect (path_component_of X x))) x y"
    by (meson path_component_of path_component_of_maximal path_connectedin_subtopology)

lemma path_connectedin_path_component_of:
  "path_connectedin X (Collect (path_component_of X x))"
proof -
  have "topspace (subtopology X (path_component_of_set X x)) = path_component_of_set X x"
    by (meson path_component_of_subset_topspace topspace_subtopology_subset)
  then have "path_connected_space (subtopology X (path_component_of_set X x))"
    by (metis (full_types) path_component_of_aux mem_Collect_eq path_component_of_equiv path_connected_space_iff_path_component)
  then show ?thesis
    by (simp add: path_component_of_subset_topspace path_connectedin_def)
qed

lemma path_connectedin_euclidean [simp]:
   "path_connectedin euclidean S \<longleftrightarrow> path_connected S"
  by (auto simp: path_connectedin_def path_connected_space_iff_path_component path_connected_component)

lemma path_connected_space_euclidean_subtopology [simp]:
   "path_connected_space(subtopology euclidean S) \<longleftrightarrow> path_connected S"
  using path_connectedin_topspace by force

lemma Union_path_components_of:
     "\<Union>(path_components_of X) = topspace X"
  by (auto simp: path_components_of_def path_component_of_equiv)

lemma path_components_of_maximal:
   "\<lbrakk>C \<in> path_components_of X; path_connectedin X S; ~disjnt C S\<rbrakk> \<Longrightarrow> S \<subseteq> C"
  apply (auto simp: path_components_of_def path_component_of_equiv)
  using path_component_of_maximal path_connectedin_def apply fastforce
  by (meson disjnt_subset2 path_component_of_disjoint path_component_of_equiv path_component_of_maximal)

lemma pairwise_disjoint_path_components_of:
     "pairwise disjnt (path_components_of X)"
  by (auto simp: path_components_of_def pairwise_def path_component_of_disjoint path_component_of_equiv)

lemma complement_path_components_of_Union:
   "C \<in> path_components_of X
        \<Longrightarrow> topspace X - C = \<Union>(path_components_of X - {C})"
  by (metis Diff_cancel Diff_subset Union_path_components_of cSup_singleton diff_Union_pairwise_disjoint insert_subset pairwise_disjoint_path_components_of)

lemma nonempty_path_components_of:
  assumes "C \<in> path_components_of X" shows "C \<noteq> {}"
proof -
  have "C \<in> path_component_of_set X ` topspace X"
    using assms path_components_of_def by blast
  then show ?thesis
    using path_component_of_refl by fastforce
qed

lemma path_components_of_subset: "C \<in> path_components_of X \<Longrightarrow> C \<subseteq> topspace X"
  by (auto simp: path_components_of_def path_component_of_equiv)

lemma path_connectedin_path_components_of:
   "C \<in> path_components_of X \<Longrightarrow> path_connectedin X C"
  by (auto simp: path_components_of_def path_connectedin_path_component_of)

lemma path_component_in_path_components_of:
  "Collect (path_component_of X a) \<in> path_components_of X \<longleftrightarrow> a \<in> topspace X"
  by (metis imageI nonempty_path_components_of path_component_of_eq_empty path_components_of_def)

lemma path_connectedin_Union:
  assumes \<A>: "\<And>S. S \<in> \<A> \<Longrightarrow> path_connectedin X S" "\<Inter>\<A> \<noteq> {}"
  shows "path_connectedin X (\<Union>\<A>)"
proof -
  obtain a where "\<And>S. S \<in> \<A> \<Longrightarrow> a \<in> S"
    using assms by blast
  then have "\<And>x. x \<in> topspace (subtopology X (\<Union>\<A>)) \<Longrightarrow> path_component_of (subtopology X (\<Union>\<A>)) a x"
    by simp (meson Union_upper \<A> path_component_of path_connectedin_subtopology)
  then show ?thesis
    using \<A> unfolding path_connectedin_def
    by (metis Sup_le_iff path_component_of_equiv path_connected_space_iff_path_component)
qed

lemma path_connectedin_Un:
   "\<lbrakk>path_connectedin X S; path_connectedin X T; S \<inter> T \<noteq> {}\<rbrakk>
    \<Longrightarrow> path_connectedin X (S \<union> T)"
  by (blast intro: path_connectedin_Union [of "{S,T}", simplified])

lemma path_connected_space_iff_components_eq:
  "path_connected_space X \<longleftrightarrow>
    (\<forall>C \<in> path_components_of X. \<forall>C' \<in> path_components_of X. C = C')"
  unfolding path_components_of_def
proof (intro iffI ballI)
  assume "\<forall>C \<in> path_component_of_set X ` topspace X.
             \<forall>C' \<in> path_component_of_set X ` topspace X. C = C'"
  then show "path_connected_space X"
    using path_component_of_refl path_connected_space_iff_path_component by fastforce
qed (auto simp: path_connected_space_path_component_set)

lemma path_components_of_eq_empty:
   "path_components_of X = {} \<longleftrightarrow> topspace X = {}"
  using Union_path_components_of nonempty_path_components_of by fastforce

lemma path_components_of_empty_space:
   "topspace X = {} \<Longrightarrow> path_components_of X = {}"
  by (simp add: path_components_of_eq_empty)

lemma path_components_of_subset_singleton:
  "path_components_of X \<subseteq> {S} \<longleftrightarrow>
        path_connected_space X \<and> (topspace X = {} \<or> topspace X = S)"
proof (cases "topspace X = {}")
  case True
  then show ?thesis
    by (auto simp: path_components_of_empty_space path_connected_space_topspace_empty)
next
  case False
  have "(path_components_of X = {S}) \<longleftrightarrow> (path_connected_space X \<and> topspace X = S)"
  proof (intro iffI conjI)
    assume L: "path_components_of X = {S}"
    then show "path_connected_space X"
      by (simp add: path_connected_space_iff_components_eq)
    show "topspace X = S"
      by (metis L ccpo_Sup_singleton [of S] Union_path_components_of)
  next
    assume R: "path_connected_space X \<and> topspace X = S"
    then show "path_components_of X = {S}"
      using ccpo_Sup_singleton [of S]
      by (metis False all_not_in_conv insert_iff mk_disjoint_insert path_component_in_path_components_of path_connected_space_iff_components_eq path_connected_space_path_component_set)
  qed
  with False show ?thesis
    by (simp add: path_components_of_eq_empty subset_singleton_iff)
qed

lemma path_connected_space_iff_components_subset_singleton:
   "path_connected_space X \<longleftrightarrow> (\<exists>a. path_components_of X \<subseteq> {a})"
  by (simp add: path_components_of_subset_singleton)

lemma path_components_of_eq_singleton:
   "path_components_of X = {S} \<longleftrightarrow> path_connected_space X \<and> topspace X \<noteq> {} \<and> S = topspace X"
  by (metis cSup_singleton insert_not_empty path_components_of_subset_singleton subset_singleton_iff)

lemma path_components_of_path_connected_space:
   "path_connected_space X \<Longrightarrow> path_components_of X = (if topspace X = {} then {} else {topspace X})"
  by (simp add: path_components_of_eq_empty path_components_of_eq_singleton)

lemma path_component_subset_connected_component_of:
   "path_component_of_set X x \<subseteq> connected_component_of_set X x"
proof (cases "x \<in> topspace X")
  case True
  then show ?thesis
    by (simp add: connected_component_of_maximal path_component_of_refl path_connectedin_imp_connectedin path_connectedin_path_component_of)
next
  case False
  then show ?thesis
    using path_component_of_eq_empty by fastforce
qed

lemma exists_path_component_of_superset:
  assumes S: "path_connectedin X S" and ne: "topspace X \<noteq> {}"
  obtains C where "C \<in> path_components_of X" "S \<subseteq> C"
proof (cases "S = {}")
  case True
  then show ?thesis
    using ne path_components_of_eq_empty that by fastforce
next
  case False
  then obtain a where "a \<in> S"
    by blast
  show ?thesis
  proof
    show "Collect (path_component_of X a) \<in> path_components_of X"
      by (meson \<open>a \<in> S\<close> S subsetD path_component_in_path_components_of path_connectedin_subset_topspace)
    show "S \<subseteq> Collect (path_component_of X a)"
      by (simp add: S \<open>a \<in> S\<close> path_component_of_maximal)
  qed
qed

lemma path_component_of_eq_overlap:
   "path_component_of X x = path_component_of X y \<longleftrightarrow>
      (x \<notin> topspace X) \<and> (y \<notin> topspace X) \<or>
      Collect (path_component_of X x) \<inter> Collect (path_component_of X y) \<noteq> {}"
  by (metis disjnt_def empty_iff inf_bot_right mem_Collect_eq path_component_of_disjoint path_component_of_eq path_component_of_eq_empty)

lemma path_component_of_nonoverlap:
   "Collect (path_component_of X x) \<inter> Collect (path_component_of X y) = {} \<longleftrightarrow>
    (x \<notin> topspace X) \<or> (y \<notin> topspace X) \<or>
    path_component_of X x \<noteq> path_component_of X y"
  by (metis inf.idem path_component_of_eq_empty path_component_of_eq_overlap)

lemma path_component_of_overlap:
   "Collect (path_component_of X x) \<inter> Collect (path_component_of X y) \<noteq> {} \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and> path_component_of X x = path_component_of X y"
  by (meson path_component_of_nonoverlap)

lemma path_components_of_disjoint:
     "\<lbrakk>C \<in> path_components_of X; C' \<in> path_components_of X\<rbrakk> \<Longrightarrow> disjnt C C' \<longleftrightarrow> C \<noteq> C'"
  by (auto simp: path_components_of_def path_component_of_disjoint path_component_of_equiv)

lemma path_components_of_overlap:
    "\<lbrakk>C \<in> path_components_of X; C' \<in> path_components_of X\<rbrakk> \<Longrightarrow> C \<inter> C' \<noteq> {} \<longleftrightarrow> C = C'"
  by (auto simp: path_components_of_def path_component_of_equiv)

lemma path_component_of_unique:
   "\<lbrakk>x \<in> C; path_connectedin X C; \<And>C'. \<lbrakk>x \<in> C'; path_connectedin X C'\<rbrakk> \<Longrightarrow> C' \<subseteq> C\<rbrakk>
        \<Longrightarrow> Collect (path_component_of X x) = C"
  by (meson subsetD eq_iff path_component_of_maximal path_connectedin_path_component_of)

lemma path_component_of_discrete_topology [simp]:
  "Collect (path_component_of (discrete_topology U) x) = (if x \<in> U then {x} else {})"
proof -
  have "\<And>C'. \<lbrakk>x \<in> C'; path_connectedin (discrete_topology U) C'\<rbrakk> \<Longrightarrow> C' \<subseteq> {x}"
    by (metis path_connectedin_discrete_topology subsetD singletonD)
  then have "x \<in> U \<Longrightarrow> Collect (path_component_of (discrete_topology U) x) = {x}"
    by (simp add: path_component_of_unique)
  then show ?thesis
    using path_component_in_topspace by fastforce
qed

lemma path_component_of_discrete_topology_iff [simp]:
  "path_component_of (discrete_topology U) x y \<longleftrightarrow> x \<in> U \<and> y=x"
  by (metis empty_iff insertI1 mem_Collect_eq path_component_of_discrete_topology singletonD)

lemma path_components_of_discrete_topology [simp]:
   "path_components_of (discrete_topology U) = (\<lambda>x. {x}) ` U"
  by (auto simp: path_components_of_def image_def fun_eq_iff)

lemma homeomorphic_map_path_component_of:
  assumes f: "homeomorphic_map X Y f" and x: "x \<in> topspace X"
  shows "Collect (path_component_of Y (f x)) = f ` Collect(path_component_of X x)"
proof -
  obtain g where g: "homeomorphic_maps X Y f g"
    using f homeomorphic_map_maps by blast
  show ?thesis
  proof
    have "Collect (path_component_of Y (f x)) \<subseteq> topspace Y"
      by (simp add: path_component_of_subset_topspace)
    moreover have "g ` Collect(path_component_of Y (f x)) \<subseteq> Collect (path_component_of X (g (f x)))"
      using g x unfolding homeomorphic_maps_def
      by (metis f homeomorphic_imp_surjective_map imageI mem_Collect_eq path_component_of_maximal path_component_of_refl path_connectedin_continuous_map_image path_connectedin_path_component_of)
    ultimately show "Collect (path_component_of Y (f x)) \<subseteq> f ` Collect (path_component_of X x)"
      using g x unfolding homeomorphic_maps_def continuous_map_def image_iff subset_iff
      by metis
    show "f ` Collect (path_component_of X x) \<subseteq> Collect (path_component_of Y (f x))"
    proof (rule path_component_of_maximal)
      show "path_connectedin Y (f ` Collect (path_component_of X x))"
        by (meson f homeomorphic_map_path_connectedness_eq path_connectedin_path_component_of)
    qed (simp add: path_component_of_refl x)
  qed
qed

lemma homeomorphic_map_path_components_of:
  assumes "homeomorphic_map X Y f"
  shows "path_components_of Y = (image f) ` (path_components_of X)"
    (is "?lhs = ?rhs")
  unfolding path_components_of_def homeomorphic_imp_surjective_map [OF assms, symmetric]
  using assms homeomorphic_map_path_component_of by fastforce


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

corollary connected_punctured_universe:
  "2 \<le> DIM('N::euclidean_space) \<Longrightarrow> connected(- {a::'N})"
  by (simp add: path_connected_punctured_universe path_connected_imp_connected)

proposition path_connected_sphere:
  fixes a :: "'a :: euclidean_space"
  assumes "2 \<le> DIM('a)"
  shows "path_connected(sphere a r)"
proof (cases r "0::real" rule: linorder_cases)
  case less
  then show ?thesis
    by (simp)
next
  case equal
  then show ?thesis
    by (simp)
next
  case greater
  then have eq: "(sphere (0::'a) r) = (\<lambda>x. (r / norm x) *\<^sub>R x) ` (- {0::'a})"
    by (force simp: image_iff split: if_split_asm)
  have "continuous_on (- {0::'a}) (\<lambda>x. (r / norm x) *\<^sub>R x)"
    by (intro continuous_intros) auto
  then have "path_connected ((\<lambda>x. (r / norm x) *\<^sub>R x) ` (- {0::'a}))"
    by (intro path_connected_continuous_image path_connected_punctured_universe assms)
  with eq have "path_connected (sphere (0::'a) r)"
    by auto
  then have "path_connected((+) a ` (sphere (0::'a) r))"
    by (simp add: path_connected_translation)
  then show ?thesis
    by (metis add.right_neutral sphere_translation)
qed

lemma connected_sphere:
    fixes a :: "'a :: euclidean_space"
    assumes "2 \<le> DIM('a)"
      shows "connected(sphere a r)"
  using path_connected_sphere [OF assms]
  by (simp add: path_connected_imp_connected)


corollary path_connected_complement_bounded_convex:
    fixes S :: "'a :: euclidean_space set"
    assumes "bounded S" "convex S" and 2: "2 \<le> DIM('a)"
    shows "path_connected (- S)"
proof (cases "S = {}")
  case True then show ?thesis
    using convex_imp_path_connected by auto
next
  case False
  then obtain a where "a \<in> S" by auto
  have \<section> [rule_format]: "\<forall>y\<in>S. \<forall>u. 0 \<le> u \<and> u \<le> 1 \<longrightarrow> (1 - u) *\<^sub>R a + u *\<^sub>R y \<in> S"
    using \<open>convex S\<close> \<open>a \<in> S\<close> by (simp add: convex_alt)
  { fix x y assume "x \<notin> S" "y \<notin> S"
    then have "x \<noteq> a" "y \<noteq> a" using \<open>a \<in> S\<close> by auto
    then have bxy: "bounded(insert x (insert y S))"
      by (simp add: \<open>bounded S\<close>)
    then obtain B::real where B: "0 < B" and Bx: "norm (a - x) < B" and By: "norm (a - y) < B"
                          and "S \<subseteq> ball a B"
      using bounded_subset_ballD [OF bxy, of a] by (auto simp: dist_norm)
    define C where "C = B / norm(x - a)"
    let ?Cxa = "a + C *\<^sub>R (x - a)"
    { fix u
      assume u: "(1 - u) *\<^sub>R x + u *\<^sub>R ?Cxa \<in> S" and "0 \<le> u" "u \<le> 1"
      have CC: "1 \<le> 1 + (C - 1) * u"
        using \<open>x \<noteq> a\<close> \<open>0 \<le> u\<close> Bx
        by (auto simp add: C_def norm_minus_commute)
      have *: "\<And>v. (1 - u) *\<^sub>R x + u *\<^sub>R (a + v *\<^sub>R (x - a)) = a + (1 + (v - 1) * u) *\<^sub>R (x - a)"
        by (simp add: algebra_simps)
      have "a + ((1 / (1 + C * u - u)) *\<^sub>R x + ((u / (1 + C * u - u)) *\<^sub>R a + (C * u / (1 + C * u - u)) *\<^sub>R x)) =
            (1 + (u / (1 + C * u - u))) *\<^sub>R a + ((1 / (1 + C * u - u)) + (C * u / (1 + C * u - u))) *\<^sub>R x"
        by (simp add: algebra_simps)
      also have "\<dots> = (1 + (u / (1 + C * u - u))) *\<^sub>R a + (1 + (u / (1 + C * u - u))) *\<^sub>R x"
        using CC by (simp add: field_simps)
      also have "\<dots> = x + (1 + (u / (1 + C * u - u))) *\<^sub>R a + (u / (1 + C * u - u)) *\<^sub>R x"
        by (simp add: algebra_simps)
      also have "\<dots> = x + ((1 / (1 + C * u - u)) *\<^sub>R a +
              ((u / (1 + C * u - u)) *\<^sub>R x + (C * u / (1 + C * u - u)) *\<^sub>R a))"
        using CC by (simp add: field_simps) (simp add: add_divide_distrib scaleR_add_left)
      finally have xeq: "(1 - 1 / (1 + (C - 1) * u)) *\<^sub>R a + (1 / (1 + (C - 1) * u)) *\<^sub>R (a + (1 + (C - 1) * u) *\<^sub>R (x - a)) = x"
        by (simp add: algebra_simps)
      have False
        using \<section> [of "a + (1 + (C - 1) * u) *\<^sub>R (x - a)" "1 / (1 + (C - 1) * u)"]
        using u \<open>x \<noteq> a\<close> \<open>x \<notin> S\<close> \<open>0 \<le> u\<close> CC
        by (auto simp: xeq *)
    }
    then have pcx: "path_component (- S) x ?Cxa"
      by (force simp: closed_segment_def intro!: path_component_linepath)
    define D where "D = B / norm(y - a)"  \<comment> \<open>massive duplication with the proof above\<close>
    let ?Dya = "a + D *\<^sub>R (y - a)"
    { fix u
      assume u: "(1 - u) *\<^sub>R y + u *\<^sub>R ?Dya \<in> S" and "0 \<le> u" "u \<le> 1"
      have DD: "1 \<le> 1 + (D - 1) * u"
        using \<open>y \<noteq> a\<close> \<open>0 \<le> u\<close> By
        by (auto simp add: D_def norm_minus_commute)
      have *: "\<And>v. (1 - u) *\<^sub>R y + u *\<^sub>R (a + v *\<^sub>R (y - a)) = a + (1 + (v - 1) * u) *\<^sub>R (y - a)"
        by (simp add: algebra_simps)
      have "a + ((1 / (1 + D * u - u)) *\<^sub>R y + ((u / (1 + D * u - u)) *\<^sub>R a + (D * u / (1 + D * u - u)) *\<^sub>R y)) =
            (1 + (u / (1 + D * u - u))) *\<^sub>R a + ((1 / (1 + D * u - u)) + (D * u / (1 + D * u - u))) *\<^sub>R y"
        by (simp add: algebra_simps)
      also have "\<dots> = (1 + (u / (1 + D * u - u))) *\<^sub>R a + (1 + (u / (1 + D * u - u))) *\<^sub>R y"
        using DD by (simp add: field_simps)
      also have "\<dots> = y + (1 + (u / (1 + D * u - u))) *\<^sub>R a + (u / (1 + D * u - u)) *\<^sub>R y"
        by (simp add: algebra_simps)
      also have "\<dots> = y + ((1 / (1 + D * u - u)) *\<^sub>R a +
              ((u / (1 + D * u - u)) *\<^sub>R y + (D * u / (1 + D * u - u)) *\<^sub>R a))"
        using DD by (simp add: field_simps) (simp add: add_divide_distrib scaleR_add_left)
      finally have xeq: "(1 - 1 / (1 + (D - 1) * u)) *\<^sub>R a + (1 / (1 + (D - 1) * u)) *\<^sub>R (a + (1 + (D - 1) * u) *\<^sub>R (y - a)) = y"
        by (simp add: algebra_simps)
      have False
        using \<section> [of "a + (1 + (D - 1) * u) *\<^sub>R (y - a)" "1 / (1 + (D - 1) * u)"]
        using u \<open>y \<noteq> a\<close> \<open>y \<notin> S\<close> \<open>0 \<le> u\<close> DD
        by (auto simp: xeq *)
    }
    then have pdy: "path_component (- S) y ?Dya"
      by (force simp: closed_segment_def intro!: path_component_linepath)
    have pyx: "path_component (- S) ?Dya ?Cxa"
    proof (rule path_component_of_subset)
      show "sphere a B \<subseteq> - S"
        using \<open>S \<subseteq> ball a B\<close> by (force simp: ball_def dist_norm norm_minus_commute)
      have aB: "?Dya \<in> sphere a B" "?Cxa \<in> sphere a B"
        using \<open>x \<noteq> a\<close> using \<open>y \<noteq> a\<close> B by (auto simp: dist_norm C_def D_def)
      then show "path_component (sphere a B) ?Dya ?Cxa"
        using path_connected_sphere [OF 2] path_connected_component by blast
    qed
    have "path_component (- S) x y"
      by (metis path_component_trans path_component_sym pcx pdy pyx)
  }
  then show ?thesis
    by (auto simp: path_connected_component)
qed

lemma connected_complement_bounded_convex:
    fixes S :: "'a :: euclidean_space set"
    assumes "bounded S" "convex S" "2 \<le> DIM('a)"
      shows  "connected (- S)"
  using path_connected_complement_bounded_convex [OF assms] path_connected_imp_connected by blast

lemma connected_diff_ball:
    fixes S :: "'a :: euclidean_space set"
    assumes "connected S" "cball a r \<subseteq> S" "2 \<le> DIM('a)"
      shows "connected (S - ball a r)"
proof (rule connected_diff_open_from_closed [OF ball_subset_cball])
  show "connected (cball a r - ball a r)"
    using assms connected_sphere by (auto simp: cball_diff_eq_sphere)
qed (auto simp: assms dist_norm)

proposition connected_open_delete:
  assumes "open S" "connected S" and 2: "2 \<le> DIM('N::euclidean_space)"
    shows "connected(S - {a::'N})"
proof (cases "a \<in> S")
  case True
  with \<open>open S\<close> obtain \<epsilon> where "\<epsilon> > 0" and \<epsilon>: "cball a \<epsilon> \<subseteq> S"
    using open_contains_cball_eq by blast
  define b where "b \<equiv> a + \<epsilon> *\<^sub>R (SOME i. i \<in> Basis)"
  have "dist a b = \<epsilon>"
    by (simp add: b_def dist_norm SOME_Basis \<open>0 < \<epsilon>\<close> less_imp_le)
  with \<epsilon> have "b \<in> \<Inter>{S - ball a r |r. 0 < r \<and> r < \<epsilon>}"
    by auto
  then have nonemp: "(\<Inter>{S - ball a r |r. 0 < r \<and> r < \<epsilon>}) = {} \<Longrightarrow> False"
    by auto
  have con: "\<And>r. r < \<epsilon> \<Longrightarrow> connected (S - ball a r)"
    using \<epsilon> by (force intro: connected_diff_ball [OF \<open>connected S\<close> _ 2])
  have "x \<in> \<Union>{S - ball a r |r. 0 < r \<and> r < \<epsilon>}" if "x \<in> S - {a}" for x
     using that \<open>0 < \<epsilon>\<close> 
     by (intro UnionI [of "S - ball a (min \<epsilon> (dist a x) / 2)"]) auto
  then have "S - {a} = \<Union>{S - ball a r | r. 0 < r \<and> r < \<epsilon>}"
    by auto
  then show ?thesis
    by (auto intro: connected_Union con dest!: nonemp)
next
  case False then show ?thesis
    by (simp add: \<open>connected S\<close>)
qed

corollary path_connected_open_delete:
  assumes "open S" "connected S" and 2: "2 \<le> DIM('N::euclidean_space)"
  shows "path_connected(S - {a::'N})"
  by (simp add: assms connected_open_delete connected_open_path_connected open_delete)

corollary path_connected_punctured_ball:
  "2 \<le> DIM('N::euclidean_space) \<Longrightarrow> path_connected(ball a r - {a::'N})"
  by (simp add: path_connected_open_delete)

corollary connected_punctured_ball:
  "2 \<le> DIM('N::euclidean_space) \<Longrightarrow> connected(ball a r - {a::'N})"
  by (simp add: connected_open_delete)

corollary connected_open_delete_finite:
  fixes S T::"'a::euclidean_space set"
  assumes S: "open S" "connected S" and 2: "2 \<le> DIM('a)" and "finite T"
  shows "connected(S - T)"
  using \<open>finite T\<close> S
proof (induct T)
  case empty
  show ?case using \<open>connected S\<close> by simp
next
  case (insert x F)
  then have "connected (S-F)" by auto
  moreover have "open (S - F)" using finite_imp_closed[OF \<open>finite F\<close>] \<open>open S\<close> by auto
  ultimately have "connected (S - F - {x})" using connected_open_delete[OF _ _ 2] by auto
  thus ?case by (metis Diff_insert)
qed

lemma sphere_1D_doubleton_zero:
  assumes 1: "DIM('a) = 1" and "r > 0"
  obtains x y::"'a::euclidean_space"
    where "sphere 0 r = {x,y} \<and> dist x y = 2*r"
proof -
  obtain b::'a where b: "Basis = {b}"
    using 1 card_1_singletonE by blast
  show ?thesis
  proof (intro that conjI)
    have "x = norm x *\<^sub>R b \<or> x = - norm x *\<^sub>R b" if "r = norm x" for x
    proof -
      have xb: "(x \<bullet> b) *\<^sub>R b = x"
        using euclidean_representation [of x, unfolded b] by force
      then have "norm ((x \<bullet> b) *\<^sub>R b) = norm x"
        by simp
      with b have "\<bar>x \<bullet> b\<bar> = norm x"
        using norm_Basis by (simp add: b)
      with xb show ?thesis
        by (metis (mono_tags, hide_lams) abs_eq_iff abs_norm_cancel)
    qed
    with \<open>r > 0\<close> b show "sphere 0 r = {r *\<^sub>R b, - r *\<^sub>R b}"
      by (force simp: sphere_def dist_norm)
    have "dist (r *\<^sub>R b) (- r *\<^sub>R b) = norm (r *\<^sub>R b + r *\<^sub>R b)"
      by (simp add: dist_norm)
    also have "\<dots> = norm ((2*r) *\<^sub>R b)"
      by (metis mult_2 scaleR_add_left)
    also have "\<dots> = 2*r"
      using \<open>r > 0\<close> b norm_Basis by fastforce
    finally show "dist (r *\<^sub>R b) (- r *\<^sub>R b) = 2*r" .
  qed
qed

lemma sphere_1D_doubleton:
  fixes a :: "'a :: euclidean_space"
  assumes "DIM('a) = 1" and "r > 0"
  obtains x y where "sphere a r = {x,y} \<and> dist x y = 2*r"
proof -
  have "sphere a r = (+) a ` sphere 0 r"
    by (metis add.right_neutral sphere_translation)
  then show ?thesis
    using sphere_1D_doubleton_zero [OF assms]
    by (metis (mono_tags, lifting) dist_add_cancel image_empty image_insert that)
qed

lemma psubset_sphere_Compl_connected:
  fixes S :: "'a::euclidean_space set"
  assumes S: "S \<subset> sphere a r" and "0 < r" and 2: "2 \<le> DIM('a)"
  shows "connected(- S)"
proof -
  have "S \<subseteq> sphere a r"
    using S by blast
  obtain b where "dist a b = r" and "b \<notin> S"
    using S mem_sphere by blast
  have CS: "- S = {x. dist a x \<le> r \<and> (x \<notin> S)} \<union> {x. r \<le> dist a x \<and> (x \<notin> S)}"
    by auto
  have "{x. dist a x \<le> r \<and> x \<notin> S} \<inter> {x. r \<le> dist a x \<and> x \<notin> S} \<noteq> {}"
    using \<open>b \<notin> S\<close> \<open>dist a b = r\<close> by blast
  moreover have "connected {x. dist a x \<le> r \<and> x \<notin> S}"
    using assms
    by (force intro: connected_intermediate_closure [of "ball a r"])
  moreover
  have "connected {x. r \<le> dist a x \<and> x \<notin> S}"
  proof (rule connected_intermediate_closure [of "- cball a r"])
    show "{x. r \<le> dist a x \<and> x \<notin> S} \<subseteq> closure (- cball a r)"
      using interior_closure by (force intro: connected_complement_bounded_convex)
  qed (use assms connected_complement_bounded_convex in auto)
  ultimately show ?thesis
    by (simp add: CS connected_Un)
qed


subsection\<open>Every annulus is a connected set\<close>

lemma path_connected_2DIM_I:
  fixes a :: "'N::euclidean_space"
  assumes 2: "2 \<le> DIM('N)" and pc: "path_connected {r. 0 \<le> r \<and> P r}"
  shows "path_connected {x. P(norm(x - a))}"
proof -
  have "{x. P(norm(x - a))} = (+) a ` {x. P(norm x)}"
    by force
  moreover have "path_connected {x::'N. P(norm x)}"
  proof -
    let ?D = "{x. 0 \<le> x \<and> P x} \<times> sphere (0::'N) 1"
    have "x \<in> (\<lambda>z. fst z *\<^sub>R snd z) ` ?D"
      if "P (norm x)" for x::'N
    proof (cases "x=0")
      case True
      with that show ?thesis
        apply (simp add: image_iff)
        by (metis (no_types) mem_sphere_0 order_refl vector_choose_size zero_le_one)
    next
      case False
      with that show ?thesis
        by (rule_tac x="(norm x, x /\<^sub>R norm x)" in image_eqI) auto
    qed
    then have *: "{x::'N. P(norm x)} =  (\<lambda>z. fst z *\<^sub>R snd z) ` ?D"
      by auto
    have "continuous_on ?D (\<lambda>z:: real\<times>'N. fst z *\<^sub>R snd z)"
      by (intro continuous_intros)
    moreover have "path_connected ?D"
      by (metis path_connected_Times [OF pc] path_connected_sphere 2)
    ultimately show ?thesis
      by (simp add: "*" path_connected_continuous_image)
  qed
  ultimately show ?thesis
    using path_connected_translation by metis
qed

proposition path_connected_annulus:
  fixes a :: "'N::euclidean_space"
  assumes "2 \<le> DIM('N)"
  shows "path_connected {x. r1 < norm(x - a) \<and> norm(x - a) < r2}"
        "path_connected {x. r1 < norm(x - a) \<and> norm(x - a) \<le> r2}"
        "path_connected {x. r1 \<le> norm(x - a) \<and> norm(x - a) < r2}"
        "path_connected {x. r1 \<le> norm(x - a) \<and> norm(x - a) \<le> r2}"
  by (auto simp: is_interval_def intro!: is_interval_convex convex_imp_path_connected path_connected_2DIM_I [OF assms])

proposition connected_annulus:
  fixes a :: "'N::euclidean_space"
  assumes "2 \<le> DIM('N::euclidean_space)"
  shows "connected {x. r1 < norm(x - a) \<and> norm(x - a) < r2}"
        "connected {x. r1 < norm(x - a) \<and> norm(x - a) \<le> r2}"
        "connected {x. r1 \<le> norm(x - a) \<and> norm(x - a) < r2}"
        "connected {x. r1 \<le> norm(x - a) \<and> norm(x - a) \<le> r2}"
  by (auto simp: path_connected_annulus [OF assms] path_connected_imp_connected)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Relations between components and path components\<close>

lemma open_connected_component:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open (connected_component_set S x)"
proof (clarsimp simp: open_contains_ball)
  fix y
  assume xy: "connected_component S x y"
  then obtain e where "e>0" "ball y e \<subseteq> S"
    using assms connected_component_in openE by blast
  then show "\<exists>e>0. ball y e  \<subseteq> connected_component_set S x"
    by (metis xy centre_in_ball connected_ball connected_component_eq_eq connected_component_in connected_component_maximal)
qed

corollary open_components:
    fixes S :: "'a::real_normed_vector set"
    shows "\<lbrakk>open u; S \<in> components u\<rbrakk> \<Longrightarrow> open S"
  by (simp add: components_iff) (metis open_connected_component)

lemma in_closure_connected_component:
  fixes S :: "'a::real_normed_vector set"
  assumes x: "x \<in> S" and S: "open S"
  shows "x \<in> closure (connected_component_set S y) \<longleftrightarrow>  x \<in> connected_component_set S y"
proof -
  { assume "x \<in> closure (connected_component_set S y)"
    moreover have "x \<in> connected_component_set S x"
      using x by simp
    ultimately have "x \<in> connected_component_set S y"
      using S by (meson Compl_disjoint closure_iff_nhds_not_empty connected_component_disjoint disjoint_eq_subset_Compl open_connected_component)
  }
  then show ?thesis
    by (auto simp: closure_def)
qed

lemma connected_disjoint_Union_open_pick:
  assumes "pairwise disjnt B"
          "\<And>S. S \<in> A \<Longrightarrow> connected S \<and> S \<noteq> {}"
          "\<And>S. S \<in> B \<Longrightarrow> open S"
          "\<Union>A \<subseteq> \<Union>B"
          "S \<in> A"
  obtains T where "T \<in> B" "S \<subseteq> T" "S \<inter> \<Union>(B - {T}) = {}"
proof -
  have "S \<subseteq> \<Union>B" "connected S" "S \<noteq> {}"
    using assms \<open>S \<in> A\<close> by blast+
  then obtain T where "T \<in> B" "S \<inter> T \<noteq> {}"
    by (metis Sup_inf_eq_bot_iff inf.absorb_iff2 inf_commute)
  have 1: "open T" by (simp add: \<open>T \<in> B\<close> assms)
  have 2: "open (\<Union>(B-{T}))" using assms by blast
  have 3: "S \<subseteq> T \<union> \<Union>(B - {T})" using \<open>S \<subseteq> \<Union>B\<close> by blast
  have "T \<inter> \<Union>(B - {T}) = {}" using \<open>T \<in> B\<close> \<open>pairwise disjnt B\<close>
    by (auto simp: pairwise_def disjnt_def)
  then have 4: "T \<inter> \<Union>(B - {T}) \<inter> S = {}" by auto
  from connectedD [OF \<open>connected S\<close> 1 2 4 3]
  have "S \<inter> \<Union>(B-{T}) = {}"
    by (auto simp: Int_commute \<open>S \<inter> T \<noteq> {}\<close>)
  with \<open>T \<in> B\<close> have "S \<subseteq> T"
    using "3" by auto
  show ?thesis
    using \<open>S \<inter> \<Union>(B - {T}) = {}\<close> \<open>S \<subseteq> T\<close> \<open>T \<in> B\<close> that by auto
qed

lemma connected_disjoint_Union_open_subset:
  assumes A: "pairwise disjnt A" and B: "pairwise disjnt B"
      and SA: "\<And>S. S \<in> A \<Longrightarrow> open S \<and> connected S \<and> S \<noteq> {}"
      and SB: "\<And>S. S \<in> B \<Longrightarrow> open S \<and> connected S \<and> S \<noteq> {}"
      and eq [simp]: "\<Union>A = \<Union>B"
    shows "A \<subseteq> B"
proof
  fix S
  assume "S \<in> A"
  obtain T where "T \<in> B" "S \<subseteq> T" "S \<inter> \<Union>(B - {T}) = {}"
    using SA SB \<open>S \<in> A\<close> connected_disjoint_Union_open_pick [OF B, of A] eq order_refl by blast
  moreover obtain S' where "S' \<in> A" "T \<subseteq> S'" "T \<inter> \<Union>(A - {S'}) = {}"
    using SA SB \<open>T \<in> B\<close> connected_disjoint_Union_open_pick [OF A, of B] eq order_refl by blast
  ultimately have "S' = S"
    by (metis A Int_subset_iff SA \<open>S \<in> A\<close> disjnt_def inf.orderE pairwise_def)
  with \<open>T \<subseteq> S'\<close> have "T \<subseteq> S" by simp
  with \<open>S \<subseteq> T\<close> have "S = T" by blast
  with \<open>T \<in> B\<close> show "S \<in> B" by simp
qed

lemma connected_disjoint_Union_open_unique:
  assumes A: "pairwise disjnt A" and B: "pairwise disjnt B"
      and SA: "\<And>S. S \<in> A \<Longrightarrow> open S \<and> connected S \<and> S \<noteq> {}"
      and SB: "\<And>S. S \<in> B \<Longrightarrow> open S \<and> connected S \<and> S \<noteq> {}"
      and eq [simp]: "\<Union>A = \<Union>B"
    shows "A = B"
by (rule subset_antisym; metis connected_disjoint_Union_open_subset assms)

proposition components_open_unique:
 fixes S :: "'a::real_normed_vector set"
  assumes "pairwise disjnt A" "\<Union>A = S"
          "\<And>X. X \<in> A \<Longrightarrow> open X \<and> connected X \<and> X \<noteq> {}"
    shows "components S = A"
proof -
  have "open S" using assms by blast
  show ?thesis
  proof (rule connected_disjoint_Union_open_unique)
    show "disjoint (components S)"
      by (simp add: components_eq disjnt_def pairwise_def)
  qed (use \<open>open S\<close> in \<open>simp_all add: assms open_components in_components_connected in_components_nonempty\<close>)
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Existence of unbounded components\<close>

lemma cobounded_unbounded_component:
    fixes S :: "'a :: euclidean_space set"
    assumes "bounded (-S)"
      shows "\<exists>x. x \<in> S \<and> \<not> bounded (connected_component_set S x)"
proof -
  obtain i::'a where i: "i \<in> Basis"
    using nonempty_Basis by blast
  obtain B where B: "B>0" "-S \<subseteq> ball 0 B"
    using bounded_subset_ballD [OF assms, of 0] by auto
  then have *: "\<And>x. B \<le> norm x \<Longrightarrow> x \<in> S"
    by (force simp: ball_def dist_norm)
  have unbounded_inner: "\<not> bounded {x. inner i x \<ge> B}"
  proof (clarsimp simp: bounded_def dist_norm)
    fix e x
    show "\<exists>y. B \<le> i \<bullet> y \<and> \<not> norm (x - y) \<le> e"
      using i
      by (rule_tac x="x + (max B e + 1 + \<bar>i \<bullet> x\<bar>) *\<^sub>R i" in exI) (auto simp: inner_right_distrib)
  qed
  have \<section>: "\<And>x. B \<le> i \<bullet> x \<Longrightarrow> x \<in> S"
    using * Basis_le_norm [OF i] by (metis abs_ge_self inner_commute order_trans)
  have "{x. B \<le> i \<bullet> x} \<subseteq> connected_component_set S (B *\<^sub>R i)"
    by (intro connected_component_maximal) (auto simp: i intro: convex_connected convex_halfspace_ge [of B] \<section>)
  then have "\<not> bounded (connected_component_set S (B *\<^sub>R i))"
    using bounded_subset unbounded_inner by blast
  moreover have "B *\<^sub>R i \<in> S"
    by (rule *) (simp add: norm_Basis [OF i])
  ultimately show ?thesis
    by blast
qed

lemma cobounded_unique_unbounded_component:
    fixes S :: "'a :: euclidean_space set"
    assumes bs: "bounded (-S)" and "2 \<le> DIM('a)"
        and bo: "\<not> bounded(connected_component_set S x)"
                "\<not> bounded(connected_component_set S y)"
      shows "connected_component_set S x = connected_component_set S y"
proof -
  obtain i::'a where i: "i \<in> Basis"
    using nonempty_Basis by blast
  obtain B where B: "B>0" "-S \<subseteq> ball 0 B"
    using bounded_subset_ballD [OF bs, of 0] by auto
  then have *: "\<And>x. B \<le> norm x \<Longrightarrow> x \<in> S"
    by (force simp: ball_def dist_norm)
  obtain x' where x': "connected_component S x x'" "norm x' > B"
    using bo [unfolded bounded_def dist_norm, simplified, rule_format]
    by (metis diff_zero norm_minus_commute not_less)
  obtain y' where y': "connected_component S y y'" "norm y' > B"
    using bo [unfolded bounded_def dist_norm, simplified, rule_format]
    by (metis diff_zero norm_minus_commute not_less)
  have x'y': "connected_component S x' y'"
    unfolding connected_component_def
  proof (intro exI conjI)
    show "connected (- ball 0 B :: 'a set)"
      using assms by (auto intro: connected_complement_bounded_convex)
  qed (use x' y' dist_norm * in auto)
  show ?thesis
  proof (rule connected_component_eq)
    show "x \<in> connected_component_set S y"
      using x' y' x'y'
      by (metis (no_types) connected_component_eq_eq connected_component_in mem_Collect_eq)
  qed
qed

lemma cobounded_unbounded_components:
    fixes S :: "'a :: euclidean_space set"
    shows "bounded (-S) \<Longrightarrow> \<exists>c. c \<in> components S \<and> \<not>bounded c"
  by (metis cobounded_unbounded_component components_def imageI)

lemma cobounded_unique_unbounded_components:
    fixes S :: "'a :: euclidean_space set"
    shows  "\<lbrakk>bounded (- S); c \<in> components S; \<not> bounded c; c' \<in> components S; \<not> bounded c'; 2 \<le> DIM('a)\<rbrakk> \<Longrightarrow> c' = c"
  unfolding components_iff
  by (metis cobounded_unique_unbounded_component)

lemma cobounded_has_bounded_component:
  fixes S :: "'a :: euclidean_space set"
  assumes "bounded (- S)" "\<not> connected S" "2 \<le> DIM('a)"
  obtains C where "C \<in> components S" "bounded C"
  by (meson cobounded_unique_unbounded_components connected_eq_connected_components_eq assms)


subsection\<open>The \<open>inside\<close> and \<open>outside\<close> of a Set\<close>

text\<^marker>\<open>tag important\<close>\<open>The inside comprises the points in a bounded connected component of the set's complement.
  The outside comprises the points in unbounded connected component of the complement.\<close>

definition\<^marker>\<open>tag important\<close> inside where
  "inside S \<equiv> {x. (x \<notin> S) \<and> bounded(connected_component_set ( - S) x)}"

definition\<^marker>\<open>tag important\<close> outside where
  "outside S \<equiv> -S \<inter> {x. \<not> bounded(connected_component_set (- S) x)}"

lemma outside: "outside S = {x. \<not> bounded(connected_component_set (- S) x)}"
  by (auto simp: outside_def) (metis Compl_iff bounded_empty connected_component_eq_empty)

lemma inside_no_overlap [simp]: "inside S \<inter> S = {}"
  by (auto simp: inside_def)

lemma outside_no_overlap [simp]:
   "outside S \<inter> S = {}"
  by (auto simp: outside_def)

lemma inside_Int_outside [simp]: "inside S \<inter> outside S = {}"
  by (auto simp: inside_def outside_def)

lemma inside_Un_outside [simp]: "inside S \<union> outside S = (- S)"
  by (auto simp: inside_def outside_def)

lemma inside_eq_outside:
   "inside S = outside S \<longleftrightarrow> S = UNIV"
  by (auto simp: inside_def outside_def)

lemma inside_outside: "inside S = (- (S \<union> outside S))"
  by (force simp: inside_def outside)

lemma outside_inside: "outside S = (- (S \<union> inside S))"
  by (auto simp: inside_outside) (metis IntI equals0D outside_no_overlap)

lemma union_with_inside: "S \<union> inside S = - outside S"
  by (auto simp: inside_outside) (simp add: outside_inside)

lemma union_with_outside: "S \<union> outside S = - inside S"
  by (simp add: inside_outside)

lemma outside_mono: "S \<subseteq> T \<Longrightarrow> outside T \<subseteq> outside S"
  by (auto simp: outside bounded_subset connected_component_mono)

lemma inside_mono: "S \<subseteq> T \<Longrightarrow> inside S - T \<subseteq> inside T"
  by (auto simp: inside_def bounded_subset connected_component_mono)

lemma segment_bound_lemma:
  fixes u::real
  assumes "x \<ge> B" "y \<ge> B" "0 \<le> u" "u \<le> 1"
  shows "(1 - u) * x + u * y \<ge> B"
proof -
  obtain dx dy where "dx \<ge> 0" "dy \<ge> 0" "x = B + dx" "y = B + dy"
    using assms by auto (metis add.commute diff_add_cancel)
  with \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> show ?thesis
    by (simp add: add_increasing2 mult_left_le field_simps)
qed

lemma cobounded_outside:
  fixes S :: "'a :: real_normed_vector set"
  assumes "bounded S" shows "bounded (- outside S)"
proof -
  obtain B where B: "B>0" "S \<subseteq> ball 0 B"
    using bounded_subset_ballD [OF assms, of 0] by auto
  { fix x::'a and C::real
    assume Bno: "B \<le> norm x" and C: "0 < C"
    have "\<exists>y. connected_component (- S) x y \<and> norm y > C"
    proof (cases "x = 0")
      case True with B Bno show ?thesis by force
    next
      case False 
      have "closed_segment x (((B + C) / norm x) *\<^sub>R x) \<subseteq> - ball 0 B"
      proof
        fix w
        assume "w \<in> closed_segment x (((B + C) / norm x) *\<^sub>R x)"
        then obtain u where
          w: "w = (1 - u + u * (B + C) / norm x) *\<^sub>R x" "0 \<le> u" "u \<le> 1"
          by (auto simp add: closed_segment_def real_vector_class.scaleR_add_left [symmetric])
        with False B C have "B \<le> (1 - u) * norm x + u * (B + C)"
          using segment_bound_lemma [of B "norm x" "B + C" u] Bno
          by simp
        with False B C show "w \<in> - ball 0 B"
          using distrib_right [of _ _ "norm x"]
          by (simp add: ball_def w not_less)
      qed
      also have "... \<subseteq> -S"
        by (simp add: B)
      finally have "\<exists>T. connected T \<and> T \<subseteq> - S \<and> x \<in> T \<and> ((B + C) / norm x) *\<^sub>R x \<in> T"
        by (rule_tac x="closed_segment x (((B+C)/norm x) *\<^sub>R x)" in exI) simp
      with False B
      show ?thesis
        by (rule_tac x="((B+C)/norm x) *\<^sub>R x" in exI) (simp add: connected_component_def)
    qed
  }
  then show ?thesis
    apply (simp add: outside_def assms)
    apply (rule bounded_subset [OF bounded_ball [of 0 B]])
    apply (force simp: dist_norm not_less bounded_pos)
    done
qed

lemma unbounded_outside:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "bounded S \<Longrightarrow> \<not> bounded(outside S)"
  using cobounded_imp_unbounded cobounded_outside by blast

lemma bounded_inside:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "bounded S \<Longrightarrow> bounded(inside S)"
  by (simp add: bounded_Int cobounded_outside inside_outside)

lemma connected_outside:
    fixes S :: "'a::euclidean_space set"
    assumes "bounded S" "2 \<le> DIM('a)"
      shows "connected(outside S)"
  apply (clarsimp simp add: connected_iff_connected_component outside)
  apply (rule_tac S="connected_component_set (- S) x" in connected_component_of_subset)
  apply (metis (no_types) assms cobounded_unbounded_component cobounded_unique_unbounded_component connected_component_eq_eq connected_component_idemp double_complement mem_Collect_eq)
  by (simp add: Collect_mono connected_component_eq)

lemma outside_connected_component_lt:
  "outside S = {x. \<forall>B. \<exists>y. B < norm(y) \<and> connected_component (- S) x y}"
  apply (auto simp: outside bounded_def dist_norm)
   apply (metis diff_0 norm_minus_cancel not_less)
  by (metis less_diff_eq norm_minus_commute norm_triangle_ineq2 order.trans pinf(6))

lemma outside_connected_component_le:
  "outside S = {x. \<forall>B. \<exists>y. B \<le> norm(y) \<and> connected_component (- S) x y}"
  apply (simp add: outside_connected_component_lt Set.set_eq_iff)
  by (meson gt_ex leD le_less_linear less_imp_le order.trans)

lemma not_outside_connected_component_lt:
    fixes S :: "'a::euclidean_space set"
    assumes S: "bounded S" and "2 \<le> DIM('a)"
      shows "- (outside S) = {x. \<forall>B. \<exists>y. B < norm(y) \<and> \<not> connected_component (- S) x y}"
proof -
  obtain B::real where B: "0 < B" and Bno: "\<And>x. x \<in> S \<Longrightarrow> norm x \<le> B"
    using S [simplified bounded_pos] by auto
  { fix y::'a and z::'a
    assume yz: "B < norm z" "B < norm y"
    have "connected_component (- cball 0 B) y z"
      using assms yz
      by (force simp: dist_norm intro: connected_componentI [OF _ subset_refl] connected_complement_bounded_convex)
    then have "connected_component (- S) y z"
      by (metis connected_component_of_subset Bno Compl_anti_mono mem_cball_0 subset_iff)
  } note cyz = this
  show ?thesis
    apply (auto simp: outside bounded_pos)
    apply (metis Compl_iff bounded_iff cobounded_imp_unbounded mem_Collect_eq not_le)
    by (metis B connected_component_trans cyz not_le)
qed

lemma not_outside_connected_component_le:
  fixes S :: "'a::euclidean_space set"
  assumes S: "bounded S"  "2 \<le> DIM('a)"
  shows "- (outside S) = {x. \<forall>B. \<exists>y. B \<le> norm(y) \<and> \<not> connected_component (- S) x y}"
  apply (auto intro: less_imp_le simp: not_outside_connected_component_lt [OF assms])
  by (meson gt_ex less_le_trans)

lemma inside_connected_component_lt:
    fixes S :: "'a::euclidean_space set"
    assumes S: "bounded S"  "2 \<le> DIM('a)"
      shows "inside S = {x. (x \<notin> S) \<and> (\<forall>B. \<exists>y. B < norm(y) \<and> \<not> connected_component (- S) x y)}"
  by (auto simp: inside_outside not_outside_connected_component_lt [OF assms])

lemma inside_connected_component_le:
    fixes S :: "'a::euclidean_space set"
    assumes S: "bounded S"  "2 \<le> DIM('a)"
      shows "inside S = {x. (x \<notin> S) \<and> (\<forall>B. \<exists>y. B \<le> norm(y) \<and> \<not> connected_component (- S) x y)}"
  by (auto simp: inside_outside not_outside_connected_component_le [OF assms])

lemma inside_subset:
  assumes "connected U" and "\<not> bounded U" and "T \<union> U = - S"
  shows "inside S \<subseteq> T"
  apply (auto simp: inside_def)
  by (metis bounded_subset [of "connected_component_set (- S) _"] connected_component_maximal
      Compl_iff Un_iff assms subsetI)

lemma frontier_not_empty:
  fixes S :: "'a :: real_normed_vector set"
  shows "\<lbrakk>S \<noteq> {}; S \<noteq> UNIV\<rbrakk> \<Longrightarrow> frontier S \<noteq> {}"
    using connected_Int_frontier [of UNIV S] by auto

lemma frontier_eq_empty:
  fixes S :: "'a :: real_normed_vector set"
  shows "frontier S = {} \<longleftrightarrow> S = {} \<or> S = UNIV"
using frontier_UNIV frontier_empty frontier_not_empty by blast

lemma frontier_of_connected_component_subset:
  fixes S :: "'a::real_normed_vector set"
  shows "frontier(connected_component_set S x) \<subseteq> frontier S"
proof -
  { fix y
    assume y1: "y \<in> closure (connected_component_set S x)"
       and y2: "y \<notin> interior (connected_component_set S x)"
    have "y \<in> closure S"
      using y1 closure_mono connected_component_subset by blast
    moreover have "z \<in> interior (connected_component_set S x)"
          if "0 < e" "ball y e \<subseteq> interior S" "dist y z < e" for e z
    proof -
      have "ball y e \<subseteq> connected_component_set S y"
        using connected_component_maximal that interior_subset 
        by (metis centre_in_ball connected_ball subset_trans)
      then show ?thesis
        using y1 apply (simp add: closure_approachable open_contains_ball_eq [OF open_interior])
        by (metis connected_component_eq dist_commute mem_Collect_eq mem_ball mem_interior subsetD \<open>0 < e\<close> y2)
    qed
    then have "y \<notin> interior S"
      using y2 by (force simp: open_contains_ball_eq [OF open_interior])
    ultimately have "y \<in> frontier S"
      by (auto simp: frontier_def)
  }
  then show ?thesis by (auto simp: frontier_def)
qed

lemma frontier_Union_subset_closure:
  fixes F :: "'a::real_normed_vector set set"
  shows "frontier(\<Union>F) \<subseteq> closure(\<Union>t \<in> F. frontier t)"
proof -
  have "\<exists>y\<in>F. \<exists>y\<in>frontier y. dist y x < e"
       if "T \<in> F" "y \<in> T" "dist y x < e"
          "x \<notin> interior (\<Union>F)" "0 < e" for x y e T
  proof (cases "x \<in> T")
    case True with that show ?thesis
      by (metis Diff_iff Sup_upper closure_subset contra_subsetD dist_self frontier_def interior_mono)
  next
    case False
    have 1: "closed_segment x y \<inter> T \<noteq> {}" 
      using \<open>y \<in> T\<close> by blast
    have 2: "closed_segment x y - T \<noteq> {}"
      using False by blast
    obtain c where "c \<in> closed_segment x y" "c \<in> frontier T"
       using False connected_Int_frontier [OF connected_segment 1 2] by auto
    then show ?thesis
    proof -
      have "norm (y - x) < e"
        by (metis dist_norm \<open>dist y x < e\<close>)
      moreover have "norm (c - x) \<le> norm (y - x)"
        by (simp add: \<open>c \<in> closed_segment x y\<close> segment_bound(1))
      ultimately have "norm (c - x) < e"
        by linarith
      then show ?thesis
        by (metis (no_types) \<open>c \<in> frontier T\<close> dist_norm that(1))
    qed
  qed
  then show ?thesis
    by (fastforce simp add: frontier_def closure_approachable)
qed

lemma frontier_Union_subset:
  fixes F :: "'a::real_normed_vector set set"
  shows "finite F \<Longrightarrow> frontier(\<Union>F) \<subseteq> (\<Union>t \<in> F. frontier t)"
by (rule order_trans [OF frontier_Union_subset_closure])
   (auto simp: closure_subset_eq)

lemma frontier_of_components_subset:
  fixes S :: "'a::real_normed_vector set"
  shows "C \<in> components S \<Longrightarrow> frontier C \<subseteq> frontier S"
  by (metis Path_Connected.frontier_of_connected_component_subset components_iff)

lemma frontier_of_components_closed_complement:
  fixes S :: "'a::real_normed_vector set"
  shows "\<lbrakk>closed S; C \<in> components (- S)\<rbrakk> \<Longrightarrow> frontier C \<subseteq> S"
  using frontier_complement frontier_of_components_subset frontier_subset_eq by blast

lemma frontier_minimal_separating_closed:
  fixes S :: "'a::real_normed_vector set"
  assumes "closed S"
      and nconn: "\<not> connected(- S)"
      and C: "C \<in> components (- S)"
      and conn: "\<And>T. \<lbrakk>closed T; T \<subset> S\<rbrakk> \<Longrightarrow> connected(- T)"
    shows "frontier C = S"
proof (rule ccontr)
  assume "frontier C \<noteq> S"
  then have "frontier C \<subset> S"
    using frontier_of_components_closed_complement [OF \<open>closed S\<close> C] by blast
  then have "connected(- (frontier C))"
    by (simp add: conn)
  have "\<not> connected(- (frontier C))"
    unfolding connected_def not_not
  proof (intro exI conjI)
    show "open C"
      using C \<open>closed S\<close> open_components by blast
    show "open (- closure C)"
      by blast
    show "C \<inter> - closure C \<inter> - frontier C = {}"
      using closure_subset by blast
    show "C \<inter> - frontier C \<noteq> {}"
      using C \<open>open C\<close> components_eq frontier_disjoint_eq by fastforce
    show "- frontier C \<subseteq> C \<union> - closure C"
      by (simp add: \<open>open C\<close> closed_Compl frontier_closures)
    then show "- closure C \<inter> - frontier C \<noteq> {}"
      by (metis (no_types, lifting) C Compl_subset_Compl_iff \<open>frontier C \<subset> S\<close> compl_sup frontier_closures in_components_subset psubsetE sup.absorb_iff2 sup.boundedE sup_bot.right_neutral sup_inf_absorb)
  qed
  then show False
    using \<open>connected (- frontier C)\<close> by blast
qed

lemma connected_component_UNIV [simp]:
    fixes x :: "'a::real_normed_vector"
    shows "connected_component_set UNIV x = UNIV"
using connected_iff_eq_connected_component_set [of "UNIV::'a set"] connected_UNIV
by auto

lemma connected_component_eq_UNIV:
    fixes x :: "'a::real_normed_vector"
    shows "connected_component_set s x = UNIV \<longleftrightarrow> s = UNIV"
  using connected_component_in connected_component_UNIV by blast

lemma components_UNIV [simp]: "components UNIV = {UNIV :: 'a::real_normed_vector set}"
  by (auto simp: components_eq_sing_iff)

lemma interior_inside_frontier:
    fixes S :: "'a::real_normed_vector set"
    assumes "bounded S"
      shows "interior S \<subseteq> inside (frontier S)"
proof -
  { fix x y
    assume x: "x \<in> interior S" and y: "y \<notin> S"
       and cc: "connected_component (- frontier S) x y"
    have "connected_component_set (- frontier S) x \<inter> frontier S \<noteq> {}"
    proof (rule connected_Int_frontier; simp add: set_eq_iff)
      show "\<exists>u. connected_component (- frontier S) x u \<and> u \<in> S"
        by (meson cc connected_component_in connected_component_refl_eq interior_subset subsetD x)
      show "\<exists>u. connected_component (- frontier S) x u \<and> u \<notin> S"
        using y cc by blast
    qed
    then have "bounded (connected_component_set (- frontier S) x)"
      using connected_component_in by auto
  }
  then show ?thesis
    apply (auto simp: inside_def frontier_def)
    apply (rule classical)
    apply (rule bounded_subset [OF assms], blast)
    done
qed

lemma inside_empty [simp]: "inside {} = ({} :: 'a :: {real_normed_vector, perfect_space} set)"
  by (simp add: inside_def)

lemma outside_empty [simp]: "outside {} = (UNIV :: 'a :: {real_normed_vector, perfect_space} set)"
  using inside_empty inside_Un_outside by blast

lemma inside_same_component:
   "\<lbrakk>connected_component (- S) x y; x \<in> inside S\<rbrakk> \<Longrightarrow> y \<in> inside S"
  using connected_component_eq connected_component_in
  by (fastforce simp add: inside_def)

lemma outside_same_component:
   "\<lbrakk>connected_component (- S) x y; x \<in> outside S\<rbrakk> \<Longrightarrow> y \<in> outside S"
  using connected_component_eq connected_component_in
  by (fastforce simp add: outside_def)

lemma convex_in_outside:
  fixes S :: "'a :: {real_normed_vector, perfect_space} set"
  assumes S: "convex S" and z: "z \<notin> S"
    shows "z \<in> outside S"
proof (cases "S={}")
  case True then show ?thesis by simp
next
  case False then obtain a where "a \<in> S" by blast
  with z have zna: "z \<noteq> a" by auto
  { assume "bounded (connected_component_set (- S) z)"
    with bounded_pos_less obtain B where "B>0" and B: "\<And>x. connected_component (- S) z x \<Longrightarrow> norm x < B"
      by (metis mem_Collect_eq)
    define C where "C = (B + 1 + norm z) / norm (z-a)"
    have "C > 0"
      using \<open>0 < B\<close> zna by (simp add: C_def field_split_simps add_strict_increasing)
    have "\<bar>norm (z + C *\<^sub>R (z-a)) - norm (C *\<^sub>R (z-a))\<bar> \<le> norm z"
      by (metis add_diff_cancel norm_triangle_ineq3)
    moreover have "norm (C *\<^sub>R (z-a)) > norm z + B"
      using zna \<open>B>0\<close> by (simp add: C_def le_max_iff_disj)
    ultimately have C: "norm (z + C *\<^sub>R (z-a)) > B" by linarith
    { fix u::real
      assume u: "0\<le>u" "u\<le>1" and ins: "(1 - u) *\<^sub>R z + u *\<^sub>R (z + C *\<^sub>R (z - a)) \<in> S"
      then have Cpos: "1 + u * C > 0"
        by (meson \<open>0 < C\<close> add_pos_nonneg less_eq_real_def zero_le_mult_iff zero_less_one)
      then have *: "(1 / (1 + u * C)) *\<^sub>R z + (u * C / (1 + u * C)) *\<^sub>R z = z"
        by (simp add: scaleR_add_left [symmetric] field_split_simps)
      then have False
        using convexD_alt [OF S \<open>a \<in> S\<close> ins, of "1/(u*C + 1)"] \<open>C>0\<close> \<open>z \<notin> S\<close> Cpos u
        by (simp add: * field_split_simps)
    } note contra = this
    have "connected_component (- S) z (z + C *\<^sub>R (z-a))"
    proof (rule connected_componentI [OF connected_segment])
      show "closed_segment z (z + C *\<^sub>R (z - a)) \<subseteq> - S"
        using contra by (force simp add: closed_segment_def)
    qed auto
    then have False
      using zna B [of "z + C *\<^sub>R (z-a)"] C
      by (auto simp: field_split_simps max_mult_distrib_right)
  }
  then show ?thesis
    by (auto simp: outside_def z)
qed

lemma outside_convex:
  fixes S :: "'a :: {real_normed_vector, perfect_space} set"
  assumes "convex S"
    shows "outside S = - S"
  by (metis ComplD assms convex_in_outside equalityI inside_Un_outside subsetI sup.cobounded2)

lemma outside_singleton [simp]:
  fixes x :: "'a :: {real_normed_vector, perfect_space}"
  shows "outside {x} = -{x}"
  by (auto simp: outside_convex)

lemma inside_convex:
  fixes S :: "'a :: {real_normed_vector, perfect_space} set"
  shows "convex S \<Longrightarrow> inside S = {}"
  by (simp add: inside_outside outside_convex)

lemma inside_singleton [simp]:
  fixes x :: "'a :: {real_normed_vector, perfect_space}"
  shows "inside {x} = {}"
  by (auto simp: inside_convex)

lemma outside_subset_convex:
  fixes S :: "'a :: {real_normed_vector, perfect_space} set"
  shows "\<lbrakk>convex T; S \<subseteq> T\<rbrakk> \<Longrightarrow> - T \<subseteq> outside S"
  using outside_convex outside_mono by blast

lemma outside_Un_outside_Un:
  fixes S :: "'a::real_normed_vector set"
  assumes "S \<inter> outside(T \<union> U) = {}"
  shows "outside(T \<union> U) \<subseteq> outside(T \<union> S)"
proof
  fix x
  assume x: "x \<in> outside (T \<union> U)"
  have "Y \<subseteq> - S" if "connected Y" "Y \<subseteq> - T" "Y \<subseteq> - U" "x \<in> Y" "u \<in> Y" for u Y
  proof -
    have "Y \<subseteq> connected_component_set (- (T \<union> U)) x"
      by (simp add: connected_component_maximal that)
    also have "\<dots> \<subseteq> outside(T \<union> U)"
      by (metis (mono_tags, lifting) Collect_mono mem_Collect_eq outside outside_same_component x)
    finally have "Y \<subseteq> outside(T \<union> U)" .
    with assms show ?thesis by auto
  qed
  with x show "x \<in> outside (T \<union> S)"
    by (simp add: outside_connected_component_lt connected_component_def) meson
qed

lemma outside_frontier_misses_closure:
    fixes S :: "'a::real_normed_vector set"
    assumes "bounded S"
    shows  "outside(frontier S) \<subseteq> - closure S"
  unfolding outside_inside Lattices.boolean_algebra_class.compl_le_compl_iff
proof -
  { assume "interior S \<subseteq> inside (frontier S)"
    hence "interior S \<union> inside (frontier S) = inside (frontier S)"
      by (simp add: subset_Un_eq)
    then have "closure S \<subseteq> frontier S \<union> inside (frontier S)"
      using frontier_def by auto
  }
  then show "closure S \<subseteq> frontier S \<union> inside (frontier S)"
    using interior_inside_frontier [OF assms] by blast
qed

lemma outside_frontier_eq_complement_closure:
  fixes S :: "'a :: {real_normed_vector, perfect_space} set"
    assumes "bounded S" "convex S"
      shows "outside(frontier S) = - closure S"
by (metis Diff_subset assms convex_closure frontier_def outside_frontier_misses_closure
          outside_subset_convex subset_antisym)

lemma inside_frontier_eq_interior:
     fixes S :: "'a :: {real_normed_vector, perfect_space} set"
     shows "\<lbrakk>bounded S; convex S\<rbrakk> \<Longrightarrow> inside(frontier S) = interior S"
  apply (simp add: inside_outside outside_frontier_eq_complement_closure)
  using closure_subset interior_subset
  apply (auto simp: frontier_def)
  done

lemma open_inside:
    fixes S :: "'a::real_normed_vector set"
    assumes "closed S"
      shows "open (inside S)"
proof -
  { fix x assume x: "x \<in> inside S"
    have "open (connected_component_set (- S) x)"
      using assms open_connected_component by blast
    then obtain e where e: "e>0" and e: "\<And>y. dist y x < e \<longrightarrow> connected_component (- S) x y"
      using dist_not_less_zero
      apply (simp add: open_dist)
      by (metis (no_types, lifting) Compl_iff connected_component_refl_eq inside_def mem_Collect_eq x)
    then have "\<exists>e>0. ball x e \<subseteq> inside S"
      by (metis e dist_commute inside_same_component mem_ball subsetI x)
  }
  then show ?thesis
    by (simp add: open_contains_ball)
qed

lemma open_outside:
    fixes S :: "'a::real_normed_vector set"
    assumes "closed S"
      shows "open (outside S)"
proof -
  { fix x assume x: "x \<in> outside S"
    have "open (connected_component_set (- S) x)"
      using assms open_connected_component by blast
    then obtain e where e: "e>0" and e: "\<And>y. dist y x < e \<longrightarrow> connected_component (- S) x y"
      using dist_not_less_zero x
      by (auto simp add: open_dist outside_def intro: connected_component_refl)
    then have "\<exists>e>0. ball x e \<subseteq> outside S"
      by (metis e dist_commute outside_same_component mem_ball subsetI x)
  }
  then show ?thesis
    by (simp add: open_contains_ball)
qed

lemma closure_inside_subset:
    fixes S :: "'a::real_normed_vector set"
    assumes "closed S"
      shows "closure(inside S) \<subseteq> S \<union> inside S"
by (metis assms closure_minimal open_closed open_outside sup.cobounded2 union_with_inside)

lemma frontier_inside_subset:
    fixes S :: "'a::real_normed_vector set"
    assumes "closed S"
      shows "frontier(inside S) \<subseteq> S"
proof -
  have "closure (inside S) \<inter> - inside S = closure (inside S) - interior (inside S)"
    by (metis (no_types) Diff_Compl assms closure_closed interior_closure open_closed open_inside)
  moreover have "- inside S \<inter> - outside S = S"
    by (metis (no_types) compl_sup double_compl inside_Un_outside)
  moreover have "closure (inside S) \<subseteq> - outside S"
    by (metis (no_types) assms closure_inside_subset union_with_inside)
  ultimately have "closure (inside S) - interior (inside S) \<subseteq> S"
    by blast
  then show ?thesis
    by (simp add: frontier_def open_inside interior_open)
qed

lemma closure_outside_subset:
    fixes S :: "'a::real_normed_vector set"
    assumes "closed S"
      shows "closure(outside S) \<subseteq> S \<union> outside S"
  by (metis assms closed_open closure_minimal inside_outside open_inside sup_ge2)

lemma frontier_outside_subset:
  fixes S :: "'a::real_normed_vector set"
  assumes "closed S"
  shows "frontier(outside S) \<subseteq> S"
  unfolding frontier_def
  by (metis Diff_subset_conv assms closure_outside_subset interior_eq open_outside sup_aci(1))

lemma inside_complement_unbounded_connected_empty:
     "\<lbrakk>connected (- S); \<not> bounded (- S)\<rbrakk> \<Longrightarrow> inside S = {}"
  using inside_subset by blast

lemma inside_bounded_complement_connected_empty:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "\<lbrakk>connected (- S); bounded S\<rbrakk> \<Longrightarrow> inside S = {}"
  by (metis inside_complement_unbounded_connected_empty cobounded_imp_unbounded)

lemma inside_inside:
    assumes "S \<subseteq> inside T"
    shows "inside S - T \<subseteq> inside T"
unfolding inside_def
proof clarify
  fix x
  assume x: "x \<notin> T" "x \<notin> S" and bo: "bounded (connected_component_set (- S) x)"
  show "bounded (connected_component_set (- T) x)"
  proof (cases "S \<inter> connected_component_set (- T) x = {}")
    case True then show ?thesis
      by (metis bounded_subset [OF bo] compl_le_compl_iff connected_component_idemp connected_component_mono disjoint_eq_subset_Compl double_compl)
  next
    case False 
    then obtain y where y: "y  \<in> S" "y \<in> connected_component_set (- T) x"
      by (meson disjoint_iff)
    then have "bounded (connected_component_set (- T) y)"
      using assms [unfolded inside_def] by blast
    with y show ?thesis
      by (metis connected_component_eq)
  qed
qed

lemma inside_inside_subset: "inside(inside S) \<subseteq> S"
  using inside_inside union_with_outside by fastforce

lemma inside_outside_intersect_connected:
      "\<lbrakk>connected T; inside S \<inter> T \<noteq> {}; outside S \<inter> T \<noteq> {}\<rbrakk> \<Longrightarrow> S \<inter> T \<noteq> {}"
  apply (simp add: inside_def outside_def ex_in_conv [symmetric] disjoint_eq_subset_Compl, clarify)
  by (metis (no_types, hide_lams) Compl_anti_mono connected_component_eq connected_component_maximal contra_subsetD double_compl)

lemma outside_bounded_nonempty:
  fixes S :: "'a :: {real_normed_vector, perfect_space} set"
    assumes "bounded S" shows "outside S \<noteq> {}"
  by (metis (no_types, lifting) Collect_empty_eq Collect_mem_eq Compl_eq_Diff_UNIV Diff_cancel
                   Diff_disjoint UNIV_I assms ball_eq_empty bounded_diff cobounded_outside convex_ball
                   double_complement order_refl outside_convex outside_def)

lemma outside_compact_in_open:
    fixes S :: "'a :: {real_normed_vector,perfect_space} set"
    assumes S: "compact S" and T: "open T" and "S \<subseteq> T" "T \<noteq> {}"
      shows "outside S \<inter> T \<noteq> {}"
proof -
  have "outside S \<noteq> {}"
    by (simp add: compact_imp_bounded outside_bounded_nonempty S)
  with assms obtain a b where a: "a \<in> outside S" and b: "b \<in> T" by auto
  show ?thesis
  proof (cases "a \<in> T")
    case True with a show ?thesis by blast
  next
    case False
      have front: "frontier T \<subseteq> - S"
        using \<open>S \<subseteq> T\<close> frontier_disjoint_eq T by auto
      { fix \<gamma>
        assume "path \<gamma>" and pimg_sbs: "path_image \<gamma> - {pathfinish \<gamma>} \<subseteq> interior (- T)"
           and pf: "pathfinish \<gamma> \<in> frontier T" and ps: "pathstart \<gamma> = a"
        define c where "c = pathfinish \<gamma>"
        have "c \<in> -S" unfolding c_def using front pf by blast
        moreover have "open (-S)" using S compact_imp_closed by blast
        ultimately obtain \<epsilon>::real where "\<epsilon> > 0" and \<epsilon>: "cball c \<epsilon> \<subseteq> -S"
          using open_contains_cball[of "-S"] S by blast
        then obtain d where "d \<in> T" and d: "dist d c < \<epsilon>"
          using closure_approachable [of c T] pf unfolding c_def
          by (metis Diff_iff frontier_def)
        then have "d \<in> -S" using \<epsilon>
          using dist_commute by (metis contra_subsetD mem_cball not_le not_less_iff_gr_or_eq)
        have pimg_sbs_cos: "path_image \<gamma> \<subseteq> -S"
          using \<open>c \<in> - S\<close> \<open>S \<subseteq> T\<close> c_def interior_subset pimg_sbs by fastforce
        have "closed_segment c d \<le> cball c \<epsilon>"
          by (metis \<open>0 < \<epsilon>\<close> centre_in_cball closed_segment_subset convex_cball d dist_commute less_eq_real_def mem_cball)
        with \<epsilon> have "closed_segment c d \<subseteq> -S" by blast
        moreover have con_gcd: "connected (path_image \<gamma> \<union> closed_segment c d)"
          by (rule connected_Un) (auto simp: c_def \<open>path \<gamma>\<close> connected_path_image)
        ultimately have "connected_component (- S) a d"
          unfolding connected_component_def using pimg_sbs_cos ps by blast
        then have "outside S \<inter> T \<noteq> {}"
          using outside_same_component [OF _ a]  by (metis IntI \<open>d \<in> T\<close> empty_iff)
      } note * = this
      have pal: "pathstart (linepath a b) \<in> closure (- T)"
        by (auto simp: False closure_def)
      show ?thesis
        by (rule exists_path_subpath_to_frontier [OF path_linepath pal _ *]) (auto simp: b)
  qed
qed

lemma inside_inside_compact_connected:
    fixes S :: "'a :: euclidean_space set"
    assumes S: "closed S" and T: "compact T" and "connected T" "S \<subseteq> inside T"
      shows "inside S \<subseteq> inside T"
proof (cases "inside T = {}")
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
    have "bounded S"
      using assms by (meson bounded_inside bounded_subset compact_imp_bounded)
    then have coms: "compact S"
      by (simp add: S compact_eq_bounded_closed)
    then have bst: "bounded (S \<union> T)"
      by (simp add: compact_imp_bounded T)
    then obtain r where "0 < r" and r: "S \<union> T \<subseteq> ball 0 r"
      using bounded_subset_ballD by blast
    have outst: "outside S \<inter> outside T \<noteq> {}"
    proof -
      have "- ball 0 r \<subseteq> outside S"
        by (meson convex_ball le_supE outside_subset_convex r)
      moreover have "- ball 0 r \<subseteq> outside T"
        by (meson convex_ball le_supE outside_subset_convex r)
      ultimately show ?thesis
        by (metis Compl_subset_Compl_iff Int_subset_iff bounded_ball inf.orderE outside_bounded_nonempty outside_no_overlap)
    qed
    have "S \<inter> T = {}" using assms
      by (metis disjoint_iff_not_equal inside_no_overlap subsetCE)
    moreover have "outside S \<inter> inside T \<noteq> {}"
      by (meson False assms(4) compact_eq_bounded_closed coms open_inside outside_compact_in_open T)
    ultimately have "inside S \<inter> T = {}"
      using inside_outside_intersect_connected [OF \<open>connected T\<close>, of S]
      by (metis "2" compact_eq_bounded_closed coms connected_outside inf.commute inside_outside_intersect_connected outst)
    then show ?thesis
      using inside_inside [OF \<open>S \<subseteq> inside T\<close>] by blast
  qed
qed

lemma connected_with_inside:
    fixes S :: "'a :: real_normed_vector set"
    assumes S: "closed S" and cons: "connected S"
      shows "connected(S \<union> inside S)"
proof (cases "S \<union> inside S = UNIV")
  case True with assms show ?thesis by auto
next
  case False
  then obtain b where b: "b \<notin> S" "b \<notin> inside S" by blast
  have *: "\<exists>y T. y \<in> S \<and> connected T \<and> a \<in> T \<and> y \<in> T \<and> T \<subseteq> (S \<union> inside S)" 
    if "a \<in> S \<union> inside S" for a
    using that 
  proof
    assume "a \<in> S" then show ?thesis
      by (rule_tac x=a in exI, rule_tac x="{a}" in exI, simp)
  next
    assume a: "a \<in> inside S"
    then have ain: "a \<in> closure (inside S)"
      by (simp add: closure_def)
    show ?thesis
      apply (rule exists_path_subpath_to_frontier [OF path_linepath [of a b], of "inside S"])
        apply (simp_all add: ain b)
      subgoal for h
        apply (rule_tac x="pathfinish h" in exI)
        apply (simp add: subsetD [OF frontier_inside_subset[OF S]])
        apply (rule_tac x="path_image h" in exI)
        apply (simp add: pathfinish_in_path_image connected_path_image, auto)
        by (metis Diff_single_insert S frontier_inside_subset insert_iff interior_subset subsetD)
      done
  qed
  show ?thesis
    apply (simp add: connected_iff_connected_component)
    apply (clarsimp simp add: connected_component_def dest!: *)
    subgoal for x y u u' T t'
      by (rule_tac x="(S \<union> T \<union> t')" in exI) (auto intro!: connected_Un cons)
    done
qed

text\<open>The proof is virtually the same as that above.\<close>
lemma connected_with_outside:
    fixes S :: "'a :: real_normed_vector set"
    assumes S: "closed S" and cons: "connected S"
      shows "connected(S \<union> outside S)"
proof (cases "S \<union> outside S = UNIV")
  case True with assms show ?thesis by auto
next
  case False
  then obtain b where b: "b \<notin> S" "b \<notin> outside S" by blast
  have *: "\<exists>y T. y \<in> S \<and> connected T \<and> a \<in> T \<and> y \<in> T \<and> T \<subseteq> (S \<union> outside S)" if "a \<in> (S \<union> outside S)" for a
  using that proof
    assume "a \<in> S" then show ?thesis
      by (rule_tac x=a in exI, rule_tac x="{a}" in exI, simp)
  next
    assume a: "a \<in> outside S"
    then have ain: "a \<in> closure (outside S)"
      by (simp add: closure_def)
    show ?thesis
      apply (rule exists_path_subpath_to_frontier [OF path_linepath [of a b], of "outside S"])
        apply (simp_all add: ain b)
      subgoal for h
      apply (rule_tac x="pathfinish h" in exI)
        apply (simp add: subsetD [OF frontier_outside_subset[OF S]])
      apply (rule_tac x="path_image h" in exI)
      apply (simp add: pathfinish_in_path_image connected_path_image, auto)
        by (metis (no_types, lifting) frontier_outside_subset insertE insert_Diff interior_eq open_outside pathfinish_in_path_image S subsetCE)
      done
  qed
  show ?thesis
    apply (simp add: connected_iff_connected_component)
    apply (clarsimp simp add: connected_component_def dest!: *)
    subgoal for x y u u' T t'
      by (rule_tac x="(S \<union> T \<union> t')" in exI) (auto intro!: connected_Un cons)
    done
qed

lemma inside_inside_eq_empty [simp]:
    fixes S :: "'a :: {real_normed_vector, perfect_space} set"
    assumes S: "closed S" and cons: "connected S"
      shows "inside (inside S) = {}"
  by (metis (no_types) unbounded_outside connected_with_outside [OF assms] bounded_Un
           inside_complement_unbounded_connected_empty unbounded_outside union_with_outside)

lemma inside_in_components:
     "inside S \<in> components (- S) \<longleftrightarrow> connected(inside S) \<and> inside S \<noteq> {}" (is "?lhs = ?rhs")
proof 
  assume R: ?rhs
  then have "\<And>x. \<lbrakk>x \<in> S; x \<in> inside S\<rbrakk> \<Longrightarrow> \<not> connected (inside S)"
    by (simp add: inside_outside)
  with R show ?lhs
    unfolding in_components_maximal
    by (auto intro: inside_same_component connected_componentI)
qed (simp add: in_components_maximal)

text\<open>The proof is like that above.\<close>
lemma outside_in_components:
     "outside S \<in> components (- S) \<longleftrightarrow> connected(outside S) \<and> outside S \<noteq> {}" (is "?lhs = ?rhs")
proof 
  assume R: ?rhs
  then have "\<And>x. \<lbrakk>x \<in> S; x \<in> outside S\<rbrakk> \<Longrightarrow> \<not> connected (outside S)"
    by (meson disjoint_iff outside_no_overlap)
  with R show ?lhs
    unfolding in_components_maximal
    by (auto intro: outside_same_component connected_componentI)
qed (simp add: in_components_maximal)

lemma bounded_unique_outside:
  fixes S :: "'a :: euclidean_space set"
  assumes "bounded S" "DIM('a) \<ge> 2"
  shows "(c \<in> components (- S) \<and> \<not> bounded c \<longleftrightarrow> c = outside S)" 
  using assms
  by (metis cobounded_unique_unbounded_components connected_outside double_compl outside_bounded_nonempty outside_in_components unbounded_outside)


subsection\<open>Condition for an open map's image to contain a ball\<close>

proposition ball_subset_open_map_image:
  fixes f :: "'a::heine_borel \<Rightarrow> 'b :: {real_normed_vector,heine_borel}"
  assumes contf: "continuous_on (closure S) f"
      and oint: "open (f ` interior S)"
      and le_no: "\<And>z. z \<in> frontier S \<Longrightarrow> r \<le> norm(f z - f a)"
      and "bounded S" "a \<in> S" "0 < r"
    shows "ball (f a) r \<subseteq> f ` S"
proof (cases "f ` S = UNIV")
  case True then show ?thesis by simp
next
  case False
  then have "closed (frontier (f ` S))" "frontier (f ` S) \<noteq> {}"
    using \<open>a \<in> S\<close> by (auto simp: frontier_eq_empty)
  then obtain w where w: "w \<in> frontier (f ` S)"
    and dw_le: "\<And>y. y \<in> frontier (f ` S) \<Longrightarrow> norm (f a - w) \<le> norm (f a - y)"
    by (auto simp add: dist_norm intro: distance_attains_inf [of "frontier(f ` S)" "f a"])
  then obtain \<xi> where \<xi>: "\<And>n. \<xi> n \<in> f ` S" and tendsw: "\<xi> \<longlonglongrightarrow> w"
    by (metis Diff_iff frontier_def closure_sequential)
    then have "\<And>n. \<exists>x \<in> S. \<xi> n = f x" by force
    then obtain z where zs: "\<And>n. z n \<in> S" and fz: "\<And>n. \<xi> n = f (z n)"
      by metis
    then obtain y K where y: "y \<in> closure S" and "strict_mono (K :: nat \<Rightarrow> nat)" 
                      and Klim: "(z \<circ> K) \<longlonglongrightarrow> y"
      using \<open>bounded S\<close>
      unfolding compact_closure [symmetric] compact_def by (meson closure_subset subset_iff)
    then have ftendsw: "((\<lambda>n. f (z n)) \<circ> K) \<longlonglongrightarrow> w"
      by (metis LIMSEQ_subseq_LIMSEQ fun.map_cong0 fz tendsw)
    have zKs: "\<And>n. (z \<circ> K) n \<in> S" by (simp add: zs)
    have fz: "f \<circ> z = \<xi>"  "(\<lambda>n. f (z n)) = \<xi>"
      using fz by auto
    then have "(\<xi> \<circ> K) \<longlonglongrightarrow> f y"
      by (metis (no_types) Klim zKs y contf comp_assoc continuous_on_closure_sequentially)
    with fz have wy: "w = f y" using fz LIMSEQ_unique ftendsw by auto
    have rle: "r \<le> norm (f y - f a)"
    proof (rule le_no)
      show "y \<in> frontier S"
        using w wy oint by (force simp: imageI image_mono interiorI interior_subset frontier_def y)
    qed
    have **: "(b \<inter> (- S) \<noteq> {} \<and> b - (- S) \<noteq> {} \<Longrightarrow> b \<inter> f \<noteq> {})
              \<Longrightarrow> (b \<inter> S \<noteq> {}) \<Longrightarrow> b \<inter> f = {} \<Longrightarrow> b \<subseteq> S" 
             for b f and S :: "'b set"
      by blast
    have \<section>: "\<And>y. \<lbrakk>norm (f a - y) < r; y \<in> frontier (f ` S)\<rbrakk> \<Longrightarrow> False"
      by (metis dw_le norm_minus_commute not_less order_trans rle wy)
    show ?thesis
      apply (rule ** [OF connected_Int_frontier [where t = "f`S", OF connected_ball]])
        (*such a horrible mess*)
      using \<open>a \<in> S\<close> \<open>0 < r\<close> by (auto simp: disjoint_iff_not_equal dist_norm dest: \<section>)
qed


subsubsection\<open>Special characterizations of classes of functions into and out of R.\<close>

lemma Hausdorff_space_euclidean [simp]: "Hausdorff_space (euclidean :: 'a::metric_space topology)"
proof -
  have "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> disjnt U V"
    if "x \<noteq> y"
    for x y :: 'a
  proof (intro exI conjI)
    let ?r = "dist x y / 2"
    have [simp]: "?r > 0"
      by (simp add: that)
    show "open (ball x ?r)" "open (ball y ?r)" "x \<in> (ball x ?r)" "y \<in> (ball y ?r)"
      by (auto simp add: that)
    show "disjnt (ball x ?r) (ball y ?r)"
      unfolding disjnt_def by (simp add: disjoint_ballI)
  qed
  then show ?thesis
    by (simp add: Hausdorff_space_def)
qed

proposition embedding_map_into_euclideanreal:
  assumes "path_connected_space X"
  shows "embedding_map X euclideanreal f \<longleftrightarrow>
         continuous_map X euclideanreal f \<and> inj_on f (topspace X)"
  proof safe
  show "continuous_map X euclideanreal f"
    if "embedding_map X euclideanreal f"
    using continuous_map_in_subtopology homeomorphic_imp_continuous_map that
    unfolding embedding_map_def by blast
  show "inj_on f (topspace X)"
    if "embedding_map X euclideanreal f"
    using that homeomorphic_imp_injective_map
    unfolding embedding_map_def by blast
  show "embedding_map X euclideanreal f"
    if cont: "continuous_map X euclideanreal f" and inj: "inj_on f (topspace X)"
  proof -
    obtain g where gf: "\<And>x. x \<in> topspace X \<Longrightarrow> g (f x) = x"
      using inv_into_f_f [OF inj] by auto
    show ?thesis
      unfolding embedding_map_def homeomorphic_map_maps homeomorphic_maps_def
    proof (intro exI conjI)
      show "continuous_map X (top_of_set (f ` topspace X)) f"
        by (simp add: cont continuous_map_in_subtopology)
      let ?S = "f ` topspace X"
      have eq: "{x \<in> ?S. g x \<in> U} = f ` U" if "openin X U" for U
        using openin_subset [OF that] by (auto simp: gf)
      have 1: "g ` ?S \<subseteq> topspace X"
        using eq by blast
      have "openin (top_of_set ?S) {x \<in> ?S. g x \<in> T}"
        if "openin X T" for T
      proof -
        have "T \<subseteq> topspace X"
          by (simp add: openin_subset that)
        have RR: "\<forall>x \<in> ?S \<inter> g -` T. \<exists>d>0. \<forall>x' \<in> ?S \<inter> ball x d. g x' \<in> T"
        proof (clarsimp simp add: gf)
          have pcS: "path_connectedin euclidean ?S"
            using assms cont path_connectedin_continuous_map_image path_connectedin_topspace by blast
          show "\<exists>d>0. \<forall>x'\<in>f ` topspace X \<inter> ball (f x) d. g x' \<in> T"
            if "x \<in> T" for x
          proof -
            have x: "x \<in> topspace X"
              using \<open>T \<subseteq> topspace X\<close> \<open>x \<in> T\<close> by blast
            obtain u v d where "0 < d" "u \<in> topspace X" "v \<in> topspace X"
                         and sub_fuv: "?S \<inter> {f x - d .. f x + d} \<subseteq> {f u..f v}"
            proof (cases "\<exists>u \<in> topspace X. f u < f x")
              case True
              then obtain u where u: "u \<in> topspace X" "f u < f x" ..
              show ?thesis
              proof (cases "\<exists>v \<in> topspace X. f x < f v")
                case True
                then obtain v where v: "v \<in> topspace X" "f x < f v" ..
                show ?thesis
                proof
                  let ?d = "min (f x - f u) (f v - f x)"
                  show "0 < ?d"
                    by (simp add: \<open>f u < f x\<close> \<open>f x < f v\<close>)
                  show "f ` topspace X \<inter> {f x - ?d..f x + ?d} \<subseteq> {f u..f v}"
                    by fastforce
                qed (auto simp: u v)
              next
                case False
                show ?thesis
                proof
                  let ?d = "f x - f u"
                  show "0 < ?d"
                    by (simp add: u)
                  show "f ` topspace X \<inter> {f x - ?d..f x + ?d} \<subseteq> {f u..f x}"
                    using x u False by auto
                qed (auto simp: x u)
              qed
            next
              case False
              note no_u = False
              show ?thesis
              proof (cases "\<exists>v \<in> topspace X. f x < f v")
                case True
                then obtain v where v: "v \<in> topspace X" "f x < f v" ..
                show ?thesis
                proof
                  let ?d = "f v - f x"
                  show "0 < ?d"
                    by (simp add: v)
                  show "f ` topspace X \<inter> {f x - ?d..f x + ?d} \<subseteq> {f x..f v}"
                    using False by auto
                qed (auto simp: x v)
              next
                case False
                show ?thesis
                proof
                  show "f ` topspace X \<inter> {f x - 1..f x + 1} \<subseteq> {f x..f x}"
                    using False no_u by fastforce
                qed (auto simp: x)
              qed
            qed
            then obtain h where "pathin X h" "h 0 = u" "h 1 = v"
              using assms unfolding path_connected_space_def by blast
            obtain C where "compactin X C" "connectedin X C" "u \<in> C" "v \<in> C"
            proof
              show "compactin X (h ` {0..1})"
                using that by (simp add: \<open>pathin X h\<close> compactin_path_image)
              show "connectedin X (h ` {0..1})"
                using \<open>pathin X h\<close> connectedin_path_image by blast
            qed (use \<open>h 0 = u\<close> \<open>h 1 = v\<close> in auto)
            have "continuous_map (subtopology euclideanreal (?S \<inter> {f x - d .. f x + d})) (subtopology X C) g"
            proof (rule continuous_inverse_map)
              show "compact_space (subtopology X C)"
                using \<open>compactin X C\<close> compactin_subspace by blast
              show "continuous_map (subtopology X C) euclideanreal f"
                by (simp add: cont continuous_map_from_subtopology)
              have "{f u .. f v} \<subseteq> f ` topspace (subtopology X C)"
              proof (rule connected_contains_Icc)
                show "connected (f ` topspace (subtopology X C))"
                  using connectedin_continuous_map_image [OF cont]
                  by (simp add: \<open>compactin X C\<close> \<open>connectedin X C\<close> compactin_subset_topspace inf_absorb2)
                show "f u \<in> f ` topspace (subtopology X C)"
                  by (simp add: \<open>u \<in> C\<close> \<open>u \<in> topspace X\<close>)
                show "f v \<in> f ` topspace (subtopology X C)"
                  by (simp add: \<open>v \<in> C\<close> \<open>v \<in> topspace X\<close>)
              qed
              then show "f ` topspace X \<inter> {f x - d..f x + d} \<subseteq> f ` topspace (subtopology X C)"
                using sub_fuv by blast
            qed (auto simp: gf)
            then have contg: "continuous_map (subtopology euclideanreal (?S \<inter> {f x - d .. f x + d})) X g"
              using continuous_map_in_subtopology by blast
            have "\<exists>e>0. \<forall>x \<in> ?S \<inter> {f x - d .. f x + d} \<inter> ball (f x) e. g x \<in> T"
              using openin_continuous_map_preimage [OF contg \<open>openin X T\<close>] x \<open>x \<in> T\<close> \<open>0 < d\<close>
              unfolding openin_euclidean_subtopology_iff
              by (force simp: gf dist_commute)
            then obtain e where "e > 0 \<and> (\<forall>x\<in>f ` topspace X \<inter> {f x - d..f x + d} \<inter> ball (f x) e. g x \<in> T)"
              by metis
            with \<open>0 < d\<close> have "min d e > 0" "\<forall>u. u \<in> topspace X \<longrightarrow> \<bar>f x - f u\<bar> < min d e \<longrightarrow> u \<in> T"
              using dist_real_def gf by force+
            then show ?thesis
              by (metis (full_types) Int_iff dist_real_def image_iff mem_ball gf)
          qed
        qed
        then obtain d where d: "\<And>r. r \<in> ?S \<inter> g -` T \<Longrightarrow>
                d r > 0 \<and> (\<forall>x \<in> ?S \<inter> ball r (d r). g x \<in> T)"
          by metis
        show ?thesis
          unfolding openin_subtopology
        proof (intro exI conjI)
          show "{x \<in> ?S. g x \<in> T} = (\<Union>r \<in> ?S \<inter> g -` T. ball r (d r)) \<inter> f ` topspace X"
            using d by (auto simp: gf)
        qed auto
      qed
      then show "continuous_map (top_of_set ?S) X g"
        by (simp add: continuous_map_def gf)
    qed (auto simp: gf)
  qed
qed

subsubsection \<open>An injective function into R is a homeomorphism and so an open map.\<close>

lemma injective_into_1d_eq_homeomorphism:
  fixes f :: "'a::topological_space \<Rightarrow> real"
  assumes f: "continuous_on S f" and S: "path_connected S"
  shows "inj_on f S \<longleftrightarrow> (\<exists>g. homeomorphism S (f ` S) f g)"
proof
  show "\<exists>g. homeomorphism S (f ` S) f g"
    if "inj_on f S"
  proof -
    have "embedding_map (top_of_set S) euclideanreal f"
      using that embedding_map_into_euclideanreal [of "top_of_set S" f] assms by auto
    then show ?thesis
      by (simp add: embedding_map_def) (metis all_closedin_homeomorphic_image f homeomorphism_injective_closed_map that)
  qed
qed (metis homeomorphism_def inj_onI)

lemma injective_into_1d_imp_open_map:
  fixes f :: "'a::topological_space \<Rightarrow> real"
  assumes "continuous_on S f" "path_connected S" "inj_on f S" "openin (subtopology euclidean S) T"
  shows "openin (subtopology euclidean (f ` S)) (f ` T)"
  using assms homeomorphism_imp_open_map injective_into_1d_eq_homeomorphism by blast

lemma homeomorphism_into_1d:
  fixes f :: "'a::topological_space \<Rightarrow> real"
  assumes "path_connected S" "continuous_on S f" "f ` S = T" "inj_on f S"
  shows "\<exists>g. homeomorphism S T f g"
  using assms injective_into_1d_eq_homeomorphism by blast

subsection\<^marker>\<open>tag unimportant\<close> \<open>Rectangular paths\<close>

definition\<^marker>\<open>tag unimportant\<close> rectpath where
  "rectpath a1 a3 = (let a2 = Complex (Re a3) (Im a1); a4 = Complex (Re a1) (Im a3)
                      in linepath a1 a2 +++ linepath a2 a3 +++ linepath a3 a4 +++ linepath a4 a1)"

lemma path_rectpath [simp, intro]: "path (rectpath a b)"
  by (simp add: Let_def rectpath_def)

lemma pathstart_rectpath [simp]: "pathstart (rectpath a1 a3) = a1"
  by (simp add: rectpath_def Let_def)

lemma pathfinish_rectpath [simp]: "pathfinish (rectpath a1 a3) = a1"
  by (simp add: rectpath_def Let_def)

lemma simple_path_rectpath [simp, intro]:
  assumes "Re a1 \<noteq> Re a3" "Im a1 \<noteq> Im a3"
  shows   "simple_path (rectpath a1 a3)"
  unfolding rectpath_def Let_def using assms
  by (intro simple_path_join_loop arc_join arc_linepath)
     (auto simp: complex_eq_iff path_image_join closed_segment_same_Re closed_segment_same_Im)

lemma path_image_rectpath:
  assumes "Re a1 \<le> Re a3" "Im a1 \<le> Im a3"
  shows "path_image (rectpath a1 a3) =
           {z. Re z \<in> {Re a1, Re a3} \<and> Im z \<in> {Im a1..Im a3}} \<union>
           {z. Im z \<in> {Im a1, Im a3} \<and> Re z \<in> {Re a1..Re a3}}" (is "?lhs = ?rhs")
proof -
  define a2 a4 where "a2 = Complex (Re a3) (Im a1)" and "a4 = Complex (Re a1) (Im a3)"
  have "?lhs = closed_segment a1 a2 \<union> closed_segment a2 a3 \<union>
                  closed_segment a4 a3 \<union> closed_segment a1 a4"
    by (simp_all add: rectpath_def Let_def path_image_join closed_segment_commute
                      a2_def a4_def Un_assoc)
  also have "\<dots> = ?rhs" using assms
    by (auto simp: rectpath_def Let_def path_image_join a2_def a4_def
          closed_segment_same_Re closed_segment_same_Im closed_segment_eq_real_ivl)
  finally show ?thesis .
qed

lemma path_image_rectpath_subset_cbox:
  assumes "Re a \<le> Re b" "Im a \<le> Im b"
  shows   "path_image (rectpath a b) \<subseteq> cbox a b"
  using assms by (auto simp: path_image_rectpath in_cbox_complex_iff)

lemma path_image_rectpath_inter_box:
  assumes "Re a \<le> Re b" "Im a \<le> Im b"
  shows   "path_image (rectpath a b) \<inter> box a b = {}"
  using assms by (auto simp: path_image_rectpath in_box_complex_iff)

lemma path_image_rectpath_cbox_minus_box:
  assumes "Re a \<le> Re b" "Im a \<le> Im b"
  shows   "path_image (rectpath a b) = cbox a b - box a b"
  using assms by (auto simp: path_image_rectpath in_cbox_complex_iff
                             in_box_complex_iff)

end
