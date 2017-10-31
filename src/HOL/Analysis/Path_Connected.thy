(*  Title:      HOL/Analysis/Path_Connected.thy
    Authors:    LC Paulson and Robert Himmelmann (TU Muenchen), based on material from HOL Light
*)

section \<open>Continuous paths and path-connected sets\<close>

theory Path_Connected
imports Continuous_Extension Continuum_Not_Denumerable
begin

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

lemma joinpaths_eq:
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
    apply (rule continuous_on_closed_Un)
    using 1 2
    apply auto
    done
qed

lemma path_join_imp: "\<lbrakk>path g1; path g2; pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow> path(g1 +++ g2)"
  by (simp add: path_join)

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
    apply (simp add: joinpaths_def split: if_split_asm)
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
    apply (simp add: joinpaths_def split: if_split_asm)
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


subsection\<open>Some reversed and "if and only if" versions of joining theorems\<close>

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
  then obtain d1 where "d1 > 0"
       and d1: "\<And>x'. \<lbrakk>x'\<in>{0..1}; norm x' < d1\<rbrakk> \<Longrightarrow> dist (g2 x') (g2 0) < e/2"
    using assms(2) unfolding path_def continuous_on_iff
    apply (drule_tac x=0 in bspec, simp)
    by (metis half_gt_zero_iff norm_conv_dist)
  obtain d2 where "d2 > 0"
       and d2: "\<And>x'. \<lbrakk>x'\<in>{0..1}; dist x' (1/2) < d2\<rbrakk>
                      \<Longrightarrow> dist ((g1 +++ g2) x') (g1 1) < e/2"
    using assms(1) \<open>e > 0\<close> unfolding path_def continuous_on_iff
    apply (drule_tac x="1/2" in bspec, simp)
    apply (drule_tac x="e/2" in spec)
    apply (force simp: joinpaths_def)
    done
  have int01_1: "min (1/2) (min d1 d2) / 2 \<in> {0..1}"
    using \<open>d1 > 0\<close> \<open>d2 > 0\<close> by (simp add: min_def)
  have dist1: "norm (min (1 / 2) (min d1 d2) / 2) < d1"
    using \<open>d1 > 0\<close> \<open>d2 > 0\<close> by (simp add: min_def dist_norm)
  have int01_2: "1/2 + min (1/2) (min d1 d2) / 4 \<in> {0..1}"
    using \<open>d1 > 0\<close> \<open>d2 > 0\<close> by (simp add: min_def)
  have dist2: "dist (1 / 2 + min (1 / 2) (min d1 d2) / 4) (1 / 2) < d2"
    using \<open>d1 > 0\<close> \<open>d2 > 0\<close> by (simp add: min_def dist_norm)
  have [simp]: "~ min (1 / 2) (min d1 d2) \<le> 0"
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
      by (force simp: joinpaths_def split_ifs divide_simps)
  qed
  ultimately have "arc g2"
    using assms  by (simp add: arc_def)
  have "g2 y = g1 0 \<or> g2 y = g1 1"
       if "g1 x = g2 y" "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1" for x y
      using * [of "x / 2" "(y + 1) / 2"] that
      by (auto simp: joinpaths_def split_ifs divide_simps)
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
    by (auto simp: joinpaths_def pathstart_def pathfinish_def split_ifs divide_simps)
  then have n1: "~ (pathstart g1 \<in> path_image g2)"
    unfolding pathstart_def path_image_def
    using atLeastAtMost_iff by blast
  show ?rhs using \<open>?lhs\<close>
    apply (rule simple_path_joinE [OF arc_imp_simple_path assms])
    using n1 by force
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


subsection\<open>The joining of paths is associative\<close>

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

subsubsection\<open>Symmetry and loops\<close>

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


section\<open>Choosing a subpath of an existing path\<close>

definition subpath :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a::real_normed_vector"
  where "subpath a b g \<equiv> \<lambda>x. g((b - a) * x + a)"

lemma path_image_subpath_gen:
  fixes g :: "_ \<Rightarrow> 'a::real_normed_vector"
  shows "path_image(subpath u v g) = g ` (closed_segment u v)"
  apply (simp add: closed_segment_real_eq path_image_def subpath_def)
  apply (subst o_def [of g, symmetric])
  apply (simp add: image_comp [symmetric])
  done

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
by (metis add.commute affine_ineq less_eq_real_def mult.right_neutral)

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
       split: if_split_asm)
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
       split: if_split_asm)
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
  apply (simp add: closed_segment_real_eq image_affinity_atLeastAtMost path_image_subpath)
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
    then have "u > 0" using \<open>0 \<le> u\<close> by auto
    { fix e::real assume "e > 0"
      obtain d where "d>0" and d: "\<And>x'. \<lbrakk>x' \<in> {0..1}; dist x' u \<le> d\<rbrakk> \<Longrightarrow> dist (g x') (g u) < e"
        using continuous_onE [OF gcon _ \<open>e > 0\<close>] \<open>0 \<le> _\<close> \<open>_ \<le> 1\<close> atLeastAtMost_iff by auto
      have *: "dist (max 0 (u - d / 2)) u \<le> d"
        using \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> \<open>d > 0\<close> by (simp add: dist_real_def)
      have "\<exists>y\<in>S. dist y (g u) < e"
        using \<open>0 < u\<close> \<open>u \<le> 1\<close> \<open>d > 0\<close>
        by (force intro: d [OF _ *] umin')
    }
    then have "g u \<in> closure S"
      by (simp add: frontier_def closure_approachable)
  }
  then show ?thesis
    apply (rule_tac u=u in that)
    apply (auto simp: \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> gu interior_closure umin)
    using \<open>_ \<le> 1\<close> interior_closure umin apply fastforce
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
    apply (rule that [OF \<open>0 \<le> u\<close> \<open>u \<le> 1\<close>])
    apply (simp add: gunot)
    using \<open>0 \<le> u\<close> u0 by (force simp: subpath_def gxin)
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
    apply (rule that [OF \<open>0 \<le> u\<close> \<open>u \<le> 1\<close>])
    apply (metis DiffI disj frontier_def g0 notin pathstart_def)
    using \<open>0 \<le> u\<close> g0 disj
    apply (simp add: path_image_subpath_gen)
    apply (auto simp: closed_segment_eq_real_ivl pathstart_def pathfinish_def subpath_def)
    apply (rename_tac y)
    apply (drule_tac x="y/u" in spec)
    apply (auto split: if_split_asm)
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
    apply (simp_all add: path_image_subpath)
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
    apply (rule that [OF \<open>path h\<close>])
    using assms h
    apply auto
    apply (metis Diff_single_insert frontier_subset_eq insert_iff interior_subset subset_iff)
    done
qed

subsection \<open>shiftpath: Reparametrizing a closed curve to start at some chosen point\<close>

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
    apply (rule continuous_on_closed_Un)
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
    apply (simp add: split: if_split_asm)
      apply (drule *; auto)+
    done
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
    by (simp add:  path_linepath) (force simp: algebra_simps linepath_def)
qed

lemma simple_path_linepath[intro]: "a \<noteq> b \<Longrightarrow> simple_path (linepath a b)"
  by (simp add: arc_imp_simple_path arc_linepath)

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


subsection\<open>Segments via convex hulls\<close>

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
    apply (rule convexD_alt)
    using assms
    apply (auto simp: convex_convex_hull)
    done
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
      also have "... \<subseteq> S"
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

subsection \<open>Bounding a point away from a path\<close>

lemma not_on_path_ball:
  fixes g :: "real \<Rightarrow> 'a::heine_borel"
  assumes "path g"
    and "z \<notin> path_image g"
  shows "\<exists>e > 0. ball z e \<inter> path_image g = {}"
proof -
  obtain a where "a \<in> path_image g" "\<forall>y \<in> path_image g. dist z a \<le> dist z y"
    apply (rule distance_attains_inf[OF _ path_image_nonempty, of g z])
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


subsubsection \<open>Path components as sets\<close>

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

lemma convex_imp_path_connected:
  fixes s :: "'a::real_normed_vector set"
  assumes "convex s"
  shows "path_connected s"
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
    using assms[unfolded open_contains_ball]
    by auto
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
  assume as: "y \<in> S - path_component_set S x"
  then obtain e where e: "e > 0" "ball y e \<subseteq> S"
    using assms [unfolded open_contains_ball]
    by auto
  show "\<exists>e>0. ball y e \<subseteq> S - path_component_set S x"
    apply (rule_tac x=e in exI)
    apply rule
    apply (rule \<open>e>0\<close>)
    apply rule
    apply rule
    defer
  proof (rule ccontr)
    fix z
    assume "z \<in> ball y e" "\<not> z \<notin> path_component_set S x"
    then have "y \<in> path_component_set S x"
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
  assumes "continuous_on S f"
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
    unfolding x' y'
    apply (rule_tac x="f \<circ> g" in exI)
    unfolding path_defs
    apply (intro conjI continuous_on_compose continuous_on_subset[OF assms(1)])
    apply auto
    done
qed

lemma path_connected_translationI:
  fixes a :: "'a :: topological_group_add"
  assumes "path_connected S" shows "path_connected ((\<lambda>x. a + x) ` S)"
  by (intro path_connected_continuous_image assms continuous_intros)

lemma path_connected_translation:
  fixes a :: "'a :: topological_group_add"
  shows "path_connected ((\<lambda>x. a + x) ` S) = path_connected S"
proof -
  have "\<forall>x y. op + (x::'a) ` op + (0 - x) ` y = y"
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
  "s homeomorphic t \<Longrightarrow> path_connected s \<longleftrightarrow> path_connected t"
  unfolding homeomorphic_def homeomorphism_def by (metis path_connected_continuous_image)

lemma path_connected_empty [simp]: "path_connected {}"
  unfolding path_connected_def by auto

lemma path_connected_singleton [simp]: "path_connected {a}"
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

subsection\<open>Lemmas about path-connectedness\<close>

lemma path_connected_linear_image:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "path_connected s" "bounded_linear f"
    shows "path_connected(f ` s)"
by (auto simp: linear_continuous_on assms path_connected_continuous_image)

lemma is_interval_path_connected: "is_interval s \<Longrightarrow> path_connected s"
  by (simp add: convex_imp_path_connected is_interval_convex)

lemma linear_homeomorphism_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
    obtains g where "homeomorphism (f ` S) S g f"
using linear_injective_left_inverse [OF assms]
apply clarify
apply (rule_tac g=g in that)
using assms
apply (auto simp: homeomorphism_def eq_id_iff [symmetric] image_comp comp_def linear_conv_bounded_linear linear_continuous_on)
done

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
    apply (simp add: path_def)
    apply (rule continuous_on_compose2 [where f = h])
    apply (rule continuous_intros | force)+
    done
  moreover have "path (\<lambda>z. (g z, y2))"
    using \<open>path g\<close>
    apply (simp add: path_def)
    apply (rule continuous_on_compose2 [where f = g])
    apply (rule continuous_intros | force)+
    done
  ultimately have 1: "path ((\<lambda>z. (x1, h z)) +++ (\<lambda>z. (g z, y2)))"
    by (metis hf gs path_join_imp pathstart_def pathfinish_def)
  have "path_image ((\<lambda>z. (x1, h z)) +++ (\<lambda>z. (g z, y2))) \<subseteq> path_image (\<lambda>z. (x1, h z)) \<union> path_image (\<lambda>z. (g z, y2))"
    by (rule Path_Connected.path_image_join_subset)
  also have "... \<subseteq> (\<Union>x\<in>s. \<Union>x1\<in>t. {(x, x1)})"
    using g h \<open>x1 \<in> s\<close> \<open>y2 \<in> t\<close> by (force simp: path_image_def)
  finally have 2: "path_image ((\<lambda>z. (x1, h z)) +++ (\<lambda>z. (g z, y2))) \<subseteq> (\<Union>x\<in>s. \<Union>x1\<in>t. {(x, x1)})" .
  show "\<exists>g. path g \<and> path_image g \<subseteq> (\<Union>x\<in>s. \<Union>x1\<in>t. {(x, x1)}) \<and>
            pathstart g = (x1, y1) \<and> pathfinish g = (x2, y2)"
    apply (intro exI conjI)
       apply (rule 1)
      apply (rule 2)
     apply (metis hs pathstart_def pathstart_join)
    by (metis gf pathfinish_def pathfinish_join)
qed

lemma is_interval_path_connected_1:
  fixes s :: "real set"
  shows "is_interval s \<longleftrightarrow> path_connected s"
using is_interval_connected_1 is_interval_path_connected path_connected_imp_connected by blast


subsection\<open>Path components\<close>

lemma Union_path_component [simp]:
   "Union {path_component_set S x |x. x \<in> S} = S"
apply (rule subset_antisym)
using path_component_subset apply force
using path_component_refl by auto

lemma path_component_disjoint:
   "disjnt (path_component_set S a) (path_component_set S b) \<longleftrightarrow>
    (a \<notin> path_component_set S b)"
apply (auto simp: disjnt_def)
using path_component_eq apply fastforce
using path_component_sym path_component_trans by blast

lemma path_component_eq_eq:
   "path_component S x = path_component S y \<longleftrightarrow>
        (x \<notin> S) \<and> (y \<notin> S) \<or> x \<in> S \<and> y \<in> S \<and> path_component S x y"
apply (rule iffI, metis (no_types) path_component_mem(1) path_component_refl)
apply (erule disjE, metis Collect_empty_eq_bot path_component_eq_empty)
apply (rule ext)
apply (metis path_component_trans path_component_sym)
done

lemma path_component_unique:
  assumes "x \<in> c" "c \<subseteq> S" "path_connected c"
          "\<And>c'. \<lbrakk>x \<in> c'; c' \<subseteq> S; path_connected c'\<rbrakk> \<Longrightarrow> c' \<subseteq> c"
   shows "path_component_set S x = c"
apply (rule subset_antisym)
using assms
apply (metis mem_Collect_eq subsetCE path_component_eq_eq path_component_subset path_connected_path_component)
by (simp add: assms path_component_maximal)

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

lemma path_connected_sphere:
  fixes a :: "'a :: euclidean_space"
  assumes "2 \<le> DIM('a)"
  shows "path_connected(sphere a r)"
proof (cases r "0::real" rule: linorder_cases)
  case less
  then show ?thesis
    by (simp add: path_connected_empty)
next
  case equal
  then show ?thesis
    by (simp add: path_connected_singleton)
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
  then have "path_connected(op +a ` (sphere (0::'a) r))"
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
    fixes s :: "'a :: euclidean_space set"
    assumes "bounded s" "convex s" and 2: "2 \<le> DIM('a)"
    shows "path_connected (- s)"
proof (cases "s = {}")
  case True then show ?thesis
    using convex_imp_path_connected by auto
next
  case False
  then obtain a where "a \<in> s" by auto
  { fix x y assume "x \<notin> s" "y \<notin> s"
    then have "x \<noteq> a" "y \<noteq> a" using \<open>a \<in> s\<close> by auto
    then have bxy: "bounded(insert x (insert y s))"
      by (simp add: \<open>bounded s\<close>)
    then obtain B::real where B: "0 < B" and Bx: "norm (a - x) < B" and By: "norm (a - y) < B"
                          and "s \<subseteq> ball a B"
      using bounded_subset_ballD [OF bxy, of a] by (auto simp: dist_norm)
    define C where "C = B / norm(x - a)"
    { fix u
      assume u: "(1 - u) *\<^sub>R x + u *\<^sub>R (a + C *\<^sub>R (x - a)) \<in> s" and "0 \<le> u" "u \<le> 1"
      have CC: "1 \<le> 1 + (C - 1) * u"
        using \<open>x \<noteq> a\<close> \<open>0 \<le> u\<close>
        apply (simp add: C_def divide_simps norm_minus_commute)
        using Bx by auto
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
        using \<open>convex s\<close>
        apply (simp add: convex_alt)
        apply (drule_tac x=a in bspec)
         apply (rule  \<open>a \<in> s\<close>)
        apply (drule_tac x="a + (1 + (C - 1) * u) *\<^sub>R (x - a)" in bspec)
         using u apply (simp add: *)
        apply (drule_tac x="1 / (1 + (C - 1) * u)" in spec)
        using \<open>x \<noteq> a\<close> \<open>x \<notin> s\<close> \<open>0 \<le> u\<close> CC
        apply (auto simp: xeq)
        done
    }
    then have pcx: "path_component (- s) x (a + C *\<^sub>R (x - a))"
      by (force simp: closed_segment_def intro!: path_connected_linepath)
    define D where "D = B / norm(y - a)"  \<comment>\<open>massive duplication with the proof above\<close>
    { fix u
      assume u: "(1 - u) *\<^sub>R y + u *\<^sub>R (a + D *\<^sub>R (y - a)) \<in> s" and "0 \<le> u" "u \<le> 1"
      have DD: "1 \<le> 1 + (D - 1) * u"
        using \<open>y \<noteq> a\<close> \<open>0 \<le> u\<close>
        apply (simp add: D_def divide_simps norm_minus_commute)
        using By by auto
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
        using \<open>convex s\<close>
        apply (simp add: convex_alt)
        apply (drule_tac x=a in bspec)
         apply (rule  \<open>a \<in> s\<close>)
        apply (drule_tac x="a + (1 + (D - 1) * u) *\<^sub>R (y - a)" in bspec)
         using u apply (simp add: *)
        apply (drule_tac x="1 / (1 + (D - 1) * u)" in spec)
        using \<open>y \<noteq> a\<close> \<open>y \<notin> s\<close> \<open>0 \<le> u\<close> DD
        apply (auto simp: xeq)
        done
    }
    then have pdy: "path_component (- s) y (a + D *\<^sub>R (y - a))"
      by (force simp: closed_segment_def intro!: path_connected_linepath)
    have pyx: "path_component (- s) (a + D *\<^sub>R (y - a)) (a + C *\<^sub>R (x - a))"
      apply (rule path_component_of_subset [of "sphere a B"])
       using \<open>s \<subseteq> ball a B\<close>
       apply (force simp: ball_def dist_norm norm_minus_commute)
      apply (rule path_connected_sphere [OF 2, of a B, simplified path_connected_component, rule_format])
       using \<open>x \<noteq> a\<close>  using \<open>y \<noteq> a\<close>  B apply (auto simp: dist_norm C_def D_def)
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

proposition connected_open_delete:
  assumes "open S" "connected S" and 2: "2 \<le> DIM('N::euclidean_space)"
    shows "connected(S - {a::'N})"
proof (cases "a \<in> S")
  case True
  with \<open>open S\<close> obtain \<epsilon> where "\<epsilon> > 0" and \<epsilon>: "cball a \<epsilon> \<subseteq> S"
    using open_contains_cball_eq by blast
  have "dist a (a + \<epsilon> *\<^sub>R (SOME i. i \<in> Basis)) = \<epsilon>"
    by (simp add: dist_norm SOME_Basis \<open>0 < \<epsilon>\<close> less_imp_le)
  with \<epsilon> have "\<Inter>{S - ball a r |r. 0 < r \<and> r < \<epsilon>} \<subseteq> {} \<Longrightarrow> False"
    apply (drule_tac c="a + scaleR (\<epsilon>) ((SOME i. i \<in> Basis))" in subsetD)
    by auto
  then have nonemp: "(\<Inter>{S - ball a r |r. 0 < r \<and> r < \<epsilon>}) = {} \<Longrightarrow> False"
    by auto
  have con: "\<And>r. r < \<epsilon> \<Longrightarrow> connected (S - ball a r)"
    using \<epsilon> by (force intro: connected_diff_ball [OF \<open>connected S\<close> _ 2])
  have "x \<in> \<Union>{S - ball a r |r. 0 < r \<and> r < \<epsilon>}" if "x \<in> S - {a}" for x
    apply (rule UnionI [of "S - ball a (min \<epsilon> (dist a x) / 2)"])
     using that \<open>0 < \<epsilon>\<close> apply (simp_all add:)
    apply (rule_tac x="min \<epsilon> (dist a x) / 2" in exI)
    apply auto
    done
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
        using norm_Basis by fastforce
      with xb show ?thesis
        apply (simp add: abs_if split: if_split_asm)
        apply (metis add.inverse_inverse real_vector.scale_minus_left xb)
        done
    qed
    with \<open>r > 0\<close> b show "sphere 0 r = {r *\<^sub>R b, - r *\<^sub>R b}"
      by (force simp: sphere_def dist_norm)
    have "dist (r *\<^sub>R b) (- r *\<^sub>R b) = norm (r *\<^sub>R b + r *\<^sub>R b)"
      by (simp add: dist_norm)
    also have "... = norm ((2*r) *\<^sub>R b)"
      by (metis mult_2 scaleR_add_left)
    also have "... = 2*r"
      using \<open>r > 0\<close> b norm_Basis by fastforce
    finally show "dist (r *\<^sub>R b) (- r *\<^sub>R b) = 2*r" .
  qed
qed

lemma sphere_1D_doubleton:
  fixes a :: "'a :: euclidean_space"
  assumes "DIM('a) = 1" and "r > 0"
  obtains x y where "sphere a r = {x,y} \<and> dist x y = 2*r"
proof -
  have "sphere a r = op +a ` sphere 0 r"
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
    by (auto simp: )
  have "{x. dist a x \<le> r \<and> x \<notin> S} \<inter> {x. r \<le> dist a x \<and> x \<notin> S} \<noteq> {}"
    using \<open>b \<notin> S\<close> \<open>dist a b = r\<close> by blast
  moreover have "connected {x. dist a x \<le> r \<and> x \<notin> S}"
    apply (rule connected_intermediate_closure [of "ball a r"])
    using assms by auto
  moreover
  have "connected {x. r \<le> dist a x \<and> x \<notin> S}"
    apply (rule connected_intermediate_closure [of "- cball a r"])
    using assms apply (auto intro: connected_complement_bounded_convex)
    apply (metis ComplI interior_cball interior_closure mem_ball not_less)
    done
  ultimately show ?thesis
    by (simp add: CS connected_Un)
qed


subsection\<open>Every annulus is a connected set\<close>

lemma path_connected_2DIM_I:
  fixes a :: "'N::euclidean_space"
  assumes 2: "2 \<le> DIM('N)" and pc: "path_connected {r. 0 \<le> r \<and> P r}"
  shows "path_connected {x. P(norm(x - a))}"
proof -
  have "{x. P(norm(x - a))} = op+a ` {x. P(norm x)}"
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
        apply (rule_tac x=0 in exI, simp)
        using vector_choose_size zero_le_one by blast
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
      apply (subst *)
      apply (rule path_connected_continuous_image, auto)
      done
  qed
  ultimately show ?thesis
    using path_connected_translation by metis
qed

lemma path_connected_annulus:
  fixes a :: "'N::euclidean_space"
  assumes "2 \<le> DIM('N)"
  shows "path_connected {x. r1 < norm(x - a) \<and> norm(x - a) < r2}"
        "path_connected {x. r1 < norm(x - a) \<and> norm(x - a) \<le> r2}"
        "path_connected {x. r1 \<le> norm(x - a) \<and> norm(x - a) < r2}"
        "path_connected {x. r1 \<le> norm(x - a) \<and> norm(x - a) \<le> r2}"
  by (auto simp: is_interval_def intro!: is_interval_convex convex_imp_path_connected path_connected_2DIM_I [OF assms])

lemma connected_annulus:
  fixes a :: "'N::euclidean_space"
  assumes "2 \<le> DIM('N::euclidean_space)"
  shows "connected {x. r1 < norm(x - a) \<and> norm(x - a) < r2}"
        "connected {x. r1 < norm(x - a) \<and> norm(x - a) \<le> r2}"
        "connected {x. r1 \<le> norm(x - a) \<and> norm(x - a) < r2}"
        "connected {x. r1 \<le> norm(x - a) \<and> norm(x - a) \<le> r2}"
  by (auto simp: path_connected_annulus [OF assms] path_connected_imp_connected)


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
  from connectedD [OF \<open>connected S\<close> 1 2 3 4]
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
      apply (rule connected_disjoint_Union_open_pick [OF B, of A])
      using SA SB \<open>S \<in> A\<close> by auto
  moreover obtain S' where "S' \<in> A" "T \<subseteq> S'" "T \<inter> \<Union>(A - {S'}) = {}"
      apply (rule connected_disjoint_Union_open_pick [OF A, of B])
      using SA SB \<open>T \<in> B\<close> by auto
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
    apply (rule connected_disjoint_Union_open_unique)
    apply (simp add: components_eq disjnt_def pairwise_def)
    using \<open>open S\<close>
    apply (simp_all add: assms open_components in_components_connected in_components_nonempty)
    done
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
  fixes S :: "'a :: euclidean_space set"
  assumes "bounded (- S)" "\<not> connected S" "2 \<le> DIM('a)"
  obtains C where "C \<in> components S" "bounded C"
  by (meson cobounded_unique_unbounded_components connected_eq_connected_components_eq assms)


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

lemma inside_Int_outside [simp]: "inside s \<inter> outside s = {}"
  by (auto simp: inside_def outside_def)

lemma inside_Un_outside [simp]: "inside s \<union> outside s = (- s)"
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
  with \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> show ?thesis
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
        apply (rule connected_component_maximal)
        using that interior_subset mem_ball apply auto
        done
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
    have 1: "closed_segment x y \<inter> T \<noteq> {}" using \<open>y \<in> T\<close> by blast
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
      and nconn: "~ connected(- S)"
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
    fixes s :: "'a::real_normed_vector set"
    assumes "bounded s"
      shows "interior s \<subseteq> inside (frontier s)"
proof -
  { fix x y
    assume x: "x \<in> interior s" and y: "y \<notin> s"
       and cc: "connected_component (- frontier s) x y"
    have "connected_component_set (- frontier s) x \<inter> frontier s \<noteq> {}"
      apply (rule connected_Int_frontier, simp)
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
using inside_empty inside_Un_outside by blast

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
    define C where "C = (B + 1 + norm z) / norm (z-a)"
    have "C > 0"
      using \<open>0 < B\<close> zna by (simp add: C_def divide_simps add_strict_increasing)
    have "\<bar>norm (z + C *\<^sub>R (z-a)) - norm (C *\<^sub>R (z-a))\<bar> \<le> norm z"
      by (metis add_diff_cancel norm_triangle_ineq3)
    moreover have "norm (C *\<^sub>R (z-a)) > norm z + B"
      using zna \<open>B>0\<close> by (simp add: C_def le_max_iff_disj field_simps)
    ultimately have C: "norm (z + C *\<^sub>R (z-a)) > B" by linarith
    { fix u::real
      assume u: "0\<le>u" "u\<le>1" and ins: "(1 - u) *\<^sub>R z + u *\<^sub>R (z + C *\<^sub>R (z - a)) \<in> s"
      then have Cpos: "1 + u * C > 0"
        by (meson \<open>0 < C\<close> add_pos_nonneg less_eq_real_def zero_le_mult_iff zero_less_one)
      then have *: "(1 / (1 + u * C)) *\<^sub>R z + (u * C / (1 + u * C)) *\<^sub>R z = z"
        by (simp add: scaleR_add_left [symmetric] divide_simps)
      then have False
        using convexD_alt [OF s \<open>a \<in> s\<close> ins, of "1/(u*C + 1)"] \<open>C>0\<close> \<open>z \<notin> s\<close> Cpos u
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
  by (metis ComplD assms convex_in_outside equalityI inside_Un_outside subsetI sup.cobounded2)

lemma outside_singleton [simp]:
  fixes x :: "'a :: {real_normed_vector, perfect_space}"
  shows "outside {x} = -{x}"
  by (auto simp: outside_convex)

lemma inside_convex:
  fixes s :: "'a :: {real_normed_vector, perfect_space} set"
  shows "convex s \<Longrightarrow> inside s = {}"
  by (simp add: inside_outside outside_convex)

lemma inside_singleton [simp]:
  fixes x :: "'a :: {real_normed_vector, perfect_space}"
  shows "inside {x} = {}"
  by (auto simp: inside_convex)

lemma outside_subset_convex:
  fixes s :: "'a :: {real_normed_vector, perfect_space} set"
  shows "\<lbrakk>convex t; s \<subseteq> t\<rbrakk> \<Longrightarrow> - t \<subseteq> outside s"
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
    also have "... \<subseteq> outside(T \<union> U)"
      by (metis (mono_tags, lifting) Collect_mono mem_Collect_eq outside outside_same_component x)
    finally have "Y \<subseteq> outside(T \<union> U)" .
    with assms show ?thesis by auto
  qed
  with x show "x \<in> outside (T \<union> S)"
    by (simp add: outside_connected_component_lt connected_component_def) meson
qed

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
    by (metis (no_types) compl_sup double_compl inside_Un_outside)
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
        using \<open>s \<subseteq> t\<close> frontier_disjoint_eq t by auto
      { fix \<gamma>
        assume "path \<gamma>" and pimg_sbs: "path_image \<gamma> - {pathfinish \<gamma>} \<subseteq> interior (- t)"
           and pf: "pathfinish \<gamma> \<in> frontier t" and ps: "pathstart \<gamma> = a"
        define c where "c = pathfinish \<gamma>"
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
          using \<open>c \<in> - s\<close> \<open>s \<subseteq> t\<close> interior_subset apply (auto simp: c_def)
          done
        have "closed_segment c d \<le> cball c \<epsilon>"
          apply (simp add: segment_convex_hull)
          apply (rule hull_minimal)
          using  \<open>\<epsilon> > 0\<close> d apply (auto simp: dist_commute)
          done
        with \<epsilon> have "closed_segment c d \<subseteq> -s" by blast
        moreover have con_gcd: "connected (path_image \<gamma> \<union> closed_segment c d)"
          by (rule connected_Un) (auto simp: c_def \<open>path \<gamma>\<close> connected_path_image)
        ultimately have "connected_component (- s) a d"
          unfolding connected_component_def using pimg_sbs_cos ps by blast
        then have "outside s \<inter> t \<noteq> {}"
          using outside_same_component [OF _ a]  by (metis IntI \<open>d \<in> t\<close> empty_iff)
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
      using inside_outside_intersect_connected [OF \<open>connected t\<close>, of s]
      by (metis "2" compact_eq_bounded_closed coms connected_outside inf.commute inside_outside_intersect_connected outst)
    then show ?thesis
      using inside_inside [OF \<open>s \<subseteq> inside t\<close>] by blast
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

subsection\<open>Condition for an open map's image to contain a ball\<close>

lemma ball_subset_open_map_image:
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
    obtain w where w: "w \<in> frontier (f ` S)"
               and dw_le: "\<And>y. y \<in> frontier (f ` S) \<Longrightarrow> norm (f a - w) \<le> norm (f a - y)"
      apply (rule distance_attains_inf [of "frontier(f ` S)" "f a"])
      using \<open>a \<in> S\<close> by (auto simp: frontier_eq_empty dist_norm False)
    then obtain \<xi> where \<xi>: "\<And>n. \<xi> n \<in> f ` S" and tendsw: "\<xi> \<longlonglongrightarrow> w"
      by (metis Diff_iff frontier_def closure_sequential)
    then have "\<And>n. \<exists>x \<in> S. \<xi> n = f x" by force
    then obtain z where zs: "\<And>n. z n \<in> S" and fz: "\<And>n. \<xi> n = f (z n)"
      by metis
    then obtain y K where y: "y \<in> closure S" and "strict_mono (K :: nat \<Rightarrow> nat)" 
                      and Klim: "(z \<circ> K) \<longlonglongrightarrow> y"
      using \<open>bounded S\<close>
      apply (simp add: compact_closure [symmetric] compact_def)
      apply (drule_tac x=z in spec)
      using closure_subset apply force
      done
    then have ftendsw: "((\<lambda>n. f (z n)) \<circ> K) \<longlonglongrightarrow> w"
      by (metis LIMSEQ_subseq_LIMSEQ fun.map_cong0 fz tendsw)
    have zKs: "\<And>n. (z o K) n \<in> S" by (simp add: zs)
    have fz: "f \<circ> z = \<xi>"  "(\<lambda>n. f (z n)) = \<xi>"
      using fz by auto
    then have "(\<xi> \<circ> K) \<longlonglongrightarrow> f y"
      by (metis (no_types) Klim zKs y contf comp_assoc continuous_on_closure_sequentially)
    with fz have wy: "w = f y" using fz LIMSEQ_unique ftendsw by auto
    have rle: "r \<le> norm (f y - f a)"
      apply (rule le_no)
      using w wy oint
      by (force simp: imageI image_mono interiorI interior_subset frontier_def y)
    have **: "(~(b \<inter> (- S) = {}) \<and> ~(b - (- S) = {}) \<Longrightarrow> (b \<inter> f \<noteq> {}))
              \<Longrightarrow> (b \<inter> S \<noteq> {}) \<Longrightarrow> b \<inter> f = {} \<Longrightarrow>
              b \<subseteq> S" for b f and S :: "'b set"
      by blast
    show ?thesis
      apply (rule **)   (*such a horrible mess*)
      apply (rule connected_Int_frontier [where t = "f`S", OF connected_ball])
      using \<open>a \<in> S\<close> \<open>0 < r\<close>
      apply (auto simp: disjoint_iff_not_equal  dist_norm)
      by (metis dw_le norm_minus_commute not_less order_trans rle wy)
qed

section\<open> Homotopy of maps p,q : X=>Y with property P of all intermediate maps.\<close>

text\<open> We often just want to require that it fixes some subset, but to take in
  the case of a loop homotopy, it's convenient to have a general property P.\<close>

definition homotopic_with ::
  "[('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> bool, 'a set, 'b set, 'a \<Rightarrow> 'b, 'a \<Rightarrow> 'b] \<Rightarrow> bool"
where
 "homotopic_with P X Y p q \<equiv>
   (\<exists>h:: real \<times> 'a \<Rightarrow> 'b.
       continuous_on ({0..1} \<times> X) h \<and>
       h ` ({0..1} \<times> X) \<subseteq> Y \<and>
       (\<forall>x. h(0, x) = p x) \<and>
       (\<forall>x. h(1, x) = q x) \<and>
       (\<forall>t \<in> {0..1}. P(\<lambda>x. h(t, x))))"


text\<open> We often want to just localize the ending function equality or whatever.\<close>
proposition homotopic_with:
  fixes X :: "'a::topological_space set" and Y :: "'b::topological_space set"
  assumes "\<And>h k. (\<And>x. x \<in> X \<Longrightarrow> h x = k x) \<Longrightarrow> (P h \<longleftrightarrow> P k)"
  shows "homotopic_with P X Y p q \<longleftrightarrow>
           (\<exists>h :: real \<times> 'a \<Rightarrow> 'b.
              continuous_on ({0..1} \<times> X) h \<and>
              h ` ({0..1} \<times> X) \<subseteq> Y \<and>
              (\<forall>x \<in> X. h(0,x) = p x) \<and>
              (\<forall>x \<in> X. h(1,x) = q x) \<and>
              (\<forall>t \<in> {0..1}. P(\<lambda>x. h(t, x))))"
  unfolding homotopic_with_def
  apply (rule iffI, blast, clarify)
  apply (rule_tac x="\<lambda>(u,v). if v \<in> X then h(u,v) else if u = 0 then p v else q v" in exI)
  apply (auto simp:)
  apply (force elim: continuous_on_eq)
  apply (drule_tac x=t in bspec, force)
  apply (subst assms; simp)
  done

proposition homotopic_with_eq:
   assumes h: "homotopic_with P X Y f g"
       and f': "\<And>x. x \<in> X \<Longrightarrow> f' x = f x"
       and g': "\<And>x. x \<in> X \<Longrightarrow> g' x = g x"
       and P:  "(\<And>h k. (\<And>x. x \<in> X \<Longrightarrow> h x = k x) \<Longrightarrow> (P h \<longleftrightarrow> P k))"
   shows "homotopic_with P X Y f' g'"
  using h unfolding homotopic_with_def
  apply safe
  apply (rule_tac x="\<lambda>(u,v). if v \<in> X then h(u,v) else if u = 0 then f' v else g' v" in exI)
  apply (simp add: f' g', safe)
  apply (fastforce intro: continuous_on_eq)
  apply fastforce
  apply (subst P; fastforce)
  done

proposition homotopic_with_equal:
   assumes contf: "continuous_on X f" and fXY: "f ` X \<subseteq> Y"
       and gf: "\<And>x. x \<in> X \<Longrightarrow> g x = f x"
       and P:  "P f" "P g"
   shows "homotopic_with P X Y f g"
  unfolding homotopic_with_def
  apply (rule_tac x="\<lambda>(u,v). if u = 1 then g v else f v" in exI)
  using assms
  apply (intro conjI)
  apply (rule continuous_on_eq [where f = "f o snd"])
  apply (rule continuous_intros | force)+
  apply clarify
  apply (case_tac "t=1"; force)
  done


lemma image_Pair_const: "(\<lambda>x. (x, c)) ` A = A \<times> {c}"
  by (auto simp:)

lemma homotopic_constant_maps:
   "homotopic_with (\<lambda>x. True) s t (\<lambda>x. a) (\<lambda>x. b) \<longleftrightarrow> s = {} \<or> path_component t a b"
proof (cases "s = {} \<or> t = {}")
  case True with continuous_on_const show ?thesis
    by (auto simp: homotopic_with path_component_def)
next
  case False
  then obtain c where "c \<in> s" by blast
  show ?thesis
  proof
    assume "homotopic_with (\<lambda>x. True) s t (\<lambda>x. a) (\<lambda>x. b)"
    then obtain h :: "real \<times> 'a \<Rightarrow> 'b"
        where conth: "continuous_on ({0..1} \<times> s) h"
          and h: "h ` ({0..1} \<times> s) \<subseteq> t" "(\<forall>x\<in>s. h (0, x) = a)" "(\<forall>x\<in>s. h (1, x) = b)"
      by (auto simp: homotopic_with)
    have "continuous_on {0..1} (h \<circ> (\<lambda>t. (t, c)))"
      apply (rule continuous_intros conth | simp add: image_Pair_const)+
      apply (blast intro:  \<open>c \<in> s\<close> continuous_on_subset [OF conth] )
      done
    with \<open>c \<in> s\<close> h show "s = {} \<or> path_component t a b"
      apply (simp_all add: homotopic_with path_component_def)
      apply (auto simp:)
      apply (drule_tac x="h o (\<lambda>t. (t, c))" in spec)
      apply (auto simp: pathstart_def pathfinish_def path_image_def path_def)
      done
  next
    assume "s = {} \<or> path_component t a b"
    with False show "homotopic_with (\<lambda>x. True) s t (\<lambda>x. a) (\<lambda>x. b)"
      apply (clarsimp simp: homotopic_with path_component_def pathstart_def pathfinish_def path_image_def path_def)
      apply (rule_tac x="g o fst" in exI)
      apply (rule conjI continuous_intros | force)+
      done
  qed
qed


subsection\<open> Trivial properties.\<close>

lemma homotopic_with_imp_property: "homotopic_with P X Y f g \<Longrightarrow> P f \<and> P g"
  unfolding homotopic_with_def Ball_def
  apply clarify
  apply (frule_tac x=0 in spec)
  apply (drule_tac x=1 in spec)
  apply (auto simp:)
  done

lemma continuous_on_o_Pair: "\<lbrakk>continuous_on (T \<times> X) h; t \<in> T\<rbrakk> \<Longrightarrow> continuous_on X (h o Pair t)"
  by (fast intro: continuous_intros elim!: continuous_on_subset)

lemma homotopic_with_imp_continuous:
    assumes "homotopic_with P X Y f g"
    shows "continuous_on X f \<and> continuous_on X g"
proof -
  obtain h :: "real \<times> 'a \<Rightarrow> 'b"
    where conth: "continuous_on ({0..1} \<times> X) h"
      and h: "\<forall>x. h (0, x) = f x" "\<forall>x. h (1, x) = g x"
    using assms by (auto simp: homotopic_with_def)
  have *: "t \<in> {0..1} \<Longrightarrow> continuous_on X (h o (\<lambda>x. (t,x)))" for t
    by (rule continuous_intros continuous_on_subset [OF conth] | force)+
  show ?thesis
    using h *[of 0] *[of 1] by auto
qed

proposition homotopic_with_imp_subset1:
     "homotopic_with P X Y f g \<Longrightarrow> f ` X \<subseteq> Y"
  by (simp add: homotopic_with_def image_subset_iff) (metis atLeastAtMost_iff order_refl zero_le_one)

proposition homotopic_with_imp_subset2:
     "homotopic_with P X Y f g \<Longrightarrow> g ` X \<subseteq> Y"
  by (simp add: homotopic_with_def image_subset_iff) (metis atLeastAtMost_iff order_refl zero_le_one)

proposition homotopic_with_mono:
    assumes hom: "homotopic_with P X Y f g"
        and Q: "\<And>h. \<lbrakk>continuous_on X h; image h X \<subseteq> Y \<and> P h\<rbrakk> \<Longrightarrow> Q h"
      shows "homotopic_with Q X Y f g"
  using hom
  apply (simp add: homotopic_with_def)
  apply (erule ex_forward)
  apply (force simp: intro!: Q dest: continuous_on_o_Pair)
  done

proposition homotopic_with_subset_left:
     "\<lbrakk>homotopic_with P X Y f g; Z \<subseteq> X\<rbrakk> \<Longrightarrow> homotopic_with P Z Y f g"
  apply (simp add: homotopic_with_def)
  apply (fast elim!: continuous_on_subset ex_forward)
  done

proposition homotopic_with_subset_right:
     "\<lbrakk>homotopic_with P X Y f g; Y \<subseteq> Z\<rbrakk> \<Longrightarrow> homotopic_with P X Z f g"
  apply (simp add: homotopic_with_def)
  apply (fast elim!: continuous_on_subset ex_forward)
  done

proposition homotopic_with_compose_continuous_right:
    "\<lbrakk>homotopic_with (\<lambda>f. p (f \<circ> h)) X Y f g; continuous_on W h; h ` W \<subseteq> X\<rbrakk>
     \<Longrightarrow> homotopic_with p W Y (f o h) (g o h)"
  apply (clarsimp simp add: homotopic_with_def)
  apply (rename_tac k)
  apply (rule_tac x="k o (\<lambda>y. (fst y, h (snd y)))" in exI)
  apply (rule conjI continuous_intros continuous_on_compose [where f=snd and g=h, unfolded o_def] | simp)+
  apply (erule continuous_on_subset)
  apply (fastforce simp: o_def)+
  done

proposition homotopic_compose_continuous_right:
     "\<lbrakk>homotopic_with (\<lambda>f. True) X Y f g; continuous_on W h; h ` W \<subseteq> X\<rbrakk>
      \<Longrightarrow> homotopic_with (\<lambda>f. True) W Y (f o h) (g o h)"
  using homotopic_with_compose_continuous_right by fastforce

proposition homotopic_with_compose_continuous_left:
     "\<lbrakk>homotopic_with (\<lambda>f. p (h \<circ> f)) X Y f g; continuous_on Y h; h ` Y \<subseteq> Z\<rbrakk>
      \<Longrightarrow> homotopic_with p X Z (h o f) (h o g)"
  apply (clarsimp simp add: homotopic_with_def)
  apply (rename_tac k)
  apply (rule_tac x="h o k" in exI)
  apply (rule conjI continuous_intros continuous_on_compose [where f=snd and g=h, unfolded o_def] | simp)+
  apply (erule continuous_on_subset)
  apply (fastforce simp: o_def)+
  done

proposition homotopic_compose_continuous_left:
   "\<lbrakk>homotopic_with (\<lambda>_. True) X Y f g;
     continuous_on Y h; h ` Y \<subseteq> Z\<rbrakk>
    \<Longrightarrow> homotopic_with (\<lambda>f. True) X Z (h o f) (h o g)"
  using homotopic_with_compose_continuous_left by fastforce

proposition homotopic_with_Pair:
   assumes hom: "homotopic_with p s t f g" "homotopic_with p' s' t' f' g'"
       and q: "\<And>f g. \<lbrakk>p f; p' g\<rbrakk> \<Longrightarrow> q(\<lambda>(x,y). (f x, g y))"
     shows "homotopic_with q (s \<times> s') (t \<times> t')
                  (\<lambda>(x,y). (f x, f' y)) (\<lambda>(x,y). (g x, g' y))"
  using hom
  apply (clarsimp simp add: homotopic_with_def)
  apply (rename_tac k k')
  apply (rule_tac x="\<lambda>z. ((k o (\<lambda>x. (fst x, fst (snd x)))) z, (k' o (\<lambda>x. (fst x, snd (snd x)))) z)" in exI)
  apply (rule conjI continuous_intros | erule continuous_on_subset | clarsimp)+
  apply (auto intro!: q [unfolded case_prod_unfold])
  done

lemma homotopic_on_empty [simp]: "homotopic_with (\<lambda>x. True) {} t f g"
  by (metis continuous_on_def empty_iff homotopic_with_equal image_subset_iff)


text\<open>Homotopy with P is an equivalence relation (on continuous functions mapping X into Y that satisfy P,
     though this only affects reflexivity.\<close>


proposition homotopic_with_refl:
   "homotopic_with P X Y f f \<longleftrightarrow> continuous_on X f \<and> image f X \<subseteq> Y \<and> P f"
  apply (rule iffI)
  using homotopic_with_imp_continuous homotopic_with_imp_property homotopic_with_imp_subset2 apply blast
  apply (simp add: homotopic_with_def)
  apply (rule_tac x="f o snd" in exI)
  apply (rule conjI continuous_intros | force)+
  done

lemma homotopic_with_symD:
  fixes X :: "'a::real_normed_vector set"
    assumes "homotopic_with P X Y f g"
      shows "homotopic_with P X Y g f"
  using assms
  apply (clarsimp simp add: homotopic_with_def)
  apply (rename_tac h)
  apply (rule_tac x="h o (\<lambda>y. (1 - fst y, snd y))" in exI)
  apply (rule conjI continuous_intros | erule continuous_on_subset | force simp add: image_subset_iff)+
  done

proposition homotopic_with_sym:
    fixes X :: "'a::real_normed_vector set"
    shows "homotopic_with P X Y f g \<longleftrightarrow> homotopic_with P X Y g f"
  using homotopic_with_symD by blast

lemma split_01: "{0..1::real} = {0..1/2} \<union> {1/2..1}"
  by force

lemma split_01_prod: "{0..1::real} \<times> X = ({0..1/2} \<times> X) \<union> ({1/2..1} \<times> X)"
  by force

proposition homotopic_with_trans:
    fixes X :: "'a::real_normed_vector set"
    assumes "homotopic_with P X Y f g" and "homotopic_with P X Y g h"
      shows "homotopic_with P X Y f h"
proof -
  have clo1: "closedin (subtopology euclidean ({0..1/2} \<times> X \<union> {1/2..1} \<times> X)) ({0..1/2::real} \<times> X)"
    apply (simp add: closedin_closed split_01_prod [symmetric])
    apply (rule_tac x="{0..1/2} \<times> UNIV" in exI)
    apply (force simp add: closed_Times)
    done
  have clo2: "closedin (subtopology euclidean ({0..1/2} \<times> X \<union> {1/2..1} \<times> X)) ({1/2..1::real} \<times> X)"
    apply (simp add: closedin_closed split_01_prod [symmetric])
    apply (rule_tac x="{1/2..1} \<times> UNIV" in exI)
    apply (force simp add: closed_Times)
    done
  { fix k1 k2:: "real \<times> 'a \<Rightarrow> 'b"
    assume cont: "continuous_on ({0..1} \<times> X) k1" "continuous_on ({0..1} \<times> X) k2"
       and Y: "k1 ` ({0..1} \<times> X) \<subseteq> Y" "k2 ` ({0..1} \<times> X) \<subseteq> Y"
       and geq: "\<forall>x. k1 (1, x) = g x" "\<forall>x. k2 (0, x) = g x"
       and k12: "\<forall>x. k1 (0, x) = f x" "\<forall>x. k2 (1, x) = h x"
       and P:   "\<forall>t\<in>{0..1}. P (\<lambda>x. k1 (t, x))" "\<forall>t\<in>{0..1}. P (\<lambda>x. k2 (t, x))"
    define k where "k y =
      (if fst y \<le> 1 / 2
       then (k1 o (\<lambda>x. (2 *\<^sub>R fst x, snd x))) y
       else (k2 o (\<lambda>x. (2 *\<^sub>R fst x -1, snd x))) y)" for y
    have keq: "k1 (2 * u, v) = k2 (2 * u - 1, v)" if "u = 1/2"  for u v
      by (simp add: geq that)
    have "continuous_on ({0..1} \<times> X) k"
      using cont
      apply (simp add: split_01_prod k_def)
      apply (rule clo1 clo2 continuous_on_cases_local continuous_intros | erule continuous_on_subset | simp add: linear image_subset_iff)+
      apply (force simp add: keq)
      done
    moreover have "k ` ({0..1} \<times> X) \<subseteq> Y"
      using Y by (force simp add: k_def)
    moreover have "\<forall>x. k (0, x) = f x"
      by (simp add: k_def k12)
    moreover have "(\<forall>x. k (1, x) = h x)"
      by (simp add: k_def k12)
    moreover have "\<forall>t\<in>{0..1}. P (\<lambda>x. k (t, x))"
      using P
      apply (clarsimp simp add: k_def)
      apply (case_tac "t \<le> 1/2")
      apply (auto simp:)
      done
    ultimately have *: "\<exists>k :: real \<times> 'a \<Rightarrow> 'b.
                       continuous_on ({0..1} \<times> X) k \<and> k ` ({0..1} \<times> X) \<subseteq> Y \<and>
                       (\<forall>x. k (0, x) = f x) \<and> (\<forall>x. k (1, x) = h x) \<and> (\<forall>t\<in>{0..1}. P (\<lambda>x. k (t, x)))"
      by blast
  } note * = this
  show ?thesis
    using assms by (auto intro: * simp add: homotopic_with_def)
qed

proposition homotopic_compose:
      fixes s :: "'a::real_normed_vector set"
      shows "\<lbrakk>homotopic_with (\<lambda>x. True) s t f f'; homotopic_with (\<lambda>x. True) t u g g'\<rbrakk>
             \<Longrightarrow> homotopic_with (\<lambda>x. True) s u (g o f) (g' o f')"
  apply (rule homotopic_with_trans [where g = "g o f'"])
  apply (metis homotopic_compose_continuous_left homotopic_with_imp_continuous homotopic_with_imp_subset1)
  by (metis homotopic_compose_continuous_right homotopic_with_imp_continuous homotopic_with_imp_subset2)


text\<open>Homotopic triviality implicitly incorporates path-connectedness.\<close>
lemma homotopic_triviality:
  fixes S :: "'a::real_normed_vector set"
  shows  "(\<forall>f g. continuous_on S f \<and> f ` S \<subseteq> T \<and>
                 continuous_on S g \<and> g ` S \<subseteq> T
                 \<longrightarrow> homotopic_with (\<lambda>x. True) S T f g) \<longleftrightarrow>
          (S = {} \<or> path_connected T) \<and>
          (\<forall>f. continuous_on S f \<and> f ` S \<subseteq> T \<longrightarrow> (\<exists>c. homotopic_with (\<lambda>x. True) S T f (\<lambda>x. c)))"
          (is "?lhs = ?rhs")
proof (cases "S = {} \<or> T = {}")
  case True then show ?thesis by auto
next
  case False show ?thesis
  proof
    assume LHS [rule_format]: ?lhs
    have pab: "path_component T a b" if "a \<in> T" "b \<in> T" for a b
    proof -
      have "homotopic_with (\<lambda>x. True) S T (\<lambda>x. a) (\<lambda>x. b)"
        by (simp add: LHS continuous_on_const image_subset_iff that)
      then show ?thesis
        using False homotopic_constant_maps by blast
    qed
      moreover
    have "\<exists>c. homotopic_with (\<lambda>x. True) S T f (\<lambda>x. c)" if "continuous_on S f" "f ` S \<subseteq> T" for f
      by (metis (full_types) False LHS equals0I homotopic_constant_maps homotopic_with_imp_continuous homotopic_with_imp_subset2 pab that)
    ultimately show ?rhs
      by (simp add: path_connected_component)
  next
    assume RHS: ?rhs
    with False have T: "path_connected T"
      by blast
    show ?lhs
    proof clarify
      fix f g
      assume "continuous_on S f" "f ` S \<subseteq> T" "continuous_on S g" "g ` S \<subseteq> T"
      obtain c d where c: "homotopic_with (\<lambda>x. True) S T f (\<lambda>x. c)" and d: "homotopic_with (\<lambda>x. True) S T g (\<lambda>x. d)"
        using False \<open>continuous_on S f\<close> \<open>f ` S \<subseteq> T\<close>  RHS \<open>continuous_on S g\<close> \<open>g ` S \<subseteq> T\<close> by blast
      then have "c \<in> T" "d \<in> T"
        using False homotopic_with_imp_subset2 by fastforce+
      with T have "path_component T c d"
        using path_connected_component by blast
      then have "homotopic_with (\<lambda>x. True) S T (\<lambda>x. c) (\<lambda>x. d)"
        by (simp add: homotopic_constant_maps)
      with c d show "homotopic_with (\<lambda>x. True) S T f g"
        by (meson homotopic_with_symD homotopic_with_trans)
    qed
  qed
qed


subsection\<open>Homotopy of paths, maintaining the same endpoints.\<close>


definition homotopic_paths :: "['a set, real \<Rightarrow> 'a, real \<Rightarrow> 'a::topological_space] \<Rightarrow> bool"
  where
     "homotopic_paths s p q \<equiv>
       homotopic_with (\<lambda>r. pathstart r = pathstart p \<and> pathfinish r = pathfinish p) {0..1} s p q"

lemma homotopic_paths:
   "homotopic_paths s p q \<longleftrightarrow>
      (\<exists>h. continuous_on ({0..1} \<times> {0..1}) h \<and>
          h ` ({0..1} \<times> {0..1}) \<subseteq> s \<and>
          (\<forall>x \<in> {0..1}. h(0,x) = p x) \<and>
          (\<forall>x \<in> {0..1}. h(1,x) = q x) \<and>
          (\<forall>t \<in> {0..1::real}. pathstart(h o Pair t) = pathstart p \<and>
                        pathfinish(h o Pair t) = pathfinish p))"
  by (auto simp: homotopic_paths_def homotopic_with pathstart_def pathfinish_def)

proposition homotopic_paths_imp_pathstart:
     "homotopic_paths s p q \<Longrightarrow> pathstart p = pathstart q"
  by (metis (mono_tags, lifting) homotopic_paths_def homotopic_with_imp_property)

proposition homotopic_paths_imp_pathfinish:
     "homotopic_paths s p q \<Longrightarrow> pathfinish p = pathfinish q"
  by (metis (mono_tags, lifting) homotopic_paths_def homotopic_with_imp_property)

lemma homotopic_paths_imp_path:
     "homotopic_paths s p q \<Longrightarrow> path p \<and> path q"
  using homotopic_paths_def homotopic_with_imp_continuous path_def by blast

lemma homotopic_paths_imp_subset:
     "homotopic_paths s p q \<Longrightarrow> path_image p \<subseteq> s \<and> path_image q \<subseteq> s"
  by (simp add: homotopic_paths_def homotopic_with_imp_subset1 homotopic_with_imp_subset2 path_image_def)

proposition homotopic_paths_refl [simp]: "homotopic_paths s p p \<longleftrightarrow> path p \<and> path_image p \<subseteq> s"
by (simp add: homotopic_paths_def homotopic_with_refl path_def path_image_def)

proposition homotopic_paths_sym: "homotopic_paths s p q \<Longrightarrow> homotopic_paths s q p"
  by (metis (mono_tags) homotopic_paths_def homotopic_paths_imp_pathfinish homotopic_paths_imp_pathstart homotopic_with_symD)

proposition homotopic_paths_sym_eq: "homotopic_paths s p q \<longleftrightarrow> homotopic_paths s q p"
  by (metis homotopic_paths_sym)

proposition homotopic_paths_trans [trans]:
     "\<lbrakk>homotopic_paths s p q; homotopic_paths s q r\<rbrakk> \<Longrightarrow> homotopic_paths s p r"
  apply (simp add: homotopic_paths_def)
  apply (rule homotopic_with_trans, assumption)
  by (metis (mono_tags, lifting) homotopic_with_imp_property homotopic_with_mono)

proposition homotopic_paths_eq:
     "\<lbrakk>path p; path_image p \<subseteq> s; \<And>t. t \<in> {0..1} \<Longrightarrow> p t = q t\<rbrakk> \<Longrightarrow> homotopic_paths s p q"
  apply (simp add: homotopic_paths_def)
  apply (rule homotopic_with_eq)
  apply (auto simp: path_def homotopic_with_refl pathstart_def pathfinish_def path_image_def elim: continuous_on_eq)
  done

proposition homotopic_paths_reparametrize:
  assumes "path p"
      and pips: "path_image p \<subseteq> s"
      and contf: "continuous_on {0..1} f"
      and f01:"f ` {0..1} \<subseteq> {0..1}"
      and [simp]: "f(0) = 0" "f(1) = 1"
      and q: "\<And>t. t \<in> {0..1} \<Longrightarrow> q(t) = p(f t)"
    shows "homotopic_paths s p q"
proof -
  have contp: "continuous_on {0..1} p"
    by (metis \<open>path p\<close> path_def)
  then have "continuous_on {0..1} (p o f)"
    using contf continuous_on_compose continuous_on_subset f01 by blast
  then have "path q"
    by (simp add: path_def) (metis q continuous_on_cong)
  have piqs: "path_image q \<subseteq> s"
    by (metis (no_types, hide_lams) pips f01 image_subset_iff path_image_def q)
  have fb0: "\<And>a b. \<lbrakk>0 \<le> a; a \<le> 1; 0 \<le> b; b \<le> 1\<rbrakk> \<Longrightarrow> 0 \<le> (1 - a) * f b + a * b"
    using f01 by force
  have fb1: "\<lbrakk>0 \<le> a; a \<le> 1; 0 \<le> b; b \<le> 1\<rbrakk> \<Longrightarrow> (1 - a) * f b + a * b \<le> 1" for a b
    using f01 [THEN subsetD, of "f b"] by (simp add: convex_bound_le)
  have "homotopic_paths s q p"
  proof (rule homotopic_paths_trans)
    show "homotopic_paths s q (p \<circ> f)"
      using q by (force intro: homotopic_paths_eq [OF  \<open>path q\<close> piqs])
  next
    show "homotopic_paths s (p \<circ> f) p"
      apply (simp add: homotopic_paths_def homotopic_with_def)
      apply (rule_tac x="p o (\<lambda>y. (1 - (fst y)) *\<^sub>R ((f o snd) y) + (fst y) *\<^sub>R snd y)"  in exI)
      apply (rule conjI contf continuous_intros continuous_on_subset [OF contp] | simp)+
      using pips [unfolded path_image_def]
      apply (auto simp: fb0 fb1 pathstart_def pathfinish_def)
      done
  qed
  then show ?thesis
    by (simp add: homotopic_paths_sym)
qed

lemma homotopic_paths_subset: "\<lbrakk>homotopic_paths s p q; s \<subseteq> t\<rbrakk> \<Longrightarrow> homotopic_paths t p q"
  using homotopic_paths_def homotopic_with_subset_right by blast


text\<open> A slightly ad-hoc but useful lemma in constructing homotopies.\<close>
lemma homotopic_join_lemma:
  fixes q :: "[real,real] \<Rightarrow> 'a::topological_space"
  assumes p: "continuous_on ({0..1} \<times> {0..1}) (\<lambda>y. p (fst y) (snd y))"
      and q: "continuous_on ({0..1} \<times> {0..1}) (\<lambda>y. q (fst y) (snd y))"
      and pf: "\<And>t. t \<in> {0..1} \<Longrightarrow> pathfinish(p t) = pathstart(q t)"
    shows "continuous_on ({0..1} \<times> {0..1}) (\<lambda>y. (p(fst y) +++ q(fst y)) (snd y))"
proof -
  have 1: "(\<lambda>y. p (fst y) (2 * snd y)) = (\<lambda>y. p (fst y) (snd y)) o (\<lambda>y. (fst y, 2 * snd y))"
    by (rule ext) (simp )
  have 2: "(\<lambda>y. q (fst y) (2 * snd y - 1)) = (\<lambda>y. q (fst y) (snd y)) o (\<lambda>y. (fst y, 2 * snd y - 1))"
    by (rule ext) (simp )
  show ?thesis
    apply (simp add: joinpaths_def)
    apply (rule continuous_on_cases_le)
    apply (simp_all only: 1 2)
    apply (rule continuous_intros continuous_on_subset [OF p] continuous_on_subset [OF q] | force)+
    using pf
    apply (auto simp: mult.commute pathstart_def pathfinish_def)
    done
qed

text\<open> Congruence properties of homotopy w.r.t. path-combining operations.\<close>

lemma homotopic_paths_reversepath_D:
      assumes "homotopic_paths s p q"
      shows   "homotopic_paths s (reversepath p) (reversepath q)"
  using assms
  apply (simp add: homotopic_paths_def homotopic_with_def, clarify)
  apply (rule_tac x="h o (\<lambda>x. (fst x, 1 - snd x))" in exI)
  apply (rule conjI continuous_intros)+
  apply (auto simp: reversepath_def pathstart_def pathfinish_def elim!: continuous_on_subset)
  done

proposition homotopic_paths_reversepath:
     "homotopic_paths s (reversepath p) (reversepath q) \<longleftrightarrow> homotopic_paths s p q"
  using homotopic_paths_reversepath_D by force


proposition homotopic_paths_join:
    "\<lbrakk>homotopic_paths s p p'; homotopic_paths s q q'; pathfinish p = pathstart q\<rbrakk> \<Longrightarrow> homotopic_paths s (p +++ q) (p' +++ q')"
  apply (simp add: homotopic_paths_def homotopic_with_def, clarify)
  apply (rename_tac k1 k2)
  apply (rule_tac x="(\<lambda>y. ((k1 o Pair (fst y)) +++ (k2 o Pair (fst y))) (snd y))" in exI)
  apply (rule conjI continuous_intros homotopic_join_lemma)+
  apply (auto simp: joinpaths_def pathstart_def pathfinish_def path_image_def)
  done

proposition homotopic_paths_continuous_image:
    "\<lbrakk>homotopic_paths s f g; continuous_on s h; h ` s \<subseteq> t\<rbrakk> \<Longrightarrow> homotopic_paths t (h o f) (h o g)"
  unfolding homotopic_paths_def
  apply (rule homotopic_with_compose_continuous_left [of _ _ _ s])
  apply (auto simp: pathstart_def pathfinish_def elim!: homotopic_with_mono)
  done

subsection\<open>Group properties for homotopy of paths\<close>

text\<open>So taking equivalence classes under homotopy would give the fundamental group\<close>

proposition homotopic_paths_rid:
    "\<lbrakk>path p; path_image p \<subseteq> s\<rbrakk> \<Longrightarrow> homotopic_paths s (p +++ linepath (pathfinish p) (pathfinish p)) p"
  apply (subst homotopic_paths_sym)
  apply (rule homotopic_paths_reparametrize [where f = "\<lambda>t. if  t \<le> 1 / 2 then 2 *\<^sub>R t else 1"])
  apply (simp_all del: le_divide_eq_numeral1)
  apply (subst split_01)
  apply (rule continuous_on_cases continuous_intros | force simp: pathfinish_def joinpaths_def)+
  done

proposition homotopic_paths_lid:
   "\<lbrakk>path p; path_image p \<subseteq> s\<rbrakk> \<Longrightarrow> homotopic_paths s (linepath (pathstart p) (pathstart p) +++ p) p"
using homotopic_paths_rid [of "reversepath p" s]
  by (metis homotopic_paths_reversepath path_image_reversepath path_reversepath pathfinish_linepath
        pathfinish_reversepath reversepath_joinpaths reversepath_linepath)

proposition homotopic_paths_assoc:
   "\<lbrakk>path p; path_image p \<subseteq> s; path q; path_image q \<subseteq> s; path r; path_image r \<subseteq> s; pathfinish p = pathstart q;
     pathfinish q = pathstart r\<rbrakk>
    \<Longrightarrow> homotopic_paths s (p +++ (q +++ r)) ((p +++ q) +++ r)"
  apply (subst homotopic_paths_sym)
  apply (rule homotopic_paths_reparametrize
           [where f = "\<lambda>t. if  t \<le> 1 / 2 then inverse 2 *\<^sub>R t
                           else if  t \<le> 3 / 4 then t - (1 / 4)
                           else 2 *\<^sub>R t - 1"])
  apply (simp_all del: le_divide_eq_numeral1)
  apply (simp add: subset_path_image_join)
  apply (rule continuous_on_cases_1 continuous_intros)+
  apply (auto simp: joinpaths_def)
  done

proposition homotopic_paths_rinv:
  assumes "path p" "path_image p \<subseteq> s"
    shows "homotopic_paths s (p +++ reversepath p) (linepath (pathstart p) (pathstart p))"
proof -
  have "continuous_on ({0..1} \<times> {0..1}) (\<lambda>x. (subpath 0 (fst x) p +++ reversepath (subpath 0 (fst x) p)) (snd x))"
    using assms
    apply (simp add: joinpaths_def subpath_def reversepath_def path_def del: le_divide_eq_numeral1)
    apply (rule continuous_on_cases_le)
    apply (rule_tac [2] continuous_on_compose [of _ _ p, unfolded o_def])
    apply (rule continuous_on_compose [of _ _ p, unfolded o_def])
    apply (auto intro!: continuous_intros simp del: eq_divide_eq_numeral1)
    apply (force elim!: continuous_on_subset simp add: mult_le_one)+
    done
  then show ?thesis
    using assms
    apply (subst homotopic_paths_sym_eq)
    unfolding homotopic_paths_def homotopic_with_def
    apply (rule_tac x="(\<lambda>y. (subpath 0 (fst y) p +++ reversepath(subpath 0 (fst y) p)) (snd y))" in exI)
    apply (simp add: path_defs joinpaths_def subpath_def reversepath_def)
    apply (force simp: mult_le_one)
    done
qed

proposition homotopic_paths_linv:
  assumes "path p" "path_image p \<subseteq> s"
    shows "homotopic_paths s (reversepath p +++ p) (linepath (pathfinish p) (pathfinish p))"
using homotopic_paths_rinv [of "reversepath p" s] assms by simp


subsection\<open> Homotopy of loops without requiring preservation of endpoints.\<close>

definition homotopic_loops :: "'a::topological_space set \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool"  where
 "homotopic_loops s p q \<equiv>
     homotopic_with (\<lambda>r. pathfinish r = pathstart r) {0..1} s p q"

lemma homotopic_loops:
   "homotopic_loops s p q \<longleftrightarrow>
      (\<exists>h. continuous_on ({0..1::real} \<times> {0..1}) h \<and>
          image h ({0..1} \<times> {0..1}) \<subseteq> s \<and>
          (\<forall>x \<in> {0..1}. h(0,x) = p x) \<and>
          (\<forall>x \<in> {0..1}. h(1,x) = q x) \<and>
          (\<forall>t \<in> {0..1}. pathfinish(h o Pair t) = pathstart(h o Pair t)))"
  by (simp add: homotopic_loops_def pathstart_def pathfinish_def homotopic_with)

proposition homotopic_loops_imp_loop:
     "homotopic_loops s p q \<Longrightarrow> pathfinish p = pathstart p \<and> pathfinish q = pathstart q"
using homotopic_with_imp_property homotopic_loops_def by blast

proposition homotopic_loops_imp_path:
     "homotopic_loops s p q \<Longrightarrow> path p \<and> path q"
  unfolding homotopic_loops_def path_def
  using homotopic_with_imp_continuous by blast

proposition homotopic_loops_imp_subset:
     "homotopic_loops s p q \<Longrightarrow> path_image p \<subseteq> s \<and> path_image q \<subseteq> s"
  unfolding homotopic_loops_def path_image_def
  by (metis homotopic_with_imp_subset1 homotopic_with_imp_subset2)

proposition homotopic_loops_refl:
     "homotopic_loops s p p \<longleftrightarrow>
      path p \<and> path_image p \<subseteq> s \<and> pathfinish p = pathstart p"
  by (simp add: homotopic_loops_def homotopic_with_refl path_image_def path_def)

proposition homotopic_loops_sym: "homotopic_loops s p q \<Longrightarrow> homotopic_loops s q p"
  by (simp add: homotopic_loops_def homotopic_with_sym)

proposition homotopic_loops_sym_eq: "homotopic_loops s p q \<longleftrightarrow> homotopic_loops s q p"
  by (metis homotopic_loops_sym)

proposition homotopic_loops_trans:
   "\<lbrakk>homotopic_loops s p q; homotopic_loops s q r\<rbrakk> \<Longrightarrow> homotopic_loops s p r"
  unfolding homotopic_loops_def by (blast intro: homotopic_with_trans)

proposition homotopic_loops_subset:
   "\<lbrakk>homotopic_loops s p q; s \<subseteq> t\<rbrakk> \<Longrightarrow> homotopic_loops t p q"
  by (simp add: homotopic_loops_def homotopic_with_subset_right)

proposition homotopic_loops_eq:
   "\<lbrakk>path p; path_image p \<subseteq> s; pathfinish p = pathstart p; \<And>t. t \<in> {0..1} \<Longrightarrow> p(t) = q(t)\<rbrakk>
          \<Longrightarrow> homotopic_loops s p q"
  unfolding homotopic_loops_def
  apply (rule homotopic_with_eq)
  apply (rule homotopic_with_refl [where f = p, THEN iffD2])
  apply (simp_all add: path_image_def path_def pathstart_def pathfinish_def)
  done

proposition homotopic_loops_continuous_image:
   "\<lbrakk>homotopic_loops s f g; continuous_on s h; h ` s \<subseteq> t\<rbrakk> \<Longrightarrow> homotopic_loops t (h \<circ> f) (h \<circ> g)"
  unfolding homotopic_loops_def
  apply (rule homotopic_with_compose_continuous_left)
  apply (erule homotopic_with_mono)
  by (simp add: pathfinish_def pathstart_def)


subsection\<open>Relations between the two variants of homotopy\<close>

proposition homotopic_paths_imp_homotopic_loops:
    "\<lbrakk>homotopic_paths s p q; pathfinish p = pathstart p; pathfinish q = pathstart p\<rbrakk> \<Longrightarrow> homotopic_loops s p q"
  by (auto simp: homotopic_paths_def homotopic_loops_def intro: homotopic_with_mono)

proposition homotopic_loops_imp_homotopic_paths_null:
  assumes "homotopic_loops s p (linepath a a)"
    shows "homotopic_paths s p (linepath (pathstart p) (pathstart p))"
proof -
  have "path p" by (metis assms homotopic_loops_imp_path)
  have ploop: "pathfinish p = pathstart p" by (metis assms homotopic_loops_imp_loop)
  have pip: "path_image p \<subseteq> s" by (metis assms homotopic_loops_imp_subset)
  obtain h where conth: "continuous_on ({0..1::real} \<times> {0..1}) h"
             and hs: "h ` ({0..1} \<times> {0..1}) \<subseteq> s"
             and [simp]: "\<And>x. x \<in> {0..1} \<Longrightarrow> h(0,x) = p x"
             and [simp]: "\<And>x. x \<in> {0..1} \<Longrightarrow> h(1,x) = a"
             and ends: "\<And>t. t \<in> {0..1} \<Longrightarrow> pathfinish (h \<circ> Pair t) = pathstart (h \<circ> Pair t)"
    using assms by (auto simp: homotopic_loops homotopic_with)
  have conth0: "path (\<lambda>u. h (u, 0))"
    unfolding path_def
    apply (rule continuous_on_compose [of _ _ h, unfolded o_def])
    apply (force intro: continuous_intros continuous_on_subset [OF conth])+
    done
  have pih0: "path_image (\<lambda>u. h (u, 0)) \<subseteq> s"
    using hs by (force simp: path_image_def)
  have c1: "continuous_on ({0..1} \<times> {0..1}) (\<lambda>x. h (fst x * snd x, 0))"
    apply (rule continuous_on_compose [of _ _ h, unfolded o_def])
    apply (force simp: mult_le_one intro: continuous_intros continuous_on_subset [OF conth])+
    done
  have c2: "continuous_on ({0..1} \<times> {0..1}) (\<lambda>x. h (fst x - fst x * snd x, 0))"
    apply (rule continuous_on_compose [of _ _ h, unfolded o_def])
    apply (force simp: mult_left_le mult_le_one intro: continuous_intros continuous_on_subset [OF conth])+
    apply (rule continuous_on_subset [OF conth])
    apply (auto simp: algebra_simps add_increasing2 mult_left_le)
    done
  have [simp]: "\<And>t. \<lbrakk>0 \<le> t \<and> t \<le> 1\<rbrakk> \<Longrightarrow> h (t, 1) = h (t, 0)"
    using ends by (simp add: pathfinish_def pathstart_def)
  have adhoc_le: "c * 4 \<le> 1 + c * (d * 4)" if "\<not> d * 4 \<le> 3" "0 \<le> c" "c \<le> 1" for c d::real
  proof -
    have "c * 3 \<le> c * (d * 4)" using that less_eq_real_def by auto
    with \<open>c \<le> 1\<close> show ?thesis by fastforce
  qed
  have *: "\<And>p x. (path p \<and> path(reversepath p)) \<and>
                  (path_image p \<subseteq> s \<and> path_image(reversepath p) \<subseteq> s) \<and>
                  (pathfinish p = pathstart(linepath a a +++ reversepath p) \<and>
                   pathstart(reversepath p) = a) \<and> pathstart p = x
                  \<Longrightarrow> homotopic_paths s (p +++ linepath a a +++ reversepath p) (linepath x x)"
    by (metis homotopic_paths_lid homotopic_paths_join
              homotopic_paths_trans homotopic_paths_sym homotopic_paths_rinv)
  have 1: "homotopic_paths s p (p +++ linepath (pathfinish p) (pathfinish p))"
    using \<open>path p\<close> homotopic_paths_rid homotopic_paths_sym pip by blast
  moreover have "homotopic_paths s (p +++ linepath (pathfinish p) (pathfinish p))
                                   (linepath (pathstart p) (pathstart p) +++ p +++ linepath (pathfinish p) (pathfinish p))"
    apply (rule homotopic_paths_sym)
    using homotopic_paths_lid [of "p +++ linepath (pathfinish p) (pathfinish p)" s]
    by (metis 1 homotopic_paths_imp_path homotopic_paths_imp_pathstart homotopic_paths_imp_subset)
  moreover have "homotopic_paths s (linepath (pathstart p) (pathstart p) +++ p +++ linepath (pathfinish p) (pathfinish p))
                                   ((\<lambda>u. h (u, 0)) +++ linepath a a +++ reversepath (\<lambda>u. h (u, 0)))"
    apply (simp add: homotopic_paths_def homotopic_with_def)
    apply (rule_tac x="\<lambda>y. (subpath 0 (fst y) (\<lambda>u. h (u, 0)) +++ (\<lambda>u. h (Pair (fst y) u)) +++ subpath (fst y) 0 (\<lambda>u. h (u, 0))) (snd y)" in exI)
    apply (simp add: subpath_reversepath)
    apply (intro conjI homotopic_join_lemma)
    using ploop
    apply (simp_all add: path_defs joinpaths_def o_def subpath_def conth c1 c2)
    apply (force simp: algebra_simps mult_le_one mult_left_le intro: hs [THEN subsetD] adhoc_le)
    done
  moreover have "homotopic_paths s ((\<lambda>u. h (u, 0)) +++ linepath a a +++ reversepath (\<lambda>u. h (u, 0)))
                                   (linepath (pathstart p) (pathstart p))"
    apply (rule *)
    apply (simp add: pih0 pathstart_def pathfinish_def conth0)
    apply (simp add: reversepath_def joinpaths_def)
    done
  ultimately show ?thesis
    by (blast intro: homotopic_paths_trans)
qed

proposition homotopic_loops_conjugate:
  fixes s :: "'a::real_normed_vector set"
  assumes "path p" "path q" and pip: "path_image p \<subseteq> s" and piq: "path_image q \<subseteq> s"
      and papp: "pathfinish p = pathstart q" and qloop: "pathfinish q = pathstart q"
    shows "homotopic_loops s (p +++ q +++ reversepath p) q"
proof -
  have contp: "continuous_on {0..1} p"  using \<open>path p\<close> [unfolded path_def] by blast
  have contq: "continuous_on {0..1} q"  using \<open>path q\<close> [unfolded path_def] by blast
  have c1: "continuous_on ({0..1} \<times> {0..1}) (\<lambda>x. p ((1 - fst x) * snd x + fst x))"
    apply (rule continuous_on_compose [of _ _ p, unfolded o_def])
    apply (force simp: mult_le_one intro!: continuous_intros)
    apply (rule continuous_on_subset [OF contp])
    apply (auto simp: algebra_simps add_increasing2 mult_right_le_one_le sum_le_prod1)
    done
  have c2: "continuous_on ({0..1} \<times> {0..1}) (\<lambda>x. p ((fst x - 1) * snd x + 1))"
    apply (rule continuous_on_compose [of _ _ p, unfolded o_def])
    apply (force simp: mult_le_one intro!: continuous_intros)
    apply (rule continuous_on_subset [OF contp])
    apply (auto simp: algebra_simps add_increasing2 mult_left_le_one_le)
    done
  have ps1: "\<And>a b. \<lbrakk>b * 2 \<le> 1; 0 \<le> b; 0 \<le> a; a \<le> 1\<rbrakk> \<Longrightarrow> p ((1 - a) * (2 * b) + a) \<in> s"
    using sum_le_prod1
    by (force simp: algebra_simps add_increasing2 mult_left_le intro: pip [unfolded path_image_def, THEN subsetD])
  have ps2: "\<And>a b. \<lbrakk>\<not> 4 * b \<le> 3; b \<le> 1; 0 \<le> a; a \<le> 1\<rbrakk> \<Longrightarrow> p ((a - 1) * (4 * b - 3) + 1) \<in> s"
    apply (rule pip [unfolded path_image_def, THEN subsetD])
    apply (rule image_eqI, blast)
    apply (simp add: algebra_simps)
    by (metis add_mono_thms_linordered_semiring(1) affine_ineq linear mult.commute mult.left_neutral mult_right_mono not_le
              add.commute zero_le_numeral)
  have qs: "\<And>a b. \<lbrakk>4 * b \<le> 3; \<not> b * 2 \<le> 1\<rbrakk> \<Longrightarrow> q (4 * b - 2) \<in> s"
    using path_image_def piq by fastforce
  have "homotopic_loops s (p +++ q +++ reversepath p)
                          (linepath (pathstart q) (pathstart q) +++ q +++ linepath (pathstart q) (pathstart q))"
    apply (simp add: homotopic_loops_def homotopic_with_def)
    apply (rule_tac x="(\<lambda>y. (subpath (fst y) 1 p +++ q +++ subpath 1 (fst y) p) (snd y))" in exI)
    apply (simp add: subpath_refl subpath_reversepath)
    apply (intro conjI homotopic_join_lemma)
    using papp qloop
    apply (simp_all add: path_defs joinpaths_def o_def subpath_def c1 c2)
    apply (force simp: contq intro: continuous_on_compose [of _ _ q, unfolded o_def] continuous_on_id continuous_on_snd)
    apply (auto simp: ps1 ps2 qs)
    done
  moreover have "homotopic_loops s (linepath (pathstart q) (pathstart q) +++ q +++ linepath (pathstart q) (pathstart q)) q"
  proof -
    have "homotopic_paths s (linepath (pathfinish q) (pathfinish q) +++ q) q"
      using \<open>path q\<close> homotopic_paths_lid qloop piq by auto
    hence 1: "\<And>f. homotopic_paths s f q \<or> \<not> homotopic_paths s f (linepath (pathfinish q) (pathfinish q) +++ q)"
      using homotopic_paths_trans by blast
    hence "homotopic_paths s (linepath (pathfinish q) (pathfinish q) +++ q +++ linepath (pathfinish q) (pathfinish q)) q"
    proof -
      have "homotopic_paths s (q +++ linepath (pathfinish q) (pathfinish q)) q"
        by (simp add: \<open>path q\<close> homotopic_paths_rid piq)
      thus ?thesis
        by (metis (no_types) 1 \<open>path q\<close> homotopic_paths_join homotopic_paths_rinv homotopic_paths_sym
                  homotopic_paths_trans qloop pathfinish_linepath piq)
    qed
    thus ?thesis
      by (metis (no_types) qloop homotopic_loops_sym homotopic_paths_imp_homotopic_loops homotopic_paths_imp_pathfinish homotopic_paths_sym)
  qed
  ultimately show ?thesis
    by (blast intro: homotopic_loops_trans)
qed

lemma homotopic_paths_loop_parts:
  assumes loops: "homotopic_loops S (p +++ reversepath q) (linepath a a)" and "path q"
  shows "homotopic_paths S p q"
proof -
  have paths: "homotopic_paths S (p +++ reversepath q) (linepath (pathstart p) (pathstart p))"
    using homotopic_loops_imp_homotopic_paths_null [OF loops] by simp
  then have "path p"
    using \<open>path q\<close> homotopic_loops_imp_path loops path_join path_join_path_ends path_reversepath by blast
  show ?thesis
  proof (cases "pathfinish p = pathfinish q")
    case True
    have pipq: "path_image p \<subseteq> S" "path_image q \<subseteq> S"
      by (metis Un_subset_iff paths \<open>path p\<close> \<open>path q\<close> homotopic_loops_imp_subset homotopic_paths_imp_path loops
           path_image_join path_image_reversepath path_imp_reversepath path_join_eq)+
    have "homotopic_paths S p (p +++ (linepath (pathfinish p) (pathfinish p)))"
      using \<open>path p\<close> \<open>path_image p \<subseteq> S\<close> homotopic_paths_rid homotopic_paths_sym by blast
    moreover have "homotopic_paths S (p +++ (linepath (pathfinish p) (pathfinish p))) (p +++ (reversepath q +++ q))"
      by (simp add: True \<open>path p\<close> \<open>path q\<close> pipq homotopic_paths_join homotopic_paths_linv homotopic_paths_sym)
    moreover have "homotopic_paths S (p +++ (reversepath q +++ q)) ((p +++ reversepath q) +++ q)"
      by (simp add: True \<open>path p\<close> \<open>path q\<close> homotopic_paths_assoc pipq)
    moreover have "homotopic_paths S ((p +++ reversepath q) +++ q) (linepath (pathstart p) (pathstart p) +++ q)"
      by (simp add: \<open>path q\<close> homotopic_paths_join paths pipq)
    moreover then have "homotopic_paths S (linepath (pathstart p) (pathstart p) +++ q) q"
      by (metis \<open>path q\<close> homotopic_paths_imp_path homotopic_paths_lid linepath_trivial path_join_path_ends pathfinish_def pipq(2))
    ultimately show ?thesis
      using homotopic_paths_trans by metis
  next
    case False
    then show ?thesis
      using \<open>path q\<close> homotopic_loops_imp_path loops path_join_path_ends by fastforce
  qed
qed


subsection\<open> Homotopy of "nearby" function, paths and loops.\<close>

lemma homotopic_with_linear:
  fixes f g :: "_ \<Rightarrow> 'b::real_normed_vector"
  assumes contf: "continuous_on s f"
      and contg:"continuous_on s g"
      and sub: "\<And>x. x \<in> s \<Longrightarrow> closed_segment (f x) (g x) \<subseteq> t"
    shows "homotopic_with (\<lambda>z. True) s t f g"
  apply (simp add: homotopic_with_def)
  apply (rule_tac x="\<lambda>y. ((1 - (fst y)) *\<^sub>R f(snd y) + (fst y) *\<^sub>R g(snd y))" in exI)
  apply (intro conjI)
  apply (rule subset_refl continuous_intros continuous_on_subset [OF contf] continuous_on_compose2 [where g=f]
                                            continuous_on_subset [OF contg] continuous_on_compose2 [where g=g]| simp)+
  using sub closed_segment_def apply fastforce+
  done

lemma homotopic_paths_linear:
  fixes g h :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "path g" "path h" "pathstart h = pathstart g" "pathfinish h = pathfinish g"
          "\<And>t. t \<in> {0..1} \<Longrightarrow> closed_segment (g t) (h t) \<subseteq> s"
    shows "homotopic_paths s g h"
  using assms
  unfolding path_def
  apply (simp add: closed_segment_def pathstart_def pathfinish_def homotopic_paths_def homotopic_with_def)
  apply (rule_tac x="\<lambda>y. ((1 - (fst y)) *\<^sub>R (g o snd) y + (fst y) *\<^sub>R (h o snd) y)" in exI)
  apply (intro conjI subsetI continuous_intros; force)
  done

lemma homotopic_loops_linear:
  fixes g h :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "path g" "path h" "pathfinish g = pathstart g" "pathfinish h = pathstart h"
          "\<And>t x. t \<in> {0..1} \<Longrightarrow> closed_segment (g t) (h t) \<subseteq> s"
    shows "homotopic_loops s g h"
  using assms
  unfolding path_def
  apply (simp add: pathstart_def pathfinish_def homotopic_loops_def homotopic_with_def)
  apply (rule_tac x="\<lambda>y. ((1 - (fst y)) *\<^sub>R g(snd y) + (fst y) *\<^sub>R h(snd y))" in exI)
  apply (auto intro!: continuous_intros intro: continuous_on_compose2 [where g=g] continuous_on_compose2 [where g=h])
  apply (force simp: closed_segment_def)
  done

lemma homotopic_paths_nearby_explicit:
  assumes "path g" "path h" "pathstart h = pathstart g" "pathfinish h = pathfinish g"
      and no: "\<And>t x. \<lbrakk>t \<in> {0..1}; x \<notin> s\<rbrakk> \<Longrightarrow> norm(h t - g t) < norm(g t - x)"
    shows "homotopic_paths s g h"
  apply (rule homotopic_paths_linear [OF assms(1-4)])
  by (metis no segment_bound(1) subsetI norm_minus_commute not_le)

lemma homotopic_loops_nearby_explicit:
  assumes "path g" "path h" "pathfinish g = pathstart g" "pathfinish h = pathstart h"
      and no: "\<And>t x. \<lbrakk>t \<in> {0..1}; x \<notin> s\<rbrakk> \<Longrightarrow> norm(h t - g t) < norm(g t - x)"
    shows "homotopic_loops s g h"
  apply (rule homotopic_loops_linear [OF assms(1-4)])
  by (metis no segment_bound(1) subsetI norm_minus_commute not_le)

lemma homotopic_nearby_paths:
  fixes g h :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "path g" "open s" "path_image g \<subseteq> s"
    shows "\<exists>e. 0 < e \<and>
               (\<forall>h. path h \<and>
                    pathstart h = pathstart g \<and> pathfinish h = pathfinish g \<and>
                    (\<forall>t \<in> {0..1}. norm(h t - g t) < e) \<longrightarrow> homotopic_paths s g h)"
proof -
  obtain e where "e > 0" and e: "\<And>x y. x \<in> path_image g \<Longrightarrow> y \<in> - s \<Longrightarrow> e \<le> dist x y"
    using separate_compact_closed [of "path_image g" "-s"] assms by force
  show ?thesis
    apply (intro exI conjI)
    using e [unfolded dist_norm]
    apply (auto simp: intro!: homotopic_paths_nearby_explicit assms  \<open>e > 0\<close>)
    by (metis atLeastAtMost_iff imageI le_less_trans not_le path_image_def)
qed

lemma homotopic_nearby_loops:
  fixes g h :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "path g" "open s" "path_image g \<subseteq> s" "pathfinish g = pathstart g"
    shows "\<exists>e. 0 < e \<and>
               (\<forall>h. path h \<and> pathfinish h = pathstart h \<and>
                    (\<forall>t \<in> {0..1}. norm(h t - g t) < e) \<longrightarrow> homotopic_loops s g h)"
proof -
  obtain e where "e > 0" and e: "\<And>x y. x \<in> path_image g \<Longrightarrow> y \<in> - s \<Longrightarrow> e \<le> dist x y"
    using separate_compact_closed [of "path_image g" "-s"] assms by force
  show ?thesis
    apply (intro exI conjI)
    using e [unfolded dist_norm]
    apply (auto simp: intro!: homotopic_loops_nearby_explicit assms  \<open>e > 0\<close>)
    by (metis atLeastAtMost_iff imageI le_less_trans not_le path_image_def)
qed

subsection\<open> Homotopy and subpaths\<close>

lemma homotopic_join_subpaths1:
  assumes "path g" and pag: "path_image g \<subseteq> s"
      and u: "u \<in> {0..1}" and v: "v \<in> {0..1}" and w: "w \<in> {0..1}" "u \<le> v" "v \<le> w"
    shows "homotopic_paths s (subpath u v g +++ subpath v w g) (subpath u w g)"
proof -
  have 1: "t * 2 \<le> 1 \<Longrightarrow> u + t * (v * 2) \<le> v + t * (u * 2)" for t
    using affine_ineq \<open>u \<le> v\<close> by fastforce
  have 2: "t * 2 > 1 \<Longrightarrow> u + (2*t - 1) * v \<le> v + (2*t - 1) * w" for t
    by (metis add_mono_thms_linordered_semiring(1) diff_gt_0_iff_gt less_eq_real_def mult.commute mult_right_mono \<open>u \<le> v\<close> \<open>v \<le> w\<close>)
  have t2: "\<And>t::real. t*2 = 1 \<Longrightarrow> t = 1/2" by auto
  show ?thesis
    apply (rule homotopic_paths_subset [OF _ pag])
    using assms
    apply (cases "w = u")
    using homotopic_paths_rinv [of "subpath u v g" "path_image g"]
    apply (force simp: closed_segment_eq_real_ivl image_mono path_image_def subpath_refl)
      apply (rule homotopic_paths_sym)
      apply (rule homotopic_paths_reparametrize
             [where f = "\<lambda>t. if  t \<le> 1 / 2
                             then inverse((w - u)) *\<^sub>R (2 * (v - u)) *\<^sub>R t
                             else inverse((w - u)) *\<^sub>R ((v - u) + (w - v) *\<^sub>R (2 *\<^sub>R t - 1))"])
      using \<open>path g\<close> path_subpath u w apply blast
      using \<open>path g\<close> path_image_subpath_subset u w(1) apply blast
      apply simp_all
      apply (subst split_01)
      apply (rule continuous_on_cases continuous_intros | force simp: pathfinish_def joinpaths_def)+
      apply (simp_all add: field_simps not_le)
      apply (force dest!: t2)
      apply (force simp: algebra_simps mult_left_mono affine_ineq dest!: 1 2)
      apply (simp add: joinpaths_def subpath_def)
      apply (force simp: algebra_simps)
      done
qed

lemma homotopic_join_subpaths2:
  assumes "homotopic_paths s (subpath u v g +++ subpath v w g) (subpath u w g)"
    shows "homotopic_paths s (subpath w v g +++ subpath v u g) (subpath w u g)"
by (metis assms homotopic_paths_reversepath_D pathfinish_subpath pathstart_subpath reversepath_joinpaths reversepath_subpath)

lemma homotopic_join_subpaths3:
  assumes hom: "homotopic_paths s (subpath u v g +++ subpath v w g) (subpath u w g)"
      and "path g" and pag: "path_image g \<subseteq> s"
      and u: "u \<in> {0..1}" and v: "v \<in> {0..1}" and w: "w \<in> {0..1}"
    shows "homotopic_paths s (subpath v w g +++ subpath w u g) (subpath v u g)"
proof -
  have "homotopic_paths s (subpath u w g +++ subpath w v g) ((subpath u v g +++ subpath v w g) +++ subpath w v g)"
    apply (rule homotopic_paths_join)
    using hom homotopic_paths_sym_eq apply blast
    apply (metis \<open>path g\<close> homotopic_paths_eq pag path_image_subpath_subset path_subpath subset_trans v w)
    apply (simp add:)
    done
  also have "homotopic_paths s ((subpath u v g +++ subpath v w g) +++ subpath w v g) (subpath u v g +++ subpath v w g +++ subpath w v g)"
    apply (rule homotopic_paths_sym [OF homotopic_paths_assoc])
    using assms by (simp_all add: path_image_subpath_subset [THEN order_trans])
  also have "homotopic_paths s (subpath u v g +++ subpath v w g +++ subpath w v g)
                               (subpath u v g +++ linepath (pathfinish (subpath u v g)) (pathfinish (subpath u v g)))"
    apply (rule homotopic_paths_join)
    apply (metis \<open>path g\<close> homotopic_paths_eq order.trans pag path_image_subpath_subset path_subpath u v)
    apply (metis (no_types, lifting) \<open>path g\<close> homotopic_paths_linv order_trans pag path_image_subpath_subset path_subpath pathfinish_subpath reversepath_subpath v w)
    apply (simp add:)
    done
  also have "homotopic_paths s (subpath u v g +++ linepath (pathfinish (subpath u v g)) (pathfinish (subpath u v g))) (subpath u v g)"
    apply (rule homotopic_paths_rid)
    using \<open>path g\<close> path_subpath u v apply blast
    apply (meson \<open>path g\<close> order.trans pag path_image_subpath_subset u v)
    done
  finally have "homotopic_paths s (subpath u w g +++ subpath w v g) (subpath u v g)" .
  then show ?thesis
    using homotopic_join_subpaths2 by blast
qed

proposition homotopic_join_subpaths:
   "\<lbrakk>path g; path_image g \<subseteq> s; u \<in> {0..1}; v \<in> {0..1}; w \<in> {0..1}\<rbrakk>
    \<Longrightarrow> homotopic_paths s (subpath u v g +++ subpath v w g) (subpath u w g)"
apply (rule le_cases3 [of u v w])
using homotopic_join_subpaths1 homotopic_join_subpaths2 homotopic_join_subpaths3 by metis+

text\<open>Relating homotopy of trivial loops to path-connectedness.\<close>

lemma path_component_imp_homotopic_points:
    "path_component S a b \<Longrightarrow> homotopic_loops S (linepath a a) (linepath b b)"
apply (simp add: path_component_def homotopic_loops_def homotopic_with_def
                 pathstart_def pathfinish_def path_image_def path_def, clarify)
apply (rule_tac x="g o fst" in exI)
apply (intro conjI continuous_intros continuous_on_compose)+
apply (auto elim!: continuous_on_subset)
done

lemma homotopic_loops_imp_path_component_value:
   "\<lbrakk>homotopic_loops S p q; 0 \<le> t; t \<le> 1\<rbrakk>
        \<Longrightarrow> path_component S (p t) (q t)"
apply (simp add: path_component_def homotopic_loops_def homotopic_with_def
                 pathstart_def pathfinish_def path_image_def path_def, clarify)
apply (rule_tac x="h o (\<lambda>u. (u, t))" in exI)
apply (intro conjI continuous_intros continuous_on_compose)+
apply (auto elim!: continuous_on_subset)
done

lemma homotopic_points_eq_path_component:
   "homotopic_loops S (linepath a a) (linepath b b) \<longleftrightarrow>
        path_component S a b"
by (auto simp: path_component_imp_homotopic_points
         dest: homotopic_loops_imp_path_component_value [where t=1])

lemma path_connected_eq_homotopic_points:
    "path_connected S \<longleftrightarrow>
      (\<forall>a b. a \<in> S \<and> b \<in> S \<longrightarrow> homotopic_loops S (linepath a a) (linepath b b))"
by (auto simp: path_connected_def path_component_def homotopic_points_eq_path_component)


subsection\<open>Simply connected sets\<close>

text\<open>defined as "all loops are homotopic (as loops)\<close>

definition simply_connected where
  "simply_connected S \<equiv>
        \<forall>p q. path p \<and> pathfinish p = pathstart p \<and> path_image p \<subseteq> S \<and>
              path q \<and> pathfinish q = pathstart q \<and> path_image q \<subseteq> S
              \<longrightarrow> homotopic_loops S p q"

lemma simply_connected_empty [iff]: "simply_connected {}"
  by (simp add: simply_connected_def)

lemma simply_connected_imp_path_connected:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<Longrightarrow> path_connected S"
by (simp add: simply_connected_def path_connected_eq_homotopic_points)

lemma simply_connected_imp_connected:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<Longrightarrow> connected S"
by (simp add: path_connected_imp_connected simply_connected_imp_path_connected)

lemma simply_connected_eq_contractible_loop_any:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
            (\<forall>p a. path p \<and> path_image p \<subseteq> S \<and>
                  pathfinish p = pathstart p \<and> a \<in> S
                  \<longrightarrow> homotopic_loops S p (linepath a a))"
apply (simp add: simply_connected_def)
apply (rule iffI, force, clarify)
apply (rule_tac q = "linepath (pathstart p) (pathstart p)" in homotopic_loops_trans)
apply (fastforce simp add:)
using homotopic_loops_sym apply blast
done

lemma simply_connected_eq_contractible_loop_some:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
                path_connected S \<and>
                (\<forall>p. path p \<and> path_image p \<subseteq> S \<and> pathfinish p = pathstart p
                    \<longrightarrow> (\<exists>a. a \<in> S \<and> homotopic_loops S p (linepath a a)))"
apply (rule iffI)
 apply (fastforce simp: simply_connected_imp_path_connected simply_connected_eq_contractible_loop_any)
apply (clarsimp simp add: simply_connected_eq_contractible_loop_any)
apply (drule_tac x=p in spec)
using homotopic_loops_trans path_connected_eq_homotopic_points
  apply blast
done

lemma simply_connected_eq_contractible_loop_all:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
         S = {} \<or>
         (\<exists>a \<in> S. \<forall>p. path p \<and> path_image p \<subseteq> S \<and> pathfinish p = pathstart p
                \<longrightarrow> homotopic_loops S p (linepath a a))"
        (is "?lhs = ?rhs")
proof (cases "S = {}")
  case True then show ?thesis by force
next
  case False
  then obtain a where "a \<in> S" by blast
  show ?thesis
  proof
    assume "simply_connected S"
    then show ?rhs
      using \<open>a \<in> S\<close> \<open>simply_connected S\<close> simply_connected_eq_contractible_loop_any
      by blast
  next
    assume ?rhs
    then show "simply_connected S"
      apply (simp add: simply_connected_eq_contractible_loop_any False)
      by (meson homotopic_loops_refl homotopic_loops_sym homotopic_loops_trans
             path_component_imp_homotopic_points path_component_refl)
  qed
qed

lemma simply_connected_eq_contractible_path:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
           path_connected S \<and>
           (\<forall>p. path p \<and> path_image p \<subseteq> S \<and> pathfinish p = pathstart p
            \<longrightarrow> homotopic_paths S p (linepath (pathstart p) (pathstart p)))"
apply (rule iffI)
 apply (simp add: simply_connected_imp_path_connected)
 apply (metis simply_connected_eq_contractible_loop_some homotopic_loops_imp_homotopic_paths_null)
by (meson homotopic_paths_imp_homotopic_loops pathfinish_linepath pathstart_in_path_image
         simply_connected_eq_contractible_loop_some subset_iff)

lemma simply_connected_eq_homotopic_paths:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
          path_connected S \<and>
          (\<forall>p q. path p \<and> path_image p \<subseteq> S \<and>
                path q \<and> path_image q \<subseteq> S \<and>
                pathstart q = pathstart p \<and> pathfinish q = pathfinish p
                \<longrightarrow> homotopic_paths S p q)"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have pc: "path_connected S"
        and *:  "\<And>p. \<lbrakk>path p; path_image p \<subseteq> S;
                       pathfinish p = pathstart p\<rbrakk>
                      \<Longrightarrow> homotopic_paths S p (linepath (pathstart p) (pathstart p))"
    by (auto simp: simply_connected_eq_contractible_path)
  have "homotopic_paths S p q"
        if "path p" "path_image p \<subseteq> S" "path q"
           "path_image q \<subseteq> S" "pathstart q = pathstart p"
           "pathfinish q = pathfinish p" for p q
  proof -
    have "homotopic_paths S p (p +++ linepath (pathfinish p) (pathfinish p))"
      by (simp add: homotopic_paths_rid homotopic_paths_sym that)
    also have "homotopic_paths S (p +++ linepath (pathfinish p) (pathfinish p))
                                 (p +++ reversepath q +++ q)"
      using that
      by (metis homotopic_paths_join homotopic_paths_linv homotopic_paths_refl homotopic_paths_sym_eq pathstart_linepath)
    also have "homotopic_paths S (p +++ reversepath q +++ q)
                                 ((p +++ reversepath q) +++ q)"
      by (simp add: that homotopic_paths_assoc)
    also have "homotopic_paths S ((p +++ reversepath q) +++ q)
                                 (linepath (pathstart q) (pathstart q) +++ q)"
      using * [of "p +++ reversepath q"] that
      by (simp add: homotopic_paths_join path_image_join)
    also have "homotopic_paths S (linepath (pathstart q) (pathstart q) +++ q) q"
      using that homotopic_paths_lid by blast
    finally show ?thesis .
  qed
  then show ?rhs
    by (blast intro: pc *)
next
  assume ?rhs
  then show ?lhs
    by (force simp: simply_connected_eq_contractible_path)
qed

proposition simply_connected_Times:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  assumes S: "simply_connected S" and T: "simply_connected T"
    shows "simply_connected(S \<times> T)"
proof -
  have "homotopic_loops (S \<times> T) p (linepath (a, b) (a, b))"
       if "path p" "path_image p \<subseteq> S \<times> T" "p 1 = p 0" "a \<in> S" "b \<in> T"
       for p a b
  proof -
    have "path (fst \<circ> p)"
      apply (rule Path_Connected.path_continuous_image [OF \<open>path p\<close>])
      apply (rule continuous_intros)+
      done
    moreover have "path_image (fst \<circ> p) \<subseteq> S"
      using that apply (simp add: path_image_def) by force
    ultimately have p1: "homotopic_loops S (fst o p) (linepath a a)"
      using S that
      apply (simp add: simply_connected_eq_contractible_loop_any)
      apply (drule_tac x="fst o p" in spec)
      apply (drule_tac x=a in spec)
      apply (auto simp: pathstart_def pathfinish_def)
      done
    have "path (snd \<circ> p)"
      apply (rule Path_Connected.path_continuous_image [OF \<open>path p\<close>])
      apply (rule continuous_intros)+
      done
    moreover have "path_image (snd \<circ> p) \<subseteq> T"
      using that apply (simp add: path_image_def) by force
    ultimately have p2: "homotopic_loops T (snd o p) (linepath b b)"
      using T that
      apply (simp add: simply_connected_eq_contractible_loop_any)
      apply (drule_tac x="snd o p" in spec)
      apply (drule_tac x=b in spec)
      apply (auto simp: pathstart_def pathfinish_def)
      done
    show ?thesis
      using p1 p2
      apply (simp add: homotopic_loops, clarify)
      apply (rename_tac h k)
      apply (rule_tac x="\<lambda>z. Pair (h z) (k z)" in exI)
      apply (intro conjI continuous_intros | assumption)+
      apply (auto simp: pathstart_def pathfinish_def)
      done
  qed
  with assms show ?thesis
    by (simp add: simply_connected_eq_contractible_loop_any pathfinish_def pathstart_def)
qed


subsection\<open>Contractible sets\<close>

definition contractible where
 "contractible S \<equiv> \<exists>a. homotopic_with (\<lambda>x. True) S S id (\<lambda>x. a)"

proposition contractible_imp_simply_connected:
  fixes S :: "_::real_normed_vector set"
  assumes "contractible S" shows "simply_connected S"
proof (cases "S = {}")
  case True then show ?thesis by force
next
  case False
  obtain a where a: "homotopic_with (\<lambda>x. True) S S id (\<lambda>x. a)"
    using assms by (force simp add: contractible_def)
  then have "a \<in> S"
    by (metis False homotopic_constant_maps homotopic_with_symD homotopic_with_trans path_component_mem(2))
  show ?thesis
    apply (simp add: simply_connected_eq_contractible_loop_all False)
    apply (rule bexI [OF _ \<open>a \<in> S\<close>])
    using a apply (simp add: homotopic_loops_def homotopic_with_def path_def path_image_def pathfinish_def pathstart_def)
    apply clarify
    apply (rule_tac x="(h o (\<lambda>y. (fst y, (p \<circ> snd) y)))" in exI)
    apply (intro conjI continuous_on_compose continuous_intros)
    apply (erule continuous_on_subset | force)+
    done
qed

corollary contractible_imp_connected:
  fixes S :: "_::real_normed_vector set"
  shows "contractible S \<Longrightarrow> connected S"
by (simp add: contractible_imp_simply_connected simply_connected_imp_connected)

lemma contractible_imp_path_connected:
  fixes S :: "_::real_normed_vector set"
  shows "contractible S \<Longrightarrow> path_connected S"
by (simp add: contractible_imp_simply_connected simply_connected_imp_path_connected)

lemma nullhomotopic_through_contractible:
  fixes S :: "_::topological_space set"
  assumes f: "continuous_on S f" "f ` S \<subseteq> T"
      and g: "continuous_on T g" "g ` T \<subseteq> U"
      and T: "contractible T"
    obtains c where "homotopic_with (\<lambda>h. True) S U (g o f) (\<lambda>x. c)"
proof -
  obtain b where b: "homotopic_with (\<lambda>x. True) T T id (\<lambda>x. b)"
    using assms by (force simp add: contractible_def)
  have "homotopic_with (\<lambda>f. True) T U (g \<circ> id) (g \<circ> (\<lambda>x. b))"
    by (rule homotopic_compose_continuous_left [OF b g])
  then have "homotopic_with (\<lambda>f. True) S U (g \<circ> id \<circ> f) (g \<circ> (\<lambda>x. b) \<circ> f)"
    by (rule homotopic_compose_continuous_right [OF _ f])
  then show ?thesis
    by (simp add: comp_def that)
qed

lemma nullhomotopic_into_contractible:
  assumes f: "continuous_on S f" "f ` S \<subseteq> T"
      and T: "contractible T"
    obtains c where "homotopic_with (\<lambda>h. True) S T f (\<lambda>x. c)"
apply (rule nullhomotopic_through_contractible [OF f, of id T])
using assms
apply (auto simp: continuous_on_id)
done

lemma nullhomotopic_from_contractible:
  assumes f: "continuous_on S f" "f ` S \<subseteq> T"
      and S: "contractible S"
    obtains c where "homotopic_with (\<lambda>h. True) S T f (\<lambda>x. c)"
apply (rule nullhomotopic_through_contractible [OF continuous_on_id _ f S, of S])
using assms
apply (auto simp: comp_def)
done

lemma homotopic_through_contractible:
  fixes S :: "_::real_normed_vector set"
  assumes "continuous_on S f1" "f1 ` S \<subseteq> T"
          "continuous_on T g1" "g1 ` T \<subseteq> U"
          "continuous_on S f2" "f2 ` S \<subseteq> T"
          "continuous_on T g2" "g2 ` T \<subseteq> U"
          "contractible T" "path_connected U"
   shows "homotopic_with (\<lambda>h. True) S U (g1 o f1) (g2 o f2)"
proof -
  obtain c1 where c1: "homotopic_with (\<lambda>h. True) S U (g1 o f1) (\<lambda>x. c1)"
    apply (rule nullhomotopic_through_contractible [of S f1 T g1 U])
    using assms apply (auto simp: )
    done
  obtain c2 where c2: "homotopic_with (\<lambda>h. True) S U (g2 o f2) (\<lambda>x. c2)"
    apply (rule nullhomotopic_through_contractible [of S f2 T g2 U])
    using assms apply (auto simp: )
    done
  have *: "S = {} \<or> (\<exists>t. path_connected t \<and> t \<subseteq> U \<and> c2 \<in> t \<and> c1 \<in> t)"
  proof (cases "S = {}")
    case True then show ?thesis by force
  next
    case False
    with c1 c2 have "c1 \<in> U" "c2 \<in> U"
      using homotopic_with_imp_subset2 all_not_in_conv image_subset_iff by blast+
    with \<open>path_connected U\<close> show ?thesis by blast
  qed
  show ?thesis
    apply (rule homotopic_with_trans [OF c1])
    apply (rule homotopic_with_symD)
    apply (rule homotopic_with_trans [OF c2])
    apply (simp add: path_component homotopic_constant_maps *)
    done
qed

lemma homotopic_into_contractible:
  fixes S :: "'a::real_normed_vector set" and T:: "'b::real_normed_vector set"
  assumes f: "continuous_on S f" "f ` S \<subseteq> T"
      and g: "continuous_on S g" "g ` S \<subseteq> T"
      and T: "contractible T"
    shows "homotopic_with (\<lambda>h. True) S T f g"
using homotopic_through_contractible [of S f T id T g id]
by (simp add: assms contractible_imp_path_connected continuous_on_id)

lemma homotopic_from_contractible:
  fixes S :: "'a::real_normed_vector set" and T:: "'b::real_normed_vector set"
  assumes f: "continuous_on S f" "f ` S \<subseteq> T"
      and g: "continuous_on S g" "g ` S \<subseteq> T"
      and "contractible S" "path_connected T"
    shows "homotopic_with (\<lambda>h. True) S T f g"
using homotopic_through_contractible [of S id S f T id g]
by (simp add: assms contractible_imp_path_connected continuous_on_id)

lemma starlike_imp_contractible_gen:
  fixes S :: "'a::real_normed_vector set"
  assumes S: "starlike S"
      and P: "\<And>a T. \<lbrakk>a \<in> S; 0 \<le> T; T \<le> 1\<rbrakk> \<Longrightarrow> P(\<lambda>x. (1 - T) *\<^sub>R x + T *\<^sub>R a)"
    obtains a where "homotopic_with P S S (\<lambda>x. x) (\<lambda>x. a)"
proof -
  obtain a where "a \<in> S" and a: "\<And>x. x \<in> S \<Longrightarrow> closed_segment a x \<subseteq> S"
    using S by (auto simp add: starlike_def)
  have "(\<lambda>y. (1 - fst y) *\<^sub>R snd y + fst y *\<^sub>R a) ` ({0..1} \<times> S) \<subseteq> S"
    apply clarify
    apply (erule a [unfolded closed_segment_def, THEN subsetD])
    apply (simp add: )
    apply (metis add_diff_cancel_right' diff_ge_0_iff_ge le_add_diff_inverse pth_c(1))
    done
  then show ?thesis
    apply (rule_tac a="a" in that)
    using \<open>a \<in> S\<close>
    apply (simp add: homotopic_with_def)
    apply (rule_tac x="\<lambda>y. (1 - (fst y)) *\<^sub>R snd y + (fst y) *\<^sub>R a" in exI)
    apply (intro conjI ballI continuous_on_compose continuous_intros)
    apply (simp_all add: P)
    done
qed

lemma starlike_imp_contractible:
  fixes S :: "'a::real_normed_vector set"
  shows "starlike S \<Longrightarrow> contractible S"
using starlike_imp_contractible_gen contractible_def by (fastforce simp: id_def)

lemma contractible_UNIV [simp]: "contractible (UNIV :: 'a::real_normed_vector set)"
  by (simp add: starlike_imp_contractible)

lemma starlike_imp_simply_connected:
  fixes S :: "'a::real_normed_vector set"
  shows "starlike S \<Longrightarrow> simply_connected S"
by (simp add: contractible_imp_simply_connected starlike_imp_contractible)

lemma convex_imp_simply_connected:
  fixes S :: "'a::real_normed_vector set"
  shows "convex S \<Longrightarrow> simply_connected S"
using convex_imp_starlike starlike_imp_simply_connected by blast

lemma starlike_imp_path_connected:
  fixes S :: "'a::real_normed_vector set"
  shows "starlike S \<Longrightarrow> path_connected S"
by (simp add: simply_connected_imp_path_connected starlike_imp_simply_connected)

lemma starlike_imp_connected:
  fixes S :: "'a::real_normed_vector set"
  shows "starlike S \<Longrightarrow> connected S"
by (simp add: path_connected_imp_connected starlike_imp_path_connected)

lemma is_interval_simply_connected_1:
  fixes S :: "real set"
  shows "is_interval S \<longleftrightarrow> simply_connected S"
using convex_imp_simply_connected is_interval_convex_1 is_interval_path_connected_1 simply_connected_imp_path_connected by auto

lemma contractible_empty [simp]: "contractible {}"
  by (simp add: contractible_def homotopic_with)

lemma contractible_convex_tweak_boundary_points:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" and TS: "rel_interior S \<subseteq> T" "T \<subseteq> closure S"
  shows "contractible T"
proof (cases "S = {}")
  case True
  with assms show ?thesis
    by (simp add: subsetCE)
next
  case False
  show ?thesis
    apply (rule starlike_imp_contractible)
    apply (rule starlike_convex_tweak_boundary_points [OF \<open>convex S\<close> False TS])
    done
qed

lemma convex_imp_contractible:
  fixes S :: "'a::real_normed_vector set"
  shows "convex S \<Longrightarrow> contractible S"
  using contractible_empty convex_imp_starlike starlike_imp_contractible by blast

lemma contractible_sing [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "contractible {a}"
by (rule convex_imp_contractible [OF convex_singleton])

lemma is_interval_contractible_1:
  fixes S :: "real set"
  shows  "is_interval S \<longleftrightarrow> contractible S"
using contractible_imp_simply_connected convex_imp_contractible is_interval_convex_1
      is_interval_simply_connected_1 by auto

lemma contractible_Times:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes S: "contractible S" and T: "contractible T"
  shows "contractible (S \<times> T)"
proof -
  obtain a h where conth: "continuous_on ({0..1} \<times> S) h"
             and hsub: "h ` ({0..1} \<times> S) \<subseteq> S"
             and [simp]: "\<And>x. x \<in> S \<Longrightarrow> h (0, x) = x"
             and [simp]: "\<And>x. x \<in> S \<Longrightarrow>  h (1::real, x) = a"
    using S by (auto simp add: contractible_def homotopic_with)
  obtain b k where contk: "continuous_on ({0..1} \<times> T) k"
             and ksub: "k ` ({0..1} \<times> T) \<subseteq> T"
             and [simp]: "\<And>x. x \<in> T \<Longrightarrow> k (0, x) = x"
             and [simp]: "\<And>x. x \<in> T \<Longrightarrow>  k (1::real, x) = b"
    using T by (auto simp add: contractible_def homotopic_with)
  show ?thesis
    apply (simp add: contractible_def homotopic_with)
    apply (rule exI [where x=a])
    apply (rule exI [where x=b])
    apply (rule exI [where x = "\<lambda>z. (h (fst z, fst(snd z)), k (fst z, snd(snd z)))"])
    apply (intro conjI ballI continuous_intros continuous_on_compose2 [OF conth] continuous_on_compose2 [OF contk])
    using hsub ksub
    apply (auto simp: )
    done
qed

lemma homotopy_dominated_contractibility:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  assumes S: "contractible S"
      and f: "continuous_on S f" "image f S \<subseteq> T"
      and g: "continuous_on T g" "image g T \<subseteq> S"
      and hom: "homotopic_with (\<lambda>x. True) T T (f o g) id"
    shows "contractible T"
proof -
  obtain b where "homotopic_with (\<lambda>h. True) S T f (\<lambda>x. b)"
    using nullhomotopic_from_contractible [OF f S] .
  then have homg: "homotopic_with (\<lambda>x. True) T T ((\<lambda>x. b) \<circ> g) (f \<circ> g)"
    by (rule homotopic_with_compose_continuous_right [OF homotopic_with_symD g])
  show ?thesis
    apply (simp add: contractible_def)
    apply (rule exI [where x = b])
    apply (rule homotopic_with_symD)
    apply (rule homotopic_with_trans [OF _ hom])
    using homg apply (simp add: o_def)
    done
qed

subsection\<open>Local versions of topological properties in general\<close>

definition locally :: "('a::topological_space set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
where
 "locally P S \<equiv>
        \<forall>w x. openin (subtopology euclidean S) w \<and> x \<in> w
              \<longrightarrow> (\<exists>u v. openin (subtopology euclidean S) u \<and> P v \<and>
                        x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> w)"

lemma locallyI:
  assumes "\<And>w x. \<lbrakk>openin (subtopology euclidean S) w; x \<in> w\<rbrakk>
                  \<Longrightarrow> \<exists>u v. openin (subtopology euclidean S) u \<and> P v \<and>
                        x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> w"
    shows "locally P S"
using assms by (force simp: locally_def)

lemma locallyE:
  assumes "locally P S" "openin (subtopology euclidean S) w" "x \<in> w"
  obtains u v where "openin (subtopology euclidean S) u"
                    "P v" "x \<in> u" "u \<subseteq> v" "v \<subseteq> w"
  using assms unfolding locally_def by meson

lemma locally_mono:
  assumes "locally P S" "\<And>t. P t \<Longrightarrow> Q t"
    shows "locally Q S"
by (metis assms locally_def)

lemma locally_open_subset:
  assumes "locally P S" "openin (subtopology euclidean S) t"
    shows "locally P t"
using assms
apply (simp add: locally_def)
apply (erule all_forward)+
apply (rule impI)
apply (erule impCE)
 using openin_trans apply blast
apply (erule ex_forward)
by (metis (no_types, hide_lams) Int_absorb1 Int_lower1 Int_subset_iff openin_open openin_subtopology_Int_subset)

lemma locally_diff_closed:
    "\<lbrakk>locally P S; closedin (subtopology euclidean S) t\<rbrakk> \<Longrightarrow> locally P (S - t)"
  using locally_open_subset closedin_def by fastforce

lemma locally_empty [iff]: "locally P {}"
  by (simp add: locally_def openin_subtopology)

lemma locally_singleton [iff]:
  fixes a :: "'a::metric_space"
  shows "locally P {a} \<longleftrightarrow> P {a}"
apply (simp add: locally_def openin_euclidean_subtopology_iff subset_singleton_iff conj_disj_distribR cong: conj_cong)
using zero_less_one by blast

lemma locally_iff:
    "locally P S \<longleftrightarrow>
     (\<forall>T x. open T \<and> x \<in> S \<inter> T \<longrightarrow> (\<exists>U. open U \<and> (\<exists>v. P v \<and> x \<in> S \<inter> U \<and> S \<inter> U \<subseteq> v \<and> v \<subseteq> S \<inter> T)))"
apply (simp add: le_inf_iff locally_def openin_open, safe)
apply (metis IntE IntI le_inf_iff)
apply (metis IntI Int_subset_iff)
done

lemma locally_Int:
  assumes S: "locally P S" and t: "locally P t"
      and P: "\<And>S t. P S \<and> P t \<Longrightarrow> P(S \<inter> t)"
    shows "locally P (S \<inter> t)"
using S t unfolding locally_iff
apply clarify
apply (drule_tac x=T in spec)+
apply (drule_tac x=x in spec)+
apply clarsimp
apply (rename_tac U1 U2 V1 V2)
apply (rule_tac x="U1 \<inter> U2" in exI)
apply (simp add: open_Int)
apply (rule_tac x="V1 \<inter> V2" in exI)
apply (auto intro: P)
done

lemma locally_Times:
  fixes S :: "('a::metric_space) set" and T :: "('b::metric_space) set"
  assumes PS: "locally P S" and QT: "locally Q T" and R: "\<And>S T. P S \<and> Q T \<Longrightarrow> R(S \<times> T)"
  shows "locally R (S \<times> T)"
    unfolding locally_def
proof (clarify)
  fix W x y
  assume W: "openin (subtopology euclidean (S \<times> T)) W" and xy: "(x, y) \<in> W"
  then obtain U V where "openin (subtopology euclidean S) U" "x \<in> U"
                        "openin (subtopology euclidean T) V" "y \<in> V" "U \<times> V \<subseteq> W"
    using Times_in_interior_subtopology by metis
  then obtain U1 U2 V1 V2
         where opeS: "openin (subtopology euclidean S) U1 \<and> P U2 \<and> x \<in> U1 \<and> U1 \<subseteq> U2 \<and> U2 \<subseteq> U"
           and opeT: "openin (subtopology euclidean T) V1 \<and> Q V2 \<and> y \<in> V1 \<and> V1 \<subseteq> V2 \<and> V2 \<subseteq> V"
    by (meson PS QT locallyE)
  with \<open>U \<times> V \<subseteq> W\<close> show "\<exists>u v. openin (subtopology euclidean (S \<times> T)) u \<and> R v \<and> (x,y) \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> W"
    apply (rule_tac x="U1 \<times> V1" in exI)
    apply (rule_tac x="U2 \<times> V2" in exI)
    apply (auto simp: openin_Times R)
    done
qed


proposition homeomorphism_locally_imp:
  fixes S :: "'a::metric_space set" and t :: "'b::t2_space set"
  assumes S: "locally P S" and hom: "homeomorphism S t f g"
      and Q: "\<And>S S'. \<lbrakk>P S; homeomorphism S S' f g\<rbrakk> \<Longrightarrow> Q S'"
    shows "locally Q t"
proof (clarsimp simp: locally_def)
  fix W y
  assume "y \<in> W" and "openin (subtopology euclidean t) W"
  then obtain T where T: "open T" "W = t \<inter> T"
    by (force simp: openin_open)
  then have "W \<subseteq> t" by auto
  have f: "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x" "f ` S = t" "continuous_on S f"
   and g: "\<And>y. y \<in> t \<Longrightarrow> f(g y) = y" "g ` t = S" "continuous_on t g"
    using hom by (auto simp: homeomorphism_def)
  have gw: "g ` W = S \<inter> f -` W"
    using \<open>W \<subseteq> t\<close>
    apply auto
    using \<open>g ` t = S\<close> \<open>W \<subseteq> t\<close> apply blast
    using g \<open>W \<subseteq> t\<close> apply auto[1]
    by (simp add: f rev_image_eqI)
  have o: "openin (subtopology euclidean S) (g ` W)"
  proof -
    have "continuous_on S f"
      using f(3) by blast
    then show "openin (subtopology euclidean S) (g ` W)"
      by (simp add: gw Collect_conj_eq \<open>openin (subtopology euclidean t) W\<close> continuous_on_open f(2))
  qed
  then obtain u v
    where osu: "openin (subtopology euclidean S) u" and uv: "P v" "g y \<in> u" "u \<subseteq> v" "v \<subseteq> g ` W"
    using S [unfolded locally_def, rule_format, of "g ` W" "g y"] \<open>y \<in> W\<close> by force
  have "v \<subseteq> S" using uv by (simp add: gw)
  have fv: "f ` v = t \<inter> {x. g x \<in> v}"
    using \<open>f ` S = t\<close> f \<open>v \<subseteq> S\<close> by auto
  have "f ` v \<subseteq> W"
    using uv using Int_lower2 gw image_subsetI mem_Collect_eq subset_iff by auto
  have contvf: "continuous_on v f"
    using \<open>v \<subseteq> S\<close> continuous_on_subset f(3) by blast
  have contvg: "continuous_on (f ` v) g"
    using \<open>f ` v \<subseteq> W\<close> \<open>W \<subseteq> t\<close> continuous_on_subset [OF g(3)] by blast
  have homv: "homeomorphism v (f ` v) f g"
    using \<open>v \<subseteq> S\<close> \<open>W \<subseteq> t\<close> f
    apply (simp add: homeomorphism_def contvf contvg, auto)
    by (metis f(1) rev_image_eqI rev_subsetD)
  have 1: "openin (subtopology euclidean t) (t \<inter> g -` u)"
    apply (rule continuous_on_open [THEN iffD1, rule_format])
    apply (rule \<open>continuous_on t g\<close>)
    using \<open>g ` t = S\<close> apply (simp add: osu)
    done
  have 2: "\<exists>V. Q V \<and> y \<in> (t \<inter> g -` u) \<and> (t \<inter> g -` u) \<subseteq> V \<and> V \<subseteq> W"
    apply (rule_tac x="f ` v" in exI)
    apply (intro conjI Q [OF \<open>P v\<close> homv])
    using \<open>W \<subseteq> t\<close> \<open>y \<in> W\<close>  \<open>f ` v \<subseteq> W\<close>  uv  apply (auto simp: fv)
    done
  show "\<exists>U. openin (subtopology euclidean t) U \<and> (\<exists>v. Q v \<and> y \<in> U \<and> U \<subseteq> v \<and> v \<subseteq> W)"
    by (meson 1 2)
qed

lemma homeomorphism_locally:
  fixes f:: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes hom: "homeomorphism S t f g"
      and eq: "\<And>S t. homeomorphism S t f g \<Longrightarrow> (P S \<longleftrightarrow> Q t)"
    shows "locally P S \<longleftrightarrow> locally Q t"
apply (rule iffI)
apply (erule homeomorphism_locally_imp [OF _ hom])
apply (simp add: eq)
apply (erule homeomorphism_locally_imp)
using eq homeomorphism_sym homeomorphism_symD [OF hom] apply blast+
done

lemma homeomorphic_locally:
  fixes S:: "'a::metric_space set" and T:: "'b::metric_space set"
  assumes hom: "S homeomorphic T"
          and iff: "\<And>X Y. X homeomorphic Y \<Longrightarrow> (P X \<longleftrightarrow> Q Y)"
    shows "locally P S \<longleftrightarrow> locally Q T"
proof -
  obtain f g where hom: "homeomorphism S T f g"
    using assms by (force simp: homeomorphic_def)
  then show ?thesis
    using homeomorphic_def local.iff
    by (blast intro!: homeomorphism_locally)
qed

lemma homeomorphic_local_compactness:
  fixes S:: "'a::metric_space set" and T:: "'b::metric_space set"
  shows "S homeomorphic T \<Longrightarrow> locally compact S \<longleftrightarrow> locally compact T"
by (simp add: homeomorphic_compactness homeomorphic_locally)

lemma locally_translation:
  fixes P :: "'a :: real_normed_vector set \<Rightarrow> bool"
  shows
   "(\<And>S. P (image (\<lambda>x. a + x) S) \<longleftrightarrow> P S)
        \<Longrightarrow> locally P (image (\<lambda>x. a + x) S) \<longleftrightarrow> locally P S"
apply (rule homeomorphism_locally [OF homeomorphism_translation])
apply (simp add: homeomorphism_def)
by metis

lemma locally_injective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "linear f" "inj f" and iff: "\<And>S. P (f ` S) \<longleftrightarrow> Q S"
    shows "locally P (f ` S) \<longleftrightarrow> locally Q S"
apply (rule linear_homeomorphism_image [OF f])
apply (rule_tac f=g and g = f in homeomorphism_locally, assumption)
by (metis iff homeomorphism_def)

lemma locally_open_map_image:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes P: "locally P S"
      and f: "continuous_on S f"
      and oo: "\<And>t. openin (subtopology euclidean S) t
                   \<Longrightarrow> openin (subtopology euclidean (f ` S)) (f ` t)"
      and Q: "\<And>t. \<lbrakk>t \<subseteq> S; P t\<rbrakk> \<Longrightarrow> Q(f ` t)"
    shows "locally Q (f ` S)"
proof (clarsimp simp add: locally_def)
  fix W y
  assume oiw: "openin (subtopology euclidean (f ` S)) W" and "y \<in> W"
  then have "W \<subseteq> f ` S" by (simp add: openin_euclidean_subtopology_iff)
  have oivf: "openin (subtopology euclidean S) (S \<inter> f -` W)"
    by (rule continuous_on_open [THEN iffD1, rule_format, OF f oiw])
  then obtain x where "x \<in> S" "f x = y"
    using \<open>W \<subseteq> f ` S\<close> \<open>y \<in> W\<close> by blast
  then obtain U V
    where "openin (subtopology euclidean S) U" "P V" "x \<in> U" "U \<subseteq> V" "V \<subseteq> S \<inter> f -` W"
    using P [unfolded locally_def, rule_format, of "(S \<inter> f -` W)" x] oivf \<open>y \<in> W\<close>
    by auto
  then show "\<exists>X. openin (subtopology euclidean (f ` S)) X \<and> (\<exists>Y. Q Y \<and> y \<in> X \<and> X \<subseteq> Y \<and> Y \<subseteq> W)"
    apply (rule_tac x="f ` U" in exI)
    apply (rule conjI, blast intro!: oo)
    apply (rule_tac x="f ` V" in exI)
    apply (force simp: \<open>f x = y\<close> rev_image_eqI intro: Q)
    done
qed

subsection\<open>Sort of induction principle for connected sets\<close>

lemma connected_induction:
  assumes "connected S"
      and opD: "\<And>T a. \<lbrakk>openin (subtopology euclidean S) T; a \<in> T\<rbrakk> \<Longrightarrow> \<exists>z. z \<in> T \<and> P z"
      and opI: "\<And>a. a \<in> S
             \<Longrightarrow> \<exists>T. openin (subtopology euclidean S) T \<and> a \<in> T \<and>
                     (\<forall>x \<in> T. \<forall>y \<in> T. P x \<and> P y \<and> Q x \<longrightarrow> Q y)"
      and etc: "a \<in> S" "b \<in> S" "P a" "P b" "Q a"
    shows "Q b"
proof -
  have 1: "openin (subtopology euclidean S)
             {b. \<exists>T. openin (subtopology euclidean S) T \<and>
                     b \<in> T \<and> (\<forall>x\<in>T. P x \<longrightarrow> Q x)}"
    apply (subst openin_subopen, clarify)
    apply (rule_tac x=T in exI, auto)
    done
  have 2: "openin (subtopology euclidean S)
             {b. \<exists>T. openin (subtopology euclidean S) T \<and>
                     b \<in> T \<and> (\<forall>x\<in>T. P x \<longrightarrow> ~ Q x)}"
    apply (subst openin_subopen, clarify)
    apply (rule_tac x=T in exI, auto)
    done
  show ?thesis
    using \<open>connected S\<close>
    apply (simp only: connected_openin HOL.not_ex HOL.de_Morgan_conj)
    apply (elim disjE allE)
         apply (blast intro: 1)
        apply (blast intro: 2, simp_all)
       apply clarify apply (metis opI)
      using opD apply (blast intro: etc elim: dest:)
     using opI etc apply meson+
    done
qed

lemma connected_equivalence_relation_gen:
  assumes "connected S"
      and etc: "a \<in> S" "b \<in> S" "P a" "P b"
      and trans: "\<And>x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z"
      and opD: "\<And>T a. \<lbrakk>openin (subtopology euclidean S) T; a \<in> T\<rbrakk> \<Longrightarrow> \<exists>z. z \<in> T \<and> P z"
      and opI: "\<And>a. a \<in> S
             \<Longrightarrow> \<exists>T. openin (subtopology euclidean S) T \<and> a \<in> T \<and>
                     (\<forall>x \<in> T. \<forall>y \<in> T. P x \<and> P y \<longrightarrow> R x y)"
    shows "R a b"
proof -
  have "\<And>a b c. \<lbrakk>a \<in> S; P a; b \<in> S; c \<in> S; P b; P c; R a b\<rbrakk> \<Longrightarrow> R a c"
    apply (rule connected_induction [OF \<open>connected S\<close> opD], simp_all)
    by (meson trans opI)
  then show ?thesis by (metis etc opI)
qed

lemma connected_induction_simple:
  assumes "connected S"
      and etc: "a \<in> S" "b \<in> S" "P a"
      and opI: "\<And>a. a \<in> S
             \<Longrightarrow> \<exists>T. openin (subtopology euclidean S) T \<and> a \<in> T \<and>
                     (\<forall>x \<in> T. \<forall>y \<in> T. P x \<longrightarrow> P y)"
    shows "P b"
apply (rule connected_induction [OF \<open>connected S\<close> _, where P = "\<lambda>x. True"], blast)
apply (frule opI)
using etc apply simp_all
done

lemma connected_equivalence_relation:
  assumes "connected S"
      and etc: "a \<in> S" "b \<in> S"
      and sym: "\<And>x y. \<lbrakk>R x y; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> R y x"
      and trans: "\<And>x y z. \<lbrakk>R x y; R y z; x \<in> S; y \<in> S; z \<in> S\<rbrakk> \<Longrightarrow> R x z"
      and opI: "\<And>a. a \<in> S \<Longrightarrow> \<exists>T. openin (subtopology euclidean S) T \<and> a \<in> T \<and> (\<forall>x \<in> T. R a x)"
    shows "R a b"
proof -
  have "\<And>a b c. \<lbrakk>a \<in> S; b \<in> S; c \<in> S; R a b\<rbrakk> \<Longrightarrow> R a c"
    apply (rule connected_induction_simple [OF \<open>connected S\<close>], simp_all)
    by (meson local.sym local.trans opI openin_imp_subset subsetCE)
  then show ?thesis by (metis etc opI)
qed

lemma locally_constant_imp_constant:
  assumes "connected S"
      and opI: "\<And>a. a \<in> S
             \<Longrightarrow> \<exists>T. openin (subtopology euclidean S) T \<and> a \<in> T \<and> (\<forall>x \<in> T. f x = f a)"
    shows "f constant_on S"
proof -
  have "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> f x = f y"
    apply (rule connected_equivalence_relation [OF \<open>connected S\<close>], simp_all)
    by (metis opI)
  then show ?thesis
    by (metis constant_on_def)
qed

lemma locally_constant:
     "connected S \<Longrightarrow> locally (\<lambda>U. f constant_on U) S \<longleftrightarrow> f constant_on S"
apply (simp add: locally_def)
apply (rule iffI)
 apply (rule locally_constant_imp_constant, assumption)
 apply (metis (mono_tags, hide_lams) constant_on_def constant_on_subset openin_subtopology_self)
by (meson constant_on_subset openin_imp_subset order_refl)


subsection\<open>Basic properties of local compactness\<close>

lemma locally_compact:
  fixes s :: "'a :: metric_space set"
  shows
    "locally compact s \<longleftrightarrow>
     (\<forall>x \<in> s. \<exists>u v. x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> s \<and>
                    openin (subtopology euclidean s) u \<and> compact v)"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply clarify
    apply (erule_tac w = "s \<inter> ball x 1" in locallyE)
    by auto
next
  assume r [rule_format]: ?rhs
  have *: "\<exists>u v.
              openin (subtopology euclidean s) u \<and>
              compact v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> s \<inter> T"
          if "open T" "x \<in> s" "x \<in> T" for x T
  proof -
    obtain u v where uv: "x \<in> u" "u \<subseteq> v" "v \<subseteq> s" "compact v" "openin (subtopology euclidean s) u"
      using r [OF \<open>x \<in> s\<close>] by auto
    obtain e where "e>0" and e: "cball x e \<subseteq> T"
      using open_contains_cball \<open>open T\<close> \<open>x \<in> T\<close> by blast
    show ?thesis
      apply (rule_tac x="(s \<inter> ball x e) \<inter> u" in exI)
      apply (rule_tac x="cball x e \<inter> v" in exI)
      using that \<open>e > 0\<close> e uv
      apply auto
      done
  qed
  show ?lhs
    apply (rule locallyI)
    apply (subst (asm) openin_open)
    apply (blast intro: *)
    done
qed

lemma locally_compactE:
  fixes s :: "'a :: metric_space set"
  assumes "locally compact s"
  obtains u v where "\<And>x. x \<in> s \<Longrightarrow> x \<in> u x \<and> u x \<subseteq> v x \<and> v x \<subseteq> s \<and>
                             openin (subtopology euclidean s) (u x) \<and> compact (v x)"
using assms
unfolding locally_compact by metis

lemma locally_compact_alt:
  fixes s :: "'a :: heine_borel set"
  shows "locally compact s \<longleftrightarrow>
         (\<forall>x \<in> s. \<exists>u. x \<in> u \<and>
                    openin (subtopology euclidean s) u \<and> compact(closure u) \<and> closure u \<subseteq> s)"
apply (simp add: locally_compact)
apply (intro ball_cong ex_cong refl iffI)
apply (metis bounded_subset closure_eq closure_mono compact_eq_bounded_closed dual_order.trans)
by (meson closure_subset compact_closure)

lemma locally_compact_Int_cball:
  fixes s :: "'a :: heine_borel set"
  shows "locally compact s \<longleftrightarrow> (\<forall>x \<in> s. \<exists>e. 0 < e \<and> closed(cball x e \<inter> s))"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (simp add: locally_compact openin_contains_cball)
    apply (clarify | assumption | drule bspec)+
    by (metis (no_types, lifting)  compact_cball compact_imp_closed compact_Int inf.absorb_iff2 inf.orderE inf_sup_aci(2))
next
  assume ?rhs
  then show ?lhs
    apply (simp add: locally_compact openin_contains_cball)
    apply (clarify | assumption | drule bspec)+
    apply (rule_tac x="ball x e \<inter> s" in exI, simp)
    apply (rule_tac x="cball x e \<inter> s" in exI)
    using compact_eq_bounded_closed
    apply auto
    apply (metis open_ball le_infI1 mem_ball open_contains_cball_eq)
    done
qed

lemma locally_compact_compact:
  fixes s :: "'a :: heine_borel set"
  shows "locally compact s \<longleftrightarrow>
         (\<forall>k. k \<subseteq> s \<and> compact k
              \<longrightarrow> (\<exists>u v. k \<subseteq> u \<and> u \<subseteq> v \<and> v \<subseteq> s \<and>
                         openin (subtopology euclidean s) u \<and> compact v))"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain u v where
    uv: "\<And>x. x \<in> s \<Longrightarrow> x \<in> u x \<and> u x \<subseteq> v x \<and> v x \<subseteq> s \<and>
                             openin (subtopology euclidean s) (u x) \<and> compact (v x)"
    by (metis locally_compactE)
  have *: "\<exists>u v. k \<subseteq> u \<and> u \<subseteq> v \<and> v \<subseteq> s \<and> openin (subtopology euclidean s) u \<and> compact v"
          if "k \<subseteq> s" "compact k" for k
  proof -
    have "\<And>C. (\<forall>c\<in>C. openin (subtopology euclidean k) c) \<and> k \<subseteq> \<Union>C \<Longrightarrow>
                    \<exists>D\<subseteq>C. finite D \<and> k \<subseteq> \<Union>D"
      using that by (simp add: compact_eq_openin_cover)
    moreover have "\<forall>c \<in> (\<lambda>x. k \<inter> u x) ` k. openin (subtopology euclidean k) c"
      using that by clarify (metis subsetD inf.absorb_iff2 openin_subset openin_subtopology_Int_subset topspace_euclidean_subtopology uv)
    moreover have "k \<subseteq> \<Union>((\<lambda>x. k \<inter> u x) ` k)"
      using that by clarsimp (meson subsetCE uv)
    ultimately obtain D where "D \<subseteq> (\<lambda>x. k \<inter> u x) ` k" "finite D" "k \<subseteq> \<Union>D"
      by metis
    then obtain T where T: "T \<subseteq> k" "finite T" "k \<subseteq> \<Union>((\<lambda>x. k \<inter> u x) ` T)"
      by (metis finite_subset_image)
    have Tuv: "UNION T u \<subseteq> UNION T v"
      using T that by (force simp: dest!: uv)
    show ?thesis
      apply (rule_tac x="\<Union>(u ` T)" in exI)
      apply (rule_tac x="\<Union>(v ` T)" in exI)
      apply (simp add: Tuv)
      using T that
      apply (auto simp: dest!: uv)
      done
  qed
  show ?rhs
    by (blast intro: *)
next
  assume ?rhs
  then show ?lhs
    apply (clarsimp simp add: locally_compact)
    apply (drule_tac x="{x}" in spec, simp)
    done
qed

lemma open_imp_locally_compact:
  fixes s :: "'a :: heine_borel set"
  assumes "open s"
    shows "locally compact s"
proof -
  have *: "\<exists>u v. x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> s \<and> openin (subtopology euclidean s) u \<and> compact v"
          if "x \<in> s" for x
  proof -
    obtain e where "e>0" and e: "cball x e \<subseteq> s"
      using open_contains_cball assms \<open>x \<in> s\<close> by blast
    have ope: "openin (subtopology euclidean s) (ball x e)"
      by (meson e open_ball ball_subset_cball dual_order.trans open_subset)
    show ?thesis
      apply (rule_tac x="ball x e" in exI)
      apply (rule_tac x="cball x e" in exI)
      using \<open>e > 0\<close> e apply (auto simp: ope)
      done
  qed
  show ?thesis
    unfolding locally_compact
    by (blast intro: *)
qed

lemma closed_imp_locally_compact:
  fixes s :: "'a :: heine_borel set"
  assumes "closed s"
    shows "locally compact s"
proof -
  have *: "\<exists>u v. x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> s \<and>
                 openin (subtopology euclidean s) u \<and> compact v"
          if "x \<in> s" for x
  proof -
    show ?thesis
      apply (rule_tac x = "s \<inter> ball x 1" in exI)
      apply (rule_tac x = "s \<inter> cball x 1" in exI)
      using \<open>x \<in> s\<close> assms apply auto
      done
  qed
  show ?thesis
    unfolding locally_compact
    by (blast intro: *)
qed

lemma locally_compact_UNIV: "locally compact (UNIV :: 'a :: heine_borel set)"
  by (simp add: closed_imp_locally_compact)

lemma locally_compact_Int:
  fixes s :: "'a :: t2_space set"
  shows "\<lbrakk>locally compact s; locally compact t\<rbrakk> \<Longrightarrow> locally compact (s \<inter> t)"
by (simp add: compact_Int locally_Int)

lemma locally_compact_closedin:
  fixes s :: "'a :: heine_borel set"
  shows "\<lbrakk>closedin (subtopology euclidean s) t; locally compact s\<rbrakk>
        \<Longrightarrow> locally compact t"
unfolding closedin_closed
using closed_imp_locally_compact locally_compact_Int by blast

lemma locally_compact_delete:
     fixes s :: "'a :: t1_space set"
     shows "locally compact s \<Longrightarrow> locally compact (s - {a})"
  by (auto simp: openin_delete locally_open_subset)

lemma locally_closed:
  fixes s :: "'a :: heine_borel set"
  shows "locally closed s \<longleftrightarrow> locally compact s"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (simp only: locally_def)
    apply (erule all_forward imp_forward asm_rl exE)+
    apply (rule_tac x = "u \<inter> ball x 1" in exI)
    apply (rule_tac x = "v \<inter> cball x 1" in exI)
    apply (force intro: openin_trans)
    done
next
  assume ?rhs then show ?lhs
    using compact_eq_bounded_closed locally_mono by blast
qed

lemma locally_compact_openin_Un:
  fixes S :: "'a::euclidean_space set"
  assumes LCS: "locally compact S" and LCT:"locally compact T"
      and opS: "openin (subtopology euclidean (S \<union> T)) S"
      and opT: "openin (subtopology euclidean (S \<union> T)) T"
    shows "locally compact (S \<union> T)"
proof -
  have "\<exists>e>0. closed (cball x e \<inter> (S \<union> T))" if "x \<in> S" for x
  proof -
    obtain e1 where "e1 > 0" and e1: "closed (cball x e1 \<inter> S)"
      using LCS \<open>x \<in> S\<close> unfolding locally_compact_Int_cball by blast
    moreover obtain e2 where "e2 > 0" and e2: "cball x e2 \<inter> (S \<union> T) \<subseteq> S"
      by (meson \<open>x \<in> S\<close> opS openin_contains_cball)
    then have "cball x e2 \<inter> (S \<union> T) = cball x e2 \<inter> S"
      by force
    ultimately show ?thesis
      apply (rule_tac x="min e1 e2" in exI)
      apply (auto simp: cball_min_Int \<open>e2 > 0\<close> inf_assoc closed_Int)
      by (metis closed_Int closed_cball inf_left_commute)
  qed
  moreover have "\<exists>e>0. closed (cball x e \<inter> (S \<union> T))" if "x \<in> T" for x
  proof -
    obtain e1 where "e1 > 0" and e1: "closed (cball x e1 \<inter> T)"
      using LCT \<open>x \<in> T\<close> unfolding locally_compact_Int_cball by blast
    moreover obtain e2 where "e2 > 0" and e2: "cball x e2 \<inter> (S \<union> T) \<subseteq> T"
      by (meson \<open>x \<in> T\<close> opT openin_contains_cball)
    then have "cball x e2 \<inter> (S \<union> T) = cball x e2 \<inter> T"
      by force
    ultimately show ?thesis
      apply (rule_tac x="min e1 e2" in exI)
      apply (auto simp: cball_min_Int \<open>e2 > 0\<close> inf_assoc closed_Int)
      by (metis closed_Int closed_cball inf_left_commute)
  qed
  ultimately show ?thesis
    by (force simp: locally_compact_Int_cball)
qed

lemma locally_compact_closedin_Un:
  fixes S :: "'a::euclidean_space set"
  assumes LCS: "locally compact S" and LCT:"locally compact T"
      and clS: "closedin (subtopology euclidean (S \<union> T)) S"
      and clT: "closedin (subtopology euclidean (S \<union> T)) T"
    shows "locally compact (S \<union> T)"
proof -
  have "\<exists>e>0. closed (cball x e \<inter> (S \<union> T))" if "x \<in> S" "x \<in> T" for x
  proof -
    obtain e1 where "e1 > 0" and e1: "closed (cball x e1 \<inter> S)"
      using LCS \<open>x \<in> S\<close> unfolding locally_compact_Int_cball by blast
    moreover
    obtain e2 where "e2 > 0" and e2: "closed (cball x e2 \<inter> T)"
      using LCT \<open>x \<in> T\<close> unfolding locally_compact_Int_cball by blast
    ultimately show ?thesis
      apply (rule_tac x="min e1 e2" in exI)
      apply (auto simp: cball_min_Int \<open>e2 > 0\<close> inf_assoc closed_Int Int_Un_distrib)
      by (metis closed_Int closed_Un closed_cball inf_left_commute)
  qed
  moreover
  have "\<exists>e>0. closed (cball x e \<inter> (S \<union> T))" if x: "x \<in> S" "x \<notin> T" for x
  proof -
    obtain e1 where "e1 > 0" and e1: "closed (cball x e1 \<inter> S)"
      using LCS \<open>x \<in> S\<close> unfolding locally_compact_Int_cball by blast
    moreover
    obtain e2 where "e2>0" and "cball x e2 \<inter> (S \<union> T) \<subseteq> S - T"
      using clT x by (fastforce simp: openin_contains_cball closedin_def)
    then have "closed (cball x e2 \<inter> T)"
    proof -
      have "{} = T - (T - cball x e2)"
        using Diff_subset Int_Diff \<open>cball x e2 \<inter> (S \<union> T) \<subseteq> S - T\<close> by auto
      then show ?thesis
        by (simp add: Diff_Diff_Int inf_commute)
    qed
    ultimately show ?thesis
      apply (rule_tac x="min e1 e2" in exI)
      apply (auto simp: cball_min_Int \<open>e2 > 0\<close> inf_assoc closed_Int Int_Un_distrib)
      by (metis closed_Int closed_Un closed_cball inf_left_commute)
  qed
  moreover
  have "\<exists>e>0. closed (cball x e \<inter> (S \<union> T))" if x: "x \<notin> S" "x \<in> T" for x
  proof -
    obtain e1 where "e1 > 0" and e1: "closed (cball x e1 \<inter> T)"
      using LCT \<open>x \<in> T\<close> unfolding locally_compact_Int_cball by blast
    moreover
    obtain e2 where "e2>0" and "cball x e2 \<inter> (S \<union> T) \<subseteq> S \<union> T - S"
      using clS x by (fastforce simp: openin_contains_cball closedin_def)
    then have "closed (cball x e2 \<inter> S)"
      by (metis Diff_disjoint Int_empty_right closed_empty inf.left_commute inf.orderE inf_sup_absorb)
    ultimately show ?thesis
      apply (rule_tac x="min e1 e2" in exI)
      apply (auto simp: cball_min_Int \<open>e2 > 0\<close> inf_assoc closed_Int Int_Un_distrib)
      by (metis closed_Int closed_Un closed_cball inf_left_commute)
  qed
  ultimately show ?thesis
    by (auto simp: locally_compact_Int_cball)
qed

lemma locally_compact_Times:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  shows "\<lbrakk>locally compact S; locally compact T\<rbrakk> \<Longrightarrow> locally compact (S \<times> T)"
  by (auto simp: compact_Times locally_Times)

lemma locally_compact_compact_subopen:
  fixes S :: "'a :: heine_borel set"
  shows
   "locally compact S \<longleftrightarrow>
    (\<forall>K T. K \<subseteq> S \<and> compact K \<and> open T \<and> K \<subseteq> T
          \<longrightarrow> (\<exists>U V. K \<subseteq> U \<and> U \<subseteq> V \<and> U \<subseteq> T \<and> V \<subseteq> S \<and>
                     openin (subtopology euclidean S) U \<and> compact V))"
   (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof clarify
    fix K :: "'a set" and T :: "'a set"
    assume "K \<subseteq> S" and "compact K" and "open T" and "K \<subseteq> T"
    obtain U V where "K \<subseteq> U" "U \<subseteq> V" "V \<subseteq> S" "compact V"
                 and ope: "openin (subtopology euclidean S) U"
      using L unfolding locally_compact_compact by (meson \<open>K \<subseteq> S\<close> \<open>compact K\<close>)
    show "\<exists>U V. K \<subseteq> U \<and> U \<subseteq> V \<and> U \<subseteq> T \<and> V \<subseteq> S \<and>
                openin (subtopology euclidean S) U \<and> compact V"
    proof (intro exI conjI)
      show "K \<subseteq> U \<inter> T"
        by (simp add: \<open>K \<subseteq> T\<close> \<open>K \<subseteq> U\<close>)
      show "U \<inter> T \<subseteq> closure(U \<inter> T)"
        by (rule closure_subset)
      show "closure (U \<inter> T) \<subseteq> S"
        by (metis \<open>U \<subseteq> V\<close> \<open>V \<subseteq> S\<close> \<open>compact V\<close> closure_closed closure_mono compact_imp_closed inf.cobounded1 subset_trans)
      show "openin (subtopology euclidean S) (U \<inter> T)"
        by (simp add: \<open>open T\<close> ope openin_Int_open)
      show "compact (closure (U \<inter> T))"
        by (meson Int_lower1 \<open>U \<subseteq> V\<close> \<open>compact V\<close> bounded_subset compact_closure compact_eq_bounded_closed)
    qed auto
  qed
next
  assume ?rhs then show ?lhs
    unfolding locally_compact_compact
    by (metis open_openin openin_topspace subtopology_superset top.extremum topspace_euclidean_subtopology)
qed

subsection\<open>Sura-Bura's results about compact components of sets.\<close>

proposition Sura_Bura_compact:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and C: "C \<in> components S"
  shows "C = \<Inter>{T. C \<subseteq> T \<and> openin (subtopology euclidean S) T \<and>
                           closedin (subtopology euclidean S) T}"
         (is "C = \<Inter>?\<T>")
proof
  obtain x where x: "C = connected_component_set S x" and "x \<in> S"
    using C by (auto simp: components_def)
  have "C \<subseteq> S"
    by (simp add: C in_components_subset)
  have "\<Inter>?\<T> \<subseteq> connected_component_set S x"
  proof (rule connected_component_maximal)
    have "x \<in> C"
      by (simp add: \<open>x \<in> S\<close> x)
    then show "x \<in> \<Inter>?\<T>"
      by blast
    have clo: "closed (\<Inter>?\<T>)"
      by (simp add: \<open>compact S\<close> closed_Inter closedin_compact_eq compact_imp_closed)
    have False
      if K1: "closedin (subtopology euclidean (\<Inter>?\<T>)) K1" and
         K2: "closedin (subtopology euclidean (\<Inter>?\<T>)) K2" and
         K12_Int: "K1 \<inter> K2 = {}" and K12_Un: "K1 \<union> K2 = \<Inter>?\<T>" and "K1 \<noteq> {}" "K2 \<noteq> {}"
       for K1 K2
    proof -
      have "closed K1" "closed K2"
        using closedin_closed_trans clo K1 K2 by blast+
      then obtain V1 V2 where "open V1" "open V2" "K1 \<subseteq> V1" "K2 \<subseteq> V2" and V12: "V1 \<inter> V2 = {}"
        using separation_normal \<open>K1 \<inter> K2 = {}\<close> by metis
      have SV12_ne: "(S - (V1 \<union> V2)) \<inter> (\<Inter>?\<T>) \<noteq> {}"
      proof (rule compact_imp_fip)
        show "compact (S - (V1 \<union> V2))"
          by (simp add: \<open>open V1\<close> \<open>open V2\<close> \<open>compact S\<close> compact_diff open_Un)
        show clo\<T>: "closed T" if "T \<in> ?\<T>" for T
          using that \<open>compact S\<close>
          by (force intro: closedin_closed_trans simp add: compact_imp_closed)
        show "(S - (V1 \<union> V2)) \<inter> \<Inter>\<F> \<noteq> {}" if "finite \<F>" and \<F>: "\<F> \<subseteq> ?\<T>" for \<F>
        proof
          assume djo: "(S - (V1 \<union> V2)) \<inter> \<Inter>\<F> = {}"
          obtain D where opeD: "openin (subtopology euclidean S) D"
                   and cloD: "closedin (subtopology euclidean S) D"
                   and "C \<subseteq> D" and DV12: "D \<subseteq> V1 \<union> V2"
          proof (cases "\<F> = {}")
            case True
            with \<open>C \<subseteq> S\<close> djo that show ?thesis
              by force
          next
            case False show ?thesis
            proof
              show ope: "openin (subtopology euclidean S) (\<Inter>\<F>)"
                using openin_Inter \<open>finite \<F>\<close> False \<F> by blast
              then show "closedin (subtopology euclidean S) (\<Inter>\<F>)"
                by (meson clo\<T> \<F> closed_Inter closed_subset openin_imp_subset subset_eq)
              show "C \<subseteq> \<Inter>\<F>"
                using \<F> by auto
              show "\<Inter>\<F> \<subseteq> V1 \<union> V2"
                using ope djo openin_imp_subset by fastforce
            qed
          qed
          have "connected C"
            by (simp add: x)
          have "closed D"
            using \<open>compact S\<close> cloD closedin_closed_trans compact_imp_closed by blast
          have cloV1: "closedin (subtopology euclidean D) (D \<inter> closure V1)"
            and cloV2: "closedin (subtopology euclidean D) (D \<inter> closure V2)"
            by (simp_all add: closedin_closed_Int)
          moreover have "D \<inter> closure V1 = D \<inter> V1" "D \<inter> closure V2 = D \<inter> V2"
            apply safe
            using \<open>D \<subseteq> V1 \<union> V2\<close> \<open>open V1\<close> \<open>open V2\<close> V12
               apply (simp_all add: closure_subset [THEN subsetD] closure_iff_nhds_not_empty, blast+)
            done
          ultimately have cloDV1: "closedin (subtopology euclidean D) (D \<inter> V1)"
                      and cloDV2:  "closedin (subtopology euclidean D) (D \<inter> V2)"
            by metis+
          then obtain U1 U2 where "closed U1" "closed U2"
               and D1: "D \<inter> V1 = D \<inter> U1" and D2: "D \<inter> V2 = D \<inter> U2"
            by (auto simp: closedin_closed)
          have "D \<inter> U1 \<inter> C \<noteq> {}"
          proof
            assume "D \<inter> U1 \<inter> C = {}"
            then have *: "C \<subseteq> D \<inter> V2"
              using D1 DV12 \<open>C \<subseteq> D\<close> by auto
            have "\<Inter>?\<T> \<subseteq> D \<inter> V2"
              apply (rule Inter_lower)
              using * apply simp
              by (meson cloDV2 \<open>open V2\<close> cloD closedin_trans le_inf_iff opeD openin_Int_open)
            then show False
              using K1 V12 \<open>K1 \<noteq> {}\<close> \<open>K1 \<subseteq> V1\<close> closedin_imp_subset by blast
          qed
          moreover have "D \<inter> U2 \<inter> C \<noteq> {}"
          proof
            assume "D \<inter> U2 \<inter> C = {}"
            then have *: "C \<subseteq> D \<inter> V1"
              using D2 DV12 \<open>C \<subseteq> D\<close> by auto
            have "\<Inter>?\<T> \<subseteq> D \<inter> V1"
              apply (rule Inter_lower)
              using * apply simp
              by (meson cloDV1 \<open>open V1\<close> cloD closedin_trans le_inf_iff opeD openin_Int_open)
            then show False
              using K2 V12 \<open>K2 \<noteq> {}\<close> \<open>K2 \<subseteq> V2\<close> closedin_imp_subset by blast
          qed
          ultimately show False
            using \<open>connected C\<close> unfolding connected_closed
            apply (simp only: not_ex)
            apply (drule_tac x="D \<inter> U1" in spec)
            apply (drule_tac x="D \<inter> U2" in spec)
            using \<open>C \<subseteq> D\<close> D1 D2 V12 DV12 \<open>closed U1\<close> \<open>closed U2\<close> \<open>closed D\<close>
            by blast
        qed
      qed
      show False
        by (metis (full_types) DiffE UnE Un_upper2 SV12_ne \<open>K1 \<subseteq> V1\<close> \<open>K2 \<subseteq> V2\<close> disjoint_iff_not_equal subsetCE sup_ge1 K12_Un)
    qed
    then show "connected (\<Inter>?\<T>)"
      by (auto simp: connected_closedin_eq)
    show "\<Inter>?\<T> \<subseteq> S"
      by (fastforce simp: C in_components_subset)
  qed
  with x show "\<Inter>?\<T> \<subseteq> C" by simp
qed auto


corollary Sura_Bura_clopen_subset:
  fixes S :: "'a::euclidean_space set"
  assumes S: "locally compact S" and C: "C \<in> components S" and "compact C"
      and U: "open U" "C \<subseteq> U"
  obtains K where "openin (subtopology euclidean S) K" "compact K" "C \<subseteq> K" "K \<subseteq> U"
proof (rule ccontr)
  assume "\<not> thesis"
  with that have neg: "\<nexists>K. openin (subtopology euclidean S) K \<and> compact K \<and> C \<subseteq> K \<and> K \<subseteq> U"
    by metis
  obtain V K where "C \<subseteq> V" "V \<subseteq> U" "V \<subseteq> K" "K \<subseteq> S" "compact K"
               and opeSV: "openin (subtopology euclidean S) V"
    using S U \<open>compact C\<close>
    apply (simp add: locally_compact_compact_subopen)
    by (meson C in_components_subset)
  let ?\<T> = "{T. C \<subseteq> T \<and> openin (subtopology euclidean K) T \<and> compact T \<and> T \<subseteq> K}"
  have CK: "C \<in> components K"
    by (meson C \<open>C \<subseteq> V\<close> \<open>K \<subseteq> S\<close> \<open>V \<subseteq> K\<close> components_intermediate_subset subset_trans)
  with \<open>compact K\<close>
  have "C = \<Inter>{T. C \<subseteq> T \<and> openin (subtopology euclidean K) T \<and> closedin (subtopology euclidean K) T}"
    by (simp add: Sura_Bura_compact)
  then have Ceq: "C = \<Inter>?\<T>"
    by (simp add: closedin_compact_eq \<open>compact K\<close>)
  obtain W where "open W" and W: "V = S \<inter> W"
    using opeSV by (auto simp: openin_open)
  have "-(U \<inter> W) \<inter> \<Inter>?\<T> \<noteq> {}"
  proof (rule closed_imp_fip_compact)
    show "- (U \<inter> W) \<inter> \<Inter>\<F> \<noteq> {}"
      if "finite \<F>" and \<F>: "\<F> \<subseteq> ?\<T>" for \<F>
    proof (cases "\<F> = {}")
      case True
      have False if "U = UNIV" "W = UNIV"
      proof -
        have "V = S"
          by (simp add: W \<open>W = UNIV\<close>)
        with neg show False
          using \<open>C \<subseteq> V\<close> \<open>K \<subseteq> S\<close> \<open>V \<subseteq> K\<close> \<open>V \<subseteq> U\<close> \<open>compact K\<close> by auto
      qed
      with True show ?thesis
        by auto
    next
      case False
      show ?thesis
      proof
        assume "- (U \<inter> W) \<inter> \<Inter>\<F> = {}"
        then have FUW: "\<Inter>\<F> \<subseteq> U \<inter> W"
          by blast
        have "C \<subseteq> \<Inter>\<F>"
          using \<F> by auto
        moreover have "compact (\<Inter>\<F>)"
          by (metis (no_types, lifting) compact_Inter False mem_Collect_eq subsetCE \<F>)
        moreover have "\<Inter>\<F> \<subseteq> K"
          using False that(2) by fastforce
        moreover have opeKF: "openin (subtopology euclidean K) (\<Inter>\<F>)"
          using False \<F> \<open>finite \<F>\<close> by blast
        then have opeVF: "openin (subtopology euclidean V) (\<Inter>\<F>)"
          using W \<open>K \<subseteq> S\<close> \<open>V \<subseteq> K\<close> opeKF \<open>\<Inter>\<F> \<subseteq> K\<close> FUW openin_subset_trans by fastforce
        then have "openin (subtopology euclidean S) (\<Inter>\<F>)"
          by (metis opeSV openin_trans)
        moreover have "\<Inter>\<F> \<subseteq> U"
          by (meson \<open>V \<subseteq> U\<close> opeVF dual_order.trans openin_imp_subset)
        ultimately show False
          using neg by blast
      qed
    qed
  qed (use \<open>open W\<close> \<open>open U\<close> in auto)
  with W Ceq \<open>C \<subseteq> V\<close> \<open>C \<subseteq> U\<close> show False
    by auto
qed


corollary Sura_Bura_clopen_subset_alt:
  fixes S :: "'a::euclidean_space set"
  assumes S: "locally compact S" and C: "C \<in> components S" and "compact C"
      and opeSU: "openin (subtopology euclidean S) U" and "C \<subseteq> U"
  obtains K where "openin (subtopology euclidean S) K" "compact K" "C \<subseteq> K" "K \<subseteq> U"
proof -
  obtain V where "open V" "U = S \<inter> V"
    using opeSU by (auto simp: openin_open)
  with \<open>C \<subseteq> U\<close> have "C \<subseteq> V"
    by auto
  then show ?thesis
    using Sura_Bura_clopen_subset [OF S C \<open>compact C\<close> \<open>open V\<close>]
    by (metis \<open>U = S \<inter> V\<close> inf.bounded_iff openin_imp_subset that)
qed

corollary Sura_Bura:
  fixes S :: "'a::euclidean_space set"
  assumes "locally compact S" "C \<in> components S" "compact C"
  shows "C = \<Inter> {K. C \<subseteq> K \<and> compact K \<and> openin (subtopology euclidean S) K}"
         (is "C = ?rhs")
proof
  show "?rhs \<subseteq> C"
  proof (clarsimp, rule ccontr)
    fix x
    assume *: "\<forall>X. C \<subseteq> X \<and> compact X \<and> openin (subtopology euclidean S) X \<longrightarrow> x \<in> X"
      and "x \<notin> C"
    obtain U V where "open U" "open V" "{x} \<subseteq> U" "C \<subseteq> V" "U \<inter> V = {}"
      using separation_normal [of "{x}" C]
      by (metis Int_empty_left \<open>x \<notin> C\<close> \<open>compact C\<close> closed_empty closed_insert compact_imp_closed insert_disjoint(1))
    have "x \<notin> V"
      using \<open>U \<inter> V = {}\<close> \<open>{x} \<subseteq> U\<close> by blast
    then show False
      by (meson "*" Sura_Bura_clopen_subset \<open>C \<subseteq> V\<close> \<open>open V\<close> assms(1) assms(2) assms(3) subsetCE)
  qed
qed blast


subsection\<open>Important special cases of local connectedness and path connectedness\<close>

lemma locally_connected_1:
  assumes
    "\<And>v x. \<lbrakk>openin (subtopology euclidean S) v; x \<in> v\<rbrakk>
              \<Longrightarrow> \<exists>u. openin (subtopology euclidean S) u \<and>
                      connected u \<and> x \<in> u \<and> u \<subseteq> v"
   shows "locally connected S"
apply (clarsimp simp add: locally_def)
apply (drule assms; blast)
done

lemma locally_connected_2:
  assumes "locally connected S"
          "openin (subtopology euclidean S) t"
          "x \<in> t"
   shows "openin (subtopology euclidean S) (connected_component_set t x)"
proof -
  { fix y :: 'a
    let ?SS = "subtopology euclidean S"
    assume 1: "openin ?SS t"
              "\<forall>w x. openin ?SS w \<and> x \<in> w \<longrightarrow> (\<exists>u. openin ?SS u \<and> (\<exists>v. connected v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> w))"
    and "connected_component t x y"
    then have "y \<in> t" and y: "y \<in> connected_component_set t x"
      using connected_component_subset by blast+
    obtain F where
      "\<forall>x y. (\<exists>w. openin ?SS w \<and> (\<exists>u. connected u \<and> x \<in> w \<and> w \<subseteq> u \<and> u \<subseteq> y)) = (openin ?SS (F x y) \<and> (\<exists>u. connected u \<and> x \<in> F x y \<and> F x y \<subseteq> u \<and> u \<subseteq> y))"
      by moura
    then obtain G where
       "\<forall>a A. (\<exists>U. openin ?SS U \<and> (\<exists>V. connected V \<and> a \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> A)) = (openin ?SS (F a A) \<and> connected (G a A) \<and> a \<in> F a A \<and> F a A \<subseteq> G a A \<and> G a A \<subseteq> A)"
      by moura
    then have *: "openin ?SS (F y t) \<and> connected (G y t) \<and> y \<in> F y t \<and> F y t \<subseteq> G y t \<and> G y t \<subseteq> t"
      using 1 \<open>y \<in> t\<close> by presburger
    have "G y t \<subseteq> connected_component_set t y"
      by (metis (no_types) * connected_component_eq_self connected_component_mono contra_subsetD)
    then have "\<exists>A. openin ?SS A \<and> y \<in> A \<and> A \<subseteq> connected_component_set t x"
      by (metis (no_types) * connected_component_eq dual_order.trans y)
  }
  then show ?thesis
    using assms openin_subopen by (force simp: locally_def)
qed

lemma locally_connected_3:
  assumes "\<And>t x. \<lbrakk>openin (subtopology euclidean S) t; x \<in> t\<rbrakk>
              \<Longrightarrow> openin (subtopology euclidean S)
                          (connected_component_set t x)"
          "openin (subtopology euclidean S) v" "x \<in> v"
   shows  "\<exists>u. openin (subtopology euclidean S) u \<and> connected u \<and> x \<in> u \<and> u \<subseteq> v"
using assms connected_component_subset by fastforce

lemma locally_connected:
  "locally connected S \<longleftrightarrow>
   (\<forall>v x. openin (subtopology euclidean S) v \<and> x \<in> v
          \<longrightarrow> (\<exists>u. openin (subtopology euclidean S) u \<and> connected u \<and> x \<in> u \<and> u \<subseteq> v))"
by (metis locally_connected_1 locally_connected_2 locally_connected_3)

lemma locally_connected_open_connected_component:
  "locally connected S \<longleftrightarrow>
   (\<forall>t x. openin (subtopology euclidean S) t \<and> x \<in> t
          \<longrightarrow> openin (subtopology euclidean S) (connected_component_set t x))"
by (metis locally_connected_1 locally_connected_2 locally_connected_3)

lemma locally_path_connected_1:
  assumes
    "\<And>v x. \<lbrakk>openin (subtopology euclidean S) v; x \<in> v\<rbrakk>
              \<Longrightarrow> \<exists>u. openin (subtopology euclidean S) u \<and> path_connected u \<and> x \<in> u \<and> u \<subseteq> v"
   shows "locally path_connected S"
apply (clarsimp simp add: locally_def)
apply (drule assms; blast)
done

lemma locally_path_connected_2:
  assumes "locally path_connected S"
          "openin (subtopology euclidean S) t"
          "x \<in> t"
   shows "openin (subtopology euclidean S) (path_component_set t x)"
proof -
  { fix y :: 'a
    let ?SS = "subtopology euclidean S"
    assume 1: "openin ?SS t"
              "\<forall>w x. openin ?SS w \<and> x \<in> w \<longrightarrow> (\<exists>u. openin ?SS u \<and> (\<exists>v. path_connected v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> w))"
    and "path_component t x y"
    then have "y \<in> t" and y: "y \<in> path_component_set t x"
      using path_component_mem(2) by blast+
    obtain F where
      "\<forall>x y. (\<exists>w. openin ?SS w \<and> (\<exists>u. path_connected u \<and> x \<in> w \<and> w \<subseteq> u \<and> u \<subseteq> y)) = (openin ?SS (F x y) \<and> (\<exists>u. path_connected u \<and> x \<in> F x y \<and> F x y \<subseteq> u \<and> u \<subseteq> y))"
      by moura
    then obtain G where
       "\<forall>a A. (\<exists>U. openin ?SS U \<and> (\<exists>V. path_connected V \<and> a \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> A)) = (openin ?SS (F a A) \<and> path_connected (G a A) \<and> a \<in> F a A \<and> F a A \<subseteq> G a A \<and> G a A \<subseteq> A)"
      by moura
    then have *: "openin ?SS (F y t) \<and> path_connected (G y t) \<and> y \<in> F y t \<and> F y t \<subseteq> G y t \<and> G y t \<subseteq> t"
      using 1 \<open>y \<in> t\<close> by presburger
    have "G y t \<subseteq> path_component_set t y"
      using * path_component_maximal set_rev_mp by blast
    then have "\<exists>A. openin ?SS A \<and> y \<in> A \<and> A \<subseteq> path_component_set t x"
      by (metis "*" \<open>G y t \<subseteq> path_component_set t y\<close> dual_order.trans path_component_eq y)
  }
  then show ?thesis
    using assms openin_subopen by (force simp: locally_def)
qed

lemma locally_path_connected_3:
  assumes "\<And>t x. \<lbrakk>openin (subtopology euclidean S) t; x \<in> t\<rbrakk>
              \<Longrightarrow> openin (subtopology euclidean S) (path_component_set t x)"
          "openin (subtopology euclidean S) v" "x \<in> v"
   shows  "\<exists>u. openin (subtopology euclidean S) u \<and> path_connected u \<and> x \<in> u \<and> u \<subseteq> v"
proof -
  have "path_component v x x"
    by (meson assms(3) path_component_refl)
  then show ?thesis
    by (metis assms(1) assms(2) assms(3) mem_Collect_eq path_component_subset path_connected_path_component)
qed

proposition locally_path_connected:
  "locally path_connected S \<longleftrightarrow>
   (\<forall>v x. openin (subtopology euclidean S) v \<and> x \<in> v
          \<longrightarrow> (\<exists>u. openin (subtopology euclidean S) u \<and> path_connected u \<and> x \<in> u \<and> u \<subseteq> v))"
by (metis locally_path_connected_1 locally_path_connected_2 locally_path_connected_3)

proposition locally_path_connected_open_path_component:
  "locally path_connected S \<longleftrightarrow>
   (\<forall>t x. openin (subtopology euclidean S) t \<and> x \<in> t
          \<longrightarrow> openin (subtopology euclidean S) (path_component_set t x))"
by (metis locally_path_connected_1 locally_path_connected_2 locally_path_connected_3)

lemma locally_connected_open_component:
  "locally connected S \<longleftrightarrow>
   (\<forall>t c. openin (subtopology euclidean S) t \<and> c \<in> components t
          \<longrightarrow> openin (subtopology euclidean S) c)"
by (metis components_iff locally_connected_open_connected_component)

proposition locally_connected_im_kleinen:
  "locally connected S \<longleftrightarrow>
   (\<forall>v x. openin (subtopology euclidean S) v \<and> x \<in> v
       \<longrightarrow> (\<exists>u. openin (subtopology euclidean S) u \<and>
                x \<in> u \<and> u \<subseteq> v \<and>
                (\<forall>y. y \<in> u \<longrightarrow> (\<exists>c. connected c \<and> c \<subseteq> v \<and> x \<in> c \<and> y \<in> c))))"
   (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (fastforce simp add: locally_connected)
next
  assume ?rhs
  have *: "\<exists>T. openin (subtopology euclidean S) T \<and> x \<in> T \<and> T \<subseteq> c"
       if "openin (subtopology euclidean S) t" and c: "c \<in> components t" and "x \<in> c" for t c x
  proof -
    from that \<open>?rhs\<close> [rule_format, of t x]
    obtain u where u:
      "openin (subtopology euclidean S) u \<and> x \<in> u \<and> u \<subseteq> t \<and>
       (\<forall>y. y \<in> u \<longrightarrow> (\<exists>c. connected c \<and> c \<subseteq> t \<and> x \<in> c \<and> y \<in> c))"
      using in_components_subset by auto
    obtain F :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
      "\<forall>x y. (\<exists>z. z \<in> x \<and> y = connected_component_set x z) = (F x y \<in> x \<and> y = connected_component_set x (F x y))"
      by moura
    then have F: "F t c \<in> t \<and> c = connected_component_set t (F t c)"
      by (meson components_iff c)
    obtain G :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
        G: "\<forall>x y. (\<exists>z. z \<in> y \<and> z \<notin> x) = (G x y \<in> y \<and> G x y \<notin> x)"
      by moura
     have "G c u \<notin> u \<or> G c u \<in> c"
      using F by (metis (full_types) u connected_componentI connected_component_eq mem_Collect_eq that(3))
    then show ?thesis
      using G u by auto
  qed
  show ?lhs
    apply (clarsimp simp add: locally_connected_open_component)
    apply (subst openin_subopen)
    apply (blast intro: *)
    done
qed

proposition locally_path_connected_im_kleinen:
  "locally path_connected S \<longleftrightarrow>
   (\<forall>v x. openin (subtopology euclidean S) v \<and> x \<in> v
       \<longrightarrow> (\<exists>u. openin (subtopology euclidean S) u \<and>
                x \<in> u \<and> u \<subseteq> v \<and>
                (\<forall>y. y \<in> u \<longrightarrow> (\<exists>p. path p \<and> path_image p \<subseteq> v \<and>
                                pathstart p = x \<and> pathfinish p = y))))"
   (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (simp add: locally_path_connected path_connected_def)
    apply (erule all_forward ex_forward imp_forward conjE | simp)+
    by (meson dual_order.trans)
next
  assume ?rhs
  have *: "\<exists>T. openin (subtopology euclidean S) T \<and>
               x \<in> T \<and> T \<subseteq> path_component_set u z"
       if "openin (subtopology euclidean S) u" and "z \<in> u" and c: "path_component u z x" for u z x
  proof -
    have "x \<in> u"
      by (meson c path_component_mem(2))
    with that \<open>?rhs\<close> [rule_format, of u x]
    obtain U where U:
      "openin (subtopology euclidean S) U \<and> x \<in> U \<and> U \<subseteq> u \<and>
       (\<forall>y. y \<in> U \<longrightarrow> (\<exists>p. path p \<and> path_image p \<subseteq> u \<and> pathstart p = x \<and> pathfinish p = y))"
       by blast
    show ?thesis
      apply (rule_tac x=U in exI)
      apply (auto simp: U)
      apply (metis U c path_component_trans path_component_def)
      done
  qed
  show ?lhs
    apply (clarsimp simp add: locally_path_connected_open_path_component)
    apply (subst openin_subopen)
    apply (blast intro: *)
    done
qed

lemma locally_path_connected_imp_locally_connected:
  "locally path_connected S \<Longrightarrow> locally connected S"
using locally_mono path_connected_imp_connected by blast

lemma locally_connected_components:
  "\<lbrakk>locally connected S; c \<in> components S\<rbrakk> \<Longrightarrow> locally connected c"
by (meson locally_connected_open_component locally_open_subset openin_subtopology_self)

lemma locally_path_connected_components:
  "\<lbrakk>locally path_connected S; c \<in> components S\<rbrakk> \<Longrightarrow> locally path_connected c"
by (meson locally_connected_open_component locally_open_subset locally_path_connected_imp_locally_connected openin_subtopology_self)

lemma locally_path_connected_connected_component:
  "locally path_connected S \<Longrightarrow> locally path_connected (connected_component_set S x)"
by (metis components_iff connected_component_eq_empty locally_empty locally_path_connected_components)

lemma open_imp_locally_path_connected:
  fixes S :: "'a :: real_normed_vector set"
  shows "open S \<Longrightarrow> locally path_connected S"
apply (rule locally_mono [of convex])
apply (simp_all add: locally_def openin_open_eq convex_imp_path_connected)
apply (meson open_ball centre_in_ball convex_ball openE order_trans)
done

lemma open_imp_locally_connected:
  fixes S :: "'a :: real_normed_vector set"
  shows "open S \<Longrightarrow> locally connected S"
by (simp add: locally_path_connected_imp_locally_connected open_imp_locally_path_connected)

lemma locally_path_connected_UNIV: "locally path_connected (UNIV::'a :: real_normed_vector set)"
  by (simp add: open_imp_locally_path_connected)

lemma locally_connected_UNIV: "locally connected (UNIV::'a :: real_normed_vector set)"
  by (simp add: open_imp_locally_connected)

lemma openin_connected_component_locally_connected:
    "locally connected S
     \<Longrightarrow> openin (subtopology euclidean S) (connected_component_set S x)"
apply (simp add: locally_connected_open_connected_component)
by (metis connected_component_eq_empty connected_component_subset open_empty open_subset openin_subtopology_self)

lemma openin_components_locally_connected:
    "\<lbrakk>locally connected S; c \<in> components S\<rbrakk> \<Longrightarrow> openin (subtopology euclidean S) c"
  using locally_connected_open_component openin_subtopology_self by blast

lemma openin_path_component_locally_path_connected:
  "locally path_connected S
        \<Longrightarrow> openin (subtopology euclidean S) (path_component_set S x)"
by (metis (no_types) empty_iff locally_path_connected_2 openin_subopen openin_subtopology_self path_component_eq_empty)

lemma closedin_path_component_locally_path_connected:
    "locally path_connected S
        \<Longrightarrow> closedin (subtopology euclidean S) (path_component_set S x)"
apply  (simp add: closedin_def path_component_subset complement_path_component_Union)
apply (rule openin_Union)
using openin_path_component_locally_path_connected by auto

lemma convex_imp_locally_path_connected:
  fixes S :: "'a:: real_normed_vector set"
  shows "convex S \<Longrightarrow> locally path_connected S"
apply (clarsimp simp add: locally_path_connected)
apply (subst (asm) openin_open)
apply clarify
apply (erule (1) openE)
apply (rule_tac x = "S \<inter> ball x e" in exI)
apply (force simp: convex_Int convex_imp_path_connected)
done

lemma convex_imp_locally_connected:
  fixes S :: "'a:: real_normed_vector set"
  shows "convex S \<Longrightarrow> locally connected S"
  by (simp add: locally_path_connected_imp_locally_connected convex_imp_locally_path_connected)


subsection\<open>Relations between components and path components\<close>

lemma path_component_eq_connected_component:
  assumes "locally path_connected S"
    shows "(path_component S x = connected_component S x)"
proof (cases "x \<in> S")
  case True
  have "openin (subtopology euclidean (connected_component_set S x)) (path_component_set S x)"
    apply (rule openin_subset_trans [of S])
    apply (intro conjI openin_path_component_locally_path_connected [OF assms])
    using path_component_subset_connected_component   apply (auto simp: connected_component_subset)
    done
  moreover have "closedin (subtopology euclidean (connected_component_set S x)) (path_component_set S x)"
    apply (rule closedin_subset_trans [of S])
    apply (intro conjI closedin_path_component_locally_path_connected [OF assms])
    using path_component_subset_connected_component   apply (auto simp: connected_component_subset)
    done
  ultimately have *: "path_component_set S x = connected_component_set S x"
    by (metis connected_connected_component connected_clopen True path_component_eq_empty)
  then show ?thesis
    by blast
next
  case False then show ?thesis
    by (metis Collect_empty_eq_bot connected_component_eq_empty path_component_eq_empty)
qed

lemma path_component_eq_connected_component_set:
     "locally path_connected S \<Longrightarrow> (path_component_set S x = connected_component_set S x)"
by (simp add: path_component_eq_connected_component)

lemma locally_path_connected_path_component:
     "locally path_connected S \<Longrightarrow> locally path_connected (path_component_set S x)"
using locally_path_connected_connected_component path_component_eq_connected_component by fastforce

lemma open_path_connected_component:
  fixes S :: "'a :: real_normed_vector set"
  shows "open S \<Longrightarrow> path_component S x = connected_component S x"
by (simp add: path_component_eq_connected_component open_imp_locally_path_connected)

lemma open_path_connected_component_set:
  fixes S :: "'a :: real_normed_vector set"
  shows "open S \<Longrightarrow> path_component_set S x = connected_component_set S x"
by (simp add: open_path_connected_component)

proposition locally_connected_quotient_image:
  assumes lcS: "locally connected S"
      and oo: "\<And>T. T \<subseteq> f ` S
                \<Longrightarrow> openin (subtopology euclidean S) (S \<inter> f -` T) \<longleftrightarrow>
                    openin (subtopology euclidean (f ` S)) T"
    shows "locally connected (f ` S)"
proof (clarsimp simp: locally_connected_open_component)
  fix U C
  assume opefSU: "openin (subtopology euclidean (f ` S)) U" and "C \<in> components U"
  then have "C \<subseteq> U" "U \<subseteq> f ` S"
    by (meson in_components_subset openin_imp_subset)+
  then have "openin (subtopology euclidean (f ` S)) C \<longleftrightarrow>
             openin (subtopology euclidean S) (S \<inter> f -` C)"
    by (auto simp: oo)
  moreover have "openin (subtopology euclidean S) (S \<inter> f -` C)"
  proof (subst openin_subopen, clarify)
    fix x
    assume "x \<in> S" "f x \<in> C"
    show "\<exists>T. openin (subtopology euclidean S) T \<and> x \<in> T \<and> T \<subseteq> (S \<inter> f -` C)"
    proof (intro conjI exI)
      show "openin (subtopology euclidean S) (connected_component_set (S \<inter> f -` U) x)"
      proof (rule ccontr)
        assume **: "\<not> openin (subtopology euclidean S) (connected_component_set (S \<inter> f -` U) x)"
        then have "x \<notin> (S \<inter> f -` U)"
          using \<open>U \<subseteq> f ` S\<close> opefSU lcS locally_connected_2 oo by blast
        with ** show False
          by (metis (no_types) connected_component_eq_empty empty_iff openin_subopen)
      qed
    next
      show "x \<in> connected_component_set (S \<inter> f -` U) x"
        using \<open>C \<subseteq> U\<close> \<open>f x \<in> C\<close> \<open>x \<in> S\<close> by auto
    next
      have contf: "continuous_on S f"
        by (simp add: continuous_on_open oo openin_imp_subset)
      then have "continuous_on (connected_component_set (S \<inter> f -` U) x) f"
        apply (rule continuous_on_subset)
        using connected_component_subset apply blast
        done
      then have "connected (f ` connected_component_set (S \<inter> f -` U) x)"
        by (rule connected_continuous_image [OF _ connected_connected_component])
      moreover have "f ` connected_component_set (S \<inter> f -` U) x \<subseteq> U"
        using connected_component_in by blast
      moreover have "C \<inter> f ` connected_component_set (S \<inter> f -` U) x \<noteq> {}"
        using \<open>C \<subseteq> U\<close> \<open>f x \<in> C\<close> \<open>x \<in> S\<close> by fastforce
      ultimately have fC: "f ` (connected_component_set (S \<inter> f -` U) x) \<subseteq> C"
        by (rule components_maximal [OF \<open>C \<in> components U\<close>])
      have cUC: "connected_component_set (S \<inter> f -` U) x \<subseteq> (S \<inter> f -` C)"
        using connected_component_subset fC by blast
      have "connected_component_set (S \<inter> f -` U) x \<subseteq> connected_component_set (S \<inter> f -` C) x"
      proof -
        { assume "x \<in> connected_component_set (S \<inter> f -` U) x"
          then have ?thesis
            using cUC connected_component_idemp connected_component_mono by blast }
        then show ?thesis
          using connected_component_eq_empty by auto
      qed
      also have "... \<subseteq> (S \<inter> f -` C)"
        by (rule connected_component_subset)
      finally show "connected_component_set (S \<inter> f -` U) x \<subseteq> (S \<inter> f -` C)" .
    qed
  qed
  ultimately show "openin (subtopology euclidean (f ` S)) C"
    by metis
qed

text\<open>The proof resembles that above but is not identical!\<close>
proposition locally_path_connected_quotient_image:
  assumes lcS: "locally path_connected S"
      and oo: "\<And>T. T \<subseteq> f ` S
                \<Longrightarrow> openin (subtopology euclidean S) (S \<inter> f -` T) \<longleftrightarrow> openin (subtopology euclidean (f ` S)) T"
    shows "locally path_connected (f ` S)"
proof (clarsimp simp: locally_path_connected_open_path_component)
  fix U y
  assume opefSU: "openin (subtopology euclidean (f ` S)) U" and "y \<in> U"
  then have "path_component_set U y \<subseteq> U" "U \<subseteq> f ` S"
    by (meson path_component_subset openin_imp_subset)+
  then have "openin (subtopology euclidean (f ` S)) (path_component_set U y) \<longleftrightarrow>
             openin (subtopology euclidean S) (S \<inter> f -` path_component_set U y)"
  proof -
    have "path_component_set U y \<subseteq> f ` S"
      using \<open>U \<subseteq> f ` S\<close> \<open>path_component_set U y \<subseteq> U\<close> by blast
    then show ?thesis
      using oo by blast
  qed
  moreover have "openin (subtopology euclidean S) (S \<inter> f -` path_component_set U y)"
  proof (subst openin_subopen, clarify)
    fix x
    assume "x \<in> S" and Uyfx: "path_component U y (f x)"
    then have "f x \<in> U"
      using path_component_mem by blast
    show "\<exists>T. openin (subtopology euclidean S) T \<and> x \<in> T \<and> T \<subseteq> (S \<inter> f -` path_component_set U y)"
    proof (intro conjI exI)
      show "openin (subtopology euclidean S) (path_component_set (S \<inter> f -` U) x)"
      proof (rule ccontr)
        assume **: "\<not> openin (subtopology euclidean S) (path_component_set (S \<inter> f -` U) x)"
        then have "x \<notin> (S \<inter> f -` U)"
          by (metis (no_types, lifting) \<open>U \<subseteq> f ` S\<close> opefSU lcS oo locally_path_connected_open_path_component)
        then show False
          using ** \<open>path_component_set U y \<subseteq> U\<close>  \<open>x \<in> S\<close> \<open>path_component U y (f x)\<close> by blast
      qed
    next
      show "x \<in> path_component_set (S \<inter> f -` U) x"
        by (simp add: \<open>f x \<in> U\<close> \<open>x \<in> S\<close> path_component_refl)
    next
      have contf: "continuous_on S f"
        by (simp add: continuous_on_open oo openin_imp_subset)
      then have "continuous_on (path_component_set (S \<inter> f -` U) x) f"
        apply (rule continuous_on_subset)
        using path_component_subset apply blast
        done
      then have "path_connected (f ` path_component_set (S \<inter> f -` U) x)"
        by (simp add: path_connected_continuous_image)
      moreover have "f ` path_component_set (S \<inter> f -` U) x \<subseteq> U"
        using path_component_mem by fastforce
      moreover have "f x \<in> f ` path_component_set (S \<inter> f -` U) x"
        by (force simp: \<open>x \<in> S\<close> \<open>f x \<in> U\<close> path_component_refl_eq)
      ultimately have "f ` (path_component_set (S \<inter> f -` U) x) \<subseteq> path_component_set U (f x)"
        by (meson path_component_maximal)
       also have  "... \<subseteq> path_component_set U y"
        by (simp add: Uyfx path_component_maximal path_component_subset path_component_sym)
      finally have fC: "f ` (path_component_set (S \<inter> f -` U) x) \<subseteq> path_component_set U y" .
      have cUC: "path_component_set (S \<inter> f -` U) x \<subseteq> (S \<inter> f -` path_component_set U y)"
        using path_component_subset fC by blast
      have "path_component_set (S \<inter> f -` U) x \<subseteq> path_component_set (S \<inter> f -` path_component_set U y) x"
      proof -
        have "\<And>a. path_component_set (path_component_set (S \<inter> f -` U) x) a \<subseteq> path_component_set (S \<inter> f -` path_component_set U y) a"
          using cUC path_component_mono by blast
        then show ?thesis
          using path_component_path_component by blast
      qed
      also have "... \<subseteq> (S \<inter> f -` path_component_set U y)"
        by (rule path_component_subset)
      finally show "path_component_set (S \<inter> f -` U) x \<subseteq> (S \<inter> f -` path_component_set U y)" .
    qed
  qed
  ultimately show "openin (subtopology euclidean (f ` S)) (path_component_set U y)"
    by metis
qed

subsection\<open>Components, continuity, openin, closedin\<close>

lemma continuous_on_components_gen:
 fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes "\<And>c. c \<in> components S \<Longrightarrow>
              openin (subtopology euclidean S) c \<and> continuous_on c f"
    shows "continuous_on S f"
proof (clarsimp simp: continuous_openin_preimage_eq)
  fix t :: "'b set"
  assume "open t"
  have *: "S \<inter> f -` t = (\<Union>c \<in> components S. c \<inter> f -` t)"
    by auto
  show "openin (subtopology euclidean S) (S \<inter> f -` t)"
    unfolding * using \<open>open t\<close> assms continuous_openin_preimage_gen openin_trans openin_Union by blast
qed

lemma continuous_on_components:
 fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes "locally connected S "
          "\<And>c. c \<in> components S \<Longrightarrow> continuous_on c f"
    shows "continuous_on S f"
apply (rule continuous_on_components_gen)
apply (auto simp: assms intro: openin_components_locally_connected)
done

lemma continuous_on_components_eq:
    "locally connected S
     \<Longrightarrow> (continuous_on S f \<longleftrightarrow> (\<forall>c \<in> components S. continuous_on c f))"
by (meson continuous_on_components continuous_on_subset in_components_subset)

lemma continuous_on_components_open:
 fixes S :: "'a::real_normed_vector set"
  assumes "open S "
          "\<And>c. c \<in> components S \<Longrightarrow> continuous_on c f"
    shows "continuous_on S f"
using continuous_on_components open_imp_locally_connected assms by blast

lemma continuous_on_components_open_eq:
  fixes S :: "'a::real_normed_vector set"
  shows "open S \<Longrightarrow> (continuous_on S f \<longleftrightarrow> (\<forall>c \<in> components S. continuous_on c f))"
using continuous_on_subset in_components_subset
by (blast intro: continuous_on_components_open)

lemma closedin_union_complement_components:
  assumes u: "locally connected u"
      and S: "closedin (subtopology euclidean u) S"
      and cuS: "c \<subseteq> components(u - S)"
    shows "closedin (subtopology euclidean u) (S \<union> \<Union>c)"
proof -
  have di: "(\<And>S t. S \<in> c \<and> t \<in> c' \<Longrightarrow> disjnt S t) \<Longrightarrow> disjnt (\<Union> c) (\<Union> c')" for c'
    by (simp add: disjnt_def) blast
  have "S \<subseteq> u"
    using S closedin_imp_subset by blast
  moreover have "u - S = \<Union>c \<union> \<Union>(components (u - S) - c)"
    by (metis Diff_partition Union_components Union_Un_distrib assms(3))
  moreover have "disjnt (\<Union>c) (\<Union>(components (u - S) - c))"
    apply (rule di)
    by (metis DiffD1 DiffD2 assms(3) components_nonoverlap disjnt_def subsetCE)
  ultimately have eq: "S \<union> \<Union>c = u - (\<Union>(components(u - S) - c))"
    by (auto simp: disjnt_def)
  have *: "openin (subtopology euclidean u) (\<Union>(components (u - S) - c))"
    apply (rule openin_Union)
    apply (rule openin_trans [of "u - S"])
    apply (simp add: u S locally_diff_closed openin_components_locally_connected)
    apply (simp add: openin_diff S)
    done
  have "openin (subtopology euclidean u) (u - (u - \<Union>(components (u - S) - c)))"
    apply (rule openin_diff, simp)
    apply (metis closedin_diff closedin_topspace topspace_euclidean_subtopology *)
    done
  then show ?thesis
    by (force simp: eq closedin_def)
qed

lemma closed_union_complement_components:
  fixes S :: "'a::real_normed_vector set"
  assumes S: "closed S" and c: "c \<subseteq> components(- S)"
    shows "closed(S \<union> \<Union> c)"
proof -
  have "closedin (subtopology euclidean UNIV) (S \<union> \<Union>c)"
    apply (rule closedin_union_complement_components [OF locally_connected_UNIV])
    using S c apply (simp_all add: Compl_eq_Diff_UNIV)
    done
  then show ?thesis by simp
qed

lemma closedin_Un_complement_component:
  fixes S :: "'a::real_normed_vector set"
  assumes u: "locally connected u"
      and S: "closedin (subtopology euclidean u) S"
      and c: " c \<in> components(u - S)"
    shows "closedin (subtopology euclidean u) (S \<union> c)"
proof -
  have "closedin (subtopology euclidean u) (S \<union> \<Union>{c})"
    using c by (blast intro: closedin_union_complement_components [OF u S])
  then show ?thesis
    by simp
qed

lemma closed_Un_complement_component:
  fixes S :: "'a::real_normed_vector set"
  assumes S: "closed S" and c: " c \<in> components(-S)"
    shows "closed (S \<union> c)"
by (metis Compl_eq_Diff_UNIV S c closed_closedin closedin_Un_complement_component locally_connected_UNIV subtopology_UNIV)


subsection\<open>Existence of isometry between subspaces of same dimension\<close>

lemma isometry_subset_subspace:
  fixes S :: "'a::euclidean_space set"
    and T :: "'b::euclidean_space set"
  assumes S: "subspace S"
      and T: "subspace T"
      and d: "dim S \<le> dim T"
  obtains f where "linear f" "f ` S \<subseteq> T" "\<And>x. x \<in> S \<Longrightarrow> norm(f x) = norm x"
proof -
  obtain B where "B \<subseteq> S" and Borth: "pairwise orthogonal B"
             and B1: "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
             and "independent B" "finite B" "card B = dim S" "span B = S"
    by (metis orthonormal_basis_subspace [OF S] independent_finite)
  obtain C where "C \<subseteq> T" and Corth: "pairwise orthogonal C"
             and C1:"\<And>x. x \<in> C \<Longrightarrow> norm x = 1"
             and "independent C" "finite C" "card C = dim T" "span C = T"
    by (metis orthonormal_basis_subspace [OF T] independent_finite)
  obtain fb where "fb ` B \<subseteq> C" "inj_on fb B"
    by (metis \<open>card B = dim S\<close> \<open>card C = dim T\<close> \<open>finite B\<close> \<open>finite C\<close> card_le_inj d)
  then have pairwise_orth_fb: "pairwise (\<lambda>v j. orthogonal (fb v) (fb j)) B"
    using Corth
    apply (auto simp: pairwise_def orthogonal_clauses)
    by (meson subsetD image_eqI inj_on_def)
  obtain f where "linear f" and ffb: "\<And>x. x \<in> B \<Longrightarrow> f x = fb x"
    using linear_independent_extend \<open>independent B\<close> by fastforce
  have "f ` S \<subseteq> T"
    by (metis ffb \<open>fb ` B \<subseteq> C\<close> \<open>linear f\<close> \<open>span B = S\<close> \<open>span C = T\<close> image_cong span_linear_image span_mono)
  have [simp]: "\<And>x. x \<in> B \<Longrightarrow> norm (fb x) = norm x"
    using B1 C1 \<open>fb ` B \<subseteq> C\<close> by auto
  have "norm (f x) = norm x" if "x \<in> S" for x
  proof -
    obtain a where x: "x = (\<Sum>v \<in> B. a v *\<^sub>R v)"
      using \<open>finite B\<close> \<open>span B = S\<close> \<open>x \<in> S\<close> span_finite by fastforce
    have "f x = (\<Sum>v \<in> B. f (a v *\<^sub>R v))"
      using linear_sum [OF \<open>linear f\<close>] x by auto
    also have "... = (\<Sum>v \<in> B. a v *\<^sub>R f v)"
      using \<open>linear f\<close> by (simp add: linear_sum linear.scaleR)
    also have "... = (\<Sum>v \<in> B. a v *\<^sub>R fb v)"
      by (simp add: ffb cong: sum.cong)
    finally have "norm (f x)^2 = norm (\<Sum>v\<in>B. a v *\<^sub>R fb v)^2" by simp
    also have "... = (\<Sum>v\<in>B. norm ((a v *\<^sub>R fb v))^2)"
      apply (rule norm_sum_Pythagorean [OF \<open>finite B\<close>])
      apply (rule pairwise_ortho_scaleR [OF pairwise_orth_fb])
      done
    also have "... = norm x ^2"
      by (simp add: x pairwise_ortho_scaleR Borth norm_sum_Pythagorean [OF \<open>finite B\<close>])
    finally show ?thesis
      by (simp add: norm_eq_sqrt_inner)
  qed
  then show ?thesis
    by (rule that [OF \<open>linear f\<close> \<open>f ` S \<subseteq> T\<close>])
qed

proposition isometries_subspaces:
  fixes S :: "'a::euclidean_space set"
    and T :: "'b::euclidean_space set"
  assumes S: "subspace S"
      and T: "subspace T"
      and d: "dim S = dim T"
  obtains f g where "linear f" "linear g" "f ` S = T" "g ` T = S"
                    "\<And>x. x \<in> S \<Longrightarrow> norm(f x) = norm x"
                    "\<And>x. x \<in> T \<Longrightarrow> norm(g x) = norm x"
                    "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x"
                    "\<And>x. x \<in> T \<Longrightarrow> f(g x) = x"
proof -
  obtain B where "B \<subseteq> S" and Borth: "pairwise orthogonal B"
             and B1: "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
             and "independent B" "finite B" "card B = dim S" "span B = S"
    by (metis orthonormal_basis_subspace [OF S] independent_finite)
  obtain C where "C \<subseteq> T" and Corth: "pairwise orthogonal C"
             and C1:"\<And>x. x \<in> C \<Longrightarrow> norm x = 1"
             and "independent C" "finite C" "card C = dim T" "span C = T"
    by (metis orthonormal_basis_subspace [OF T] independent_finite)
  obtain fb where "bij_betw fb B C"
    by (metis \<open>finite B\<close> \<open>finite C\<close> bij_betw_iff_card \<open>card B = dim S\<close> \<open>card C = dim T\<close> d)
  then have pairwise_orth_fb: "pairwise (\<lambda>v j. orthogonal (fb v) (fb j)) B"
    using Corth
    apply (auto simp: pairwise_def orthogonal_clauses bij_betw_def)
    by (meson subsetD image_eqI inj_on_def)
  obtain f where "linear f" and ffb: "\<And>x. x \<in> B \<Longrightarrow> f x = fb x"
    using linear_independent_extend \<open>independent B\<close> by fastforce
  define gb where "gb \<equiv> inv_into B fb"
  then have pairwise_orth_gb: "pairwise (\<lambda>v j. orthogonal (gb v) (gb j)) C"
    using Borth
    apply (auto simp: pairwise_def orthogonal_clauses bij_betw_def)
    by (metis \<open>bij_betw fb B C\<close> bij_betw_imp_surj_on bij_betw_inv_into_right inv_into_into)
  obtain g where "linear g" and ggb: "\<And>x. x \<in> C \<Longrightarrow> g x = gb x"
    using linear_independent_extend \<open>independent C\<close> by fastforce
  have "f ` S \<subseteq> T"
    by (metis \<open>bij_betw fb B C\<close> bij_betw_imp_surj_on eq_iff ffb  \<open>linear f\<close> \<open>span B = S\<close> \<open>span C = T\<close> image_cong span_linear_image)
  have [simp]: "\<And>x. x \<in> B \<Longrightarrow> norm (fb x) = norm x"
    using B1 C1 \<open>bij_betw fb B C\<close> bij_betw_imp_surj_on by fastforce
  have f [simp]: "norm (f x) = norm x" "g (f x) = x" if "x \<in> S" for x
  proof -
    obtain a where x: "x = (\<Sum>v \<in> B. a v *\<^sub>R v)"
      using \<open>finite B\<close> \<open>span B = S\<close> \<open>x \<in> S\<close> span_finite by fastforce
    have "f x = (\<Sum>v \<in> B. f (a v *\<^sub>R v))"
      using linear_sum [OF \<open>linear f\<close>] x by auto
    also have "... = (\<Sum>v \<in> B. a v *\<^sub>R f v)"
      using \<open>linear f\<close> by (simp add: linear_sum linear.scaleR)
    also have "... = (\<Sum>v \<in> B. a v *\<^sub>R fb v)"
      by (simp add: ffb cong: sum.cong)
    finally have *: "f x = (\<Sum>v\<in>B. a v *\<^sub>R fb v)" .
    then have "(norm (f x))\<^sup>2 = (norm (\<Sum>v\<in>B. a v *\<^sub>R fb v))\<^sup>2" by simp
    also have "... = (\<Sum>v\<in>B. norm ((a v *\<^sub>R fb v))^2)"
      apply (rule norm_sum_Pythagorean [OF \<open>finite B\<close>])
      apply (rule pairwise_ortho_scaleR [OF pairwise_orth_fb])
      done
    also have "... = (norm x)\<^sup>2"
      by (simp add: x pairwise_ortho_scaleR Borth norm_sum_Pythagorean [OF \<open>finite B\<close>])
    finally show "norm (f x) = norm x"
      by (simp add: norm_eq_sqrt_inner)
    have "g (f x) = g (\<Sum>v\<in>B. a v *\<^sub>R fb v)" by (simp add: *)
    also have "... = (\<Sum>v\<in>B. g (a v *\<^sub>R fb v))"
      using \<open>linear g\<close> by (simp add: linear_sum linear.scaleR)
    also have "... = (\<Sum>v\<in>B. a v *\<^sub>R g (fb v))"
      by (simp add: \<open>linear g\<close> linear.scaleR)
    also have "... = (\<Sum>v\<in>B. a v *\<^sub>R v)"
      apply (rule sum.cong [OF refl])
      using \<open>bij_betw fb B C\<close> gb_def bij_betwE bij_betw_inv_into_left gb_def ggb by fastforce
    also have "... = x"
      using x by blast
    finally show "g (f x) = x" .
  qed
  have [simp]: "\<And>x. x \<in> C \<Longrightarrow> norm (gb x) = norm x"
    by (metis B1 C1 \<open>bij_betw fb B C\<close> bij_betw_imp_surj_on gb_def inv_into_into)
  have g [simp]: "f (g x) = x" if "x \<in> T" for x
  proof -
    obtain a where x: "x = (\<Sum>v \<in> C. a v *\<^sub>R v)"
      using \<open>finite C\<close> \<open>span C = T\<close> \<open>x \<in> T\<close> span_finite by fastforce
    have "g x = (\<Sum>v \<in> C. g (a v *\<^sub>R v))"
      using linear_sum [OF \<open>linear g\<close>] x by auto
    also have "... = (\<Sum>v \<in> C. a v *\<^sub>R g v)"
      using \<open>linear g\<close> by (simp add: linear_sum linear.scaleR)
    also have "... = (\<Sum>v \<in> C. a v *\<^sub>R gb v)"
      by (simp add: ggb cong: sum.cong)
    finally have "f (g x) = f (\<Sum>v\<in>C. a v *\<^sub>R gb v)" by simp
    also have "... = (\<Sum>v\<in>C. f (a v *\<^sub>R gb v))"
      using \<open>linear f\<close> by (simp add: linear_sum linear.scaleR)
    also have "... = (\<Sum>v\<in>C. a v *\<^sub>R f (gb v))"
      by (simp add: \<open>linear f\<close> linear.scaleR)
    also have "... = (\<Sum>v\<in>C. a v *\<^sub>R v)"
      using \<open>bij_betw fb B C\<close>
      by (simp add: bij_betw_def gb_def bij_betw_inv_into_right ffb inv_into_into)
    also have "... = x"
      using x by blast
    finally show "f (g x) = x" .
  qed
  have gim: "g ` T = S"
    by (metis (no_types, lifting) \<open>f ` S \<subseteq> T\<close> \<open>linear g\<close> \<open>span B = S\<close> \<open>span C = T\<close> d dim_eq_span dim_image_le f(2) image_subset_iff span_linear_image span_span subsetI)
  have fim: "f ` S = T"
    using \<open>g ` T = S\<close> image_iff by fastforce
  have [simp]: "norm (g x) = norm x" if "x \<in> T" for x
    using fim that by auto
  show ?thesis
    apply (rule that [OF \<open>linear f\<close> \<open>linear g\<close>])
    apply (simp_all add: fim gim)
    done
qed

corollary isometry_subspaces:
  fixes S :: "'a::euclidean_space set"
    and T :: "'b::euclidean_space set"
  assumes S: "subspace S"
      and T: "subspace T"
      and d: "dim S = dim T"
  obtains f where "linear f" "f ` S = T" "\<And>x. x \<in> S \<Longrightarrow> norm(f x) = norm x"
using isometries_subspaces [OF assms]
by metis

corollary isomorphisms_UNIV_UNIV:
  assumes "DIM('M) = DIM('N)"
  obtains f::"'M::euclidean_space \<Rightarrow>'N::euclidean_space" and g
  where "linear f" "linear g"
                    "\<And>x. norm(f x) = norm x" "\<And>y. norm(g y) = norm y"
                    "\<And>x. g(f x) = x" "\<And>y. f(g y) = y"
  using assms by (auto simp: dim_UNIV intro: isometries_subspaces [of "UNIV::'M set" "UNIV::'N set"])

lemma homeomorphic_subspaces:
  fixes S :: "'a::euclidean_space set"
    and T :: "'b::euclidean_space set"
  assumes S: "subspace S"
      and T: "subspace T"
      and d: "dim S = dim T"
    shows "S homeomorphic T"
proof -
  obtain f g where "linear f" "linear g" "f ` S = T" "g ` T = S"
                   "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x" "\<And>x. x \<in> T \<Longrightarrow> f(g x) = x"
    by (blast intro: isometries_subspaces [OF assms])
  then show ?thesis
    apply (simp add: homeomorphic_def homeomorphism_def)
    apply (rule_tac x=f in exI)
    apply (rule_tac x=g in exI)
    apply (auto simp: linear_continuous_on linear_conv_bounded_linear)
    done
qed

lemma homeomorphic_affine_sets:
  assumes "affine S" "affine T" "aff_dim S = aff_dim T"
    shows "S homeomorphic T"
proof (cases "S = {} \<or> T = {}")
  case True  with assms aff_dim_empty homeomorphic_empty show ?thesis
    by metis
next
  case False
  then obtain a b where ab: "a \<in> S" "b \<in> T" by auto
  then have ss: "subspace (op + (- a) ` S)" "subspace (op + (- b) ` T)"
    using affine_diffs_subspace assms by blast+
  have dd: "dim (op + (- a) ` S) = dim (op + (- b) ` T)"
    using assms ab  by (simp add: aff_dim_eq_dim  [OF hull_inc] image_def)
  have "S homeomorphic (op + (- a) ` S)"
    by (simp add: homeomorphic_translation)
  also have "... homeomorphic (op + (- b) ` T)"
    by (rule homeomorphic_subspaces [OF ss dd])
  also have "... homeomorphic T"
    using homeomorphic_sym homeomorphic_translation by auto
  finally show ?thesis .
qed

subsection\<open>Retracts, in a general sense, preserve (co)homotopic triviality)\<close>

locale Retracts =
  fixes s h t k
  assumes conth: "continuous_on s h"
      and imh: "h ` s = t"
      and contk: "continuous_on t k"
      and imk: "k ` t \<subseteq> s"
      and idhk: "\<And>y. y \<in> t \<Longrightarrow> h(k y) = y"

begin

lemma homotopically_trivial_retraction_gen:
  assumes P: "\<And>f. \<lbrakk>continuous_on u f; f ` u \<subseteq> t; Q f\<rbrakk> \<Longrightarrow> P(k o f)"
      and Q: "\<And>f. \<lbrakk>continuous_on u f; f ` u \<subseteq> s; P f\<rbrakk> \<Longrightarrow> Q(h o f)"
      and Qeq: "\<And>h k. (\<And>x. x \<in> u \<Longrightarrow> h x = k x) \<Longrightarrow> Q h = Q k"
      and hom: "\<And>f g. \<lbrakk>continuous_on u f; f ` u \<subseteq> s; P f;
                       continuous_on u g; g ` u \<subseteq> s; P g\<rbrakk>
                       \<Longrightarrow> homotopic_with P u s f g"
      and contf: "continuous_on u f" and imf: "f ` u \<subseteq> t" and Qf: "Q f"
      and contg: "continuous_on u g" and img: "g ` u \<subseteq> t" and Qg: "Q g"
    shows "homotopic_with Q u t f g"
proof -
  have feq: "\<And>x. x \<in> u \<Longrightarrow> (h \<circ> (k \<circ> f)) x = f x" using idhk imf by auto
  have geq: "\<And>x. x \<in> u \<Longrightarrow> (h \<circ> (k \<circ> g)) x = g x" using idhk img by auto
  have "continuous_on u (k \<circ> f)"
    using contf continuous_on_compose continuous_on_subset contk imf by blast
  moreover have "(k \<circ> f) ` u \<subseteq> s"
    using imf imk by fastforce
  moreover have "P (k \<circ> f)"
    by (simp add: P Qf contf imf)
  moreover have "continuous_on u (k \<circ> g)"
    using contg continuous_on_compose continuous_on_subset contk img by blast
  moreover have "(k \<circ> g) ` u \<subseteq> s"
    using img imk by fastforce
  moreover have "P (k \<circ> g)"
    by (simp add: P Qg contg img)
  ultimately have "homotopic_with P u s (k \<circ> f) (k \<circ> g)"
    by (rule hom)
  then have "homotopic_with Q u t (h \<circ> (k \<circ> f)) (h \<circ> (k \<circ> g))"
    apply (rule homotopic_with_compose_continuous_left [OF homotopic_with_mono])
    using Q by (auto simp: conth imh)
  then show ?thesis
    apply (rule homotopic_with_eq)
    apply (metis feq)
    apply (metis geq)
    apply (metis Qeq)
    done
qed

lemma homotopically_trivial_retraction_null_gen:
  assumes P: "\<And>f. \<lbrakk>continuous_on u f; f ` u \<subseteq> t; Q f\<rbrakk> \<Longrightarrow> P(k o f)"
      and Q: "\<And>f. \<lbrakk>continuous_on u f; f ` u \<subseteq> s; P f\<rbrakk> \<Longrightarrow> Q(h o f)"
      and Qeq: "\<And>h k. (\<And>x. x \<in> u \<Longrightarrow> h x = k x) \<Longrightarrow> Q h = Q k"
      and hom: "\<And>f. \<lbrakk>continuous_on u f; f ` u \<subseteq> s; P f\<rbrakk>
                     \<Longrightarrow> \<exists>c. homotopic_with P u s f (\<lambda>x. c)"
      and contf: "continuous_on u f" and imf:"f ` u \<subseteq> t" and Qf: "Q f"
  obtains c where "homotopic_with Q u t f (\<lambda>x. c)"
proof -
  have feq: "\<And>x. x \<in> u \<Longrightarrow> (h \<circ> (k \<circ> f)) x = f x" using idhk imf by auto
  have "continuous_on u (k \<circ> f)"
    using contf continuous_on_compose continuous_on_subset contk imf by blast
  moreover have "(k \<circ> f) ` u \<subseteq> s"
    using imf imk by fastforce
  moreover have "P (k \<circ> f)"
    by (simp add: P Qf contf imf)
  ultimately obtain c where "homotopic_with P u s (k \<circ> f) (\<lambda>x. c)"
    by (metis hom)
  then have "homotopic_with Q u t (h \<circ> (k \<circ> f)) (h o (\<lambda>x. c))"
    apply (rule homotopic_with_compose_continuous_left [OF homotopic_with_mono])
    using Q by (auto simp: conth imh)
  then show ?thesis
    apply (rule_tac c = "h c" in that)
    apply (erule homotopic_with_eq)
    apply (metis feq, simp)
    apply (metis Qeq)
    done
qed

lemma cohomotopically_trivial_retraction_gen:
  assumes P: "\<And>f. \<lbrakk>continuous_on t f; f ` t \<subseteq> u; Q f\<rbrakk> \<Longrightarrow> P(f o h)"
      and Q: "\<And>f. \<lbrakk>continuous_on s f; f ` s \<subseteq> u; P f\<rbrakk> \<Longrightarrow> Q(f o k)"
      and Qeq: "\<And>h k. (\<And>x. x \<in> t \<Longrightarrow> h x = k x) \<Longrightarrow> Q h = Q k"
      and hom: "\<And>f g. \<lbrakk>continuous_on s f; f ` s \<subseteq> u; P f;
                       continuous_on s g; g ` s \<subseteq> u; P g\<rbrakk>
                       \<Longrightarrow> homotopic_with P s u f g"
      and contf: "continuous_on t f" and imf: "f ` t \<subseteq> u" and Qf: "Q f"
      and contg: "continuous_on t g" and img: "g ` t \<subseteq> u" and Qg: "Q g"
    shows "homotopic_with Q t u f g"
proof -
  have feq: "\<And>x. x \<in> t \<Longrightarrow> (f \<circ> h \<circ> k) x = f x" using idhk imf by auto
  have geq: "\<And>x. x \<in> t \<Longrightarrow> (g \<circ> h \<circ> k) x = g x" using idhk img by auto
  have "continuous_on s (f \<circ> h)"
    using contf conth continuous_on_compose imh by blast
  moreover have "(f \<circ> h) ` s \<subseteq> u"
    using imf imh by fastforce
  moreover have "P (f \<circ> h)"
    by (simp add: P Qf contf imf)
  moreover have "continuous_on s (g o h)"
    using contg continuous_on_compose continuous_on_subset conth imh by blast
  moreover have "(g \<circ> h) ` s \<subseteq> u"
    using img imh by fastforce
  moreover have "P (g \<circ> h)"
    by (simp add: P Qg contg img)
  ultimately have "homotopic_with P s u (f o h) (g \<circ> h)"
    by (rule hom)
  then have "homotopic_with Q t u (f o h o k) (g \<circ> h o k)"
    apply (rule homotopic_with_compose_continuous_right [OF homotopic_with_mono])
    using Q by (auto simp: contk imk)
  then show ?thesis
    apply (rule homotopic_with_eq)
    apply (metis feq)
    apply (metis geq)
    apply (metis Qeq)
    done
qed

lemma cohomotopically_trivial_retraction_null_gen:
  assumes P: "\<And>f. \<lbrakk>continuous_on t f; f ` t \<subseteq> u; Q f\<rbrakk> \<Longrightarrow> P(f o h)"
      and Q: "\<And>f. \<lbrakk>continuous_on s f; f ` s \<subseteq> u; P f\<rbrakk> \<Longrightarrow> Q(f o k)"
      and Qeq: "\<And>h k. (\<And>x. x \<in> t \<Longrightarrow> h x = k x) \<Longrightarrow> Q h = Q k"
      and hom: "\<And>f g. \<lbrakk>continuous_on s f; f ` s \<subseteq> u; P f\<rbrakk>
                       \<Longrightarrow> \<exists>c. homotopic_with P s u f (\<lambda>x. c)"
      and contf: "continuous_on t f" and imf: "f ` t \<subseteq> u" and Qf: "Q f"
  obtains c where "homotopic_with Q t u f (\<lambda>x. c)"
proof -
  have feq: "\<And>x. x \<in> t \<Longrightarrow> (f \<circ> h \<circ> k) x = f x" using idhk imf by auto
  have "continuous_on s (f \<circ> h)"
    using contf conth continuous_on_compose imh by blast
  moreover have "(f \<circ> h) ` s \<subseteq> u"
    using imf imh by fastforce
  moreover have "P (f \<circ> h)"
    by (simp add: P Qf contf imf)
  ultimately obtain c where "homotopic_with P s u (f o h) (\<lambda>x. c)"
    by (metis hom)
  then have "homotopic_with Q t u (f o h o k) ((\<lambda>x. c) o k)"
    apply (rule homotopic_with_compose_continuous_right [OF homotopic_with_mono])
    using Q by (auto simp: contk imk)
  then show ?thesis
    apply (rule_tac c = c in that)
    apply (erule homotopic_with_eq)
    apply (metis feq, simp)
    apply (metis Qeq)
    done
qed

end

lemma simply_connected_retraction_gen:
  shows "\<lbrakk>simply_connected S; continuous_on S h; h ` S = T;
          continuous_on T k; k ` T \<subseteq> S; \<And>y. y \<in> T \<Longrightarrow> h(k y) = y\<rbrakk>
        \<Longrightarrow> simply_connected T"
apply (simp add: simply_connected_def path_def path_image_def homotopic_loops_def, clarify)
apply (rule Retracts.homotopically_trivial_retraction_gen
        [of S h _ k _ "\<lambda>p. pathfinish p = pathstart p"  "\<lambda>p. pathfinish p = pathstart p"])
apply (simp_all add: Retracts_def pathfinish_def pathstart_def)
done

lemma homeomorphic_simply_connected:
    "\<lbrakk>S homeomorphic T; simply_connected S\<rbrakk> \<Longrightarrow> simply_connected T"
  by (auto simp: homeomorphic_def homeomorphism_def intro: simply_connected_retraction_gen)

lemma homeomorphic_simply_connected_eq:
    "S homeomorphic T \<Longrightarrow> (simply_connected S \<longleftrightarrow> simply_connected T)"
  by (metis homeomorphic_simply_connected homeomorphic_sym)

subsection\<open>Homotopy equivalence\<close>

definition homotopy_eqv :: "'a::topological_space set \<Rightarrow> 'b::topological_space set \<Rightarrow> bool"
             (infix "homotopy'_eqv" 50)
  where "S homotopy_eqv T \<equiv>
        \<exists>f g. continuous_on S f \<and> f ` S \<subseteq> T \<and>
              continuous_on T g \<and> g ` T \<subseteq> S \<and>
              homotopic_with (\<lambda>x. True) S S (g o f) id \<and>
              homotopic_with (\<lambda>x. True) T T (f o g) id"

lemma homeomorphic_imp_homotopy_eqv: "S homeomorphic T \<Longrightarrow> S homotopy_eqv T"
  unfolding homeomorphic_def homotopy_eqv_def homeomorphism_def
  by (fastforce intro!: homotopic_with_equal continuous_on_compose)

lemma homotopy_eqv_refl: "S homotopy_eqv S"
  by (rule homeomorphic_imp_homotopy_eqv homeomorphic_refl)+

lemma homotopy_eqv_sym: "S homotopy_eqv T \<longleftrightarrow> T homotopy_eqv S"
  by (auto simp: homotopy_eqv_def)

lemma homotopy_eqv_trans [trans]:
    fixes S :: "'a::real_normed_vector set" and U :: "'c::real_normed_vector set"
  assumes ST: "S homotopy_eqv T" and TU: "T homotopy_eqv U"
    shows "S homotopy_eqv U"
proof -
  obtain f1 g1 where f1: "continuous_on S f1" "f1 ` S \<subseteq> T"
                 and g1: "continuous_on T g1" "g1 ` T \<subseteq> S"
                 and hom1: "homotopic_with (\<lambda>x. True) S S (g1 o f1) id"
                           "homotopic_with (\<lambda>x. True) T T (f1 o g1) id"
    using ST by (auto simp: homotopy_eqv_def)
  obtain f2 g2 where f2: "continuous_on T f2" "f2 ` T \<subseteq> U"
                 and g2: "continuous_on U g2" "g2 ` U \<subseteq> T"
                 and hom2: "homotopic_with (\<lambda>x. True) T T (g2 o f2) id"
                           "homotopic_with (\<lambda>x. True) U U (f2 o g2) id"
    using TU by (auto simp: homotopy_eqv_def)
  have "homotopic_with (\<lambda>f. True) S T (g2 \<circ> f2 \<circ> f1) (id \<circ> f1)"
    by (rule homotopic_with_compose_continuous_right hom2 f1)+
  then have "homotopic_with (\<lambda>f. True) S T (g2 \<circ> (f2 \<circ> f1)) (id \<circ> f1)"
    by (simp add: o_assoc)
  then have "homotopic_with (\<lambda>x. True) S S
         (g1 \<circ> (g2 \<circ> (f2 \<circ> f1))) (g1 o (id o f1))"
    by (simp add: g1 homotopic_with_compose_continuous_left)
  moreover have "homotopic_with (\<lambda>x. True) S S (g1 o id o f1) id"
    using hom1 by simp
  ultimately have SS: "homotopic_with (\<lambda>x. True) S S (g1 \<circ> g2 \<circ> (f2 \<circ> f1)) id"
    apply (simp add: o_assoc)
    apply (blast intro: homotopic_with_trans)
    done
  have "homotopic_with (\<lambda>f. True) U T (f1 \<circ> g1 \<circ> g2) (id \<circ> g2)"
    by (rule homotopic_with_compose_continuous_right hom1 g2)+
  then have "homotopic_with (\<lambda>f. True) U T (f1 \<circ> (g1 \<circ> g2)) (id \<circ> g2)"
    by (simp add: o_assoc)
  then have "homotopic_with (\<lambda>x. True) U U
         (f2 \<circ> (f1 \<circ> (g1 \<circ> g2))) (f2 o (id o g2))"
    by (simp add: f2 homotopic_with_compose_continuous_left)
  moreover have "homotopic_with (\<lambda>x. True) U U (f2 o id o g2) id"
    using hom2 by simp
  ultimately have UU: "homotopic_with (\<lambda>x. True) U U (f2 \<circ> f1 \<circ> (g1 \<circ> g2)) id"
    apply (simp add: o_assoc)
    apply (blast intro: homotopic_with_trans)
    done
  show ?thesis
    unfolding homotopy_eqv_def
    apply (rule_tac x = "f2 \<circ> f1" in exI)
    apply (rule_tac x = "g1 \<circ> g2" in exI)
    apply (intro conjI continuous_on_compose SS UU)
    using f1 f2 g1 g2  apply (force simp: elim!: continuous_on_subset)+
    done
qed

lemma homotopy_eqv_inj_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
    shows "(f ` S) homotopy_eqv S"
apply (rule homeomorphic_imp_homotopy_eqv)
using assms homeomorphic_sym linear_homeomorphic_image by auto

lemma homotopy_eqv_translation:
    fixes S :: "'a::real_normed_vector set"
    shows "op + a ` S homotopy_eqv S"
  apply (rule homeomorphic_imp_homotopy_eqv)
  using homeomorphic_translation homeomorphic_sym by blast

lemma homotopy_eqv_homotopic_triviality_imp:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
    and U :: "'c::real_normed_vector set"
  assumes "S homotopy_eqv T"
      and f: "continuous_on U f" "f ` U \<subseteq> T"
      and g: "continuous_on U g" "g ` U \<subseteq> T"
      and homUS: "\<And>f g. \<lbrakk>continuous_on U f; f ` U \<subseteq> S;
                         continuous_on U g; g ` U \<subseteq> S\<rbrakk>
                         \<Longrightarrow> homotopic_with (\<lambda>x. True) U S f g"
    shows "homotopic_with (\<lambda>x. True) U T f g"
proof -
  obtain h k where h: "continuous_on S h" "h ` S \<subseteq> T"
               and k: "continuous_on T k" "k ` T \<subseteq> S"
               and hom: "homotopic_with (\<lambda>x. True) S S (k o h) id"
                        "homotopic_with (\<lambda>x. True) T T (h o k) id"
    using assms by (auto simp: homotopy_eqv_def)
  have "homotopic_with (\<lambda>f. True) U S (k \<circ> f) (k \<circ> g)"
    apply (rule homUS)
    using f g k
    apply (safe intro!: continuous_on_compose h k f elim!: continuous_on_subset)
    apply (force simp: o_def)+
    done
  then have "homotopic_with (\<lambda>x. True) U T (h o (k o f)) (h o (k o g))"
    apply (rule homotopic_with_compose_continuous_left)
    apply (simp_all add: h)
    done
  moreover have "homotopic_with (\<lambda>x. True) U T (h o k o f) (id o f)"
    apply (rule homotopic_with_compose_continuous_right [where X=T and Y=T])
    apply (auto simp: hom f)
    done
  moreover have "homotopic_with (\<lambda>x. True) U T (h o k o g) (id o g)"
    apply (rule homotopic_with_compose_continuous_right [where X=T and Y=T])
    apply (auto simp: hom g)
    done
  ultimately show "homotopic_with (\<lambda>x. True) U T f g"
    apply (simp add: o_assoc)
    using homotopic_with_trans homotopic_with_sym by blast
qed

lemma homotopy_eqv_homotopic_triviality:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
    and U :: "'c::real_normed_vector set"
  assumes "S homotopy_eqv T"
    shows "(\<forall>f g. continuous_on U f \<and> f ` U \<subseteq> S \<and>
                   continuous_on U g \<and> g ` U \<subseteq> S
                   \<longrightarrow> homotopic_with (\<lambda>x. True) U S f g) \<longleftrightarrow>
           (\<forall>f g. continuous_on U f \<and> f ` U \<subseteq> T \<and>
                  continuous_on U g \<and> g ` U \<subseteq> T
                  \<longrightarrow> homotopic_with (\<lambda>x. True) U T f g)"
apply (rule iffI)
apply (metis assms homotopy_eqv_homotopic_triviality_imp)
by (metis (no_types) assms homotopy_eqv_homotopic_triviality_imp homotopy_eqv_sym)

lemma homotopy_eqv_cohomotopic_triviality_null_imp:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
    and U :: "'c::real_normed_vector set"
  assumes "S homotopy_eqv T"
      and f: "continuous_on T f" "f ` T \<subseteq> U"
      and homSU: "\<And>f. \<lbrakk>continuous_on S f; f ` S \<subseteq> U\<rbrakk>
                      \<Longrightarrow> \<exists>c. homotopic_with (\<lambda>x. True) S U f (\<lambda>x. c)"
  obtains c where "homotopic_with (\<lambda>x. True) T U f (\<lambda>x. c)"
proof -
  obtain h k where h: "continuous_on S h" "h ` S \<subseteq> T"
               and k: "continuous_on T k" "k ` T \<subseteq> S"
               and hom: "homotopic_with (\<lambda>x. True) S S (k o h) id"
                        "homotopic_with (\<lambda>x. True) T T (h o k) id"
    using assms by (auto simp: homotopy_eqv_def)
  obtain c where "homotopic_with (\<lambda>x. True) S U (f \<circ> h) (\<lambda>x. c)"
    apply (rule exE [OF homSU [of "f \<circ> h"]])
    apply (intro continuous_on_compose h)
    using h f  apply (force elim!: continuous_on_subset)+
    done
  then have "homotopic_with (\<lambda>x. True) T U ((f o h) o k) ((\<lambda>x. c) o k)"
    apply (rule homotopic_with_compose_continuous_right [where X=S])
    using k by auto
  moreover have "homotopic_with (\<lambda>x. True) T U (f \<circ> id) (f \<circ> (h \<circ> k))"
    apply (rule homotopic_with_compose_continuous_left [where Y=T])
      apply (simp add: hom homotopic_with_symD)
     using f apply auto
    done
  ultimately show ?thesis
    apply (rule_tac c=c in that)
    apply (simp add: o_def)
    using homotopic_with_trans by blast
qed

lemma homotopy_eqv_cohomotopic_triviality_null:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
    and U :: "'c::real_normed_vector set"
  assumes "S homotopy_eqv T"
    shows "(\<forall>f. continuous_on S f \<and> f ` S \<subseteq> U
                \<longrightarrow> (\<exists>c. homotopic_with (\<lambda>x. True) S U f (\<lambda>x. c))) \<longleftrightarrow>
           (\<forall>f. continuous_on T f \<and> f ` T \<subseteq> U
                \<longrightarrow> (\<exists>c. homotopic_with (\<lambda>x. True) T U f (\<lambda>x. c)))"
apply (rule iffI)
apply (metis assms homotopy_eqv_cohomotopic_triviality_null_imp)
by (metis assms homotopy_eqv_cohomotopic_triviality_null_imp homotopy_eqv_sym)

lemma homotopy_eqv_homotopic_triviality_null_imp:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
    and U :: "'c::real_normed_vector set"
  assumes "S homotopy_eqv T"
      and f: "continuous_on U f" "f ` U \<subseteq> T"
      and homSU: "\<And>f. \<lbrakk>continuous_on U f; f ` U \<subseteq> S\<rbrakk>
                      \<Longrightarrow> \<exists>c. homotopic_with (\<lambda>x. True) U S f (\<lambda>x. c)"
    shows "\<exists>c. homotopic_with (\<lambda>x. True) U T f (\<lambda>x. c)"
proof -
  obtain h k where h: "continuous_on S h" "h ` S \<subseteq> T"
               and k: "continuous_on T k" "k ` T \<subseteq> S"
               and hom: "homotopic_with (\<lambda>x. True) S S (k \<circ> h) id"
                        "homotopic_with (\<lambda>x. True) T T (h \<circ> k) id"
    using assms by (auto simp: homotopy_eqv_def)
  obtain c::'a where "homotopic_with (\<lambda>x. True) U S (k \<circ> f) (\<lambda>x. c)"
    apply (rule exE [OF homSU [of "k \<circ> f"]])
    apply (intro continuous_on_compose h)
    using k f  apply (force elim!: continuous_on_subset)+
    done
  then have "homotopic_with (\<lambda>x. True) U T (h \<circ> (k \<circ> f)) (h \<circ> (\<lambda>x. c))"
    apply (rule homotopic_with_compose_continuous_left [where Y=S])
    using h by auto
  moreover have "homotopic_with (\<lambda>x. True) U T (id \<circ> f) ((h \<circ> k) \<circ> f)"
    apply (rule homotopic_with_compose_continuous_right [where X=T])
      apply (simp add: hom homotopic_with_symD)
     using f apply auto
    done
  ultimately show ?thesis
    using homotopic_with_trans by (fastforce simp add: o_def)
qed

lemma homotopy_eqv_homotopic_triviality_null:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
    and U :: "'c::real_normed_vector set"
  assumes "S homotopy_eqv T"
    shows "(\<forall>f. continuous_on U f \<and> f ` U \<subseteq> S
                  \<longrightarrow> (\<exists>c. homotopic_with (\<lambda>x. True) U S f (\<lambda>x. c))) \<longleftrightarrow>
           (\<forall>f. continuous_on U f \<and> f ` U \<subseteq> T
                  \<longrightarrow> (\<exists>c. homotopic_with (\<lambda>x. True) U T f (\<lambda>x. c)))"
apply (rule iffI)
apply (metis assms homotopy_eqv_homotopic_triviality_null_imp)
by (metis assms homotopy_eqv_homotopic_triviality_null_imp homotopy_eqv_sym)

lemma homotopy_eqv_contractible_sets:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
  assumes "contractible S" "contractible T" "S = {} \<longleftrightarrow> T = {}"
    shows "S homotopy_eqv T"
proof (cases "S = {}")
  case True with assms show ?thesis
    by (simp add: homeomorphic_imp_homotopy_eqv)
next
  case False
  with assms obtain a b where "a \<in> S" "b \<in> T"
    by auto
  then show ?thesis
    unfolding homotopy_eqv_def
    apply (rule_tac x="\<lambda>x. b" in exI)
    apply (rule_tac x="\<lambda>x. a" in exI)
    apply (intro assms conjI continuous_on_id' homotopic_into_contractible)
    apply (auto simp: o_def continuous_on_const)
    done
qed

lemma homotopy_eqv_empty1 [simp]:
  fixes S :: "'a::real_normed_vector set"
  shows "S homotopy_eqv ({}::'b::real_normed_vector set) \<longleftrightarrow> S = {}"
apply (rule iffI)
using homotopy_eqv_def apply fastforce
by (simp add: homotopy_eqv_contractible_sets)

lemma homotopy_eqv_empty2 [simp]:
  fixes S :: "'a::real_normed_vector set"
  shows "({}::'b::real_normed_vector set) homotopy_eqv S \<longleftrightarrow> S = {}"
by (metis homotopy_eqv_empty1 homotopy_eqv_sym)

lemma homotopy_eqv_contractibility:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  shows "S homotopy_eqv T \<Longrightarrow> (contractible S \<longleftrightarrow> contractible T)"
unfolding homotopy_eqv_def
by (blast intro: homotopy_dominated_contractibility)

lemma homotopy_eqv_sing:
  fixes S :: "'a::real_normed_vector set" and a :: "'b::real_normed_vector"
  shows "S homotopy_eqv {a} \<longleftrightarrow> S \<noteq> {} \<and> contractible S"
proof (cases "S = {}")
  case True then show ?thesis
    by simp
next
  case False then show ?thesis
    by (metis contractible_sing empty_not_insert homotopy_eqv_contractibility homotopy_eqv_contractible_sets)
qed

lemma homeomorphic_contractible_eq:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  shows "S homeomorphic T \<Longrightarrow> (contractible S \<longleftrightarrow> contractible T)"
by (simp add: homeomorphic_imp_homotopy_eqv homotopy_eqv_contractibility)

lemma homeomorphic_contractible:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  shows "\<lbrakk>contractible S; S homeomorphic T\<rbrakk> \<Longrightarrow> contractible T"
  by (metis homeomorphic_contractible_eq)

subsection\<open>Misc other results\<close>

lemma bounded_connected_Compl_real:
  fixes S :: "real set"
  assumes "bounded S" and conn: "connected(- S)"
    shows "S = {}"
proof -
  obtain a b where "S \<subseteq> box a b"
    by (meson assms bounded_subset_open_interval)
  then have "a \<notin> S" "b \<notin> S"
    by auto
  then have "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> x \<in> - S"
    by (meson Compl_iff conn connected_iff_interval)
  then show ?thesis
    using \<open>S \<subseteq> box a b\<close> by auto
qed

lemma bounded_connected_Compl_1:
  fixes S :: "'a::{euclidean_space} set"
  assumes "bounded S" and conn: "connected(- S)" and 1: "DIM('a) = 1"
    shows "S = {}"
proof -
  have "DIM('a) = DIM(real)"
    by (simp add: "1")
  then obtain f::"'a \<Rightarrow> real" and g
  where "linear f" "\<And>x. norm(f x) = norm x" "\<And>x. g(f x) = x" "\<And>y. f(g y) = y"
    by (rule isomorphisms_UNIV_UNIV) blast
  with \<open>bounded S\<close> have "bounded (f ` S)"
    using bounded_linear_image linear_linear by blast
  have "connected (f ` (-S))"
    using connected_linear_image assms \<open>linear f\<close> by blast
  moreover have "f ` (-S) = - (f ` S)"
    apply (rule bij_image_Compl_eq)
    apply (auto simp: bij_def)
     apply (metis \<open>\<And>x. g (f x) = x\<close> injI)
    by (metis UNIV_I \<open>\<And>y. f (g y) = y\<close> image_iff)
  finally have "connected (- (f ` S))"
    by simp
  then have "f ` S = {}"
    using \<open>bounded (f ` S)\<close> bounded_connected_Compl_real by blast
  then show ?thesis
    by blast
qed

subsection\<open>Some Uncountable Sets\<close>

lemma uncountable_closed_segment:
  fixes a :: "'a::real_normed_vector"
  assumes "a \<noteq> b" shows "uncountable (closed_segment a b)"
unfolding path_image_linepath [symmetric] path_image_def
  using inj_on_linepath [OF assms] uncountable_closed_interval [of 0 1]
        countable_image_inj_on by auto

lemma uncountable_open_segment:
  fixes a :: "'a::real_normed_vector"
  assumes "a \<noteq> b" shows "uncountable (open_segment a b)"
  by (simp add: assms open_segment_def uncountable_closed_segment uncountable_minus_countable)

lemma uncountable_convex:
  fixes a :: "'a::real_normed_vector"
  assumes "convex S" "a \<in> S" "b \<in> S" "a \<noteq> b"
    shows "uncountable S"
proof -
  have "uncountable (closed_segment a b)"
    by (simp add: uncountable_closed_segment assms)
  then show ?thesis
    by (meson assms convex_contains_segment countable_subset)
qed

lemma uncountable_ball:
  fixes a :: "'a::euclidean_space"
  assumes "r > 0"
    shows "uncountable (ball a r)"
proof -
  have "uncountable (open_segment a (a + r *\<^sub>R (SOME i. i \<in> Basis)))"
    by (metis Basis_zero SOME_Basis add_cancel_right_right assms less_le real_vector.scale_eq_0_iff uncountable_open_segment)
  moreover have "open_segment a (a + r *\<^sub>R (SOME i. i \<in> Basis)) \<subseteq> ball a r"
    using assms by (auto simp: in_segment algebra_simps dist_norm SOME_Basis)
  ultimately show ?thesis
    by (metis countable_subset)
qed

lemma ball_minus_countable_nonempty:
  assumes "countable (A :: 'a :: euclidean_space set)" "r > 0"
  shows   "ball z r - A \<noteq> {}"
proof
  assume *: "ball z r - A = {}"
  have "uncountable (ball z r - A)"
    by (intro uncountable_minus_countable assms uncountable_ball)
  thus False by (subst (asm) *) auto
qed

lemma uncountable_cball:
  fixes a :: "'a::euclidean_space"
  assumes "r > 0"
  shows "uncountable (cball a r)"
  using assms countable_subset uncountable_ball by auto

lemma pairwise_disjnt_countable:
  fixes \<N> :: "nat set set"
  assumes "pairwise disjnt \<N>"
    shows "countable \<N>"
proof -
  have "inj_on (\<lambda>X. SOME n. n \<in> X) (\<N> - {{}})"
    apply (clarsimp simp add: inj_on_def)
    by (metis assms disjnt_insert2 insert_absorb pairwise_def subsetI subset_empty tfl_some)
  then show ?thesis
    by (metis countable_Diff_eq countable_def)
qed

lemma pairwise_disjnt_countable_Union:
    assumes "countable (\<Union>\<N>)" and pwd: "pairwise disjnt \<N>"
    shows "countable \<N>"
proof -
  obtain f :: "_ \<Rightarrow> nat" where f: "inj_on f (\<Union>\<N>)"
    using assms by blast
  then have "pairwise disjnt (\<Union> X \<in> \<N>. {f ` X})"
    using assms by (force simp: pairwise_def disjnt_inj_on_iff [OF f])
  then have "countable (\<Union> X \<in> \<N>. {f ` X})"
    using pairwise_disjnt_countable by blast
  then show ?thesis
    by (meson pwd countable_image_inj_on disjoint_image f inj_on_image pairwise_disjnt_countable)
qed

lemma connected_uncountable:
  fixes S :: "'a::metric_space set"
  assumes "connected S" "a \<in> S" "b \<in> S" "a \<noteq> b" shows "uncountable S"
proof -
  have "continuous_on S (dist a)"
    by (intro continuous_intros)
  then have "connected (dist a ` S)"
    by (metis connected_continuous_image \<open>connected S\<close>)
  then have "closed_segment 0 (dist a b) \<subseteq> (dist a ` S)"
    by (simp add: assms closed_segment_subset is_interval_connected_1 is_interval_convex)
  then have "uncountable (dist a ` S)"
    by (metis \<open>a \<noteq> b\<close> countable_subset dist_eq_0_iff uncountable_closed_segment)
  then show ?thesis
    by blast
qed

lemma path_connected_uncountable:
  fixes S :: "'a::metric_space set"
  assumes "path_connected S" "a \<in> S" "b \<in> S" "a \<noteq> b" shows "uncountable S"
  using path_connected_imp_connected assms connected_uncountable by metis

lemma connected_finite_iff_sing:
  fixes S :: "'a::metric_space set"
  assumes "connected S"
  shows "finite S \<longleftrightarrow> S = {} \<or> (\<exists>a. S = {a})"  (is "_ = ?rhs")
proof -
  have "uncountable S" if "\<not> ?rhs"
    using connected_uncountable assms that by blast
  then show ?thesis
    using uncountable_infinite by auto
qed

lemma connected_card_eq_iff_nontrivial:
  fixes S :: "'a::metric_space set"
  shows "connected S \<Longrightarrow> uncountable S \<longleftrightarrow> ~(\<exists>a. S \<subseteq> {a})"
  apply (auto simp: countable_finite finite_subset)
  by (metis connected_uncountable is_singletonI' is_singleton_the_elem subset_singleton_iff)

lemma simple_path_image_uncountable:
  fixes g :: "real \<Rightarrow> 'a::metric_space"
  assumes "simple_path g"
  shows "uncountable (path_image g)"
proof -
  have "g 0 \<in> path_image g" "g (1/2) \<in> path_image g"
    by (simp_all add: path_defs)
  moreover have "g 0 \<noteq> g (1/2)"
    using assms by (fastforce simp add: simple_path_def)
  ultimately show ?thesis
    apply (simp add: assms connected_card_eq_iff_nontrivial connected_simple_path_image)
    by blast
qed

lemma arc_image_uncountable:
  fixes g :: "real \<Rightarrow> 'a::metric_space"
  assumes "arc g"
  shows "uncountable (path_image g)"
  by (simp add: arc_imp_simple_path assms simple_path_image_uncountable)


subsection\<open> Some simple positive connection theorems\<close>

proposition path_connected_convex_diff_countable:
  fixes U :: "'a::euclidean_space set"
  assumes "convex U" "~ collinear U" "countable S"
    shows "path_connected(U - S)"
proof (clarsimp simp add: path_connected_def)
  fix a b
  assume "a \<in> U" "a \<notin> S" "b \<in> U" "b \<notin> S"
  let ?m = "midpoint a b"
  show "\<exists>g. path g \<and> path_image g \<subseteq> U - S \<and> pathstart g = a \<and> pathfinish g = b"
  proof (cases "a = b")
    case True
    then show ?thesis
      by (metis DiffI \<open>a \<in> U\<close> \<open>a \<notin> S\<close> path_component_def path_component_refl)
  next
    case False
    then have "a \<noteq> ?m" "b \<noteq> ?m"
      using midpoint_eq_endpoint by fastforce+
    have "?m \<in> U"
      using \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>convex U\<close> convex_contains_segment by force
    obtain c where "c \<in> U" and nc_abc: "\<not> collinear {a,b,c}"
      by (metis False \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>~ collinear U\<close> collinear_triples insert_absorb)
    have ncoll_mca: "\<not> collinear {?m,c,a}"
      by (metis (full_types) \<open>a \<noteq> ?m\<close> collinear_3_trans collinear_midpoint insert_commute nc_abc)
    have ncoll_mcb: "\<not> collinear {?m,c,b}"
      by (metis (full_types) \<open>b \<noteq> ?m\<close> collinear_3_trans collinear_midpoint insert_commute nc_abc)
    have "c \<noteq> ?m"
      by (metis collinear_midpoint insert_commute nc_abc)
    then have "closed_segment ?m c \<subseteq> U"
      by (simp add: \<open>c \<in> U\<close> \<open>?m \<in> U\<close> \<open>convex U\<close> closed_segment_subset)
    then obtain z where z: "z \<in> closed_segment ?m c"
                    and disjS: "(closed_segment a z \<union> closed_segment z b) \<inter> S = {}"
    proof -
      have False if "closed_segment ?m c \<subseteq> {z. (closed_segment a z \<union> closed_segment z b) \<inter> S \<noteq> {}}"
      proof -
        have closb: "closed_segment ?m c \<subseteq>
                 {z \<in> closed_segment ?m c. closed_segment a z \<inter> S \<noteq> {}} \<union> {z \<in> closed_segment ?m c. closed_segment z b \<inter> S \<noteq> {}}"
          using that by blast
        have *: "countable {z \<in> closed_segment ?m c. closed_segment z u \<inter> S \<noteq> {}}"
          if "u \<in> U" "u \<notin> S" and ncoll: "\<not> collinear {?m, c, u}" for u
        proof -
          have **: False if x1: "x1 \<in> closed_segment ?m c" and x2: "x2 \<in> closed_segment ?m c"
                            and "x1 \<noteq> x2" "x1 \<noteq> u"
                            and w: "w \<in> closed_segment x1 u" "w \<in> closed_segment x2 u"
                            and "w \<in> S" for x1 x2 w
          proof -
            have "x1 \<in> affine hull {?m,c}" "x2 \<in> affine hull {?m,c}"
              using segment_as_ball x1 x2 by auto
            then have coll_x1: "collinear {x1, ?m, c}" and coll_x2: "collinear {?m, c, x2}"
              by (simp_all add: affine_hull_3_imp_collinear) (metis affine_hull_3_imp_collinear insert_commute)
            have "\<not> collinear {x1, u, x2}"
            proof
              assume "collinear {x1, u, x2}"
              then have "collinear {?m, c, u}"
                by (metis (full_types) \<open>c \<noteq> ?m\<close> coll_x1 coll_x2 collinear_3_trans insert_commute ncoll \<open>x1 \<noteq> x2\<close>)
              with ncoll show False ..
            qed
            then have "closed_segment x1 u \<inter> closed_segment u x2 = {u}"
              by (blast intro!: Int_closed_segment)
            then have "w = u"
              using closed_segment_commute w by auto
            show ?thesis
              using \<open>u \<notin> S\<close> \<open>w = u\<close> that(7) by auto
          qed
          then have disj: "disjoint ((\<Union>z\<in>closed_segment ?m c. {closed_segment z u \<inter> S}))"
            by (fastforce simp: pairwise_def disjnt_def)
          have cou: "countable ((\<Union>z \<in> closed_segment ?m c. {closed_segment z u \<inter> S}) - {{}})"
            apply (rule pairwise_disjnt_countable_Union [OF _ pairwise_subset [OF disj]])
             apply (rule countable_subset [OF _ \<open>countable S\<close>], auto)
            done
          define f where "f \<equiv> \<lambda>X. (THE z. z \<in> closed_segment ?m c \<and> X = closed_segment z u \<inter> S)"
          show ?thesis
          proof (rule countable_subset [OF _ countable_image [OF cou, where f=f]], clarify)
            fix x
            assume x: "x \<in> closed_segment ?m c" "closed_segment x u \<inter> S \<noteq> {}"
            show "x \<in> f ` ((\<Union>z\<in>closed_segment ?m c. {closed_segment z u \<inter> S}) - {{}})"
            proof (rule_tac x="closed_segment x u \<inter> S" in image_eqI)
              show "x = f (closed_segment x u \<inter> S)"
                unfolding f_def
                apply (rule the_equality [symmetric])
                using x  apply (auto simp: dest: **)
                done
            qed (use x in auto)
          qed
        qed
        have "uncountable (closed_segment ?m c)"
          by (metis \<open>c \<noteq> ?m\<close> uncountable_closed_segment)
        then show False
          using closb * [OF \<open>a \<in> U\<close> \<open>a \<notin> S\<close> ncoll_mca] * [OF \<open>b \<in> U\<close> \<open>b \<notin> S\<close> ncoll_mcb]
          apply (simp add: closed_segment_commute)
          by (simp add: countable_subset)
      qed
      then show ?thesis
        by (force intro: that)
    qed
    show ?thesis
    proof (intro exI conjI)
      have "path_image (linepath a z +++ linepath z b) \<subseteq> U"
        by (metis \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>closed_segment ?m c \<subseteq> U\<close> z \<open>convex U\<close> closed_segment_subset contra_subsetD path_image_linepath subset_path_image_join)
      with disjS show "path_image (linepath a z +++ linepath z b) \<subseteq> U - S"
        by (force simp: path_image_join)
    qed auto
  qed
qed


corollary connected_convex_diff_countable:
  fixes U :: "'a::euclidean_space set"
  assumes "convex U" "~ collinear U" "countable S"
  shows "connected(U - S)"
  by (simp add: assms path_connected_convex_diff_countable path_connected_imp_connected)

lemma path_connected_punctured_convex:
  assumes "convex S" and aff: "aff_dim S \<noteq> 1"
    shows "path_connected(S - {a})"
proof -
  consider "aff_dim S = -1" | "aff_dim S = 0" | "aff_dim S \<ge> 2"
    using assms aff_dim_geq [of S] by linarith
  then show ?thesis
  proof cases
    assume "aff_dim S = -1"
    then show ?thesis
      by (metis aff_dim_empty empty_Diff path_connected_empty)
  next
    assume "aff_dim S = 0"
    then show ?thesis
      by (metis aff_dim_eq_0 Diff_cancel Diff_empty Diff_insert0 convex_empty convex_imp_path_connected path_connected_singleton singletonD)
  next
    assume ge2: "aff_dim S \<ge> 2"
    then have "\<not> collinear S"
    proof (clarsimp simp add: collinear_affine_hull)
      fix u v
      assume "S \<subseteq> affine hull {u, v}"
      then have "aff_dim S \<le> aff_dim {u, v}"
        by (metis (no_types) aff_dim_affine_hull aff_dim_subset)
      with ge2 show False
        by (metis (no_types) aff_dim_2 antisym aff not_numeral_le_zero one_le_numeral order_trans)
    qed
    then show ?thesis
      apply (rule path_connected_convex_diff_countable [OF \<open>convex S\<close>])
      by simp
  qed
qed

lemma connected_punctured_convex:
  shows "\<lbrakk>convex S; aff_dim S \<noteq> 1\<rbrakk> \<Longrightarrow> connected(S - {a})"
  using path_connected_imp_connected path_connected_punctured_convex by blast

lemma path_connected_complement_countable:
  fixes S :: "'a::euclidean_space set"
  assumes "2 \<le> DIM('a)" "countable S"
  shows "path_connected(- S)"
proof -
  have "path_connected(UNIV - S)"
    apply (rule path_connected_convex_diff_countable)
    using assms by (auto simp: collinear_aff_dim [of "UNIV :: 'a set"])
  then show ?thesis
    by (simp add: Compl_eq_Diff_UNIV)
qed

proposition path_connected_openin_diff_countable:
  fixes S :: "'a::euclidean_space set"
  assumes "connected S" and ope: "openin (subtopology euclidean (affine hull S)) S"
      and "~ collinear S" "countable T"
    shows "path_connected(S - T)"
proof (clarsimp simp add: path_connected_component)
  fix x y
  assume xy: "x \<in> S" "x \<notin> T" "y \<in> S" "y \<notin> T"
  show "path_component (S - T) x y"
  proof (rule connected_equivalence_relation_gen [OF \<open>connected S\<close>, where P = "\<lambda>x. x \<notin> T"])
    show "\<exists>z. z \<in> U \<and> z \<notin> T" if opeU: "openin (subtopology euclidean S) U" and "x \<in> U" for U x
    proof -
      have "openin (subtopology euclidean (affine hull S)) U"
        using opeU ope openin_trans by blast
      with \<open>x \<in> U\<close> obtain r where Usub: "U \<subseteq> affine hull S" and "r > 0"
                              and subU: "ball x r \<inter> affine hull S \<subseteq> U"
        by (auto simp: openin_contains_ball)
      with \<open>x \<in> U\<close> have x: "x \<in> ball x r \<inter> affine hull S"
        by auto
      have "~ S \<subseteq> {x}"
        using \<open>~ collinear S\<close>  collinear_subset by blast
      then obtain x' where "x' \<noteq> x" "x' \<in> S"
        by blast
      obtain y where y: "y \<noteq> x" "y \<in> ball x r \<inter> affine hull S"
      proof
        show "x + (r / 2 / norm(x' - x)) *\<^sub>R (x' - x) \<noteq> x"
          using \<open>x' \<noteq> x\<close> \<open>r > 0\<close> by auto
        show "x + (r / 2 / norm (x' - x)) *\<^sub>R (x' - x) \<in> ball x r \<inter> affine hull S"
          using \<open>x' \<noteq> x\<close> \<open>r > 0\<close> \<open>x' \<in> S\<close> x
          by (simp add: dist_norm mem_affine_3_minus hull_inc)
      qed
      have "convex (ball x r \<inter> affine hull S)"
        by (simp add: affine_imp_convex convex_Int)
      with x y subU have "uncountable U"
        by (meson countable_subset uncountable_convex)
      then have "\<not> U \<subseteq> T"
        using \<open>countable T\<close> countable_subset by blast
      then show ?thesis by blast
    qed
    show "\<exists>U. openin (subtopology euclidean S) U \<and> x \<in> U \<and>
              (\<forall>x\<in>U. \<forall>y\<in>U. x \<notin> T \<and> y \<notin> T \<longrightarrow> path_component (S - T) x y)"
          if "x \<in> S" for x
    proof -
      obtain r where Ssub: "S \<subseteq> affine hull S" and "r > 0"
                 and subS: "ball x r \<inter> affine hull S \<subseteq> S"
        using ope \<open>x \<in> S\<close> by (auto simp: openin_contains_ball)
      then have conv: "convex (ball x r \<inter> affine hull S)"
        by (simp add: affine_imp_convex convex_Int)
      have "\<not> aff_dim (affine hull S) \<le> 1"
        using \<open>\<not> collinear S\<close> collinear_aff_dim by auto
      then have "\<not> collinear (ball x r \<inter> affine hull S)"
        apply (simp add: collinear_aff_dim)
        by (metis (no_types, hide_lams) aff_dim_convex_Int_open IntI open_ball \<open>0 < r\<close> aff_dim_affine_hull affine_affine_hull affine_imp_convex centre_in_ball empty_iff hull_subset inf_commute subsetCE that)
      then have *: "path_connected ((ball x r \<inter> affine hull S) - T)"
        by (rule path_connected_convex_diff_countable [OF conv _ \<open>countable T\<close>])
      have ST: "ball x r \<inter> affine hull S - T \<subseteq> S - T"
        using subS by auto
      show ?thesis
      proof (intro exI conjI)
        show "x \<in> ball x r \<inter> affine hull S"
          using \<open>x \<in> S\<close> \<open>r > 0\<close> by (simp add: hull_inc)
        have "openin (subtopology euclidean (affine hull S)) (ball x r \<inter> affine hull S)"
          by (simp add: inf.commute openin_Int_open)
        then show "openin (subtopology euclidean S) (ball x r \<inter> affine hull S)"
          by (rule openin_subset_trans [OF _ subS Ssub])
      qed (use * path_component_trans in \<open>auto simp: path_connected_component path_component_of_subset [OF ST]\<close>)
    qed
  qed (use xy path_component_trans in auto)
qed

corollary connected_openin_diff_countable:
  fixes S :: "'a::euclidean_space set"
  assumes "connected S" and ope: "openin (subtopology euclidean (affine hull S)) S"
      and "~ collinear S" "countable T"
    shows "connected(S - T)"
  by (metis path_connected_imp_connected path_connected_openin_diff_countable [OF assms])

corollary path_connected_open_diff_countable:
  fixes S :: "'a::euclidean_space set"
  assumes "2 \<le> DIM('a)" "open S" "connected S" "countable T"
  shows "path_connected(S - T)"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp add: path_connected_empty)
next
  case False
  show ?thesis
  proof (rule path_connected_openin_diff_countable)
    show "openin (subtopology euclidean (affine hull S)) S"
      by (simp add: assms hull_subset open_subset)
    show "\<not> collinear S"
      using assms False by (simp add: collinear_aff_dim aff_dim_open)
  qed (simp_all add: assms)
qed

corollary connected_open_diff_countable:
  fixes S :: "'a::euclidean_space set"
  assumes "2 \<le> DIM('a)" "open S" "connected S" "countable T"
  shows "connected(S - T)"
by (simp add: assms path_connected_imp_connected path_connected_open_diff_countable)



subsection\<open> Self-homeomorphisms shuffling points about in various ways.\<close>

subsubsection\<open>The theorem \<open>homeomorphism_moving_points_exists\<close>\<close>

lemma homeomorphism_moving_point_1:
  fixes a :: "'a::euclidean_space"
  assumes "affine T" "a \<in> T" and u: "u \<in> ball a r \<inter> T"
  obtains f g where "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) f g"
                    "f a = u" "\<And>x. x \<in> sphere a r \<Longrightarrow> f x = x"
proof -
  have nou: "norm (u - a) < r" and "u \<in> T"
    using u by (auto simp: dist_norm norm_minus_commute)
  then have "0 < r"
    by (metis DiffD1 Diff_Diff_Int ball_eq_empty centre_in_ball not_le u)
  define f where "f \<equiv> \<lambda>x. (1 - norm(x - a) / r) *\<^sub>R (u - a) + x"
  have *: "False" if eq: "x + (norm y / r) *\<^sub>R u = y + (norm x / r) *\<^sub>R u"
                  and nou: "norm u < r" and yx: "norm y < norm x" for x y and u::'a
  proof -
    have "x = y + (norm x / r - (norm y / r)) *\<^sub>R u"
      using eq by (simp add: algebra_simps)
    then have "norm x = norm (y + ((norm x - norm y) / r) *\<^sub>R u)"
      by (metis diff_divide_distrib)
    also have "... \<le> norm y + norm(((norm x - norm y) / r) *\<^sub>R u)"
      using norm_triangle_ineq by blast
    also have "... = norm y + (norm x - norm y) * (norm u / r)"
      using yx \<open>r > 0\<close>
      by (simp add: divide_simps)
    also have "... < norm y + (norm x - norm y) * 1"
      apply (subst add_less_cancel_left)
      apply (rule mult_strict_left_mono)
      using nou \<open>0 < r\<close> yx
       apply (simp_all add: field_simps)
      done
    also have "... = norm x"
      by simp
    finally show False by simp
  qed
  have "inj f"
    unfolding f_def
  proof (clarsimp simp: inj_on_def)
    fix x y
    assume "(1 - norm (x - a) / r) *\<^sub>R (u - a) + x =
            (1 - norm (y - a) / r) *\<^sub>R (u - a) + y"
    then have eq: "(x - a) + (norm (y - a) / r) *\<^sub>R (u - a) = (y - a) + (norm (x - a) / r) *\<^sub>R (u - a)"
      by (auto simp: algebra_simps)
    show "x=y"
    proof (cases "norm (x - a) = norm (y - a)")
      case True
      then show ?thesis
        using eq by auto
    next
      case False
      then consider "norm (x - a) < norm (y - a)" | "norm (x - a) > norm (y - a)"
        by linarith
      then have "False"
      proof cases
        case 1 show False
          using * [OF _ nou 1] eq by simp
      next
        case 2 with * [OF eq nou] show False
          by auto
      qed
      then show "x=y" ..
    qed
  qed
  then have inj_onf: "inj_on f (cball a r \<inter> T)"
    using inj_on_Int by fastforce
  have contf: "continuous_on (cball a r \<inter> T) f"
    unfolding f_def using \<open>0 < r\<close>  by (intro continuous_intros) blast
  have fim: "f ` (cball a r \<inter> T) = cball a r \<inter> T"
  proof
    have *: "norm (y + (1 - norm y / r) *\<^sub>R u) \<le> r" if "norm y \<le> r" "norm u < r" for y u::'a
    proof -
      have "norm (y + (1 - norm y / r) *\<^sub>R u) \<le> norm y + norm((1 - norm y / r) *\<^sub>R u)"
        using norm_triangle_ineq by blast
      also have "... = norm y + abs(1 - norm y / r) * norm u"
        by simp
      also have "... \<le> r"
      proof -
        have "(r - norm u) * (r - norm y) \<ge> 0"
          using that by auto
        then have "r * norm u + r * norm y \<le> r * r + norm u * norm y"
          by (simp add: algebra_simps)
        then show ?thesis
        using that \<open>0 < r\<close> by (simp add: abs_if field_simps)
      qed
      finally show ?thesis .
    qed
    have "f ` (cball a r) \<subseteq> cball a r"
      apply (clarsimp simp add: dist_norm norm_minus_commute f_def)
      using * by (metis diff_add_eq diff_diff_add diff_diff_eq2 norm_minus_commute nou)
    moreover have "f ` T \<subseteq> T"
      unfolding f_def using \<open>affine T\<close> \<open>a \<in> T\<close> \<open>u \<in> T\<close>
      by (force simp: add.commute mem_affine_3_minus)
    ultimately show "f ` (cball a r \<inter> T) \<subseteq> cball a r \<inter> T"
      by blast
  next
    show "cball a r \<inter> T \<subseteq> f ` (cball a r \<inter> T)"
    proof (clarsimp simp add: dist_norm norm_minus_commute)
      fix x
      assume x: "norm (x - a) \<le> r" and "x \<in> T"
      have "\<exists>v \<in> {0..1}. ((1 - v) * r - norm ((x - a) - v *\<^sub>R (u - a))) \<bullet> 1 = 0"
        by (rule ivt_decreasing_component_on_1) (auto simp: x continuous_intros)
      then obtain v where "0\<le>v" "v\<le>1" and v: "(1 - v) * r = norm ((x - a) - v *\<^sub>R (u - a))"
        by auto
      show "x \<in> f ` (cball a r \<inter> T)"
      proof (rule image_eqI)
        show "x = f (x - v *\<^sub>R (u - a))"
          using \<open>r > 0\<close> v by (simp add: f_def field_simps)
        have "x - v *\<^sub>R (u - a) \<in> cball a r"
          using \<open>r > 0\<close> v \<open>0 \<le> v\<close>
          apply (simp add: field_simps dist_norm norm_minus_commute)
          by (metis le_add_same_cancel2 order.order_iff_strict zero_le_mult_iff)
        moreover have "x - v *\<^sub>R (u - a) \<in> T"
          by (simp add: f_def \<open>affine T\<close> \<open>u \<in> T\<close> \<open>x \<in> T\<close> assms mem_affine_3_minus2)
        ultimately show "x - v *\<^sub>R (u - a) \<in> cball a r \<inter> T"
          by blast
      qed
    qed
  qed
  have "\<exists>g. homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) f g"
    apply (rule homeomorphism_compact [OF _ contf fim inj_onf])
    apply (simp add: affine_closed compact_Int_closed \<open>affine T\<close>)
    done
  then show ?thesis
    apply (rule exE)
    apply (erule_tac f=f in that)
    using \<open>r > 0\<close>
     apply (simp_all add: f_def dist_norm norm_minus_commute)
    done
qed

corollary homeomorphism_moving_point_2:
  fixes a :: "'a::euclidean_space"
  assumes "affine T" "a \<in> T" and u: "u \<in> ball a r \<inter> T" and v: "v \<in> ball a r \<inter> T"
  obtains f g where "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) f g"
                    "f u = v" "\<And>x. \<lbrakk>x \<in> sphere a r; x \<in> T\<rbrakk> \<Longrightarrow> f x = x"
proof -
  have "0 < r"
    by (metis DiffD1 Diff_Diff_Int ball_eq_empty centre_in_ball not_le u)
  obtain f1 g1 where hom1: "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) f1 g1"
                 and "f1 a = u" and f1: "\<And>x. x \<in> sphere a r \<Longrightarrow> f1 x = x"
    using homeomorphism_moving_point_1 [OF \<open>affine T\<close> \<open>a \<in> T\<close> u] by blast
  obtain f2 g2 where hom2: "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) f2 g2"
                 and "f2 a = v" and f2: "\<And>x. x \<in> sphere a r \<Longrightarrow> f2 x = x"
    using homeomorphism_moving_point_1 [OF \<open>affine T\<close> \<open>a \<in> T\<close> v] by blast
  show ?thesis
  proof
    show "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) (f2 \<circ> g1) (f1 \<circ> g2)"
      by (metis homeomorphism_compose homeomorphism_symD hom1 hom2)
    have "g1 u = a"
      using \<open>0 < r\<close> \<open>f1 a = u\<close> assms hom1 homeomorphism_apply1 by fastforce
    then show "(f2 \<circ> g1) u = v"
      by (simp add: \<open>f2 a = v\<close>)
    show "\<And>x. \<lbrakk>x \<in> sphere a r; x \<in> T\<rbrakk> \<Longrightarrow> (f2 \<circ> g1) x = x"
      using f1 f2 hom1 homeomorphism_apply1 by fastforce
  qed
qed


corollary homeomorphism_moving_point_3:
  fixes a :: "'a::euclidean_space"
  assumes "affine T" "a \<in> T" and ST: "ball a r \<inter> T \<subseteq> S" "S \<subseteq> T"
      and u: "u \<in> ball a r \<inter> T" and v: "v \<in> ball a r \<inter> T"
  obtains f g where "homeomorphism S S f g"
                    "f u = v" "{x. ~ (f x = x \<and> g x = x)} \<subseteq> ball a r \<inter> T"
proof -
  obtain f g where hom: "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) f g"
               and "f u = v" and fid: "\<And>x. \<lbrakk>x \<in> sphere a r; x \<in> T\<rbrakk> \<Longrightarrow> f x = x"
    using homeomorphism_moving_point_2 [OF \<open>affine T\<close> \<open>a \<in> T\<close> u v] by blast
  have gid: "\<And>x. \<lbrakk>x \<in> sphere a r; x \<in> T\<rbrakk> \<Longrightarrow> g x = x"
    using fid hom homeomorphism_apply1 by fastforce
  define ff where "ff \<equiv> \<lambda>x. if x \<in> ball a r \<inter> T then f x else x"
  define gg where "gg \<equiv> \<lambda>x. if x \<in> ball a r \<inter> T then g x else x"
  show ?thesis
  proof
    show "homeomorphism S S ff gg"
    proof (rule homeomorphismI)
      have "continuous_on ((cball a r \<inter> T) \<union> (T - ball a r)) ff"
        apply (simp add: ff_def)
        apply (rule continuous_on_cases)
        using homeomorphism_cont1 [OF hom]
            apply (auto simp: affine_closed \<open>affine T\<close> continuous_on_id fid)
        done
      then show "continuous_on S ff"
        apply (rule continuous_on_subset)
        using ST by auto
      have "continuous_on ((cball a r \<inter> T) \<union> (T - ball a r)) gg"
        apply (simp add: gg_def)
        apply (rule continuous_on_cases)
        using homeomorphism_cont2 [OF hom]
            apply (auto simp: affine_closed \<open>affine T\<close> continuous_on_id gid)
        done
      then show "continuous_on S gg"
        apply (rule continuous_on_subset)
        using ST by auto
      show "ff ` S \<subseteq> S"
      proof (clarsimp simp add: ff_def)
        fix x
        assume "x \<in> S" and x: "dist a x < r" and "x \<in> T"
        then have "f x \<in> cball a r \<inter> T"
          using homeomorphism_image1 [OF hom] by force
        then show "f x \<in> S"
          using ST(1) \<open>x \<in> T\<close> gid hom homeomorphism_def x by fastforce
      qed
      show "gg ` S \<subseteq> S"
      proof (clarsimp simp add: gg_def)
        fix x
        assume "x \<in> S" and x: "dist a x < r" and "x \<in> T"
        then have "g x \<in> cball a r \<inter> T"
          using homeomorphism_image2 [OF hom] by force
        then have "g x \<in> ball a r"
          using homeomorphism_apply2 [OF hom]
            by (metis Diff_Diff_Int Diff_iff  \<open>x \<in> T\<close> cball_def fid le_less mem_Collect_eq mem_ball mem_sphere x)
        then show "g x \<in> S"
          using ST(1) \<open>g x \<in> cball a r \<inter> T\<close> by force
        qed
      show "\<And>x. x \<in> S \<Longrightarrow> gg (ff x) = x"
        apply (simp add: ff_def gg_def)
        using homeomorphism_apply1 [OF hom] homeomorphism_image1 [OF hom]
        apply auto
        apply (metis Int_iff homeomorphism_apply1 [OF hom] fid image_eqI less_eq_real_def mem_cball mem_sphere)
        done
      show "\<And>x. x \<in> S \<Longrightarrow> ff (gg x) = x"
        apply (simp add: ff_def gg_def)
        using homeomorphism_apply2 [OF hom] homeomorphism_image2 [OF hom]
        apply auto
        apply (metis Int_iff fid image_eqI less_eq_real_def mem_cball mem_sphere)
        done
    qed
    show "ff u = v"
      using u by (auto simp: ff_def \<open>f u = v\<close>)
    show "{x. \<not> (ff x = x \<and> gg x = x)} \<subseteq> ball a r \<inter> T"
      by (auto simp: ff_def gg_def)
  qed
qed


proposition homeomorphism_moving_point:
  fixes a :: "'a::euclidean_space"
  assumes ope: "openin (subtopology euclidean (affine hull S)) S"
      and "S \<subseteq> T"
      and TS: "T \<subseteq> affine hull S"
      and S: "connected S" "a \<in> S" "b \<in> S"
  obtains f g where "homeomorphism T T f g" "f a = b"
                    "{x. ~ (f x = x \<and> g x = x)} \<subseteq> S"
                    "bounded {x. ~ (f x = x \<and> g x = x)}"
proof -
  have 1: "\<exists>h k. homeomorphism T T h k \<and> h (f d) = d \<and>
              {x. ~ (h x = x \<and> k x = x)} \<subseteq> S \<and> bounded {x. ~ (h x = x \<and> k x = x)}"
        if "d \<in> S" "f d \<in> S" and homfg: "homeomorphism T T f g"
        and S: "{x. ~ (f x = x \<and> g x = x)} \<subseteq> S"
        and bo: "bounded {x. ~ (f x = x \<and> g x = x)}" for d f g
  proof (intro exI conjI)
    show homgf: "homeomorphism T T g f"
      by (metis homeomorphism_symD homfg)
    then show "g (f d) = d"
      by (meson \<open>S \<subseteq> T\<close> homeomorphism_def subsetD \<open>d \<in> S\<close>)
    show "{x. \<not> (g x = x \<and> f x = x)} \<subseteq> S"
      using S by blast
    show "bounded {x. \<not> (g x = x \<and> f x = x)}"
      using bo by (simp add: conj_commute)
  qed
  have 2: "\<exists>f g. homeomorphism T T f g \<and> f x = f2 (f1 x) \<and>
                 {x. \<not> (f x = x \<and> g x = x)} \<subseteq> S \<and> bounded {x. \<not> (f x = x \<and> g x = x)}"
             if "x \<in> S" "f1 x \<in> S" "f2 (f1 x) \<in> S"
                and hom: "homeomorphism T T f1 g1" "homeomorphism T T f2 g2"
                and sub: "{x. \<not> (f1 x = x \<and> g1 x = x)} \<subseteq> S"   "{x. \<not> (f2 x = x \<and> g2 x = x)} \<subseteq> S"
                and bo: "bounded {x. \<not> (f1 x = x \<and> g1 x = x)}"  "bounded {x. \<not> (f2 x = x \<and> g2 x = x)}"
             for x f1 f2 g1 g2
  proof (intro exI conjI)
    show homgf: "homeomorphism T T (f2 \<circ> f1) (g1 \<circ> g2)"
      by (metis homeomorphism_compose hom)
    then show "(f2 \<circ> f1) x = f2 (f1 x)"
      by force
    show "{x. \<not> ((f2 \<circ> f1) x = x \<and> (g1 \<circ> g2) x = x)} \<subseteq> S"
      using sub by force
    have "bounded ({x. ~(f1 x = x \<and> g1 x = x)} \<union> {x. ~(f2 x = x \<and> g2 x = x)})"
      using bo by simp
    then show "bounded {x. \<not> ((f2 \<circ> f1) x = x \<and> (g1 \<circ> g2) x = x)}"
      by (rule bounded_subset) auto
  qed
  have 3: "\<exists>U. openin (subtopology euclidean S) U \<and>
              d \<in> U \<and>
              (\<forall>x\<in>U.
                  \<exists>f g. homeomorphism T T f g \<and> f d = x \<and>
                        {x. \<not> (f x = x \<and> g x = x)} \<subseteq> S \<and>
                        bounded {x. \<not> (f x = x \<and> g x = x)})"
           if "d \<in> S" for d
  proof -
    obtain r where "r > 0" and r: "ball d r \<inter> affine hull S \<subseteq> S"
      by (metis \<open>d \<in> S\<close> ope openin_contains_ball)
    have *: "\<exists>f g. homeomorphism T T f g \<and> f d = e \<and>
                   {x. \<not> (f x = x \<and> g x = x)} \<subseteq> S \<and>
                   bounded {x. \<not> (f x = x \<and> g x = x)}" if "e \<in> S" "e \<in> ball d r" for e
      apply (rule homeomorphism_moving_point_3 [of "affine hull S" d r T d e])
      using r \<open>S \<subseteq> T\<close> TS that
            apply (auto simp: \<open>d \<in> S\<close> \<open>0 < r\<close> hull_inc)
      using bounded_subset by blast
    show ?thesis
      apply (rule_tac x="S \<inter> ball d r" in exI)
      apply (intro conjI)
        apply (simp add: openin_open_Int)
       apply (simp add: \<open>0 < r\<close> that)
      apply (blast intro: *)
      done
  qed
  have "\<exists>f g. homeomorphism T T f g \<and> f a = b \<and>
              {x. ~ (f x = x \<and> g x = x)} \<subseteq> S \<and> bounded {x. ~ (f x = x \<and> g x = x)}"
    apply (rule connected_equivalence_relation [OF S], safe)
      apply (blast intro: 1 2 3)+
    done
  then show ?thesis
    using that by auto
qed


lemma homeomorphism_moving_points_exists_gen:
  assumes K: "finite K" "\<And>i. i \<in> K \<Longrightarrow> x i \<in> S \<and> y i \<in> S"
             "pairwise (\<lambda>i j. (x i \<noteq> x j) \<and> (y i \<noteq> y j)) K"
      and "2 \<le> aff_dim S"
      and ope: "openin (subtopology euclidean (affine hull S)) S"
      and "S \<subseteq> T" "T \<subseteq> affine hull S" "connected S"
  shows "\<exists>f g. homeomorphism T T f g \<and> (\<forall>i \<in> K. f(x i) = y i) \<and>
               {x. ~ (f x = x \<and> g x = x)} \<subseteq> S \<and> bounded {x. ~ (f x = x \<and> g x = x)}"
  using assms
proof (induction K)
  case empty
  then show ?case
    by (force simp: homeomorphism_ident)
next
  case (insert i K)
  then have xney: "\<And>j. \<lbrakk>j \<in> K; j \<noteq> i\<rbrakk> \<Longrightarrow> x i \<noteq> x j \<and> y i \<noteq> y j"
       and pw: "pairwise (\<lambda>i j. x i \<noteq> x j \<and> y i \<noteq> y j) K"
       and "x i \<in> S" "y i \<in> S"
       and xyS: "\<And>i. i \<in> K \<Longrightarrow> x i \<in> S \<and> y i \<in> S"
    by (simp_all add: pairwise_insert)
  obtain f g where homfg: "homeomorphism T T f g" and feq: "\<And>i. i \<in> K \<Longrightarrow> f(x i) = y i"
               and fg_sub: "{x. ~ (f x = x \<and> g x = x)} \<subseteq> S"
               and bo_fg: "bounded {x. ~ (f x = x \<and> g x = x)}"
    using insert.IH [OF xyS pw] insert.prems by (blast intro: that)
  then have "\<exists>f g. homeomorphism T T f g \<and> (\<forall>i \<in> K. f(x i) = y i) \<and>
                   {x. ~ (f x = x \<and> g x = x)} \<subseteq> S \<and> bounded {x. ~ (f x = x \<and> g x = x)}"
    using insert by blast
  have aff_eq: "affine hull (S - y ` K) = affine hull S"
    apply (rule affine_hull_Diff)
    apply (auto simp: insert)
    using \<open>y i \<in> S\<close> insert.hyps(2) xney xyS by fastforce
  have f_in_S: "f x \<in> S" if "x \<in> S" for x
    using homfg fg_sub homeomorphism_apply1 \<open>S \<subseteq> T\<close>
  proof -
    have "(f (f x) \<noteq> f x \<or> g (f x) \<noteq> f x) \<or> f x \<in> S"
      by (metis \<open>S \<subseteq> T\<close> homfg subsetD homeomorphism_apply1 that)
    then show ?thesis
      using fg_sub by force
  qed
  obtain h k where homhk: "homeomorphism T T h k" and heq: "h (f (x i)) = y i"
               and hk_sub: "{x. \<not> (h x = x \<and> k x = x)} \<subseteq> S - y ` K"
               and bo_hk:  "bounded {x. \<not> (h x = x \<and> k x = x)}"
  proof (rule homeomorphism_moving_point [of "S - y`K" T "f(x i)" "y i"])
    show "openin (subtopology euclidean (affine hull (S - y ` K))) (S - y ` K)"
      by (simp add: aff_eq openin_diff finite_imp_closedin image_subset_iff hull_inc insert xyS)
    show "S - y ` K \<subseteq> T"
      using \<open>S \<subseteq> T\<close> by auto
    show "T \<subseteq> affine hull (S - y ` K)"
      using insert by (simp add: aff_eq)
    show "connected (S - y ` K)"
    proof (rule connected_openin_diff_countable [OF \<open>connected S\<close> ope])
      show "\<not> collinear S"
        using collinear_aff_dim \<open>2 \<le> aff_dim S\<close> by force
      show "countable (y ` K)"
        using countable_finite insert.hyps(1) by blast
    qed
    show "f (x i) \<in> S - y ` K"
      apply (auto simp: f_in_S \<open>x i \<in> S\<close>)
        by (metis feq homfg \<open>x i \<in> S\<close> homeomorphism_def \<open>S \<subseteq> T\<close> \<open>i \<notin> K\<close> subsetCE xney xyS)
    show "y i \<in> S - y ` K"
      using insert.hyps xney by (auto simp: \<open>y i \<in> S\<close>)
  qed blast
  show ?case
  proof (intro exI conjI)
    show "homeomorphism T T (h \<circ> f) (g \<circ> k)"
      using homfg homhk homeomorphism_compose by blast
    show "\<forall>i \<in> insert i K. (h \<circ> f) (x i) = y i"
      using feq hk_sub by (auto simp: heq)
    show "{x. \<not> ((h \<circ> f) x = x \<and> (g \<circ> k) x = x)} \<subseteq> S"
      using fg_sub hk_sub by force
    have "bounded ({x. ~(f x = x \<and> g x = x)} \<union> {x. ~(h x = x \<and> k x = x)})"
      using bo_fg bo_hk bounded_Un by blast
    then show "bounded {x. \<not> ((h \<circ> f) x = x \<and> (g \<circ> k) x = x)}"
      by (rule bounded_subset) auto
  qed
qed

proposition homeomorphism_moving_points_exists:
  fixes S :: "'a::euclidean_space set"
  assumes 2: "2 \<le> DIM('a)" "open S" "connected S" "S \<subseteq> T" "finite K"
      and KS: "\<And>i. i \<in> K \<Longrightarrow> x i \<in> S \<and> y i \<in> S"
      and pw: "pairwise (\<lambda>i j. (x i \<noteq> x j) \<and> (y i \<noteq> y j)) K"
      and S: "S \<subseteq> T" "T \<subseteq> affine hull S" "connected S"
  obtains f g where "homeomorphism T T f g" "\<And>i. i \<in> K \<Longrightarrow> f(x i) = y i"
                    "{x. ~ (f x = x \<and> g x = x)} \<subseteq> S" "bounded {x. (~ (f x = x \<and> g x = x))}"
proof (cases "S = {}")
  case True
  then show ?thesis
    using KS homeomorphism_ident that by fastforce
next
  case False
  then have affS: "affine hull S = UNIV"
    by (simp add: affine_hull_open \<open>open S\<close>)
  then have ope: "openin (subtopology euclidean (affine hull S)) S"
    using \<open>open S\<close> open_openin by auto
  have "2 \<le> DIM('a)" by (rule 2)
  also have "... = aff_dim (UNIV :: 'a set)"
    by simp
  also have "... \<le> aff_dim S"
    by (metis aff_dim_UNIV aff_dim_affine_hull aff_dim_le_DIM affS)
  finally have "2 \<le> aff_dim S"
    by linarith
  then show ?thesis
    using homeomorphism_moving_points_exists_gen [OF \<open>finite K\<close> KS pw _ ope S] that by fastforce
qed


subsubsection\<open>The theorem \<open>homeomorphism_grouping_points_exists\<close>\<close>

lemma homeomorphism_grouping_point_1:
  fixes a::real and c::real
  assumes "a < b" "c < d"
  obtains f g where "homeomorphism (cbox a b) (cbox c d) f g" "f a = c" "f b = d"
proof -
  define f where "f \<equiv> \<lambda>x. ((d - c) / (b - a)) * x + (c - a * ((d - c) / (b - a)))"
  have "\<exists>g. homeomorphism (cbox a b) (cbox c d) f g"
  proof (rule homeomorphism_compact)
    show "continuous_on (cbox a b) f"
      apply (simp add: f_def)
      apply (intro continuous_intros)
      using assms by auto
    have "f ` {a..b} = {c..d}"
      unfolding f_def image_affinity_atLeastAtMost
      using assms sum_sqs_eq by (auto simp: divide_simps algebra_simps)
    then show "f ` cbox a b = cbox c d"
      by auto
    show "inj_on f (cbox a b)"
      unfolding f_def inj_on_def using assms by auto
  qed auto
  then obtain g where "homeomorphism (cbox a b) (cbox c d) f g" ..
  then show ?thesis
  proof
    show "f a = c"
      by (simp add: f_def)
    show "f b = d"
      using assms sum_sqs_eq [of a b] by (auto simp: f_def divide_simps algebra_simps)
  qed
qed

lemma homeomorphism_grouping_point_2:
  fixes a::real and w::real
  assumes hom_ab: "homeomorphism (cbox a b) (cbox u v) f1 g1"
      and hom_bc: "homeomorphism (cbox b c) (cbox v w) f2 g2"
      and "b \<in> cbox a c" "v \<in> cbox u w"
      and eq: "f1 a = u" "f1 b = v" "f2 b = v" "f2 c = w"
 obtains f g where "homeomorphism (cbox a c) (cbox u w) f g" "f a = u" "f c = w"
                   "\<And>x. x \<in> cbox a b \<Longrightarrow> f x = f1 x" "\<And>x. x \<in> cbox b c \<Longrightarrow> f x = f2 x"
proof -
  have le: "a \<le> b" "b \<le> c" "u \<le> v" "v \<le> w"
    using assms by simp_all
  then have ac: "cbox a c = cbox a b \<union> cbox b c" and uw: "cbox u w = cbox u v \<union> cbox v w"
    by auto
  define f where "f \<equiv> \<lambda>x. if x \<le> b then f1 x else f2 x"
  have "\<exists>g. homeomorphism (cbox a c) (cbox u w) f g"
  proof (rule homeomorphism_compact)
    have cf1: "continuous_on (cbox a b) f1"
      using hom_ab homeomorphism_cont1 by blast
    have cf2: "continuous_on (cbox b c) f2"
      using hom_bc homeomorphism_cont1 by blast
    show "continuous_on (cbox a c) f"
      apply (simp add: f_def)
      apply (rule continuous_on_cases_le [OF continuous_on_subset [OF cf1] continuous_on_subset [OF cf2]])
      using le eq apply (force simp: continuous_on_id)+
      done
    have "f ` cbox a b = f1 ` cbox a b" "f ` cbox b c = f2 ` cbox b c"
      unfolding f_def using eq by force+
    then show "f ` cbox a c = cbox u w"
      apply (simp only: ac uw image_Un)
      by (metis hom_ab hom_bc homeomorphism_def)
    have neq12: "f1 x \<noteq> f2 y" if x: "a \<le> x" "x \<le> b" and y: "b < y" "y \<le> c" for x y
    proof -
      have "f1 x \<in> cbox u v"
        by (metis hom_ab homeomorphism_def image_eqI mem_box_real(2) x)
      moreover have "f2 y \<in> cbox v w"
        by (metis (full_types) hom_bc homeomorphism_def image_subset_iff mem_box_real(2) not_le not_less_iff_gr_or_eq order_refl y)
      moreover have "f2 y \<noteq> f2 b"
        by (metis cancel_comm_monoid_add_class.diff_cancel diff_gt_0_iff_gt hom_bc homeomorphism_def le(2) less_imp_le less_numeral_extra(3) mem_box_real(2) order_refl y)
      ultimately show ?thesis
        using le eq by simp
    qed
    have "inj_on f1 (cbox a b)"
      by (metis (full_types) hom_ab homeomorphism_def inj_onI)
    moreover have "inj_on f2 (cbox b c)"
      by (metis (full_types) hom_bc homeomorphism_def inj_onI)
    ultimately show "inj_on f (cbox a c)"
      apply (simp (no_asm) add: inj_on_def)
      apply (simp add: f_def inj_on_eq_iff)
      using neq12  apply force
      done
  qed auto
  then obtain g where "homeomorphism (cbox a c) (cbox u w) f g" ..
  then show ?thesis
    apply (rule that)
    using eq le by (auto simp: f_def)
qed

lemma homeomorphism_grouping_point_3:
  fixes a::real
  assumes cbox_sub: "cbox c d \<subseteq> box a b" "cbox u v \<subseteq> box a b"
      and box_ne: "box c d \<noteq> {}" "box u v \<noteq> {}"
  obtains f g where "homeomorphism (cbox a b) (cbox a b) f g" "f a = a" "f b = b"
                    "\<And>x. x \<in> cbox c d \<Longrightarrow> f x \<in> cbox u v"
proof -
  have less: "a < c" "a < u" "d < b" "v < b" "c < d" "u < v" "cbox c d \<noteq> {}"
    using assms
    by (simp_all add: cbox_sub subset_eq)
  obtain f1 g1 where 1: "homeomorphism (cbox a c) (cbox a u) f1 g1"
                   and f1_eq: "f1 a = a" "f1 c = u"
    using homeomorphism_grouping_point_1 [OF \<open>a < c\<close> \<open>a < u\<close>] .
  obtain f2 g2 where 2: "homeomorphism (cbox c d) (cbox u v) f2 g2"
                   and f2_eq: "f2 c = u" "f2 d = v"
    using homeomorphism_grouping_point_1 [OF \<open>c < d\<close> \<open>u < v\<close>] .
  obtain f3 g3 where 3: "homeomorphism (cbox d b) (cbox v b) f3 g3"
                   and f3_eq: "f3 d = v" "f3 b = b"
    using homeomorphism_grouping_point_1 [OF \<open>d < b\<close> \<open>v < b\<close>] .
  obtain f4 g4 where 4: "homeomorphism (cbox a d) (cbox a v) f4 g4" and "f4 a = a" "f4 d = v"
                 and f4_eq: "\<And>x. x \<in> cbox a c \<Longrightarrow> f4 x = f1 x" "\<And>x. x \<in> cbox c d \<Longrightarrow> f4 x = f2 x"
    using homeomorphism_grouping_point_2 [OF 1 2] less  by (auto simp: f1_eq f2_eq)
  obtain f g where fg: "homeomorphism (cbox a b) (cbox a b) f g" "f a = a" "f b = b"
               and f_eq: "\<And>x. x \<in> cbox a d \<Longrightarrow> f x = f4 x" "\<And>x. x \<in> cbox d b \<Longrightarrow> f x = f3 x"
    using homeomorphism_grouping_point_2 [OF 4 3] less by (auto simp: f4_eq f3_eq f2_eq f1_eq)
  show ?thesis
    apply (rule that [OF fg])
    using f4_eq f_eq homeomorphism_image1 [OF 2]
    apply simp
    by (metis atLeastAtMost_iff box_real(1) box_real(2) cbox_sub(1) greaterThanLessThan_iff imageI less_eq_real_def subset_eq)
qed


lemma homeomorphism_grouping_point_4:
  fixes T :: "real set"
  assumes "open U" "open S" "connected S" "U \<noteq> {}" "finite K" "K \<subseteq> S" "U \<subseteq> S" "S \<subseteq> T"
  obtains f g where "homeomorphism T T f g"
                    "\<And>x. x \<in> K \<Longrightarrow> f x \<in> U" "{x. (~ (f x = x \<and> g x = x))} \<subseteq> S"
                    "bounded {x. (~ (f x = x \<and> g x = x))}"
proof -
  obtain c d where "box c d \<noteq> {}" "cbox c d \<subseteq> U"
  proof -
    obtain u where "u \<in> U"
      using \<open>U \<noteq> {}\<close> by blast
    then obtain e where "e > 0" "cball u e \<subseteq> U"
      using \<open>open U\<close> open_contains_cball by blast
    then show ?thesis
      by (rule_tac c=u and d="u+e" in that) (auto simp: dist_norm subset_iff)
  qed
  have "compact K"
    by (simp add: \<open>finite K\<close> finite_imp_compact)
  obtain a b where "box a b \<noteq> {}" "K \<subseteq> cbox a b" "cbox a b \<subseteq> S"
  proof (cases "K = {}")
    case True then show ?thesis
      using \<open>box c d \<noteq> {}\<close> \<open>cbox c d \<subseteq> U\<close> \<open>U \<subseteq> S\<close> that by blast
  next
    case False
    then obtain a b where "a \<in> K" "b \<in> K"
            and a: "\<And>x. x \<in> K \<Longrightarrow> a \<le> x" and b: "\<And>x. x \<in> K \<Longrightarrow> x \<le> b"
      using compact_attains_inf compact_attains_sup by (metis \<open>compact K\<close>)+
    obtain e where "e > 0" "cball b e \<subseteq> S"
      using \<open>open S\<close> open_contains_cball
      by (metis \<open>b \<in> K\<close> \<open>K \<subseteq> S\<close> subsetD)
    show ?thesis
    proof
      show "box a (b + e) \<noteq> {}"
        using \<open>0 < e\<close> \<open>b \<in> K\<close> a by force
      show "K \<subseteq> cbox a (b + e)"
        using \<open>0 < e\<close> a b by fastforce
      have "a \<in> S"
        using \<open>a \<in> K\<close> assms(6) by blast
      have "b + e \<in> S"
        using \<open>0 < e\<close> \<open>cball b e \<subseteq> S\<close>  by (force simp: dist_norm)
      show "cbox a (b + e) \<subseteq> S"
        using \<open>a \<in> S\<close> \<open>b + e \<in> S\<close> \<open>connected S\<close> connected_contains_Icc by auto
    qed
  qed
  obtain w z where "cbox w z \<subseteq> S" and sub_wz: "cbox a b \<union> cbox c d \<subseteq> box w z"
  proof -
    have "a \<in> S" "b \<in> S"
      using \<open>box a b \<noteq> {}\<close> \<open>cbox a b \<subseteq> S\<close> by auto
    moreover have "c \<in> S" "d \<in> S"
      using \<open>box c d \<noteq> {}\<close> \<open>cbox c d \<subseteq> U\<close> \<open>U \<subseteq> S\<close> by force+
    ultimately have "min a c \<in> S" "max b d \<in> S"
      by linarith+
    then obtain e1 e2 where "e1 > 0" "cball (min a c) e1 \<subseteq> S" "e2 > 0" "cball (max b d) e2 \<subseteq> S"
      using \<open>open S\<close> open_contains_cball by metis
    then have *: "min a c - e1 \<in> S" "max b d + e2 \<in> S"
      by (auto simp: dist_norm)
    show ?thesis
    proof
      show "cbox (min a c - e1) (max b d+ e2) \<subseteq> S"
        using * \<open>connected S\<close> connected_contains_Icc by auto
      show "cbox a b \<union> cbox c d \<subseteq> box (min a c - e1) (max b d + e2)"
        using \<open>0 < e1\<close> \<open>0 < e2\<close> by auto
    qed
  qed
  then
  obtain f g where hom: "homeomorphism (cbox w z) (cbox w z) f g"
               and "f w = w" "f z = z"
               and fin: "\<And>x. x \<in> cbox a b \<Longrightarrow> f x \<in> cbox c d"
    using homeomorphism_grouping_point_3 [of a b w z c d]
    using \<open>box a b \<noteq> {}\<close> \<open>box c d \<noteq> {}\<close> by blast
  have contfg: "continuous_on (cbox w z) f" "continuous_on (cbox w z) g"
    using hom homeomorphism_def by blast+
  define f' where "f' \<equiv> \<lambda>x. if x \<in> cbox w z then f x else x"
  define g' where "g' \<equiv> \<lambda>x. if x \<in> cbox w z then g x else x"
  show ?thesis
  proof
    have T: "cbox w z \<union> (T - box w z) = T"
      using \<open>cbox w z \<subseteq> S\<close> \<open>S \<subseteq> T\<close> by auto
    show "homeomorphism T T f' g'"
    proof
      have clo: "closedin (subtopology euclidean (cbox w z \<union> (T - box w z))) (T - box w z)"
        by (metis Diff_Diff_Int Diff_subset T closedin_def open_box openin_open_Int topspace_euclidean_subtopology)
      have "continuous_on (cbox w z \<union> (T - box w z)) f'" "continuous_on (cbox w z \<union> (T - box w z)) g'"
        unfolding f'_def g'_def
         apply (safe intro!: continuous_on_cases_local contfg continuous_on_id clo)
         apply (simp_all add: closed_subset)
        using \<open>f w = w\<close> \<open>f z = z\<close> apply force
        by (metis \<open>f w = w\<close> \<open>f z = z\<close> hom homeomorphism_def less_eq_real_def mem_box_real(2))
      then show "continuous_on T f'" "continuous_on T g'"
        by (simp_all only: T)
      show "f' ` T \<subseteq> T"
        unfolding f'_def
        by clarsimp (metis \<open>cbox w z \<subseteq> S\<close> \<open>S \<subseteq> T\<close> subsetD hom homeomorphism_def imageI mem_box_real(2))
      show "g' ` T \<subseteq> T"
        unfolding g'_def
        by clarsimp (metis \<open>cbox w z \<subseteq> S\<close> \<open>S \<subseteq> T\<close> subsetD hom homeomorphism_def imageI mem_box_real(2))
      show "\<And>x. x \<in> T \<Longrightarrow> g' (f' x) = x"
        unfolding f'_def g'_def
        using homeomorphism_apply1 [OF hom]  homeomorphism_image1 [OF hom] by fastforce
      show "\<And>y. y \<in> T \<Longrightarrow> f' (g' y) = y"
        unfolding f'_def g'_def
        using homeomorphism_apply2 [OF hom]  homeomorphism_image2 [OF hom] by fastforce
    qed
    show "\<And>x. x \<in> K \<Longrightarrow> f' x \<in> U"
      using fin sub_wz \<open>K \<subseteq> cbox a b\<close> \<open>cbox c d \<subseteq> U\<close> by (force simp: f'_def)
    show "{x. \<not> (f' x = x \<and> g' x = x)} \<subseteq> S"
      using \<open>cbox w z \<subseteq> S\<close> by (auto simp: f'_def g'_def)
    show "bounded {x. \<not> (f' x = x \<and> g' x = x)}"
      apply (rule bounded_subset [of "cbox w z"])
      using bounded_cbox apply blast
      apply (auto simp: f'_def g'_def)
      done
  qed
qed

proposition homeomorphism_grouping_points_exists:
  fixes S :: "'a::euclidean_space set"
  assumes "open U" "open S" "connected S" "U \<noteq> {}" "finite K" "K \<subseteq> S" "U \<subseteq> S" "S \<subseteq> T"
  obtains f g where "homeomorphism T T f g" "{x. (~ (f x = x \<and> g x = x))} \<subseteq> S"
                    "bounded {x. (~ (f x = x \<and> g x = x))}" "\<And>x. x \<in> K \<Longrightarrow> f x \<in> U"
proof (cases "2 \<le> DIM('a)")
  case True
  have TS: "T \<subseteq> affine hull S"
    using affine_hull_open assms by blast
  have "infinite U"
    using \<open>open U\<close> \<open>U \<noteq> {}\<close> finite_imp_not_open by blast
  then obtain P where "P \<subseteq> U" "finite P" "card K = card P"
    using infinite_arbitrarily_large by metis
  then obtain \<gamma> where \<gamma>: "bij_betw \<gamma> K P"
    using \<open>finite K\<close> finite_same_card_bij by blast
  obtain f g where "homeomorphism T T f g" "\<And>i. i \<in> K \<Longrightarrow> f (id i) = \<gamma> i" "{x. \<not> (f x = x \<and> g x = x)} \<subseteq> S" "bounded {x. \<not> (f x = x \<and> g x = x)}"
  proof (rule homeomorphism_moving_points_exists [OF True \<open>open S\<close> \<open>connected S\<close> \<open>S \<subseteq> T\<close> \<open>finite K\<close>])
    show "\<And>i. i \<in> K \<Longrightarrow> id i \<in> S \<and> \<gamma> i \<in> S"
      using \<open>P \<subseteq> U\<close> \<open>bij_betw \<gamma> K P\<close> \<open>K \<subseteq> S\<close> \<open>U \<subseteq> S\<close> bij_betwE by blast
    show "pairwise (\<lambda>i j. id i \<noteq> id j \<and> \<gamma> i \<noteq> \<gamma> j) K"
      using \<gamma> by (auto simp: pairwise_def bij_betw_def inj_on_def)
  qed (use affine_hull_open assms that in auto)
  then show ?thesis
    using \<gamma> \<open>P \<subseteq> U\<close> bij_betwE by (fastforce simp add: intro!: that)
next
  case False
  with DIM_positive have "DIM('a) = 1"
    by (simp add: dual_order.antisym)
  then obtain h::"'a \<Rightarrow>real" and j
  where "linear h" "linear j"
    and noh: "\<And>x. norm(h x) = norm x" and noj: "\<And>y. norm(j y) = norm y"
    and hj:  "\<And>x. j(h x) = x" "\<And>y. h(j y) = y"
    and ranh: "surj h"
    using isomorphisms_UNIV_UNIV
    by (metis (mono_tags, hide_lams) DIM_real UNIV_eq_I range_eqI)
  obtain f g where hom: "homeomorphism (h ` T) (h ` T) f g"
               and f: "\<And>x. x \<in> h ` K \<Longrightarrow> f x \<in> h ` U"
               and sub: "{x. \<not> (f x = x \<and> g x = x)} \<subseteq> h ` S"
               and bou: "bounded {x. \<not> (f x = x \<and> g x = x)}"
    apply (rule homeomorphism_grouping_point_4 [of "h ` U" "h ` S" "h ` K" "h ` T"])
    by (simp_all add: assms image_mono  \<open>linear h\<close> open_surjective_linear_image connected_linear_image ranh)
  have jf: "j (f (h x)) = x \<longleftrightarrow> f (h x) = h x" for x
    by (metis hj)
  have jg: "j (g (h x)) = x \<longleftrightarrow> g (h x) = h x" for x
    by (metis hj)
  have cont_hj: "continuous_on X h"  "continuous_on Y j" for X Y
    by (simp_all add: \<open>linear h\<close> \<open>linear j\<close> linear_linear linear_continuous_on)
  show ?thesis
  proof
    show "homeomorphism T T (j \<circ> f \<circ> h) (j \<circ> g \<circ> h)"
    proof
      show "continuous_on T (j \<circ> f \<circ> h)"
        apply (intro continuous_on_compose cont_hj)
        using hom homeomorphism_def by blast
      show "continuous_on T (j \<circ> g \<circ> h)"
        apply (intro continuous_on_compose cont_hj)
        using hom homeomorphism_def by blast
      show "(j \<circ> f \<circ> h) ` T \<subseteq> T"
        by clarsimp (metis (mono_tags, hide_lams) hj(1) hom homeomorphism_def imageE imageI)
      show "(j \<circ> g \<circ> h) ` T \<subseteq> T"
        by clarsimp (metis (mono_tags, hide_lams) hj(1) hom homeomorphism_def imageE imageI)
      show "\<And>x. x \<in> T \<Longrightarrow> (j \<circ> g \<circ> h) ((j \<circ> f \<circ> h) x) = x"
        using hj hom homeomorphism_apply1 by fastforce
      show "\<And>y. y \<in> T \<Longrightarrow> (j \<circ> f \<circ> h) ((j \<circ> g \<circ> h) y) = y"
        using hj hom homeomorphism_apply2 by fastforce
    qed
    show "{x. \<not> ((j \<circ> f \<circ> h) x = x \<and> (j \<circ> g \<circ> h) x = x)} \<subseteq> S"
      apply (clarsimp simp: jf jg hj)
      using sub hj
      apply (drule_tac c="h x" in subsetD, force)
      by (metis imageE)
    have "bounded (j ` {x. (~ (f x = x \<and> g x = x))})"
      apply (rule bounded_linear_image [OF bou])
      using \<open>linear j\<close> linear_conv_bounded_linear by auto
    moreover
    have *: "{x. ~((j \<circ> f \<circ> h) x = x \<and> (j \<circ> g \<circ> h) x = x)} = j ` {x. (~ (f x = x \<and> g x = x))}"
      using hj apply (auto simp: jf jg image_iff, metis+)
      done
    ultimately show "bounded {x. \<not> ((j \<circ> f \<circ> h) x = x \<and> (j \<circ> g \<circ> h) x = x)}"
      by metis
    show "\<And>x. x \<in> K \<Longrightarrow> (j \<circ> f \<circ> h) x \<in> U"
      using f hj by fastforce
  qed
qed


proposition homeomorphism_grouping_points_exists_gen:
  fixes S :: "'a::euclidean_space set"
  assumes opeU: "openin (subtopology euclidean S) U"
      and opeS: "openin (subtopology euclidean (affine hull S)) S"
      and "U \<noteq> {}" "finite K" "K \<subseteq> S" and S: "S \<subseteq> T" "T \<subseteq> affine hull S" "connected S"
  obtains f g where "homeomorphism T T f g" "{x. (~ (f x = x \<and> g x = x))} \<subseteq> S"
                    "bounded {x. (~ (f x = x \<and> g x = x))}" "\<And>x. x \<in> K \<Longrightarrow> f x \<in> U"
proof (cases "2 \<le> aff_dim S")
  case True
  have opeU': "openin (subtopology euclidean (affine hull S)) U"
    using opeS opeU openin_trans by blast
  obtain u where "u \<in> U" "u \<in> S"
    using \<open>U \<noteq> {}\<close> opeU openin_imp_subset by fastforce+
  have "infinite U"
    apply (rule infinite_openin [OF opeU \<open>u \<in> U\<close>])
    apply (rule connected_imp_perfect_aff_dim [OF \<open>connected S\<close> _ \<open>u \<in> S\<close>])
    using True apply simp
    done
  then obtain P where "P \<subseteq> U" "finite P" "card K = card P"
    using infinite_arbitrarily_large by metis
  then obtain \<gamma> where \<gamma>: "bij_betw \<gamma> K P"
    using \<open>finite K\<close> finite_same_card_bij by blast
  have "\<exists>f g. homeomorphism T T f g \<and> (\<forall>i \<in> K. f(id i) = \<gamma> i) \<and>
               {x. ~ (f x = x \<and> g x = x)} \<subseteq> S \<and> bounded {x. ~ (f x = x \<and> g x = x)}"
  proof (rule homeomorphism_moving_points_exists_gen [OF \<open>finite K\<close> _ _ True opeS S])
    show "\<And>i. i \<in> K \<Longrightarrow> id i \<in> S \<and> \<gamma> i \<in> S"
      by (metis id_apply opeU openin_contains_cball subsetCE \<open>P \<subseteq> U\<close> \<open>bij_betw \<gamma> K P\<close> \<open>K \<subseteq> S\<close> bij_betwE)
    show "pairwise (\<lambda>i j. id i \<noteq> id j \<and> \<gamma> i \<noteq> \<gamma> j) K"
      using \<gamma> by (auto simp: pairwise_def bij_betw_def inj_on_def)
  qed
  then show ?thesis
    using \<gamma> \<open>P \<subseteq> U\<close> bij_betwE by (fastforce simp add: intro!: that)
next
  case False
  with aff_dim_geq [of S] consider "aff_dim S = -1" | "aff_dim S = 0" | "aff_dim S = 1" by linarith
  then show ?thesis
  proof cases
    assume "aff_dim S = -1"
    then have "S = {}"
      using aff_dim_empty by blast
    then have "False"
      using \<open>U \<noteq> {}\<close> \<open>K \<subseteq> S\<close> openin_imp_subset [OF opeU] by blast
    then show ?thesis ..
  next
    assume "aff_dim S = 0"
    then obtain a where "S = {a}"
      using aff_dim_eq_0 by blast
    then have "K \<subseteq> U"
      using \<open>U \<noteq> {}\<close> \<open>K \<subseteq> S\<close> openin_imp_subset [OF opeU] by blast
    show ?thesis
      apply (rule that [of id id])
      using \<open>K \<subseteq> U\<close> by (auto simp: continuous_on_id intro: homeomorphismI)
  next
    assume "aff_dim S = 1"
    then have "affine hull S homeomorphic (UNIV :: real set)"
      by (auto simp: homeomorphic_affine_sets)
    then obtain h::"'a\<Rightarrow>real" and j where homhj: "homeomorphism (affine hull S) UNIV h j"
      using homeomorphic_def by blast
    then have h: "\<And>x. x \<in> affine hull S \<Longrightarrow> j(h(x)) = x" and j: "\<And>y. j y \<in> affine hull S \<and> h(j y) = y"
      by (auto simp: homeomorphism_def)
    have connh: "connected (h ` S)"
      by (meson Topological_Spaces.connected_continuous_image \<open>connected S\<close> homeomorphism_cont1 homeomorphism_of_subsets homhj hull_subset top_greatest)
    have hUS: "h ` U \<subseteq> h ` S"
      by (meson homeomorphism_imp_open_map homeomorphism_of_subsets homhj hull_subset opeS opeU open_UNIV openin_open_eq)
    have op: "openin (subtopology euclidean (affine hull S)) U \<Longrightarrow> open (h ` U)" for U
      using homeomorphism_imp_open_map [OF homhj]  by simp
    have "open (h ` U)" "open (h ` S)"
      by (auto intro: opeS opeU openin_trans op)
    then obtain f g where hom: "homeomorphism (h ` T) (h ` T) f g"
                 and f: "\<And>x. x \<in> h ` K \<Longrightarrow> f x \<in> h ` U"
                 and sub: "{x. \<not> (f x = x \<and> g x = x)} \<subseteq> h ` S"
                 and bou: "bounded {x. \<not> (f x = x \<and> g x = x)}"
      apply (rule homeomorphism_grouping_points_exists [of "h ` U" "h ` S" "h ` K" "h ` T"])
      using assms by (auto simp: connh hUS)
    have jf: "\<And>x. x \<in> affine hull S \<Longrightarrow> j (f (h x)) = x \<longleftrightarrow> f (h x) = h x"
      by (metis h j)
    have jg: "\<And>x. x \<in> affine hull S \<Longrightarrow> j (g (h x)) = x \<longleftrightarrow> g (h x) = h x"
      by (metis h j)
    have cont_hj: "continuous_on T h"  "continuous_on Y j" for Y
      apply (rule continuous_on_subset [OF _ \<open>T \<subseteq> affine hull S\<close>])
      using homeomorphism_def homhj apply blast
      by (meson continuous_on_subset homeomorphism_def homhj top_greatest)
    define f' where "f' \<equiv> \<lambda>x. if x \<in> affine hull S then (j \<circ> f \<circ> h) x else x"
    define g' where "g' \<equiv> \<lambda>x. if x \<in> affine hull S then (j \<circ> g \<circ> h) x else x"
    show ?thesis
    proof
      show "homeomorphism T T f' g'"
      proof
        have "continuous_on T (j \<circ> f \<circ> h)"
          apply (intro continuous_on_compose cont_hj)
          using hom homeomorphism_def by blast
        then show "continuous_on T f'"
          apply (rule continuous_on_eq)
          using \<open>T \<subseteq> affine hull S\<close> f'_def by auto
        have "continuous_on T (j \<circ> g \<circ> h)"
          apply (intro continuous_on_compose cont_hj)
          using hom homeomorphism_def by blast
        then show "continuous_on T g'"
          apply (rule continuous_on_eq)
          using \<open>T \<subseteq> affine hull S\<close> g'_def by auto
        show "f' ` T \<subseteq> T"
        proof (clarsimp simp: f'_def)
          fix x assume "x \<in> T"
          then have "f (h x) \<in> h ` T"
            by (metis (no_types) hom homeomorphism_def image_subset_iff subset_refl)
          then show "j (f (h x)) \<in> T"
            using \<open>T \<subseteq> affine hull S\<close> h by auto
        qed
        show "g' ` T \<subseteq> T"
        proof (clarsimp simp: g'_def)
          fix x assume "x \<in> T"
          then have "g (h x) \<in> h ` T"
            by (metis (no_types) hom homeomorphism_def image_subset_iff subset_refl)
          then show "j (g (h x)) \<in> T"
            using \<open>T \<subseteq> affine hull S\<close> h by auto
        qed
        show "\<And>x. x \<in> T \<Longrightarrow> g' (f' x) = x"
          using h j hom homeomorphism_apply1 by (fastforce simp add: f'_def g'_def)
        show "\<And>y. y \<in> T \<Longrightarrow> f' (g' y) = y"
          using h j hom homeomorphism_apply2 by (fastforce simp add: f'_def g'_def)
      qed
    next
      show "{x. \<not> (f' x = x \<and> g' x = x)} \<subseteq> S"
        apply (clarsimp simp: f'_def g'_def jf jg)
        apply (rule imageE [OF subsetD [OF sub]], force)
        by (metis h hull_inc)
    next
      have "bounded (j ` {x. (~ (f x = x \<and> g x = x))})"
        apply (rule bounded_closure_image)
        apply (rule compact_imp_bounded)
        using bou by (auto simp: compact_continuous_image cont_hj)
      moreover
      have *: "{x \<in> affine hull S. j (f (h x)) \<noteq> x \<or> j (g (h x)) \<noteq> x} = j ` {x. (~ (f x = x \<and> g x = x))}"
        using h j by (auto simp: image_iff; metis)
      ultimately have "bounded {x \<in> affine hull S. j (f (h x)) \<noteq> x \<or> j (g (h x)) \<noteq> x}"
        by metis
      then show "bounded {x. \<not> (f' x = x \<and> g' x = x)}"
        by (simp add: f'_def g'_def Collect_mono bounded_subset)
    next
      show "f' x \<in> U" if "x \<in> K" for x
      proof -
        have "U \<subseteq> S"
          using opeU openin_imp_subset by blast
        then have "j (f (h x)) \<in> U"
          using f h hull_subset that by fastforce
        then show "f' x \<in> U"
          using \<open>K \<subseteq> S\<close> S f'_def that by auto
      qed
    qed
  qed
qed

subsection\<open>nullhomotopic mappings\<close>

text\<open> A mapping out of a sphere is nullhomotopic iff it extends to the ball.
This even works out in the degenerate cases when the radius is \<open>\<le>\<close> 0, and
we also don't need to explicitly assume continuity since it's already implicit
in both sides of the equivalence.\<close>

lemma nullhomotopic_from_lemma:
  assumes contg: "continuous_on (cball a r - {a}) g"
      and fa: "\<And>e. 0 < e
               \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>x. x \<noteq> a \<and> norm(x - a) < d \<longrightarrow> norm(g x - f a) < e)"
      and r: "\<And>x. x \<in> cball a r \<and> x \<noteq> a \<Longrightarrow> f x = g x"
    shows "continuous_on (cball a r) f"
proof (clarsimp simp: continuous_on_eq_continuous_within Ball_def)
  fix x
  assume x: "dist a x \<le> r"
  show "continuous (at x within cball a r) f"
  proof (cases "x=a")
    case True
    then show ?thesis
      by (metis continuous_within_eps_delta fa dist_norm dist_self r)
  next
    case False
    show ?thesis
    proof (rule continuous_transform_within [where f=g and d = "norm(x-a)"])
      have "\<exists>d>0. \<forall>x'\<in>cball a r.
                      dist x' x < d \<longrightarrow> dist (g x') (g x) < e" if "e>0" for e
      proof -
        obtain d where "d > 0"
           and d: "\<And>x'. \<lbrakk>dist x' a \<le> r; x' \<noteq> a; dist x' x < d\<rbrakk> \<Longrightarrow>
                                 dist (g x') (g x) < e"
          using contg False x \<open>e>0\<close>
          unfolding continuous_on_iff by (fastforce simp add: dist_commute intro: that)
        show ?thesis
          using \<open>d > 0\<close> \<open>x \<noteq> a\<close>
          by (rule_tac x="min d (norm(x - a))" in exI)
             (auto simp: dist_commute dist_norm [symmetric]  intro!: d)
      qed
      then show "continuous (at x within cball a r) g"
        using contg False by (auto simp: continuous_within_eps_delta)
      show "0 < norm (x - a)"
        using False by force
      show "x \<in> cball a r"
        by (simp add: x)
      show "\<And>x'. \<lbrakk>x' \<in> cball a r; dist x' x < norm (x - a)\<rbrakk>
        \<Longrightarrow> g x' = f x'"
        by (metis dist_commute dist_norm less_le r)
    qed
  qed
qed

proposition nullhomotopic_from_sphere_extension:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  shows  "(\<exists>c. homotopic_with (\<lambda>x. True) (sphere a r) S f (\<lambda>x. c)) \<longleftrightarrow>
          (\<exists>g. continuous_on (cball a r) g \<and> g ` (cball a r) \<subseteq> S \<and>
               (\<forall>x \<in> sphere a r. g x = f x))"
         (is "?lhs = ?rhs")
proof (cases r "0::real" rule: linorder_cases)
  case less
  then show ?thesis by simp
next
  case equal
  with continuous_on_const show ?thesis
    apply (auto simp: homotopic_with)
    apply (rule_tac x="\<lambda>x. h (0, a)" in exI)
    apply (fastforce simp add:)
    done
next
  case greater
  let ?P = "continuous_on {x. norm(x - a) = r} f \<and> f ` {x. norm(x - a) = r} \<subseteq> S"
  have ?P if ?lhs using that
  proof
    fix c
    assume c: "homotopic_with (\<lambda>x. True) (sphere a r) S f (\<lambda>x. c)"
    then have contf: "continuous_on (sphere a r) f" and fim: "f ` sphere a r \<subseteq> S"
      by (auto simp: homotopic_with_imp_subset1 homotopic_with_imp_continuous)
    show ?P
      using contf fim by (auto simp: sphere_def dist_norm norm_minus_commute)
  qed
  moreover have ?P if ?rhs using that
  proof
    fix g
    assume g: "continuous_on (cball a r) g \<and> g ` cball a r \<subseteq> S \<and> (\<forall>xa\<in>sphere a r. g xa = f xa)"
    then
    show ?P
      apply (safe elim!: continuous_on_eq [OF continuous_on_subset])
      apply (auto simp: dist_norm norm_minus_commute)
      by (metis dist_norm image_subset_iff mem_sphere norm_minus_commute sphere_cball subsetCE)
  qed
  moreover have ?thesis if ?P
  proof
    assume ?lhs
    then obtain c where "homotopic_with (\<lambda>x. True) (sphere a r) S (\<lambda>x. c) f"
      using homotopic_with_sym by blast
    then obtain h where conth: "continuous_on ({0..1::real} \<times> sphere a r) h"
                    and him: "h ` ({0..1} \<times> sphere a r) \<subseteq> S"
                    and h: "\<And>x. h(0, x) = c" "\<And>x. h(1, x) = f x"
      by (auto simp: homotopic_with_def)
    obtain b1::'M where "b1 \<in> Basis"
      using SOME_Basis by auto
    have "c \<in> S"
      apply (rule him [THEN subsetD])
      apply (rule_tac x = "(0, a + r *\<^sub>R b1)" in image_eqI)
      using h greater \<open>b1 \<in> Basis\<close>
       apply (auto simp: dist_norm)
      done
    have uconth: "uniformly_continuous_on ({0..1::real} \<times> (sphere a r)) h"
      by (force intro: compact_Times conth compact_uniformly_continuous)
    let ?g = "\<lambda>x. h (norm (x - a)/r,
                     a + (if x = a then r *\<^sub>R b1 else (r / norm(x - a)) *\<^sub>R (x - a)))"
    let ?g' = "\<lambda>x. h (norm (x - a)/r, a + (r / norm(x - a)) *\<^sub>R (x - a))"
    show ?rhs
    proof (intro exI conjI)
      have "continuous_on (cball a r - {a}) ?g'"
        apply (rule continuous_on_compose2 [OF conth])
         apply (intro continuous_intros)
        using greater apply (auto simp: dist_norm norm_minus_commute)
        done
      then show "continuous_on (cball a r) ?g"
      proof (rule nullhomotopic_from_lemma)
        show "\<exists>d>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < d \<longrightarrow> norm (?g' x - ?g a) < e" if "0 < e" for e
        proof -
          obtain d where "0 < d"
             and d: "\<And>x x'. \<lbrakk>x \<in> {0..1} \<times> sphere a r; x' \<in> {0..1} \<times> sphere a r; dist x' x < d\<rbrakk>
                        \<Longrightarrow> dist (h x') (h x) < e"
            using uniformly_continuous_onE [OF uconth \<open>0 < e\<close>] by auto
          have *: "norm (h (norm (x - a) / r,
                         a + (r / norm (x - a)) *\<^sub>R (x - a)) - h (0, a + r *\<^sub>R b1)) < e"
                   if "x \<noteq> a" "norm (x - a) < r" "norm (x - a) < d * r" for x
          proof -
            have "norm (h (norm (x - a) / r, a + (r / norm (x - a)) *\<^sub>R (x - a)) - h (0, a + r *\<^sub>R b1)) =
                  norm (h (norm (x - a) / r, a + (r / norm (x - a)) *\<^sub>R (x - a)) - h (0, a + (r / norm (x - a)) *\<^sub>R (x - a)))"
              by (simp add: h)
            also have "... < e"
              apply (rule d [unfolded dist_norm])
              using greater \<open>0 < d\<close> \<open>b1 \<in> Basis\<close> that
                by (auto simp: dist_norm divide_simps)
            finally show ?thesis .
          qed
          show ?thesis
            apply (rule_tac x = "min r (d * r)" in exI)
            using greater \<open>0 < d\<close> by (auto simp: *)
        qed
        show "\<And>x. x \<in> cball a r \<and> x \<noteq> a \<Longrightarrow> ?g x = ?g' x"
          by auto
      qed
    next
      show "?g ` cball a r \<subseteq> S"
        using greater him \<open>c \<in> S\<close>
        by (force simp: h dist_norm norm_minus_commute)
    next
      show "\<forall>x\<in>sphere a r. ?g x = f x"
        using greater by (auto simp: h dist_norm norm_minus_commute)
    qed
  next
    assume ?rhs
    then obtain g where contg: "continuous_on (cball a r) g"
                    and gim: "g ` cball a r \<subseteq> S"
                    and gf: "\<forall>x \<in> sphere a r. g x = f x"
      by auto
    let ?h = "\<lambda>y. g (a + (fst y) *\<^sub>R (snd y - a))"
    have "continuous_on ({0..1} \<times> sphere a r) ?h"
      apply (rule continuous_on_compose2 [OF contg])
       apply (intro continuous_intros)
      apply (auto simp: dist_norm norm_minus_commute mult_left_le_one_le)
      done
    moreover
    have "?h ` ({0..1} \<times> sphere a r) \<subseteq> S"
      by (auto simp: dist_norm norm_minus_commute mult_left_le_one_le gim [THEN subsetD])
    moreover
    have "\<forall>x\<in>sphere a r. ?h (0, x) = g a" "\<forall>x\<in>sphere a r. ?h (1, x) = f x"
      by (auto simp: dist_norm norm_minus_commute mult_left_le_one_le gf)
    ultimately
    show ?lhs
      apply (subst homotopic_with_sym)
      apply (rule_tac x="g a" in exI)
      apply (auto simp: homotopic_with)
      done
  qed
  ultimately
  show ?thesis by meson
qed

end
