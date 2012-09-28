(*  Title:      HOL/Multivariate_Analysis/Path_Connected.thy
    Author:     Robert Himmelmann, TU Muenchen
*)

header {* Continuous paths and path-connected sets *}

theory Path_Connected
imports Convex_Euclidean_Space
begin

subsection {* Paths. *}

definition path :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "path g \<longleftrightarrow> continuous_on {0 .. 1} g"

definition pathstart :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> 'a"
  where "pathstart g = g 0"

definition pathfinish :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> 'a"
  where "pathfinish g = g 1"

definition path_image :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> 'a set"
  where "path_image g = g ` {0 .. 1}"

definition reversepath :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> (real \<Rightarrow> 'a)"
  where "reversepath g = (\<lambda>x. g(1 - x))"

definition joinpaths :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a)"
    (infixr "+++" 75)
  where "g1 +++ g2 = (\<lambda>x. if x \<le> 1/2 then g1 (2 * x) else g2 (2 * x - 1))"

definition simple_path :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "simple_path g \<longleftrightarrow>
    (\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. g x = g y \<longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0)"

definition injective_path :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "injective_path g \<longleftrightarrow> (\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. g x = g y \<longrightarrow> x = y)"


subsection {* Some lemmas about these concepts. *}

lemma injective_imp_simple_path: "injective_path g \<Longrightarrow> simple_path g"
  unfolding injective_path_def simple_path_def by auto

lemma path_image_nonempty: "path_image g \<noteq> {}"
  unfolding path_image_def image_is_empty interval_eq_empty by auto 

lemma pathstart_in_path_image[intro]: "(pathstart g) \<in> path_image g"
  unfolding pathstart_def path_image_def by auto

lemma pathfinish_in_path_image[intro]: "(pathfinish g) \<in> path_image g"
  unfolding pathfinish_def path_image_def by auto

lemma connected_path_image[intro]: "path g \<Longrightarrow> connected(path_image g)"
  unfolding path_def path_image_def
  apply (erule connected_continuous_image)
  apply (rule convex_connected, rule convex_real_interval)
  done

lemma compact_path_image[intro]: "path g \<Longrightarrow> compact(path_image g)"
  unfolding path_def path_image_def
  by (erule compact_continuous_image, rule compact_interval)

lemma reversepath_reversepath[simp]: "reversepath(reversepath g) = g"
  unfolding reversepath_def by auto

lemma pathstart_reversepath[simp]: "pathstart(reversepath g) = pathfinish g"
  unfolding pathstart_def reversepath_def pathfinish_def by auto

lemma pathfinish_reversepath[simp]: "pathfinish(reversepath g) = pathstart g"
  unfolding pathstart_def reversepath_def pathfinish_def by auto

lemma pathstart_join[simp]: "pathstart (g1 +++ g2) = pathstart g1"
  unfolding pathstart_def joinpaths_def pathfinish_def by auto

lemma pathfinish_join[simp]: "pathfinish (g1 +++ g2) = pathfinish g2"
  unfolding pathstart_def joinpaths_def pathfinish_def by auto

lemma path_image_reversepath[simp]: "path_image(reversepath g) = path_image g"
proof -
  have *: "\<And>g. path_image(reversepath g) \<subseteq> path_image g"
    unfolding path_image_def subset_eq reversepath_def Ball_def image_iff
    apply(rule,rule,erule bexE)
    apply(rule_tac x="1 - xa" in bexI)
    apply auto
    done
  show ?thesis
    using *[of g] *[of "reversepath g"]
    unfolding reversepath_reversepath by auto
qed

lemma path_reversepath[simp]: "path (reversepath g) \<longleftrightarrow> path g"
proof -
  have *: "\<And>g. path g \<Longrightarrow> path (reversepath g)"
    unfolding path_def reversepath_def
    apply (rule continuous_on_compose[unfolded o_def, of _ "\<lambda>x. 1 - x"])
    apply (intro continuous_on_intros)
    apply (rule continuous_on_subset[of "{0..1}"], assumption)
    apply auto
    done
  show ?thesis
    using *[of "reversepath g"] *[of g]
    unfolding reversepath_reversepath
    by (rule iffI)
qed

lemmas reversepath_simps =
  path_reversepath path_image_reversepath pathstart_reversepath pathfinish_reversepath

lemma path_join[simp]:
  assumes "pathfinish g1 = pathstart g2"
  shows "path (g1 +++ g2) \<longleftrightarrow> path g1 \<and> path g2"
  unfolding path_def pathfinish_def pathstart_def
  apply rule defer
  apply(erule conjE)
proof -
  assume as: "continuous_on {0..1} (g1 +++ g2)"
  have *: "g1 = (\<lambda>x. g1 (2 *\<^sub>R x)) \<circ> (\<lambda>x. (1/2) *\<^sub>R x)"
      "g2 = (\<lambda>x. g2 (2 *\<^sub>R x - 1)) \<circ> (\<lambda>x. (1/2) *\<^sub>R (x + 1))"
    unfolding o_def by (auto simp add: add_divide_distrib)
  have "op *\<^sub>R (1 / 2) ` {0::real..1} \<subseteq> {0..1}"
    "(\<lambda>x. (1 / 2) *\<^sub>R (x + 1)) ` {(0::real)..1} \<subseteq> {0..1}"
    by auto
  then show "continuous_on {0..1} g1 \<and> continuous_on {0..1} g2"
    apply -
    apply rule
    apply (subst *) defer
    apply (subst *)
    apply (rule_tac[!] continuous_on_compose)
    apply (intro continuous_on_intros) defer
    apply (intro continuous_on_intros)
    apply (rule_tac[!] continuous_on_eq[of _ "g1 +++ g2"]) defer prefer 3
    apply (rule_tac[1-2] continuous_on_subset[of "{0 .. 1}"])
    apply (rule as, assumption, rule as, assumption)
    apply rule defer
    apply rule
  proof -
    fix x
    assume "x \<in> op *\<^sub>R (1 / 2) ` {0::real..1}"
    hence "x \<le> 1 / 2" unfolding image_iff by auto
    thus "(g1 +++ g2) x = g1 (2 *\<^sub>R x)" unfolding joinpaths_def by auto
  next
    fix x
    assume "x \<in> (\<lambda>x. (1 / 2) *\<^sub>R (x + 1)) ` {0::real..1}"
    hence "x \<ge> 1 / 2" unfolding image_iff by auto
    thus "(g1 +++ g2) x = g2 (2 *\<^sub>R x - 1)"
    proof (cases "x = 1 / 2")
      case True
      hence "x = (1/2) *\<^sub>R 1" by auto
      thus ?thesis
        unfolding joinpaths_def
        using assms[unfolded pathstart_def pathfinish_def]
        by (auto simp add: mult_ac)
    qed (auto simp add:le_less joinpaths_def)
  qed
next
  assume as:"continuous_on {0..1} g1" "continuous_on {0..1} g2"
  have *: "{0 .. 1::real} = {0.. (1/2)*\<^sub>R 1} \<union> {(1/2) *\<^sub>R 1 .. 1}" by auto
  have **: "op *\<^sub>R 2 ` {0..(1 / 2) *\<^sub>R 1} = {0..1::real}"
    apply (rule set_eqI, rule)
    unfolding image_iff
    defer
    apply (rule_tac x="(1/2)*\<^sub>R x" in bexI)
    apply auto
    done
  have ***: "(\<lambda>x. 2 *\<^sub>R x - 1) ` {(1 / 2) *\<^sub>R 1..1} = {0..1::real}"
    apply (auto simp add: image_def)
    apply (rule_tac x="(x + 1) / 2" in bexI)
    apply (auto simp add: add_divide_distrib)
    done
  show "continuous_on {0..1} (g1 +++ g2)"
    unfolding *
    apply (rule continuous_on_union)
    apply (rule closed_real_atLeastAtMost)+
  proof -
    show "continuous_on {0..(1 / 2) *\<^sub>R 1} (g1 +++ g2)"
      apply (rule continuous_on_eq[of _ "\<lambda>x. g1 (2 *\<^sub>R x)"]) defer
      unfolding o_def[THEN sym]
      apply (rule continuous_on_compose)
      apply (intro continuous_on_intros)
      unfolding **
      apply (rule as(1))
      unfolding joinpaths_def
      apply auto
      done
  next
    show "continuous_on {(1/2)*\<^sub>R1..1} (g1 +++ g2)"
      apply (rule continuous_on_eq[of _ "g2 \<circ> (\<lambda>x. 2 *\<^sub>R x - 1)"]) defer
      apply (rule continuous_on_compose)
      apply (intro continuous_on_intros)
      unfolding *** o_def joinpaths_def
      apply (rule as(2))
      using assms[unfolded pathstart_def pathfinish_def]
      apply (auto simp add: mult_ac)  
      done
  qed
qed

lemma path_image_join_subset: "path_image(g1 +++ g2) \<subseteq> (path_image g1 \<union> path_image g2)"
proof
  fix x
  assume "x \<in> path_image (g1 +++ g2)"
  then obtain y where y:"y\<in>{0..1}" "x = (if y \<le> 1 / 2 then g1 (2 *\<^sub>R y) else g2 (2 *\<^sub>R y - 1))"
    unfolding path_image_def image_iff joinpaths_def by auto
  thus "x \<in> path_image g1 \<union> path_image g2"
    apply (cases "y \<le> 1/2")
    apply (rule_tac UnI1) defer
    apply (rule_tac UnI2)
    unfolding y(2) path_image_def
    using y(1)
    apply (auto intro!: imageI)
    done
qed

lemma subset_path_image_join:
  assumes "path_image g1 \<subseteq> s" "path_image g2 \<subseteq> s"
  shows "path_image(g1 +++ g2) \<subseteq> s"
  using path_image_join_subset[of g1 g2] and assms by auto

lemma path_image_join:
  assumes "path g1" "path g2" "pathfinish g1 = pathstart g2"
  shows "path_image(g1 +++ g2) = (path_image g1) \<union> (path_image g2)"
  apply (rule, rule path_image_join_subset, rule)
  unfolding Un_iff
proof (erule disjE)
  fix x
  assume "x \<in> path_image g1"
  then obtain y where y: "y\<in>{0..1}" "x = g1 y"
    unfolding path_image_def image_iff by auto
  thus "x \<in> path_image (g1 +++ g2)"
    unfolding joinpaths_def path_image_def image_iff
    apply (rule_tac x="(1/2) *\<^sub>R y" in bexI)
    apply auto
    done
next
  fix x
  assume "x \<in> path_image g2"
  then obtain y where y: "y\<in>{0..1}" "x = g2 y"
    unfolding path_image_def image_iff by auto
  then show "x \<in> path_image (g1 +++ g2)"
    unfolding joinpaths_def path_image_def image_iff
    apply(rule_tac x="(1/2) *\<^sub>R (y + 1)" in bexI)
    using assms(3)[unfolded pathfinish_def pathstart_def]
    apply (auto simp add: add_divide_distrib) 
    done
qed

lemma not_in_path_image_join:
  assumes "x \<notin> path_image g1" "x \<notin> path_image g2"
  shows "x \<notin> path_image(g1 +++ g2)"
  using assms and path_image_join_subset[of g1 g2] by auto

lemma simple_path_reversepath:
  assumes "simple_path g"
  shows "simple_path (reversepath g)"
  using assms
  unfolding simple_path_def reversepath_def
  apply -
  apply (rule ballI)+
  apply (erule_tac x="1-x" in ballE, erule_tac x="1-y" in ballE)
  apply auto
  done

lemma simple_path_join_loop:
  assumes "injective_path g1" "injective_path g2" "pathfinish g2 = pathstart g1"
    "(path_image g1 \<inter> path_image g2) \<subseteq> {pathstart g1,pathstart g2}"
  shows "simple_path(g1 +++ g2)"
  unfolding simple_path_def
proof ((rule ballI)+, rule impI)
  let ?g = "g1 +++ g2"
  note inj = assms(1,2)[unfolded injective_path_def, rule_format]
  fix x y :: real
  assume xy: "x \<in> {0..1}" "y \<in> {0..1}" "?g x = ?g y"
  show "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
  proof (case_tac "x \<le> 1/2", case_tac[!] "y \<le> 1/2", unfold not_le)
    assume as: "x \<le> 1 / 2" "y \<le> 1 / 2"
    hence "g1 (2 *\<^sub>R x) = g1 (2 *\<^sub>R y)"
      using xy(3) unfolding joinpaths_def by auto
    moreover
    have "2 *\<^sub>R x \<in> {0..1}" "2 *\<^sub>R y \<in> {0..1}" using xy(1,2) as
      by auto
    ultimately
    show ?thesis using inj(1)[of "2*\<^sub>R x" "2*\<^sub>R y"] by auto
  next
    assume as:"x > 1 / 2" "y > 1 / 2"
    hence "g2 (2 *\<^sub>R x - 1) = g2 (2 *\<^sub>R y - 1)"
      using xy(3) unfolding joinpaths_def by auto
    moreover
    have "2 *\<^sub>R x - 1 \<in> {0..1}" "2 *\<^sub>R y - 1 \<in> {0..1}"
      using xy(1,2) as by auto
    ultimately
    show ?thesis using inj(2)[of "2*\<^sub>R x - 1" "2*\<^sub>R y - 1"] by auto
  next
    assume as:"x \<le> 1 / 2" "y > 1 / 2"
    hence "?g x \<in> path_image g1" "?g y \<in> path_image g2"
      unfolding path_image_def joinpaths_def
      using xy(1,2) by auto
    moreover
      have "?g y \<noteq> pathstart g2" using as(2) unfolding pathstart_def joinpaths_def
      using inj(2)[of "2 *\<^sub>R y - 1" 0] and xy(2)
      by (auto simp add: field_simps)
    ultimately
    have *:"?g x = pathstart g1" using assms(4) unfolding xy(3) by auto
    hence "x = 0" unfolding pathstart_def joinpaths_def using as(1) and xy(1)
      using inj(1)[of "2 *\<^sub>R x" 0] by auto
    moreover
    have "y = 1" using * unfolding xy(3) assms(3)[THEN sym]
      unfolding joinpaths_def pathfinish_def using as(2) and xy(2)
      using inj(2)[of "2 *\<^sub>R y - 1" 1] by auto
    ultimately show ?thesis by auto
  next
    assume as: "x > 1 / 2" "y \<le> 1 / 2"
    hence "?g x \<in> path_image g2" "?g y \<in> path_image g1"
      unfolding path_image_def joinpaths_def
      using xy(1,2) by auto
    moreover
      have "?g x \<noteq> pathstart g2" using as(1) unfolding pathstart_def joinpaths_def
      using inj(2)[of "2 *\<^sub>R x - 1" 0] and xy(1)
      by (auto simp add: field_simps)
    ultimately
    have *: "?g y = pathstart g1" using assms(4) unfolding xy(3) by auto
    hence "y = 0" unfolding pathstart_def joinpaths_def using as(2) and xy(2)
      using inj(1)[of "2 *\<^sub>R y" 0] by auto
    moreover
    have "x = 1" using * unfolding xy(3)[THEN sym] assms(3)[THEN sym]
      unfolding joinpaths_def pathfinish_def using as(1) and xy(1)
      using inj(2)[of "2 *\<^sub>R x - 1" 1] by auto
    ultimately show ?thesis by auto
  qed
qed

lemma injective_path_join:
  assumes "injective_path g1" "injective_path g2" "pathfinish g1 = pathstart g2"
    "(path_image g1 \<inter> path_image g2) \<subseteq> {pathstart g2}"
  shows "injective_path(g1 +++ g2)"
  unfolding injective_path_def
proof (rule, rule, rule)
  let ?g = "g1 +++ g2"
  note inj = assms(1,2)[unfolded injective_path_def, rule_format]
  fix x y
  assume xy: "x \<in> {0..1}" "y \<in> {0..1}" "(g1 +++ g2) x = (g1 +++ g2) y"
  show "x = y"
  proof (cases "x \<le> 1/2", case_tac[!] "y \<le> 1/2", unfold not_le)
    assume "x \<le> 1 / 2" "y \<le> 1 / 2"
    thus ?thesis using inj(1)[of "2*\<^sub>R x" "2*\<^sub>R y"] and xy
      unfolding joinpaths_def by auto
  next
    assume "x > 1 / 2" "y > 1 / 2"
    thus ?thesis using inj(2)[of "2*\<^sub>R x - 1" "2*\<^sub>R y - 1"] and xy
      unfolding joinpaths_def by auto
  next
    assume as: "x \<le> 1 / 2" "y > 1 / 2"
    hence "?g x \<in> path_image g1" "?g y \<in> path_image g2"
      unfolding path_image_def joinpaths_def
      using xy(1,2) by auto
    hence "?g x = pathfinish g1" "?g y = pathstart g2"
      using assms(4) unfolding assms(3) xy(3) by auto
    thus ?thesis
      using as and inj(1)[of "2 *\<^sub>R x" 1] inj(2)[of "2 *\<^sub>R y - 1" 0] and xy(1,2)
      unfolding pathstart_def pathfinish_def joinpaths_def
      by auto
  next
    assume as:"x > 1 / 2" "y \<le> 1 / 2" 
    hence "?g x \<in> path_image g2" "?g y \<in> path_image g1"
      unfolding path_image_def joinpaths_def
      using xy(1,2) by auto
    hence "?g x = pathstart g2" "?g y = pathfinish g1"
      using assms(4) unfolding assms(3) xy(3) by auto
    thus ?thesis using as and inj(2)[of "2 *\<^sub>R x - 1" 0] inj(1)[of "2 *\<^sub>R y" 1] and xy(1,2)
      unfolding pathstart_def pathfinish_def joinpaths_def
      by auto
  qed
qed

lemmas join_paths_simps = path_join path_image_join pathstart_join pathfinish_join
 

subsection {* Reparametrizing a closed curve to start at some chosen point. *}

definition "shiftpath a (f::real \<Rightarrow> 'a::topological_space) =
  (\<lambda>x. if (a + x) \<le> 1 then f(a + x) else f(a + x - 1))"

lemma pathstart_shiftpath: "a \<le> 1 \<Longrightarrow> pathstart(shiftpath a g) = g a"
  unfolding pathstart_def shiftpath_def by auto

lemma pathfinish_shiftpath:
  assumes "0 \<le> a" "pathfinish g = pathstart g"
  shows "pathfinish(shiftpath a g) = g a"
  using assms unfolding pathstart_def pathfinish_def shiftpath_def
  by auto

lemma endpoints_shiftpath:
  assumes "pathfinish g = pathstart g" "a \<in> {0 .. 1}" 
  shows "pathfinish(shiftpath a g) = g a" "pathstart(shiftpath a g) = g a"
  using assms by(auto intro!:pathfinish_shiftpath pathstart_shiftpath)

lemma closed_shiftpath:
  assumes "pathfinish g = pathstart g" "a \<in> {0..1}"
  shows "pathfinish(shiftpath a g) = pathstart(shiftpath a g)"
  using endpoints_shiftpath[OF assms] by auto

lemma path_shiftpath:
  assumes "path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
  shows "path(shiftpath a g)"
proof -
  have *: "{0 .. 1} = {0 .. 1-a} \<union> {1-a .. 1}" using assms(3) by auto
  have **: "\<And>x. x + a = 1 \<Longrightarrow> g (x + a - 1) = g (x + a)"
    using assms(2)[unfolded pathfinish_def pathstart_def] by auto
  show ?thesis
    unfolding path_def shiftpath_def *
    apply (rule continuous_on_union)
    apply (rule closed_real_atLeastAtMost)+
    apply (rule continuous_on_eq[of _ "g \<circ> (\<lambda>x. a + x)"]) prefer 3
    apply (rule continuous_on_eq[of _ "g \<circ> (\<lambda>x. a - 1 + x)"]) defer prefer 3
    apply (rule continuous_on_intros)+ prefer 2
    apply (rule continuous_on_intros)+
    apply (rule_tac[1-2] continuous_on_subset[OF assms(1)[unfolded path_def]])
    using assms(3) and **
    apply (auto, auto simp add: field_simps)
    done
qed

lemma shiftpath_shiftpath:
  assumes "pathfinish g = pathstart g" "a \<in> {0..1}" "x \<in> {0..1}" 
  shows "shiftpath (1 - a) (shiftpath a g) x = g x"
  using assms unfolding pathfinish_def pathstart_def shiftpath_def by auto

lemma path_image_shiftpath:
  assumes "a \<in> {0..1}" "pathfinish g = pathstart g"
  shows "path_image(shiftpath a g) = path_image g"
proof -
  { fix x
    assume as:"g 1 = g 0" "x \<in> {0..1::real}" " \<forall>y\<in>{0..1} \<inter> {x. \<not> a + x \<le> 1}. g x \<noteq> g (a + y - 1)" 
    hence "\<exists>y\<in>{0..1} \<inter> {x. a + x \<le> 1}. g x = g (a + y)"
    proof (cases "a \<le> x")
      case False
      thus ?thesis
        apply (rule_tac x="1 + x - a" in bexI)
        using as(1,2) and as(3)[THEN bspec[where x="1 + x - a"]] and assms(1)
        apply (auto simp add: field_simps atomize_not)
        done
    next
      case True
      thus ?thesis using as(1-2) and assms(1) apply(rule_tac x="x - a" in bexI)
        by(auto simp add: field_simps)
    qed
  }
  thus ?thesis
    using assms unfolding shiftpath_def path_image_def pathfinish_def pathstart_def
    by(auto simp add: image_iff)
qed


subsection {* Special case of straight-line paths. *}

definition linepath :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a"
  where "linepath a b = (\<lambda>x. (1 - x) *\<^sub>R a + x *\<^sub>R b)"

lemma pathstart_linepath[simp]: "pathstart(linepath a b) = a"
  unfolding pathstart_def linepath_def by auto

lemma pathfinish_linepath[simp]: "pathfinish(linepath a b) = b"
  unfolding pathfinish_def linepath_def by auto

lemma continuous_linepath_at[intro]: "continuous (at x) (linepath a b)"
  unfolding linepath_def by (intro continuous_intros)

lemma continuous_on_linepath[intro]: "continuous_on s (linepath a b)"
  using continuous_linepath_at by(auto intro!: continuous_at_imp_continuous_on)

lemma path_linepath[intro]: "path(linepath a b)"
  unfolding path_def by(rule continuous_on_linepath)

lemma path_image_linepath[simp]: "path_image(linepath a b) = (closed_segment a b)"
  unfolding path_image_def segment linepath_def
  apply (rule set_eqI, rule) defer
  unfolding mem_Collect_eq image_iff
  apply(erule exE)
  apply(rule_tac x="u *\<^sub>R 1" in bexI)
  apply auto
  done

lemma reversepath_linepath[simp]: "reversepath(linepath a b) = linepath b a"
  unfolding reversepath_def linepath_def
  by auto

lemma injective_path_linepath:
  assumes "a \<noteq> b"
  shows "injective_path (linepath a b)"
proof -
  { fix x y :: "real"
    assume "x *\<^sub>R b + y *\<^sub>R a = x *\<^sub>R a + y *\<^sub>R b"
    hence "(x - y) *\<^sub>R a = (x - y) *\<^sub>R b" by (simp add: algebra_simps)
    with assms have "x = y" by simp }
  thus ?thesis
    unfolding injective_path_def linepath_def
    by (auto simp add: algebra_simps)
qed

lemma simple_path_linepath[intro]: "a \<noteq> b \<Longrightarrow> simple_path(linepath a b)"
  by(auto intro!: injective_imp_simple_path injective_path_linepath)


subsection {* Bounding a point away from a path. *}

lemma not_on_path_ball:
  fixes g :: "real \<Rightarrow> 'a::heine_borel"
  assumes "path g" "z \<notin> path_image g"
  shows "\<exists>e > 0. ball z e \<inter> (path_image g) = {}"
proof -
  obtain a where "a \<in> path_image g" "\<forall>y \<in> path_image g. dist z a \<le> dist z y"
    using distance_attains_inf[OF _ path_image_nonempty, of g z]
    using compact_path_image[THEN compact_imp_closed, OF assms(1)] by auto
  thus ?thesis
    apply (rule_tac x="dist z a" in exI)
    using assms(2)
    apply (auto intro!: dist_pos_lt)
    done
qed

lemma not_on_path_cball:
  fixes g :: "real \<Rightarrow> 'a::heine_borel"
  assumes "path g" "z \<notin> path_image g"
  shows "\<exists>e>0. cball z e \<inter> (path_image g) = {}"
proof -
  obtain e where "ball z e \<inter> path_image g = {}" "e>0"
    using not_on_path_ball[OF assms] by auto
  moreover have "cball z (e/2) \<subseteq> ball z e" using `e>0` by auto
  ultimately show ?thesis apply(rule_tac x="e/2" in exI) by auto
qed


subsection {* Path component, considered as a "joinability" relation (from Tom Hales). *}

definition "path_component s x y \<longleftrightarrow>
  (\<exists>g. path g \<and> path_image g \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y)"

lemmas path_defs = path_def pathstart_def pathfinish_def path_image_def path_component_def 

lemma path_component_mem:
  assumes "path_component s x y"
  shows "x \<in> s" "y \<in> s"
  using assms unfolding path_defs by auto

lemma path_component_refl:
  assumes "x \<in> s"
  shows "path_component s x x"
  unfolding path_defs
  apply (rule_tac x="\<lambda>u. x" in exI)
  using assms apply (auto intro!:continuous_on_intros) done

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
  assumes "path_component s x y" "path_component s y z"
  shows "path_component s x z"
  using assms
  unfolding path_component_def
  apply -
  apply (erule exE)+
  apply (rule_tac x="g +++ ga" in exI)
  apply (auto simp add: path_image_join)
  done

lemma path_component_of_subset: "s \<subseteq> t \<Longrightarrow>  path_component s x y \<Longrightarrow> path_component t x y"
  unfolding path_component_def by auto


subsection {* Can also consider it as a set, as the name suggests. *}

lemma path_component_set:
  "{y. path_component s x y} =
    {y. (\<exists>g. path g \<and> path_image g \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y)}"
  apply (rule set_eqI)
  unfolding mem_Collect_eq
  unfolding path_component_def
  apply auto
  done

lemma path_component_subset: "{y. path_component s x y} \<subseteq> s"
  apply (rule, rule path_component_mem(2))
  apply auto
  done

lemma path_component_eq_empty: "{y. path_component s x y} = {} \<longleftrightarrow> x \<notin> s"
  apply rule
  apply (drule equals0D[of _ x]) defer
  apply (rule equals0I)
  unfolding mem_Collect_eq
  apply (drule path_component_mem(1))
  using path_component_refl
  apply auto
  done


subsection {* Path connectedness of a space. *}

definition "path_connected s \<longleftrightarrow>
  (\<forall>x\<in>s. \<forall>y\<in>s. \<exists>g. path g \<and> (path_image g) \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y)"

lemma path_connected_component: "path_connected s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. path_component s x y)"
  unfolding path_connected_def path_component_def by auto

lemma path_connected_component_set: "path_connected s \<longleftrightarrow> (\<forall>x\<in>s. {y. path_component s x y} = s)" 
  unfolding path_connected_component
  apply (rule, rule, rule, rule path_component_subset) 
  unfolding subset_eq mem_Collect_eq Ball_def
  apply auto
  done


subsection {* Some useful lemmas about path-connectedness. *}

lemma convex_imp_path_connected:
  fixes s :: "'a::real_normed_vector set"
  assumes "convex s" shows "path_connected s"
  unfolding path_connected_def
  apply (rule, rule, rule_tac x = "linepath x y" in exI)
  unfolding path_image_linepath
  using assms [unfolded convex_contains_segment]
  apply auto
  done

lemma path_connected_imp_connected:
  assumes "path_connected s"
  shows "connected s"
  unfolding connected_def not_ex
  apply (rule, rule, rule ccontr)
  unfolding not_not
  apply (erule conjE)+
proof -
  fix e1 e2
  assume as: "open e1" "open e2" "s \<subseteq> e1 \<union> e2" "e1 \<inter> e2 \<inter> s = {}" "e1 \<inter> s \<noteq> {}" "e2 \<inter> s \<noteq> {}"
  then obtain x1 x2 where obt:"x1\<in>e1\<inter>s" "x2\<in>e2\<inter>s" by auto
  then obtain g where g:"path g" "path_image g \<subseteq> s" "pathstart g = x1" "pathfinish g = x2"
    using assms[unfolded path_connected_def,rule_format,of x1 x2] by auto
  have *: "connected {0..1::real}"
    by (auto intro!: convex_connected convex_real_interval)
  have "{0..1} \<subseteq> {x \<in> {0..1}. g x \<in> e1} \<union> {x \<in> {0..1}. g x \<in> e2}"
    using as(3) g(2)[unfolded path_defs] by blast
  moreover have "{x \<in> {0..1}. g x \<in> e1} \<inter> {x \<in> {0..1}. g x \<in> e2} = {}"
    using as(4) g(2)[unfolded path_defs] unfolding subset_eq by auto 
  moreover have "{x \<in> {0..1}. g x \<in> e1} \<noteq> {} \<and> {x \<in> {0..1}. g x \<in> e2} \<noteq> {}"
    using g(3,4)[unfolded path_defs] using obt
    by (simp add: ex_in_conv [symmetric], metis zero_le_one order_refl)
  ultimately show False
    using *[unfolded connected_local not_ex, rule_format, of "{x\<in>{0..1}. g x \<in> e1}" "{x\<in>{0..1}. g x \<in> e2}"]
    using continuous_open_in_preimage[OF g(1)[unfolded path_def] as(1)]
    using continuous_open_in_preimage[OF g(1)[unfolded path_def] as(2)]
    by auto
qed

lemma open_path_component:
  fixes s :: "'a::real_normed_vector set" (*TODO: generalize to metric_space*)
  assumes "open s"
  shows "open {y. path_component s x y}"
  unfolding open_contains_ball
proof
  fix y
  assume as: "y \<in> {y. path_component s x y}"
  hence "y \<in> s"
    apply -
    apply (rule path_component_mem(2))
    unfolding mem_Collect_eq
    apply auto
    done
  then obtain e where e:"e>0" "ball y e \<subseteq> s"
    using assms[unfolded open_contains_ball] by auto
  show "\<exists>e > 0. ball y e \<subseteq> {y. path_component s x y}"
    apply (rule_tac x=e in exI)
    apply (rule,rule `e>0`, rule)
    unfolding mem_ball mem_Collect_eq
  proof -
    fix z
    assume "dist y z < e"
    thus "path_component s x z"
      apply (rule_tac path_component_trans[of _ _ y]) defer
      apply (rule path_component_of_subset[OF e(2)])
      apply (rule convex_imp_path_connected[OF convex_ball, unfolded path_connected_component, rule_format])
      using `e>0` as
      apply auto
      done
  qed
qed

lemma open_non_path_component:
  fixes s :: "'a::real_normed_vector set" (*TODO: generalize to metric_space*)
  assumes "open s"
  shows "open(s - {y. path_component s x y})"
  unfolding open_contains_ball
proof
  fix y
  assume as: "y\<in>s - {y. path_component s x y}"
  then obtain e where e:"e>0" "ball y e \<subseteq> s"
    using assms [unfolded open_contains_ball] by auto
  show "\<exists>e>0. ball y e \<subseteq> s - {y. path_component s x y}"
    apply (rule_tac x=e in exI)
    apply (rule, rule `e>0`, rule, rule) defer
  proof (rule ccontr)
    fix z
    assume "z \<in> ball y e" "\<not> z \<notin> {y. path_component s x y}"
    hence "y \<in> {y. path_component s x y}"
      unfolding not_not mem_Collect_eq using `e>0`
      apply -
      apply (rule path_component_trans, assumption)
      apply (rule path_component_of_subset[OF e(2)])
      apply (rule convex_imp_path_connected[OF convex_ball, unfolded path_connected_component, rule_format])
      apply auto
      done
    thus False using as by auto
  qed (insert e(2), auto)
qed

lemma connected_open_path_connected:
  fixes s :: "'a::real_normed_vector set" (*TODO: generalize to metric_space*)
  assumes "open s" "connected s"
  shows "path_connected s"
  unfolding path_connected_component_set
proof (rule, rule, rule path_component_subset, rule)
  fix x y
  assume "x \<in> s" "y \<in> s"
  show "y \<in> {y. path_component s x y}"
  proof (rule ccontr)
    assume "y \<notin> {y. path_component s x y}"
    moreover
    have "{y. path_component s x y} \<inter> s \<noteq> {}"
      using `x\<in>s` path_component_eq_empty path_component_subset[of s x] by auto
    ultimately
    show False
      using `y\<in>s` open_non_path_component[OF assms(1)] open_path_component[OF assms(1)]
      using assms(2)[unfolded connected_def not_ex, rule_format, of"{y. path_component s x y}" "s - {y. path_component s x y}"]
      by auto
  qed
qed

lemma path_connected_continuous_image:
  assumes "continuous_on s f" "path_connected s"
  shows "path_connected (f ` s)"
  unfolding path_connected_def
proof (rule, rule)
  fix x' y'
  assume "x' \<in> f ` s" "y' \<in> f ` s"
  then obtain x y where xy: "x\<in>s" "y\<in>s" "x' = f x" "y' = f y" by auto
  guess g using assms(2)[unfolded path_connected_def, rule_format, OF xy(1,2)] ..
  thus "\<exists>g. path g \<and> path_image g \<subseteq> f ` s \<and> pathstart g = x' \<and> pathfinish g = y'"
    unfolding xy
    apply (rule_tac x="f \<circ> g" in exI)
    unfolding path_defs
    using assms(1)
    apply (auto intro!: continuous_on_compose continuous_on_subset[of _ _ "g ` {0..1}"])
    done
qed

lemma homeomorphic_path_connectedness:
  "s homeomorphic t \<Longrightarrow> (path_connected s \<longleftrightarrow> path_connected t)"
  unfolding homeomorphic_def homeomorphism_def
  apply (erule exE|erule conjE)+  
  apply rule
  apply (drule_tac f=f in path_connected_continuous_image) prefer 3
  apply (drule_tac f=g in path_connected_continuous_image)
  apply auto
  done

lemma path_connected_empty: "path_connected {}"
  unfolding path_connected_def by auto

lemma path_connected_singleton: "path_connected {a}"
  unfolding path_connected_def pathstart_def pathfinish_def path_image_def
  apply (clarify, rule_tac x="\<lambda>x. a" in exI, simp add: image_constant_conv)
  apply (simp add: path_def continuous_on_const)
  done

lemma path_connected_Un:
  assumes "path_connected s" "path_connected t" "s \<inter> t \<noteq> {}"
  shows "path_connected (s \<union> t)"
  unfolding path_connected_component
proof (rule, rule)
  fix x y
  assume as: "x \<in> s \<union> t" "y \<in> s \<union> t"
  from assms(3) obtain z where "z \<in> s \<inter> t" by auto
  thus "path_component (s \<union> t) x y"
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
  hence "path_component (S i) x z" and "path_component (S j) z y"
    using assms by (simp_all add: path_connected_component)
  hence "path_component (\<Union>i\<in>A. S i) x z" and "path_component (\<Union>i\<in>A. S i) z y"
    using *(1,3) by (auto elim!: path_component_of_subset [rotated])
  thus "path_component (\<Union>i\<in>A. S i) x y"
    by (rule path_component_trans)
qed


subsection {* sphere is path-connected. *}

lemma path_connected_punctured_universe:
  assumes "2 \<le> DIM('a::euclidean_space)"
  shows "path_connected((UNIV::'a::euclidean_space set) - {a})"
proof -
  let ?A = "{x::'a. \<exists>i\<in>{..<DIM('a)}. x $$ i < a $$ i}"
  let ?B = "{x::'a. \<exists>i\<in>{..<DIM('a)}. a $$ i < x $$ i}"

  have A: "path_connected ?A"
    unfolding Collect_bex_eq
  proof (rule path_connected_UNION)
    fix i
    assume "i \<in> {..<DIM('a)}"
    thus "(\<chi>\<chi> i. a $$ i - 1) \<in> {x::'a. x $$ i < a $$ i}" by simp
    show "path_connected {x. x $$ i < a $$ i}" unfolding euclidean_component_def
      by (rule convex_imp_path_connected [OF convex_halfspace_lt])
  qed
  have B: "path_connected ?B" unfolding Collect_bex_eq
  proof (rule path_connected_UNION)
    fix i
    assume "i \<in> {..<DIM('a)}"
    thus "(\<chi>\<chi> i. a $$ i + 1) \<in> {x::'a. a $$ i < x $$ i}" by simp
    show "path_connected {x. a $$ i < x $$ i}" unfolding euclidean_component_def
      by (rule convex_imp_path_connected [OF convex_halfspace_gt])
  qed
  from assms have "1 < DIM('a)" by auto
  hence "a + basis 0 - basis 1 \<in> ?A \<inter> ?B" by auto
  hence "?A \<inter> ?B \<noteq> {}" by fast
  with A B have "path_connected (?A \<union> ?B)"
    by (rule path_connected_Un)
  also have "?A \<union> ?B = {x. \<exists>i\<in>{..<DIM('a)}. x $$ i \<noteq> a $$ i}"
    unfolding neq_iff bex_disj_distrib Collect_disj_eq ..
  also have "\<dots> = {x. x \<noteq> a}"
    unfolding Bex_def euclidean_eq [where 'a='a] by simp
  also have "\<dots> = UNIV - {a}" by auto
  finally show ?thesis .
qed

lemma path_connected_sphere:
  assumes "2 \<le> DIM('a::euclidean_space)"
  shows "path_connected {x::'a::euclidean_space. norm(x - a) = r}"
proof (rule linorder_cases [of r 0])
  assume "r < 0"
  hence "{x::'a. norm(x - a) = r} = {}" by auto
  thus ?thesis using path_connected_empty by simp
next
  assume "r = 0"
  thus ?thesis using path_connected_singleton by simp
next
  assume r: "0 < r"
  hence *: "{x::'a. norm(x - a) = r} = (\<lambda>x. a + r *\<^sub>R x) ` {x. norm x = 1}"
    apply -
    apply (rule set_eqI, rule)
    unfolding image_iff
    apply (rule_tac x="(1/r) *\<^sub>R (x - a)" in bexI)
    unfolding mem_Collect_eq norm_scaleR
    apply (auto simp add: scaleR_right_diff_distrib)
    done
  have **: "{x::'a. norm x = 1} = (\<lambda>x. (1/norm x) *\<^sub>R x) ` (UNIV - {0})"
    apply (rule set_eqI,rule)
    unfolding image_iff
    apply (rule_tac x=x in bexI)
    unfolding mem_Collect_eq
    apply (auto split:split_if_asm)
    done
  have "continuous_on (UNIV - {0}) (\<lambda>x::'a. 1 / norm x)"
    unfolding field_divide_inverse by (simp add: continuous_on_intros)
  thus ?thesis unfolding * ** using path_connected_punctured_universe[OF assms]
    by (auto intro!: path_connected_continuous_image continuous_on_intros)
qed

lemma connected_sphere: "2 \<le> DIM('a::euclidean_space) \<Longrightarrow> connected {x::'a. norm(x - a) = r}"
  using path_connected_sphere path_connected_imp_connected by auto

end
