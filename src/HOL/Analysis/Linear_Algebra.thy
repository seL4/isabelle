(*  Title:      HOL/Analysis/Linear_Algebra.thy
    Author:     Amine Chaieb, University of Cambridge
*)

section \<open>Elementary linear algebra on Euclidean spaces\<close>

theory Linear_Algebra
imports
  Euclidean_Space
  "~~/src/HOL/Library/Infinite_Set"
begin

lemma linear_simps:
  assumes "bounded_linear f"
  shows
    "f (a + b) = f a + f b"
    "f (a - b) = f a - f b"
    "f 0 = 0"
    "f (- a) = - f a"
    "f (s *\<^sub>R v) = s *\<^sub>R (f v)"
proof -
  interpret f: bounded_linear f by fact
  show "f (a + b) = f a + f b" by (rule f.add)
  show "f (a - b) = f a - f b" by (rule f.diff)
  show "f 0 = 0" by (rule f.zero)
  show "f (- a) = - f a" by (rule f.minus)
  show "f (s *\<^sub>R v) = s *\<^sub>R (f v)" by (rule f.scaleR)
qed

lemma bounded_linearI:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (r *\<^sub>R x) = r *\<^sub>R f x"
    and "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_linear f"
  using assms by (rule bounded_linear_intro) (* FIXME: duplicate *)

subsection \<open>A generic notion of "hull" (convex, affine, conic hull and closure).\<close>

definition hull :: "('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set"  (infixl "hull" 75)
  where "S hull s = \<Inter>{t. S t \<and> s \<subseteq> t}"

lemma hull_same: "S s \<Longrightarrow> S hull s = s"
  unfolding hull_def by auto

lemma hull_in: "(\<And>T. Ball T S \<Longrightarrow> S (\<Inter>T)) \<Longrightarrow> S (S hull s)"
  unfolding hull_def Ball_def by auto

lemma hull_eq: "(\<And>T. Ball T S \<Longrightarrow> S (\<Inter>T)) \<Longrightarrow> (S hull s) = s \<longleftrightarrow> S s"
  using hull_same[of S s] hull_in[of S s] by metis

lemma hull_hull [simp]: "S hull (S hull s) = S hull s"
  unfolding hull_def by blast

lemma hull_subset[intro]: "s \<subseteq> (S hull s)"
  unfolding hull_def by blast

lemma hull_mono: "s \<subseteq> t \<Longrightarrow> (S hull s) \<subseteq> (S hull t)"
  unfolding hull_def by blast

lemma hull_antimono: "\<forall>x. S x \<longrightarrow> T x \<Longrightarrow> (T hull s) \<subseteq> (S hull s)"
  unfolding hull_def by blast

lemma hull_minimal: "s \<subseteq> t \<Longrightarrow> S t \<Longrightarrow> (S hull s) \<subseteq> t"
  unfolding hull_def by blast

lemma subset_hull: "S t \<Longrightarrow> S hull s \<subseteq> t \<longleftrightarrow> s \<subseteq> t"
  unfolding hull_def by blast

lemma hull_UNIV [simp]: "S hull UNIV = UNIV"
  unfolding hull_def by auto

lemma hull_unique: "s \<subseteq> t \<Longrightarrow> S t \<Longrightarrow> (\<And>t'. s \<subseteq> t' \<Longrightarrow> S t' \<Longrightarrow> t \<subseteq> t') \<Longrightarrow> (S hull s = t)"
  unfolding hull_def by auto

lemma hull_induct: "(\<And>x. x\<in> S \<Longrightarrow> P x) \<Longrightarrow> Q {x. P x} \<Longrightarrow> \<forall>x\<in> Q hull S. P x"
  using hull_minimal[of S "{x. P x}" Q]
  by (auto simp add: subset_eq)

lemma hull_inc: "x \<in> S \<Longrightarrow> x \<in> P hull S"
  by (metis hull_subset subset_eq)

lemma hull_union_subset: "(S hull s) \<union> (S hull t) \<subseteq> (S hull (s \<union> t))"
  unfolding Un_subset_iff by (metis hull_mono Un_upper1 Un_upper2)

lemma hull_union:
  assumes T: "\<And>T. Ball T S \<Longrightarrow> S (\<Inter>T)"
  shows "S hull (s \<union> t) = S hull (S hull s \<union> S hull t)"
  apply rule
  apply (rule hull_mono)
  unfolding Un_subset_iff
  apply (metis hull_subset Un_upper1 Un_upper2 subset_trans)
  apply (rule hull_minimal)
  apply (metis hull_union_subset)
  apply (metis hull_in T)
  done

lemma hull_redundant_eq: "a \<in> (S hull s) \<longleftrightarrow> S hull (insert a s) = S hull s"
  unfolding hull_def by blast

lemma hull_redundant: "a \<in> (S hull s) \<Longrightarrow> S hull (insert a s) = S hull s"
  by (metis hull_redundant_eq)

subsection \<open>Linear functions.\<close>

lemma linear_iff:
  "linear f \<longleftrightarrow> (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (c *\<^sub>R x) = c *\<^sub>R f x)"
  (is "linear f \<longleftrightarrow> ?rhs")
proof
  assume "linear f"
  then interpret f: linear f .
  show "?rhs" by (simp add: f.add f.scaleR)
next
  assume "?rhs"
  then show "linear f" by unfold_locales simp_all
qed

lemma linear_compose_cmul: "linear f \<Longrightarrow> linear (\<lambda>x. c *\<^sub>R f x)"
  by (simp add: linear_iff algebra_simps)

lemma linear_compose_scaleR: "linear f \<Longrightarrow> linear (\<lambda>x. f x *\<^sub>R c)"
  by (simp add: linear_iff scaleR_add_left)

lemma linear_compose_neg: "linear f \<Longrightarrow> linear (\<lambda>x. - f x)"
  by (simp add: linear_iff)

lemma linear_compose_add: "linear f \<Longrightarrow> linear g \<Longrightarrow> linear (\<lambda>x. f x + g x)"
  by (simp add: linear_iff algebra_simps)

lemma linear_compose_sub: "linear f \<Longrightarrow> linear g \<Longrightarrow> linear (\<lambda>x. f x - g x)"
  by (simp add: linear_iff algebra_simps)

lemma linear_compose: "linear f \<Longrightarrow> linear g \<Longrightarrow> linear (g \<circ> f)"
  by (simp add: linear_iff)

lemma linear_id: "linear id"
  by (simp add: linear_iff id_def)

lemma linear_zero: "linear (\<lambda>x. 0)"
  by (simp add: linear_iff)

lemma linear_uminus: "linear uminus"
by (simp add: linear_iff)

lemma linear_compose_sum:
  assumes lS: "\<forall>a \<in> S. linear (f a)"
  shows "linear (\<lambda>x. sum (\<lambda>a. f a x) S)"
proof (cases "finite S")
  case True
  then show ?thesis
    using lS by induct (simp_all add: linear_zero linear_compose_add)
next
  case False
  then show ?thesis
    by (simp add: linear_zero)
qed

lemma linear_0: "linear f \<Longrightarrow> f 0 = 0"
  unfolding linear_iff
  apply clarsimp
  apply (erule allE[where x="0::'a"])
  apply simp
  done

lemma linear_cmul: "linear f \<Longrightarrow> f (c *\<^sub>R x) = c *\<^sub>R f x"
  by (rule linear.scaleR)

lemma linear_neg: "linear f \<Longrightarrow> f (- x) = - f x"
  using linear_cmul [where c="-1"] by simp

lemma linear_add: "linear f \<Longrightarrow> f (x + y) = f x + f y"
  by (metis linear_iff)

lemma linear_diff: "linear f \<Longrightarrow> f (x - y) = f x - f y"
  using linear_add [of f x "- y"] by (simp add: linear_neg)

lemma linear_sum:
  assumes f: "linear f"
  shows "f (sum g S) = sum (f \<circ> g) S"
proof (cases "finite S")
  case True
  then show ?thesis
    by induct (simp_all add: linear_0 [OF f] linear_add [OF f])
next
  case False
  then show ?thesis
    by (simp add: linear_0 [OF f])
qed

lemma linear_sum_mul:
  assumes lin: "linear f"
  shows "f (sum (\<lambda>i. c i *\<^sub>R v i) S) = sum (\<lambda>i. c i *\<^sub>R f (v i)) S"
  using linear_sum[OF lin, of "\<lambda>i. c i *\<^sub>R v i" , unfolded o_def] linear_cmul[OF lin]
  by simp

lemma linear_injective_0:
  assumes lin: "linear f"
  shows "inj f \<longleftrightarrow> (\<forall>x. f x = 0 \<longrightarrow> x = 0)"
proof -
  have "inj f \<longleftrightarrow> (\<forall> x y. f x = f y \<longrightarrow> x = y)"
    by (simp add: inj_on_def)
  also have "\<dots> \<longleftrightarrow> (\<forall> x y. f x - f y = 0 \<longrightarrow> x - y = 0)"
    by simp
  also have "\<dots> \<longleftrightarrow> (\<forall> x y. f (x - y) = 0 \<longrightarrow> x - y = 0)"
    by (simp add: linear_diff[OF lin])
  also have "\<dots> \<longleftrightarrow> (\<forall> x. f x = 0 \<longrightarrow> x = 0)"
    by auto
  finally show ?thesis .
qed

lemma linear_scaleR  [simp]: "linear (\<lambda>x. scaleR c x)"
  by (simp add: linear_iff scaleR_add_right)

lemma linear_scaleR_left [simp]: "linear (\<lambda>r. scaleR r x)"
  by (simp add: linear_iff scaleR_add_left)

lemma injective_scaleR: "c \<noteq> 0 \<Longrightarrow> inj (\<lambda>x::'a::real_vector. scaleR c x)"
  by (simp add: inj_on_def)

lemma linear_add_cmul:
  assumes "linear f"
  shows "f (a *\<^sub>R x + b *\<^sub>R y) = a *\<^sub>R f x +  b *\<^sub>R f y"
  using linear_add[of f] linear_cmul[of f] assms by simp

subsection \<open>Subspaces of vector spaces\<close>

definition (in real_vector) subspace :: "'a set \<Rightarrow> bool"
  where "subspace S \<longleftrightarrow> 0 \<in> S \<and> (\<forall>x \<in> S. \<forall>y \<in> S. x + y \<in> S) \<and> (\<forall>c. \<forall>x \<in> S. c *\<^sub>R x \<in> S)"

definition (in real_vector) "span S = (subspace hull S)"
definition (in real_vector) "dependent S \<longleftrightarrow> (\<exists>a \<in> S. a \<in> span (S - {a}))"
abbreviation (in real_vector) "independent s \<equiv> \<not> dependent s"

text \<open>Closure properties of subspaces.\<close>

lemma subspace_UNIV[simp]: "subspace UNIV"
  by (simp add: subspace_def)

lemma (in real_vector) subspace_0: "subspace S \<Longrightarrow> 0 \<in> S"
  by (metis subspace_def)

lemma (in real_vector) subspace_add: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x + y \<in> S"
  by (metis subspace_def)

lemma (in real_vector) subspace_mul: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> c *\<^sub>R x \<in> S"
  by (metis subspace_def)

lemma subspace_neg: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> - x \<in> S"
  by (metis scaleR_minus1_left subspace_mul)

lemma subspace_diff: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x - y \<in> S"
  using subspace_add [of S x "- y"] by (simp add: subspace_neg)

lemma (in real_vector) subspace_sum:
  assumes sA: "subspace A"
    and f: "\<And>x. x \<in> B \<Longrightarrow> f x \<in> A"
  shows "sum f B \<in> A"
proof (cases "finite B")
  case True
  then show ?thesis
    using f by induct (simp_all add: subspace_0 [OF sA] subspace_add [OF sA])
qed (simp add: subspace_0 [OF sA])

lemma subspace_trivial [iff]: "subspace {0}"
  by (simp add: subspace_def)

lemma (in real_vector) subspace_inter: "subspace A \<Longrightarrow> subspace B \<Longrightarrow> subspace (A \<inter> B)"
  by (simp add: subspace_def)

lemma subspace_Times: "subspace A \<Longrightarrow> subspace B \<Longrightarrow> subspace (A \<times> B)"
  unfolding subspace_def zero_prod_def by simp

lemma subspace_sums: "\<lbrakk>subspace S; subspace T\<rbrakk> \<Longrightarrow> subspace {x + y|x y. x \<in> S \<and> y \<in> T}"
apply (simp add: subspace_def)
apply (intro conjI impI allI)
  using add.right_neutral apply blast
 apply clarify
 apply (metis add.assoc add.left_commute)
using scaleR_add_right by blast

subsection \<open>Properties of span\<close>

lemma (in real_vector) span_mono: "A \<subseteq> B \<Longrightarrow> span A \<subseteq> span B"
  by (metis span_def hull_mono)

lemma (in real_vector) subspace_span [iff]: "subspace (span S)"
  unfolding span_def
  apply (rule hull_in)
  apply (simp only: subspace_def Inter_iff Int_iff subset_eq)
  apply auto
  done

lemma (in real_vector) span_clauses:
  "a \<in> S \<Longrightarrow> a \<in> span S"
  "0 \<in> span S"
  "x\<in> span S \<Longrightarrow> y \<in> span S \<Longrightarrow> x + y \<in> span S"
  "x \<in> span S \<Longrightarrow> c *\<^sub>R x \<in> span S"
  by (metis span_def hull_subset subset_eq) (metis subspace_span subspace_def)+

lemma span_unique:
  "S \<subseteq> T \<Longrightarrow> subspace T \<Longrightarrow> (\<And>T'. S \<subseteq> T' \<Longrightarrow> subspace T' \<Longrightarrow> T \<subseteq> T') \<Longrightarrow> span S = T"
  unfolding span_def by (rule hull_unique)

lemma span_minimal: "S \<subseteq> T \<Longrightarrow> subspace T \<Longrightarrow> span S \<subseteq> T"
  unfolding span_def by (rule hull_minimal)

lemma span_UNIV: "span UNIV = UNIV"
  by (intro span_unique) auto

lemma (in real_vector) span_induct:
  assumes x: "x \<in> span S"
    and P: "subspace (Collect P)"
    and SP: "\<And>x. x \<in> S \<Longrightarrow> P x"
  shows "P x"
proof -
  from SP have SP': "S \<subseteq> Collect P"
    by (simp add: subset_eq)
  from x hull_minimal[where S=subspace, OF SP' P, unfolded span_def[symmetric]]
  show ?thesis
    using subset_eq by force
qed

lemma span_empty[simp]: "span {} = {0}"
  apply (simp add: span_def)
  apply (rule hull_unique)
  apply (auto simp add: subspace_def)
  done

lemma (in real_vector) independent_empty [iff]: "independent {}"
  by (simp add: dependent_def)

lemma dependent_single[simp]: "dependent {x} \<longleftrightarrow> x = 0"
  unfolding dependent_def by auto

lemma (in real_vector) independent_mono: "independent A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> independent B"
  apply (clarsimp simp add: dependent_def span_mono)
  apply (subgoal_tac "span (B - {a}) \<le> span (A - {a})")
  apply force
  apply (rule span_mono)
  apply auto
  done

lemma (in real_vector) span_subspace: "A \<subseteq> B \<Longrightarrow> B \<le> span A \<Longrightarrow>  subspace B \<Longrightarrow> span A = B"
  by (metis order_antisym span_def hull_minimal)

lemma (in real_vector) span_induct':
  "\<forall>x \<in> S. P x \<Longrightarrow> subspace {x. P x} \<Longrightarrow> \<forall>x \<in> span S. P x"
  unfolding span_def by (rule hull_induct) auto

inductive_set (in real_vector) span_induct_alt_help for S :: "'a set"
where
  span_induct_alt_help_0: "0 \<in> span_induct_alt_help S"
| span_induct_alt_help_S:
    "x \<in> S \<Longrightarrow> z \<in> span_induct_alt_help S \<Longrightarrow>
      (c *\<^sub>R x + z) \<in> span_induct_alt_help S"

lemma span_induct_alt':
  assumes h0: "h 0"
    and hS: "\<And>c x y. x \<in> S \<Longrightarrow> h y \<Longrightarrow> h (c *\<^sub>R x + y)"
  shows "\<forall>x \<in> span S. h x"
proof -
  {
    fix x :: 'a
    assume x: "x \<in> span_induct_alt_help S"
    have "h x"
      apply (rule span_induct_alt_help.induct[OF x])
      apply (rule h0)
      apply (rule hS)
      apply assumption
      apply assumption
      done
  }
  note th0 = this
  {
    fix x
    assume x: "x \<in> span S"
    have "x \<in> span_induct_alt_help S"
    proof (rule span_induct[where x=x and S=S])
      show "x \<in> span S" by (rule x)
    next
      fix x
      assume xS: "x \<in> S"
      from span_induct_alt_help_S[OF xS span_induct_alt_help_0, of 1]
      show "x \<in> span_induct_alt_help S"
        by simp
    next
      have "0 \<in> span_induct_alt_help S" by (rule span_induct_alt_help_0)
      moreover
      {
        fix x y
        assume h: "x \<in> span_induct_alt_help S" "y \<in> span_induct_alt_help S"
        from h have "(x + y) \<in> span_induct_alt_help S"
          apply (induct rule: span_induct_alt_help.induct)
          apply simp
          unfolding add.assoc
          apply (rule span_induct_alt_help_S)
          apply assumption
          apply simp
          done
      }
      moreover
      {
        fix c x
        assume xt: "x \<in> span_induct_alt_help S"
        then have "(c *\<^sub>R x) \<in> span_induct_alt_help S"
          apply (induct rule: span_induct_alt_help.induct)
          apply (simp add: span_induct_alt_help_0)
          apply (simp add: scaleR_right_distrib)
          apply (rule span_induct_alt_help_S)
          apply assumption
          apply simp
          done }
      ultimately show "subspace {a. a \<in> span_induct_alt_help S}"
        unfolding subspace_def Ball_def by blast
    qed
  }
  with th0 show ?thesis by blast
qed

lemma span_induct_alt:
  assumes h0: "h 0"
    and hS: "\<And>c x y. x \<in> S \<Longrightarrow> h y \<Longrightarrow> h (c *\<^sub>R x + y)"
    and x: "x \<in> span S"
  shows "h x"
  using span_induct_alt'[of h S] h0 hS x by blast

text \<open>Individual closure properties.\<close>

lemma span_span: "span (span A) = span A"
  unfolding span_def hull_hull ..

lemma (in real_vector) span_superset: "x \<in> S \<Longrightarrow> x \<in> span S"
  by (metis span_clauses(1))

lemma (in real_vector) span_0 [simp]: "0 \<in> span S"
  by (metis subspace_span subspace_0)

lemma span_inc: "S \<subseteq> span S"
  by (metis subset_eq span_superset)

lemma span_eq: "span S = span T \<longleftrightarrow> S \<subseteq> span T \<and> T \<subseteq> span S"
  using span_inc[unfolded subset_eq] using span_mono[of T "span S"] span_mono[of S "span T"]
  by (auto simp add: span_span)

lemma (in real_vector) dependent_0:
  assumes "0 \<in> A"
  shows "dependent A"
  unfolding dependent_def
  using assms span_0
  by blast

lemma (in real_vector) span_add: "x \<in> span S \<Longrightarrow> y \<in> span S \<Longrightarrow> x + y \<in> span S"
  by (metis subspace_add subspace_span)

lemma (in real_vector) span_mul: "x \<in> span S \<Longrightarrow> c *\<^sub>R x \<in> span S"
  by (metis subspace_span subspace_mul)

lemma span_neg: "x \<in> span S \<Longrightarrow> - x \<in> span S"
  by (metis subspace_neg subspace_span)

lemma span_diff: "x \<in> span S \<Longrightarrow> y \<in> span S \<Longrightarrow> x - y \<in> span S"
  by (metis subspace_span subspace_diff)

lemma (in real_vector) span_sum: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> span S) \<Longrightarrow> sum f A \<in> span S"
  by (rule subspace_sum [OF subspace_span])

lemma span_add_eq: "x \<in> span S \<Longrightarrow> x + y \<in> span S \<longleftrightarrow> y \<in> span S"
  by (metis add_minus_cancel scaleR_minus1_left subspace_def subspace_span)

text \<open>The key breakdown property.\<close>

lemma span_singleton: "span {x} = range (\<lambda>k. k *\<^sub>R x)"
proof (rule span_unique)
  show "{x} \<subseteq> range (\<lambda>k. k *\<^sub>R x)"
    by (fast intro: scaleR_one [symmetric])
  show "subspace (range (\<lambda>k. k *\<^sub>R x))"
    unfolding subspace_def
    by (auto intro: scaleR_add_left [symmetric])
next
  fix T
  assume "{x} \<subseteq> T" and "subspace T"
  then show "range (\<lambda>k. k *\<^sub>R x) \<subseteq> T"
    unfolding subspace_def by auto
qed

text \<open>Mapping under linear image.\<close>

lemma subspace_linear_image:
  assumes lf: "linear f"
    and sS: "subspace S"
  shows "subspace (f ` S)"
  using lf sS linear_0[OF lf]
  unfolding linear_iff subspace_def
  apply (auto simp add: image_iff)
  apply (rule_tac x="x + y" in bexI)
  apply auto
  apply (rule_tac x="c *\<^sub>R x" in bexI)
  apply auto
  done

lemma subspace_linear_vimage: "linear f \<Longrightarrow> subspace S \<Longrightarrow> subspace (f -` S)"
  by (auto simp add: subspace_def linear_iff linear_0[of f])

lemma subspace_linear_preimage: "linear f \<Longrightarrow> subspace S \<Longrightarrow> subspace {x. f x \<in> S}"
  by (auto simp add: subspace_def linear_iff linear_0[of f])

lemma span_linear_image:
  assumes lf: "linear f"
  shows "span (f ` S) = f ` span S"
proof (rule span_unique)
  show "f ` S \<subseteq> f ` span S"
    by (intro image_mono span_inc)
  show "subspace (f ` span S)"
    using lf subspace_span by (rule subspace_linear_image)
next
  fix T
  assume "f ` S \<subseteq> T" and "subspace T"
  then show "f ` span S \<subseteq> T"
    unfolding image_subset_iff_subset_vimage
    by (intro span_minimal subspace_linear_vimage lf)
qed

lemma spans_image:
  assumes lf: "linear f"
    and VB: "V \<subseteq> span B"
  shows "f ` V \<subseteq> span (f ` B)"
  unfolding span_linear_image[OF lf] by (metis VB image_mono)

lemma span_Un: "span (A \<union> B) = (\<lambda>(a, b). a + b) ` (span A \<times> span B)"
proof (rule span_unique)
  show "A \<union> B \<subseteq> (\<lambda>(a, b). a + b) ` (span A \<times> span B)"
    by safe (force intro: span_clauses)+
next
  have "linear (\<lambda>(a, b). a + b)"
    by (simp add: linear_iff scaleR_add_right)
  moreover have "subspace (span A \<times> span B)"
    by (intro subspace_Times subspace_span)
  ultimately show "subspace ((\<lambda>(a, b). a + b) ` (span A \<times> span B))"
    by (rule subspace_linear_image)
next
  fix T
  assume "A \<union> B \<subseteq> T" and "subspace T"
  then show "(\<lambda>(a, b). a + b) ` (span A \<times> span B) \<subseteq> T"
    by (auto intro!: subspace_add elim: span_induct)
qed

lemma span_insert: "span (insert a S) = {x. \<exists>k. (x - k *\<^sub>R a) \<in> span S}"
proof -
  have "span ({a} \<union> S) = {x. \<exists>k. (x - k *\<^sub>R a) \<in> span S}"
    unfolding span_Un span_singleton
    apply safe
    apply (rule_tac x=k in exI, simp)
    apply (erule rev_image_eqI [OF SigmaI [OF rangeI]])
    apply auto
    done
  then show ?thesis by simp
qed

lemma span_breakdown:
  assumes bS: "b \<in> S"
    and aS: "a \<in> span S"
  shows "\<exists>k. a - k *\<^sub>R b \<in> span (S - {b})"
  using assms span_insert [of b "S - {b}"]
  by (simp add: insert_absorb)

lemma span_breakdown_eq: "x \<in> span (insert a S) \<longleftrightarrow> (\<exists>k. x - k *\<^sub>R a \<in> span S)"
  by (simp add: span_insert)

text \<open>Hence some "reversal" results.\<close>

lemma in_span_insert:
  assumes a: "a \<in> span (insert b S)"
    and na: "a \<notin> span S"
  shows "b \<in> span (insert a S)"
proof -
  from a obtain k where k: "a - k *\<^sub>R b \<in> span S"
    unfolding span_insert by fast
  show ?thesis
  proof (cases "k = 0")
    case True
    with k have "a \<in> span S" by simp
    with na show ?thesis by simp
  next
    case False
    from k have "(- inverse k) *\<^sub>R (a - k *\<^sub>R b) \<in> span S"
      by (rule span_mul)
    then have "b - inverse k *\<^sub>R a \<in> span S"
      using \<open>k \<noteq> 0\<close> by (simp add: scaleR_diff_right)
    then show ?thesis
      unfolding span_insert by fast
  qed
qed

lemma in_span_delete:
  assumes a: "a \<in> span S"
    and na: "a \<notin> span (S - {b})"
  shows "b \<in> span (insert a (S - {b}))"
  apply (rule in_span_insert)
  apply (rule set_rev_mp)
  apply (rule a)
  apply (rule span_mono)
  apply blast
  apply (rule na)
  done

text \<open>Transitivity property.\<close>

lemma span_redundant: "x \<in> span S \<Longrightarrow> span (insert x S) = span S"
  unfolding span_def by (rule hull_redundant)

lemma span_trans:
  assumes x: "x \<in> span S"
    and y: "y \<in> span (insert x S)"
  shows "y \<in> span S"
  using assms by (simp only: span_redundant)

lemma span_insert_0[simp]: "span (insert 0 S) = span S"
  by (simp only: span_redundant span_0)

text \<open>An explicit expansion is sometimes needed.\<close>

lemma span_explicit:
  "span P = {y. \<exists>S u. finite S \<and> S \<subseteq> P \<and> sum (\<lambda>v. u v *\<^sub>R v) S = y}"
  (is "_ = ?E" is "_ = {y. ?h y}" is "_ = {y. \<exists>S u. ?Q S u y}")
proof -
  {
    fix x
    assume "?h x"
    then obtain S u where "finite S" and "S \<subseteq> P" and "sum (\<lambda>v. u v *\<^sub>R v) S = x"
      by blast
    then have "x \<in> span P"
      by (auto intro: span_sum span_mul span_superset)
  }
  moreover
  have "\<forall>x \<in> span P. ?h x"
  proof (rule span_induct_alt')
    show "?h 0"
      by (rule exI[where x="{}"], simp)
  next
    fix c x y
    assume x: "x \<in> P"
    assume hy: "?h y"
    from hy obtain S u where fS: "finite S" and SP: "S\<subseteq>P"
      and u: "sum (\<lambda>v. u v *\<^sub>R v) S = y" by blast
    let ?S = "insert x S"
    let ?u = "\<lambda>y. if y = x then (if x \<in> S then u y + c else c) else u y"
    from fS SP x have th0: "finite (insert x S)" "insert x S \<subseteq> P"
      by blast+
    have "?Q ?S ?u (c*\<^sub>R x + y)"
    proof cases
      assume xS: "x \<in> S"
      have "sum (\<lambda>v. ?u v *\<^sub>R v) ?S = (\<Sum>v\<in>S - {x}. u v *\<^sub>R v) + (u x + c) *\<^sub>R x"
        using xS by (simp add: sum.remove [OF fS xS] insert_absorb)
      also have "\<dots> = (\<Sum>v\<in>S. u v *\<^sub>R v) + c *\<^sub>R x"
        by (simp add: sum.remove [OF fS xS] algebra_simps)
      also have "\<dots> = c*\<^sub>R x + y"
        by (simp add: add.commute u)
      finally have "sum (\<lambda>v. ?u v *\<^sub>R v) ?S = c*\<^sub>R x + y" .
      then show ?thesis using th0 by blast
    next
      assume xS: "x \<notin> S"
      have th00: "(\<Sum>v\<in>S. (if v = x then c else u v) *\<^sub>R v) = y"
        unfolding u[symmetric]
        apply (rule sum.cong)
        using xS
        apply auto
        done
      show ?thesis using fS xS th0
        by (simp add: th00 add.commute cong del: if_weak_cong)
    qed
    then show "?h (c*\<^sub>R x + y)"
      by fast
  qed
  ultimately show ?thesis by blast
qed

lemma dependent_explicit:
  "dependent P \<longleftrightarrow> (\<exists>S u. finite S \<and> S \<subseteq> P \<and> (\<exists>v\<in>S. u v \<noteq> 0 \<and> sum (\<lambda>v. u v *\<^sub>R v) S = 0))"
  (is "?lhs = ?rhs")
proof -
  {
    assume dP: "dependent P"
    then obtain a S u where aP: "a \<in> P" and fS: "finite S"
      and SP: "S \<subseteq> P - {a}" and ua: "sum (\<lambda>v. u v *\<^sub>R v) S = a"
      unfolding dependent_def span_explicit by blast
    let ?S = "insert a S"
    let ?u = "\<lambda>y. if y = a then - 1 else u y"
    let ?v = a
    from aP SP have aS: "a \<notin> S"
      by blast
    from fS SP aP have th0: "finite ?S" "?S \<subseteq> P" "?v \<in> ?S" "?u ?v \<noteq> 0"
      by auto
    have s0: "sum (\<lambda>v. ?u v *\<^sub>R v) ?S = 0"
      using fS aS
      apply simp
      apply (subst (2) ua[symmetric])
      apply (rule sum.cong)
      apply auto
      done
    with th0 have ?rhs by fast
  }
  moreover
  {
    fix S u v
    assume fS: "finite S"
      and SP: "S \<subseteq> P"
      and vS: "v \<in> S"
      and uv: "u v \<noteq> 0"
      and u: "sum (\<lambda>v. u v *\<^sub>R v) S = 0"
    let ?a = v
    let ?S = "S - {v}"
    let ?u = "\<lambda>i. (- u i) / u v"
    have th0: "?a \<in> P" "finite ?S" "?S \<subseteq> P"
      using fS SP vS by auto
    have "sum (\<lambda>v. ?u v *\<^sub>R v) ?S =
      sum (\<lambda>v. (- (inverse (u ?a))) *\<^sub>R (u v *\<^sub>R v)) S - ?u v *\<^sub>R v"
      using fS vS uv by (simp add: sum_diff1 field_simps)
    also have "\<dots> = ?a"
      unfolding scaleR_right.sum [symmetric] u using uv by simp
    finally have "sum (\<lambda>v. ?u v *\<^sub>R v) ?S = ?a" .
    with th0 have ?lhs
      unfolding dependent_def span_explicit
      apply -
      apply (rule bexI[where x= "?a"])
      apply (simp_all del: scaleR_minus_left)
      apply (rule exI[where x= "?S"])
      apply (auto simp del: scaleR_minus_left)
      done
  }
  ultimately show ?thesis by blast
qed

lemma dependent_finite:
  assumes "finite S"
    shows "dependent S \<longleftrightarrow> (\<exists>u. (\<exists>v \<in> S. u v \<noteq> 0) \<and> (\<Sum>v\<in>S. u v *\<^sub>R v) = 0)"
           (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain T u v
         where "finite T" "T \<subseteq> S" "v\<in>T" "u v \<noteq> 0" "(\<Sum>v\<in>T. u v *\<^sub>R v) = 0"
    by (force simp: dependent_explicit)
  with assms show ?rhs
    apply (rule_tac x="\<lambda>v. if v \<in> T then u v else 0" in exI)
    apply (auto simp: sum.mono_neutral_right)
    done
next
  assume ?rhs  with assms show ?lhs
    by (fastforce simp add: dependent_explicit)
qed

lemma span_alt:
  "span B = {(\<Sum>x | f x \<noteq> 0. f x *\<^sub>R x) | f. {x. f x \<noteq> 0} \<subseteq> B \<and> finite {x. f x \<noteq> 0}}"
  unfolding span_explicit
  apply safe
  subgoal for x S u
    by (intro exI[of _ "\<lambda>x. if x \<in> S then u x else 0"])
        (auto intro!: sum.mono_neutral_cong_right)
  apply auto
  done

lemma dependent_alt:
  "dependent B \<longleftrightarrow>
    (\<exists>X. finite {x. X x \<noteq> 0} \<and> {x. X x \<noteq> 0} \<subseteq> B \<and> (\<Sum>x|X x \<noteq> 0. X x *\<^sub>R x) = 0 \<and> (\<exists>x. X x \<noteq> 0))"
  unfolding dependent_explicit
  apply safe
  subgoal for S u v
    apply (intro exI[of _ "\<lambda>x. if x \<in> S then u x else 0"])
    apply (subst sum.mono_neutral_cong_left[where T=S])
    apply (auto intro!: sum.mono_neutral_cong_right cong: rev_conj_cong)
    done
  apply auto
  done

lemma independent_alt:
  "independent B \<longleftrightarrow>
    (\<forall>X. finite {x. X x \<noteq> 0} \<longrightarrow> {x. X x \<noteq> 0} \<subseteq> B \<longrightarrow> (\<Sum>x|X x \<noteq> 0. X x *\<^sub>R x) = 0 \<longrightarrow> (\<forall>x. X x = 0))"
  unfolding dependent_alt by auto

lemma independentD_alt:
  "independent B \<Longrightarrow> finite {x. X x \<noteq> 0} \<Longrightarrow> {x. X x \<noteq> 0} \<subseteq> B \<Longrightarrow> (\<Sum>x|X x \<noteq> 0. X x *\<^sub>R x) = 0 \<Longrightarrow> X x = 0"
  unfolding independent_alt by blast

lemma independentD_unique:
  assumes B: "independent B"
    and X: "finite {x. X x \<noteq> 0}" "{x. X x \<noteq> 0} \<subseteq> B"
    and Y: "finite {x. Y x \<noteq> 0}" "{x. Y x \<noteq> 0} \<subseteq> B"
    and "(\<Sum>x | X x \<noteq> 0. X x *\<^sub>R x) = (\<Sum>x| Y x \<noteq> 0. Y x *\<^sub>R x)"
  shows "X = Y"
proof -
  have "X x - Y x = 0" for x
    using B
  proof (rule independentD_alt)
    have "{x. X x - Y x \<noteq> 0} \<subseteq> {x. X x \<noteq> 0} \<union> {x. Y x \<noteq> 0}"
      by auto
    then show "finite {x. X x - Y x \<noteq> 0}" "{x. X x - Y x \<noteq> 0} \<subseteq> B"
      using X Y by (auto dest: finite_subset)
    then have "(\<Sum>x | X x - Y x \<noteq> 0. (X x - Y x) *\<^sub>R x) = (\<Sum>v\<in>{S. X S \<noteq> 0} \<union> {S. Y S \<noteq> 0}. (X v - Y v) *\<^sub>R v)"
      using X Y by (intro sum.mono_neutral_cong_left) auto
    also have "\<dots> = (\<Sum>v\<in>{S. X S \<noteq> 0} \<union> {S. Y S \<noteq> 0}. X v *\<^sub>R v) - (\<Sum>v\<in>{S. X S \<noteq> 0} \<union> {S. Y S \<noteq> 0}. Y v *\<^sub>R v)"
      by (simp add: scaleR_diff_left sum_subtractf assms)
    also have "(\<Sum>v\<in>{S. X S \<noteq> 0} \<union> {S. Y S \<noteq> 0}. X v *\<^sub>R v) = (\<Sum>v\<in>{S. X S \<noteq> 0}. X v *\<^sub>R v)"
      using X Y by (intro sum.mono_neutral_cong_right) auto
    also have "(\<Sum>v\<in>{S. X S \<noteq> 0} \<union> {S. Y S \<noteq> 0}. Y v *\<^sub>R v) = (\<Sum>v\<in>{S. Y S \<noteq> 0}. Y v *\<^sub>R v)"
      using X Y by (intro sum.mono_neutral_cong_right) auto
    finally show "(\<Sum>x | X x - Y x \<noteq> 0. (X x - Y x) *\<^sub>R x) = 0"
      using assms by simp
  qed
  then show ?thesis
    by auto
qed

text \<open>This is useful for building a basis step-by-step.\<close>

lemma independent_insert:
  "independent (insert a S) \<longleftrightarrow>
    (if a \<in> S then independent S else independent S \<and> a \<notin> span S)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "a \<in> S")
  case True
  then show ?thesis
    using insert_absorb[OF True] by simp
next
  case False
  show ?thesis
  proof
    assume i: ?lhs
    then show ?rhs
      using False
      apply simp
      apply (rule conjI)
      apply (rule independent_mono)
      apply assumption
      apply blast
      apply (simp add: dependent_def)
      done
  next
    assume i: ?rhs
    show ?lhs
      using i False
      apply (auto simp add: dependent_def)
      by (metis in_span_insert insert_Diff_if insert_Diff_single insert_absorb)
  qed
qed

lemma independent_Union_directed:
  assumes directed: "\<And>c d. c \<in> C \<Longrightarrow> d \<in> C \<Longrightarrow> c \<subseteq> d \<or> d \<subseteq> c"
  assumes indep: "\<And>c. c \<in> C \<Longrightarrow> independent c"
  shows "independent (\<Union>C)"
proof
  assume "dependent (\<Union>C)"
  then obtain u v S where S: "finite S" "S \<subseteq> \<Union>C" "v \<in> S" "u v \<noteq> 0" "(\<Sum>v\<in>S. u v *\<^sub>R v) = 0"
    by (auto simp: dependent_explicit)

  have "S \<noteq> {}"
    using \<open>v \<in> S\<close> by auto
  have "\<exists>c\<in>C. S \<subseteq> c"
    using \<open>finite S\<close> \<open>S \<noteq> {}\<close> \<open>S \<subseteq> \<Union>C\<close>
  proof (induction rule: finite_ne_induct)
    case (insert i I)
    then obtain c d where cd: "c \<in> C" "d \<in> C" and iI: "I \<subseteq> c" "i \<in> d"
      by blast
    from directed[OF cd] cd have "c \<union> d \<in> C"
      by (auto simp: sup.absorb1 sup.absorb2)
    with iI show ?case
      by (intro bexI[of _ "c \<union> d"]) auto
  qed auto
  then obtain c where "c \<in> C" "S \<subseteq> c"
    by auto
  have "dependent c"
    unfolding dependent_explicit
    by (intro exI[of _ S] exI[of _ u] bexI[of _ v] conjI) fact+
  with indep[OF \<open>c \<in> C\<close>] show False
    by auto
qed

text \<open>Hence we can create a maximal independent subset.\<close>

lemma maximal_independent_subset_extend:
  assumes "S \<subseteq> V" "independent S"
  shows "\<exists>B. S \<subseteq> B \<and> B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
proof -
  let ?C = "{B. S \<subseteq> B \<and> independent B \<and> B \<subseteq> V}"
  have "\<exists>M\<in>?C. \<forall>X\<in>?C. M \<subseteq> X \<longrightarrow> X = M"
  proof (rule subset_Zorn)
    fix C :: "'a set set" assume "subset.chain ?C C"
    then have C: "\<And>c. c \<in> C \<Longrightarrow> c \<subseteq> V" "\<And>c. c \<in> C \<Longrightarrow> S \<subseteq> c" "\<And>c. c \<in> C \<Longrightarrow> independent c"
      "\<And>c d. c \<in> C \<Longrightarrow> d \<in> C \<Longrightarrow> c \<subseteq> d \<or> d \<subseteq> c"
      unfolding subset.chain_def by blast+

    show "\<exists>U\<in>?C. \<forall>X\<in>C. X \<subseteq> U"
    proof cases
      assume "C = {}" with assms show ?thesis
        by (auto intro!: exI[of _ S])
    next
      assume "C \<noteq> {}"
      with C(2) have "S \<subseteq> \<Union>C"
        by auto
      moreover have "independent (\<Union>C)"
        by (intro independent_Union_directed C)
      moreover have "\<Union>C \<subseteq> V"
        using C by auto
      ultimately show ?thesis
        by auto
    qed
  qed
  then obtain B where B: "independent B" "B \<subseteq> V" "S \<subseteq> B"
    and max: "\<And>S. independent S \<Longrightarrow> S \<subseteq> V \<Longrightarrow> B \<subseteq> S \<Longrightarrow> S = B"
    by auto
  moreover
  { assume "\<not> V \<subseteq> span B"
    then obtain v where "v \<in> V" "v \<notin> span B"
      by auto
    with B have "independent (insert v B)"
      unfolding independent_insert by auto
    from max[OF this] \<open>v \<in> V\<close> \<open>B \<subseteq> V\<close>
    have "v \<in> B"
      by auto
    with \<open>v \<notin> span B\<close> have False
      by (auto intro: span_superset) }
  ultimately show ?thesis
    by (auto intro!: exI[of _ B])
qed


lemma maximal_independent_subset:
  "\<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  by (metis maximal_independent_subset_extend[of "{}"] empty_subsetI independent_empty)

lemma span_finite:
  assumes fS: "finite S"
  shows "span S = {y. \<exists>u. sum (\<lambda>v. u v *\<^sub>R v) S = y}"
  (is "_ = ?rhs")
proof -
  {
    fix y
    assume y: "y \<in> span S"
    from y obtain S' u where fS': "finite S'"
      and SS': "S' \<subseteq> S"
      and u: "sum (\<lambda>v. u v *\<^sub>R v) S' = y"
      unfolding span_explicit by blast
    let ?u = "\<lambda>x. if x \<in> S' then u x else 0"
    have "sum (\<lambda>v. ?u v *\<^sub>R v) S = sum (\<lambda>v. u v *\<^sub>R v) S'"
      using SS' fS by (auto intro!: sum.mono_neutral_cong_right)
    then have "sum (\<lambda>v. ?u v *\<^sub>R v) S = y" by (metis u)
    then have "y \<in> ?rhs" by auto
  }
  moreover
  {
    fix y u
    assume u: "sum (\<lambda>v. u v *\<^sub>R v) S = y"
    then have "y \<in> span S" using fS unfolding span_explicit by auto
  }
  ultimately show ?thesis by blast
qed

lemma linear_independent_extend_subspace:
  assumes "independent B"
  shows "\<exists>g. linear g \<and> (\<forall>x\<in>B. g x = f x) \<and> range g = span (f`B)"
proof -
  from maximal_independent_subset_extend[OF _ \<open>independent B\<close>, of UNIV]
  obtain B' where "B \<subseteq> B'" "independent B'" "span B' = UNIV"
    by (auto simp: top_unique)
  have "\<forall>y. \<exists>X. {x. X x \<noteq> 0} \<subseteq> B' \<and> finite {x. X x \<noteq> 0} \<and> y = (\<Sum>x|X x \<noteq> 0. X x *\<^sub>R x)"
    using \<open>span B' = UNIV\<close> unfolding span_alt by auto
  then obtain X where X: "\<And>y. {x. X y x \<noteq> 0} \<subseteq> B'" "\<And>y. finite {x. X y x \<noteq> 0}"
    "\<And>y. y = (\<Sum>x|X y x \<noteq> 0. X y x *\<^sub>R x)"
    unfolding choice_iff by auto

  have X_add: "X (x + y) = (\<lambda>z. X x z + X y z)" for x y
    using \<open>independent B'\<close>
  proof (rule independentD_unique)
    have "(\<Sum>z | X x z + X y z \<noteq> 0. (X x z + X y z) *\<^sub>R z)
      = (\<Sum>z\<in>{z. X x z \<noteq> 0} \<union> {z. X y z \<noteq> 0}. (X x z + X y z) *\<^sub>R z)"
      by (intro sum.mono_neutral_cong_left) (auto intro: X)
    also have "\<dots> = (\<Sum>z\<in>{z. X x z \<noteq> 0}. X x z *\<^sub>R z) + (\<Sum>z\<in>{z. X y z \<noteq> 0}. X y z *\<^sub>R z)"
      by (auto simp add: scaleR_add_left sum.distrib
               intro!: arg_cong2[where f="op +"]  sum.mono_neutral_cong_right X)
    also have "\<dots> = x + y"
      by (simp add: X(3)[symmetric])
    also have "\<dots> = (\<Sum>z | X (x + y) z \<noteq> 0. X (x + y) z *\<^sub>R z)"
      by (rule X(3))
    finally show "(\<Sum>z | X (x + y) z \<noteq> 0. X (x + y) z *\<^sub>R z) = (\<Sum>z | X x z + X y z \<noteq> 0. (X x z + X y z) *\<^sub>R z)"
      ..
    have "{z. X x z + X y z \<noteq> 0} \<subseteq> {z. X x z \<noteq> 0} \<union> {z. X y z \<noteq> 0}"
      by auto
    then show "finite {z. X x z + X y z \<noteq> 0}" "{xa. X x xa + X y xa \<noteq> 0} \<subseteq> B'"
        "finite {xa. X (x + y) xa \<noteq> 0}" "{xa. X (x + y) xa \<noteq> 0} \<subseteq> B'"
      using X(1) by (auto dest: finite_subset intro: X)
  qed

  have X_cmult: "X (c *\<^sub>R x) = (\<lambda>z. c * X x z)" for x c
    using \<open>independent B'\<close>
  proof (rule independentD_unique)
    show "finite {z. X (c *\<^sub>R x) z \<noteq> 0}" "{z. X (c *\<^sub>R x) z \<noteq> 0} \<subseteq> B'"
      "finite {z. c * X x z \<noteq> 0}" "{z. c * X x z \<noteq> 0} \<subseteq> B' "
      using X(1,2) by auto
    show "(\<Sum>z | X (c *\<^sub>R x) z \<noteq> 0. X (c *\<^sub>R x) z *\<^sub>R z) = (\<Sum>z | c * X x z \<noteq> 0. (c * X x z) *\<^sub>R z)"
      unfolding scaleR_scaleR[symmetric] scaleR_sum_right[symmetric]
      by (cases "c = 0") (auto simp: X(3)[symmetric])
  qed

  have X_B': "x \<in> B' \<Longrightarrow> X x = (\<lambda>z. if z = x then 1 else 0)" for x
    using \<open>independent B'\<close>
    by (rule independentD_unique[OF _ X(2) X(1)]) (auto intro: X simp: X(3)[symmetric])

  define f' where "f' y = (if y \<in> B then f y else 0)" for y
  define g where "g y = (\<Sum>x|X y x \<noteq> 0. X y x *\<^sub>R f' x)" for y

  have g_f': "x \<in> B' \<Longrightarrow> g x = f' x" for x
    by (auto simp: g_def X_B')

  have "linear g"
  proof
    fix x y
    have *: "(\<Sum>z | X x z + X y z \<noteq> 0. (X x z + X y z) *\<^sub>R f' z)
      = (\<Sum>z\<in>{z. X x z \<noteq> 0} \<union> {z. X y z \<noteq> 0}. (X x z + X y z) *\<^sub>R f' z)"
      by (intro sum.mono_neutral_cong_left) (auto intro: X)
    show "g (x + y) = g x + g y"
      unfolding g_def X_add *
      by (auto simp add: scaleR_add_left sum.distrib
               intro!: arg_cong2[where f="op +"]  sum.mono_neutral_cong_right X)
  next
    show "g (r *\<^sub>R x) = r *\<^sub>R g x" for r x
      by (auto simp add: g_def X_cmult scaleR_sum_right intro!: sum.mono_neutral_cong_left X)
  qed
  moreover have "\<forall>x\<in>B. g x = f x"
    using \<open>B \<subseteq> B'\<close> by (auto simp: g_f' f'_def)
  moreover have "range g = span (f`B)"
    unfolding \<open>span B' = UNIV\<close>[symmetric] span_linear_image[OF \<open>linear g\<close>, symmetric]
  proof (rule span_subspace)
    have "g ` B' \<subseteq> f`B \<union> {0}"
      by (auto simp: g_f' f'_def)
    also have "\<dots> \<subseteq> span (f`B)"
      by (auto intro: span_superset span_0)
    finally show "g ` B' \<subseteq> span (f`B)"
      by auto
    have "x \<in> B \<Longrightarrow> f x = g x" for x
      using \<open>B \<subseteq> B'\<close> by (auto simp add: g_f' f'_def)
    then show "span (f ` B) \<subseteq> span (g ` B')"
      using \<open>B \<subseteq> B'\<close> by (intro span_mono) auto
  qed (rule subspace_span)
  ultimately show ?thesis
    by auto
qed

lemma linear_independent_extend:
  "independent B \<Longrightarrow> \<exists>g. linear g \<and> (\<forall>x\<in>B. g x = f x)"
  using linear_independent_extend_subspace[of B f] by auto

text \<open>Linear functions are equal on a subspace if they are on a spanning set.\<close>

lemma subspace_kernel:
  assumes lf: "linear f"
  shows "subspace {x. f x = 0}"
  apply (simp add: subspace_def)
  apply (simp add: linear_add[OF lf] linear_cmul[OF lf] linear_0[OF lf])
  done

lemma linear_eq_0_span:
  assumes lf: "linear f" and f0: "\<forall>x\<in>B. f x = 0"
  shows "\<forall>x \<in> span B. f x = 0"
  using f0 subspace_kernel[OF lf]
  by (rule span_induct')

lemma linear_eq_0: "linear f \<Longrightarrow> S \<subseteq> span B \<Longrightarrow> \<forall>x\<in>B. f x = 0 \<Longrightarrow> \<forall>x\<in>S. f x = 0"
  using linear_eq_0_span[of f B] by auto

lemma linear_eq_span:  "linear f \<Longrightarrow> linear g \<Longrightarrow> \<forall>x\<in>B. f x = g x \<Longrightarrow> \<forall>x \<in> span B. f x = g x"
  using linear_eq_0_span[of "\<lambda>x. f x - g x" B] by (auto simp: linear_compose_sub)

lemma linear_eq: "linear f \<Longrightarrow> linear g \<Longrightarrow> S \<subseteq> span B \<Longrightarrow> \<forall>x\<in>B. f x = g x \<Longrightarrow> \<forall>x\<in>S. f x = g x"
  using linear_eq_span[of f g B] by auto

text \<open>The degenerate case of the Exchange Lemma.\<close>

lemma spanning_subset_independent:
  assumes BA: "B \<subseteq> A"
    and iA: "independent A"
    and AsB: "A \<subseteq> span B"
  shows "A = B"
proof
  show "B \<subseteq> A" by (rule BA)

  from span_mono[OF BA] span_mono[OF AsB]
  have sAB: "span A = span B" unfolding span_span by blast

  {
    fix x
    assume x: "x \<in> A"
    from iA have th0: "x \<notin> span (A - {x})"
      unfolding dependent_def using x by blast
    from x have xsA: "x \<in> span A"
      by (blast intro: span_superset)
    have "A - {x} \<subseteq> A" by blast
    then have th1: "span (A - {x}) \<subseteq> span A"
      by (metis span_mono)
    {
      assume xB: "x \<notin> B"
      from xB BA have "B \<subseteq> A - {x}"
        by blast
      then have "span B \<subseteq> span (A - {x})"
        by (metis span_mono)
      with th1 th0 sAB have "x \<notin> span A"
        by blast
      with x have False
        by (metis span_superset)
    }
    then have "x \<in> B" by blast
  }
  then show "A \<subseteq> B" by blast
qed

text \<open>Relation between bases and injectivity/surjectivity of map.\<close>

lemma spanning_surjective_image:
  assumes us: "UNIV \<subseteq> span S"
    and lf: "linear f"
    and sf: "surj f"
  shows "UNIV \<subseteq> span (f ` S)"
proof -
  have "UNIV \<subseteq> f ` UNIV"
    using sf by (auto simp add: surj_def)
  also have " \<dots> \<subseteq> span (f ` S)"
    using spans_image[OF lf us] .
  finally show ?thesis .
qed

lemma independent_inj_on_image:
  assumes iS: "independent S"
    and lf: "linear f"
    and fi: "inj_on f (span S)"
  shows "independent (f ` S)"
proof -
  {
    fix a
    assume a: "a \<in> S" "f a \<in> span (f ` S - {f a})"
    have eq: "f ` S - {f a} = f ` (S - {a})"
      using fi \<open>a\<in>S\<close> by (auto simp add: inj_on_def span_superset)
    from a have "f a \<in> f ` span (S - {a})"
      unfolding eq span_linear_image[OF lf, of "S - {a}"] by blast
    then have "a \<in> span (S - {a})"
      by (rule inj_on_image_mem_iff_alt[OF fi, rotated])
         (insert span_mono[of "S - {a}" S], auto intro: span_superset \<open>a\<in>S\<close>)
    with a(1) iS have False
      by (simp add: dependent_def)
  }
  then show ?thesis
    unfolding dependent_def by blast
qed

lemma independent_injective_image:
  "independent S \<Longrightarrow> linear f \<Longrightarrow> inj f \<Longrightarrow> independent (f ` S)"
  using independent_inj_on_image[of S f] by (auto simp: subset_inj_on)

text \<open>Detailed theorems about left and right invertibility in general case.\<close>

lemma linear_inj_on_left_inverse:
  assumes lf: "linear f" and fi: "inj_on f (span S)"
  shows "\<exists>g. range g \<subseteq> span S \<and> linear g \<and> (\<forall>x\<in>span S. g (f x) = x)"
proof -
  obtain B where "independent B" "B \<subseteq> S" "S \<subseteq> span B"
    using maximal_independent_subset[of S] by auto
  then have "span S = span B"
    unfolding span_eq by (auto simp: span_superset)
  with linear_independent_extend_subspace[OF independent_inj_on_image, OF \<open>independent B\<close> lf] fi
  obtain g where g: "linear g" "\<forall>x\<in>f ` B. g x = inv_into B f x" "range g = span (inv_into B f ` f ` B)"
    by fastforce
  have fB: "inj_on f B"
    using fi by (auto simp: \<open>span S = span B\<close> intro: subset_inj_on span_superset)

  have "\<forall>x\<in>span B. g (f x) = x"
  proof (intro linear_eq_span)
    show "linear (\<lambda>x. x)" "linear (\<lambda>x. g (f x))"
      using linear_id linear_compose[OF \<open>linear f\<close> \<open>linear g\<close>] by (auto simp: id_def comp_def)
    show "\<forall>x \<in> B. g (f x) = x"
      using g fi \<open>span S = span B\<close> by (auto simp: fB)
  qed
  moreover
  have "inv_into B f ` f ` B \<subseteq> B"
    by (auto simp: fB)
  then have "range g \<subseteq> span S"
    unfolding g \<open>span S = span B\<close> by (intro span_mono)
  ultimately show ?thesis
    using \<open>span S = span B\<close> \<open>linear g\<close> by auto
qed

lemma linear_injective_left_inverse: "linear f \<Longrightarrow> inj f \<Longrightarrow> \<exists>g. linear g \<and> g \<circ> f = id"
  using linear_inj_on_left_inverse[of f UNIV] by (auto simp: fun_eq_iff span_UNIV)

lemma linear_surj_right_inverse:
  assumes lf: "linear f" and sf: "span T \<subseteq> f`span S"
  shows "\<exists>g. range g \<subseteq> span S \<and> linear g \<and> (\<forall>x\<in>span T. f (g x) = x)"
proof -
  obtain B where "independent B" "B \<subseteq> T" "T \<subseteq> span B"
    using maximal_independent_subset[of T] by auto
  then have "span T = span B"
    unfolding span_eq by (auto simp: span_superset)

  from linear_independent_extend_subspace[OF \<open>independent B\<close>, of "inv_into (span S) f"]
  obtain g where g: "linear g" "\<forall>x\<in>B. g x = inv_into (span S) f x" "range g = span (inv_into (span S) f`B)"
    by auto
  moreover have "x \<in> B \<Longrightarrow> f (inv_into (span S) f x) = x" for x
    using \<open>B \<subseteq> T\<close> \<open>span T \<subseteq> f`span S\<close> by (intro f_inv_into_f) (auto intro: span_superset)
  ultimately have "\<forall>x\<in>B. f (g x) = x"
    by auto
  then have "\<forall>x\<in>span B. f (g x) = x"
    using linear_id linear_compose[OF \<open>linear g\<close> \<open>linear f\<close>]
    by (intro linear_eq_span) (auto simp: id_def comp_def)
  moreover have "inv_into (span S) f ` B \<subseteq> span S"
    using \<open>B \<subseteq> T\<close> \<open>span T \<subseteq> f`span S\<close> by (auto intro: inv_into_into span_superset)
  then have "range g \<subseteq> span S"
    unfolding g by (intro span_minimal subspace_span) auto
  ultimately show ?thesis
    using \<open>linear g\<close> \<open>span T = span B\<close> by auto
qed

lemma linear_surjective_right_inverse: "linear f \<Longrightarrow> surj f \<Longrightarrow> \<exists>g. linear g \<and> f \<circ> g = id"
  using linear_surj_right_inverse[of f UNIV UNIV]
  by (auto simp: span_UNIV fun_eq_iff)

text \<open>The general case of the Exchange Lemma, the key to what follows.\<close>

lemma exchange_lemma:
  assumes f:"finite t"
    and i: "independent s"
    and sp: "s \<subseteq> span t"
  shows "\<exists>t'. card t' = card t \<and> finite t' \<and> s \<subseteq> t' \<and> t' \<subseteq> s \<union> t \<and> s \<subseteq> span t'"
  using f i sp
proof (induct "card (t - s)" arbitrary: s t rule: less_induct)
  case less
  note ft = \<open>finite t\<close> and s = \<open>independent s\<close> and sp = \<open>s \<subseteq> span t\<close>
  let ?P = "\<lambda>t'. card t' = card t \<and> finite t' \<and> s \<subseteq> t' \<and> t' \<subseteq> s \<union> t \<and> s \<subseteq> span t'"
  let ?ths = "\<exists>t'. ?P t'"
  {
    assume "s \<subseteq> t"
    then have ?ths
      by (metis ft Un_commute sp sup_ge1)
  }
  moreover
  {
    assume st: "t \<subseteq> s"
    from spanning_subset_independent[OF st s sp] st ft span_mono[OF st]
    have ?ths
      by (metis Un_absorb sp)
  }
  moreover
  {
    assume st: "\<not> s \<subseteq> t" "\<not> t \<subseteq> s"
    from st(2) obtain b where b: "b \<in> t" "b \<notin> s"
      by blast
    from b have "t - {b} - s \<subset> t - s"
      by blast
    then have cardlt: "card (t - {b} - s) < card (t - s)"
      using ft by (auto intro: psubset_card_mono)
    from b ft have ct0: "card t \<noteq> 0"
      by auto
    have ?ths
    proof cases
      assume stb: "s \<subseteq> span (t - {b})"
      from ft have ftb: "finite (t - {b})"
        by auto
      from less(1)[OF cardlt ftb s stb]
      obtain u where u: "card u = card (t - {b})" "s \<subseteq> u" "u \<subseteq> s \<union> (t - {b})" "s \<subseteq> span u"
        and fu: "finite u" by blast
      let ?w = "insert b u"
      have th0: "s \<subseteq> insert b u"
        using u by blast
      from u(3) b have "u \<subseteq> s \<union> t"
        by blast
      then have th1: "insert b u \<subseteq> s \<union> t"
        using u b by blast
      have bu: "b \<notin> u"
        using b u by blast
      from u(1) ft b have "card u = (card t - 1)"
        by auto
      then have th2: "card (insert b u) = card t"
        using card_insert_disjoint[OF fu bu] ct0 by auto
      from u(4) have "s \<subseteq> span u" .
      also have "\<dots> \<subseteq> span (insert b u)"
        by (rule span_mono) blast
      finally have th3: "s \<subseteq> span (insert b u)" .
      from th0 th1 th2 th3 fu have th: "?P ?w"
        by blast
      from th show ?thesis by blast
    next
      assume stb: "\<not> s \<subseteq> span (t - {b})"
      from stb obtain a where a: "a \<in> s" "a \<notin> span (t - {b})"
        by blast
      have ab: "a \<noteq> b"
        using a b by blast
      have at: "a \<notin> t"
        using a ab span_superset[of a "t- {b}"] by auto
      have mlt: "card ((insert a (t - {b})) - s) < card (t - s)"
        using cardlt ft a b by auto
      have ft': "finite (insert a (t - {b}))"
        using ft by auto
      {
        fix x
        assume xs: "x \<in> s"
        have t: "t \<subseteq> insert b (insert a (t - {b}))"
          using b by auto
        from b(1) have "b \<in> span t"
          by (simp add: span_superset)
        have bs: "b \<in> span (insert a (t - {b}))"
          apply (rule in_span_delete)
          using a sp unfolding subset_eq
          apply auto
          done
        from xs sp have "x \<in> span t"
          by blast
        with span_mono[OF t] have x: "x \<in> span (insert b (insert a (t - {b})))" ..
        from span_trans[OF bs x] have "x \<in> span (insert a (t - {b}))" .
      }
      then have sp': "s \<subseteq> span (insert a (t - {b}))"
        by blast
      from less(1)[OF mlt ft' s sp'] obtain u where u:
        "card u = card (insert a (t - {b}))"
        "finite u" "s \<subseteq> u" "u \<subseteq> s \<union> insert a (t - {b})"
        "s \<subseteq> span u" by blast
      from u a b ft at ct0 have "?P u"
        by auto
      then show ?thesis by blast
    qed
  }
  ultimately show ?ths by blast
qed

text \<open>This implies corresponding size bounds.\<close>

lemma independent_span_bound:
  assumes f: "finite t"
    and i: "independent s"
    and sp: "s \<subseteq> span t"
  shows "finite s \<and> card s \<le> card t"
  by (metis exchange_lemma[OF f i sp] finite_subset card_mono)

lemma finite_Atleast_Atmost_nat[simp]: "finite {f x |x. x\<in> (UNIV::'a::finite set)}"
proof -
  have eq: "{f x |x. x\<in> UNIV} = f ` UNIV"
    by auto
  show ?thesis unfolding eq
    apply (rule finite_imageI)
    apply (rule finite)
    done
qed


subsection \<open>More interesting properties of the norm.\<close>

lemma cond_application_beta: "(if b then f else g) x = (if b then f x else g x)"
  by auto

notation inner (infix "\<bullet>" 70)

lemma square_bound_lemma:
  fixes x :: real
  shows "x < (1 + x) * (1 + x)"
proof -
  have "(x + 1/2)\<^sup>2 + 3/4 > 0"
    using zero_le_power2[of "x+1/2"] by arith
  then show ?thesis
    by (simp add: field_simps power2_eq_square)
qed

lemma square_continuous:
  fixes e :: real
  shows "e > 0 \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>y. \<bar>y - x\<bar> < d \<longrightarrow> \<bar>y * y - x * x\<bar> < e)"
  using isCont_power[OF continuous_ident, of x, unfolded isCont_def LIM_eq, rule_format, of e 2]
  by (force simp add: power2_eq_square)


lemma norm_eq_0_dot: "norm x = 0 \<longleftrightarrow> x \<bullet> x = (0::real)"
  by simp (* TODO: delete *)

lemma norm_triangle_sub:
  fixes x y :: "'a::real_normed_vector"
  shows "norm x \<le> norm y + norm (x - y)"
  using norm_triangle_ineq[of "y" "x - y"] by (simp add: field_simps)

lemma norm_le: "norm x \<le> norm y \<longleftrightarrow> x \<bullet> x \<le> y \<bullet> y"
  by (simp add: norm_eq_sqrt_inner)

lemma norm_lt: "norm x < norm y \<longleftrightarrow> x \<bullet> x < y \<bullet> y"
  by (simp add: norm_eq_sqrt_inner)

lemma norm_eq: "norm x = norm y \<longleftrightarrow> x \<bullet> x = y \<bullet> y"
  apply (subst order_eq_iff)
  apply (auto simp: norm_le)
  done

lemma norm_eq_1: "norm x = 1 \<longleftrightarrow> x \<bullet> x = 1"
  by (simp add: norm_eq_sqrt_inner)

text\<open>Squaring equations and inequalities involving norms.\<close>

lemma dot_square_norm: "x \<bullet> x = (norm x)\<^sup>2"
  by (simp only: power2_norm_eq_inner) (* TODO: move? *)

lemma norm_eq_square: "norm x = a \<longleftrightarrow> 0 \<le> a \<and> x \<bullet> x = a\<^sup>2"
  by (auto simp add: norm_eq_sqrt_inner)

lemma norm_le_square: "norm x \<le> a \<longleftrightarrow> 0 \<le> a \<and> x \<bullet> x \<le> a\<^sup>2"
  apply (simp add: dot_square_norm abs_le_square_iff[symmetric])
  using norm_ge_zero[of x]
  apply arith
  done

lemma norm_ge_square: "norm x \<ge> a \<longleftrightarrow> a \<le> 0 \<or> x \<bullet> x \<ge> a\<^sup>2"
  apply (simp add: dot_square_norm abs_le_square_iff[symmetric])
  using norm_ge_zero[of x]
  apply arith
  done

lemma norm_lt_square: "norm x < a \<longleftrightarrow> 0 < a \<and> x \<bullet> x < a\<^sup>2"
  by (metis not_le norm_ge_square)

lemma norm_gt_square: "norm x > a \<longleftrightarrow> a < 0 \<or> x \<bullet> x > a\<^sup>2"
  by (metis norm_le_square not_less)

text\<open>Dot product in terms of the norm rather than conversely.\<close>

lemmas inner_simps = inner_add_left inner_add_right inner_diff_right inner_diff_left
  inner_scaleR_left inner_scaleR_right

lemma dot_norm: "x \<bullet> y = ((norm (x + y))\<^sup>2 - (norm x)\<^sup>2 - (norm y)\<^sup>2) / 2"
  by (simp only: power2_norm_eq_inner inner_simps inner_commute) auto

lemma dot_norm_neg: "x \<bullet> y = (((norm x)\<^sup>2 + (norm y)\<^sup>2) - (norm (x - y))\<^sup>2) / 2"
  by (simp only: power2_norm_eq_inner inner_simps inner_commute)
    (auto simp add: algebra_simps)

text\<open>Equality of vectors in terms of @{term "op \<bullet>"} products.\<close>

lemma linear_componentwise:
  fixes f:: "'a::euclidean_space \<Rightarrow> 'b::real_inner"
  assumes lf: "linear f"
  shows "(f x) \<bullet> j = (\<Sum>i\<in>Basis. (x\<bullet>i) * (f i\<bullet>j))" (is "?lhs = ?rhs")
proof -
  have "?rhs = (\<Sum>i\<in>Basis. (x\<bullet>i) *\<^sub>R (f i))\<bullet>j"
    by (simp add: inner_sum_left)
  then show ?thesis
    unfolding linear_sum_mul[OF lf, symmetric]
    unfolding euclidean_representation ..
qed

lemma vector_eq: "x = y \<longleftrightarrow> x \<bullet> x = x \<bullet> y \<and> y \<bullet> y = x \<bullet> x"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs by simp
next
  assume ?rhs
  then have "x \<bullet> x - x \<bullet> y = 0 \<and> x \<bullet> y - y \<bullet> y = 0"
    by simp
  then have "x \<bullet> (x - y) = 0 \<and> y \<bullet> (x - y) = 0"
    by (simp add: inner_diff inner_commute)
  then have "(x - y) \<bullet> (x - y) = 0"
    by (simp add: field_simps inner_diff inner_commute)
  then show "x = y" by simp
qed

lemma norm_triangle_half_r:
  "norm (y - x1) < e / 2 \<Longrightarrow> norm (y - x2) < e / 2 \<Longrightarrow> norm (x1 - x2) < e"
  using dist_triangle_half_r unfolding dist_norm[symmetric] by auto

lemma norm_triangle_half_l:
  assumes "norm (x - y) < e / 2"
    and "norm (x' - y) < e / 2"
  shows "norm (x - x') < e"
  using dist_triangle_half_l[OF assms[unfolded dist_norm[symmetric]]]
  unfolding dist_norm[symmetric] .

lemma norm_triangle_le: "norm x + norm y \<le> e \<Longrightarrow> norm (x + y) \<le> e"
  by (rule norm_triangle_ineq [THEN order_trans])

lemma norm_triangle_lt: "norm x + norm y < e \<Longrightarrow> norm (x + y) < e"
  by (rule norm_triangle_ineq [THEN le_less_trans])

lemma sum_clauses:
  shows "sum f {} = 0"
    and "finite S \<Longrightarrow> sum f (insert x S) = (if x \<in> S then sum f S else f x + sum f S)"
  by (auto simp add: insert_absorb)

lemma sum_norm_bound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes K: "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> K"
  shows "norm (sum f S) \<le> of_nat (card S)*K"
  using sum_norm_le[OF K] sum_constant[symmetric]
  by simp

lemma sum_group:
  assumes fS: "finite S" and fT: "finite T" and fST: "f ` S \<subseteq> T"
  shows "sum (\<lambda>y. sum g {x. x \<in> S \<and> f x = y}) T = sum g S"
  apply (subst sum_image_gen[OF fS, of g f])
  apply (rule sum.mono_neutral_right[OF fT fST])
  apply (auto intro: sum.neutral)
  done

lemma vector_eq_ldot: "(\<forall>x. x \<bullet> y = x \<bullet> z) \<longleftrightarrow> y = z"
proof
  assume "\<forall>x. x \<bullet> y = x \<bullet> z"
  then have "\<forall>x. x \<bullet> (y - z) = 0"
    by (simp add: inner_diff)
  then have "(y - z) \<bullet> (y - z) = 0" ..
  then show "y = z" by simp
qed simp

lemma vector_eq_rdot: "(\<forall>z. x \<bullet> z = y \<bullet> z) \<longleftrightarrow> x = y"
proof
  assume "\<forall>z. x \<bullet> z = y \<bullet> z"
  then have "\<forall>z. (x - y) \<bullet> z = 0"
    by (simp add: inner_diff)
  then have "(x - y) \<bullet> (x - y) = 0" ..
  then show "x = y" by simp
qed simp


subsection \<open>Orthogonality.\<close>

context real_inner
begin

definition "orthogonal x y \<longleftrightarrow> x \<bullet> y = 0"

lemma orthogonal_self: "orthogonal x x \<longleftrightarrow> x = 0"
  by (simp add: orthogonal_def)

lemma orthogonal_clauses:
  "orthogonal a 0"
  "orthogonal a x \<Longrightarrow> orthogonal a (c *\<^sub>R x)"
  "orthogonal a x \<Longrightarrow> orthogonal a (- x)"
  "orthogonal a x \<Longrightarrow> orthogonal a y \<Longrightarrow> orthogonal a (x + y)"
  "orthogonal a x \<Longrightarrow> orthogonal a y \<Longrightarrow> orthogonal a (x - y)"
  "orthogonal 0 a"
  "orthogonal x a \<Longrightarrow> orthogonal (c *\<^sub>R x) a"
  "orthogonal x a \<Longrightarrow> orthogonal (- x) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a \<Longrightarrow> orthogonal (x + y) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a \<Longrightarrow> orthogonal (x - y) a"
  unfolding orthogonal_def inner_add inner_diff by auto

end

lemma orthogonal_commute: "orthogonal x y \<longleftrightarrow> orthogonal y x"
  by (simp add: orthogonal_def inner_commute)

lemma orthogonal_scaleR [simp]: "c \<noteq> 0 \<Longrightarrow> orthogonal (c *\<^sub>R x) = orthogonal x"
  by (rule ext) (simp add: orthogonal_def)

lemma pairwise_ortho_scaleR:
    "pairwise (\<lambda>i j. orthogonal (f i) (g j)) B
    \<Longrightarrow> pairwise (\<lambda>i j. orthogonal (a i *\<^sub>R f i) (a j *\<^sub>R g j)) B"
  by (auto simp: pairwise_def orthogonal_clauses)

lemma orthogonal_rvsum:
    "\<lbrakk>finite s; \<And>y. y \<in> s \<Longrightarrow> orthogonal x (f y)\<rbrakk> \<Longrightarrow> orthogonal x (sum f s)"
  by (induction s rule: finite_induct) (auto simp: orthogonal_clauses)

lemma orthogonal_lvsum:
    "\<lbrakk>finite s; \<And>x. x \<in> s \<Longrightarrow> orthogonal (f x) y\<rbrakk> \<Longrightarrow> orthogonal (sum f s) y"
  by (induction s rule: finite_induct) (auto simp: orthogonal_clauses)

lemma norm_add_Pythagorean:
  assumes "orthogonal a b"
    shows "norm(a + b) ^ 2 = norm a ^ 2 + norm b ^ 2"
proof -
  from assms have "(a - (0 - b)) \<bullet> (a - (0 - b)) = a \<bullet> a - (0 - b \<bullet> b)"
    by (simp add: algebra_simps orthogonal_def inner_commute)
  then show ?thesis
    by (simp add: power2_norm_eq_inner)
qed

lemma norm_sum_Pythagorean:
  assumes "finite I" "pairwise (\<lambda>i j. orthogonal (f i) (f j)) I"
    shows "(norm (sum f I))\<^sup>2 = (\<Sum>i\<in>I. (norm (f i))\<^sup>2)"
using assms
proof (induction I rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert x I)
  then have "orthogonal (f x) (sum f I)"
    by (metis pairwise_insert orthogonal_rvsum)
  with insert show ?case
    by (simp add: pairwise_insert norm_add_Pythagorean)
qed


subsection \<open>Bilinear functions.\<close>

definition "bilinear f \<longleftrightarrow> (\<forall>x. linear (\<lambda>y. f x y)) \<and> (\<forall>y. linear (\<lambda>x. f x y))"

lemma bilinear_ladd: "bilinear h \<Longrightarrow> h (x + y) z = h x z + h y z"
  by (simp add: bilinear_def linear_iff)

lemma bilinear_radd: "bilinear h \<Longrightarrow> h x (y + z) = h x y + h x z"
  by (simp add: bilinear_def linear_iff)

lemma bilinear_lmul: "bilinear h \<Longrightarrow> h (c *\<^sub>R x) y = c *\<^sub>R h x y"
  by (simp add: bilinear_def linear_iff)

lemma bilinear_rmul: "bilinear h \<Longrightarrow> h x (c *\<^sub>R y) = c *\<^sub>R h x y"
  by (simp add: bilinear_def linear_iff)

lemma bilinear_lneg: "bilinear h \<Longrightarrow> h (- x) y = - h x y"
  by (drule bilinear_lmul [of _ "- 1"]) simp

lemma bilinear_rneg: "bilinear h \<Longrightarrow> h x (- y) = - h x y"
  by (drule bilinear_rmul [of _ _ "- 1"]) simp

lemma (in ab_group_add) eq_add_iff: "x = x + y \<longleftrightarrow> y = 0"
  using add_left_imp_eq[of x y 0] by auto

lemma bilinear_lzero:
  assumes "bilinear h"
  shows "h 0 x = 0"
  using bilinear_ladd [OF assms, of 0 0 x] by (simp add: eq_add_iff field_simps)

lemma bilinear_rzero:
  assumes "bilinear h"
  shows "h x 0 = 0"
  using bilinear_radd [OF assms, of x 0 0 ] by (simp add: eq_add_iff field_simps)

lemma bilinear_lsub: "bilinear h \<Longrightarrow> h (x - y) z = h x z - h y z"
  using bilinear_ladd [of h x "- y"] by (simp add: bilinear_lneg)

lemma bilinear_rsub: "bilinear h \<Longrightarrow> h z (x - y) = h z x - h z y"
  using bilinear_radd [of h _ x "- y"] by (simp add: bilinear_rneg)

lemma bilinear_sum:
  assumes bh: "bilinear h"
    and fS: "finite S"
    and fT: "finite T"
  shows "h (sum f S) (sum g T) = sum (\<lambda>(i,j). h (f i) (g j)) (S \<times> T) "
proof -
  have "h (sum f S) (sum g T) = sum (\<lambda>x. h (f x) (sum g T)) S"
    apply (rule linear_sum[unfolded o_def])
    using bh fS
    apply (auto simp add: bilinear_def)
    done
  also have "\<dots> = sum (\<lambda>x. sum (\<lambda>y. h (f x) (g y)) T) S"
    apply (rule sum.cong, simp)
    apply (rule linear_sum[unfolded o_def])
    using bh fT
    apply (auto simp add: bilinear_def)
    done
  finally show ?thesis
    unfolding sum.cartesian_product .
qed


subsection \<open>Adjoints.\<close>

definition "adjoint f = (SOME f'. \<forall>x y. f x \<bullet> y = x \<bullet> f' y)"

lemma adjoint_unique:
  assumes "\<forall>x y. inner (f x) y = inner x (g y)"
  shows "adjoint f = g"
  unfolding adjoint_def
proof (rule some_equality)
  show "\<forall>x y. inner (f x) y = inner x (g y)"
    by (rule assms)
next
  fix h
  assume "\<forall>x y. inner (f x) y = inner x (h y)"
  then have "\<forall>x y. inner x (g y) = inner x (h y)"
    using assms by simp
  then have "\<forall>x y. inner x (g y - h y) = 0"
    by (simp add: inner_diff_right)
  then have "\<forall>y. inner (g y - h y) (g y - h y) = 0"
    by simp
  then have "\<forall>y. h y = g y"
    by simp
  then show "h = g" by (simp add: ext)
qed

text \<open>TODO: The following lemmas about adjoints should hold for any
  Hilbert space (i.e. complete inner product space).
  (see \<^url>\<open>http://en.wikipedia.org/wiki/Hermitian_adjoint\<close>)
\<close>

lemma adjoint_works:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "x \<bullet> adjoint f y = f x \<bullet> y"
proof -
  have "\<forall>y. \<exists>w. \<forall>x. f x \<bullet> y = x \<bullet> w"
  proof (intro allI exI)
    fix y :: "'m" and x
    let ?w = "(\<Sum>i\<in>Basis. (f i \<bullet> y) *\<^sub>R i) :: 'n"
    have "f x \<bullet> y = f (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R i) \<bullet> y"
      by (simp add: euclidean_representation)
    also have "\<dots> = (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R f i) \<bullet> y"
      unfolding linear_sum[OF lf]
      by (simp add: linear_cmul[OF lf])
    finally show "f x \<bullet> y = x \<bullet> ?w"
      by (simp add: inner_sum_left inner_sum_right mult.commute)
  qed
  then show ?thesis
    unfolding adjoint_def choice_iff
    by (intro someI2_ex[where Q="\<lambda>f'. x \<bullet> f' y = f x \<bullet> y"]) auto
qed

lemma adjoint_clauses:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "x \<bullet> adjoint f y = f x \<bullet> y"
    and "adjoint f y \<bullet> x = y \<bullet> f x"
  by (simp_all add: adjoint_works[OF lf] inner_commute)

lemma adjoint_linear:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "linear (adjoint f)"
  by (simp add: lf linear_iff euclidean_eq_iff[where 'a='n] euclidean_eq_iff[where 'a='m]
    adjoint_clauses[OF lf] inner_distrib)

lemma adjoint_adjoint:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "adjoint (adjoint f) = f"
  by (rule adjoint_unique, simp add: adjoint_clauses [OF lf])


subsection \<open>Interlude: Some properties of real sets\<close>

lemma seq_mono_lemma:
  assumes "\<forall>(n::nat) \<ge> m. (d n :: real) < e n"
    and "\<forall>n \<ge> m. e n \<le> e m"
  shows "\<forall>n \<ge> m. d n < e m"
  using assms
  apply auto
  apply (erule_tac x="n" in allE)
  apply (erule_tac x="n" in allE)
  apply auto
  done

lemma infinite_enumerate:
  assumes fS: "infinite S"
  shows "\<exists>r. subseq r \<and> (\<forall>n. r n \<in> S)"
  unfolding subseq_def
  using enumerate_in_set[OF fS] enumerate_mono[of _ _ S] fS by auto

lemma approachable_lt_le: "(\<exists>(d::real) > 0. \<forall>x. f x < d \<longrightarrow> P x) \<longleftrightarrow> (\<exists>d>0. \<forall>x. f x \<le> d \<longrightarrow> P x)"
  apply auto
  apply (rule_tac x="d/2" in exI)
  apply auto
  done

lemma approachable_lt_le2:  \<comment>\<open>like the above, but pushes aside an extra formula\<close>
    "(\<exists>(d::real) > 0. \<forall>x. Q x \<longrightarrow> f x < d \<longrightarrow> P x) \<longleftrightarrow> (\<exists>d>0. \<forall>x. f x \<le> d \<longrightarrow> Q x \<longrightarrow> P x)"
  apply auto
  apply (rule_tac x="d/2" in exI, auto)
  done

lemma triangle_lemma:
  fixes x y z :: real
  assumes x: "0 \<le> x"
    and y: "0 \<le> y"
    and z: "0 \<le> z"
    and xy: "x\<^sup>2 \<le> y\<^sup>2 + z\<^sup>2"
  shows "x \<le> y + z"
proof -
  have "y\<^sup>2 + z\<^sup>2 \<le> y\<^sup>2 + 2 * y * z + z\<^sup>2"
    using z y by simp
  with xy have th: "x\<^sup>2 \<le> (y + z)\<^sup>2"
    by (simp add: power2_eq_square field_simps)
  from y z have yz: "y + z \<ge> 0"
    by arith
  from power2_le_imp_le[OF th yz] show ?thesis .
qed



subsection \<open>Archimedean properties and useful consequences\<close>

text\<open>Bernoulli's inequality\<close>
proposition Bernoulli_inequality:
  fixes x :: real
  assumes "-1 \<le> x"
    shows "1 + n * x \<le> (1 + x) ^ n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "1 + Suc n * x \<le> 1 + (Suc n)*x + n * x^2"
    by (simp add: algebra_simps)
  also have "... = (1 + x) * (1 + n*x)"
    by (auto simp: power2_eq_square algebra_simps  of_nat_Suc)
  also have "... \<le> (1 + x) ^ Suc n"
    using Suc.hyps assms mult_left_mono by fastforce
  finally show ?case .
qed

corollary Bernoulli_inequality_even:
  fixes x :: real
  assumes "even n"
    shows "1 + n * x \<le> (1 + x) ^ n"
proof (cases "-1 \<le> x \<or> n=0")
  case True
  then show ?thesis
    by (auto simp: Bernoulli_inequality)
next
  case False
  then have "real n \<ge> 1"
    by simp
  with False have "n * x \<le> -1"
    by (metis linear minus_zero mult.commute mult.left_neutral mult_left_mono_neg neg_le_iff_le order_trans zero_le_one)
  then have "1 + n * x \<le> 0"
    by auto
  also have "... \<le> (1 + x) ^ n"
    using assms
    using zero_le_even_power by blast
  finally show ?thesis .
qed

corollary real_arch_pow:
  fixes x :: real
  assumes x: "1 < x"
  shows "\<exists>n. y < x^n"
proof -
  from x have x0: "x - 1 > 0"
    by arith
  from reals_Archimedean3[OF x0, rule_format, of y]
  obtain n :: nat where n: "y < real n * (x - 1)" by metis
  from x0 have x00: "x- 1 \<ge> -1" by arith
  from Bernoulli_inequality[OF x00, of n] n
  have "y < x^n" by auto
  then show ?thesis by metis
qed

corollary real_arch_pow_inv:
  fixes x y :: real
  assumes y: "y > 0"
    and x1: "x < 1"
  shows "\<exists>n. x^n < y"
proof (cases "x > 0")
  case True
  with x1 have ix: "1 < 1/x" by (simp add: field_simps)
  from real_arch_pow[OF ix, of "1/y"]
  obtain n where n: "1/y < (1/x)^n" by blast
  then show ?thesis using y \<open>x > 0\<close>
    by (auto simp add: field_simps)
next
  case False
  with y x1 show ?thesis
    apply auto
    apply (rule exI[where x=1])
    apply auto
    done
qed

lemma forall_pos_mono:
  "(\<And>d e::real. d < e \<Longrightarrow> P d \<Longrightarrow> P e) \<Longrightarrow>
    (\<And>n::nat. n \<noteq> 0 \<Longrightarrow> P (inverse (real n))) \<Longrightarrow> (\<And>e. 0 < e \<Longrightarrow> P e)"
  by (metis real_arch_inverse)

lemma forall_pos_mono_1:
  "(\<And>d e::real. d < e \<Longrightarrow> P d \<Longrightarrow> P e) \<Longrightarrow>
    (\<And>n. P (inverse (real (Suc n)))) \<Longrightarrow> 0 < e \<Longrightarrow> P e"
  apply (rule forall_pos_mono)
  apply auto
  apply (metis Suc_pred of_nat_Suc)
  done


subsection \<open>Euclidean Spaces as Typeclass\<close>

lemma independent_Basis: "independent Basis"
  unfolding dependent_def
  apply (subst span_finite)
  apply simp
  apply clarify
  apply (drule_tac f="inner a" in arg_cong)
  apply (simp add: inner_Basis inner_sum_right eq_commute)
  done

lemma span_Basis [simp]: "span Basis = UNIV"
  unfolding span_finite [OF finite_Basis]
  by (fast intro: euclidean_representation)

lemma in_span_Basis: "x \<in> span Basis"
  unfolding span_Basis ..

lemma Basis_le_norm: "b \<in> Basis \<Longrightarrow> \<bar>x \<bullet> b\<bar> \<le> norm x"
  by (rule order_trans [OF Cauchy_Schwarz_ineq2]) simp

lemma norm_bound_Basis_le: "b \<in> Basis \<Longrightarrow> norm x \<le> e \<Longrightarrow> \<bar>x \<bullet> b\<bar> \<le> e"
  by (metis Basis_le_norm order_trans)

lemma norm_bound_Basis_lt: "b \<in> Basis \<Longrightarrow> norm x < e \<Longrightarrow> \<bar>x \<bullet> b\<bar> < e"
  by (metis Basis_le_norm le_less_trans)

lemma norm_le_l1: "norm x \<le> (\<Sum>b\<in>Basis. \<bar>x \<bullet> b\<bar>)"
  apply (subst euclidean_representation[of x, symmetric])
  apply (rule order_trans[OF norm_sum])
  apply (auto intro!: sum_mono)
  done

lemma sum_norm_allsubsets_bound:
  fixes f :: "'a \<Rightarrow> 'n::euclidean_space"
  assumes fP: "finite P"
    and fPs: "\<And>Q. Q \<subseteq> P \<Longrightarrow> norm (sum f Q) \<le> e"
  shows "(\<Sum>x\<in>P. norm (f x)) \<le> 2 * real DIM('n) * e"
proof -
  have "(\<Sum>x\<in>P. norm (f x)) \<le> (\<Sum>x\<in>P. \<Sum>b\<in>Basis. \<bar>f x \<bullet> b\<bar>)"
    by (rule sum_mono) (rule norm_le_l1)
  also have "(\<Sum>x\<in>P. \<Sum>b\<in>Basis. \<bar>f x \<bullet> b\<bar>) = (\<Sum>b\<in>Basis. \<Sum>x\<in>P. \<bar>f x \<bullet> b\<bar>)"
    by (rule sum.commute)
  also have "\<dots> \<le> of_nat (card (Basis :: 'n set)) * (2 * e)"
  proof (rule sum_bounded_above)
    fix i :: 'n
    assume i: "i \<in> Basis"
    have "norm (\<Sum>x\<in>P. \<bar>f x \<bullet> i\<bar>) \<le>
      norm ((\<Sum>x\<in>P \<inter> - {x. f x \<bullet> i < 0}. f x) \<bullet> i) + norm ((\<Sum>x\<in>P \<inter> {x. f x \<bullet> i < 0}. f x) \<bullet> i)"
      by (simp add: abs_real_def sum.If_cases[OF fP] sum_negf norm_triangle_ineq4 inner_sum_left
        del: real_norm_def)
    also have "\<dots> \<le> e + e"
      unfolding real_norm_def
      by (intro add_mono norm_bound_Basis_le i fPs) auto
    finally show "(\<Sum>x\<in>P. \<bar>f x \<bullet> i\<bar>) \<le> 2*e" by simp
  qed
  also have "\<dots> = 2 * real DIM('n) * e" by simp
  finally show ?thesis .
qed


subsection \<open>Linearity and Bilinearity continued\<close>

lemma linear_bounded:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes lf: "linear f"
  shows "\<exists>B. \<forall>x. norm (f x) \<le> B * norm x"
proof
  let ?B = "\<Sum>b\<in>Basis. norm (f b)"
  show "\<forall>x. norm (f x) \<le> ?B * norm x"
  proof
    fix x :: 'a
    let ?g = "\<lambda>b. (x \<bullet> b) *\<^sub>R f b"
    have "norm (f x) = norm (f (\<Sum>b\<in>Basis. (x \<bullet> b) *\<^sub>R b))"
      unfolding euclidean_representation ..
    also have "\<dots> = norm (sum ?g Basis)"
      by (simp add: linear_sum [OF lf] linear_cmul [OF lf])
    finally have th0: "norm (f x) = norm (sum ?g Basis)" .
    have th: "norm (?g i) \<le> norm (f i) * norm x" if "i \<in> Basis" for i
    proof -
      from Basis_le_norm[OF that, of x]
      show "norm (?g i) \<le> norm (f i) * norm x"
        unfolding norm_scaleR
        apply (subst mult.commute)
        apply (rule mult_mono)
        apply (auto simp add: field_simps)
        done
    qed
    from sum_norm_le[of _ ?g, OF th]
    show "norm (f x) \<le> ?B * norm x"
      unfolding th0 sum_distrib_right by metis
  qed
qed

lemma linear_conv_bounded_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<longleftrightarrow> bounded_linear f"
proof
  assume "linear f"
  then interpret f: linear f .
  show "bounded_linear f"
  proof
    have "\<exists>B. \<forall>x. norm (f x) \<le> B * norm x"
      using \<open>linear f\<close> by (rule linear_bounded)
    then show "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
      by (simp add: mult.commute)
  qed
next
  assume "bounded_linear f"
  then interpret f: bounded_linear f .
  show "linear f" ..
qed

lemmas linear_linear = linear_conv_bounded_linear[symmetric]

lemma linear_bounded_pos:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes lf: "linear f"
  shows "\<exists>B > 0. \<forall>x. norm (f x) \<le> B * norm x"
proof -
  have "\<exists>B > 0. \<forall>x. norm (f x) \<le> norm x * B"
    using lf unfolding linear_conv_bounded_linear
    by (rule bounded_linear.pos_bounded)
  then show ?thesis
    by (simp only: mult.commute)
qed

lemma bounded_linearI':
  fixes f ::"'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c x. f (c *\<^sub>R x) = c *\<^sub>R f x"
  shows "bounded_linear f"
  unfolding linear_conv_bounded_linear[symmetric]
  by (rule linearI[OF assms])

lemma bilinear_bounded:
  fixes h :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'k::real_normed_vector"
  assumes bh: "bilinear h"
  shows "\<exists>B. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
proof (clarify intro!: exI[of _ "\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. norm (h i j)"])
  fix x :: 'm
  fix y :: 'n
  have "norm (h x y) = norm (h (sum (\<lambda>i. (x \<bullet> i) *\<^sub>R i) Basis) (sum (\<lambda>i. (y \<bullet> i) *\<^sub>R i) Basis))"
    apply (subst euclidean_representation[where 'a='m])
    apply (subst euclidean_representation[where 'a='n])
    apply rule
    done
  also have "\<dots> = norm (sum (\<lambda> (i,j). h ((x \<bullet> i) *\<^sub>R i) ((y \<bullet> j) *\<^sub>R j)) (Basis \<times> Basis))"
    unfolding bilinear_sum[OF bh finite_Basis finite_Basis] ..
  finally have th: "norm (h x y) = \<dots>" .
  show "norm (h x y) \<le> (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. norm (h i j)) * norm x * norm y"
    apply (auto simp add: sum_distrib_right th sum.cartesian_product)
    apply (rule sum_norm_le)
    apply (auto simp add: bilinear_rmul[OF bh] bilinear_lmul[OF bh]
      field_simps simp del: scaleR_scaleR)
    apply (rule mult_mono)
    apply (auto simp add: zero_le_mult_iff Basis_le_norm)
    apply (rule mult_mono)
    apply (auto simp add: zero_le_mult_iff Basis_le_norm)
    done
qed

lemma bilinear_conv_bounded_bilinear:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
  shows "bilinear h \<longleftrightarrow> bounded_bilinear h"
proof
  assume "bilinear h"
  show "bounded_bilinear h"
  proof
    fix x y z
    show "h (x + y) z = h x z + h y z"
      using \<open>bilinear h\<close> unfolding bilinear_def linear_iff by simp
  next
    fix x y z
    show "h x (y + z) = h x y + h x z"
      using \<open>bilinear h\<close> unfolding bilinear_def linear_iff by simp
  next
    fix r x y
    show "h (scaleR r x) y = scaleR r (h x y)"
      using \<open>bilinear h\<close> unfolding bilinear_def linear_iff
      by simp
  next
    fix r x y
    show "h x (scaleR r y) = scaleR r (h x y)"
      using \<open>bilinear h\<close> unfolding bilinear_def linear_iff
      by simp
  next
    have "\<exists>B. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
      using \<open>bilinear h\<close> by (rule bilinear_bounded)
    then show "\<exists>K. \<forall>x y. norm (h x y) \<le> norm x * norm y * K"
      by (simp add: ac_simps)
  qed
next
  assume "bounded_bilinear h"
  then interpret h: bounded_bilinear h .
  show "bilinear h"
    unfolding bilinear_def linear_conv_bounded_linear
    using h.bounded_linear_left h.bounded_linear_right by simp
qed

lemma bilinear_bounded_pos:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
  assumes bh: "bilinear h"
  shows "\<exists>B > 0. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
proof -
  have "\<exists>B > 0. \<forall>x y. norm (h x y) \<le> norm x * norm y * B"
    using bh [unfolded bilinear_conv_bounded_bilinear]
    by (rule bounded_bilinear.pos_bounded)
  then show ?thesis
    by (simp only: ac_simps)
qed

lemma bounded_linear_imp_has_derivative:
     "bounded_linear f \<Longrightarrow> (f has_derivative f) net"
  by (simp add: has_derivative_def bounded_linear.linear linear_diff)

lemma linear_imp_has_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<Longrightarrow> (f has_derivative f) net"
by (simp add: has_derivative_def linear_conv_bounded_linear linear_diff)

lemma bounded_linear_imp_differentiable: "bounded_linear f \<Longrightarrow> f differentiable net"
  using bounded_linear_imp_has_derivative differentiable_def by blast

lemma linear_imp_differentiable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<Longrightarrow> f differentiable net"
by (metis linear_imp_has_derivative differentiable_def)


subsection \<open>We continue.\<close>

lemma independent_bound:
  fixes S :: "'a::euclidean_space set"
  shows "independent S \<Longrightarrow> finite S \<and> card S \<le> DIM('a)"
  using independent_span_bound[OF finite_Basis, of S] by auto

corollary
  fixes S :: "'a::euclidean_space set"
  assumes "independent S"
  shows independent_imp_finite: "finite S" and independent_card_le:"card S \<le> DIM('a)"
using assms independent_bound by auto

lemma independent_explicit:
  fixes B :: "'a::euclidean_space set"
  shows "independent B \<longleftrightarrow>
         finite B \<and> (\<forall>c. (\<Sum>v\<in>B. c v *\<^sub>R v) = 0 \<longrightarrow> (\<forall>v \<in> B. c v = 0))"
apply (cases "finite B")
 apply (force simp: dependent_finite)
using independent_bound
apply auto
done

lemma dependent_biggerset:
  fixes S :: "'a::euclidean_space set"
  shows "(finite S \<Longrightarrow> card S > DIM('a)) \<Longrightarrow> dependent S"
  by (metis independent_bound not_less)

text \<open>Notion of dimension.\<close>

definition "dim V = (SOME n. \<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> card B = n)"

lemma basis_exists:
  "\<exists>B. (B :: ('a::euclidean_space) set) \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (card B = dim V)"
  unfolding dim_def some_eq_ex[of "\<lambda>n. \<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (card B = n)"]
  using maximal_independent_subset[of V] independent_bound
  by auto

corollary dim_le_card:
  fixes s :: "'a::euclidean_space set"
  shows "finite s \<Longrightarrow> dim s \<le> card s"
by (metis basis_exists card_mono)

text \<open>Consequences of independence or spanning for cardinality.\<close>

lemma independent_card_le_dim:
  fixes B :: "'a::euclidean_space set"
  assumes "B \<subseteq> V"
    and "independent B"
  shows "card B \<le> dim V"
proof -
  from basis_exists[of V] \<open>B \<subseteq> V\<close>
  obtain B' where "independent B'"
    and "B \<subseteq> span B'"
    and "card B' = dim V"
    by blast
  with independent_span_bound[OF _ \<open>independent B\<close> \<open>B \<subseteq> span B'\<close>] independent_bound[of B']
  show ?thesis by auto
qed

lemma span_card_ge_dim:
  fixes B :: "'a::euclidean_space set"
  shows "B \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> finite B \<Longrightarrow> dim V \<le> card B"
  by (metis basis_exists[of V] independent_span_bound subset_trans)

lemma basis_card_eq_dim:
  fixes V :: "'a::euclidean_space set"
  shows "B \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> independent B \<Longrightarrow> finite B \<and> card B = dim V"
  by (metis order_eq_iff independent_card_le_dim span_card_ge_dim independent_bound)

lemma dim_unique:
  fixes B :: "'a::euclidean_space set"
  shows "B \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> independent B \<Longrightarrow> card B = n \<Longrightarrow> dim V = n"
  by (metis basis_card_eq_dim)

text \<open>More lemmas about dimension.\<close>

lemma dim_UNIV [simp]: "dim (UNIV :: 'a::euclidean_space set) = DIM('a)"
  using independent_Basis
  by (intro dim_unique[of Basis]) auto

lemma dim_subset:
  fixes S :: "'a::euclidean_space set"
  shows "S \<subseteq> T \<Longrightarrow> dim S \<le> dim T"
  using basis_exists[of T] basis_exists[of S]
  by (metis independent_card_le_dim subset_trans)

lemma dim_subset_UNIV:
  fixes S :: "'a::euclidean_space set"
  shows "dim S \<le> DIM('a)"
  by (metis dim_subset subset_UNIV dim_UNIV)

text \<open>Converses to those.\<close>

lemma card_ge_dim_independent:
  fixes B :: "'a::euclidean_space set"
  assumes BV: "B \<subseteq> V"
    and iB: "independent B"
    and dVB: "dim V \<le> card B"
  shows "V \<subseteq> span B"
proof
  fix a
  assume aV: "a \<in> V"
  {
    assume aB: "a \<notin> span B"
    then have iaB: "independent (insert a B)"
      using iB aV BV by (simp add: independent_insert)
    from aV BV have th0: "insert a B \<subseteq> V"
      by blast
    from aB have "a \<notin>B"
      by (auto simp add: span_superset)
    with independent_card_le_dim[OF th0 iaB] dVB independent_bound[OF iB]
    have False by auto
  }
  then show "a \<in> span B" by blast
qed

lemma card_le_dim_spanning:
  assumes BV: "(B:: ('a::euclidean_space) set) \<subseteq> V"
    and VB: "V \<subseteq> span B"
    and fB: "finite B"
    and dVB: "dim V \<ge> card B"
  shows "independent B"
proof -
  {
    fix a
    assume a: "a \<in> B" "a \<in> span (B - {a})"
    from a fB have c0: "card B \<noteq> 0"
      by auto
    from a fB have cb: "card (B - {a}) = card B - 1"
      by auto
    from BV a have th0: "B - {a} \<subseteq> V"
      by blast
    {
      fix x
      assume x: "x \<in> V"
      from a have eq: "insert a (B - {a}) = B"
        by blast
      from x VB have x': "x \<in> span B"
        by blast
      from span_trans[OF a(2), unfolded eq, OF x']
      have "x \<in> span (B - {a})" .
    }
    then have th1: "V \<subseteq> span (B - {a})"
      by blast
    have th2: "finite (B - {a})"
      using fB by auto
    from span_card_ge_dim[OF th0 th1 th2]
    have c: "dim V \<le> card (B - {a})" .
    from c c0 dVB cb have False by simp
  }
  then show ?thesis
    unfolding dependent_def by blast
qed

lemma card_eq_dim:
  fixes B :: "'a::euclidean_space set"
  shows "B \<subseteq> V \<Longrightarrow> card B = dim V \<Longrightarrow> finite B \<Longrightarrow> independent B \<longleftrightarrow> V \<subseteq> span B"
  by (metis order_eq_iff card_le_dim_spanning card_ge_dim_independent)

text \<open>More general size bound lemmas.\<close>

lemma independent_bound_general:
  fixes S :: "'a::euclidean_space set"
  shows "independent S \<Longrightarrow> finite S \<and> card S \<le> dim S"
  by (metis independent_card_le_dim independent_bound subset_refl)

lemma dependent_biggerset_general:
  fixes S :: "'a::euclidean_space set"
  shows "(finite S \<Longrightarrow> card S > dim S) \<Longrightarrow> dependent S"
  using independent_bound_general[of S] by (metis linorder_not_le)

lemma dim_span [simp]:
  fixes S :: "'a::euclidean_space set"
  shows "dim (span S) = dim S"
proof -
  have th0: "dim S \<le> dim (span S)"
    by (auto simp add: subset_eq intro: dim_subset span_superset)
  from basis_exists[of S]
  obtain B where B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S"
    by blast
  from B have fB: "finite B" "card B = dim S"
    using independent_bound by blast+
  have bSS: "B \<subseteq> span S"
    using B(1) by (metis subset_eq span_inc)
  have sssB: "span S \<subseteq> span B"
    using span_mono[OF B(3)] by (simp add: span_span)
  from span_card_ge_dim[OF bSS sssB fB(1)] th0 show ?thesis
    using fB(2) by arith
qed

lemma subset_le_dim:
  fixes S :: "'a::euclidean_space set"
  shows "S \<subseteq> span T \<Longrightarrow> dim S \<le> dim T"
  by (metis dim_span dim_subset)

lemma span_eq_dim:
  fixes S :: "'a::euclidean_space set"
  shows "span S = span T \<Longrightarrow> dim S = dim T"
  by (metis dim_span)

lemma dim_image_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes lf: "linear f"
  shows "dim (f ` S) \<le> dim (S)"
proof -
  from basis_exists[of S] obtain B where
    B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S" by blast
  from B have fB: "finite B" "card B = dim S"
    using independent_bound by blast+
  have "dim (f ` S) \<le> card (f ` B)"
    apply (rule span_card_ge_dim)
    using lf B fB
    apply (auto simp add: span_linear_image spans_image subset_image_iff)
    done
  also have "\<dots> \<le> dim S"
    using card_image_le[OF fB(1)] fB by simp
  finally show ?thesis .
qed

text \<open>Picking an orthogonal replacement for a spanning set.\<close>

lemma vector_sub_project_orthogonal:
  fixes b x :: "'a::euclidean_space"
  shows "b \<bullet> (x - ((b \<bullet> x) / (b \<bullet> b)) *\<^sub>R b) = 0"
  unfolding inner_simps by auto

lemma pairwise_orthogonal_insert:
  assumes "pairwise orthogonal S"
    and "\<And>y. y \<in> S \<Longrightarrow> orthogonal x y"
  shows "pairwise orthogonal (insert x S)"
  using assms unfolding pairwise_def
  by (auto simp add: orthogonal_commute)

lemma basis_orthogonal:
  fixes B :: "'a::real_inner set"
  assumes fB: "finite B"
  shows "\<exists>C. finite C \<and> card C \<le> card B \<and> span C = span B \<and> pairwise orthogonal C"
  (is " \<exists>C. ?P B C")
  using fB
proof (induct rule: finite_induct)
  case empty
  then show ?case
    apply (rule exI[where x="{}"])
    apply (auto simp add: pairwise_def)
    done
next
  case (insert a B)
  note fB = \<open>finite B\<close> and aB = \<open>a \<notin> B\<close>
  from \<open>\<exists>C. finite C \<and> card C \<le> card B \<and> span C = span B \<and> pairwise orthogonal C\<close>
  obtain C where C: "finite C" "card C \<le> card B"
    "span C = span B" "pairwise orthogonal C" by blast
  let ?a = "a - sum (\<lambda>x. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x) C"
  let ?C = "insert ?a C"
  from C(1) have fC: "finite ?C"
    by simp
  from fB aB C(1,2) have cC: "card ?C \<le> card (insert a B)"
    by (simp add: card_insert_if)
  {
    fix x k
    have th0: "\<And>(a::'a) b c. a - (b - c) = c + (a - b)"
      by (simp add: field_simps)
    have "x - k *\<^sub>R (a - (\<Sum>x\<in>C. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x)) \<in> span C \<longleftrightarrow> x - k *\<^sub>R a \<in> span C"
      apply (simp only: scaleR_right_diff_distrib th0)
      apply (rule span_add_eq)
      apply (rule span_mul)
      apply (rule span_sum)
      apply (rule span_mul)
      apply (rule span_superset)
      apply assumption
      done
  }
  then have SC: "span ?C = span (insert a B)"
    unfolding set_eq_iff span_breakdown_eq C(3)[symmetric] by auto
  {
    fix y
    assume yC: "y \<in> C"
    then have Cy: "C = insert y (C - {y})"
      by blast
    have fth: "finite (C - {y})"
      using C by simp
    have "orthogonal ?a y"
      unfolding orthogonal_def
      unfolding inner_diff inner_sum_left right_minus_eq
      unfolding sum.remove [OF \<open>finite C\<close> \<open>y \<in> C\<close>]
      apply (clarsimp simp add: inner_commute[of y a])
      apply (rule sum.neutral)
      apply clarsimp
      apply (rule C(4)[unfolded pairwise_def orthogonal_def, rule_format])
      using \<open>y \<in> C\<close> by auto
  }
  with \<open>pairwise orthogonal C\<close> have CPO: "pairwise orthogonal ?C"
    by (rule pairwise_orthogonal_insert)
  from fC cC SC CPO have "?P (insert a B) ?C"
    by blast
  then show ?case by blast
qed

lemma orthogonal_basis_exists:
  fixes V :: "('a::euclidean_space) set"
  shows "\<exists>B. independent B \<and> B \<subseteq> span V \<and> V \<subseteq> span B \<and> (card B = dim V) \<and> pairwise orthogonal B"
proof -
  from basis_exists[of V] obtain B where
    B: "B \<subseteq> V" "independent B" "V \<subseteq> span B" "card B = dim V"
    by blast
  from B have fB: "finite B" "card B = dim V"
    using independent_bound by auto
  from basis_orthogonal[OF fB(1)] obtain C where
    C: "finite C" "card C \<le> card B" "span C = span B" "pairwise orthogonal C"
    by blast
  from C B have CSV: "C \<subseteq> span V"
    by (metis span_inc span_mono subset_trans)
  from span_mono[OF B(3)] C have SVC: "span V \<subseteq> span C"
    by (simp add: span_span)
  from card_le_dim_spanning[OF CSV SVC C(1)] C(2,3) fB
  have iC: "independent C"
    by (simp add: dim_span)
  from C fB have "card C \<le> dim V"
    by simp
  moreover have "dim V \<le> card C"
    using span_card_ge_dim[OF CSV SVC C(1)]
    by (simp add: dim_span)
  ultimately have CdV: "card C = dim V"
    using C(1) by simp
  from C B CSV CdV iC show ?thesis
    by auto
qed

text \<open>Low-dimensional subset is in a hyperplane (weak orthogonal complement).\<close>

lemma span_not_univ_orthogonal:
  fixes S :: "'a::euclidean_space set"
  assumes sU: "span S \<noteq> UNIV"
  shows "\<exists>a::'a. a \<noteq> 0 \<and> (\<forall>x \<in> span S. a \<bullet> x = 0)"
proof -
  from sU obtain a where a: "a \<notin> span S"
    by blast
  from orthogonal_basis_exists obtain B where
    B: "independent B" "B \<subseteq> span S" "S \<subseteq> span B" "card B = dim S" "pairwise orthogonal B"
    by blast
  from B have fB: "finite B" "card B = dim S"
    using independent_bound by auto
  from span_mono[OF B(2)] span_mono[OF B(3)]
  have sSB: "span S = span B"
    by (simp add: span_span)
  let ?a = "a - sum (\<lambda>b. (a \<bullet> b / (b \<bullet> b)) *\<^sub>R b) B"
  have "sum (\<lambda>b. (a \<bullet> b / (b \<bullet> b)) *\<^sub>R b) B \<in> span S"
    unfolding sSB
    apply (rule span_sum)
    apply (rule span_mul)
    apply (rule span_superset)
    apply assumption
    done
  with a have a0:"?a  \<noteq> 0"
    by auto
  have "\<forall>x\<in>span B. ?a \<bullet> x = 0"
  proof (rule span_induct')
    show "subspace {x. ?a \<bullet> x = 0}"
      by (auto simp add: subspace_def inner_add)
  next
    {
      fix x
      assume x: "x \<in> B"
      from x have B': "B = insert x (B - {x})"
        by blast
      have fth: "finite (B - {x})"
        using fB by simp
      have "?a \<bullet> x = 0"
        apply (subst B')
        using fB fth
        unfolding sum_clauses(2)[OF fth]
        apply simp unfolding inner_simps
        apply (clarsimp simp add: inner_add inner_sum_left)
        apply (rule sum.neutral, rule ballI)
        apply (simp only: inner_commute)
        apply (auto simp add: x field_simps
          intro: B(5)[unfolded pairwise_def orthogonal_def, rule_format])
        done
    }
    then show "\<forall>x \<in> B. ?a \<bullet> x = 0"
      by blast
  qed
  with a0 show ?thesis
    unfolding sSB by (auto intro: exI[where x="?a"])
qed

lemma span_not_univ_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes SU: "span S \<noteq> UNIV"
  shows "\<exists> a. a \<noteq>0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
  using span_not_univ_orthogonal[OF SU] by auto

lemma lowdim_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes d: "dim S < DIM('a)"
  shows "\<exists>a::'a. a \<noteq> 0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
proof -
  {
    assume "span S = UNIV"
    then have "dim (span S) = dim (UNIV :: ('a) set)"
      by simp
    then have "dim S = DIM('a)"
      by (simp add: dim_span dim_UNIV)
    with d have False by arith
  }
  then have th: "span S \<noteq> UNIV"
    by blast
  from span_not_univ_subset_hyperplane[OF th] show ?thesis .
qed

text \<open>We can extend a linear basis-basis injection to the whole set.\<close>

lemma linear_indep_image_lemma:
  assumes lf: "linear f"
    and fB: "finite B"
    and ifB: "independent (f ` B)"
    and fi: "inj_on f B"
    and xsB: "x \<in> span B"
    and fx: "f x = 0"
  shows "x = 0"
  using fB ifB fi xsB fx
proof (induct arbitrary: x rule: finite_induct[OF fB])
  case 1
  then show ?case by auto
next
  case (2 a b x)
  have fb: "finite b" using "2.prems" by simp
  have th0: "f ` b \<subseteq> f ` (insert a b)"
    apply (rule image_mono)
    apply blast
    done
  from independent_mono[ OF "2.prems"(2) th0]
  have ifb: "independent (f ` b)"  .
  have fib: "inj_on f b"
    apply (rule subset_inj_on [OF "2.prems"(3)])
    apply blast
    done
  from span_breakdown[of a "insert a b", simplified, OF "2.prems"(4)]
  obtain k where k: "x - k*\<^sub>R a \<in> span (b - {a})"
    by blast
  have "f (x - k*\<^sub>R a) \<in> span (f ` b)"
    unfolding span_linear_image[OF lf]
    apply (rule imageI)
    using k span_mono[of "b - {a}" b]
    apply blast
    done
  then have "f x - k*\<^sub>R f a \<in> span (f ` b)"
    by (simp add: linear_diff[OF lf] linear_cmul[OF lf])
  then have th: "-k *\<^sub>R f a \<in> span (f ` b)"
    using "2.prems"(5) by simp
  have xsb: "x \<in> span b"
  proof (cases "k = 0")
    case True
    with k have "x \<in> span (b - {a})" by simp
    then show ?thesis using span_mono[of "b - {a}" b]
      by blast
  next
    case False
    with span_mul[OF th, of "- 1/ k"]
    have th1: "f a \<in> span (f ` b)"
      by auto
    from inj_on_image_set_diff[OF "2.prems"(3), of "insert a b " "{a}", symmetric]
    have tha: "f ` insert a b - f ` {a} = f ` (insert a b - {a})" by blast
    from "2.prems"(2) [unfolded dependent_def bex_simps(8), rule_format, of "f a"]
    have "f a \<notin> span (f ` b)" using tha
      using "2.hyps"(2)
      "2.prems"(3) by auto
    with th1 have False by blast
    then show ?thesis by blast
  qed
  from "2.hyps"(3)[OF fb ifb fib xsb "2.prems"(5)] show "x = 0" .
qed

text \<open>Can construct an isomorphism between spaces of same dimension.\<close>

lemma subspace_isomorphism:
  fixes S :: "'a::euclidean_space set"
    and T :: "'b::euclidean_space set"
  assumes s: "subspace S"
    and t: "subspace T"
    and d: "dim S = dim T"
  shows "\<exists>f. linear f \<and> f ` S = T \<and> inj_on f S"
proof -
  from basis_exists[of S] independent_bound
  obtain B where B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S" and fB: "finite B"
    by blast
  from basis_exists[of T] independent_bound
  obtain C where C: "C \<subseteq> T" "independent C" "T \<subseteq> span C" "card C = dim T" and fC: "finite C"
    by blast
  from B(4) C(4) card_le_inj[of B C] d
  obtain f where f: "f ` B \<subseteq> C" "inj_on f B" using \<open>finite B\<close> \<open>finite C\<close>
    by auto
  from linear_independent_extend[OF B(2)]
  obtain g where g: "linear g" "\<forall>x\<in> B. g x = f x"
    by blast
  from inj_on_iff_eq_card[OF fB, of f] f(2) have "card (f ` B) = card B"
    by simp
  with B(4) C(4) have ceq: "card (f ` B) = card C"
    using d by simp
  have "g ` B = f ` B"
    using g(2) by (auto simp add: image_iff)
  also have "\<dots> = C" using card_subset_eq[OF fC f(1) ceq] .
  finally have gBC: "g ` B = C" .
  have gi: "inj_on g B"
    using f(2) g(2) by (auto simp add: inj_on_def)
  note g0 = linear_indep_image_lemma[OF g(1) fB, unfolded gBC, OF C(2) gi]
  {
    fix x y
    assume x: "x \<in> S" and y: "y \<in> S" and gxy: "g x = g y"
    from B(3) x y have x': "x \<in> span B" and y': "y \<in> span B"
      by blast+
    from gxy have th0: "g (x - y) = 0"
      by (simp add: linear_diff[OF g(1)])
    have th1: "x - y \<in> span B"
      using x' y' by (metis span_diff)
    have "x = y"
      using g0[OF th1 th0] by simp
  }
  then have giS: "inj_on g S"
    unfolding inj_on_def by blast
  from span_subspace[OF B(1,3) s] have "g ` S = span (g ` B)"
    by (simp add: span_linear_image[OF g(1)])
  also have "\<dots> = span C" unfolding gBC ..
  also have "\<dots> = T" using span_subspace[OF C(1,3) t] .
  finally have gS: "g ` S = T" .
  from g(1) gS giS show ?thesis
    by blast
qed

lemma linear_eq_stdbasis:
  fixes f :: "'a::euclidean_space \<Rightarrow> _"
  assumes lf: "linear f"
    and lg: "linear g"
    and fg: "\<forall>b\<in>Basis. f b = g b"
  shows "f = g"
  using linear_eq[OF lf lg, of _ Basis] fg by auto

text \<open>Similar results for bilinear functions.\<close>

lemma bilinear_eq:
  assumes bf: "bilinear f"
    and bg: "bilinear g"
    and SB: "S \<subseteq> span B"
    and TC: "T \<subseteq> span C"
    and fg: "\<forall>x\<in> B. \<forall>y\<in> C. f x y = g x y"
  shows "\<forall>x\<in>S. \<forall>y\<in>T. f x y = g x y "
proof -
  let ?P = "{x. \<forall>y\<in> span C. f x y = g x y}"
  from bf bg have sp: "subspace ?P"
    unfolding bilinear_def linear_iff subspace_def bf bg
    by (auto simp add: span_0 bilinear_lzero[OF bf] bilinear_lzero[OF bg] span_add Ball_def
      intro: bilinear_ladd[OF bf])

  have "\<forall>x \<in> span B. \<forall>y\<in> span C. f x y = g x y"
    apply (rule span_induct' [OF _ sp])
    apply (rule ballI)
    apply (rule span_induct')
    apply (simp add: fg)
    apply (auto simp add: subspace_def)
    using bf bg unfolding bilinear_def linear_iff
    apply (auto simp add: span_0 bilinear_rzero[OF bf] bilinear_rzero[OF bg] span_add Ball_def
      intro: bilinear_ladd[OF bf])
    done
  then show ?thesis
    using SB TC by auto
qed

lemma bilinear_eq_stdbasis:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> _"
  assumes bf: "bilinear f"
    and bg: "bilinear g"
    and fg: "\<forall>i\<in>Basis. \<forall>j\<in>Basis. f i j = g i j"
  shows "f = g"
  using bilinear_eq[OF bf bg equalityD2[OF span_Basis] equalityD2[OF span_Basis] fg] by blast

text \<open>An injective map @{typ "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"} is also surjective.\<close>

lemma linear_injective_imp_surjective:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes lf: "linear f"
    and fi: "inj f"
  shows "surj f"
proof -
  let ?U = "UNIV :: 'a set"
  from basis_exists[of ?U] obtain B
    where B: "B \<subseteq> ?U" "independent B" "?U \<subseteq> span B" "card B = dim ?U"
    by blast
  from B(4) have d: "dim ?U = card B"
    by simp
  have th: "?U \<subseteq> span (f ` B)"
    apply (rule card_ge_dim_independent)
    apply blast
    apply (rule independent_injective_image[OF B(2) lf fi])
    apply (rule order_eq_refl)
    apply (rule sym)
    unfolding d
    apply (rule card_image)
    apply (rule subset_inj_on[OF fi])
    apply blast
    done
  from th show ?thesis
    unfolding span_linear_image[OF lf] surj_def
    using B(3) by blast
qed

text \<open>And vice versa.\<close>

lemma surjective_iff_injective_gen:
  assumes fS: "finite S"
    and fT: "finite T"
    and c: "card S = card T"
    and ST: "f ` S \<subseteq> T"
  shows "(\<forall>y \<in> T. \<exists>x \<in> S. f x = y) \<longleftrightarrow> inj_on f S"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume h: "?lhs"
  {
    fix x y
    assume x: "x \<in> S"
    assume y: "y \<in> S"
    assume f: "f x = f y"
    from x fS have S0: "card S \<noteq> 0"
      by auto
    have "x = y"
    proof (rule ccontr)
      assume xy: "\<not> ?thesis"
      have th: "card S \<le> card (f ` (S - {y}))"
        unfolding c
        apply (rule card_mono)
        apply (rule finite_imageI)
        using fS apply simp
        using h xy x y f unfolding subset_eq image_iff
        apply auto
        apply (case_tac "xa = f x")
        apply (rule bexI[where x=x])
        apply auto
        done
      also have " \<dots> \<le> card (S - {y})"
        apply (rule card_image_le)
        using fS by simp
      also have "\<dots> \<le> card S - 1" using y fS by simp
      finally show False using S0 by arith
    qed
  }
  then show ?rhs
    unfolding inj_on_def by blast
next
  assume h: ?rhs
  have "f ` S = T"
    apply (rule card_subset_eq[OF fT ST])
    unfolding card_image[OF h]
    apply (rule c)
    done
  then show ?lhs by blast
qed

lemma linear_surjective_imp_injective:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes lf: "linear f"
    and sf: "surj f"
  shows "inj f"
proof -
  let ?U = "UNIV :: 'a set"
  from basis_exists[of ?U] obtain B
    where B: "B \<subseteq> ?U" "independent B" "?U \<subseteq> span B" and d: "card B = dim ?U"
    by blast
  {
    fix x
    assume x: "x \<in> span B"
    assume fx: "f x = 0"
    from B(2) have fB: "finite B"
      using independent_bound by auto
    have fBi: "independent (f ` B)"
      apply (rule card_le_dim_spanning[of "f ` B" ?U])
      apply blast
      using sf B(3)
      unfolding span_linear_image[OF lf] surj_def subset_eq image_iff
      apply blast
      using fB apply blast
      unfolding d[symmetric]
      apply (rule card_image_le)
      apply (rule fB)
      done
    have th0: "dim ?U \<le> card (f ` B)"
      apply (rule span_card_ge_dim)
      apply blast
      unfolding span_linear_image[OF lf]
      apply (rule subset_trans[where B = "f ` UNIV"])
      using sf unfolding surj_def
      apply blast
      apply (rule image_mono)
      apply (rule B(3))
      apply (metis finite_imageI fB)
      done
    moreover have "card (f ` B) \<le> card B"
      by (rule card_image_le, rule fB)
    ultimately have th1: "card B = card (f ` B)"
      unfolding d by arith
    have fiB: "inj_on f B"
      unfolding surjective_iff_injective_gen[OF fB finite_imageI[OF fB] th1 subset_refl, symmetric]
      by blast
    from linear_indep_image_lemma[OF lf fB fBi fiB x] fx
    have "x = 0" by blast
  }
  then show ?thesis
    unfolding linear_injective_0[OF lf]
    using B(3)
    by blast
qed

text \<open>Hence either is enough for isomorphism.\<close>

lemma left_right_inverse_eq:
  assumes fg: "f \<circ> g = id"
    and gh: "g \<circ> h = id"
  shows "f = h"
proof -
  have "f = f \<circ> (g \<circ> h)"
    unfolding gh by simp
  also have "\<dots> = (f \<circ> g) \<circ> h"
    by (simp add: o_assoc)
  finally show "f = h"
    unfolding fg by simp
qed

lemma isomorphism_expand:
  "f \<circ> g = id \<and> g \<circ> f = id \<longleftrightarrow> (\<forall>x. f (g x) = x) \<and> (\<forall>x. g (f x) = x)"
  by (simp add: fun_eq_iff o_def id_def)

lemma linear_injective_isomorphism:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes lf: "linear f"
    and fi: "inj f"
  shows "\<exists>f'. linear f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
  unfolding isomorphism_expand[symmetric]
  using linear_surjective_right_inverse[OF lf linear_injective_imp_surjective[OF lf fi]]
    linear_injective_left_inverse[OF lf fi]
  by (metis left_right_inverse_eq)

lemma linear_surjective_isomorphism:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes lf: "linear f"
    and sf: "surj f"
  shows "\<exists>f'. linear f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
  unfolding isomorphism_expand[symmetric]
  using linear_surjective_right_inverse[OF lf sf]
    linear_injective_left_inverse[OF lf linear_surjective_imp_injective[OF lf sf]]
  by (metis left_right_inverse_eq)

text \<open>Left and right inverses are the same for
  @{typ "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"}.\<close>

lemma linear_inverse_left:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes lf: "linear f"
    and lf': "linear f'"
  shows "f \<circ> f' = id \<longleftrightarrow> f' \<circ> f = id"
proof -
  {
    fix f f':: "'a \<Rightarrow> 'a"
    assume lf: "linear f" "linear f'"
    assume f: "f \<circ> f' = id"
    from f have sf: "surj f"
      apply (auto simp add: o_def id_def surj_def)
      apply metis
      done
    from linear_surjective_isomorphism[OF lf(1) sf] lf f
    have "f' \<circ> f = id"
      unfolding fun_eq_iff o_def id_def by metis
  }
  then show ?thesis
    using lf lf' by metis
qed

text \<open>Moreover, a one-sided inverse is automatically linear.\<close>

lemma left_inverse_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes lf: "linear f"
    and gf: "g \<circ> f = id"
  shows "linear g"
proof -
  from gf have fi: "inj f"
    apply (auto simp add: inj_on_def o_def id_def fun_eq_iff)
    apply metis
    done
  from linear_injective_isomorphism[OF lf fi]
  obtain h :: "'a \<Rightarrow> 'a" where h: "linear h" "\<forall>x. h (f x) = x" "\<forall>x. f (h x) = x"
    by blast
  have "h = g"
    apply (rule ext) using gf h(2,3)
    apply (simp add: o_def id_def fun_eq_iff)
    apply metis
    done
  with h(1) show ?thesis by blast
qed

lemma inj_linear_imp_inv_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "linear f" "inj f" shows "linear (inv f)"
using assms inj_iff left_inverse_linear by blast


subsection \<open>Infinity norm\<close>

definition "infnorm (x::'a::euclidean_space) = Sup {\<bar>x \<bullet> b\<bar> |b. b \<in> Basis}"

lemma infnorm_set_image:
  fixes x :: "'a::euclidean_space"
  shows "{\<bar>x \<bullet> i\<bar> |i. i \<in> Basis} = (\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis"
  by blast

lemma infnorm_Max:
  fixes x :: "'a::euclidean_space"
  shows "infnorm x = Max ((\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis)"
  by (simp add: infnorm_def infnorm_set_image cSup_eq_Max)

lemma infnorm_set_lemma:
  fixes x :: "'a::euclidean_space"
  shows "finite {\<bar>x \<bullet> i\<bar> |i. i \<in> Basis}"
    and "{\<bar>x \<bullet> i\<bar> |i. i \<in> Basis} \<noteq> {}"
  unfolding infnorm_set_image
  by auto

lemma infnorm_pos_le:
  fixes x :: "'a::euclidean_space"
  shows "0 \<le> infnorm x"
  by (simp add: infnorm_Max Max_ge_iff ex_in_conv)

lemma infnorm_triangle:
  fixes x :: "'a::euclidean_space"
  shows "infnorm (x + y) \<le> infnorm x + infnorm y"
proof -
  have *: "\<And>a b c d :: real. \<bar>a\<bar> \<le> c \<Longrightarrow> \<bar>b\<bar> \<le> d \<Longrightarrow> \<bar>a + b\<bar> \<le> c + d"
    by simp
  show ?thesis
    by (auto simp: infnorm_Max inner_add_left intro!: *)
qed

lemma infnorm_eq_0:
  fixes x :: "'a::euclidean_space"
  shows "infnorm x = 0 \<longleftrightarrow> x = 0"
proof -
  have "infnorm x \<le> 0 \<longleftrightarrow> x = 0"
    unfolding infnorm_Max by (simp add: euclidean_all_zero_iff)
  then show ?thesis
    using infnorm_pos_le[of x] by simp
qed

lemma infnorm_0: "infnorm 0 = 0"
  by (simp add: infnorm_eq_0)

lemma infnorm_neg: "infnorm (- x) = infnorm x"
  unfolding infnorm_def
  apply (rule cong[of "Sup" "Sup"])
  apply blast
  apply auto
  done

lemma infnorm_sub: "infnorm (x - y) = infnorm (y - x)"
proof -
  have "y - x = - (x - y)" by simp
  then show ?thesis
    by (metis infnorm_neg)
qed

lemma real_abs_sub_infnorm: "\<bar>infnorm x - infnorm y\<bar> \<le> infnorm (x - y)"
proof -
  have th: "\<And>(nx::real) n ny. nx \<le> n + ny \<Longrightarrow> ny \<le> n + nx \<Longrightarrow> \<bar>nx - ny\<bar> \<le> n"
    by arith
  from infnorm_triangle[of "x - y" " y"] infnorm_triangle[of "x - y" "-x"]
  have ths: "infnorm x \<le> infnorm (x - y) + infnorm y"
    "infnorm y \<le> infnorm (x - y) + infnorm x"
    by (simp_all add: field_simps infnorm_neg)
  from th[OF ths] show ?thesis .
qed

lemma real_abs_infnorm: "\<bar>infnorm x\<bar> = infnorm x"
  using infnorm_pos_le[of x] by arith

lemma Basis_le_infnorm:
  fixes x :: "'a::euclidean_space"
  shows "b \<in> Basis \<Longrightarrow> \<bar>x \<bullet> b\<bar> \<le> infnorm x"
  by (simp add: infnorm_Max)

lemma infnorm_mul: "infnorm (a *\<^sub>R x) = \<bar>a\<bar> * infnorm x"
  unfolding infnorm_Max
proof (safe intro!: Max_eqI)
  let ?B = "(\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis"
  {
    fix b :: 'a
    assume "b \<in> Basis"
    then show "\<bar>a *\<^sub>R x \<bullet> b\<bar> \<le> \<bar>a\<bar> * Max ?B"
      by (simp add: abs_mult mult_left_mono)
  next
    from Max_in[of ?B] obtain b where "b \<in> Basis" "Max ?B = \<bar>x \<bullet> b\<bar>"
      by (auto simp del: Max_in)
    then show "\<bar>a\<bar> * Max ((\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis) \<in> (\<lambda>i. \<bar>a *\<^sub>R x \<bullet> i\<bar>) ` Basis"
      by (intro image_eqI[where x=b]) (auto simp: abs_mult)
  }
qed simp

lemma infnorm_mul_lemma: "infnorm (a *\<^sub>R x) \<le> \<bar>a\<bar> * infnorm x"
  unfolding infnorm_mul ..

lemma infnorm_pos_lt: "infnorm x > 0 \<longleftrightarrow> x \<noteq> 0"
  using infnorm_pos_le[of x] infnorm_eq_0[of x] by arith

text \<open>Prove that it differs only up to a bound from Euclidean norm.\<close>

lemma infnorm_le_norm: "infnorm x \<le> norm x"
  by (simp add: Basis_le_norm infnorm_Max)

lemma (in euclidean_space) euclidean_inner: "inner x y = (\<Sum>b\<in>Basis. (x \<bullet> b) * (y \<bullet> b))"
  by (subst (1 2) euclidean_representation [symmetric])
    (simp add: inner_sum_right inner_Basis ac_simps)

lemma norm_le_infnorm:
  fixes x :: "'a::euclidean_space"
  shows "norm x \<le> sqrt DIM('a) * infnorm x"
proof -
  let ?d = "DIM('a)"
  have "real ?d \<ge> 0"
    by simp
  then have d2: "(sqrt (real ?d))\<^sup>2 = real ?d"
    by (auto intro: real_sqrt_pow2)
  have th: "sqrt (real ?d) * infnorm x \<ge> 0"
    by (simp add: zero_le_mult_iff infnorm_pos_le)
  have th1: "x \<bullet> x \<le> (sqrt (real ?d) * infnorm x)\<^sup>2"
    unfolding power_mult_distrib d2
    apply (subst euclidean_inner)
    apply (subst power2_abs[symmetric])
    apply (rule order_trans[OF sum_bounded_above[where K="\<bar>infnorm x\<bar>\<^sup>2"]])
    apply (auto simp add: power2_eq_square[symmetric])
    apply (subst power2_abs[symmetric])
    apply (rule power_mono)
    apply (auto simp: infnorm_Max)
    done
  from real_le_lsqrt[OF inner_ge_zero th th1]
  show ?thesis
    unfolding norm_eq_sqrt_inner id_def .
qed

lemma tendsto_infnorm [tendsto_intros]:
  assumes "(f \<longlongrightarrow> a) F"
  shows "((\<lambda>x. infnorm (f x)) \<longlongrightarrow> infnorm a) F"
proof (rule tendsto_compose [OF LIM_I assms])
  fix r :: real
  assume "r > 0"
  then show "\<exists>s>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < s \<longrightarrow> norm (infnorm x - infnorm a) < r"
    by (metis real_norm_def le_less_trans real_abs_sub_infnorm infnorm_le_norm)
qed

text \<open>Equality in Cauchy-Schwarz and triangle inequalities.\<close>

lemma norm_cauchy_schwarz_eq: "x \<bullet> y = norm x * norm y \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  {
    assume h: "x = 0"
    then have ?thesis by simp
  }
  moreover
  {
    assume h: "y = 0"
    then have ?thesis by simp
  }
  moreover
  {
    assume x: "x \<noteq> 0" and y: "y \<noteq> 0"
    from inner_eq_zero_iff[of "norm y *\<^sub>R x - norm x *\<^sub>R y"]
    have "?rhs \<longleftrightarrow>
      (norm y * (norm y * norm x * norm x - norm x * (x \<bullet> y)) -
        norm x * (norm y * (y \<bullet> x) - norm x * norm y * norm y) =  0)"
      using x y
      unfolding inner_simps
      unfolding power2_norm_eq_inner[symmetric] power2_eq_square right_minus_eq
      apply (simp add: inner_commute)
      apply (simp add: field_simps)
      apply metis
      done
    also have "\<dots> \<longleftrightarrow> (2 * norm x * norm y * (norm x * norm y - x \<bullet> y) = 0)" using x y
      by (simp add: field_simps inner_commute)
    also have "\<dots> \<longleftrightarrow> ?lhs" using x y
      apply simp
      apply metis
      done
    finally have ?thesis by blast
  }
  ultimately show ?thesis by blast
qed

lemma norm_cauchy_schwarz_abs_eq:
  "\<bar>x \<bullet> y\<bar> = norm x * norm y \<longleftrightarrow>
    norm x *\<^sub>R y = norm y *\<^sub>R x \<or> norm x *\<^sub>R y = - norm y *\<^sub>R x"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have th: "\<And>(x::real) a. a \<ge> 0 \<Longrightarrow> \<bar>x\<bar> = a \<longleftrightarrow> x = a \<or> x = - a"
    by arith
  have "?rhs \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x \<or> norm (- x) *\<^sub>R y = norm y *\<^sub>R (- x)"
    by simp
  also have "\<dots> \<longleftrightarrow>(x \<bullet> y = norm x * norm y \<or> (- x) \<bullet> y = norm x * norm y)"
    unfolding norm_cauchy_schwarz_eq[symmetric]
    unfolding norm_minus_cancel norm_scaleR ..
  also have "\<dots> \<longleftrightarrow> ?lhs"
    unfolding th[OF mult_nonneg_nonneg, OF norm_ge_zero[of x] norm_ge_zero[of y]] inner_simps
    by auto
  finally show ?thesis ..
qed

lemma norm_triangle_eq:
  fixes x y :: "'a::real_inner"
  shows "norm (x + y) = norm x + norm y \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
proof -
  {
    assume x: "x = 0 \<or> y = 0"
    then have ?thesis
      by (cases "x = 0") simp_all
  }
  moreover
  {
    assume x: "x \<noteq> 0" and y: "y \<noteq> 0"
    then have "norm x \<noteq> 0" "norm y \<noteq> 0"
      by simp_all
    then have n: "norm x > 0" "norm y > 0"
      using norm_ge_zero[of x] norm_ge_zero[of y] by arith+
    have th: "\<And>(a::real) b c. a + b + c \<noteq> 0 \<Longrightarrow> a = b + c \<longleftrightarrow> a\<^sup>2 = (b + c)\<^sup>2"
      by algebra
    have "norm (x + y) = norm x + norm y \<longleftrightarrow> (norm (x + y))\<^sup>2 = (norm x + norm y)\<^sup>2"
      apply (rule th)
      using n norm_ge_zero[of "x + y"]
      apply arith
      done
    also have "\<dots> \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
      unfolding norm_cauchy_schwarz_eq[symmetric]
      unfolding power2_norm_eq_inner inner_simps
      by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square inner_commute field_simps)
    finally have ?thesis .
  }
  ultimately show ?thesis by blast
qed


subsection \<open>Collinearity\<close>

definition collinear :: "'a::real_vector set \<Rightarrow> bool"
  where "collinear S \<longleftrightarrow> (\<exists>u. \<forall>x \<in> S. \<forall> y \<in> S. \<exists>c. x - y = c *\<^sub>R u)"

lemma collinear_alt:
     "collinear S \<longleftrightarrow> (\<exists>u v. \<forall>x \<in> S. \<exists>c. x = u + c *\<^sub>R v)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding collinear_def by (metis Groups.add_ac(2) diff_add_cancel)
next
  assume ?rhs
  then obtain u v where *: "\<And>x. x \<in> S \<Longrightarrow> \<exists>c. x = u + c *\<^sub>R v"
    by (auto simp: )
  have "\<exists>c. x - y = c *\<^sub>R v" if "x \<in> S" "y \<in> S" for x y
        by (metis *[OF \<open>x \<in> S\<close>] *[OF \<open>y \<in> S\<close>] scaleR_left.diff add_diff_cancel_left)
  then show ?lhs
    using collinear_def by blast
qed

lemma collinear:
  fixes S :: "'a::{perfect_space,real_vector} set"
  shows "collinear S \<longleftrightarrow> (\<exists>u. u \<noteq> 0 \<and> (\<forall>x \<in> S. \<forall> y \<in> S. \<exists>c. x - y = c *\<^sub>R u))"
proof -
  have "\<exists>v. v \<noteq> 0 \<and> (\<forall>x\<in>S. \<forall>y\<in>S. \<exists>c. x - y = c *\<^sub>R v)"
    if "\<forall>x\<in>S. \<forall>y\<in>S. \<exists>c. x - y = c *\<^sub>R u" "u=0" for u
  proof -
    have "\<forall>x\<in>S. \<forall>y\<in>S. x = y"
      using that by auto
    moreover
    obtain v::'a where "v \<noteq> 0"
      using UNIV_not_singleton [of 0] by auto
    ultimately have "\<forall>x\<in>S. \<forall>y\<in>S. \<exists>c. x - y = c *\<^sub>R v"
      by auto
    then show ?thesis
      using \<open>v \<noteq> 0\<close> by blast
  qed
  then show ?thesis
    apply (clarsimp simp: collinear_def)
    by (metis real_vector.scale_zero_right vector_fraction_eq_iff)
qed

lemma collinear_subset: "\<lbrakk>collinear T; S \<subseteq> T\<rbrakk> \<Longrightarrow> collinear S"
  by (meson collinear_def subsetCE)

lemma collinear_empty [iff]: "collinear {}"
  by (simp add: collinear_def)

lemma collinear_sing [iff]: "collinear {x}"
  by (simp add: collinear_def)

lemma collinear_2 [iff]: "collinear {x, y}"
  apply (simp add: collinear_def)
  apply (rule exI[where x="x - y"])
  apply auto
  apply (rule exI[where x=1], simp)
  apply (rule exI[where x="- 1"], simp)
  done

lemma collinear_lemma: "collinear {0, x, y} \<longleftrightarrow> x = 0 \<or> y = 0 \<or> (\<exists>c. y = c *\<^sub>R x)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  {
    assume "x = 0 \<or> y = 0"
    then have ?thesis
      by (cases "x = 0") (simp_all add: collinear_2 insert_commute)
  }
  moreover
  {
    assume x: "x \<noteq> 0" and y: "y \<noteq> 0"
    have ?thesis
    proof
      assume h: "?lhs"
      then obtain u where u: "\<forall> x\<in> {0,x,y}. \<forall>y\<in> {0,x,y}. \<exists>c. x - y = c *\<^sub>R u"
        unfolding collinear_def by blast
      from u[rule_format, of x 0] u[rule_format, of y 0]
      obtain cx and cy where
        cx: "x = cx *\<^sub>R u" and cy: "y = cy *\<^sub>R u"
        by auto
      from cx x have cx0: "cx \<noteq> 0" by auto
      from cy y have cy0: "cy \<noteq> 0" by auto
      let ?d = "cy / cx"
      from cx cy cx0 have "y = ?d *\<^sub>R x"
        by simp
      then show ?rhs using x y by blast
    next
      assume h: "?rhs"
      then obtain c where c: "y = c *\<^sub>R x"
        using x y by blast
      show ?lhs
        unfolding collinear_def c
        apply (rule exI[where x=x])
        apply auto
        apply (rule exI[where x="- 1"], simp)
        apply (rule exI[where x= "-c"], simp)
        apply (rule exI[where x=1], simp)
        apply (rule exI[where x="1 - c"], simp add: scaleR_left_diff_distrib)
        apply (rule exI[where x="c - 1"], simp add: scaleR_left_diff_distrib)
        done
    qed
  }
  ultimately show ?thesis by blast
qed

lemma norm_cauchy_schwarz_equal: "\<bar>x \<bullet> y\<bar> = norm x * norm y \<longleftrightarrow> collinear {0, x, y}"
  unfolding norm_cauchy_schwarz_abs_eq
  apply (cases "x=0", simp_all)
  apply (cases "y=0", simp_all add: insert_commute)
  unfolding collinear_lemma
  apply simp
  apply (subgoal_tac "norm x \<noteq> 0")
  apply (subgoal_tac "norm y \<noteq> 0")
  apply (rule iffI)
  apply (cases "norm x *\<^sub>R y = norm y *\<^sub>R x")
  apply (rule exI[where x="(1/norm x) * norm y"])
  apply (drule sym)
  unfolding scaleR_scaleR[symmetric]
  apply (simp add: field_simps)
  apply (rule exI[where x="(1/norm x) * - norm y"])
  apply clarify
  apply (drule sym)
  unfolding scaleR_scaleR[symmetric]
  apply (simp add: field_simps)
  apply (erule exE)
  apply (erule ssubst)
  unfolding scaleR_scaleR
  unfolding norm_scaleR
  apply (subgoal_tac "norm x * c = \<bar>c\<bar> * norm x \<or> norm x * c = - \<bar>c\<bar> * norm x")
  apply (auto simp add: field_simps)
  done

end
