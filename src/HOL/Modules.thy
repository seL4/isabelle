(*  Title:      HOL/Modules.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Author:     Johannes Hölzl, VU Amsterdam
    Author:     Fabian Immler, TUM
*)

section \<open>Modules\<close>

text \<open>Bases of a linear algebra based on modules (i.e. vector spaces of rings). \<close>

theory Modules
  imports Hull
begin

subsection \<open>Locale for additive functions\<close>

locale additive =
  fixes f :: "'a::ab_group_add \<Rightarrow> 'b::ab_group_add"
  assumes add: "f (x + y) = f x + f y"
begin

lemma zero: "f 0 = 0"
proof -
  have "f 0 = f (0 + 0)" by simp
  also have "\<dots> = f 0 + f 0" by (rule add)
  finally show "f 0 = 0" by simp
qed

lemma minus: "f (- x) = - f x"
proof -
  have "f (- x) + f x = f (- x + x)" by (rule add [symmetric])
  also have "\<dots> = - f x + f x" by (simp add: zero)
  finally show "f (- x) = - f x" by (rule add_right_imp_eq)
qed

lemma diff: "f (x - y) = f x - f y"
  using add [of x "- y"] by (simp add: minus)

lemma sum: "f (sum g A) = (\<Sum>x\<in>A. f (g x))"
  by (induct A rule: infinite_finite_induct) (simp_all add: zero add)

end


text \<open>Modules form the central spaces in linear algebra. They are a generalization from vector
spaces by replacing the scalar field by a scalar ring.\<close>
locale module =
  fixes scale :: "'a::comm_ring_1 \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr \<open>*s\<close> 75)
  assumes scale_right_distrib [algebra_simps, algebra_split_simps]:
      "a *s (x + y) = a *s x + a *s y"
    and scale_left_distrib [algebra_simps, algebra_split_simps]:
      "(a + b) *s x = a *s x + b *s x"
    and scale_scale [simp]: "a *s (b *s x) = (a * b) *s x"
    and scale_one [simp]: "1 *s x = x"
begin

lemma scale_left_commute: "a *s (b *s x) = b *s (a *s x)"
  by (simp add: mult.commute)

lemma scale_zero_left [simp]: "0 *s x = 0"
  and scale_minus_left [simp]: "(- a) *s x = - (a *s x)"
  and scale_left_diff_distrib [algebra_simps, algebra_split_simps]:
    "(a - b) *s x = a *s x - b *s x"
  and scale_sum_left: "(sum f A) *s x = (\<Sum>a\<in>A. (f a) *s x)"
proof -
  interpret s: additive "\<lambda>a. a *s x"
    by standard (rule scale_left_distrib)
  show "0 *s x = 0" by (rule s.zero)
  show "(- a) *s x = - (a *s x)" by (rule s.minus)
  show "(a - b) *s x = a *s x - b *s x" by (rule s.diff)
  show "(sum f A) *s x = (\<Sum>a\<in>A. (f a) *s x)" by (rule s.sum)
qed

lemma scale_zero_right [simp]: "a *s 0 = 0"
  and scale_minus_right [simp]: "a *s (- x) = - (a *s x)"
  and scale_right_diff_distrib [algebra_simps, algebra_split_simps]: 
    "a *s (x - y) = a *s x - a *s y"
  and scale_sum_right: "a *s (sum f A) = (\<Sum>x\<in>A. a *s (f x))"
proof -
  interpret s: additive "\<lambda>x. a *s x"
    by standard (rule scale_right_distrib)
  show "a *s 0 = 0" by (rule s.zero)
  show "a *s (- x) = - (a *s x)" by (rule s.minus)
  show "a *s (x - y) = a *s x - a *s y" by (rule s.diff)
  show "a *s (sum f A) = (\<Sum>x\<in>A. a *s (f x))" by (rule s.sum)
qed

lemma sum_constant_scale: "(\<Sum>x\<in>A. y) = scale (of_nat (card A)) y"
  by (induct A rule: infinite_finite_induct) (simp_all add: algebra_simps)

end

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>divide\<close>, SOME \<^typ>\<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>)\<close>

context module
begin

lemma [field_simps, field_split_simps]:
  shows scale_left_distrib_NO_MATCH: "NO_MATCH (x div y) c \<Longrightarrow> (a + b) *s x = a *s x + b *s x"
    and scale_right_distrib_NO_MATCH: "NO_MATCH (x div y) a \<Longrightarrow> a *s (x + y) = a *s x + a *s y"
    and scale_left_diff_distrib_NO_MATCH: "NO_MATCH (x div y) c \<Longrightarrow> (a - b) *s x = a *s x - b *s x"
    and scale_right_diff_distrib_NO_MATCH: "NO_MATCH (x div y) a \<Longrightarrow> a *s (x - y) = a *s x - a *s y"
  by (rule scale_left_distrib scale_right_distrib scale_left_diff_distrib scale_right_diff_distrib)+

end

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>divide\<close>, SOME \<^typ>\<open>'a::divide \<Rightarrow> 'a \<Rightarrow> 'a\<close>)\<close>


section \<open>Subspace\<close>

context module
begin

definition subspace :: "'b set \<Rightarrow> bool"
  where "subspace S \<longleftrightarrow> 0 \<in> S \<and> (\<forall>x\<in>S. \<forall>y\<in>S. x + y \<in> S) \<and> (\<forall>c. \<forall>x\<in>S. c *s x \<in> S)"

lemma subspaceI:
  "0 \<in> S \<Longrightarrow> (\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x + y \<in> S) \<Longrightarrow> (\<And>c x. x \<in> S \<Longrightarrow> c *s x \<in> S) \<Longrightarrow> subspace S"
  by (auto simp: subspace_def)

lemma subspace_UNIV[simp]: "subspace UNIV"
  by (simp add: subspace_def)

lemma subspace_single_0[simp]: "subspace {0}"
  by (simp add: subspace_def)

lemma subspace_0: "subspace S \<Longrightarrow> 0 \<in> S"
  by (metis subspace_def)

lemma subspace_add: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x + y \<in> S"
  by (metis subspace_def)

lemma subspace_scale: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> c *s x \<in> S"
  by (metis subspace_def)

lemma subspace_neg: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> - x \<in> S"
  by (metis scale_minus_left scale_one subspace_scale)

lemma subspace_diff: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x - y \<in> S"
  by (metis diff_conv_add_uminus subspace_add subspace_neg)

lemma subspace_sum: "subspace A \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> f x \<in> A) \<Longrightarrow> sum f B \<in> A"
  by (induct B rule: infinite_finite_induct) (auto simp add: subspace_add subspace_0)

lemma subspace_Int: "(\<And>i. i \<in> I \<Longrightarrow> subspace (s i)) \<Longrightarrow> subspace (\<Inter>i\<in>I. s i)"
  by (auto simp: subspace_def)

lemma subspace_Inter: "\<forall>s \<in> f. subspace s \<Longrightarrow> subspace (\<Inter>f)"
  unfolding subspace_def by auto

lemma subspace_inter: "subspace A \<Longrightarrow> subspace B \<Longrightarrow> subspace (A \<inter> B)"
  by (simp add: subspace_def)


section \<open>Span: subspace generated by a set\<close>

definition span :: "'b set \<Rightarrow> 'b set"
  where span_explicit: "span b = {(\<Sum>a\<in>t. r a *s  a) | t r. finite t \<and> t \<subseteq> b}"

lemma span_explicit':
  "span b = {(\<Sum>v | f v \<noteq> 0. f v *s v) | f. finite {v. f v \<noteq> 0} \<and> (\<forall>v. f v \<noteq> 0 \<longrightarrow> v \<in> b)}"
  unfolding span_explicit
proof safe
  fix t r assume "finite t" "t \<subseteq> b"
  then show "\<exists>f. (\<Sum>a\<in>t. r a *s a) = (\<Sum>v | f v \<noteq> 0. f v *s v) \<and> finite {v. f v \<noteq> 0} \<and> (\<forall>v. f v \<noteq> 0 \<longrightarrow> v \<in> b)"
    by (intro exI[of _ "\<lambda>v. if v \<in> t then r v else 0"]) (auto intro!: sum.mono_neutral_cong_right)
next
  fix f :: "'b \<Rightarrow> 'a" assume "finite {v. f v \<noteq> 0}" "(\<forall>v. f v \<noteq> 0 \<longrightarrow> v \<in> b)"
  then show "\<exists>t r. (\<Sum>v | f v \<noteq> 0. f v *s v) = (\<Sum>a\<in>t. r a *s a) \<and> finite t \<and> t \<subseteq> b"
    by (intro exI[of _ "{v. f v \<noteq> 0}"] exI[of _ f]) auto
qed

lemma span_alt:
  "span B = {(\<Sum>x | f x \<noteq> 0. f x *s x) | f. {x. f x \<noteq> 0} \<subseteq> B \<and> finite {x. f x \<noteq> 0}}"
  unfolding span_explicit' by auto

lemma span_finite:
  assumes fS: "finite S"
  shows "span S = range (\<lambda>u. \<Sum>v\<in>S. u v *s v)"
  unfolding span_explicit
proof safe
  fix t r assume "t \<subseteq> S" then show "(\<Sum>a\<in>t. r a *s a) \<in> range (\<lambda>u. \<Sum>v\<in>S. u v *s v)"
    by (intro image_eqI[of _ _ "\<lambda>a. if a \<in> t then r a else 0"])
       (auto simp: if_distrib[of "\<lambda>r. r *s a" for a] sum.If_cases fS Int_absorb1)
next
  show "\<exists>t r. (\<Sum>v\<in>S. u v *s v) = (\<Sum>a\<in>t. r a *s a) \<and> finite t \<and> t \<subseteq> S" for u
    by (intro exI[of _ u] exI[of _ S]) (auto intro: fS)
qed

lemma span_induct_alt [consumes 1, case_names base step, induct set: span]:
  assumes x: "x \<in> span S"
  assumes h0: "h 0" and hS: "\<And>c x y. x \<in> S \<Longrightarrow> h y \<Longrightarrow> h (c *s x + y)"
  shows "h x"
  using x unfolding span_explicit
proof safe
  fix t r assume "finite t" "t \<subseteq> S" then show "h (\<Sum>a\<in>t. r a *s a)"
    by (induction t) (auto intro!: hS h0)
qed

lemma span_mono: "A \<subseteq> B \<Longrightarrow> span A \<subseteq> span B"
  by (auto simp: span_explicit)

lemma span_base: "a \<in> S \<Longrightarrow> a \<in> span S"
  by (auto simp: span_explicit intro!: exI[of _ "{a}"] exI[of _ "\<lambda>_. 1"])

lemma span_superset: "S \<subseteq> span S"
  by (auto simp: span_base)

lemma span_zero: "0 \<in> span S"
  by (auto simp: span_explicit intro!: exI[of _ "{}"])

lemma span_UNIV[simp]: "span UNIV = UNIV"
  by (auto intro: span_base)

lemma span_add: "x \<in> span S \<Longrightarrow> y \<in> span S \<Longrightarrow> x + y \<in> span S"
  unfolding span_explicit
proof safe
  fix tx ty rx ry assume *: "finite tx" "finite ty" "tx \<subseteq> S" "ty \<subseteq> S"
  have [simp]: "(tx \<union> ty) \<inter> tx = tx" "(tx \<union> ty) \<inter> ty = ty"
    by auto
  show "\<exists>t r. (\<Sum>a\<in>tx. rx a *s a) + (\<Sum>a\<in>ty. ry a *s a) = (\<Sum>a\<in>t. r a *s a) \<and> finite t \<and> t \<subseteq> S"
    apply (intro exI[of _ "tx \<union> ty"])
    apply (intro exI[of _ "\<lambda>a. (if a \<in> tx then rx a else 0) + (if a \<in> ty then ry a else 0)"])
    apply (auto simp: * scale_left_distrib sum.distrib if_distrib[of "\<lambda>r. r *s a" for a] sum.If_cases)
    done
qed

lemma span_scale: "x \<in> span S \<Longrightarrow> c *s x \<in> span S"
  unfolding span_explicit
proof safe
  fix t r assume *: "finite t" "t \<subseteq> S"
  show "\<exists>t' r'. c *s (\<Sum>a\<in>t. r a *s a) = (\<Sum>a\<in>t'. r' a *s a) \<and> finite t' \<and> t' \<subseteq> S"
    by (intro exI[of _ t] exI[of _ "\<lambda>a. c * r a"]) (auto simp: * scale_sum_right)
qed

lemma subspace_span [iff]: "subspace (span S)"
  by (auto simp: subspace_def span_zero span_add span_scale)

lemma span_neg: "x \<in> span S \<Longrightarrow> - x \<in> span S"
  by (metis subspace_neg subspace_span)

lemma span_diff: "x \<in> span S \<Longrightarrow> y \<in> span S \<Longrightarrow> x - y \<in> span S"
  by (metis subspace_span subspace_diff)

lemma span_sum: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> span S) \<Longrightarrow> sum f A \<in> span S"
  by (rule subspace_sum, rule subspace_span)

lemma span_minimal: "S \<subseteq> T \<Longrightarrow> subspace T \<Longrightarrow> span S \<subseteq> T"
  by (auto simp: span_explicit intro!: subspace_sum subspace_scale)

lemma span_def: "span S = subspace hull S" 
  by (intro hull_unique[symmetric] span_superset subspace_span span_minimal)

lemma span_unique:
  "S \<subseteq> T \<Longrightarrow> subspace T \<Longrightarrow> (\<And>T'. S \<subseteq> T' \<Longrightarrow> subspace T' \<Longrightarrow> T \<subseteq> T') \<Longrightarrow> span S = T"
  unfolding span_def by (rule hull_unique)

lemma span_subspace_induct[consumes 2]:
  assumes x: "x \<in> span S"
    and P: "subspace P"
    and SP: "\<And>x. x \<in> S \<Longrightarrow> x \<in> P"
  shows "x \<in> P"
proof -
  from SP have SP': "S \<subseteq> P"
    by (simp add: subset_eq)
  from x hull_minimal[where S=subspace, OF SP' P, unfolded span_def[symmetric]]
  show "x \<in> P"
    by (metis subset_eq)
qed

lemma (in module) span_induct[consumes 1, case_names base step, induct set: span]:
  assumes x: "x \<in> span S"
    and P: "subspace (Collect P)"
    and SP: "\<And>x. x \<in> S \<Longrightarrow> P x"
  shows "P x"
  using P SP span_subspace_induct x by fastforce

lemma span_empty[simp]: "span {} = {0}"
  by (rule span_unique) (auto simp add: subspace_def)

lemma span_subspace: "A \<subseteq> B \<Longrightarrow> B \<subseteq> span A \<Longrightarrow> subspace B \<Longrightarrow> span A = B"
  by (metis order_antisym span_def hull_minimal)

lemma span_span: "span (span A) = span A"
  unfolding span_def hull_hull ..

(* TODO: proof generally for subspace: *)
lemma span_add_eq: assumes x: "x \<in> span S" shows "x + y \<in> span S \<longleftrightarrow> y \<in> span S"
proof
  assume *: "x + y \<in> span S"
  have "(x + y) - x \<in> span S" using * x by (rule span_diff)
  then show "y \<in> span S" by simp
qed (intro span_add x)

lemma span_add_eq2: assumes y: "y \<in> span S" shows "x + y \<in> span S \<longleftrightarrow> x \<in> span S"
  using span_add_eq[of y S x] y by (auto simp: ac_simps)

lemma span_singleton: "span {x} = range (\<lambda>k. k *s x)"
  by (auto simp: span_finite)

lemma span_Un: "span (S \<union> T) = {x + y | x y. x \<in> span S \<and> y \<in> span T}"
proof safe
  fix x assume "x \<in> span (S \<union> T)"
  then obtain t r where t: "finite t" "t \<subseteq> S \<union> T" and x: "x = (\<Sum>a\<in>t. r a *s a)"
    by (auto simp: span_explicit)
  moreover have "t \<inter> S \<union> (t - S) = t" by auto
  ultimately show "\<exists>xa y. x = xa + y \<and> xa \<in> span S \<and> y \<in> span T"
    unfolding x
    apply (rule_tac exI[of _ "\<Sum>a\<in>t \<inter> S. r a *s a"])
    apply (rule_tac exI[of _ "\<Sum>a\<in>t - S. r a *s a"])
    apply (subst sum.union_inter_neutral[symmetric])
    apply (auto intro!: span_sum span_scale intro: span_base)
    done
next
  fix x y assume"x \<in> span S" "y \<in> span T" then show "x + y \<in> span (S \<union> T)"
    using span_mono[of S "S \<union> T"] span_mono[of T "S \<union> T"]
    by (auto intro!: span_add)
qed

lemma span_insert: "span (insert a S) = {x. \<exists>k. (x - k *s a) \<in> span S}"
proof -
  have "span ({a} \<union> S) = {x. \<exists>k. (x - k *s a) \<in> span S}"
    unfolding span_Un span_singleton
    apply (auto simp add: set_eq_iff)
    subgoal for y k by (auto intro!: exI[of _ "k"])
    subgoal for y k by (rule exI[of _ "k *s a"], rule exI[of _ "y - k *s a"]) auto
    done
  then show ?thesis by simp
qed

lemma span_breakdown:
  assumes bS: "b \<in> S"
    and aS: "a \<in> span S"
  shows "\<exists>k. a - k *s b \<in> span (S - {b})"
  using assms span_insert [of b "S - {b}"]
  by (simp add: insert_absorb)

lemma span_breakdown_eq: "x \<in> span (insert a S) \<longleftrightarrow> (\<exists>k. x - k *s a \<in> span S)"
  by (simp add: span_insert)

lemmas span_clauses = span_base span_zero span_add span_scale

lemma span_eq_iff[simp]: "span s = s \<longleftrightarrow> subspace s"
  unfolding span_def by (rule hull_eq) (rule subspace_Inter)

lemma span_eq: "span S = span T \<longleftrightarrow> S \<subseteq> span T \<and> T \<subseteq> span S"
  by (metis span_minimal span_subspace span_superset subspace_span)

lemma eq_span_insert_eq:
  assumes "(x - y) \<in> span S"
    shows "span(insert x S) = span(insert y S)"
proof -
  have *: "span(insert x S) \<subseteq> span(insert y S)" if "(x - y) \<in> span S" for x y
  proof -
    have 1: "(r *s x - r *s y) \<in> span S" for r
      by (metis scale_right_diff_distrib span_scale that)
    have 2: "(z - k *s y) - k *s (x - y) = z - k *s x" for  z k
      by (simp add: scale_right_diff_distrib)
  show ?thesis
    apply (clarsimp simp add: span_breakdown_eq)
    by (metis 1 2 diff_add_cancel scale_right_diff_distrib span_add_eq)
  qed
  show ?thesis
    apply (intro subset_antisym * assms)
    using assms subspace_neg subspace_span minus_diff_eq by force
qed


section \<open>Dependent and independent sets\<close>

definition dependent :: "'b set \<Rightarrow> bool"
  where dependent_explicit: "dependent s \<longleftrightarrow> (\<exists>t u. finite t \<and> t \<subseteq> s \<and> (\<Sum>v\<in>t. u v *s v) = 0 \<and> (\<exists>v\<in>t. u v \<noteq> 0))"

abbreviation "independent s \<equiv> \<not> dependent s"

lemma dependent_mono: "dependent B \<Longrightarrow> B \<subseteq> A \<Longrightarrow> dependent A"
  by (auto simp add: dependent_explicit)

lemma independent_mono: "independent A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> independent B"
  by (auto intro: dependent_mono)

lemma dependent_zero: "0 \<in> A \<Longrightarrow> dependent A"
  by (auto simp: dependent_explicit intro!: exI[of _ "\<lambda>i. 1"] exI[of _ "{0}"])

lemma independent_empty[intro]: "independent {}"
  by (simp add: dependent_explicit)

lemma independent_explicit_module:
  "independent s \<longleftrightarrow> (\<forall>t u v. finite t \<longrightarrow> t \<subseteq> s \<longrightarrow> (\<Sum>v\<in>t. u v *s v) = 0 \<longrightarrow> v \<in> t \<longrightarrow> u v = 0)"
  unfolding dependent_explicit by auto

lemma independentD: "independent s \<Longrightarrow> finite t \<Longrightarrow> t \<subseteq> s \<Longrightarrow> (\<Sum>v\<in>t. u v *s v) = 0 \<Longrightarrow> v \<in> t \<Longrightarrow> u v = 0"
  by (simp add: independent_explicit_module)

lemma independent_Union_directed:
  assumes directed: "\<And>c d. c \<in> C \<Longrightarrow> d \<in> C \<Longrightarrow> c \<subseteq> d \<or> d \<subseteq> c"
  assumes indep: "\<And>c. c \<in> C \<Longrightarrow> independent c"
  shows "independent (\<Union>C)"
proof
  assume "dependent (\<Union>C)"
  then obtain u v S where S: "finite S" "S \<subseteq> \<Union>C" "v \<in> S" "u v \<noteq> 0" "(\<Sum>v\<in>S. u v *s v) = 0"
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

lemma dependent_finite:
  assumes "finite S"
  shows "dependent S \<longleftrightarrow> (\<exists>u. (\<exists>v \<in> S. u v \<noteq> 0) \<and> (\<Sum>v\<in>S. u v *s v) = 0)"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain T u v
    where "finite T" "T \<subseteq> S" "v\<in>T" "u v \<noteq> 0" "(\<Sum>v\<in>T. u v *s v) = 0"
    by (force simp: dependent_explicit)
  with assms show ?rhs
    apply (rule_tac x="\<lambda>v. if v \<in> T then u v else 0" in exI)
    apply (auto simp: sum.mono_neutral_right)
    done
next
  assume ?rhs  with assms show ?lhs
    by (fastforce simp add: dependent_explicit)
qed

lemma dependent_alt:
  "dependent B \<longleftrightarrow>
    (\<exists>X. finite {x. X x \<noteq> 0} \<and> {x. X x \<noteq> 0} \<subseteq> B \<and> (\<Sum>x|X x \<noteq> 0. X x *s x) = 0 \<and> (\<exists>x. X x \<noteq> 0))"
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
    (\<forall>X. finite {x. X x \<noteq> 0} \<longrightarrow> {x. X x \<noteq> 0} \<subseteq> B \<longrightarrow> (\<Sum>x|X x \<noteq> 0. X x *s x) = 0 \<longrightarrow> (\<forall>x. X x = 0))"
  unfolding dependent_alt by auto

lemma independentD_alt:
  "independent B \<Longrightarrow> finite {x. X x \<noteq> 0} \<Longrightarrow> {x. X x \<noteq> 0} \<subseteq> B \<Longrightarrow> (\<Sum>x|X x \<noteq> 0. X x *s x) = 0 \<Longrightarrow> X x = 0"
  unfolding independent_alt by blast

lemma independentD_unique:
  assumes B: "independent B"
    and X: "finite {x. X x \<noteq> 0}" "{x. X x \<noteq> 0} \<subseteq> B"
    and Y: "finite {x. Y x \<noteq> 0}" "{x. Y x \<noteq> 0} \<subseteq> B"
    and "(\<Sum>x | X x \<noteq> 0. X x *s x) = (\<Sum>x| Y x \<noteq> 0. Y x *s x)"
  shows "X = Y"
proof -
  have "X x - Y x = 0" for x
    using B
  proof (rule independentD_alt)
    have "{x. X x - Y x \<noteq> 0} \<subseteq> {x. X x \<noteq> 0} \<union> {x. Y x \<noteq> 0}"
      by auto
    then show "finite {x. X x - Y x \<noteq> 0}" "{x. X x - Y x \<noteq> 0} \<subseteq> B"
      using X Y by (auto dest: finite_subset)
    then have "(\<Sum>x | X x - Y x \<noteq> 0. (X x - Y x) *s x) = (\<Sum>v\<in>{S. X S \<noteq> 0} \<union> {S. Y S \<noteq> 0}. (X v - Y v) *s v)"
      using X Y by (intro sum.mono_neutral_cong_left) auto
    also have "\<dots> = (\<Sum>v\<in>{S. X S \<noteq> 0} \<union> {S. Y S \<noteq> 0}. X v *s v) - (\<Sum>v\<in>{S. X S \<noteq> 0} \<union> {S. Y S \<noteq> 0}. Y v *s v)"
      by (simp add: scale_left_diff_distrib sum_subtractf assms)
    also have "(\<Sum>v\<in>{S. X S \<noteq> 0} \<union> {S. Y S \<noteq> 0}. X v *s v) = (\<Sum>v\<in>{S. X S \<noteq> 0}. X v *s v)"
      using X Y by (intro sum.mono_neutral_cong_right) auto
    also have "(\<Sum>v\<in>{S. X S \<noteq> 0} \<union> {S. Y S \<noteq> 0}. Y v *s v) = (\<Sum>v\<in>{S. Y S \<noteq> 0}. Y v *s v)"
      using X Y by (intro sum.mono_neutral_cong_right) auto
    finally show "(\<Sum>x | X x - Y x \<noteq> 0. (X x - Y x) *s x) = 0"
      using assms by simp
  qed
  then show ?thesis
    by auto
qed


section \<open>Representation of a vector on a specific basis\<close>

definition representation :: "'b set \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'a"
  where "representation basis v =
    (if independent basis \<and> v \<in> span basis then
      SOME f. (\<forall>v. f v \<noteq> 0 \<longrightarrow> v \<in> basis) \<and> finite {v. f v \<noteq> 0} \<and> (\<Sum>v\<in>{v. f v \<noteq> 0}. f v *s v) = v
    else (\<lambda>b. 0))"

lemma unique_representation:
  assumes basis: "independent basis"
    and in_basis: "\<And>v. f v \<noteq> 0 \<Longrightarrow> v \<in> basis" "\<And>v. g v \<noteq> 0 \<Longrightarrow> v \<in> basis"
    and [simp]: "finite {v. f v \<noteq> 0}" "finite {v. g v \<noteq> 0}"
    and eq: "(\<Sum>v\<in>{v. f v \<noteq> 0}. f v *s v) = (\<Sum>v\<in>{v. g v \<noteq> 0}. g v *s v)"
  shows "f = g"
proof (rule ext, rule ccontr)
  fix v assume ne: "f v \<noteq> g v"
  have "dependent basis"
    unfolding dependent_explicit
  proof (intro exI conjI)
    have *: "{v. f v - g v \<noteq> 0} \<subseteq> {v. f v \<noteq> 0} \<union> {v. g v \<noteq> 0}"
      by auto
    show "finite {v. f v - g v \<noteq> 0}"
      by (rule finite_subset[OF *]) simp
    show "\<exists>v\<in>{v. f v - g v \<noteq> 0}. f v - g v \<noteq> 0"
      by (rule bexI[of _ v]) (auto simp: ne)
    have "(\<Sum>v | f v - g v \<noteq> 0. (f v - g v) *s v) = 
        (\<Sum>v\<in>{v. f v \<noteq> 0} \<union> {v. g v \<noteq> 0}. (f v - g v) *s v)"
      by (intro sum.mono_neutral_cong_left *) auto
    also have "... =
        (\<Sum>v\<in>{v. f v \<noteq> 0} \<union> {v. g v \<noteq> 0}. f v *s v) - (\<Sum>v\<in>{v. f v \<noteq> 0} \<union> {v. g v \<noteq> 0}. g v *s v)"
      by (simp add: algebra_simps sum_subtractf)
    also have "... = (\<Sum>v | f v \<noteq> 0. f v *s v) - (\<Sum>v | g v \<noteq> 0. g v *s v)"
      by (intro arg_cong2[where f= "(-)"] sum.mono_neutral_cong_right) auto
    finally show "(\<Sum>v | f v - g v \<noteq> 0. (f v - g v) *s v) = 0"
      by (simp add: eq)
    show "{v. f v - g v \<noteq> 0} \<subseteq> basis"
      using in_basis * by auto
  qed
  with basis show False by auto
qed

lemma
  shows representation_ne_zero: "\<And>b. representation basis v b \<noteq> 0 \<Longrightarrow> b \<in> basis"
    and finite_representation: "finite {b. representation basis v b \<noteq> 0}"
    and sum_nonzero_representation_eq:
      "independent basis \<Longrightarrow> v \<in> span basis \<Longrightarrow> (\<Sum>b | representation basis v b \<noteq> 0. representation basis v b *s b) = v"
proof -
  { assume basis: "independent basis" and v: "v \<in> span basis"
    define p where "p f \<longleftrightarrow>
      (\<forall>v. f v \<noteq> 0 \<longrightarrow> v \<in> basis) \<and> finite {v. f v \<noteq> 0} \<and> (\<Sum>v\<in>{v. f v \<noteq> 0}. f v *s v) = v" for f
    obtain t r where *: "finite t" "t \<subseteq> basis" "(\<Sum>b\<in>t. r b *s b) = v"
      using \<open>v \<in> span basis\<close> by (auto simp: span_explicit)
    define f where "f b = (if b \<in> t then r b else 0)" for b
    have "p f"
      using * by (auto simp: p_def f_def intro!: sum.mono_neutral_cong_left)
    have *: "representation basis v = Eps p" by (simp add: p_def[abs_def] representation_def basis v)
    from someI[of p f, OF \<open>p f\<close>] have "p (representation basis v)"
      unfolding * . }
  note * = this

  show "representation basis v b \<noteq> 0 \<Longrightarrow> b \<in> basis" for b
    using * by (cases "independent basis \<and> v \<in> span basis") (auto simp: representation_def)

  show "finite {b. representation basis v b \<noteq> 0}"
    using * by (cases "independent basis \<and> v \<in> span basis") (auto simp: representation_def)

  show "independent basis \<Longrightarrow> v \<in> span basis \<Longrightarrow> (\<Sum>b | representation basis v b \<noteq> 0. representation basis v b *s b) = v"
    using * by auto
qed

lemma sum_representation_eq:
  "(\<Sum>b\<in>B. representation basis v b *s b) = v"
  if "independent basis" "v \<in> span basis" "finite B" "basis \<subseteq> B"
proof -
  have "(\<Sum>b\<in>B. representation basis v b *s b) =
      (\<Sum>b | representation basis v b \<noteq> 0. representation basis v b *s b)"
    apply (rule sum.mono_neutral_cong)
        apply (rule finite_representation)
       apply fact
    subgoal for b
      using that representation_ne_zero[of basis v b]
      by auto
    subgoal by auto
    subgoal by simp
    done
  also have "\<dots> = v"
    by (rule sum_nonzero_representation_eq; fact)
  finally show ?thesis .
qed

lemma representation_eqI:
  assumes basis: "independent basis" and b: "v \<in> span basis"
    and ne_zero: "\<And>b. f b \<noteq> 0 \<Longrightarrow> b \<in> basis"
    and finite: "finite {b. f b \<noteq> 0}"
    and eq: "(\<Sum>b | f b \<noteq> 0. f b *s b) = v"
  shows "representation basis v = f"
  by (rule unique_representation[OF basis])
     (auto simp: representation_ne_zero finite_representation
       sum_nonzero_representation_eq[OF basis b] ne_zero finite eq)

lemma representation_basis:
  assumes basis: "independent basis" and b: "b \<in> basis"
  shows "representation basis b = (\<lambda>v. if v = b then 1 else 0)"
proof (rule unique_representation[OF basis])
  show "representation basis b v \<noteq> 0 \<Longrightarrow> v \<in> basis" for v
    using representation_ne_zero .
  show "finite {v. representation basis b v \<noteq> 0}"
    using finite_representation .
  show "(if v = b then 1 else 0) \<noteq> 0 \<Longrightarrow> v \<in> basis" for v
    by (cases "v = b") (auto simp: b)
  have *: "{v. (if v = b then 1 else 0 :: 'a) \<noteq> 0} = {b}"
    by auto
  show "finite {v. (if v = b then 1 else 0) \<noteq> 0}" unfolding * by auto
  show "(\<Sum>v | representation basis b v \<noteq> 0. representation basis b v *s v) =
    (\<Sum>v | (if v = b then 1 else 0::'a) \<noteq> 0. (if v = b then 1 else 0) *s v)"
    unfolding * sum_nonzero_representation_eq[OF basis span_base[OF b]] by auto
qed

lemma representation_zero: "representation basis 0 = (\<lambda>b. 0)"
proof cases
  assume basis: "independent basis" show ?thesis
    by (rule representation_eqI[OF basis span_zero]) auto
qed (simp add: representation_def)

lemma representation_diff:
  assumes basis: "independent basis" and v: "v \<in> span basis" and u: "u \<in> span basis"
  shows "representation basis (u - v) = (\<lambda>b. representation basis u b - representation basis v b)"
proof (rule representation_eqI[OF basis span_diff[OF u v]])
  let ?R = "representation basis"
  note finite_representation[simp] u[simp] v[simp]
  have *: "{b. ?R u b - ?R v b \<noteq> 0} \<subseteq> {b. ?R u b \<noteq> 0} \<union> {b. ?R v b \<noteq> 0}"
    by auto
  then show "?R u b - ?R v b \<noteq> 0 \<Longrightarrow> b \<in> basis" for b
    by (auto dest: representation_ne_zero)
  show "finite {b. ?R u b - ?R v b \<noteq> 0}"
    by (intro finite_subset[OF *]) simp_all
  have "(\<Sum>b | ?R u b - ?R v b \<noteq> 0. (?R u b - ?R v b) *s b) =
      (\<Sum>b\<in>{b. ?R u b \<noteq> 0} \<union> {b. ?R v b \<noteq> 0}. (?R u b - ?R v b) *s b)"
    by (intro sum.mono_neutral_cong_left *) auto
  also have "... =
      (\<Sum>b\<in>{b. ?R u b \<noteq> 0} \<union> {b. ?R v b \<noteq> 0}. ?R u b *s b) - (\<Sum>b\<in>{b. ?R u b \<noteq> 0} \<union> {b. ?R v b \<noteq> 0}. ?R v b *s b)"
    by (simp add: algebra_simps sum_subtractf)
  also have "... = (\<Sum>b | ?R u b \<noteq> 0. ?R u b *s b) - (\<Sum>b | ?R v b \<noteq> 0. ?R v b *s b)"
    by (intro arg_cong2[where f= "(-)"] sum.mono_neutral_cong_right) auto
  finally show "(\<Sum>b | ?R u b - ?R v b \<noteq> 0. (?R u b - ?R v b) *s b) = u - v"
    by (simp add: sum_nonzero_representation_eq[OF basis])
qed

lemma representation_neg:
  "independent basis \<Longrightarrow> v \<in> span basis \<Longrightarrow> representation basis (- v) = (\<lambda>b. - representation basis v b)"
  using representation_diff[of basis v 0] by (simp add: representation_zero span_zero)

lemma representation_add:
  "independent basis \<Longrightarrow> v \<in> span basis \<Longrightarrow> u \<in> span basis \<Longrightarrow>
    representation basis (u + v) = (\<lambda>b. representation basis u b + representation basis v b)"
  using representation_diff[of basis "-v" u] by (simp add: representation_neg representation_diff span_neg)

lemma representation_sum:
  "independent basis \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> v i \<in> span basis) \<Longrightarrow>
    representation basis (sum v I) = (\<lambda>b. \<Sum>i\<in>I. representation basis (v i) b)"
  by (induction I rule: infinite_finite_induct)
     (auto simp: representation_zero representation_add span_sum)

lemma representation_scale:
  assumes basis: "independent basis" and v: "v \<in> span basis"
  shows "representation basis (r *s v) = (\<lambda>b. r * representation basis v b)"
proof (rule representation_eqI[OF basis span_scale[OF v]])
  let ?R = "representation basis"
  note finite_representation[simp] v[simp]
  have *: "{b. r * ?R v b \<noteq> 0} \<subseteq> {b. ?R v b \<noteq> 0}"
    by auto
  then show "r * representation basis v b \<noteq> 0 \<Longrightarrow> b \<in> basis" for b
    using representation_ne_zero by auto
  show "finite {b. r * ?R v b \<noteq> 0}"
    by (intro finite_subset[OF *]) simp_all
  have "(\<Sum>b | r * ?R v b \<noteq> 0. (r * ?R v b) *s b) = (\<Sum>b\<in>{b. ?R v b \<noteq> 0}. (r * ?R v b) *s b)"
    by (intro sum.mono_neutral_cong_left *) auto
  also have "... = r *s (\<Sum>b | ?R v b \<noteq> 0. ?R v b *s b)"
    by (simp add: scale_scale[symmetric] scale_sum_right del: scale_scale)
  finally show "(\<Sum>b | r * ?R v b \<noteq> 0. (r * ?R v b) *s b) = r *s v"
    by (simp add: sum_nonzero_representation_eq[OF basis])
qed

lemma representation_extend:
  assumes basis: "independent basis" and v: "v \<in> span basis'" and basis': "basis' \<subseteq> basis"
  shows "representation basis v = representation basis' v"
proof (rule representation_eqI[OF basis])
  show v': "v \<in> span basis" using span_mono[OF basis'] v by auto
  have *: "independent basis'" using basis' basis by (auto intro: dependent_mono)
  show "representation basis' v b \<noteq> 0 \<Longrightarrow> b \<in> basis" for b
    using representation_ne_zero basis' by auto
  show "finite {b. representation basis' v b \<noteq> 0}"
    using finite_representation .
  show "(\<Sum>b | representation basis' v b \<noteq> 0. representation basis' v b *s b) = v"
    using sum_nonzero_representation_eq[OF * v] .
qed

text \<open>The set \<open>B\<close> is the maximal independent set for \<open>span B\<close>, or \<open>A\<close> is the minimal spanning set\<close>
lemma spanning_subset_independent:
  assumes BA: "B \<subseteq> A"
    and iA: "independent A"
    and AsB: "A \<subseteq> span B"
  shows "A = B"
proof (intro antisym[OF _ BA] subsetI)
  have iB: "independent B" using independent_mono [OF iA BA] .
  fix v assume "v \<in> A"
  with AsB have "v \<in> span B" by auto
  let ?RB = "representation B v" and ?RA = "representation A v"
  have "?RB v = 1"
    unfolding representation_extend[OF iA \<open>v \<in> span B\<close> BA, symmetric] representation_basis[OF iA \<open>v \<in> A\<close>] by simp
  then show "v \<in> B"
    using representation_ne_zero[of B v v] by auto
qed

end

(* We need to introduce more specific modules, where the ring structure gets more and more finer,
  i.e. Bezout rings & domains, division rings, fields *)

text \<open>A linear function is a mapping between two modules over the same ring.\<close>

locale module_hom = m1: module s1 + m2: module s2
    for s1 :: "'a::comm_ring_1 \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr \<open>*a\<close> 75)
    and s2 :: "'a::comm_ring_1 \<Rightarrow> 'c::ab_group_add \<Rightarrow> 'c" (infixr \<open>*b\<close> 75) +
  fixes f :: "'b \<Rightarrow> 'c"
  assumes add: "f (b1 + b2) = f b1 + f b2"
    and scale: "f (r *a b) = r *b f b"
begin

lemma zero[simp]: "f 0 = 0"
  using scale[of 0 0] by simp

lemma neg: "f (- x) = - f x"
  using scale [where r="-1"] by (metis add add_eq_0_iff zero)

lemma diff: "f (x - y) = f x - f y"
  by (metis diff_conv_add_uminus add neg)

lemma sum: "f (sum g S) = (\<Sum>a\<in>S. f (g a))"
proof (induct S rule: infinite_finite_induct)
  case (insert x F)
  have "f (sum g (insert x F)) = f (g x + sum g F)"
    using insert.hyps by simp
  also have "\<dots> = f (g x) + f (sum g F)"
    using add by simp
  also have "\<dots> = (\<Sum>a\<in>insert x F. f (g a))"
    using insert.hyps by simp
  finally show ?case .
qed simp_all

lemma inj_on_iff_eq_0:
  assumes s: "m1.subspace s"
  shows "inj_on f s \<longleftrightarrow> (\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0)"
proof -
  have "inj_on f s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. f x - f y = 0 \<longrightarrow> x - y = 0)"
    by (simp add: inj_on_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. f (x - y) = 0 \<longrightarrow> x - y = 0)"
    by (simp add: diff)
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0)" (is "?l = ?r")(* TODO: sledgehammer! *)
  proof safe
    fix x assume ?l assume "x \<in> s" "f x = 0" with \<open>?l\<close>[rule_format, of x 0] s show "x = 0"
      by (auto simp: m1.subspace_0)
  next
    fix x y assume ?r assume "x \<in> s" "y \<in> s" "f (x - y) = 0"
    with \<open>?r\<close>[rule_format, of "x - y"] s
    show "x - y = 0"
      by (auto simp: m1.subspace_diff)
  qed
  finally show ?thesis
    by auto
qed

lemma inj_iff_eq_0: "inj f = (\<forall>x. f x = 0 \<longrightarrow> x = 0)"
  by (rule inj_on_iff_eq_0[OF m1.subspace_UNIV, unfolded ball_UNIV])

lemma subspace_image: assumes S: "m1.subspace S" shows "m2.subspace (f ` S)"
  unfolding m2.subspace_def
proof safe
  show "0 \<in> f ` S"
    by (rule image_eqI[of _ _ 0]) (auto simp: S m1.subspace_0)
  show "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> f x + f y \<in> f ` S" for x y
    by (rule image_eqI[of _ _ "x + y"]) (auto simp: S m1.subspace_add add)
  show "x \<in> S \<Longrightarrow> r *b f x \<in> f ` S" for r x
    by (rule image_eqI[of _ _ "r *a x"]) (auto simp: S m1.subspace_scale scale)
qed

lemma subspace_vimage: "m2.subspace S \<Longrightarrow> m1.subspace (f -` S)"
  by (simp add: vimage_def add scale m1.subspace_def m2.subspace_0 m2.subspace_add m2.subspace_scale)

lemma subspace_kernel: "m1.subspace {x. f x = 0}"
  using subspace_vimage[OF m2.subspace_single_0] by (simp add: vimage_def)

lemma span_image: "m2.span (f ` S) = f ` (m1.span S)"
proof (rule m2.span_unique)
  show "f ` S \<subseteq> f ` m1.span S"
    by (rule image_mono, rule m1.span_superset)
  show "m2.subspace (f ` m1.span S)"
    using m1.subspace_span by (rule subspace_image)
next
  fix T assume "f ` S \<subseteq> T" and "m2.subspace T" then show "f ` m1.span S \<subseteq> T"
    unfolding image_subset_iff_subset_vimage by (metis subspace_vimage m1.span_minimal)
qed

lemma dependent_inj_imageD:
  assumes d: "m2.dependent (f ` s)" and i: "inj_on f (m1.span s)"
  shows "m1.dependent s"
proof -
  have [intro]: "inj_on f s"
    using \<open>inj_on f (m1.span s)\<close> m1.span_superset by (rule inj_on_subset)
  from d obtain s' r v where *: "finite s'" "s' \<subseteq> s" "(\<Sum>v\<in>f ` s'. r v *b v) = 0" "v \<in> s'" "r (f v) \<noteq> 0"
    by (auto simp: m2.dependent_explicit subset_image_iff dest!: finite_imageD intro: inj_on_subset)
  have "f (\<Sum>v\<in>s'. r (f v) *a v) = (\<Sum>v\<in>s'. r (f v) *b f v)"
    by (simp add: sum scale)
  also have "... = (\<Sum>v\<in>f ` s'. r v *b v)"
    using \<open>s' \<subseteq> s\<close> by (subst sum.reindex) (auto dest!: finite_imageD intro: inj_on_subset)
  finally have "f (\<Sum>v\<in>s'. r (f v) *a v) = 0"
    by (simp add: *)
  with \<open>s' \<subseteq> s\<close> have "(\<Sum>v\<in>s'. r (f v) *a v) = 0"
    by (intro inj_onD[OF i] m1.span_zero m1.span_sum m1.span_scale) (auto intro: m1.span_base)
  then show "m1.dependent s"
    using \<open>finite s'\<close> \<open>s' \<subseteq> s\<close> \<open>v \<in> s'\<close> \<open>r (f v) \<noteq> 0\<close> by (force simp add: m1.dependent_explicit)
qed

lemma eq_0_on_span:
  assumes f0: "\<And>x. x \<in> b \<Longrightarrow> f x = 0" and x: "x \<in> m1.span b" shows "f x = 0"
  using m1.span_induct[OF x subspace_kernel] f0 by simp

lemma independent_injective_image: "m1.independent s \<Longrightarrow> inj_on f (m1.span s) \<Longrightarrow> m2.independent (f ` s)"
  using dependent_inj_imageD[of s] by auto

lemma inj_on_span_independent_image:
  assumes ifB: "m2.independent (f ` B)" and f: "inj_on f B" shows "inj_on f (m1.span B)"
  unfolding inj_on_iff_eq_0[OF m1.subspace_span] unfolding m1.span_explicit'
proof safe
  fix r assume fr: "finite {v. r v \<noteq> 0}" and r: "\<forall>v. r v \<noteq> 0 \<longrightarrow> v \<in> B"
    and eq0: "f (\<Sum>v | r v \<noteq> 0. r v *a v) = 0"
  have "0 = (\<Sum>v | r v \<noteq> 0. r v *b f v)"
    using eq0 by (simp add: sum scale)
  also have "... = (\<Sum>v\<in>f ` {v. r v \<noteq> 0}. r (the_inv_into B f v) *b v)"
    using r by (subst sum.reindex) (auto simp: the_inv_into_f_f[OF f] intro!: inj_on_subset[OF f] sum.cong)
  finally have "r v \<noteq> 0 \<Longrightarrow> r (the_inv_into B f (f v)) = 0" for v
    using fr r ifB[unfolded m2.independent_explicit_module, rule_format,
        of "f ` {v. r v \<noteq> 0}" "\<lambda>v. r (the_inv_into B f v)"]
    by auto
  then have "r v = 0" for v
    using the_inv_into_f_f[OF f] r by auto
  then show "(\<Sum>v | r v \<noteq> 0. r v *a v) = 0" by auto
qed

lemma inj_on_span_iff_independent_image: "m2.independent (f ` B) \<Longrightarrow> inj_on f (m1.span B) \<longleftrightarrow> inj_on f B"
  using inj_on_span_independent_image[of B] inj_on_subset[OF _ m1.span_superset, of f B] by auto

lemma subspace_linear_preimage: "m2.subspace S \<Longrightarrow> m1.subspace {x. f x \<in> S}"
  by (simp add: add scale m1.subspace_def m2.subspace_def)

lemma spans_image: "V \<subseteq> m1.span B \<Longrightarrow> f ` V \<subseteq> m2.span (f ` B)"
  by (metis image_mono span_image)

text \<open>Relation between bases and injectivity/surjectivity of map.\<close>

lemma spanning_surjective_image:
  assumes us: "UNIV \<subseteq> m1.span S"
    and sf: "surj f"
  shows "UNIV \<subseteq> m2.span (f ` S)"
proof -
  have "UNIV \<subseteq> f ` UNIV"
    using sf by (auto simp add: surj_def)
  also have " \<dots> \<subseteq> m2.span (f ` S)"
    using spans_image[OF us] .
  finally show ?thesis .
qed

lemmas independent_inj_on_image = independent_injective_image

lemma independent_inj_image:
  "m1.independent S \<Longrightarrow> inj f \<Longrightarrow> m2.independent (f ` S)"
  using independent_inj_on_image[of S] by (auto simp: subset_inj_on)

end

lemma module_hom_iff:
  "module_hom s1 s2  f \<longleftrightarrow>
    module s1 \<and> module s2 \<and>
    (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (s1 c x) = s2 c (f x))"
  by (simp add: module_hom_def module_hom_axioms_def)

locale module_pair = m1: module s1 + m2: module s2
  for s1 :: "'a :: comm_ring_1 \<Rightarrow> 'b \<Rightarrow> 'b :: ab_group_add"
  and s2 :: "'a :: comm_ring_1 \<Rightarrow> 'c \<Rightarrow> 'c :: ab_group_add"
begin

lemma module_hom_zero: "module_hom s1 s2 (\<lambda>x. 0)"
  by (simp add: module_hom_iff m1.module_axioms m2.module_axioms)

lemma module_hom_add: "module_hom s1 s2 f \<Longrightarrow> module_hom s1 s2 g \<Longrightarrow> module_hom s1 s2 (\<lambda>x. f x + g x)"
  by (simp add: module_hom_iff module.scale_right_distrib)

lemma module_hom_sub: "module_hom s1 s2 f \<Longrightarrow> module_hom s1 s2 g \<Longrightarrow> module_hom s1 s2 (\<lambda>x. f x - g x)"
  by (simp add: module_hom_iff module.scale_right_diff_distrib)

lemma module_hom_neg: "module_hom s1 s2 f \<Longrightarrow> module_hom s1 s2 (\<lambda>x. - f x)"
  by (simp add: module_hom_iff module.scale_minus_right)

lemma module_hom_scale: "module_hom s1 s2 f \<Longrightarrow> module_hom s1 s2 (\<lambda>x. s2 c (f x))"
  by (simp add: module_hom_iff module.scale_scale module.scale_right_distrib ac_simps)

lemma module_hom_compose_scale:
  "module_hom s1 s2 (\<lambda>x. s2 (f x) (c))"
  if "module_hom s1 (*) f"
proof -
  interpret mh: module_hom s1 "(*)" f by fact
  show ?thesis
    by unfold_locales (simp_all add: mh.add mh.scale m2.scale_left_distrib)
qed

lemma bij_module_hom_imp_inv_module_hom: "module_hom scale1 scale2 f \<Longrightarrow> bij f \<Longrightarrow>
  module_hom scale2 scale1 (inv f)"
  by (auto simp: module_hom_iff bij_is_surj bij_is_inj surj_f_inv_f
      intro!: Hilbert_Choice.inv_f_eq)

lemma module_hom_sum: "(\<And>i. i \<in> I \<Longrightarrow> module_hom s1 s2 (f i)) \<Longrightarrow> (I = {} \<Longrightarrow> module s1 \<and> module s2) \<Longrightarrow> module_hom s1 s2 (\<lambda>x. \<Sum>i\<in>I. f i x)"
  apply (induction I rule: infinite_finite_induct)
  apply (auto intro!: module_hom_zero module_hom_add)
  using m1.module_axioms m2.module_axioms by blast

lemma module_hom_eq_on_span: "f x = g x"
  if "module_hom s1 s2 f" "module_hom s1 s2 g"
  and "(\<And>x. x \<in> B \<Longrightarrow> f x = g x)" "x \<in> m1.span B"
proof -
  interpret module_hom s1 s2 "\<lambda>x. f x - g x"
    by (rule module_hom_sub that)+
  from eq_0_on_span[OF _ that(4)] that(3) show ?thesis by auto
qed

end

context module begin

lemma module_hom_scale_self[simp]:
  "module_hom scale scale (\<lambda>x. scale c x)"
  using module_axioms module_hom_iff scale_left_commute scale_right_distrib by blast

lemma module_hom_scale_left[simp]:
  "module_hom (*) scale (\<lambda>r. scale r x)"
  by unfold_locales (auto simp: algebra_simps)

lemma module_hom_id: "module_hom scale scale id"
  by (simp add: module_hom_iff module_axioms)

lemma module_hom_ident: "module_hom scale scale (\<lambda>x. x)"
  by (simp add: module_hom_iff module_axioms)

lemma module_hom_uminus: "module_hom scale scale uminus"
  by (simp add: module_hom_iff module_axioms)

end

lemma module_hom_compose: "module_hom s1 s2 f \<Longrightarrow> module_hom s2 s3 g \<Longrightarrow> module_hom s1 s3 (g o f)"
  by (auto simp: module_hom_iff)

end
