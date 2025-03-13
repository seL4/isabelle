(*  Title:      HOL/Equiv_Relations.thy
    Author:     Lawrence C Paulson, 1996 Cambridge University Computer Laboratory
*)

section \<open>Equivalence Relations in Higher-Order Set Theory\<close>

theory Equiv_Relations
  imports BNF_Least_Fixpoint
begin

subsection \<open>Equivalence relations -- set version\<close>

definition equiv :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"
  where "equiv A r \<longleftrightarrow> r \<subseteq> A \<times> A \<and> refl_on A r \<and> sym r \<and> trans r"

lemma equivI: "r \<subseteq> A \<times> A \<Longrightarrow> refl_on A r \<Longrightarrow> sym r \<Longrightarrow> trans r \<Longrightarrow> equiv A r"
  by (simp add: equiv_def)

lemma equivE:
  assumes "equiv A r"
  obtains "r \<subseteq> A \<times> A" and "refl_on A r" and "sym r" and "trans r"
  using assms by (simp add: equiv_def)

text \<open>
  Suppes, Theorem 70: \<open>r\<close> is an equiv relation iff \<open>r\<inverse> O r = r\<close>.

  First half: \<open>equiv A r \<Longrightarrow> r\<inverse> O r = r\<close>.
\<close>

lemma sym_trans_comp_subset:
  assumes "r \<subseteq> A \<times> A" and "sym_on A r" and "trans_on A r"
  shows "r\<inverse> O r \<subseteq> r"
proof (rule subsetI)
  fix p
  assume "p \<in> r\<inverse> O r"
  then obtain x y z where "p = (x, z)" and "(y, x) \<in> r" and "(y, z) \<in> r"
    by auto
  hence "x \<in> A" and "y \<in> A" and "z \<in> A"
    using \<open>r \<subseteq> A \<times> A\<close> by auto
  have "(x, y) \<in> r"
    using \<open>(y, x) \<in> r\<close> \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>sym_on A r\<close> by (simp add: sym_on_def)
  hence "(x, z) \<in> r"
    using \<open>trans_on A r\<close>[THEN trans_onD, OF \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>z \<in> A\<close>] \<open>(y, z) \<in> r\<close> by blast
  thus "p \<in> r"
    unfolding \<open>p = (x, z)\<close> .
qed

lemma refl_on_comp_subset: "r \<subseteq> A \<times> A \<Longrightarrow> refl_on A r \<Longrightarrow> r \<subseteq> r\<inverse> O r"
  unfolding refl_on_def by blast

lemma equiv_comp_eq: "equiv A r \<Longrightarrow> r\<inverse> O r = r"
proof (rule subset_antisym)
  show "equiv A r \<Longrightarrow> r\<inverse> O r \<subseteq> r"
    by (rule sym_trans_comp_subset[of r A]) (auto elim: equivE intro: sym_on_subset trans_on_subset)
next
  show "equiv A r \<Longrightarrow> r \<subseteq> r\<inverse> O r"
    by (rule refl_on_comp_subset[of r A]) (auto elim: equivE)
qed

text \<open>Second half.\<close>

lemma comp_equivI:
  assumes "r\<inverse> O r = r" "Domain r = A"
  shows "equiv A r"
proof (rule equivI)
  show "r \<subseteq> A \<times> A"
    using assms by auto

  have *: "\<And>x y. (x, y) \<in> r \<Longrightarrow> (y, x) \<in> r"
    using assms by blast

  thus "refl_on A r" "sym r" "trans r"
    unfolding refl_on_def sym_def trans_def
    using assms by auto
qed


subsection \<open>Equivalence classes\<close>

lemma equiv_class_subset: "equiv A r \<Longrightarrow> (a, b) \<in> r \<Longrightarrow> r``{a} \<subseteq> r``{b}"
  \<comment> \<open>lemma for the next result\<close>
  unfolding equiv_def trans_def sym_def by blast

theorem equiv_class_eq:
  assumes "equiv A r" and "(a, b) \<in> r"
  shows "r``{a} = r``{b}"
proof (intro subset_antisym equiv_class_subset[OF \<open>equiv A r\<close>])
  show "(a, b) \<in> r"
    using \<open>(a, b) \<in> r\<close> .
next
  have "sym r"
    using \<open>equiv A r\<close> by (auto elim: equivE)
  thus "(b, a) \<in> r"
    using \<open>(a, b) \<in> r\<close>
    by (auto dest: symD)
qed

lemma equiv_class_self: "equiv A r \<Longrightarrow> a \<in> A \<Longrightarrow> a \<in> r``{a}"
  unfolding equiv_def refl_on_def by blast

lemma subset_equiv_class: "equiv A r \<Longrightarrow> r``{b} \<subseteq> r``{a} \<Longrightarrow> b \<in> A \<Longrightarrow> (a, b) \<in> r"
  \<comment> \<open>lemma for the next result\<close>
  unfolding equiv_def refl_on_def by blast

lemma eq_equiv_class: "r``{a} = r``{b} \<Longrightarrow> equiv A r \<Longrightarrow> b \<in> A \<Longrightarrow> (a, b) \<in> r"
  by (iprover intro: equalityD2 subset_equiv_class)

lemma equiv_class_nondisjoint: "equiv A r \<Longrightarrow> x \<in> (r``{a} \<inter> r``{b}) \<Longrightarrow> (a, b) \<in> r"
  unfolding equiv_def trans_def sym_def by blast

lemma equiv_type: "equiv A r \<Longrightarrow> r \<subseteq> A \<times> A"
  unfolding equiv_def refl_on_def by blast

lemma equiv_class_eq_iff: "equiv A r \<Longrightarrow> (x, y) \<in> r \<longleftrightarrow> r``{x} = r``{y} \<and> x \<in> A \<and> y \<in> A"
  by (blast intro!: equiv_class_eq dest: eq_equiv_class equiv_type)

lemma eq_equiv_class_iff: "equiv A r \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> r``{x} = r``{y} \<longleftrightarrow> (x, y) \<in> r"
  by (blast intro!: equiv_class_eq dest: eq_equiv_class equiv_type)

lemma disjnt_equiv_class: "equiv A r \<Longrightarrow> disjnt (r``{a}) (r``{b}) \<longleftrightarrow> (a, b) \<notin> r"
  by (auto dest: equiv_class_self simp: equiv_class_eq_iff disjnt_def)


subsection \<open>Quotients\<close>

definition quotient :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set set"  (infixl \<open>'/'/\<close> 90)
  where "A//r = (\<Union>x \<in> A. {r``{x}})"  \<comment> \<open>set of equiv classes\<close>

lemma quotientI: "x \<in> A \<Longrightarrow> r``{x} \<in> A//r"
  unfolding quotient_def by blast

lemma quotientE: "X \<in> A//r \<Longrightarrow> (\<And>x. X = r``{x} \<Longrightarrow> x \<in> A \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding quotient_def by blast

lemma Union_quotient: "equiv A r \<Longrightarrow> \<Union>(A//r) = A"
  unfolding equiv_def refl_on_def quotient_def by blast

lemma quotient_disj_strong:
  assumes "r \<subseteq> A \<times> A" and "sym_on A r" and "trans_on A r" and "X \<in> A//r" and "Y \<in> A//r"
  shows "X = Y \<or> X \<inter> Y = {}"
proof -
  obtain x where "x \<in> A" and "X = {x'. (x, x') \<in> r}"
    using \<open>X \<in> A//r\<close> unfolding quotient_def UN_iff by blast

  moreover obtain y where "y \<in> A" and "Y = {y'. (y, y') \<in> r}"
    using \<open>Y \<in> A//r\<close> unfolding quotient_def UN_iff by blast

  have f8: "\<forall>a aa. (aa, a) \<in> r \<or> (a, aa) \<notin> r"
    using \<open>r \<subseteq> A \<times> A\<close>[unfolded subset_eq] \<open>sym_on A r\<close>[THEN sym_onD] by blast
  have f9: "\<forall>a aa ab. (aa, ab) \<in> r \<or> (aa, a) \<notin> r \<or> (a, ab) \<notin> r"
    using \<open>r \<subseteq> A \<times> A\<close>[unfolded subset_eq] \<open>trans_on A r\<close>[THEN trans_onD] by blast
  then have "\<forall>a aa. aa \<in> Y \<or> (y, a) \<notin> r \<or> (a, aa) \<notin> r"
    using \<open>Y = {y'. (y, y') \<in> r}\<close> by simp
  then show ?thesis
    using f9 f8 \<open>X = {x'. (x, x') \<in> r}\<close> \<open>Y = {y'. (y, y') \<in> r}\<close>
      Collect_cong disjoint_iff_not_equal mem_Collect_eq by blast
qed

lemma quotient_disj: "equiv A r \<Longrightarrow> X \<in> A//r \<Longrightarrow> Y \<in> A//r \<Longrightarrow> X = Y \<or> X \<inter> Y = {}"
  by (rule quotient_disj_strong[of r A X Y])
    (auto elim: equivE intro: sym_on_subset trans_on_subset)

lemma quotient_eqI:
  assumes "equiv A r" "X \<in> A//r" "Y \<in> A//r" and xy: "x \<in> X" "y \<in> Y" "(x, y) \<in> r"
  shows "X = Y"
proof -
  obtain a b where "a \<in> A" and a: "X = r `` {a}" and "b \<in> A" and b: "Y = r `` {b}"
    using assms by (auto elim!: quotientE)
  moreover have "sym r" and "trans r"
    using \<open>equiv A r\<close>
    by (auto elim: equivE)
  ultimately have "(a,b) \<in> r"
      using xy unfolding sym_def trans_def by blast
  then show ?thesis
    unfolding a b by (rule equiv_class_eq [OF \<open>equiv A r\<close>])
qed

lemma quotient_eq_iff:
  assumes "equiv A r" "X \<in> A//r" "Y \<in> A//r" and xy: "x \<in> X" "y \<in> Y" 
  shows "X = Y \<longleftrightarrow> (x, y) \<in> r"
proof
  assume L: "X = Y" 
  with assms show "(x, y) \<in> r" 
    unfolding equiv_def sym_def trans_def by (blast elim!: quotientE)
next
  assume \<section>: "(x, y) \<in> r" show "X = Y"
    by (rule quotient_eqI) (use \<section> assms in \<open>blast+\<close>)
qed

lemma eq_equiv_class_iff2: "equiv A r \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> {x}//r = {y}//r \<longleftrightarrow> (x, y) \<in> r"
  by (simp add: quotient_def eq_equiv_class_iff)

lemma quotient_empty [simp]: "{}//r = {}"
  by (simp add: quotient_def)

lemma quotient_is_empty [iff]: "A//r = {} \<longleftrightarrow> A = {}"
  by (simp add: quotient_def)

lemma quotient_is_empty2 [iff]: "{} = A//r \<longleftrightarrow> A = {}"
  by (simp add: quotient_def)

lemma singleton_quotient: "{x}//r = {r `` {x}}"
  by (simp add: quotient_def)

lemma quotient_diff1: "inj_on (\<lambda>a. {a}//r) A \<Longrightarrow> a \<in> A \<Longrightarrow> (A - {a})//r = A//r - {a}//r"
  unfolding quotient_def inj_on_def by blast


subsection \<open>Refinement of one equivalence relation WRT another\<close>

lemma refines_equiv_class_eq: "R \<subseteq> S \<Longrightarrow> equiv A R \<Longrightarrow> equiv A S \<Longrightarrow> R``(S``{a}) = S``{a}"
  by (auto simp: equiv_class_eq_iff)

lemma refines_equiv_class_eq2: "R \<subseteq> S \<Longrightarrow> equiv A R \<Longrightarrow> equiv A S \<Longrightarrow> S``(R``{a}) = S``{a}"
  by (auto simp: equiv_class_eq_iff)

lemma refines_equiv_image_eq: "R \<subseteq> S \<Longrightarrow> equiv A R \<Longrightarrow> equiv A S \<Longrightarrow> (\<lambda>X. S``X) ` (A//R) = A//S"
   by (auto simp: quotient_def image_UN refines_equiv_class_eq2)

lemma finite_refines_finite:
  "finite (A//R) \<Longrightarrow> R \<subseteq> S \<Longrightarrow> equiv A R \<Longrightarrow> equiv A S \<Longrightarrow> finite (A//S)"
  by (erule finite_surj [where f = "\<lambda>X. S``X"]) (simp add: refines_equiv_image_eq)

lemma finite_refines_card_le:
  "finite (A//R) \<Longrightarrow> R \<subseteq> S \<Longrightarrow> equiv A R \<Longrightarrow> equiv A S \<Longrightarrow> card (A//S) \<le> card (A//R)"
  by (subst refines_equiv_image_eq [of R S A, symmetric])
    (auto simp: card_image_le [where f = "\<lambda>X. S``X"])


subsection \<open>Defining unary operations upon equivalence classes\<close>

text \<open>A congruence-preserving function.\<close>

definition congruent :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "congruent r f \<longleftrightarrow> (\<forall>(y, z) \<in> r. f y = f z)"

lemma congruentI: "(\<And>y z. (y, z) \<in> r \<Longrightarrow> f y = f z) \<Longrightarrow> congruent r f"
  by (auto simp add: congruent_def)

lemma congruentD: "congruent r f \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> f y = f z"
  by (auto simp add: congruent_def)

abbreviation RESPECTS :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"  (infixr \<open>respects\<close> 80)
  where "f respects r \<equiv> congruent r f"


lemma UN_constant_eq: "a \<in> A \<Longrightarrow> \<forall>y \<in> A. f y = c \<Longrightarrow> (\<Union>y \<in> A. f y) = c"
  \<comment> \<open>lemma required to prove \<open>UN_equiv_class\<close>\<close>
  by auto

lemma UN_equiv_class:
  assumes "equiv A r" "f respects r" "a \<in> A"
  shows "(\<Union>x \<in> r``{a}. f x) = f a"
  \<comment> \<open>Conversion rule\<close>
proof -
  have \<section>: "\<forall>x\<in>r `` {a}. f x = f a"
    using assms unfolding equiv_def congruent_def sym_def by blast
  show ?thesis
    by (iprover intro: assms UN_constant_eq [OF equiv_class_self \<section>])
qed

lemma UN_equiv_class_type:
  assumes r: "equiv A r" "f respects r" and X: "X \<in> A//r" and AB: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B"
  shows "(\<Union>x \<in> X. f x) \<in> B"
  using assms unfolding quotient_def
  by (auto simp: UN_equiv_class [OF r])

text \<open>
  Sufficient conditions for injectiveness.  Could weaken premises!
  major premise could be an inclusion; \<open>bcong\<close> could be
  \<open>\<And>y. y \<in> A \<Longrightarrow> f y \<in> B\<close>.
\<close>

lemma UN_equiv_class_inject:
  assumes "equiv A r" "f respects r"
    and eq: "(\<Union>x \<in> X. f x) = (\<Union>y \<in> Y. f y)" 
    and X: "X \<in> A//r" and Y: "Y \<in> A//r" 
    and fr: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x = f y \<Longrightarrow> (x, y) \<in> r"
  shows "X = Y"
proof -
  obtain a b where "a \<in> A" and a: "X = r `` {a}" and "b \<in> A" and b: "Y = r `` {b}"
    using assms by (auto elim!: quotientE)
  then have "\<Union> (f ` r `` {a}) = f a" "\<Union> (f ` r `` {b}) = f b"
    by (iprover intro: UN_equiv_class [OF \<open>equiv A r\<close>] assms)+
  then have "f a = f b"
    using eq unfolding a b by (iprover intro: trans sym)
  then have "(a,b) \<in> r"
    using fr \<open>a \<in> A\<close> \<open>b \<in> A\<close> by blast
  then show ?thesis
    unfolding a b by (rule equiv_class_eq [OF \<open>equiv A r\<close>])
qed


subsection \<open>Defining binary operations upon equivalence classes\<close>

text \<open>A congruence-preserving function of two arguments.\<close>

definition congruent2 :: "('a \<times> 'a) set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> bool"
  where "congruent2 r1 r2 f \<longleftrightarrow> (\<forall>(y1, z1) \<in> r1. \<forall>(y2, z2) \<in> r2. f y1 y2 = f z1 z2)"

lemma congruent2I':
  assumes "\<And>y1 z1 y2 z2. (y1, z1) \<in> r1 \<Longrightarrow> (y2, z2) \<in> r2 \<Longrightarrow> f y1 y2 = f z1 z2"
  shows "congruent2 r1 r2 f"
  using assms by (auto simp add: congruent2_def)

lemma congruent2D: "congruent2 r1 r2 f \<Longrightarrow> (y1, z1) \<in> r1 \<Longrightarrow> (y2, z2) \<in> r2 \<Longrightarrow> f y1 y2 = f z1 z2"
  by (auto simp add: congruent2_def)

text \<open>Abbreviation for the common case where the relations are identical.\<close>
abbreviation RESPECTS2:: "('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"  (infixr \<open>respects2\<close> 80)
  where "f respects2 r \<equiv> congruent2 r r f"


lemma congruent2_implies_congruent:
  "equiv A r1 \<Longrightarrow> congruent2 r1 r2 f \<Longrightarrow> a \<in> A \<Longrightarrow> congruent r2 (f a)"
  unfolding congruent_def congruent2_def equiv_def refl_on_def by blast

lemma congruent2_implies_congruent_UN:
  assumes "equiv A1 r1" "equiv A2 r2" "congruent2 r1 r2 f" "a \<in> A2" 
  shows "congruent r1 (\<lambda>x1. \<Union>x2 \<in> r2``{a}. f x1 x2)"
  unfolding congruent_def
proof clarify
  fix c d
  assume cd: "(c,d) \<in> r1"
  then have "c \<in> A1" "d \<in> A1"
    using \<open>equiv A1 r1\<close> by (auto elim!: equiv_type [THEN subsetD, THEN SigmaE2])
  moreover have "f c a = f d a"
    using assms cd unfolding congruent2_def equiv_def refl_on_def by blast
  ultimately show "\<Union> (f c ` r2 `` {a}) = \<Union> (f d ` r2 `` {a})"
    using assms by (simp add: UN_equiv_class congruent2_implies_congruent)
qed

lemma UN_equiv_class2:
  "equiv A1 r1 \<Longrightarrow> equiv A2 r2 \<Longrightarrow> congruent2 r1 r2 f \<Longrightarrow> a1 \<in> A1 \<Longrightarrow> a2 \<in> A2 \<Longrightarrow>
    (\<Union>x1 \<in> r1``{a1}. \<Union>x2 \<in> r2``{a2}. f x1 x2) = f a1 a2"
  by (simp add: UN_equiv_class congruent2_implies_congruent congruent2_implies_congruent_UN)

lemma UN_equiv_class_type2:
  "equiv A1 r1 \<Longrightarrow> equiv A2 r2 \<Longrightarrow> congruent2 r1 r2 f
    \<Longrightarrow> X1 \<in> A1//r1 \<Longrightarrow> X2 \<in> A2//r2
    \<Longrightarrow> (\<And>x1 x2. x1 \<in> A1 \<Longrightarrow> x2 \<in> A2 \<Longrightarrow> f x1 x2 \<in> B)
    \<Longrightarrow> (\<Union>x1 \<in> X1. \<Union>x2 \<in> X2. f x1 x2) \<in> B"
  unfolding quotient_def
  by (blast intro: UN_equiv_class_type congruent2_implies_congruent_UN
                   congruent2_implies_congruent quotientI)


lemma UN_UN_split_split_eq:
  "(\<Union>(x1, x2) \<in> X. \<Union>(y1, y2) \<in> Y. A x1 x2 y1 y2) =
    (\<Union>x \<in> X. \<Union>y \<in> Y. (\<lambda>(x1, x2). (\<lambda>(y1, y2). A x1 x2 y1 y2) y) x)"
  \<comment> \<open>Allows a natural expression of binary operators,\<close>
  \<comment> \<open>without explicit calls to \<open>split\<close>\<close>
  by auto

lemma congruent2I:
  "equiv A1 r1 \<Longrightarrow> equiv A2 r2
    \<Longrightarrow> (\<And>y z w. w \<in> A2 \<Longrightarrow> (y,z) \<in> r1 \<Longrightarrow> f y w = f z w)
    \<Longrightarrow> (\<And>y z w. w \<in> A1 \<Longrightarrow> (y,z) \<in> r2 \<Longrightarrow> f w y = f w z)
    \<Longrightarrow> congruent2 r1 r2 f"
  \<comment> \<open>Suggested by John Harrison -- the two subproofs may be\<close>
  \<comment> \<open>\<^emph>\<open>much\<close> simpler than the direct proof.\<close>
  unfolding congruent2_def equiv_def refl_on_def
  by (blast intro: trans)

lemma congruent2_commuteI:
  assumes equivA: "equiv A r"
    and commute: "\<And>y z. y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> f y z = f z y"
    and congt: "\<And>y z w. w \<in> A \<Longrightarrow> (y,z) \<in> r \<Longrightarrow> f w y = f w z"
  shows "f respects2 r"
proof (rule congruent2I [OF equivA equivA])
  note eqv = equivA [THEN equiv_type, THEN subsetD, THEN SigmaE2]
  show "\<And>y z w. \<lbrakk>w \<in> A; (y, z) \<in> r\<rbrakk> \<Longrightarrow> f y w = f z w"
    by (iprover intro: commute [THEN trans] sym congt elim: eqv)
  show "\<And>y z w. \<lbrakk>w \<in> A; (y, z) \<in> r\<rbrakk> \<Longrightarrow> f w y = f w z"
    by (iprover intro: congt elim: eqv)
qed


subsection \<open>Quotients and finiteness\<close>

text \<open>Suggested by Florian Kammüller\<close>

lemma finite_quotient:
  assumes "finite A" "r \<subseteq> A \<times> A"
  shows "finite (A//r)"
    \<comment> \<open>recall @{thm equiv_type}\<close>
proof -
  have "A//r \<subseteq> Pow A"
    using assms unfolding quotient_def by blast
  moreover have "finite (Pow A)"
    using assms by simp
  ultimately show ?thesis
    by (iprover intro: finite_subset)
qed

lemma finite_equiv_class: "finite A \<Longrightarrow> r \<subseteq> A \<times> A \<Longrightarrow> X \<in> A//r \<Longrightarrow> finite X"
  unfolding quotient_def
  by (erule rev_finite_subset) blast

lemma equiv_imp_dvd_card:
  assumes "finite A" "equiv A r" "\<And>X. X \<in> A//r \<Longrightarrow> k dvd card X"
  shows "k dvd card A"
proof (rule Union_quotient [THEN subst])
  show "k dvd card (\<Union> (A // r))"
    apply (rule dvd_partition)
    using assms
    by (auto simp: Union_quotient dest: quotient_disj)
qed (use assms in blast)


subsection \<open>Projection\<close>

definition proj :: "('b \<times> 'a) set \<Rightarrow> 'b \<Rightarrow> 'a set"
  where "proj r x = r `` {x}"

lemma proj_preserves: "x \<in> A \<Longrightarrow> proj r x \<in> A//r"
  unfolding proj_def by (rule quotientI)

lemma proj_in_iff:
  assumes "equiv A r"
  shows "proj r x \<in> A//r \<longleftrightarrow> x \<in> A"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then show ?lhs by (simp add: proj_preserves)
next
  assume ?lhs
  then show ?rhs
    unfolding proj_def quotient_def
  proof safe
    fix y
    assume y: "y \<in> A" and "r `` {x} = r `` {y}"
    moreover have "y \<in> r `` {y}"
      using assms y unfolding equiv_def refl_on_def by blast
    ultimately have "(x, y) \<in> r" by blast
    then show "x \<in> A"
      using assms unfolding equiv_def refl_on_def by blast
  qed
qed

lemma proj_iff: "equiv A r \<Longrightarrow> {x, y} \<subseteq> A \<Longrightarrow> proj r x = proj r y \<longleftrightarrow> (x, y) \<in> r"
  by (simp add: proj_def eq_equiv_class_iff)

(*
lemma in_proj: "\<lbrakk>equiv A r; x \<in> A\<rbrakk> \<Longrightarrow> x \<in> proj r x"
unfolding proj_def equiv_def refl_on_def by blast
*)

lemma proj_image: "proj r ` A = A//r"
  unfolding proj_def[abs_def] quotient_def by blast

lemma in_quotient_imp_non_empty: "equiv A r \<Longrightarrow> X \<in> A//r \<Longrightarrow> X \<noteq> {}"
  unfolding quotient_def using equiv_class_self by fast

lemma in_quotient_imp_in_rel: "equiv A r \<Longrightarrow> X \<in> A//r \<Longrightarrow> {x, y} \<subseteq> X \<Longrightarrow> (x, y) \<in> r"
  using quotient_eq_iff[THEN iffD1] by fastforce

lemma in_quotient_imp_closed: "equiv A r \<Longrightarrow> X \<in> A//r \<Longrightarrow> x \<in> X \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> y \<in> X"
  unfolding quotient_def equiv_def trans_def by blast

lemma in_quotient_imp_subset: "equiv A r \<Longrightarrow> X \<in> A//r \<Longrightarrow> X \<subseteq> A"
  using in_quotient_imp_in_rel equiv_type by fastforce


subsection \<open>Equivalence relations -- predicate version\<close>

text \<open>Partial equivalences.\<close>

definition part_equivp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "part_equivp R \<longleftrightarrow> (\<exists>x. R x x) \<and> (\<forall>x y. R x y \<longleftrightarrow> R x x \<and> R y y \<and> R x = R y)"
    \<comment> \<open>John-Harrison-style characterization\<close>

lemma part_equivpI: "\<exists>x. R x x \<Longrightarrow> symp R \<Longrightarrow> transp R \<Longrightarrow> part_equivp R"
  by (auto simp add: part_equivp_def) (auto elim: sympE transpE)

lemma part_equivpE:
  assumes "part_equivp R"
  obtains x where "R x x" and "symp R" and "transp R"
proof -
  from assms have 1: "\<exists>x. R x x"
    and 2: "\<And>x y. R x y \<longleftrightarrow> R x x \<and> R y y \<and> R x = R y"
    unfolding part_equivp_def by blast+
  from 1 obtain x where "R x x" ..
  moreover have "symp R"
  proof (rule sympI)
    fix x y
    assume "R x y"
    with 2 [of x y] show "R y x" by auto
  qed
  moreover have "transp R"
  proof (rule transpI)
    fix x y z
    assume "R x y" and "R y z"
    with 2 [of x y] 2 [of y z] show "R x z" by auto
  qed
  ultimately show thesis by (rule that)
qed

lemma part_equivp_refl_symp_transp: "part_equivp R \<longleftrightarrow> (\<exists>x. R x x) \<and> symp R \<and> transp R"
  by (auto intro: part_equivpI elim: part_equivpE)

lemma part_equivp_symp: "part_equivp R \<Longrightarrow> R x y \<Longrightarrow> R y x"
  by (erule part_equivpE, erule sympE)

lemma part_equivp_transp: "part_equivp R \<Longrightarrow> R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  by (erule part_equivpE, erule transpE)

lemma part_equivp_typedef: "part_equivp R \<Longrightarrow> \<exists>d. d \<in> {c. \<exists>x. R x x \<and> c = Collect (R x)}"
  by (auto elim: part_equivpE)


text \<open>Total equivalences.\<close>

definition equivp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "equivp R \<longleftrightarrow> (\<forall>x y. R x y = (R x = R y))" \<comment> \<open>John-Harrison-style characterization\<close>

lemma equivpI: "reflp R \<Longrightarrow> symp R \<Longrightarrow> transp R \<Longrightarrow> equivp R"
  by (auto elim: reflpE sympE transpE simp add: equivp_def)

lemma equivpE:
  assumes "equivp R"
  obtains "reflp R" and "symp R" and "transp R"
  using assms by (auto intro!: that reflpI sympI transpI simp add: equivp_def)

lemma equivp_implies_part_equivp: "equivp R \<Longrightarrow> part_equivp R"
  by (auto intro: part_equivpI elim: equivpE reflpE)

lemma equivp_equiv: "equiv UNIV A \<longleftrightarrow> equivp (\<lambda>x y. (x, y) \<in> A)"
  by (auto intro!: equivI equivpI [to_set] elim!: equivE equivpE [to_set])

lemma equivp_reflp_symp_transp: "equivp R \<longleftrightarrow> reflp R \<and> symp R \<and> transp R"
  by (auto intro: equivpI elim: equivpE)

lemma identity_equivp: "equivp (=)"
  by (auto intro: equivpI reflpI sympI transpI)

lemma equivp_reflp: "equivp R \<Longrightarrow> R x x"
  by (erule equivpE, erule reflpE)

lemma equivp_symp: "equivp R \<Longrightarrow> R x y \<Longrightarrow> R y x"
  by (erule equivpE, erule sympE)

lemma equivp_transp: "equivp R \<Longrightarrow> R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  by (erule equivpE, erule transpE)

lemma equivp_rtranclp: "symp r \<Longrightarrow> equivp r\<^sup>*\<^sup>*"
  by(intro equivpI reflpI sympI transpI)(auto dest: sympD[OF symp_rtranclp])

lemmas equivp_rtranclp_symclp [simp] = equivp_rtranclp[OF symp_on_symclp]

lemma equivp_vimage2p: "equivp R \<Longrightarrow> equivp (vimage2p f f R)"
  by(auto simp add: equivp_def vimage2p_def dest: fun_cong)

lemma equivp_imp_transp: "equivp R \<Longrightarrow> transp R"
  by(simp add: equivp_reflp_symp_transp)


subsection \<open>Equivalence closure\<close>

definition equivclp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "equivclp r = (symclp r)\<^sup>*\<^sup>*"

lemma transp_equivclp [simp]: "transp (equivclp r)"
  by(simp add: equivclp_def)

lemma reflp_equivclp [simp]: "reflp (equivclp r)"
  by(simp add: equivclp_def)

lemma symp_equivclp [simp]: "symp (equivclp r)"
  by(simp add: equivclp_def)

lemma equivp_evquivclp [simp]: "equivp (equivclp r)"
  by(simp add: equivpI)

lemma tranclp_equivclp [simp]: "(equivclp r)\<^sup>+\<^sup>+ = equivclp r"
  by(simp add: equivclp_def)

lemma rtranclp_equivclp [simp]: "(equivclp r)\<^sup>*\<^sup>* = equivclp r"
  by(simp add: equivclp_def)

lemma symclp_equivclp [simp]: "symclp (equivclp r) = equivclp r"
  by(simp add: equivclp_def symp_symclp_eq)

lemma equivclp_symclp [simp]: "equivclp (symclp r) = equivclp r"
  by(simp add: equivclp_def)

lemma equivclp_conversep [simp]: "equivclp (conversep r) = equivclp r"
  by(simp add: equivclp_def)

lemma equivclp_sym [sym]: "equivclp r x y \<Longrightarrow> equivclp r y x"
  by(rule sympD[OF symp_equivclp])

lemma equivclp_OO_equivclp_le_equivclp: "equivclp r OO equivclp r \<le> equivclp r"
  by(rule transp_relcompp_less_eq transp_equivclp)+

lemma rtranlcp_le_equivclp: "r\<^sup>*\<^sup>* \<le> equivclp r"
  unfolding equivclp_def by(rule rtranclp_mono)(simp add: symclp_pointfree)

lemma rtranclp_conversep_le_equivclp: "r\<inverse>\<inverse>\<^sup>*\<^sup>* \<le> equivclp r"
  unfolding equivclp_def by(rule rtranclp_mono)(simp add: symclp_pointfree)

lemma symclp_rtranclp_le_equivclp: "symclp r\<^sup>*\<^sup>* \<le> equivclp r"
  unfolding symclp_pointfree
  by(rule le_supI)(simp_all add: rtranclp_conversep[symmetric] rtranlcp_le_equivclp rtranclp_conversep_le_equivclp)

lemma r_OO_conversep_into_equivclp:
  "r\<^sup>*\<^sup>* OO r\<inverse>\<inverse>\<^sup>*\<^sup>* \<le> equivclp r"
  by(blast intro: order_trans[OF _ equivclp_OO_equivclp_le_equivclp] relcompp_mono rtranlcp_le_equivclp rtranclp_conversep_le_equivclp del: predicate2I)

lemma equivclp_induct [consumes 1, case_names base step, induct pred: equivclp]:
  assumes a: "equivclp r a b"
    and cases: "P a" "\<And>y z. equivclp r a y \<Longrightarrow> r y z \<or> r z y \<Longrightarrow> P y \<Longrightarrow> P z"
  shows "P b"
  using a unfolding equivclp_def
  by(induction rule: rtranclp_induct; fold equivclp_def; blast intro: cases elim: symclpE)

lemma converse_equivclp_induct [consumes 1, case_names base step]:
  assumes major: "equivclp r a b"
    and cases: "P b" "\<And>y z. r y z \<or> r z y \<Longrightarrow> equivclp r z b \<Longrightarrow> P z \<Longrightarrow> P y"
  shows "P a"
  using major unfolding equivclp_def
  by(induction rule: converse_rtranclp_induct; fold equivclp_def; blast intro: cases elim: symclpE)

lemma equivclp_refl [simp]: "equivclp r x x"
  by(rule reflpD[OF reflp_equivclp])

lemma r_into_equivclp [intro]: "r x y \<Longrightarrow> equivclp r x y"
  unfolding equivclp_def by(blast intro: symclpI)

lemma converse_r_into_equivclp [intro]: "r y x \<Longrightarrow> equivclp r x y"
  unfolding equivclp_def by(blast intro: symclpI)

lemma rtranclp_into_equivclp: "r\<^sup>*\<^sup>* x y \<Longrightarrow> equivclp r x y"
  using rtranlcp_le_equivclp[of r] by blast

lemma converse_rtranclp_into_equivclp: "r\<^sup>*\<^sup>* y x \<Longrightarrow> equivclp r x y"
  by(blast intro: equivclp_sym rtranclp_into_equivclp)

lemma equivclp_into_equivclp: "\<lbrakk> equivclp r a b; r b c \<or> r c b \<rbrakk> \<Longrightarrow> equivclp r a c"
  unfolding equivclp_def by(erule rtranclp.rtrancl_into_rtrancl)(auto intro: symclpI)

lemma equivclp_trans [trans]: "\<lbrakk> equivclp r a b; equivclp r b c \<rbrakk> \<Longrightarrow> equivclp r a c"
  using equivclp_OO_equivclp_le_equivclp[of r] by blast

hide_const (open) proj

end
