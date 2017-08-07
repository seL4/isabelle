(*  Title:      HOL/Equiv_Relations.thy
    Author:     Lawrence C Paulson, 1996 Cambridge University Computer Laboratory
*)

section \<open>Equivalence Relations in Higher-Order Set Theory\<close>

theory Equiv_Relations
  imports Groups_Big
begin

subsection \<open>Equivalence relations -- set version\<close>

definition equiv :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"
  where "equiv A r \<longleftrightarrow> refl_on A r \<and> sym r \<and> trans r"

lemma equivI: "refl_on A r \<Longrightarrow> sym r \<Longrightarrow> trans r \<Longrightarrow> equiv A r"
  by (simp add: equiv_def)

lemma equivE:
  assumes "equiv A r"
  obtains "refl_on A r" and "sym r" and "trans r"
  using assms by (simp add: equiv_def)

text \<open>
  Suppes, Theorem 70: \<open>r\<close> is an equiv relation iff \<open>r\<inverse> O r = r\<close>.

  First half: \<open>equiv A r \<Longrightarrow> r\<inverse> O r = r\<close>.
\<close>

lemma sym_trans_comp_subset: "sym r \<Longrightarrow> trans r \<Longrightarrow> r\<inverse> O r \<subseteq> r"
  unfolding trans_def sym_def converse_unfold by blast

lemma refl_on_comp_subset: "refl_on A r \<Longrightarrow> r \<subseteq> r\<inverse> O r"
  unfolding refl_on_def by blast

lemma equiv_comp_eq: "equiv A r \<Longrightarrow> r\<inverse> O r = r"
  apply (unfold equiv_def)
  apply clarify
  apply (rule equalityI)
   apply (iprover intro: sym_trans_comp_subset refl_on_comp_subset)+
  done

text \<open>Second half.\<close>

lemma comp_equivI: "r\<inverse> O r = r \<Longrightarrow> Domain r = A \<Longrightarrow> equiv A r"
  apply (unfold equiv_def refl_on_def sym_def trans_def)
  apply (erule equalityE)
  apply (subgoal_tac "\<forall>x y. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r")
   apply fast
  apply fast
  done


subsection \<open>Equivalence classes\<close>

lemma equiv_class_subset: "equiv A r \<Longrightarrow> (a, b) \<in> r \<Longrightarrow> r``{a} \<subseteq> r``{b}"
  \<comment> \<open>lemma for the next result\<close>
  unfolding equiv_def trans_def sym_def by blast

theorem equiv_class_eq: "equiv A r \<Longrightarrow> (a, b) \<in> r \<Longrightarrow> r``{a} = r``{b}"
  apply (assumption | rule equalityI equiv_class_subset)+
  apply (unfold equiv_def sym_def)
  apply blast
  done

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


subsection \<open>Quotients\<close>

definition quotient :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set set"  (infixl "'/'/" 90)
  where "A//r = (\<Union>x \<in> A. {r``{x}})"  \<comment> \<open>set of equiv classes\<close>

lemma quotientI: "x \<in> A ==> r``{x} \<in> A//r"
  unfolding quotient_def by blast

lemma quotientE: "X \<in> A//r \<Longrightarrow> (\<And>x. X = r``{x} \<Longrightarrow> x \<in> A \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding quotient_def by blast

lemma Union_quotient: "equiv A r \<Longrightarrow> \<Union>(A//r) = A"
  unfolding equiv_def refl_on_def quotient_def by blast

lemma quotient_disj: "equiv A r \<Longrightarrow> X \<in> A//r \<Longrightarrow> Y \<in> A//r \<Longrightarrow> X = Y \<or> X \<inter> Y = {}"
  apply (unfold quotient_def)
  apply clarify
  apply (rule equiv_class_eq)
   apply assumption
  apply (unfold equiv_def trans_def sym_def)
  apply blast
  done

lemma quotient_eqI:
  "equiv A r \<Longrightarrow> X \<in> A//r \<Longrightarrow> Y \<in> A//r \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> X = Y"
  apply (clarify elim!: quotientE)
  apply (rule equiv_class_eq)
   apply assumption
  apply (unfold equiv_def sym_def trans_def)
  apply blast
  done

lemma quotient_eq_iff:
  "equiv A r \<Longrightarrow> X \<in> A//r \<Longrightarrow> Y \<in> A//r \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> X = Y \<longleftrightarrow> (x, y) \<in> r"
  apply (rule iffI)
   prefer 2
   apply (blast del: equalityI intro: quotient_eqI)
  apply (clarify elim!: quotientE)
  apply (unfold equiv_def sym_def trans_def)
  apply blast
  done

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

abbreviation RESPECTS :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"  (infixr "respects" 80)
  where "f respects r \<equiv> congruent r f"


lemma UN_constant_eq: "a \<in> A \<Longrightarrow> \<forall>y \<in> A. f y = c \<Longrightarrow> (\<Union>y \<in> A. f y) = c"
  \<comment> \<open>lemma required to prove \<open>UN_equiv_class\<close>\<close>
  by auto

lemma UN_equiv_class: "equiv A r \<Longrightarrow> f respects r \<Longrightarrow> a \<in> A \<Longrightarrow> (\<Union>x \<in> r``{a}. f x) = f a"
  \<comment> \<open>Conversion rule\<close>
  apply (rule equiv_class_self [THEN UN_constant_eq])
    apply assumption
   apply assumption
  apply (unfold equiv_def congruent_def sym_def)
  apply (blast del: equalityI)
  done

lemma UN_equiv_class_type:
  "equiv A r \<Longrightarrow> f respects r \<Longrightarrow> X \<in> A//r \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> (\<Union>x \<in> X. f x) \<in> B"
  apply (unfold quotient_def)
  apply clarify
  apply (subst UN_equiv_class)
     apply auto
  done

text \<open>
  Sufficient conditions for injectiveness.  Could weaken premises!
  major premise could be an inclusion; \<open>bcong\<close> could be
  \<open>\<And>y. y \<in> A \<Longrightarrow> f y \<in> B\<close>.
\<close>

lemma UN_equiv_class_inject:
  "equiv A r \<Longrightarrow> f respects r \<Longrightarrow>
    (\<Union>x \<in> X. f x) = (\<Union>y \<in> Y. f y) \<Longrightarrow> X \<in> A//r ==> Y \<in> A//r
    \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x = f y \<Longrightarrow> (x, y) \<in> r)
    \<Longrightarrow> X = Y"
  apply (unfold quotient_def)
  apply clarify
  apply (rule equiv_class_eq)
   apply assumption
  apply (subgoal_tac "f x = f xa")
   apply blast
  apply (erule box_equals)
   apply (assumption | rule UN_equiv_class)+
  done


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
abbreviation RESPECTS2:: "('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"  (infixr "respects2" 80)
  where "f respects2 r \<equiv> congruent2 r r f"


lemma congruent2_implies_congruent:
  "equiv A r1 \<Longrightarrow> congruent2 r1 r2 f \<Longrightarrow> a \<in> A \<Longrightarrow> congruent r2 (f a)"
  unfolding congruent_def congruent2_def equiv_def refl_on_def by blast

lemma congruent2_implies_congruent_UN:
  "equiv A1 r1 \<Longrightarrow> equiv A2 r2 \<Longrightarrow> congruent2 r1 r2 f \<Longrightarrow> a \<in> A2 \<Longrightarrow>
    congruent r1 (\<lambda>x1. \<Union>x2 \<in> r2``{a}. f x1 x2)"
  apply (unfold congruent_def)
  apply clarify
  apply (rule equiv_type [THEN subsetD, THEN SigmaE2], assumption+)
  apply (simp add: UN_equiv_class congruent2_implies_congruent)
  apply (unfold congruent2_def equiv_def refl_on_def)
  apply (blast del: equalityI)
  done

lemma UN_equiv_class2:
  "equiv A1 r1 \<Longrightarrow> equiv A2 r2 \<Longrightarrow> congruent2 r1 r2 f \<Longrightarrow> a1 \<in> A1 \<Longrightarrow> a2 \<in> A2 \<Longrightarrow>
    (\<Union>x1 \<in> r1``{a1}. \<Union>x2 \<in> r2``{a2}. f x1 x2) = f a1 a2"
  by (simp add: UN_equiv_class congruent2_implies_congruent congruent2_implies_congruent_UN)

lemma UN_equiv_class_type2:
  "equiv A1 r1 \<Longrightarrow> equiv A2 r2 \<Longrightarrow> congruent2 r1 r2 f
    \<Longrightarrow> X1 \<in> A1//r1 \<Longrightarrow> X2 \<in> A2//r2
    \<Longrightarrow> (\<And>x1 x2. x1 \<in> A1 \<Longrightarrow> x2 \<in> A2 \<Longrightarrow> f x1 x2 \<in> B)
    \<Longrightarrow> (\<Union>x1 \<in> X1. \<Union>x2 \<in> X2. f x1 x2) \<in> B"
  apply (unfold quotient_def)
  apply clarify
  apply (blast intro: UN_equiv_class_type congruent2_implies_congruent_UN
      congruent2_implies_congruent quotientI)
  done

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
  apply (unfold congruent2_def equiv_def refl_on_def)
  apply clarify
  apply (blast intro: trans)
  done

lemma congruent2_commuteI:
  assumes equivA: "equiv A r"
    and commute: "\<And>y z. y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> f y z = f z y"
    and congt: "\<And>y z w. w \<in> A \<Longrightarrow> (y,z) \<in> r \<Longrightarrow> f w y = f w z"
  shows "f respects2 r"
  apply (rule congruent2I [OF equivA equivA])
   apply (rule commute [THEN trans])
     apply (rule_tac [3] commute [THEN trans, symmetric])
       apply (rule_tac [5] sym)
       apply (rule congt | assumption |
         erule equivA [THEN equiv_type, THEN subsetD, THEN SigmaE2])+
  done


subsection \<open>Quotients and finiteness\<close>

text \<open>Suggested by Florian Kammüller\<close>

lemma finite_quotient: "finite A \<Longrightarrow> r \<subseteq> A \<times> A \<Longrightarrow> finite (A//r)"
  \<comment> \<open>recall @{thm equiv_type}\<close>
  apply (rule finite_subset)
   apply (erule_tac [2] finite_Pow_iff [THEN iffD2])
  apply (unfold quotient_def)
  apply blast
  done

lemma finite_equiv_class: "finite A \<Longrightarrow> r \<subseteq> A \<times> A \<Longrightarrow> X \<in> A//r \<Longrightarrow> finite X"
  apply (unfold quotient_def)
  apply (rule finite_subset)
   prefer 2 apply assumption
  apply blast
  done

lemma equiv_imp_dvd_card: "finite A \<Longrightarrow> equiv A r \<Longrightarrow> \<forall>X \<in> A//r. k dvd card X \<Longrightarrow> k dvd card A"
  apply (rule Union_quotient [THEN subst [where P="\<lambda>A. k dvd card A"]])
   apply assumption
  apply (rule dvd_partition)
    prefer 3 apply (blast dest: quotient_disj)
   apply (simp_all add: Union_quotient equiv_type)
  done

lemma card_quotient_disjoint: "finite A \<Longrightarrow> inj_on (\<lambda>x. {x} // r) A \<Longrightarrow> card (A//r) = card A"
  apply (simp add:quotient_def)
  apply (subst card_UN_disjoint)
     apply assumption
    apply simp
   apply (fastforce simp add:inj_on_def)
  apply simp
  done


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
  proof clarsimp
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

lemma identity_equivp: "equivp (op =)"
  by (auto intro: equivpI reflpI sympI transpI)

lemma equivp_reflp: "equivp R \<Longrightarrow> R x x"
  by (erule equivpE, erule reflpE)

lemma equivp_symp: "equivp R \<Longrightarrow> R x y \<Longrightarrow> R y x"
  by (erule equivpE, erule sympE)

lemma equivp_transp: "equivp R \<Longrightarrow> R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  by (erule equivpE, erule transpE)

hide_const (open) proj

end
