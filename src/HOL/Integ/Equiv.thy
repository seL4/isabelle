(*  Title:      HOL/Integ/Equiv.thy
    ID:         $Id$
    Authors:    Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

header {* Equivalence relations in Higher-Order Set Theory *}

theory Equiv = Relation + Finite_Set:

subsection {* Equiv relations *}

locale equiv =
  fixes A and r
  assumes refl: "refl A r"
    and sym: "sym r"
    and trans: "trans r"

text {*
  Suppes, Theorem 70: @{text r} is an equiv relation iff @{text "r\<inverse> O
  r = r"}.

  First half: @{text "equiv A r ==> r\<inverse> O r = r"}.
*}

lemma sym_trans_comp_subset:
    "sym r ==> trans r ==> r\<inverse> O r \<subseteq> r"
  by (unfold trans_def sym_def converse_def) blast

lemma refl_comp_subset: "refl A r ==> r \<subseteq> r\<inverse> O r"
  by (unfold refl_def) blast

lemma equiv_comp_eq: "equiv A r ==> r\<inverse> O r = r"
  apply (unfold equiv_def)
  apply clarify
  apply (rule equalityI)
   apply (rules intro: sym_trans_comp_subset refl_comp_subset)+
  done

text {*
  Second half.
*}

lemma comp_equivI:
    "r\<inverse> O r = r ==> Domain r = A ==> equiv A r"
  apply (unfold equiv_def refl_def sym_def trans_def)
  apply (erule equalityE)
  apply (subgoal_tac "\<forall>x y. (x, y) \<in> r --> (y, x) \<in> r")
   apply fast
  apply fast
  done


subsection {* Equivalence classes *}

lemma equiv_class_subset:
  "equiv A r ==> (a, b) \<in> r ==> r``{a} \<subseteq> r``{b}"
  -- {* lemma for the next result *}
  by (unfold equiv_def trans_def sym_def) blast

lemma equiv_class_eq: "equiv A r ==> (a, b) \<in> r ==> r``{a} = r``{b}"
  apply (assumption | rule equalityI equiv_class_subset)+
  apply (unfold equiv_def sym_def)
  apply blast
  done

lemma equiv_class_self: "equiv A r ==> a \<in> A ==> a \<in> r``{a}"
  by (unfold equiv_def refl_def) blast

lemma subset_equiv_class:
    "equiv A r ==> r``{b} \<subseteq> r``{a} ==> b \<in> A ==> (a,b) \<in> r"
  -- {* lemma for the next result *}
  by (unfold equiv_def refl_def) blast

lemma eq_equiv_class:
    "r``{a} = r``{b} ==> equiv A r ==> b \<in> A ==> (a, b) \<in> r"
  by (rules intro: equalityD2 subset_equiv_class)

lemma equiv_class_nondisjoint:
    "equiv A r ==> x \<in> (r``{a} \<inter> r``{b}) ==> (a, b) \<in> r"
  by (unfold equiv_def trans_def sym_def) blast

lemma equiv_type: "equiv A r ==> r \<subseteq> A \<times> A"
  by (unfold equiv_def refl_def) blast

lemma equiv_class_eq_iff:
  "equiv A r ==> ((x, y) \<in> r) = (r``{x} = r``{y} & x \<in> A & y \<in> A)"
  by (blast intro!: equiv_class_eq dest: eq_equiv_class equiv_type)

lemma eq_equiv_class_iff:
  "equiv A r ==> x \<in> A ==> y \<in> A ==> (r``{x} = r``{y}) = ((x, y) \<in> r)"
  by (blast intro!: equiv_class_eq dest: eq_equiv_class equiv_type)


subsection {* Quotients *}

constdefs
  quotient :: "['a set, ('a*'a) set] => 'a set set"  (infixl "'/'/" 90)
  "A//r == \<Union>x \<in> A. {r``{x}}"  -- {* set of equiv classes *}

lemma quotientI: "x \<in> A ==> r``{x} \<in> A//r"
  by (unfold quotient_def) blast

lemma quotientE:
  "X \<in> A//r ==> (!!x. X = r``{x} ==> x \<in> A ==> P) ==> P"
  by (unfold quotient_def) blast

lemma Union_quotient: "equiv A r ==> Union (A//r) = A"
  by (unfold equiv_def refl_def quotient_def) blast

lemma quotient_disj:
  "equiv A r ==> X \<in> A//r ==> Y \<in> A//r ==> X = Y | (X \<inter> Y = {})"
  apply (unfold quotient_def)
  apply clarify
  apply (rule equiv_class_eq)
   apply assumption
  apply (unfold equiv_def trans_def sym_def)
  apply blast
  done


subsection {* Defining unary operations upon equivalence classes *}

locale congruent =
  fixes r and b
  assumes congruent: "(y, z) \<in> r ==> b y = b z"

lemma UN_constant_eq: "a \<in> A ==> \<forall>y \<in> A. b y = c ==> (\<Union>y \<in> A. b(y))=c"
  -- {* lemma required to prove @{text UN_equiv_class} *}
  by auto

lemma UN_equiv_class:
  "equiv A r ==> congruent r b ==> a \<in> A
    ==> (\<Union>x \<in> r``{a}. b x) = b a"
  -- {* Conversion rule *}
  apply (rule equiv_class_self [THEN UN_constant_eq], assumption+)
  apply (unfold equiv_def congruent_def sym_def)
  apply (blast del: equalityI)
  done

lemma UN_equiv_class_type:
  "equiv A r ==> congruent r b ==> X \<in> A//r ==>
    (!!x. x \<in> A ==> b x : B) ==> (\<Union>x \<in> X. b x) : B"
  apply (unfold quotient_def)
  apply clarify
  apply (subst UN_equiv_class)
     apply auto
  done

text {*
  Sufficient conditions for injectiveness.  Could weaken premises!
  major premise could be an inclusion; bcong could be @{text "!!y. y \<in>
  A ==> b y \<in> B"}.
*}

lemma UN_equiv_class_inject:
  "equiv A r ==> congruent r b ==>
    (\<Union>x \<in> X. b x) = (\<Union>y \<in> Y. b y) ==> X \<in> A//r ==> Y \<in> A//r
    ==> (!!x y. x \<in> A ==> y \<in> A ==> b x = b y ==> (x, y) \<in> r)
    ==> X = Y"
  apply (unfold quotient_def)
  apply clarify
  apply (rule equiv_class_eq)
   apply assumption
  apply (subgoal_tac "b x = b xa")
   apply blast
  apply (erule box_equals)
   apply (assumption | rule UN_equiv_class)+
  done


subsection {* Defining binary operations upon equivalence classes *}

locale congruent2 =
  fixes r and b
  assumes congruent2:
    "(y1, z1) \<in> r ==> (y2, z2) \<in> r ==> b y1 y2 = b z1 z2"

lemma congruent2_implies_congruent:
    "equiv A r ==> congruent2 r b ==> a \<in> A ==> congruent r (b a)"
  by (unfold congruent_def congruent2_def equiv_def refl_def) blast

lemma congruent2_implies_congruent_UN:
  "equiv A r ==> congruent2 r b ==> a \<in> A ==>
    congruent r (\<lambda>x1. \<Union>x2 \<in> r``{a}. b x1 x2)"
  apply (unfold congruent_def)
  apply clarify
  apply (rule equiv_type [THEN subsetD, THEN SigmaE2], assumption+)
  apply (simp add: UN_equiv_class congruent2_implies_congruent)
  apply (unfold congruent2_def equiv_def refl_def)
  apply (blast del: equalityI)
  done

lemma UN_equiv_class2:
  "equiv A r ==> congruent2 r b ==> a1 \<in> A ==> a2 \<in> A
    ==> (\<Union>x1 \<in> r``{a1}. \<Union>x2 \<in> r``{a2}. b x1 x2) = b a1 a2"
  by (simp add: UN_equiv_class congruent2_implies_congruent
    congruent2_implies_congruent_UN)

lemma UN_equiv_class_type2:
  "equiv A r ==> congruent2 r b ==> X1 \<in> A//r ==> X2 \<in> A//r
    ==> (!!x1 x2. x1 \<in> A ==> x2 \<in> A ==> b x1 x2 \<in> B)
    ==> (\<Union>x1 \<in> X1. \<Union>x2 \<in> X2. b x1 x2) \<in> B"
  apply (unfold quotient_def)
  apply clarify
  apply (blast intro: UN_equiv_class_type congruent2_implies_congruent_UN
    congruent2_implies_congruent quotientI)
  done

lemma UN_UN_split_split_eq:
  "(\<Union>(x1, x2) \<in> X. \<Union>(y1, y2) \<in> Y. A x1 x2 y1 y2) =
    (\<Union>x \<in> X. \<Union>y \<in> Y. (\<lambda>(x1, x2). (\<lambda>(y1, y2). A x1 x2 y1 y2) y) x)"
  -- {* Allows a natural expression of binary operators, *}
  -- {* without explicit calls to @{text split} *}
  by auto

lemma congruent2I:
  "equiv A r
    ==> (!!y z w. w \<in> A ==> (y, z) \<in> r ==> b y w = b z w)
    ==> (!!y z w. w \<in> A ==> (y, z) \<in> r ==> b w y = b w z)
    ==> congruent2 r b"
  -- {* Suggested by John Harrison -- the two subproofs may be *}
  -- {* \emph{much} simpler than the direct proof. *}
  apply (unfold congruent2_def equiv_def refl_def)
  apply clarify
  apply (blast intro: trans)
  done

lemma congruent2_commuteI:
  assumes equivA: "equiv A r"
    and commute: "!!y z. y \<in> A ==> z \<in> A ==> b y z = b z y"
    and congt: "!!y z w. w \<in> A ==> (y, z) \<in> r ==> b w y = b w z"
  shows "congruent2 r b"
  apply (rule equivA [THEN congruent2I])
   apply (rule commute [THEN trans])
     apply (rule_tac [3] commute [THEN trans, symmetric])
       apply (rule_tac [5] sym)
       apply (assumption | rule congt |
         erule equivA [THEN equiv_type, THEN subsetD, THEN SigmaE2])+
  done


subsection {* Cardinality results *}

text {* (suggested by Florian Kammüller) *}

lemma finite_quotient: "finite A ==> r \<subseteq> A \<times> A ==> finite (A//r)"
  -- {* recall @{thm equiv_type} *}
  apply (rule finite_subset)
   apply (erule_tac [2] finite_Pow_iff [THEN iffD2])
  apply (unfold quotient_def)
  apply blast
  done

lemma finite_equiv_class:
  "finite A ==> r \<subseteq> A \<times> A ==> X \<in> A//r ==> finite X"
  apply (unfold quotient_def)
  apply (rule finite_subset)
   prefer 2 apply assumption
  apply blast
  done

lemma equiv_imp_dvd_card:
  "finite A ==> equiv A r ==> \<forall>X \<in> A//r. k dvd card X
    ==> k dvd card A"
  apply (rule Union_quotient [THEN subst])
   apply assumption
  apply (rule dvd_partition)
     prefer 4 apply (blast dest: quotient_disj)
    apply (simp_all add: Union_quotient equiv_type finite_quotient)
  done

ML
{*

(* legacy ML bindings *)

val UN_UN_split_split_eq = thm "UN_UN_split_split_eq";
val UN_constant_eq = thm "UN_constant_eq";
val UN_equiv_class = thm "UN_equiv_class";
val UN_equiv_class2 = thm "UN_equiv_class2";
val UN_equiv_class_inject = thm "UN_equiv_class_inject";
val UN_equiv_class_type = thm "UN_equiv_class_type";
val UN_equiv_class_type2 = thm "UN_equiv_class_type2";
val Union_quotient = thm "Union_quotient";
val comp_equivI = thm "comp_equivI";
val congruent2I = thm "congruent2I";
val congruent2_commuteI = thm "congruent2_commuteI";
val congruent2_def = thm "congruent2_def";
val congruent2_implies_congruent = thm "congruent2_implies_congruent";
val congruent2_implies_congruent_UN = thm "congruent2_implies_congruent_UN";
val congruent_def = thm "congruent_def";
val eq_equiv_class = thm "eq_equiv_class";
val eq_equiv_class_iff = thm "eq_equiv_class_iff";
val equiv_class_eq = thm "equiv_class_eq";
val equiv_class_eq_iff = thm "equiv_class_eq_iff";
val equiv_class_nondisjoint = thm "equiv_class_nondisjoint";
val equiv_class_self = thm "equiv_class_self";
val equiv_class_subset = thm "equiv_class_subset";
val equiv_comp_eq = thm "equiv_comp_eq";
val equiv_def = thm "equiv_def";
val equiv_imp_dvd_card = thm "equiv_imp_dvd_card";
val equiv_type = thm "equiv_type";
val finite_equiv_class = thm "finite_equiv_class";
val finite_quotient = thm "finite_quotient";
val quotientE = thm "quotientE";
val quotientI = thm "quotientI";
val quotient_def = thm "quotient_def";
val quotient_disj = thm "quotient_disj";
val refl_comp_subset = thm "refl_comp_subset";
val subset_equiv_class = thm "subset_equiv_class";
val sym_trans_comp_subset = thm "sym_trans_comp_subset";
*}

end
