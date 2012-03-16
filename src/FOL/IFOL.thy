(*  Title:      FOL/IFOL.thy
    Author:     Lawrence C Paulson and Markus Wenzel
*)

header {* Intuitionistic first-order logic *}

theory IFOL
imports Pure
uses
  "~~/src/Tools/misc_legacy.ML"
  "~~/src/Provers/splitter.ML"
  "~~/src/Provers/hypsubst.ML"
  "~~/src/Tools/IsaPlanner/zipper.ML"
  "~~/src/Tools/IsaPlanner/isand.ML"
  "~~/src/Tools/IsaPlanner/rw_tools.ML"
  "~~/src/Tools/IsaPlanner/rw_inst.ML"
  "~~/src/Tools/eqsubst.ML"
  "~~/src/Provers/quantifier1.ML"
  "~~/src/Tools/intuitionistic.ML"
  "~~/src/Tools/project_rule.ML"
  "~~/src/Tools/atomize_elim.ML"
  ("fologic.ML")
  ("intprover.ML")
begin


subsection {* Syntax and axiomatic basis *}

setup Pure_Thy.old_appl_syntax_setup

classes "term"
default_sort "term"

typedecl o

judgment
  Trueprop      :: "o => prop"                  ("(_)" 5)


subsubsection {* Equality *}

axiomatization
  eq :: "['a, 'a] => o"  (infixl "=" 50)
where
  refl:         "a=a" and
  subst:        "a=b \<Longrightarrow> P(a) \<Longrightarrow> P(b)"


subsubsection {* Propositional logic *}

axiomatization
  False :: o and
  conj :: "[o, o] => o"  (infixr "&" 35) and
  disj :: "[o, o] => o"  (infixr "|" 30) and
  imp :: "[o, o] => o"  (infixr "-->" 25)
where
  conjI: "[| P;  Q |] ==> P&Q" and
  conjunct1: "P&Q ==> P" and
  conjunct2: "P&Q ==> Q" and

  disjI1: "P ==> P|Q" and
  disjI2: "Q ==> P|Q" and
  disjE: "[| P|Q;  P ==> R;  Q ==> R |] ==> R" and

  impI: "(P ==> Q) ==> P-->Q" and
  mp: "[| P-->Q;  P |] ==> Q" and

  FalseE: "False ==> P"


subsubsection {* Quantifiers *}

axiomatization
  All :: "('a => o) => o"  (binder "ALL " 10) and
  Ex :: "('a => o) => o"  (binder "EX " 10)
where
  allI: "(!!x. P(x)) ==> (ALL x. P(x))" and
  spec: "(ALL x. P(x)) ==> P(x)" and
  exI: "P(x) ==> (EX x. P(x))" and
  exE: "[| EX x. P(x);  !!x. P(x) ==> R |] ==> R"


subsubsection {* Definitions *}

definition "True == False-->False"
definition Not ("~ _" [40] 40) where not_def: "~P == P-->False"
definition iff  (infixr "<->" 25) where "P<->Q == (P-->Q) & (Q-->P)"

definition Ex1 :: "('a => o) => o"  (binder "EX! " 10)
  where ex1_def: "EX! x. P(x) == EX x. P(x) & (ALL y. P(y) --> y=x)"

axiomatization where  -- {* Reflection, admissible *}
  eq_reflection: "(x=y) ==> (x==y)" and
  iff_reflection: "(P<->Q) ==> (P==Q)"


subsubsection {* Additional notation *}

abbreviation not_equal :: "['a, 'a] => o"  (infixl "~=" 50)
  where "x ~= y == ~ (x = y)"

notation (xsymbols)
  not_equal  (infixl "\<noteq>" 50)

notation (HTML output)
  not_equal  (infixl "\<noteq>" 50)

notation (xsymbols)
  Not  ("\<not> _" [40] 40) and
  conj  (infixr "\<and>" 35) and
  disj  (infixr "\<or>" 30) and
  All  (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  Ex1  (binder "\<exists>!" 10) and
  imp  (infixr "\<longrightarrow>" 25) and
  iff  (infixr "\<longleftrightarrow>" 25)

notation (HTML output)
  Not  ("\<not> _" [40] 40) and
  conj  (infixr "\<and>" 35) and
  disj  (infixr "\<or>" 30) and
  All  (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  Ex1  (binder "\<exists>!" 10)


subsection {* Lemmas and proof tools *}

lemmas strip = impI allI

lemma TrueI: True
  unfolding True_def by (rule impI)


(*** Sequent-style elimination rules for & --> and ALL ***)

lemma conjE:
  assumes major: "P & Q"
    and r: "[| P; Q |] ==> R"
  shows R
  apply (rule r)
   apply (rule major [THEN conjunct1])
  apply (rule major [THEN conjunct2])
  done

lemma impE:
  assumes major: "P --> Q"
    and P
  and r: "Q ==> R"
  shows R
  apply (rule r)
  apply (rule major [THEN mp])
  apply (rule `P`)
  done

lemma allE:
  assumes major: "ALL x. P(x)"
    and r: "P(x) ==> R"
  shows R
  apply (rule r)
  apply (rule major [THEN spec])
  done

(*Duplicates the quantifier; for use with eresolve_tac*)
lemma all_dupE:
  assumes major: "ALL x. P(x)"
    and r: "[| P(x); ALL x. P(x) |] ==> R"
  shows R
  apply (rule r)
   apply (rule major [THEN spec])
  apply (rule major)
  done


(*** Negation rules, which translate between ~P and P-->False ***)

lemma notI: "(P ==> False) ==> ~P"
  unfolding not_def by (erule impI)

lemma notE: "[| ~P;  P |] ==> R"
  unfolding not_def by (erule mp [THEN FalseE])

lemma rev_notE: "[| P; ~P |] ==> R"
  by (erule notE)

(*This is useful with the special implication rules for each kind of P. *)
lemma not_to_imp:
  assumes "~P"
    and r: "P --> False ==> Q"
  shows Q
  apply (rule r)
  apply (rule impI)
  apply (erule notE [OF `~P`])
  done

(* For substitution into an assumption P, reduce Q to P-->Q, substitute into
   this implication, then apply impI to move P back into the assumptions.*)
lemma rev_mp: "[| P;  P --> Q |] ==> Q"
  by (erule mp)

(*Contrapositive of an inference rule*)
lemma contrapos:
  assumes major: "~Q"
    and minor: "P ==> Q"
  shows "~P"
  apply (rule major [THEN notE, THEN notI])
  apply (erule minor)
  done


(*** Modus Ponens Tactics ***)

(*Finds P-->Q and P in the assumptions, replaces implication by Q *)
ML {*
  fun mp_tac i = eresolve_tac [@{thm notE}, @{thm impE}] i  THEN  assume_tac i
  fun eq_mp_tac i = eresolve_tac [@{thm notE}, @{thm impE}] i  THEN  eq_assume_tac i
*}


(*** If-and-only-if ***)

lemma iffI: "[| P ==> Q; Q ==> P |] ==> P<->Q"
  apply (unfold iff_def)
  apply (rule conjI)
   apply (erule impI)
  apply (erule impI)
  done


(*Observe use of rewrite_rule to unfold "<->" in meta-assumptions (prems) *)
lemma iffE:
  assumes major: "P <-> Q"
    and r: "P-->Q ==> Q-->P ==> R"
  shows R
  apply (insert major, unfold iff_def)
  apply (erule conjE)
  apply (erule r)
  apply assumption
  done

(* Destruct rules for <-> similar to Modus Ponens *)

lemma iffD1: "[| P <-> Q;  P |] ==> Q"
  apply (unfold iff_def)
  apply (erule conjunct1 [THEN mp])
  apply assumption
  done

lemma iffD2: "[| P <-> Q;  Q |] ==> P"
  apply (unfold iff_def)
  apply (erule conjunct2 [THEN mp])
  apply assumption
  done

lemma rev_iffD1: "[| P; P <-> Q |] ==> Q"
  apply (erule iffD1)
  apply assumption
  done

lemma rev_iffD2: "[| Q; P <-> Q |] ==> P"
  apply (erule iffD2)
  apply assumption
  done

lemma iff_refl: "P <-> P"
  by (rule iffI)

lemma iff_sym: "Q <-> P ==> P <-> Q"
  apply (erule iffE)
  apply (rule iffI)
  apply (assumption | erule mp)+
  done

lemma iff_trans: "[| P <-> Q;  Q<-> R |] ==> P <-> R"
  apply (rule iffI)
  apply (assumption | erule iffE | erule (1) notE impE)+
  done


(*** Unique existence.  NOTE THAT the following 2 quantifications
   EX!x such that [EX!y such that P(x,y)]     (sequential)
   EX!x,y such that P(x,y)                    (simultaneous)
 do NOT mean the same thing.  The parser treats EX!x y.P(x,y) as sequential.
***)

lemma ex1I:
  "P(a) \<Longrightarrow> (!!x. P(x) ==> x=a) \<Longrightarrow> EX! x. P(x)"
  apply (unfold ex1_def)
  apply (assumption | rule exI conjI allI impI)+
  done

(*Sometimes easier to use: the premises have no shared variables.  Safe!*)
lemma ex_ex1I:
  "EX x. P(x) \<Longrightarrow> (!!x y. [| P(x); P(y) |] ==> x=y) \<Longrightarrow> EX! x. P(x)"
  apply (erule exE)
  apply (rule ex1I)
   apply assumption
  apply assumption
  done

lemma ex1E:
  "EX! x. P(x) \<Longrightarrow> (!!x. [| P(x);  ALL y. P(y) --> y=x |] ==> R) \<Longrightarrow> R"
  apply (unfold ex1_def)
  apply (assumption | erule exE conjE)+
  done


(*** <-> congruence rules for simplification ***)

(*Use iffE on a premise.  For conj_cong, imp_cong, all_cong, ex_cong*)
ML {*
  fun iff_tac prems i =
    resolve_tac (prems RL @{thms iffE}) i THEN
    REPEAT1 (eresolve_tac [@{thm asm_rl}, @{thm mp}] i)
*}

lemma conj_cong:
  assumes "P <-> P'"
    and "P' ==> Q <-> Q'"
  shows "(P&Q) <-> (P'&Q')"
  apply (insert assms)
  apply (assumption | rule iffI conjI | erule iffE conjE mp |
    tactic {* iff_tac @{thms assms} 1 *})+
  done

(*Reversed congruence rule!   Used in ZF/Order*)
lemma conj_cong2:
  assumes "P <-> P'"
    and "P' ==> Q <-> Q'"
  shows "(Q&P) <-> (Q'&P')"
  apply (insert assms)
  apply (assumption | rule iffI conjI | erule iffE conjE mp |
    tactic {* iff_tac @{thms assms} 1 *})+
  done

lemma disj_cong:
  assumes "P <-> P'" and "Q <-> Q'"
  shows "(P|Q) <-> (P'|Q')"
  apply (insert assms)
  apply (erule iffE disjE disjI1 disjI2 | assumption | rule iffI | erule (1) notE impE)+
  done

lemma imp_cong:
  assumes "P <-> P'"
    and "P' ==> Q <-> Q'"
  shows "(P-->Q) <-> (P'-->Q')"
  apply (insert assms)
  apply (assumption | rule iffI impI | erule iffE | erule (1) notE impE |
    tactic {* iff_tac @{thms assms} 1 *})+
  done

lemma iff_cong: "[| P <-> P'; Q <-> Q' |] ==> (P<->Q) <-> (P'<->Q')"
  apply (erule iffE | assumption | rule iffI | erule (1) notE impE)+
  done

lemma not_cong: "P <-> P' ==> ~P <-> ~P'"
  apply (assumption | rule iffI notI | erule (1) notE impE | erule iffE notE)+
  done

lemma all_cong:
  assumes "!!x. P(x) <-> Q(x)"
  shows "(ALL x. P(x)) <-> (ALL x. Q(x))"
  apply (assumption | rule iffI allI | erule (1) notE impE | erule allE |
    tactic {* iff_tac @{thms assms} 1 *})+
  done

lemma ex_cong:
  assumes "!!x. P(x) <-> Q(x)"
  shows "(EX x. P(x)) <-> (EX x. Q(x))"
  apply (erule exE | assumption | rule iffI exI | erule (1) notE impE |
    tactic {* iff_tac @{thms assms} 1 *})+
  done

lemma ex1_cong:
  assumes "!!x. P(x) <-> Q(x)"
  shows "(EX! x. P(x)) <-> (EX! x. Q(x))"
  apply (erule ex1E spec [THEN mp] | assumption | rule iffI ex1I | erule (1) notE impE |
    tactic {* iff_tac @{thms assms} 1 *})+
  done

(*** Equality rules ***)

lemma sym: "a=b ==> b=a"
  apply (erule subst)
  apply (rule refl)
  done

lemma trans: "[| a=b;  b=c |] ==> a=c"
  apply (erule subst, assumption)
  done

(**  **)
lemma not_sym: "b ~= a ==> a ~= b"
  apply (erule contrapos)
  apply (erule sym)
  done
  
(* Two theorms for rewriting only one instance of a definition:
   the first for definitions of formulae and the second for terms *)

lemma def_imp_iff: "(A == B) ==> A <-> B"
  apply unfold
  apply (rule iff_refl)
  done

lemma meta_eq_to_obj_eq: "(A == B) ==> A = B"
  apply unfold
  apply (rule refl)
  done

lemma meta_eq_to_iff: "x==y ==> x<->y"
  by unfold (rule iff_refl)

(*substitution*)
lemma ssubst: "[| b = a; P(a) |] ==> P(b)"
  apply (drule sym)
  apply (erule (1) subst)
  done

(*A special case of ex1E that would otherwise need quantifier expansion*)
lemma ex1_equalsE:
    "[| EX! x. P(x);  P(a);  P(b) |] ==> a=b"
  apply (erule ex1E)
  apply (rule trans)
   apply (rule_tac [2] sym)
   apply (assumption | erule spec [THEN mp])+
  done

(** Polymorphic congruence rules **)

lemma subst_context: "[| a=b |]  ==>  t(a)=t(b)"
  apply (erule ssubst)
  apply (rule refl)
  done

lemma subst_context2: "[| a=b;  c=d |]  ==>  t(a,c)=t(b,d)"
  apply (erule ssubst)+
  apply (rule refl)
  done

lemma subst_context3: "[| a=b;  c=d;  e=f |]  ==>  t(a,c,e)=t(b,d,f)"
  apply (erule ssubst)+
  apply (rule refl)
  done

(*Useful with eresolve_tac for proving equalties from known equalities.
        a = b
        |   |
        c = d   *)
lemma box_equals: "[| a=b;  a=c;  b=d |] ==> c=d"
  apply (rule trans)
   apply (rule trans)
    apply (rule sym)
    apply assumption+
  done

(*Dual of box_equals: for proving equalities backwards*)
lemma simp_equals: "[| a=c;  b=d;  c=d |] ==> a=b"
  apply (rule trans)
   apply (rule trans)
    apply assumption+
  apply (erule sym)
  done

(** Congruence rules for predicate letters **)

lemma pred1_cong: "a=a' ==> P(a) <-> P(a')"
  apply (rule iffI)
   apply (erule (1) subst)
  apply (erule (1) ssubst)
  done

lemma pred2_cong: "[| a=a';  b=b' |] ==> P(a,b) <-> P(a',b')"
  apply (rule iffI)
   apply (erule subst)+
   apply assumption
  apply (erule ssubst)+
  apply assumption
  done

lemma pred3_cong: "[| a=a';  b=b';  c=c' |] ==> P(a,b,c) <-> P(a',b',c')"
  apply (rule iffI)
   apply (erule subst)+
   apply assumption
  apply (erule ssubst)+
  apply assumption
  done

(*special case for the equality predicate!*)
lemma eq_cong: "[| a = a'; b = b' |] ==> a = b <-> a' = b'"
  apply (erule (1) pred2_cong)
  done


(*** Simplifications of assumed implications.
     Roy Dyckhoff has proved that conj_impE, disj_impE, and imp_impE
     used with mp_tac (restricted to atomic formulae) is COMPLETE for 
     intuitionistic propositional logic.  See
   R. Dyckhoff, Contraction-free sequent calculi for intuitionistic logic
    (preprint, University of St Andrews, 1991)  ***)

lemma conj_impE:
  assumes major: "(P&Q)-->S"
    and r: "P-->(Q-->S) ==> R"
  shows R
  by (assumption | rule conjI impI major [THEN mp] r)+

lemma disj_impE:
  assumes major: "(P|Q)-->S"
    and r: "[| P-->S; Q-->S |] ==> R"
  shows R
  by (assumption | rule disjI1 disjI2 impI major [THEN mp] r)+

(*Simplifies the implication.  Classical version is stronger. 
  Still UNSAFE since Q must be provable -- backtracking needed.  *)
lemma imp_impE:
  assumes major: "(P-->Q)-->S"
    and r1: "[| P; Q-->S |] ==> Q"
    and r2: "S ==> R"
  shows R
  by (assumption | rule impI major [THEN mp] r1 r2)+

(*Simplifies the implication.  Classical version is stronger. 
  Still UNSAFE since ~P must be provable -- backtracking needed.  *)
lemma not_impE:
  "~P --> S \<Longrightarrow> (P ==> False) \<Longrightarrow> (S ==> R) \<Longrightarrow> R"
  apply (drule mp)
   apply (rule notI)
   apply assumption
  apply assumption
  done

(*Simplifies the implication.   UNSAFE.  *)
lemma iff_impE:
  assumes major: "(P<->Q)-->S"
    and r1: "[| P; Q-->S |] ==> Q"
    and r2: "[| Q; P-->S |] ==> P"
    and r3: "S ==> R"
  shows R
  apply (assumption | rule iffI impI major [THEN mp] r1 r2 r3)+
  done

(*What if (ALL x.~~P(x)) --> ~~(ALL x.P(x)) is an assumption? UNSAFE*)
lemma all_impE:
  assumes major: "(ALL x. P(x))-->S"
    and r1: "!!x. P(x)"
    and r2: "S ==> R"
  shows R
  apply (rule allI impI major [THEN mp] r1 r2)+
  done

(*Unsafe: (EX x.P(x))-->S  is equivalent to  ALL x.P(x)-->S.  *)
lemma ex_impE:
  assumes major: "(EX x. P(x))-->S"
    and r: "P(x)-->S ==> R"
  shows R
  apply (assumption | rule exI impI major [THEN mp] r)+
  done

(*** Courtesy of Krzysztof Grabczewski ***)

lemma disj_imp_disj:
  "P|Q \<Longrightarrow> (P==>R) \<Longrightarrow> (Q==>S) \<Longrightarrow> R|S"
  apply (erule disjE)
  apply (rule disjI1) apply assumption
  apply (rule disjI2) apply assumption
  done

ML {*
structure Project_Rule = Project_Rule
(
  val conjunct1 = @{thm conjunct1}
  val conjunct2 = @{thm conjunct2}
  val mp = @{thm mp}
)
*}

use "fologic.ML"

lemma thin_refl: "[|x=x; PROP W|] ==> PROP W" .

ML {*
structure Hypsubst = Hypsubst
(
  val dest_eq = FOLogic.dest_eq
  val dest_Trueprop = FOLogic.dest_Trueprop
  val dest_imp = FOLogic.dest_imp
  val eq_reflection = @{thm eq_reflection}
  val rev_eq_reflection = @{thm meta_eq_to_obj_eq}
  val imp_intr = @{thm impI}
  val rev_mp = @{thm rev_mp}
  val subst = @{thm subst}
  val sym = @{thm sym}
  val thin_refl = @{thm thin_refl}
);
open Hypsubst;
*}

setup hypsubst_setup
use "intprover.ML"


subsection {* Intuitionistic Reasoning *}

setup {* Intuitionistic.method_setup @{binding iprover} *}

lemma impE':
  assumes 1: "P --> Q"
    and 2: "Q ==> R"
    and 3: "P --> Q ==> P"
  shows R
proof -
  from 3 and 1 have P .
  with 1 have Q by (rule impE)
  with 2 show R .
qed

lemma allE':
  assumes 1: "ALL x. P(x)"
    and 2: "P(x) ==> ALL x. P(x) ==> Q"
  shows Q
proof -
  from 1 have "P(x)" by (rule spec)
  from this and 1 show Q by (rule 2)
qed

lemma notE':
  assumes 1: "~ P"
    and 2: "~ P ==> P"
  shows R
proof -
  from 2 and 1 have P .
  with 1 show R by (rule notE)
qed

lemmas [Pure.elim!] = disjE iffE FalseE conjE exE
  and [Pure.intro!] = iffI conjI impI TrueI notI allI refl
  and [Pure.elim 2] = allE notE' impE'
  and [Pure.intro] = exI disjI2 disjI1

setup {* Context_Rules.addSWrapper (fn tac => hyp_subst_tac ORELSE' tac) *}


lemma iff_not_sym: "~ (Q <-> P) ==> ~ (P <-> Q)"
  by iprover

lemmas [sym] = sym iff_sym not_sym iff_not_sym
  and [Pure.elim?] = iffD1 iffD2 impE


lemma eq_commute: "a=b <-> b=a"
apply (rule iffI) 
apply (erule sym)+
done


subsection {* Atomizing meta-level rules *}

lemma atomize_all [atomize]: "(!!x. P(x)) == Trueprop (ALL x. P(x))"
proof
  assume "!!x. P(x)"
  then show "ALL x. P(x)" ..
next
  assume "ALL x. P(x)"
  then show "!!x. P(x)" ..
qed

lemma atomize_imp [atomize]: "(A ==> B) == Trueprop (A --> B)"
proof
  assume "A ==> B"
  then show "A --> B" ..
next
  assume "A --> B" and A
  then show B by (rule mp)
qed

lemma atomize_eq [atomize]: "(x == y) == Trueprop (x = y)"
proof
  assume "x == y"
  show "x = y" unfolding `x == y` by (rule refl)
next
  assume "x = y"
  then show "x == y" by (rule eq_reflection)
qed

lemma atomize_iff [atomize]: "(A == B) == Trueprop (A <-> B)"
proof
  assume "A == B"
  show "A <-> B" unfolding `A == B` by (rule iff_refl)
next
  assume "A <-> B"
  then show "A == B" by (rule iff_reflection)
qed

lemma atomize_conj [atomize]: "(A &&& B) == Trueprop (A & B)"
proof
  assume conj: "A &&& B"
  show "A & B"
  proof (rule conjI)
    from conj show A by (rule conjunctionD1)
    from conj show B by (rule conjunctionD2)
  qed
next
  assume conj: "A & B"
  show "A &&& B"
  proof -
    from conj show A ..
    from conj show B ..
  qed
qed

lemmas [symmetric, rulify] = atomize_all atomize_imp
  and [symmetric, defn] = atomize_all atomize_imp atomize_eq atomize_iff


subsection {* Atomizing elimination rules *}

setup AtomizeElim.setup

lemma atomize_exL[atomize_elim]: "(!!x. P(x) ==> Q) == ((EX x. P(x)) ==> Q)"
by rule iprover+

lemma atomize_conjL[atomize_elim]: "(A ==> B ==> C) == (A & B ==> C)"
by rule iprover+

lemma atomize_disjL[atomize_elim]: "((A ==> C) ==> (B ==> C) ==> C) == ((A | B ==> C) ==> C)"
by rule iprover+

lemma atomize_elimL[atomize_elim]: "(!!B. (A ==> B) ==> B) == Trueprop(A)" ..


subsection {* Calculational rules *}

lemma forw_subst: "a = b ==> P(b) ==> P(a)"
  by (rule ssubst)

lemma back_subst: "P(a) ==> a = b ==> P(b)"
  by (rule subst)

text {*
  Note that this list of rules is in reverse order of priorities.
*}

lemmas basic_trans_rules [trans] =
  forw_subst
  back_subst
  rev_mp
  mp
  trans

subsection {* ``Let'' declarations *}

nonterminal letbinds and letbind

definition Let :: "['a::{}, 'a => 'b] => ('b::{})" where
    "Let(s, f) == f(s)"

syntax
  "_bind"       :: "[pttrn, 'a] => letbind"           ("(2_ =/ _)" 10)
  ""            :: "letbind => letbinds"              ("_")
  "_binds"      :: "[letbind, letbinds] => letbinds"  ("_;/ _")
  "_Let"        :: "[letbinds, 'a] => 'a"             ("(let (_)/ in (_))" 10)

translations
  "_Let(_binds(b, bs), e)"  == "_Let(b, _Let(bs, e))"
  "let x = a in e"          == "CONST Let(a, %x. e)"


lemma LetI: 
  assumes "!!x. x=t ==> P(u(x))"
  shows "P(let x=t in u(x))"
  apply (unfold Let_def)
  apply (rule refl [THEN assms])
  done


subsection {* Intuitionistic simplification rules *}

lemma conj_simps:
  "P & True <-> P"
  "True & P <-> P"
  "P & False <-> False"
  "False & P <-> False"
  "P & P <-> P"
  "P & P & Q <-> P & Q"
  "P & ~P <-> False"
  "~P & P <-> False"
  "(P & Q) & R <-> P & (Q & R)"
  by iprover+

lemma disj_simps:
  "P | True <-> True"
  "True | P <-> True"
  "P | False <-> P"
  "False | P <-> P"
  "P | P <-> P"
  "P | P | Q <-> P | Q"
  "(P | Q) | R <-> P | (Q | R)"
  by iprover+

lemma not_simps:
  "~(P|Q)  <-> ~P & ~Q"
  "~ False <-> True"
  "~ True <-> False"
  by iprover+

lemma imp_simps:
  "(P --> False) <-> ~P"
  "(P --> True) <-> True"
  "(False --> P) <-> True"
  "(True --> P) <-> P"
  "(P --> P) <-> True"
  "(P --> ~P) <-> ~P"
  by iprover+

lemma iff_simps:
  "(True <-> P) <-> P"
  "(P <-> True) <-> P"
  "(P <-> P) <-> True"
  "(False <-> P) <-> ~P"
  "(P <-> False) <-> ~P"
  by iprover+

(*The x=t versions are needed for the simplification procedures*)
lemma quant_simps:
  "!!P. (ALL x. P) <-> P"
  "(ALL x. x=t --> P(x)) <-> P(t)"
  "(ALL x. t=x --> P(x)) <-> P(t)"
  "!!P. (EX x. P) <-> P"
  "EX x. x=t"
  "EX x. t=x"
  "(EX x. x=t & P(x)) <-> P(t)"
  "(EX x. t=x & P(x)) <-> P(t)"
  by iprover+

(*These are NOT supplied by default!*)
lemma distrib_simps:
  "P & (Q | R) <-> P&Q | P&R"
  "(Q | R) & P <-> Q&P | R&P"
  "(P | Q --> R) <-> (P --> R) & (Q --> R)"
  by iprover+


text {* Conversion into rewrite rules *}

lemma P_iff_F: "~P ==> (P <-> False)" by iprover
lemma iff_reflection_F: "~P ==> (P == False)" by (rule P_iff_F [THEN iff_reflection])

lemma P_iff_T: "P ==> (P <-> True)" by iprover
lemma iff_reflection_T: "P ==> (P == True)" by (rule P_iff_T [THEN iff_reflection])


text {* More rewrite rules *}

lemma conj_commute: "P&Q <-> Q&P" by iprover
lemma conj_left_commute: "P&(Q&R) <-> Q&(P&R)" by iprover
lemmas conj_comms = conj_commute conj_left_commute

lemma disj_commute: "P|Q <-> Q|P" by iprover
lemma disj_left_commute: "P|(Q|R) <-> Q|(P|R)" by iprover
lemmas disj_comms = disj_commute disj_left_commute

lemma conj_disj_distribL: "P&(Q|R) <-> (P&Q | P&R)" by iprover
lemma conj_disj_distribR: "(P|Q)&R <-> (P&R | Q&R)" by iprover

lemma disj_conj_distribL: "P|(Q&R) <-> (P|Q) & (P|R)" by iprover
lemma disj_conj_distribR: "(P&Q)|R <-> (P|R) & (Q|R)" by iprover

lemma imp_conj_distrib: "(P --> (Q&R)) <-> (P-->Q) & (P-->R)" by iprover
lemma imp_conj: "((P&Q)-->R)   <-> (P --> (Q --> R))" by iprover
lemma imp_disj: "(P|Q --> R)   <-> (P-->R) & (Q-->R)" by iprover

lemma de_Morgan_disj: "(~(P | Q)) <-> (~P & ~Q)" by iprover

lemma not_ex: "(~ (EX x. P(x))) <-> (ALL x.~P(x))" by iprover
lemma imp_ex: "((EX x. P(x)) --> Q) <-> (ALL x. P(x) --> Q)" by iprover

lemma ex_disj_distrib:
  "(EX x. P(x) | Q(x)) <-> ((EX x. P(x)) | (EX x. Q(x)))" by iprover

lemma all_conj_distrib:
  "(ALL x. P(x) & Q(x)) <-> ((ALL x. P(x)) & (ALL x. Q(x)))" by iprover

end
