(*  Title:      FOL/IFOL.thy
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel
*)

header {* Intuitionistic first-order logic *}

theory IFOL = Pure
files ("IFOL_lemmas.ML") ("fologic.ML") ("hypsubstdata.ML") ("intprover.ML"):


subsection {* Syntax and axiomatic basis *}

global

classes "term" < logic
defaultsort "term"

typedecl o

judgment
  Trueprop      :: "o => prop"                  ("(_)" 5)

consts
  True          :: o
  False         :: o

  (* Connectives *)

  "="           :: "['a, 'a] => o"              (infixl 50)

  Not           :: "o => o"                     ("~ _" [40] 40)
  &             :: "[o, o] => o"                (infixr 35)
  "|"           :: "[o, o] => o"                (infixr 30)
  -->           :: "[o, o] => o"                (infixr 25)
  <->           :: "[o, o] => o"                (infixr 25)

  (* Quantifiers *)

  All           :: "('a => o) => o"             (binder "ALL " 10)
  Ex            :: "('a => o) => o"             (binder "EX " 10)
  Ex1           :: "('a => o) => o"             (binder "EX! " 10)


syntax
  "_not_equal"  :: "['a, 'a] => o"              (infixl "~=" 50)
translations
  "x ~= y"      == "~ (x = y)"

syntax (xsymbols)
  Not           :: "o => o"                     ("\<not> _" [40] 40)
  "op &"        :: "[o, o] => o"                (infixr "\<and>" 35)
  "op |"        :: "[o, o] => o"                (infixr "\<or>" 30)
  "ALL "        :: "[idts, o] => o"             ("(3\<forall>_./ _)" [0, 10] 10)
  "EX "         :: "[idts, o] => o"             ("(3\<exists>_./ _)" [0, 10] 10)
  "EX! "        :: "[idts, o] => o"             ("(3\<exists>!_./ _)" [0, 10] 10)
  "_not_equal"  :: "['a, 'a] => o"              (infixl "\<noteq>" 50)
  "op -->"      :: "[o, o] => o"                (infixr "\<longrightarrow>" 25)
  "op <->"      :: "[o, o] => o"                (infixr "\<longleftrightarrow>" 25)

syntax (HTML output)
  Not           :: "o => o"                     ("\<not> _" [40] 40)


local

axioms

  (* Equality *)

  refl:         "a=a"
  subst:        "[| a=b;  P(a) |] ==> P(b)"

  (* Propositional logic *)

  conjI:        "[| P;  Q |] ==> P&Q"
  conjunct1:    "P&Q ==> P"
  conjunct2:    "P&Q ==> Q"

  disjI1:       "P ==> P|Q"
  disjI2:       "Q ==> P|Q"
  disjE:        "[| P|Q;  P ==> R;  Q ==> R |] ==> R"

  impI:         "(P ==> Q) ==> P-->Q"
  mp:           "[| P-->Q;  P |] ==> Q"

  FalseE:       "False ==> P"


  (* Definitions *)

  True_def:     "True  == False-->False"
  not_def:      "~P    == P-->False"
  iff_def:      "P<->Q == (P-->Q) & (Q-->P)"

  (* Unique existence *)

  ex1_def:      "EX! x. P(x) == EX x. P(x) & (ALL y. P(y) --> y=x)"


  (* Quantifiers *)

  allI:         "(!!x. P(x)) ==> (ALL x. P(x))"
  spec:         "(ALL x. P(x)) ==> P(x)"

  exI:          "P(x) ==> (EX x. P(x))"
  exE:          "[| EX x. P(x);  !!x. P(x) ==> R |] ==> R"

  (* Reflection *)

  eq_reflection:  "(x=y)   ==> (x==y)"
  iff_reflection: "(P<->Q) ==> (P==Q)"


subsection {* Lemmas and proof tools *}

setup Simplifier.setup
use "IFOL_lemmas.ML"

use "fologic.ML"
use "hypsubstdata.ML"
setup hypsubst_setup
use "intprover.ML"


subsection {* Intuitionistic Reasoning *}

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

ML_setup {*
  Context.>> (ContextRules.addSWrapper (fn tac => hyp_subst_tac ORELSE' tac));
*}


lemma iff_not_sym: "~ (Q <-> P) ==> ~ (P <-> Q)"
  by rules

lemmas [sym] = sym iff_sym not_sym iff_not_sym
  and [Pure.elim?] = iffD1 iffD2 impE


subsection {* Atomizing meta-level rules *}

lemma atomize_all [atomize]: "(!!x. P(x)) == Trueprop (ALL x. P(x))"
proof
  assume "!!x. P(x)"
  show "ALL x. P(x)" ..
next
  assume "ALL x. P(x)"
  thus "!!x. P(x)" ..
qed

lemma atomize_imp [atomize]: "(A ==> B) == Trueprop (A --> B)"
proof
  assume "A ==> B"
  thus "A --> B" ..
next
  assume "A --> B" and A
  thus B by (rule mp)
qed

lemma atomize_eq [atomize]: "(x == y) == Trueprop (x = y)"
proof
  assume "x == y"
  show "x = y" by (unfold prems) (rule refl)
next
  assume "x = y"
  thus "x == y" by (rule eq_reflection)
qed

lemma atomize_conj [atomize]:
  "(!!C. (A ==> B ==> PROP C) ==> PROP C) == Trueprop (A & B)"
proof
  assume "!!C. (A ==> B ==> PROP C) ==> PROP C"
  show "A & B" by (rule conjI)
next
  fix C
  assume "A & B"
  assume "A ==> B ==> PROP C"
  thus "PROP C"
  proof this
    show A by (rule conjunct1)
    show B by (rule conjunct2)
  qed
qed

lemmas [symmetric, rulify] = atomize_all atomize_imp


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

end
