(*  Title:      FOL/FOL.thy
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

Classical first-order logic.

This may serve as a good example of initializing all the tools and
packages required for a reasonable working environment.  Please go
elsewhere to see actual applications!
*)

theory FOL = IFOL
files
  ("FOL_lemmas1.ML") ("cladata.ML") ("blastdata.ML")
  ("simpdata.ML") ("FOL_lemmas2.ML"):


subsection {* The classical axiom *}

axioms
  classical: "(~P ==> P) ==> P"


subsection {* Setup of several proof tools *}

use "FOL_lemmas1.ML"

lemma atomize_all: "(!!x. P(x)) == Trueprop (ALL x. P(x))"
proof (rule equal_intr_rule)
  assume "!!x. P(x)"
  show "ALL x. P(x)" by (rule allI)
next
  assume "ALL x. P(x)"
  thus "!!x. P(x)" by (rule allE)
qed

lemma atomize_imp: "(A ==> B) == Trueprop (A --> B)"
proof (rule equal_intr_rule)
  assume r: "A ==> B"
  show "A --> B" by (rule impI) (rule r)
next
  assume "A --> B" and A
  thus B by (rule mp)
qed

lemma atomize_eq: "(x == y) == Trueprop (x = y)"
proof (rule equal_intr_rule)
  assume "x == y"
  show "x = y" by (unfold prems) (rule refl)
next
  assume "x = y"
  thus "x == y" by (rule eq_reflection)
qed

lemmas atomize = atomize_all atomize_imp
lemmas atomize' = atomize atomize_eq

use "cladata.ML"
setup Cla.setup
setup clasetup

use "blastdata.ML"
setup Blast.setup
use "FOL_lemmas2.ML"

use "simpdata.ML"
setup simpsetup
setup "Simplifier.method_setup Splitter.split_modifiers"
setup Splitter.setup
setup Clasimp.setup
setup Rulify.setup


subsection {* Calculational rules *}

lemma forw_subst: "a = b ==> P(b) ==> P(a)"
  by (rule ssubst)

lemma back_subst: "P(a) ==> a = b ==> P(b)"
  by (rule subst)

text {*
  Note that this list of rules is in reverse order of priorities.
*}

lemmas trans_rules [trans] =
  forw_subst
  back_subst
  rev_mp
  mp
  transitive
  trans

lemmas [elim?] = sym

end
