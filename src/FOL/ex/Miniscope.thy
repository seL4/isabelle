(*  Title:      FOL/ex/Miniscope.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Classical First-Order Logic.
Conversion to nnf/miniscope format: pushing quantifiers in.
Demonstration of formula rewriting by proof.
*)

theory Miniscope
imports FOL
begin


lemmas ccontr = FalseE [THEN classical]

subsection {* Negation Normal Form *}

subsubsection {* de Morgan laws *}

lemma demorgans:
  "~(P&Q) <-> ~P | ~Q"
  "~(P|Q) <-> ~P & ~Q"
  "~~P <-> P"
  "!!P. ~(ALL x. P(x)) <-> (EX x. ~P(x))"
  "!!P. ~(EX x. P(x)) <-> (ALL x. ~P(x))"
  by blast+

(*** Removal of --> and <-> (positive and negative occurrences) ***)
(*Last one is important for computing a compact CNF*)
lemma nnf_simps:
  "(P-->Q) <-> (~P | Q)"
  "~(P-->Q) <-> (P & ~Q)"
  "(P<->Q) <-> (~P | Q) & (~Q | P)"
  "~(P<->Q) <-> (P | Q) & (~P | ~Q)"
  by blast+


(* BEWARE: rewrite rules for <-> can confuse the simplifier!! *)

subsubsection {* Pushing in the existential quantifiers *}

lemma ex_simps:
  "(EX x. P) <-> P"
  "!!P Q. (EX x. P(x) & Q) <-> (EX x. P(x)) & Q"
  "!!P Q. (EX x. P & Q(x)) <-> P & (EX x. Q(x))"
  "!!P Q. (EX x. P(x) | Q(x)) <-> (EX x. P(x)) | (EX x. Q(x))"
  "!!P Q. (EX x. P(x) | Q) <-> (EX x. P(x)) | Q"
  "!!P Q. (EX x. P | Q(x)) <-> P | (EX x. Q(x))"
  by blast+


subsubsection {* Pushing in the universal quantifiers *}

lemma all_simps:
  "(ALL x. P) <-> P"
  "!!P Q. (ALL x. P(x) & Q(x)) <-> (ALL x. P(x)) & (ALL x. Q(x))"
  "!!P Q. (ALL x. P(x) & Q) <-> (ALL x. P(x)) & Q"
  "!!P Q. (ALL x. P & Q(x)) <-> P & (ALL x. Q(x))"
  "!!P Q. (ALL x. P(x) | Q) <-> (ALL x. P(x)) | Q"
  "!!P Q. (ALL x. P | Q(x)) <-> P | (ALL x. Q(x))"
  by blast+

lemmas mini_simps = demorgans nnf_simps ex_simps all_simps

ML {*
val mini_ss = simpset() addsimps (thms "mini_simps");
val mini_tac = rtac (thm "ccontr") THEN' asm_full_simp_tac mini_ss;
*}

end
