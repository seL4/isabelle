(*  Title:      FOLP/ex/Quantifiers_Cla.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

First-Order Logic: quantifier examples (intuitionistic and classical)
Needs declarations of the theory "thy" and the tactic "tac".
*)

theory Quantifiers_Cla
imports FOLP
begin

schematic_lemma "?p : (ALL x y. P(x,y))  -->  (ALL y x. P(x,y))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})

schematic_lemma "?p : (EX x y. P(x,y)) --> (EX y x. P(x,y))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})


(*Converse is false*)
schematic_lemma "?p : (ALL x. P(x)) | (ALL x. Q(x)) --> (ALL x. P(x) | Q(x))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})

schematic_lemma "?p : (ALL x. P-->Q(x))  <->  (P--> (ALL x. Q(x)))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})


schematic_lemma "?p : (ALL x. P(x)-->Q)  <->  ((EX x. P(x)) --> Q)"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})


text "Some harder ones"

schematic_lemma "?p : (EX x. P(x) | Q(x)) <-> (EX x. P(x)) | (EX x. Q(x))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})

(*Converse is false*)
schematic_lemma "?p : (EX x. P(x)&Q(x)) --> (EX x. P(x))  &  (EX x. Q(x))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})


text "Basic test of quantifier reasoning"
(*TRUE*)
schematic_lemma "?p : (EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})

schematic_lemma "?p : (ALL x. Q(x))  -->  (EX x. Q(x))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})


text "The following should fail, as they are false!"

schematic_lemma "?p : (ALL x. EX y. Q(x,y))  -->  (EX y. ALL x. Q(x,y))"
  apply (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})?
  oops

schematic_lemma "?p : (EX x. Q(x))  -->  (ALL x. Q(x))"
  apply (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})?
  oops

schematic_lemma "?p : P(?a) --> (ALL x. P(x))"
  apply (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})?
  oops

schematic_lemma "?p : (P(?a) --> (ALL x. Q(x))) --> (ALL x. P(x) --> Q(x))"
  apply (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})?
  oops


text "Back to things that are provable..."

schematic_lemma "?p : (ALL x. P(x)-->Q(x)) & (EX x. P(x)) --> (EX x. Q(x))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})


(*An example of why exI should be delayed as long as possible*)
schematic_lemma "?p : (P --> (EX x. Q(x))) & P --> (EX x. Q(x))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})

schematic_lemma "?p : (ALL x. P(x)-->Q(f(x))) & (ALL x. Q(x)-->R(g(x))) & P(d) --> R(?a)"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})

schematic_lemma "?p : (ALL x. Q(x))  -->  (EX x. Q(x))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})


text "Some slow ones"

(*Principia Mathematica *11.53  *)
schematic_lemma "?p : (ALL x y. P(x) --> Q(y)) <-> ((EX x. P(x)) --> (ALL y. Q(y)))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})

(*Principia Mathematica *11.55  *)
schematic_lemma "?p : (EX x y. P(x) & Q(x,y)) <-> (EX x. P(x) & (EX y. Q(x,y)))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})

(*Principia Mathematica *11.61  *)
schematic_lemma "?p : (EX y. ALL x. P(x) --> Q(x,y)) --> (ALL x. P(x) --> (EX y. Q(x,y)))"
  by (tactic {* Cla.fast_tac @{context} FOLP_cs 1 *})

end
