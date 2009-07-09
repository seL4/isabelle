(*  Title:      FOL/ex/Quantifiers_Int.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header {* First-Order Logic: quantifier examples (intuitionistic version) *}

theory Quantifiers_Int
imports IFOL
begin

lemma "(ALL x y. P(x,y))  -->  (ALL y x. P(x,y))"
  by (tactic "IntPr.fast_tac 1")

lemma "(EX x y. P(x,y)) --> (EX y x. P(x,y))"
  by (tactic "IntPr.fast_tac 1")


-- {* Converse is false *}
lemma "(ALL x. P(x)) | (ALL x. Q(x)) --> (ALL x. P(x) | Q(x))"
  by (tactic "IntPr.fast_tac 1")

lemma "(ALL x. P-->Q(x))  <->  (P--> (ALL x. Q(x)))"
  by (tactic "IntPr.fast_tac 1")


lemma "(ALL x. P(x)-->Q)  <->  ((EX x. P(x)) --> Q)"
  by (tactic "IntPr.fast_tac 1")


text {* Some harder ones *}

lemma "(EX x. P(x) | Q(x)) <-> (EX x. P(x)) | (EX x. Q(x))"
  by (tactic "IntPr.fast_tac 1")

-- {* Converse is false *}
lemma "(EX x. P(x)&Q(x)) --> (EX x. P(x))  &  (EX x. Q(x))"
  by (tactic "IntPr.fast_tac 1")


text {* Basic test of quantifier reasoning *}

-- {* TRUE *}
lemma "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
  by (tactic "IntPr.fast_tac 1")

lemma "(ALL x. Q(x))  -->  (EX x. Q(x))"
  by (tactic "IntPr.fast_tac 1")


text {* The following should fail, as they are false! *}

lemma "(ALL x. EX y. Q(x,y))  -->  (EX y. ALL x. Q(x,y))"
  apply (tactic "IntPr.fast_tac 1")?
  oops

lemma "(EX x. Q(x))  -->  (ALL x. Q(x))"
  apply (tactic "IntPr.fast_tac 1")?
  oops

lemma "P(?a) --> (ALL x. P(x))"
  apply (tactic "IntPr.fast_tac 1")?
  oops

lemma "(P(?a) --> (ALL x. Q(x))) --> (ALL x. P(x) --> Q(x))"
  apply (tactic "IntPr.fast_tac 1")?
  oops


text {* Back to things that are provable \dots *}

lemma "(ALL x. P(x)-->Q(x)) & (EX x. P(x)) --> (EX x. Q(x))"
  by (tactic "IntPr.fast_tac 1")

-- {* An example of why exI should be delayed as long as possible *}
lemma "(P --> (EX x. Q(x))) & P --> (EX x. Q(x))"
  by (tactic "IntPr.fast_tac 1")

lemma "(ALL x. P(x)-->Q(f(x))) & (ALL x. Q(x)-->R(g(x))) & P(d) --> R(?a)"
  by (tactic "IntPr.fast_tac 1")

lemma "(ALL x. Q(x))  -->  (EX x. Q(x))"
  by (tactic "IntPr.fast_tac 1")


text {* Some slow ones *}

-- {* Principia Mathematica *11.53 *}
lemma "(ALL x y. P(x) --> Q(y)) <-> ((EX x. P(x)) --> (ALL y. Q(y)))"
  by (tactic "IntPr.fast_tac 1")

(*Principia Mathematica *11.55  *)
lemma "(EX x y. P(x) & Q(x,y)) <-> (EX x. P(x) & (EX y. Q(x,y)))"
  by (tactic "IntPr.fast_tac 1")

(*Principia Mathematica *11.61  *)
lemma "(EX y. ALL x. P(x) --> Q(x,y)) --> (ALL x. P(x) --> (EX y. Q(x,y)))"
  by (tactic "IntPr.fast_tac 1")

end
