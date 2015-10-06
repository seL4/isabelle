(*  Title:      FOL/ex/Quantifiers_Int.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section \<open>First-Order Logic: quantifier examples (intuitionistic version)\<close>

theory Quantifiers_Int
imports IFOL
begin

lemma "(ALL x y. P(x,y))  -->  (ALL y x. P(x,y))"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "(EX x y. P(x,y)) --> (EX y x. P(x,y))"
  by (tactic "IntPr.fast_tac @{context} 1")


-- \<open>Converse is false\<close>
lemma "(ALL x. P(x)) | (ALL x. Q(x)) --> (ALL x. P(x) | Q(x))"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "(ALL x. P-->Q(x))  <->  (P--> (ALL x. Q(x)))"
  by (tactic "IntPr.fast_tac @{context} 1")


lemma "(ALL x. P(x)-->Q)  <->  ((EX x. P(x)) --> Q)"
  by (tactic "IntPr.fast_tac @{context} 1")


text \<open>Some harder ones\<close>

lemma "(EX x. P(x) | Q(x)) <-> (EX x. P(x)) | (EX x. Q(x))"
  by (tactic "IntPr.fast_tac @{context} 1")

-- \<open>Converse is false\<close>
lemma "(EX x. P(x)&Q(x)) --> (EX x. P(x))  &  (EX x. Q(x))"
  by (tactic "IntPr.fast_tac @{context} 1")


text \<open>Basic test of quantifier reasoning\<close>

-- \<open>TRUE\<close>
lemma "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "(ALL x. Q(x))  -->  (EX x. Q(x))"
  by (tactic "IntPr.fast_tac @{context} 1")


text \<open>The following should fail, as they are false!\<close>

lemma "(ALL x. EX y. Q(x,y))  -->  (EX y. ALL x. Q(x,y))"
  apply (tactic "IntPr.fast_tac @{context} 1")?
  oops

lemma "(EX x. Q(x))  -->  (ALL x. Q(x))"
  apply (tactic "IntPr.fast_tac @{context} 1")?
  oops

schematic_goal "P(?a) --> (ALL x. P(x))"
  apply (tactic "IntPr.fast_tac @{context} 1")?
  oops

schematic_goal "(P(?a) --> (ALL x. Q(x))) --> (ALL x. P(x) --> Q(x))"
  apply (tactic "IntPr.fast_tac @{context} 1")?
  oops


text \<open>Back to things that are provable \dots\<close>

lemma "(ALL x. P(x)-->Q(x)) & (EX x. P(x)) --> (EX x. Q(x))"
  by (tactic "IntPr.fast_tac @{context} 1")

-- \<open>An example of why exI should be delayed as long as possible\<close>
lemma "(P --> (EX x. Q(x))) & P --> (EX x. Q(x))"
  by (tactic "IntPr.fast_tac @{context} 1")

schematic_goal "(ALL x. P(x)-->Q(f(x))) & (ALL x. Q(x)-->R(g(x))) & P(d) --> R(?a)"
  by (tactic "IntPr.fast_tac @{context} 1")

lemma "(ALL x. Q(x))  -->  (EX x. Q(x))"
  by (tactic "IntPr.fast_tac @{context} 1")


text \<open>Some slow ones\<close>

-- \<open>Principia Mathematica *11.53\<close>
lemma "(ALL x y. P(x) --> Q(y)) <-> ((EX x. P(x)) --> (ALL y. Q(y)))"
  by (tactic "IntPr.fast_tac @{context} 1")

(*Principia Mathematica *11.55  *)
lemma "(EX x y. P(x) & Q(x,y)) <-> (EX x. P(x) & (EX y. Q(x,y)))"
  by (tactic "IntPr.fast_tac @{context} 1")

(*Principia Mathematica *11.61  *)
lemma "(EX y. ALL x. P(x) --> Q(x,y)) --> (ALL x. P(x) --> (EX y. Q(x,y)))"
  by (tactic "IntPr.fast_tac @{context} 1")

end
