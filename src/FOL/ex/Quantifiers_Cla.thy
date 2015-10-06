(*  Title:      FOL/ex/Quantifiers_Cla.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section \<open>First-Order Logic: quantifier examples (classical version)\<close>

theory Quantifiers_Cla
imports FOL
begin

lemma "(ALL x y. P(x,y))  -->  (ALL y x. P(x,y))"
  by fast

lemma "(EX x y. P(x,y)) --> (EX y x. P(x,y))"
  by fast


-- \<open>Converse is false\<close>
lemma "(ALL x. P(x)) | (ALL x. Q(x)) --> (ALL x. P(x) | Q(x))"
  by fast

lemma "(ALL x. P-->Q(x))  <->  (P--> (ALL x. Q(x)))"
  by fast


lemma "(ALL x. P(x)-->Q)  <->  ((EX x. P(x)) --> Q)"
  by fast


text \<open>Some harder ones\<close>

lemma "(EX x. P(x) | Q(x)) <-> (EX x. P(x)) | (EX x. Q(x))"
  by fast

-- \<open>Converse is false\<close>
lemma "(EX x. P(x)&Q(x)) --> (EX x. P(x))  &  (EX x. Q(x))"
  by fast


text \<open>Basic test of quantifier reasoning\<close>

-- \<open>TRUE\<close>
lemma "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
  by fast

lemma "(ALL x. Q(x))  -->  (EX x. Q(x))"
  by fast


text \<open>The following should fail, as they are false!\<close>

lemma "(ALL x. EX y. Q(x,y))  -->  (EX y. ALL x. Q(x,y))"
  apply fast?
  oops

lemma "(EX x. Q(x))  -->  (ALL x. Q(x))"
  apply fast?
  oops

schematic_goal "P(?a) --> (ALL x. P(x))"
  apply fast?
  oops

schematic_goal "(P(?a) --> (ALL x. Q(x))) --> (ALL x. P(x) --> Q(x))"
  apply fast?
  oops


text \<open>Back to things that are provable \dots\<close>

lemma "(ALL x. P(x)-->Q(x)) & (EX x. P(x)) --> (EX x. Q(x))"
  by fast

-- \<open>An example of why exI should be delayed as long as possible\<close>
lemma "(P --> (EX x. Q(x))) & P --> (EX x. Q(x))"
  by fast

schematic_goal "(ALL x. P(x)-->Q(f(x))) & (ALL x. Q(x)-->R(g(x))) & P(d) --> R(?a)"
  by fast

lemma "(ALL x. Q(x))  -->  (EX x. Q(x))"
  by fast


text \<open>Some slow ones\<close>

-- \<open>Principia Mathematica *11.53\<close>
lemma "(ALL x y. P(x) --> Q(y)) <-> ((EX x. P(x)) --> (ALL y. Q(y)))"
  by fast

(*Principia Mathematica *11.55  *)
lemma "(EX x y. P(x) & Q(x,y)) <-> (EX x. P(x) & (EX y. Q(x,y)))"
  by fast

(*Principia Mathematica *11.61  *)
lemma "(EX y. ALL x. P(x) --> Q(x,y)) --> (ALL x. P(x) --> (EX y. Q(x,y)))"
  by fast

end
