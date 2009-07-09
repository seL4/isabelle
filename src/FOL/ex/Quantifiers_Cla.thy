(*  Title:      FOL/ex/Quantifiers_Int.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header {* First-Order Logic: quantifier examples (classical version) *}

theory Quantifiers_Cla
imports FOL
begin

lemma "(ALL x y. P(x,y))  -->  (ALL y x. P(x,y))"
  by fast

lemma "(EX x y. P(x,y)) --> (EX y x. P(x,y))"
  by fast


-- {* Converse is false *}
lemma "(ALL x. P(x)) | (ALL x. Q(x)) --> (ALL x. P(x) | Q(x))"
  by fast

lemma "(ALL x. P-->Q(x))  <->  (P--> (ALL x. Q(x)))"
  by fast


lemma "(ALL x. P(x)-->Q)  <->  ((EX x. P(x)) --> Q)"
  by fast


text {* Some harder ones *}

lemma "(EX x. P(x) | Q(x)) <-> (EX x. P(x)) | (EX x. Q(x))"
  by fast

-- {* Converse is false *}
lemma "(EX x. P(x)&Q(x)) --> (EX x. P(x))  &  (EX x. Q(x))"
  by fast


text {* Basic test of quantifier reasoning *}

-- {* TRUE *}
lemma "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
  by fast

lemma "(ALL x. Q(x))  -->  (EX x. Q(x))"
  by fast


text {* The following should fail, as they are false! *}

lemma "(ALL x. EX y. Q(x,y))  -->  (EX y. ALL x. Q(x,y))"
  apply fast?
  oops

lemma "(EX x. Q(x))  -->  (ALL x. Q(x))"
  apply fast?
  oops

lemma "P(?a) --> (ALL x. P(x))"
  apply fast?
  oops

lemma "(P(?a) --> (ALL x. Q(x))) --> (ALL x. P(x) --> Q(x))"
  apply fast?
  oops


text {* Back to things that are provable \dots *}

lemma "(ALL x. P(x)-->Q(x)) & (EX x. P(x)) --> (EX x. Q(x))"
  by fast

-- {* An example of why exI should be delayed as long as possible *}
lemma "(P --> (EX x. Q(x))) & P --> (EX x. Q(x))"
  by fast

lemma "(ALL x. P(x)-->Q(f(x))) & (ALL x. Q(x)-->R(g(x))) & P(d) --> R(?a)"
  by fast

lemma "(ALL x. Q(x))  -->  (EX x. Q(x))"
  by fast


text {* Some slow ones *}

-- {* Principia Mathematica *11.53 *}
lemma "(ALL x y. P(x) --> Q(y)) <-> ((EX x. P(x)) --> (ALL y. Q(y)))"
  by fast

(*Principia Mathematica *11.55  *)
lemma "(EX x y. P(x) & Q(x,y)) <-> (EX x. P(x) & (EX y. Q(x,y)))"
  by fast

(*Principia Mathematica *11.61  *)
lemma "(EX y. ALL x. P(x) --> Q(x,y)) --> (ALL x. P(x) --> (EX y. Q(x,y)))"
  by fast

end
