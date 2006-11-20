(*  Title:      LK/Quantifiers.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Classical sequent calculus: examples with quantifiers.
*)

theory Quantifiers
imports LK
begin

lemma "|- (ALL x. P)  <->  P"
  by fast

lemma "|- (ALL x y. P(x,y))  <->  (ALL y x. P(x,y))"
  by fast

lemma "ALL u. P(u), ALL v. Q(v) |- ALL u v. P(u) & Q(v)"
  by fast


text "Permutation of existential quantifier."

lemma "|- (EX x y. P(x,y)) <-> (EX y x. P(x,y))"
  by fast

lemma "|- (ALL x. P(x) & Q(x)) <-> (ALL x. P(x)) & (ALL x. Q(x))"
  by fast

(*Converse is invalid*)
lemma "|- (ALL x. P(x)) | (ALL x. Q(x)) --> (ALL x. P(x)|Q(x))"
  by fast


text "Pushing ALL into an implication."

lemma "|- (ALL x. P --> Q(x))  <->  (P --> (ALL x. Q(x)))"
  by fast

lemma "|- (ALL x. P(x)-->Q)  <->  ((EX x. P(x)) --> Q)"
  by fast

lemma "|- (EX x. P)  <->  P"
  by fast


text "Distribution of EX over disjunction."

lemma "|- (EX x. P(x) | Q(x)) <-> (EX x. P(x))  |  (EX x. Q(x))"
  by fast

(*Converse is invalid*)
lemma "|- (EX x. P(x) & Q(x))  -->  (EX x. P(x))  &  (EX x. Q(x))"
  by fast


text "Harder examples: classical theorems."

lemma "|- (EX x. P-->Q(x))  <->  (P --> (EX x. Q(x)))"
  by fast

lemma "|- (EX x. P(x)-->Q)  <->  (ALL x. P(x)) --> Q"
  by fast

lemma "|- (ALL x. P(x)) | Q  <->  (ALL x. P(x) | Q)"
  by fast


text "Basic test of quantifier reasoning"

lemma "|- (EX y. ALL x. Q(x,y)) --> (ALL x. EX y. Q(x,y))"
  by fast

lemma "|- (ALL x. Q(x))  -->  (EX x. Q(x))"
  by fast


text "The following are invalid!"

(*INVALID*)
lemma "|- (ALL x. EX y. Q(x,y))  -->  (EX y. ALL x. Q(x,y))"
  apply fast?
  apply (rule _)
  oops

(*INVALID*)
lemma "|- (EX x. Q(x))  -->  (ALL x. Q(x))"
  apply fast?
  apply (rule _)
  oops

(*INVALID*)
lemma "|- P(?a) --> (ALL x. P(x))"
  apply fast?
  apply (rule _)
  oops

(*INVALID*)
lemma "|- (P(?a) --> (ALL x. Q(x))) --> (ALL x. P(x) --> Q(x))"
  apply fast?
  apply (rule _)
  oops


text "Back to things that are provable..."

lemma "|- (ALL x. P(x)-->Q(x)) & (EX x. P(x)) --> (EX x. Q(x))"
  by fast

(*An example of why exR should be delayed as long as possible*)
lemma "|- (P--> (EX x. Q(x))) & P--> (EX x. Q(x))"
  by fast


text "Solving for a Var"

lemma "|- (ALL x. P(x)-->Q(f(x))) & (ALL x. Q(x)-->R(g(x))) & P(d) --> R(?a)"
  by fast


text "Principia Mathematica *11.53"

lemma "|- (ALL x y. P(x) --> Q(y)) <-> ((EX x. P(x)) --> (ALL y. Q(y)))"
  by fast


text "Principia Mathematica *11.55"

lemma "|- (EX x y. P(x) & Q(x,y)) <-> (EX x. P(x) & (EX y. Q(x,y)))"
  by fast


text "Principia Mathematica *11.61"

lemma "|- (EX y. ALL x. P(x) --> Q(x,y)) --> (ALL x. P(x) --> (EX y. Q(x,y)))"
  by fast


(*21 August 88: loaded in 45.7 secs*)
(*18 September 2005: loaded in 0.114 secs*)

end
