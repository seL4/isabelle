(*  Title:      FOLP/ex/Quantifiers_Int.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

First-Order Logic: quantifier examples (intuitionistic and classical)
Needs declarations of the theory "thy" and the tactic "tac".
*)

theory Quantifiers_Int
imports IFOLP
begin

schematic_goal "?p : (ALL x y. P(x,y))  -->  (ALL y x. P(x,y))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)

schematic_goal "?p : (EX x y. P(x,y)) --> (EX y x. P(x,y))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)


(*Converse is false*)
schematic_goal "?p : (ALL x. P(x)) | (ALL x. Q(x)) --> (ALL x. P(x) | Q(x))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)

schematic_goal "?p : (ALL x. P-->Q(x))  <->  (P--> (ALL x. Q(x)))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)


schematic_goal "?p : (ALL x. P(x)-->Q)  <->  ((EX x. P(x)) --> Q)"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)


text "Some harder ones"

schematic_goal "?p : (EX x. P(x) | Q(x)) <-> (EX x. P(x)) | (EX x. Q(x))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)

(*Converse is false*)
schematic_goal "?p : (EX x. P(x)&Q(x)) --> (EX x. P(x))  &  (EX x. Q(x))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)


text "Basic test of quantifier reasoning"
(*TRUE*)
schematic_goal "?p : (EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)

schematic_goal "?p : (ALL x. Q(x))  -->  (EX x. Q(x))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)


text "The following should fail, as they are false!"

schematic_goal "?p : (ALL x. EX y. Q(x,y))  -->  (EX y. ALL x. Q(x,y))"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)?
  oops

schematic_goal "?p : (EX x. Q(x))  -->  (ALL x. Q(x))"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)?
  oops

schematic_goal "?p : P(?a) --> (ALL x. P(x))"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)?
  oops

schematic_goal "?p : (P(?a) --> (ALL x. Q(x))) --> (ALL x. P(x) --> Q(x))"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)?
  oops


text "Back to things that are provable..."

schematic_goal "?p : (ALL x. P(x)-->Q(x)) & (EX x. P(x)) --> (EX x. Q(x))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)


(*An example of why exI should be delayed as long as possible*)
schematic_goal "?p : (P --> (EX x. Q(x))) & P --> (EX x. Q(x))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)

schematic_goal "?p : (ALL x. P(x)-->Q(f(x))) & (ALL x. Q(x)-->R(g(x))) & P(d) --> R(?a)"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)

schematic_goal "?p : (ALL x. Q(x))  -->  (EX x. Q(x))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)


text "Some slow ones"

(*Principia Mathematica *11.53  *)
schematic_goal "?p : (ALL x y. P(x) --> Q(y)) <-> ((EX x. P(x)) --> (ALL y. Q(y)))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)

(*Principia Mathematica *11.55  *)
schematic_goal "?p : (EX x y. P(x) & Q(x,y)) <-> (EX x. P(x) & (EX y. Q(x,y)))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)

(*Principia Mathematica *11.61  *)
schematic_goal "?p : (EX y. ALL x. P(x) --> Q(x,y)) --> (ALL x. P(x) --> (EX y. Q(x,y)))"
  by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)

end
