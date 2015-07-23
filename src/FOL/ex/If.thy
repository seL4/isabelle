(*  Title:      FOL/ex/If.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section \<open>First-Order Logic: the 'if' example\<close>

theory If imports FOL begin

definition "if" :: "[o,o,o]=>o" where
  "if(P,Q,R) == P&Q | ~P&R"

lemma ifI:
    "[| P ==> Q; ~P ==> R |] ==> if(P,Q,R)"
apply (simp add: if_def, blast)
done

lemma ifE:
   "[| if(P,Q,R);  [| P; Q |] ==> S; [| ~P; R |] ==> S |] ==> S"
apply (simp add: if_def, blast)
done

lemma if_commute: "if(P, if(Q,A,B), if(Q,C,D)) <-> if(Q, if(P,A,C), if(P,B,D))"
apply (rule iffI)
apply (erule ifE)
apply (erule ifE)
apply (rule ifI)
apply (rule ifI)
oops

text\<open>Trying again from the beginning in order to use @{text blast}\<close>
declare ifI [intro!]
declare ifE [elim!]

lemma if_commute: "if(P, if(Q,A,B), if(Q,C,D)) <-> if(Q, if(P,A,C), if(P,B,D))"
by blast


lemma "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,A,B))"
by blast

text\<open>Trying again from the beginning in order to prove from the definitions\<close>
lemma "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,A,B))"
by (simp add: if_def, blast)


text\<open>An invalid formula.  High-level rules permit a simpler diagnosis\<close>
lemma "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,B,A))"
apply auto
  -- \<open>The next step will fail unless subgoals remain\<close>
apply (tactic all_tac)
oops

text\<open>Trying again from the beginning in order to prove from the definitions\<close>
lemma "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,B,A))"
apply (simp add: if_def, auto) 
  -- \<open>The next step will fail unless subgoals remain\<close>
apply (tactic all_tac)
oops

end
