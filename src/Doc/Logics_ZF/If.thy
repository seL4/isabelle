(*  Title:      Doc/Logics_ZF/If.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

First-Order Logic: the 'if' example.
*)

theory If imports FOL begin

definition "if" :: "[o,o,o]=>o" where
  "if(P,Q,R) == P&Q | ~P&R"

lemma ifI:
    "[| P ==> Q; ~P ==> R |] ==> if(P,Q,R)"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (simp add: if_def)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply blast
done

lemma ifE:
   "[| if(P,Q,R);  [| P; Q |] ==> S; [| ~P; R |] ==> S |] ==> S"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (simp add: if_def)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply blast
done

lemma if_commute: "if(P, if(Q,A,B), if(Q,C,D)) <-> if(Q, if(P,A,C), if(P,B,D))"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule iffI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule ifE)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule ifE)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule ifI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule ifI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
oops

text\<open>Trying again from the beginning in order to use @{text blast}\<close>
declare ifI [intro!]
declare ifE [elim!]

lemma if_commute: "if(P, if(Q,A,B), if(Q,C,D)) <-> if(Q, if(P,A,C), if(P,B,D))"
by blast


lemma "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,A,B))"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
by blast

text\<open>Trying again from the beginning in order to prove from the definitions\<close>
lemma "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,A,B))"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (simp add: if_def)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply blast
done


text\<open>An invalid formula.  High-level rules permit a simpler diagnosis\<close>
lemma "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,B,A))"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply auto
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
(*The next step will fail unless subgoals remain*)
apply (tactic all_tac)
oops

text\<open>Trying again from the beginning in order to prove from the definitions\<close>
lemma "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,B,A))"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (simp add: if_def)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (auto) 
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
(*The next step will fail unless subgoals remain*)
apply (tactic all_tac)
oops


end
