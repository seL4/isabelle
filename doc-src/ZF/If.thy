(*  Title:      FOL/ex/If.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

First-Order Logic: the 'if' example.
*)

theory If = FOL:

constdefs
  if :: "[o,o,o]=>o"
   "if(P,Q,R) == P&Q | ~P&R"

lemma ifI:
    "[| P ==> Q; ~P ==> R |] ==> if(P,Q,R)"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (simp add: if_def)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply blast
done

lemma ifE:
   "[| if(P,Q,R);  [| P; Q |] ==> S; [| ~P; R |] ==> S |] ==> S"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (simp add: if_def)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply blast
done

lemma if_commute: "if(P, if(Q,A,B), if(Q,C,D)) <-> if(Q, if(P,A,C), if(P,B,D))"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule iffI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule ifE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule ifE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule ifI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule ifI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
oops

text{*Trying again from the beginning in order to use @{text blast}*}
declare ifI [intro!]
declare ifE [elim!]

lemma if_commute: "if(P, if(Q,A,B), if(Q,C,D)) <-> if(Q, if(P,A,C), if(P,B,D))"
by blast


lemma "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,A,B))"
  --{* @{subgoals[display,indent=0,margin=65]} *}
by blast

text{*Trying again from the beginning in order to prove from the definitions*}
lemma "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,A,B))"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (simp add: if_def)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply blast
done


text{*An invalid formula.  High-level rules permit a simpler diagnosis*}
lemma "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,B,A))"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply auto
  --{* @{subgoals[display,indent=0,margin=65]} *}
(*The next step will fail unless subgoals remain*)
apply (tactic all_tac)
oops

text{*Trying again from the beginning in order to prove from the definitions*}
lemma "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,B,A))"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (simp add: if_def)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (auto) 
  --{* @{subgoals[display,indent=0,margin=65]} *}
(*The next step will fail unless subgoals remain*)
apply (tactic all_tac)
oops


end
