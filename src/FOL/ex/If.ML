(*  Title:      FOL/ex/If.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

First-Order Logic: the 'if' example.
*)

open Cla;    (*in case structure IntPr is open!*)

val prems = Goalw [if_def]
    "[| P ==> Q; ~P ==> R |] ==> if(P,Q,R)";
by (blast_tac (claset() addIs prems) 1);
qed "ifI";

val major::prems = Goalw [if_def]
   "[| if(P,Q,R);  [| P; Q |] ==> S; [| ~P; R |] ==> S |] ==> S";
by (cut_facts_tac [major] 1);
by (blast_tac (claset() addIs prems) 1);
qed "ifE";


Goal "if(P, if(Q,A,B), if(Q,C,D)) <-> if(Q, if(P,A,C), if(P,B,D))";
by (rtac iffI 1);
by (etac ifE 1);
by (etac ifE 1);
by (rtac ifI 1);
by (rtac ifI 1);

choplev 0;
AddSIs [ifI];
AddSEs [ifE];
by (Blast_tac 1);
qed "if_commute";


Goal "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,A,B))";
by (Blast_tac 1);
qed "nested_ifs";

choplev 0;
by (rewtac if_def);
by (blast_tac FOL_cs 1);
qed "";


(*An invalid formula.  High-level rules permit a simpler diagnosis*)
Goal "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,B,A))";
by (Blast_tac 1) handle ERROR => writeln"Failed, as expected";
(*Check that subgoals remain: proof failed.*)
getgoal 1; 
by (REPEAT (Step_tac 1));

choplev 0;
by (rewtac if_def);
by (blast_tac FOL_cs 1) handle ERROR => writeln"Failed, as expected";
(*Check that subgoals remain: proof failed.*)
getgoal 1; 
by (REPEAT (step_tac FOL_cs 1));
