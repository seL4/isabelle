(*  Title: 	FOL/ex/if
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

For ex/if.thy.  First-Order Logic: the 'if' example
*)

open If;
open Cla;    (*in case structure Int is open!*)

val prems = goalw If.thy [if_def]
    "[| P ==> Q; ~P ==> R |] ==> if(P,Q,R)";
by (fast_tac (FOL_cs addIs prems) 1);
val ifI = result();

val major::prems = goalw If.thy [if_def]
   "[| if(P,Q,R);  [| P; Q |] ==> S; [| ~P; R |] ==> S |] ==> S";
by (cut_facts_tac [major] 1);
by (fast_tac (FOL_cs addIs prems) 1);
val ifE = result();


goal If.thy
    "if(P, if(Q,A,B), if(Q,C,D)) <-> if(Q, if(P,A,C), if(P,B,D))";
by (resolve_tac [iffI] 1);
by (eresolve_tac [ifE] 1);
by (eresolve_tac [ifE] 1);
by (resolve_tac [ifI] 1);
by (resolve_tac [ifI] 1);

choplev 0;
val if_cs = FOL_cs addSIs [ifI] addSEs[ifE];
by (fast_tac if_cs 1);
val if_commute = result();


goal If.thy "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,A,B))";
by (fast_tac if_cs 1);
val nested_ifs = result();

choplev 0;
by (rewrite_goals_tac [if_def]);
by (fast_tac FOL_cs 1);
result();


(*An invalid formula.  High-level rules permit a simpler diagnosis*)
goal If.thy "if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,B,A))";
by (fast_tac if_cs 1) handle ERROR => writeln"Failed, as expected";
(*Check that subgoals remain: proof failed.*)
getgoal 1; 
by (REPEAT (step_tac if_cs 1));

choplev 0;
by (rewrite_goals_tac [if_def]);
by (fast_tac FOL_cs 1) handle ERROR => writeln"Failed, as expected";
(*Check that subgoals remain: proof failed.*)
getgoal 1; 
by (REPEAT (step_tac FOL_cs 1));



writeln"Reached end of file.";
