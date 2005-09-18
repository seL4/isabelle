(*  Title:      FOLP/ex/If.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

val prems = goalw (the_context ()) [if_def]
    "[| !!x. x:P ==> f(x):Q; !!x. x:~P ==> g(x):R |] ==> ?p:if(P,Q,R)";
by (fast_tac (FOLP_cs addIs prems) 1);
val ifI = result();

val major::prems = goalw (the_context ()) [if_def]
   "[| p:if(P,Q,R);  !!x y.[| x:P; y:Q |] ==> f(x,y):S; \
\                    !!x y.[| x:~P; y:R |] ==> g(x,y):S |] ==> ?p:S";
by (cut_facts_tac [major] 1);
by (fast_tac (FOLP_cs addIs prems) 1);
val ifE = result();


Goal
    "?p : if(P, if(Q,A,B), if(Q,C,D)) <-> if(Q, if(P,A,C), if(P,B,D))";
by (rtac iffI 1);
by (etac ifE 1);
by (etac ifE 1);
by (rtac ifI 1);
by (rtac ifI 1);

choplev 0;
val if_cs = FOLP_cs addSIs [ifI] addSEs[ifE];
by (fast_tac if_cs 1);
val if_commute = result();


Goal "?p : if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,A,B))";
by (fast_tac if_cs 1);
val nested_ifs = result();
