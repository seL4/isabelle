(*  Title: 	CCL/mono
    ID:         $Id$

Modified version of
    Title: 	HOL/mono
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Monotonicity of various operations
*)

writeln"File HOL/mono";

val prems = goal Set.thy "A<=B ==> Union(A) <= Union(B)";
by (cfast_tac prems 1);
val Union_mono = result();

val prems = goal Set.thy "[| B<=A |] ==> Inter(A) <= Inter(B)";
by (cfast_tac prems 1);
val Inter_anti_mono = result();

val prems = goal Set.thy
    "[| A<=B;  !!x. x:A ==> f(x)<=g(x) |] ==> \
\    (UN x:A. f(x)) <= (UN x:B. g(x))";
by (REPEAT (eresolve_tac [UN_E,ssubst] 1
     ORELSE ares_tac ((prems RL [subsetD]) @ [subsetI,UN_I]) 1));
val UN_mono = result();

val prems = goal Set.thy
    "[| B<=A;  !!x. x:A ==> f(x)<=g(x) |] ==> \
\    (INT x:A. f(x)) <= (INT x:A. g(x))";
by (REPEAT (ares_tac ((prems RL [subsetD]) @ [subsetI,INT_I]) 1
     ORELSE etac INT_D 1));
val INT_anti_mono = result();

val prems = goal Set.thy "[| A<=C;  B<=D |] ==> A Un B <= C Un D";
by (cfast_tac prems 1);
val Un_mono = result();

val prems = goal Set.thy "[| A<=C;  B<=D |] ==> A Int B <= C Int D";
by (cfast_tac prems 1);
val Int_mono = result();

val prems = goal Set.thy "[| A<=B |] ==> Compl(B) <= Compl(A)";
by (cfast_tac prems 1);
val Compl_anti_mono = result();
