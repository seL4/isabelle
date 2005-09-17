(*  Title:      CCL/mono.ML
    ID:         $Id$

Monotonicity of various operations.
*)

val prems = goal (the_context ()) "A<=B ==> Union(A) <= Union(B)";
by (cfast_tac prems 1);
qed "Union_mono";

val prems = goal (the_context ()) "[| B<=A |] ==> Inter(A) <= Inter(B)";
by (cfast_tac prems 1);
qed "Inter_anti_mono";

val prems = goal (the_context ())
    "[| A<=B;  !!x. x:A ==> f(x)<=g(x) |] ==> \
\    (UN x:A. f(x)) <= (UN x:B. g(x))";
by (REPEAT (eresolve_tac [UN_E,ssubst] 1
     ORELSE ares_tac ((prems RL [subsetD]) @ [subsetI,UN_I]) 1));
qed "UN_mono";

val prems = goal (the_context ())
    "[| B<=A;  !!x. x:A ==> f(x)<=g(x) |] ==> \
\    (INT x:A. f(x)) <= (INT x:A. g(x))";
by (REPEAT (ares_tac ((prems RL [subsetD]) @ [subsetI,INT_I]) 1
     ORELSE etac INT_D 1));
qed "INT_anti_mono";

val prems = goal (the_context ()) "[| A<=C;  B<=D |] ==> A Un B <= C Un D";
by (cfast_tac prems 1);
qed "Un_mono";

val prems = goal (the_context ()) "[| A<=C;  B<=D |] ==> A Int B <= C Int D";
by (cfast_tac prems 1);
qed "Int_mono";

val prems = goal (the_context ()) "[| A<=B |] ==> Compl(B) <= Compl(A)";
by (cfast_tac prems 1);
qed "Compl_anti_mono";
