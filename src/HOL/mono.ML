(*  Title:      HOL/mono.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Monotonicity of various operations
*)

goal Set.thy "!!A B. A<=B ==> f``A <= f``B";
by (Blast_tac 1);
qed "image_mono";

goal Set.thy "!!A B. A<=B ==> Pow(A) <= Pow(B)";
by (Blast_tac 1);
qed "Pow_mono";

goal Set.thy "!!A B. A<=B ==> Union(A) <= Union(B)";
by (Blast_tac 1);
qed "Union_mono";

goal Set.thy "!!A B. B<=A ==> Inter(A) <= Inter(B)";
by (Blast_tac 1);
qed "Inter_anti_mono";

val prems = goal Set.thy
    "[| A<=B;  !!x. x:A ==> f(x)<=g(x) |] ==> \
\    (UN x:A. f(x)) <= (UN x:B. g(x))";
by (blast_tac (claset() addIs (prems RL [subsetD])) 1);
qed "UN_mono";

(*The last inclusion is POSITIVE! *)
val prems = goal Set.thy
    "[| B<=A;  !!x. x:A ==> f(x)<=g(x) |] ==> \
\    (INT x:A. f(x)) <= (INT x:A. g(x))";
by (blast_tac (claset() addIs (prems RL [subsetD])) 1);
qed "INT_anti_mono";

goal Set.thy "!!C D. C<=D ==> insert a C <= insert a D";
by (Blast_tac 1);
qed "insert_mono";

goal Set.thy "!!A B. [| A<=C;  B<=D |] ==> A Un B <= C Un D";
by (Blast_tac 1);
qed "Un_mono";

goal Set.thy "!!A B. [| A<=C;  B<=D |] ==> A Int B <= C Int D";
by (Blast_tac 1);
qed "Int_mono";

goal Set.thy "!!A::'a set. [| A<=C;  D<=B |] ==> A-B <= C-D";
by (Blast_tac 1);
qed "Diff_mono";

goal Set.thy "!!A B. A<=B ==> Compl(B) <= Compl(A)";
by (Blast_tac 1);
qed "Compl_anti_mono";

(** Monotonicity of implications.  For inductive definitions **)

goal Set.thy "!!A B x. A<=B ==> x:A --> x:B";
by (rtac impI 1);
by (etac subsetD 1);
by (assume_tac 1);
qed "in_mono";

goal HOL.thy "!!P1 P2 Q1 Q2. [| P1-->Q1; P2-->Q2 |] ==> (P1&P2) --> (Q1&Q2)";
by (Blast_tac 1);
qed "conj_mono";

goal HOL.thy "!!P1 P2 Q1 Q2. [| P1-->Q1; P2-->Q2 |] ==> (P1|P2) --> (Q1|Q2)";
by (Blast_tac 1);
qed "disj_mono";

goal HOL.thy "!!P1 P2 Q1 Q2.[| Q1-->P1; P2-->Q2 |] ==> (P1-->P2)-->(Q1-->Q2)";
by (Blast_tac 1);
qed "imp_mono";

goal HOL.thy "P-->P";
by (rtac impI 1);
by (assume_tac 1);
qed "imp_refl";

val [PQimp] = goal HOL.thy
    "[| !!x. P(x) --> Q(x) |] ==> (EX x. P(x)) --> (EX x. Q(x))";
by (blast_tac (claset() addIs [PQimp RS mp]) 1);
qed "ex_mono";

val [PQimp] = goal HOL.thy
    "[| !!x. P(x) --> Q(x) |] ==> (ALL x. P(x)) --> (ALL x. Q(x))";
by (blast_tac (claset() addIs [PQimp RS mp]) 1);
qed "all_mono";

val [PQimp] = goal Set.thy
    "[| !!x. P(x) --> Q(x) |] ==> Collect(P) <= Collect(Q)";
by (blast_tac (claset() addIs [PQimp RS mp]) 1);
qed "Collect_mono";

(*Used in indrule.ML*)
val [subs,PQimp] = goal Set.thy
    "[| A<=B;  !!x. x:A ==> P(x) --> Q(x) \
\    |] ==> A Int Collect(P) <= B Int Collect(Q)";
by (blast_tac (claset() addIs [subs RS subsetD, PQimp RS mp]) 1);
qed "Int_Collect_mono";

(*Used in intr_elim.ML and in individual datatype definitions*)
val basic_monos = [subset_refl, imp_refl, disj_mono, conj_mono, 
                   ex_mono, Collect_mono, in_mono];

