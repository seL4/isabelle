(*  Title:      HOL/UNITY/UNITY
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)

From Misra, "A Logic for Concurrent Programming", 1994
*)

set proof_timing;
HOL_quantifiers := false;


(*CAN BOOLEAN SIMPLIFICATION BE AUTOMATED?*)

(** Rewrites rules to eliminate A.  Conditions can be satisfied by letting B
    be any set including A Int C and contained in A Un C, such as B=A or B=C.
**)

Goal "[| A Int C <= B; B <= A Un C |] \
\              ==> (A Int B) Un (Compl A Int C) = B Un C";
by (Blast_tac 1);

Goal "[| A Int C <= B; B <= A Un C |] \
\              ==> (A Un B) Int (Compl A Un C) = B Int C";
by (Blast_tac 1);

(*The base B=A*)
Goal "A Un (Compl A Int C) = A Un C";
by (Blast_tac 1);

Goal "A Int (Compl A Un C) = A Int C";
by (Blast_tac 1);

(*The base B=C*)
Goal "(A Int C) Un (Compl A Int C) = C";
by (Blast_tac 1);

Goal "(A Un C) Int (Compl A Un C) = C";
by (Blast_tac 1);


(** More ad-hoc rules **)

Goal "A Un B - (A - B) = B";
by (Blast_tac 1);
qed "Un_Diff_Diff";

Goal "A Int (B - C) Un C = A Int B Un C";
by (Blast_tac 1);
qed "Int_Diff_Un";


open UNITY;


(*** constrains ***)

val prems = goalw thy [constrains_def]
    "(!!act s s'. [| act: Acts;  (s,s') : act;  s: A |] ==> s': A') \
\    ==> constrains Acts A A'";
by (blast_tac (claset() addIs prems) 1);
qed "constrainsI";

Goalw [constrains_def]
    "[| constrains Acts A A'; act: Acts;  (s,s'): act;  s: A |] \
\            ==> s': A'";
by (Blast_tac 1);
qed "constrainsD";

Goalw [constrains_def] "constrains Acts {} B";
by (Blast_tac 1);
qed "constrains_empty";

Goalw [constrains_def] "constrains Acts A UNIV";
by (Blast_tac 1);
qed "constrains_UNIV";
AddIffs [constrains_empty, constrains_UNIV];

Goalw [constrains_def]
    "[| constrains Acts A A'; A'<=B' |] ==> constrains Acts A B'";
by (Blast_tac 1);
qed "constrains_weaken_R";

Goalw [constrains_def]
    "[| constrains Acts A A'; B<=A |] ==> constrains Acts B A'";
by (Blast_tac 1);
qed "constrains_weaken_L";

Goalw [constrains_def]
   "[| constrains Acts A A'; B<=A; A'<=B' |] ==> constrains Acts B B'";
by (Blast_tac 1);
qed "constrains_weaken";

(*Set difference: UNUSED*)
Goalw [constrains_def]
  "[| constrains Acts (A-B) C; constrains Acts B C |] \
\       ==> constrains Acts A C";
by (Blast_tac 1);
qed "constrains_Diff";

(** Union **)

Goalw [constrains_def]
    "[| constrains Acts A A'; constrains Acts B B' |]   \
\           ==> constrains Acts (A Un B) (A' Un B')";
by (Blast_tac 1);
qed "constrains_Un";

Goalw [constrains_def]
    "ALL i:I. constrains Acts (A i) (A' i) \
\    ==> constrains Acts (UN i:I. A i) (UN i:I. A' i)";
by (Blast_tac 1);
qed "ball_constrains_UN";

Goalw [constrains_def]
    "[| ALL i. constrains Acts (A i) (A' i) |] \
\           ==> constrains Acts (UN i. A i) (UN i. A' i)";
by (Blast_tac 1);
qed "all_constrains_UN";

(** Intersection **)

Goalw [constrains_def]
    "[| constrains Acts A A'; constrains Acts B B' |]   \
\           ==> constrains Acts (A Int B) (A' Int B')";
by (Blast_tac 1);
qed "constrains_Int";

Goalw [constrains_def]
    "ALL i:I. constrains Acts (A i) (A' i) \
\    ==> constrains Acts (INT i:I. A i) (INT i:I. A' i)";
by (Blast_tac 1);
qed "ball_constrains_INT";

Goalw [constrains_def]
    "[| ALL i. constrains Acts (A i) (A' i) |] \
\           ==> constrains Acts (INT i. A i) (INT i. A' i)";
by (Blast_tac 1);
qed "all_constrains_INT";

Goalw [stable_def, constrains_def]
    "[| stable Acts C; constrains Acts A (C Un A') |]   \
\           ==> constrains Acts (C Un A) (C Un A')";
by (Blast_tac 1);
qed "stable_constrains_Un";

Goalw [stable_def, constrains_def]
    "[| stable Acts C; constrains Acts (C Int A) A' |]   \
\           ==> constrains Acts (C Int A) (C Int A')";
by (Blast_tac 1);
qed "stable_constrains_Int";


(*** stable ***)

Goalw [stable_def]
    "constrains Acts A A ==> stable Acts A";
by (assume_tac 1);
qed "stableI";

Goalw [stable_def]
    "stable Acts A ==> constrains Acts A A";
by (assume_tac 1);
qed "stableD";

Goalw [stable_def]
    "[| stable Acts A; stable Acts A' |]   \
\           ==> stable Acts (A Un A')";
by (blast_tac (claset() addIs [constrains_Un]) 1);
qed "stable_Un";

Goalw [stable_def]
    "[| stable Acts A; stable Acts A' |]   \
\           ==> stable Acts (A Int A')";
by (blast_tac (claset() addIs [constrains_Int]) 1);
qed "stable_Int";

Goalw [constrains_def]
    "[| constrains Acts A A'; id: Acts |] ==> A<=A'";
by (Blast_tac 1);
qed "constrains_imp_subset";


Goalw [constrains_def]
    "[| id: Acts; constrains Acts A B; constrains Acts B C |]   \
\           ==> constrains Acts A C";
by (Blast_tac 1);
qed "constrains_trans";


(*The Elimination Theorem.  The "free" m has become universally quantified!
  Should the premise be !!m instead of ALL m ?  Would make it harder to use
  in forward proof.*)
Goalw [constrains_def]
    "[| ALL m. constrains Acts {s. s x = m} (B m) |] \
\           ==> constrains Acts {s. P(s x)} (UN m. {s. P(m)} Int B m)";
by (Blast_tac 1);
qed "elimination";

(*As above, but for the trivial case of a one-variable state, in which the
  state is identified with its one variable.*)
Goalw [constrains_def]
    "[| ALL m. constrains Acts {m} (B m) |] \
\           ==> constrains Acts {s. P s} (UN m. {s. P(m)} Int B m)";
by (Blast_tac 1);
qed "elimination_sing";


Goalw [constrains_def]
   "[| constrains Acts A (A' Un B); constrains Acts B B'; id: Acts |] \
\           ==> constrains Acts A (A' Un B')";
by (Blast_tac 1);
qed "constrains_cancel";



(*** Theoretical Results from Section 6 ***)

Goalw [constrains_def, strongest_rhs_def]
    "constrains Acts A (strongest_rhs Acts A )";
by (Blast_tac 1);
qed "constrains_strongest_rhs";

Goalw [constrains_def, strongest_rhs_def]
    "constrains Acts A B ==> strongest_rhs Acts A <= B";
by (Blast_tac 1);
qed "strongest_rhs_is_strongest";
