(*  Title:      HOL/UNITY/UNITY
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)

From Misra, "A Logic for Concurrent Programming", 1994
*)

set proof_timing;
HOL_quantifiers := false;


(*** constrains ***)

val prems = Goalw [constrains_def]
    "(!!act s s'. [| act: acts;  (s,s') : act;  s: A |] ==> s': A') \
\    ==> constrains acts A A'";
by (blast_tac (claset() addIs prems) 1);
qed "constrainsI";

Goalw [constrains_def]
    "[| constrains acts A A'; act: acts;  (s,s'): act;  s: A |] ==> s': A'";
by (Blast_tac 1);
qed "constrainsD";

Goalw [constrains_def] "constrains acts {} B";
by (Blast_tac 1);
qed "constrains_empty";

Goalw [constrains_def] "constrains acts A UNIV";
by (Blast_tac 1);
qed "constrains_UNIV";
AddIffs [constrains_empty, constrains_UNIV];

Goalw [constrains_def]
    "[| constrains acts A A'; A'<=B' |] ==> constrains acts A B'";
by (Blast_tac 1);
qed "constrains_weaken_R";

Goalw [constrains_def]
    "[| constrains acts A A'; B<=A |] ==> constrains acts B A'";
by (Blast_tac 1);
qed "constrains_weaken_L";

Goalw [constrains_def]
   "[| constrains acts A A'; B<=A; A'<=B' |] ==> constrains acts B B'";
by (Blast_tac 1);
qed "constrains_weaken";

(** Union **)

Goalw [constrains_def]
    "[| constrains acts A A'; constrains acts B B' |]   \
\    ==> constrains acts (A Un B) (A' Un B')";
by (Blast_tac 1);
qed "constrains_Un";

Goalw [constrains_def]
    "ALL i:I. constrains acts (A i) (A' i) \
\    ==> constrains acts (UN i:I. A i) (UN i:I. A' i)";
by (Blast_tac 1);
qed "ball_constrains_UN";

Goalw [constrains_def]
    "[| ALL i. constrains acts (A i) (A' i) |] \
\    ==> constrains acts (UN i. A i) (UN i. A' i)";
by (Blast_tac 1);
qed "all_constrains_UN";

(** Intersection **)

Goalw [constrains_def]
    "[| constrains acts A A'; constrains acts B B' |]   \
\    ==> constrains acts (A Int B) (A' Int B')";
by (Blast_tac 1);
qed "constrains_Int";

Goalw [constrains_def]
    "ALL i:I. constrains acts (A i) (A' i) \
\    ==> constrains acts (INT i:I. A i) (INT i:I. A' i)";
by (Blast_tac 1);
qed "ball_constrains_INT";

Goalw [constrains_def]
    "[| ALL i. constrains acts (A i) (A' i) |] \
\    ==> constrains acts (INT i. A i) (INT i. A' i)";
by (Blast_tac 1);
qed "all_constrains_INT";

Goalw [constrains_def] "[| constrains acts A A'; id: acts |] ==> A<=A'";
by (Blast_tac 1);
qed "constrains_imp_subset";

Goalw [constrains_def]
    "[| id: acts; constrains acts A B; constrains acts B C |]   \
\    ==> constrains acts A C";
by (Blast_tac 1);
qed "constrains_trans";


(*** stable ***)

Goalw [stable_def] "constrains acts A A ==> stable acts A";
by (assume_tac 1);
qed "stableI";

Goalw [stable_def] "stable acts A ==> constrains acts A A";
by (assume_tac 1);
qed "stableD";

Goalw [stable_def]
    "[| stable acts A; stable acts A' |] ==> stable acts (A Un A')";
by (blast_tac (claset() addIs [constrains_Un]) 1);
qed "stable_Un";

Goalw [stable_def]
    "[| stable acts A; stable acts A' |] ==> stable acts (A Int A')";
by (blast_tac (claset() addIs [constrains_Int]) 1);
qed "stable_Int";

Goalw [stable_def, constrains_def]
    "[| stable acts C; constrains acts A (C Un A') |]   \
\    ==> constrains acts (C Un A) (C Un A')";
by (Blast_tac 1);
qed "stable_constrains_Un";

Goalw [stable_def, constrains_def]
    "[| stable acts C; constrains acts (C Int A) A' |]   \
\    ==> constrains acts (C Int A) (C Int A')";
by (Blast_tac 1);
qed "stable_constrains_Int";


(*The Elimination Theorem.  The "free" m has become universally quantified!
  Should the premise be !!m instead of ALL m ?  Would make it harder to use
  in forward proof.*)
Goalw [constrains_def]
    "[| ALL m. constrains acts {s. s x = m} (B m) |] \
\    ==> constrains acts {s. s x : M} (UN m:M. B m)";
by (Blast_tac 1);
qed "elimination";


(*As above, but for the trivial case of a one-variable state, in which the
  state is identified with its one variable.*)
Goalw [constrains_def]
    "(ALL m. constrains acts {m} (B m)) ==> constrains acts M (UN m:M. B m)";
by (Blast_tac 1);
qed "elimination_sing";


Goalw [constrains_def]
   "[| constrains acts A (A' Un B); constrains acts B B'; id: acts |] \
\   ==> constrains acts A (A' Un B')";
by (Blast_tac 1);
qed "constrains_cancel";



(*** Theoretical Results from Section 6 ***)

Goalw [constrains_def, strongest_rhs_def]
    "constrains acts A (strongest_rhs acts A )";
by (Blast_tac 1);
qed "constrains_strongest_rhs";

Goalw [constrains_def, strongest_rhs_def]
    "constrains acts A B ==> strongest_rhs acts A <= B";
by (Blast_tac 1);
qed "strongest_rhs_is_strongest";
