(*  Title:      HOL/UNITY/UNITY
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)

From Misra, "A Logic for Concurrent Programming", 1994
*)

set proof_timing;
HOL_quantifiers := false;


(*** General lemmas ***)

Goal "UNIV Times UNIV = UNIV";
by Auto_tac;
qed "UNIV_Times_UNIV"; 
Addsimps [UNIV_Times_UNIV];

Goal "- (UNIV Times A) = UNIV Times (-A)";
by Auto_tac;
qed "Compl_Times_UNIV1"; 

Goal "- (A Times UNIV) = (-A) Times UNIV";
by Auto_tac;
qed "Compl_Times_UNIV2"; 

Addsimps [Compl_Times_UNIV1, Compl_Times_UNIV2]; 


(*** constrains ***)

overload_1st_set "UNITY.constrains";
overload_1st_set "UNITY.stable";
overload_1st_set "UNITY.unless";

val prems = Goalw [constrains_def]
    "(!!act s s'. [| act: Acts F;  (s,s') : act;  s: A |] ==> s': A') \
\    ==> F : constrains A A'";
by (blast_tac (claset() addIs prems) 1);
qed "constrainsI";

Goalw [constrains_def]
    "[| F : constrains A A'; act: Acts F;  (s,s'): act;  s: A |] ==> s': A'";
by (Blast_tac 1);
qed "constrainsD";

Goalw [constrains_def] "F : constrains {} B";
by (Blast_tac 1);
qed "constrains_empty";

Goalw [constrains_def] "F : constrains A UNIV";
by (Blast_tac 1);
qed "constrains_UNIV";
AddIffs [constrains_empty, constrains_UNIV];

(*monotonic in 2nd argument*)
Goalw [constrains_def]
    "[| F : constrains A A'; A'<=B' |] ==> F : constrains A B'";
by (Blast_tac 1);
qed "constrains_weaken_R";

(*anti-monotonic in 1st argument*)
Goalw [constrains_def]
    "[| F : constrains A A'; B<=A |] ==> F : constrains B A'";
by (Blast_tac 1);
qed "constrains_weaken_L";

Goalw [constrains_def]
   "[| F : constrains A A'; B<=A; A'<=B' |] ==> F : constrains B B'";
by (Blast_tac 1);
qed "constrains_weaken";

(** Union **)

Goalw [constrains_def]
    "[| F : constrains A A'; F : constrains B B' |]   \
\    ==> F : constrains (A Un B) (A' Un B')";
by (Blast_tac 1);
qed "constrains_Un";

Goalw [constrains_def]
    "ALL i:I. F : constrains (A i) (A' i) \
\    ==> F : constrains (UN i:I. A i) (UN i:I. A' i)";
by (Blast_tac 1);
qed "ball_constrains_UN";

(** Intersection **)

Goalw [constrains_def]
    "[| F : constrains A A'; F : constrains B B' |]   \
\    ==> F : constrains (A Int B) (A' Int B')";
by (Blast_tac 1);
qed "constrains_Int";

Goalw [constrains_def]
    "ALL i:I. F : constrains (A i) (A' i) \
\    ==> F : constrains (INT i:I. A i) (INT i:I. A' i)";
by (Blast_tac 1);
qed "ball_constrains_INT";

Goalw [constrains_def] "F : constrains A A' ==> A <= A'";
by Auto_tac;
qed "constrains_imp_subset";

(*The reasoning is by subsets since "constrains" refers to single actions
  only.  So this rule isn't that useful.*)
Goalw [constrains_def]
    "[| F : constrains A B; F : constrains B C |]   \
\    ==> F : constrains A C";
by (Blast_tac 1);
qed "constrains_trans";

Goalw [constrains_def]
   "[| F : constrains A (A' Un B); F : constrains B B' |] \
\   ==> F : constrains A (A' Un B')";
by (Clarify_tac 1);
by (Blast_tac 1);
qed "constrains_cancel";


(*** stable ***)

Goalw [stable_def] "F : constrains A A ==> F : stable A";
by (assume_tac 1);
qed "stableI";

Goalw [stable_def] "F : stable A ==> F : constrains A A";
by (assume_tac 1);
qed "stableD";

(** Union **)

Goalw [stable_def]
    "[| F : stable A; F : stable A' |] ==> F : stable (A Un A')";
by (blast_tac (claset() addIs [constrains_Un]) 1);
qed "stable_Un";

Goalw [stable_def]
    "ALL i:I. F : stable (A i) ==> F : stable (UN i:I. A i)";
by (blast_tac (claset() addIs [ball_constrains_UN]) 1);
qed "ball_stable_UN";

(** Intersection **)

Goalw [stable_def]
    "[| F : stable A; F : stable A' |] ==> F : stable (A Int A')";
by (blast_tac (claset() addIs [constrains_Int]) 1);
qed "stable_Int";

Goalw [stable_def]
    "ALL i:I. F : stable (A i) ==> F : stable (INT i:I. A i)";
by (blast_tac (claset() addIs [ball_constrains_INT]) 1);
qed "ball_stable_INT";

Goalw [stable_def, constrains_def]
    "[| F : stable C; F : constrains A (C Un A') |]   \
\    ==> F : constrains (C Un A) (C Un A')";
by (Blast_tac 1);
qed "stable_constrains_Un";

Goalw [stable_def, constrains_def]
    "[| F : stable C; F : constrains (C Int A) A' |]   \
\    ==> F : constrains (C Int A) (C Int A')";
by (Blast_tac 1);
qed "stable_constrains_Int";

Goal "Init F <= reachable F";
by (blast_tac (claset() addIs reachable.intrs) 1);
qed "Init_subset_reachable";

Goal "Acts G <= Acts F ==> G : stable (reachable F)";
by (blast_tac (claset() addIs [stableI, constrainsI] @ reachable.intrs) 1);
qed "stable_reachable";

(*[| F : stable C; F : constrains (C Int A) A |] ==> F : stable (C Int A)*)
bind_thm ("stable_constrains_stable", stable_constrains_Int RS stableI);


(*** invariant ***)

Goal "[| Init F<=A;  F: stable A |] ==> F : invariant A";
by (asm_simp_tac (simpset() addsimps [invariant_def]) 1);
qed "invariantI";

(*Could also say "invariant A Int invariant B <= invariant (A Int B)"*)
Goal "[| F : invariant A;  F : invariant B |] ==> F : invariant (A Int B)";
by (auto_tac (claset(), simpset() addsimps [invariant_def, stable_Int]));
qed "invariant_Int";

(*The set of all reachable states is an invariant...*)
Goal "F : invariant (reachable F)";
by (simp_tac (simpset() addsimps [invariant_def]) 1);
by (blast_tac (claset() addIs (stable_reachable::reachable.intrs)) 1);
qed "invariant_reachable";

(*...in fact the strongest invariant!*)
Goal "F : invariant A ==> reachable F <= A";
by (full_simp_tac 
    (simpset() addsimps [stable_def, constrains_def, invariant_def]) 1);
by (rtac subsetI 1);
by (etac reachable.induct 1);
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "invariant_includes_reachable";


(*** increasing ***)

Goalw [increasing_def, stable_def, constrains_def]
     "increasing f <= increasing (length o f)";
by Auto_tac;
by (blast_tac (claset() addIs [prefix_length_le, le_trans]) 1);
qed "increasing_size";

Goalw [increasing_def]
     "increasing f <= {F. ALL z::nat. F: stable {s. z < f s}}";
by (simp_tac (simpset() addsimps [Suc_le_eq RS sym]) 1);
by (Blast_tac 1);
qed "increasing_stable_less";


(** The Elimination Theorem.  The "free" m has become universally quantified!
    Should the premise be !!m instead of ALL m ?  Would make it harder to use
    in forward proof. **)

Goalw [constrains_def]
    "[| ALL m. F : constrains {s. s x = m} (B m) |] \
\    ==> F : constrains {s. s x : M} (UN m:M. B m)";
by (Blast_tac 1);
qed "elimination";

(*As above, but for the trivial case of a one-variable state, in which the
  state is identified with its one variable.*)
Goalw [constrains_def]
    "(ALL m. F : constrains {m} (B m)) ==> F : constrains M (UN m:M. B m)";
by (Blast_tac 1);
qed "elimination_sing";



(*** Theoretical Results from Section 6 ***)

Goalw [constrains_def, strongest_rhs_def]
    "F : constrains A (strongest_rhs F A )";
by (Blast_tac 1);
qed "constrains_strongest_rhs";

Goalw [constrains_def, strongest_rhs_def]
    "F : constrains A B ==> strongest_rhs F A <= B";
by (Blast_tac 1);
qed "strongest_rhs_is_strongest";
