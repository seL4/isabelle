(*  Title:      HOL/UNITY/Constrains
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Safety relations: restricted to the set of reachable states.
*)



(**MOVE TO EQUALITIES.ML**)

Goal "(A Un B <= C) = (A <= C & B <= C)";
by (Blast_tac 1);
qed "Un_subset_iff";

Goal "(C <= A Int B) = (C <= A & C <= B)";
by (Blast_tac 1);
qed "Int_subset_iff";


(*** Constrains ***)

(*constrains (Acts prg) B B'
  ==> constrains (Acts prg) (reachable prg Int B) (reachable prg Int B')*)
bind_thm ("constrains_reachable_Int",
	  subset_refl RS
	  rewrite_rule [stable_def] stable_reachable RS 
	  constrains_Int);

Goalw [Constrains_def]
    "constrains (Acts prg) A A' ==> Constrains prg A A'";
by (etac constrains_reachable_Int 1);
qed "constrains_imp_Constrains";

val prems = Goal
    "(!!act s s'. [| act: Acts prg;  (s,s') : act;  s: A |] ==> s': A') \
\    ==> Constrains prg A A'";
by (rtac constrains_imp_Constrains 1);
by (blast_tac (claset() addIs (constrainsI::prems)) 1);
qed "ConstrainsI";

Goalw [Constrains_def, constrains_def] "Constrains prg {} B";
by (Blast_tac 1);
qed "Constrains_empty";

Goal "Constrains prg A UNIV";
by (blast_tac (claset() addIs [ConstrainsI]) 1);
qed "Constrains_UNIV";
AddIffs [Constrains_empty, Constrains_UNIV];


Goalw [Constrains_def]
    "[| Constrains prg A A'; A'<=B' |] ==> Constrains prg A B'";
by (blast_tac (claset() addIs [constrains_weaken_R]) 1);
qed "Constrains_weaken_R";

Goalw [Constrains_def]
    "[| Constrains prg A A'; B<=A |] ==> Constrains prg B A'";
by (blast_tac (claset() addIs [constrains_weaken_L]) 1);
qed "Constrains_weaken_L";

Goalw [Constrains_def]
   "[| Constrains prg A A'; B<=A; A'<=B' |] ==> Constrains prg B B'";
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "Constrains_weaken";

(** Union **)

Goalw [Constrains_def]
    "[| Constrains prg A A'; Constrains prg B B' |]   \
\    ==> Constrains prg (A Un B) (A' Un B')";
by (blast_tac (claset() addIs [constrains_Un RS constrains_weaken]) 1);
qed "Constrains_Un";

Goalw [Constrains_def]
    "ALL i:I. Constrains prg (A i) (A' i) \
\    ==> Constrains prg (UN i:I. A i) (UN i:I. A' i)";
by (dtac ball_constrains_UN 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "ball_Constrains_UN";

(** Intersection **)

Goalw [Constrains_def]
    "[| Constrains prg A A'; Constrains prg B B' |]   \
\    ==> Constrains prg (A Int B) (A' Int B')";
by (blast_tac (claset() addIs [constrains_Int RS constrains_weaken]) 1);
qed "Constrains_Int";

Goalw [Constrains_def]
    "[| ALL i:I. Constrains prg (A i) (A' i) |]   \
\    ==> Constrains prg (INT i:I. A i) (INT i:I. A' i)";
by (dtac ball_constrains_INT 1);
by (blast_tac (claset() addIs [constrains_reachable_Int, constrains_weaken]) 1);
qed "ball_Constrains_INT";

Goalw [Constrains_def]
     "[| Constrains prg A A'; id: Acts prg |] ==> reachable prg Int A <= A'";
by (dtac constrains_imp_subset 1);
by (assume_tac 1);
by (full_simp_tac (simpset() addsimps [Int_subset_iff, Int_lower1]) 1);
qed "Constrains_imp_subset";

Goalw [Constrains_def]
    "[| id: Acts prg; Constrains prg A B; Constrains prg B C |]   \
\    ==> Constrains prg A C";
by (blast_tac (claset() addIs [constrains_trans, constrains_weaken]) 1);
qed "Constrains_trans";


(*** Stable ***)

Goal "Stable prg A = stable (Acts prg) (reachable prg Int A)";
by (simp_tac (simpset() addsimps [Stable_def, Constrains_def, stable_def]) 1);
qed "Stable_eq_stable";

Goalw [Stable_def] "Constrains prg A A ==> Stable prg A";
by (assume_tac 1);
qed "StableI";

Goalw [Stable_def] "Stable prg A ==> Constrains prg A A";
by (assume_tac 1);
qed "StableD";

Goalw [Stable_def]
    "[| Stable prg A; Stable prg A' |] ==> Stable prg (A Un A')";
by (blast_tac (claset() addIs [Constrains_Un]) 1);
qed "Stable_Un";

Goalw [Stable_def]
    "[| Stable prg A; Stable prg A' |] ==> Stable prg (A Int A')";
by (blast_tac (claset() addIs [Constrains_Int]) 1);
qed "Stable_Int";

Goalw [Stable_def]
    "[| Stable prg C; Constrains prg A (C Un A') |]   \
\    ==> Constrains prg (C Un A) (C Un A')";
by (blast_tac (claset() addIs [Constrains_Un RS Constrains_weaken]) 1);
qed "Stable_Constrains_Un";

Goalw [Stable_def]
    "[| Stable prg C; Constrains prg (C Int A) A' |]   \
\    ==> Constrains prg (C Int A) (C Int A')";
by (blast_tac (claset() addIs [Constrains_Int RS Constrains_weaken]) 1);
qed "Stable_Constrains_Int";

Goalw [Stable_def]
    "(ALL i:I. Stable prg (A i)) ==> Stable prg (INT i:I. A i)";
by (etac ball_Constrains_INT 1);
qed "ball_Stable_INT";

Goal "Stable prg (reachable prg)";
by (simp_tac (simpset() addsimps [Stable_eq_stable, stable_reachable]) 1);
qed "Stable_reachable";



(*** The Elimination Theorem.  The "free" m has become universally quantified!
     Should the premise be !!m instead of ALL m ?  Would make it harder to use
     in forward proof. ***)

Goalw [Constrains_def, constrains_def]
    "[| ALL m. Constrains prg {s. s x = m} (B m) |] \
\    ==> Constrains prg {s. s x : M} (UN m:M. B m)";
by (Blast_tac 1);
qed "Elimination";

(*As above, but for the trivial case of a one-variable state, in which the
  state is identified with its one variable.*)
Goalw [Constrains_def, constrains_def]
    "(ALL m. Constrains prg {m} (B m)) ==> Constrains prg M (UN m:M. B m)";
by (Blast_tac 1);
qed "Elimination_sing";

Goalw [Constrains_def, constrains_def]
   "[| Constrains prg A (A' Un B); Constrains prg B B'; id: Acts prg |] \
\   ==> Constrains prg A (A' Un B')";
by (Blast_tac 1);
qed "Constrains_cancel";


(*** Specialized laws for handling Invariants ***)

(** Natural deduction rules for "Invariant prg A" **)

Goal "[| Init prg<=A;  Stable prg A |] ==> Invariant prg A";
by (asm_simp_tac (simpset() addsimps [Invariant_def]) 1);
qed "InvariantI";

Goal "Invariant prg A ==> Init prg<=A & Stable prg A";
by (asm_full_simp_tac (simpset() addsimps [Invariant_def]) 1);
qed "InvariantD";

bind_thm ("InvariantE", InvariantD RS conjE);


(*The set of all reachable states is an Invariant...*)
Goal "Invariant prg (reachable prg)";
by (simp_tac (simpset() addsimps [Invariant_def]) 1);
by (blast_tac (claset() addIs (Stable_reachable::reachable.intrs)) 1);
qed "Invariant_reachable";

(*...in fact the strongest Invariant!*)
Goal "Invariant prg A ==> reachable prg <= A";
by (full_simp_tac 
    (simpset() addsimps [Stable_def, Constrains_def, constrains_def, 
			 Invariant_def]) 1);
by (rtac subsetI 1);
by (etac reachable.induct 1);
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "Invariant_includes_reachable";


Goal "Invariant prg INV ==> reachable prg Int INV = reachable prg";
by (dtac Invariant_includes_reachable 1);
by (Blast_tac 1);
qed "reachable_Int_INV";

Goal "[| Invariant prg INV;  Constrains prg (INV Int A) A' |]   \
\     ==> Constrains prg A A'";
by (asm_full_simp_tac
    (simpset() addsimps [Constrains_def, reachable_Int_INV,
			 Int_assoc RS sym]) 1);
qed "Invariant_ConstrainsI";

bind_thm ("Invariant_StableI", Invariant_ConstrainsI RS StableI);

Goal "[| Invariant prg INV;  Constrains prg A A' |]   \
\     ==> Constrains prg A (INV Int A')";
by (asm_full_simp_tac
    (simpset() addsimps [Constrains_def, reachable_Int_INV,
			 Int_assoc RS sym]) 1);
qed "Invariant_ConstrainsD";

bind_thm ("Invariant_StableD", StableD RSN (2,Invariant_ConstrainsD));



(** Conjoining Invariants **)

Goal "[| Invariant prg A;  Invariant prg B |] ==> Invariant prg (A Int B)";
by (auto_tac (claset(),
	      simpset() addsimps [Invariant_def, Stable_Int]));
qed "Invariant_Int";

(*Delete the nearest invariance assumption (which will be the second one
  used by Invariant_Int) *)
val Invariant_thin =
    read_instantiate_sg (sign_of thy)
                [("V", "Invariant ?Prg ?A")] thin_rl;

(*Combines two invariance ASSUMPTIONS into one.  USEFUL??*)
val Invariant_Int_tac = dtac Invariant_Int THEN' 
                        assume_tac THEN'
			etac Invariant_thin;

(*Combines two invariance THEOREMS into one.*)
val Invariant_Int_rule = foldr1 (fn (th1,th2) => [th1,th2] MRS Invariant_Int);



