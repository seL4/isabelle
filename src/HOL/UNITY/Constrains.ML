(*  Title:      HOL/UNITY/Constrains
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Safety relations: restricted to the set of reachable states.
*)


(*** Constrains ***)

(*Map its type, ('a * 'a)set set, 'a set, 'a set] => bool, to just 'a*)
Blast.overloaded ("Constrains.Constrains", 
		  HOLogic.dest_setT o domain_type o range_type);

(*constrains (Acts F) B B'
  ==> constrains (Acts F) (reachable F Int B) (reachable F Int B')*)
bind_thm ("constrains_reachable_Int",
	  subset_refl RS
	  rewrite_rule [stable_def] stable_reachable RS 
	  constrains_Int);

Goalw [Constrains_def]
    "constrains (Acts F) A A' ==> Constrains F A A'";
by (etac constrains_reachable_Int 1);
qed "constrains_imp_Constrains";

val prems = Goal
    "(!!act s s'. [| act: Acts F;  (s,s') : act;  s: A |] ==> s': A') \
\    ==> Constrains F A A'";
by (rtac constrains_imp_Constrains 1);
by (blast_tac (claset() addIs (constrainsI::prems)) 1);
qed "ConstrainsI";

Goalw [Constrains_def, constrains_def] "Constrains F {} B";
by (Blast_tac 1);
qed "Constrains_empty";

Goal "Constrains F A UNIV";
by (blast_tac (claset() addIs [ConstrainsI]) 1);
qed "Constrains_UNIV";
AddIffs [Constrains_empty, Constrains_UNIV];


Goalw [Constrains_def]
    "[| Constrains F A A'; A'<=B' |] ==> Constrains F A B'";
by (blast_tac (claset() addIs [constrains_weaken_R]) 1);
qed "Constrains_weaken_R";

Goalw [Constrains_def]
    "[| Constrains F A A'; B<=A |] ==> Constrains F B A'";
by (blast_tac (claset() addIs [constrains_weaken_L]) 1);
qed "Constrains_weaken_L";

Goalw [Constrains_def]
   "[| Constrains F A A'; B<=A; A'<=B' |] ==> Constrains F B B'";
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "Constrains_weaken";

(** Union **)

Goalw [Constrains_def]
    "[| Constrains F A A'; Constrains F B B' |]   \
\    ==> Constrains F (A Un B) (A' Un B')";
by (blast_tac (claset() addIs [constrains_Un RS constrains_weaken]) 1);
qed "Constrains_Un";

Goalw [Constrains_def]
    "ALL i:I. Constrains F (A i) (A' i) \
\    ==> Constrains F (UN i:I. A i) (UN i:I. A' i)";
by (dtac ball_constrains_UN 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "ball_Constrains_UN";

(** Intersection **)

Goalw [Constrains_def]
    "[| Constrains F A A'; Constrains F B B' |]   \
\    ==> Constrains F (A Int B) (A' Int B')";
by (blast_tac (claset() addIs [constrains_Int RS constrains_weaken]) 1);
qed "Constrains_Int";

Goalw [Constrains_def]
    "[| ALL i:I. Constrains F (A i) (A' i) |]   \
\    ==> Constrains F (INT i:I. A i) (INT i:I. A' i)";
by (dtac ball_constrains_INT 1);
by (dtac constrains_reachable_Int 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "ball_Constrains_INT";

Goalw [Constrains_def]
     "Constrains F A A' ==> reachable F Int A <= A'";
by (dtac constrains_imp_subset 1);
by (ALLGOALS
    (full_simp_tac (simpset() addsimps [Int_subset_iff, Int_lower1])));
qed "Constrains_imp_subset";

Goalw [Constrains_def]
    "[| Constrains F A B; Constrains F B C |]   \
\    ==> Constrains F A C";
by (blast_tac (claset() addIs [constrains_trans, constrains_weaken]) 1);
qed "Constrains_trans";


(*** Stable ***)

Goal "Stable F A = stable (Acts F) (reachable F Int A)";
by (simp_tac (simpset() addsimps [Stable_def, Constrains_def, stable_def]) 1);
qed "Stable_eq_stable";

Goalw [Stable_def] "Constrains F A A ==> Stable F A";
by (assume_tac 1);
qed "StableI";

Goalw [Stable_def] "Stable F A ==> Constrains F A A";
by (assume_tac 1);
qed "StableD";

Goalw [Stable_def]
    "[| Stable F A; Stable F A' |] ==> Stable F (A Un A')";
by (blast_tac (claset() addIs [Constrains_Un]) 1);
qed "Stable_Un";

Goalw [Stable_def]
    "[| Stable F A; Stable F A' |] ==> Stable F (A Int A')";
by (blast_tac (claset() addIs [Constrains_Int]) 1);
qed "Stable_Int";

Goalw [Stable_def]
    "[| Stable F C; Constrains F A (C Un A') |]   \
\    ==> Constrains F (C Un A) (C Un A')";
by (blast_tac (claset() addIs [Constrains_Un RS Constrains_weaken]) 1);
qed "Stable_Constrains_Un";

Goalw [Stable_def]
    "[| Stable F C; Constrains F (C Int A) A' |]   \
\    ==> Constrains F (C Int A) (C Int A')";
by (blast_tac (claset() addIs [Constrains_Int RS Constrains_weaken]) 1);
qed "Stable_Constrains_Int";

Goalw [Stable_def]
    "(ALL i:I. Stable F (A i)) ==> Stable F (INT i:I. A i)";
by (etac ball_Constrains_INT 1);
qed "ball_Stable_INT";

Goal "Stable F (reachable F)";
by (simp_tac (simpset() addsimps [Stable_eq_stable, stable_reachable]) 1);
qed "Stable_reachable";



(*** The Elimination Theorem.  The "free" m has become universally quantified!
     Should the premise be !!m instead of ALL m ?  Would make it harder to use
     in forward proof. ***)

Goalw [Constrains_def, constrains_def]
    "[| ALL m. Constrains F {s. s x = m} (B m) |] \
\    ==> Constrains F {s. s x : M} (UN m:M. B m)";
by (Blast_tac 1);
qed "Elimination";

(*As above, but for the trivial case of a one-variable state, in which the
  state is identified with its one variable.*)
Goalw [Constrains_def, constrains_def]
    "(ALL m. Constrains F {m} (B m)) ==> Constrains F M (UN m:M. B m)";
by (Blast_tac 1);
qed "Elimination_sing";

Goalw [Constrains_def, constrains_def]
   "[| Constrains F A (A' Un B); Constrains F B B' |] \
\   ==> Constrains F A (A' Un B')";
by (Blast_tac 1);
qed "Constrains_cancel";


(*** Specialized laws for handling Invariants ***)

(** Natural deduction rules for "Invariant F A" **)

Goal "[| Init F<=A;  Stable F A |] ==> Invariant F A";
by (asm_simp_tac (simpset() addsimps [Invariant_def]) 1);
qed "InvariantI";

Goal "Invariant F A ==> Init F<=A & Stable F A";
by (asm_full_simp_tac (simpset() addsimps [Invariant_def]) 1);
qed "InvariantD";

bind_thm ("InvariantE", InvariantD RS conjE);


(*The set of all reachable states is an Invariant...*)
Goal "Invariant F (reachable F)";
by (simp_tac (simpset() addsimps [Invariant_def]) 1);
by (blast_tac (claset() addIs (Stable_reachable::reachable.intrs)) 1);
qed "Invariant_reachable";

(*...in fact the strongest Invariant!*)
Goal "Invariant F A ==> reachable F <= A";
by (full_simp_tac 
    (simpset() addsimps [Stable_def, Constrains_def, constrains_def, 
			 Invariant_def]) 1);
by (rtac subsetI 1);
by (etac reachable.induct 1);
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "Invariant_includes_reachable";


Goal "Invariant F INV ==> reachable F Int INV = reachable F";
by (dtac Invariant_includes_reachable 1);
by (Blast_tac 1);
qed "reachable_Int_INV";

Goal "[| Invariant F INV;  Constrains F (INV Int A) A' |]   \
\     ==> Constrains F A A'";
by (asm_full_simp_tac
    (simpset() addsimps [Constrains_def, reachable_Int_INV,
			 Int_assoc RS sym]) 1);
qed "Invariant_ConstrainsI";

(* [| Invariant F INV; Constrains F (INV Int A) A |]
   ==> Stable F A *)
bind_thm ("Invariant_StableI", Invariant_ConstrainsI RS StableI);

Goal "[| Invariant F INV;  Constrains F A A' |]   \
\     ==> Constrains F A (INV Int A')";
by (asm_full_simp_tac
    (simpset() addsimps [Constrains_def, reachable_Int_INV,
			 Int_assoc RS sym]) 1);
qed "Invariant_ConstrainsD";

bind_thm ("Invariant_StableD", StableD RSN (2,Invariant_ConstrainsD));



(** Conjoining Invariants **)

Goal "[| Invariant F A;  Invariant F B |] ==> Invariant F (A Int B)";
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

(*Combines a list of invariance THEOREMS into one.*)
val Invariant_Int_rule = foldr1 (fn (th1,th2) => [th1,th2] MRS Invariant_Int);


(*proves "constrains" properties when the program is specified*)
val constrains_tac = 
   SELECT_GOAL
      (EVERY [REPEAT (resolve_tac [StableI, stableI,
				   constrains_imp_Constrains] 1),
	      rtac constrainsI 1,
	      Full_simp_tac 1,
	      REPEAT (FIRSTGOAL (etac disjE)),
	      ALLGOALS Clarify_tac,
	      ALLGOALS Asm_full_simp_tac]);


