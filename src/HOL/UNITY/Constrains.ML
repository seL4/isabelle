(*  Title:      HOL/UNITY/Constrains
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Safety relations: restricted to the set of reachable states.
*)


(*** traces and reachable ***)

Goal "reachable F = {s. EX evs. (s,evs): traces (Init F) (Acts F)}";
by Safe_tac;
by (etac traces.induct 2);
by (etac reachable.induct 1);
by (ALLGOALS (blast_tac (claset() addIs reachable.intrs @ traces.intrs)));
qed "reachable_equiv_traces";

Goal "Init F <= reachable F";
by (blast_tac (claset() addIs reachable.intrs) 1);
qed "Init_subset_reachable";

Goal "Acts G <= Acts F ==> G : stable (reachable F)";
by (blast_tac (claset() addIs [stableI, constrainsI] @ reachable.intrs) 1);
qed "stable_reachable";


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


(*** Constrains ***)

overload_1st_set "Constrains.Constrains";

(*F : constrains B B'
  ==> F : constrains (reachable F Int B) (reachable F Int B')*)
bind_thm ("constrains_reachable_Int",
	  subset_refl RS
	  rewrite_rule [stable_def] stable_reachable RS 
	  constrains_Int);

Goalw [Constrains_def] "F : constrains A A' ==> F : Constrains A A'";
by (blast_tac (claset() addIs [constrains_reachable_Int]) 1);
qed "constrains_imp_Constrains";

Goalw [stable_def, Stable_def] "F : stable A ==> F : Stable A";
by (etac constrains_imp_Constrains 1);
qed "stable_imp_Stable";

val prems = Goal
    "(!!act s s'. [| act: Acts F;  (s,s') : act;  s: A |] ==> s': A') \
\    ==> F : Constrains A A'";
by (rtac constrains_imp_Constrains 1);
by (blast_tac (claset() addIs (constrainsI::prems)) 1);
qed "ConstrainsI";

Goalw [Constrains_def, constrains_def] "F : Constrains {} B";
by (Blast_tac 1);
qed "Constrains_empty";

Goal "F : Constrains A UNIV";
by (blast_tac (claset() addIs [ConstrainsI]) 1);
qed "Constrains_UNIV";
AddIffs [Constrains_empty, Constrains_UNIV];


Goalw [Constrains_def]
    "[| F : Constrains A A'; A'<=B' |] ==> F : Constrains A B'";
by (blast_tac (claset() addIs [constrains_weaken_R]) 1);
qed "Constrains_weaken_R";

Goalw [Constrains_def]
    "[| F : Constrains A A'; B<=A |] ==> F : Constrains B A'";
by (blast_tac (claset() addIs [constrains_weaken_L]) 1);
qed "Constrains_weaken_L";

Goalw [Constrains_def]
   "[| F : Constrains A A'; B<=A; A'<=B' |] ==> F : Constrains B B'";
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "Constrains_weaken";

(** Union **)

Goalw [Constrains_def]
    "[| F : Constrains A A'; F : Constrains B B' |]   \
\    ==> F : Constrains (A Un B) (A' Un B')";
by (blast_tac (claset() addIs [constrains_Un RS constrains_weaken]) 1);
qed "Constrains_Un";

Goal "ALL i:I. F : Constrains (A i) (A' i) \
\     ==> F : Constrains (UN i:I. A i) (UN i:I. A' i)";
by (asm_full_simp_tac (simpset() addsimps [Constrains_def]) 1);
by (dtac ball_constrains_UN 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "ball_Constrains_UN";

(** Intersection **)

Goalw [Constrains_def]
    "[| F : Constrains A A'; F : Constrains B B' |]   \
\    ==> F : Constrains (A Int B) (A' Int B')";
by (blast_tac (claset() addIs [constrains_Int RS constrains_weaken]) 1);
qed "Constrains_Int";

Goal "ALL i:I. F : Constrains (A i) (A' i)   \
\     ==> F : Constrains (INT i:I. A i) (INT i:I. A' i)";
by (asm_full_simp_tac (simpset() addsimps [Constrains_def]) 1);
by (dtac ball_constrains_INT 1);
by (dtac constrains_reachable_Int 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "ball_Constrains_INT";

Goal "F : Constrains A A' ==> reachable F Int A <= A'";
by (asm_full_simp_tac (simpset() addsimps [Constrains_def]) 1);
by (dtac constrains_imp_subset 1);
by (ALLGOALS
    (full_simp_tac (simpset() addsimps [Int_subset_iff, Int_lower1])));
qed "Constrains_imp_subset";

Goalw [Constrains_def]
    "[| F : Constrains A B; F : Constrains B C |]   \
\    ==> F : Constrains A C";
by (blast_tac (claset() addIs [constrains_trans, constrains_weaken]) 1);
qed "Constrains_trans";

Goalw [Constrains_def, constrains_def]
   "[| F : Constrains A (A' Un B); F : Constrains B B' |] \
\   ==> F : Constrains A (A' Un B')";
by (Clarify_tac 1);
by (Blast_tac 1);
qed "Constrains_cancel";


(*** Stable ***)

Goal "(F : Stable A) = (F : stable (reachable F Int A))";
by (simp_tac (simpset() addsimps [Stable_def, Constrains_def, stable_def]) 1);
qed "Stable_eq_stable";

Goalw [Stable_def] "F : Constrains A A ==> F : Stable A";
by (assume_tac 1);
qed "StableI";

Goalw [Stable_def] "F : Stable A ==> F : Constrains A A";
by (assume_tac 1);
qed "StableD";

Goalw [Stable_def]
    "[| F : Stable A; F : Stable A' |] ==> F : Stable (A Un A')";
by (blast_tac (claset() addIs [Constrains_Un]) 1);
qed "Stable_Un";

Goalw [Stable_def]
    "[| F : Stable A; F : Stable A' |] ==> F : Stable (A Int A')";
by (blast_tac (claset() addIs [Constrains_Int]) 1);
qed "Stable_Int";

Goalw [Stable_def]
    "[| F : Stable C; F : Constrains A (C Un A') |]   \
\    ==> F : Constrains (C Un A) (C Un A')";
by (blast_tac (claset() addIs [Constrains_Un RS Constrains_weaken]) 1);
qed "Stable_Constrains_Un";

Goalw [Stable_def]
    "[| F : Stable C; F : Constrains (C Int A) A' |]   \
\    ==> F : Constrains (C Int A) (C Int A')";
by (blast_tac (claset() addIs [Constrains_Int RS Constrains_weaken]) 1);
qed "Stable_Constrains_Int";

Goalw [Stable_def]
    "(ALL i:I. F : Stable (A i)) ==> F : Stable (UN i:I. A i)";
by (etac ball_Constrains_UN 1);
qed "ball_Stable_UN";

Goalw [Stable_def]
    "(ALL i:I. F : Stable (A i)) ==> F : Stable (INT i:I. A i)";
by (etac ball_Constrains_INT 1);
qed "ball_Stable_INT";

Goal "F : Stable (reachable F)";
by (simp_tac (simpset() addsimps [Stable_eq_stable, stable_reachable]) 1);
qed "Stable_reachable";



(*** Increasing ***)

Goalw [Increasing_def, Stable_def, Constrains_def, stable_def, constrains_def]
     "Increasing f <= Increasing (length o f)";
by Auto_tac;
by (blast_tac (claset() addIs [prefix_length_le, le_trans]) 1);
qed "Increasing_size";

Goalw [Increasing_def]
     "Increasing f <= {F. ALL z::nat. F: Stable {s. z < f s}}";
by (simp_tac (simpset() addsimps [Suc_le_eq RS sym]) 1);
by (Blast_tac 1);
qed "Increasing_Stable_less";

Goalw [increasing_def, Increasing_def]
     "F : increasing f ==> F : Increasing f";
by (blast_tac (claset() addIs [stable_imp_Stable]) 1);
qed "increasing_imp_Increasing";



(*** The Elimination Theorem.  The "free" m has become universally quantified!
     Should the premise be !!m instead of ALL m ?  Would make it harder to use
     in forward proof. ***)

Goalw [Constrains_def, constrains_def]
    "[| ALL m. F : Constrains {s. s x = m} (B m) |] \
\    ==> F : Constrains {s. s x : M} (UN m:M. B m)";
by (Blast_tac 1);
qed "Elimination";

(*As above, but for the trivial case of a one-variable state, in which the
  state is identified with its one variable.*)
Goalw [Constrains_def, constrains_def]
    "(ALL m. F : Constrains {m} (B m)) ==> F : Constrains M (UN m:M. B m)";
by (Blast_tac 1);
qed "Elimination_sing";


(*** Specialized laws for handling Invariants ***)

(** Natural deduction rules for "Invariant F A" **)

Goal "[| Init F<=A;  F : Stable A |] ==> F : Invariant A";
by (asm_simp_tac (simpset() addsimps [Invariant_def]) 1);
qed "InvariantI";

Goal "F : Invariant A ==> Init F<=A & F : Stable A";
by (asm_full_simp_tac (simpset() addsimps [Invariant_def]) 1);
qed "InvariantD";

bind_thm ("InvariantE", InvariantD RS conjE);


(*The set of all reachable states is the strongest Invariant*)
Goal "F : Invariant A ==> reachable F <= A";
by (full_simp_tac 
    (simpset() addsimps [Stable_def, Constrains_def, constrains_def, 
			 Invariant_def]) 1);
by (rtac subsetI 1);
by (etac reachable.induct 1);
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "Invariant_includes_reachable";

Goalw [Invariant_def, invariant_def, Stable_def, Constrains_def, stable_def]
     "F : invariant A ==> F : Invariant A";
by (blast_tac (claset() addIs [constrains_reachable_Int]) 1);
qed "invariant_imp_Invariant";

Goalw [Invariant_def, invariant_def, Stable_def, Constrains_def, stable_def]
     "Invariant A = {F. F : invariant (reachable F Int A)}";
by (blast_tac (claset() addIs reachable.intrs) 1);
qed "Invariant_eq_invariant_reachable";

(*Invariant is the "always" notion*)
Goal "Invariant A = {F. reachable F <= A}";
by (auto_tac (claset() addDs [invariant_includes_reachable],
	      simpset() addsimps [Int_absorb2, invariant_reachable,
				  Invariant_eq_invariant_reachable]));
qed "Invariant_eq_always";


Goal "Invariant A = (UN I: Pow A. invariant I)";
by (simp_tac (simpset() addsimps [Invariant_eq_always]) 1);
by (blast_tac (claset() addIs [invariantI, impOfSubs Init_subset_reachable, 
                               stable_reachable,
			       impOfSubs invariant_includes_reachable]) 1);
qed "Invariant_eq_UN_invariant";


(*** "Constrains" rules involving Invariant ***)

Goal "[| F : Invariant INV;  F : Constrains (INV Int A) A' |]   \
\     ==> F : Constrains A A'";
by (asm_full_simp_tac
    (simpset() addsimps [Invariant_includes_reachable RS Int_absorb2,
			 Constrains_def, Int_assoc RS sym]) 1);
qed "Invariant_ConstrainsI";

(* [| F : Invariant INV; F : Constrains (INV Int A) A |]
   ==> F : Stable A *)
bind_thm ("Invariant_StableI", Invariant_ConstrainsI RS StableI);

Goal "[| F : Invariant INV;  F : Constrains A A' |]   \
\     ==> F : Constrains A (INV Int A')";
by (asm_full_simp_tac
    (simpset() addsimps [Invariant_includes_reachable RS Int_absorb2,
			 Constrains_def, Int_assoc RS sym]) 1);
qed "Invariant_ConstrainsD";

bind_thm ("Invariant_StableD", StableD RSN (2,Invariant_ConstrainsD));



(** Conjoining Invariants **)

Goal "[| F : Invariant A;  F : Invariant B |] ==> F : Invariant (A Int B)";
by (auto_tac (claset(), simpset() addsimps [Invariant_eq_always]));
qed "Invariant_Int";

(*Delete the nearest invariance assumption (which will be the second one
  used by Invariant_Int) *)
val Invariant_thin =
    read_instantiate_sg (sign_of thy)
                [("V", "?F : Invariant ?A")] thin_rl;

(*Combines two invariance ASSUMPTIONS into one.  USEFUL??*)
val Invariant_Int_tac = dtac Invariant_Int THEN' 
                        assume_tac THEN'
			etac Invariant_thin;

(*Combines a list of invariance THEOREMS into one.*)
val Invariant_Int_rule = foldr1 (fn (th1,th2) => [th1,th2] MRS Invariant_Int);


(*To allow expansion of the program's definition when appropriate*)
val program_defs_ref = ref ([] : thm list);

(*proves "constrains" properties when the program is specified*)
fun constrains_tac i = 
   SELECT_GOAL
      (EVERY [simp_tac (simpset() addsimps !program_defs_ref) 1,
	      REPEAT (resolve_tac [StableI, stableI,
				   constrains_imp_Constrains] 1),
	      rtac constrainsI 1,
	      Full_simp_tac 1,
	      REPEAT (FIRSTGOAL (etac disjE)),
	      ALLGOALS Clarify_tac,
	      ALLGOALS Asm_full_simp_tac]) i;


