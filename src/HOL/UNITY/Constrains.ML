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


(*** Co ***)

overload_1st_set "Constrains.op Co";

(*F : B co B' ==> F : (reachable F Int B) co (reachable F Int B')*)
bind_thm ("constrains_reachable_Int",
	  subset_refl RS
	  rewrite_rule [stable_def] stable_reachable RS 
	  constrains_Int);

(*Resembles the previous definition of Constrains*)
Goalw [Constrains_def]
     "A Co B = {F. F : (reachable F  Int  A) co (reachable F  Int  B)}";
by (blast_tac (claset() addDs [constrains_reachable_Int]
			addIs [constrains_weaken]) 1);
qed "Constrains_eq_constrains";

Goalw [Constrains_def] "F : A co A' ==> F : A Co A'";
by (blast_tac (claset() addIs [constrains_weaken_L]) 1);
qed "constrains_imp_Constrains";

Goalw [stable_def, Stable_def] "F : stable A ==> F : Stable A";
by (etac constrains_imp_Constrains 1);
qed "stable_imp_Stable";

val prems = Goal
    "(!!act s s'. [| act: Acts F;  (s,s') : act;  s: A |] ==> s': A') \
\    ==> F : A Co A'";
by (rtac constrains_imp_Constrains 1);
by (blast_tac (claset() addIs (constrainsI::prems)) 1);
qed "ConstrainsI";

Goalw [Constrains_def, constrains_def] "F : {} Co B";
by (Blast_tac 1);
qed "Constrains_empty";

Goal "F : A Co UNIV";
by (blast_tac (claset() addIs [ConstrainsI]) 1);
qed "Constrains_UNIV";
AddIffs [Constrains_empty, Constrains_UNIV];

Goalw [Constrains_def]
    "[| F : A Co A'; A'<=B' |] ==> F : A Co B'";
by (blast_tac (claset() addIs [constrains_weaken_R]) 1);
qed "Constrains_weaken_R";

Goalw [Constrains_def]
    "[| F : A Co A'; B<=A |] ==> F : B Co A'";
by (blast_tac (claset() addIs [constrains_weaken_L]) 1);
qed "Constrains_weaken_L";

Goalw [Constrains_def]
   "[| F : A Co A'; B<=A; A'<=B' |] ==> F : B Co B'";
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "Constrains_weaken";

(** Union **)

Goalw [Constrains_def]
    "[| F : A Co A'; F : B Co B' |]   \
\    ==> F : (A Un B) Co (A' Un B')";
by (blast_tac (claset() addIs [constrains_Un RS constrains_weaken]) 1);
qed "Constrains_Un";

Goal "ALL i:I. F : (A i) Co (A' i) \
\     ==> F : (UN i:I. A i) Co (UN i:I. A' i)";
by (asm_full_simp_tac (simpset() addsimps [Constrains_def]) 1);
by (dtac ball_constrains_UN 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "ball_Constrains_UN";

(** Intersection **)

Goalw [Constrains_def]
    "[| F : A Co A'; F : B Co B' |]   \
\    ==> F : (A Int B) Co (A' Int B')";
by (blast_tac (claset() addIs [constrains_Int RS constrains_weaken]) 1);
qed "Constrains_Int";

Goal "ALL i:I. F : (A i) Co (A' i)   \
\     ==> F : (INT i:I. A i) Co (INT i:I. A' i)";
by (asm_full_simp_tac (simpset() addsimps [Constrains_def]) 1);
by (dtac ball_constrains_INT 1);
by (dtac constrains_reachable_Int 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "ball_Constrains_INT";

Goal "F : A Co A' ==> reachable F Int A <= A'";
by (asm_full_simp_tac (simpset() addsimps [constrains_imp_subset, 
					   Constrains_def]) 1);
qed "Constrains_imp_subset";

Goal "[| F : A Co B; F : B Co C |] ==> F : A Co C";
by (full_simp_tac (simpset() addsimps [Constrains_eq_constrains]) 1);
by (blast_tac (claset() addIs [constrains_trans, constrains_weaken]) 1);
qed "Constrains_trans";

Goal "[| F : A Co (A' Un B); F : B Co B' |] ==> F : A Co (A' Un B')";
by (full_simp_tac (simpset() addsimps [Constrains_eq_constrains, 
				       constrains_def]) 1);
by (Blast_tac 1);
qed "Constrains_cancel";


(*** Stable ***)

Goal "(F : Stable A) = (F : stable (reachable F Int A))";
by (simp_tac (simpset() addsimps [Stable_def, Constrains_eq_constrains, 
				  stable_def]) 1);
qed "Stable_eq_stable";

Goalw [Stable_def] "F : A Co A ==> F : Stable A";
by (assume_tac 1);
qed "StableI";

Goalw [Stable_def] "F : Stable A ==> F : A Co A";
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
    "[| F : Stable C; F : A Co (C Un A') |]   \
\    ==> F : (C Un A) Co (C Un A')";
by (blast_tac (claset() addIs [Constrains_Un RS Constrains_weaken]) 1);
qed "Stable_Constrains_Un";

Goalw [Stable_def]
    "[| F : Stable C; F : (C Int A) Co A' |]   \
\    ==> F : (C Int A) Co (C Int A')";
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
     "mono g ==> Increasing f <= Increasing (g o f)";
by Auto_tac;
by (blast_tac (claset() addIs [monoD, order_trans]) 1);
qed "mono_Increasing_o";

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
    "[| ALL m. F : {s. s x = m} Co (B m) |] \
\    ==> F : {s. s x : M} Co (UN m:M. B m)";
by (Blast_tac 1);
qed "Elimination";

(*As above, but for the trivial case of a one-variable state, in which the
  state is identified with its one variable.*)
Goalw [Constrains_def, constrains_def]
    "(ALL m. F : {m} Co (B m)) ==> F : M Co (UN m:M. B m)";
by (Blast_tac 1);
qed "Elimination_sing";


(*** Specialized laws for handling Always ***)

(** Natural deduction rules for "Always A" **)

Goal "[| Init F<=A;  F : Stable A |] ==> F : Always A";
by (asm_simp_tac (simpset() addsimps [Always_def]) 1);
qed "AlwaysI";

Goal "F : Always A ==> Init F<=A & F : Stable A";
by (asm_full_simp_tac (simpset() addsimps [Always_def]) 1);
qed "AlwaysD";

bind_thm ("AlwaysE", AlwaysD RS conjE);


(*The set of all reachable states is Always*)
Goal "F : Always A ==> reachable F <= A";
by (full_simp_tac 
    (simpset() addsimps [Stable_def, Constrains_def, constrains_def, 
			 Always_def]) 1);
by (rtac subsetI 1);
by (etac reachable.induct 1);
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "Always_includes_reachable";

Goalw [Always_def, invariant_def, Stable_def, stable_def]
     "F : invariant A ==> F : Always A";
by (blast_tac (claset() addIs [constrains_imp_Constrains]) 1);
qed "invariant_imp_Always";

bind_thm ("Always_reachable", invariant_reachable RS invariant_imp_Always);

Goal "Always A = {F. F : invariant (reachable F Int A)}";
by (simp_tac (simpset() addsimps [Always_def, invariant_def, Stable_def, 
				  Constrains_eq_constrains, stable_def]) 1);
by (blast_tac (claset() addIs reachable.intrs) 1);
qed "Always_eq_invariant_reachable";

(*the RHS is the traditional definition of the "always" operator*)
Goal "Always A = {F. reachable F <= A}";
by (auto_tac (claset() addDs [invariant_includes_reachable],
	      simpset() addsimps [Int_absorb2, invariant_reachable,
				  Always_eq_invariant_reachable]));
qed "Always_eq_includes_reachable";


Goal "Always A = (UN I: Pow A. invariant I)";
by (simp_tac (simpset() addsimps [Always_eq_includes_reachable]) 1);
by (blast_tac (claset() addIs [invariantI, impOfSubs Init_subset_reachable, 
                               stable_reachable,
			       impOfSubs invariant_includes_reachable]) 1);
qed "Always_eq_UN_invariant";

Goal "[| F : Always A; A <= B |] ==> F : Always B";
by (auto_tac (claset(), simpset() addsimps [Always_eq_includes_reachable]));
qed "Always_weaken";


(*** "Co" rules involving Always ***)

Goal "[| F : Always INV;  F : (INV Int A) Co A' |] ==> F : A Co A'";
by (asm_full_simp_tac
    (simpset() addsimps [Always_includes_reachable RS Int_absorb2,
			 Constrains_def, Int_assoc RS sym]) 1);
qed "Always_ConstrainsI";

(* [| F : Always INV; F : (INV Int A) Co A |]
   ==> F : Stable A *)
bind_thm ("Always_StableI", Always_ConstrainsI RS StableI);

Goal "[| F : Always INV;  F : A Co A' |]   \
\     ==> F : A Co (INV Int A')";
by (asm_full_simp_tac
    (simpset() addsimps [Always_includes_reachable RS Int_absorb2,
			 Constrains_eq_constrains, Int_assoc RS sym]) 1);
qed "Always_ConstrainsD";

bind_thm ("Always_StableD", StableD RSN (2,Always_ConstrainsD));



(** Conjoining Always properties **)

Goal "[| F : Always A;  F : Always B |] ==> F : Always (A Int B)";
by (auto_tac (claset(), simpset() addsimps [Always_eq_includes_reachable]));
qed "Always_Int";

(*Delete the nearest invariance assumption (which will be the second one
  used by Always_Int) *)
val Always_thin =
    read_instantiate_sg (sign_of thy)
                [("V", "?F : Always ?A")] thin_rl;

(*Combines two invariance ASSUMPTIONS into one.  USEFUL??*)
val Always_Int_tac = dtac Always_Int THEN' assume_tac THEN' etac Always_thin;

(*Combines a list of invariance THEOREMS into one.*)
val Always_Int_rule = foldr1 (fn (th1,th2) => [th1,th2] MRS Always_Int);


(*To allow expansion of the program's definition when appropriate*)
val program_defs_ref = ref ([] : thm list);

(*proves "co" properties when the program is specified*)
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


