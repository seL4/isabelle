(*  Title:      HOL/UNITY/SubstAx
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

LeadsTo relation, restricted to the set of reachable states.
*)

overload_1st_set "SubstAx.op LeadsTo";


(*Resembles the previous definition of LeadsTo*)
Goalw [LeadsTo_def]
     "A LeadsTo B = {F. F : (reachable F Int A) leadsTo (reachable F Int B)}";
by (blast_tac (claset() addDs [psp_stable2] addIs [leadsTo_weaken]) 1);
qed "LeadsTo_eq_leadsTo";


(*** Specialized laws for handling invariants ***)

(** Conjoining an Always property **)

Goal "F : Always INV ==> (F : (INV Int A) LeadsTo A') = (F : A LeadsTo A')";
by (asm_full_simp_tac
    (simpset() addsimps [LeadsTo_def, Always_eq_includes_reachable,
			 Int_absorb2, Int_assoc RS sym]) 1);
qed "Always_LeadsTo_pre";

Goal "F : Always INV ==> (F : A LeadsTo (INV Int A')) = (F : A LeadsTo A')";
by (asm_full_simp_tac
    (simpset() addsimps [LeadsTo_eq_leadsTo, Always_eq_includes_reachable, 
			 Int_absorb2, Int_assoc RS sym]) 1);
qed "Always_LeadsTo_post";

(* [| F : Always C;  F : (C Int A) LeadsTo A' |] ==> F : A LeadsTo A' *)
bind_thm ("Always_LeadsToI", Always_LeadsTo_pre RS iffD1);

(* [| F : Always INV;  F : A LeadsTo A' |] ==> F : A LeadsTo (INV Int A') *)
bind_thm ("Always_LeadsToD", Always_LeadsTo_post RS iffD2);


(*** Introduction rules: Basis, Trans, Union ***)

Goal "F : A leadsTo B ==> F : A LeadsTo B";
by (simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [leadsTo_weaken_L]) 1);
qed "leadsTo_imp_LeadsTo";

Goal "[| F : A LeadsTo B;  F : B LeadsTo C |] ==> F : A LeadsTo C";
by (full_simp_tac (simpset() addsimps [LeadsTo_eq_leadsTo]) 1);
by (blast_tac (claset() addIs [leadsTo_Trans]) 1);
qed "LeadsTo_Trans";

val prems = Goalw [LeadsTo_def]
     "(!!A. A : S ==> F : A LeadsTo B) ==> F : (Union S) LeadsTo B";
by (Simp_tac 1);
by (stac Int_Union 1);
by (blast_tac (claset() addIs [leadsTo_UN] addDs prems) 1);
qed "LeadsTo_Union";


(*** Derived rules ***)

Goal "F : A LeadsTo UNIV";
by (simp_tac (simpset() addsimps [LeadsTo_def]) 1);
qed "LeadsTo_UNIV";
Addsimps [LeadsTo_UNIV];

(*Useful with cancellation, disjunction*)
Goal "F : A LeadsTo (A' Un A') ==> F : A LeadsTo A'";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "LeadsTo_Un_duplicate";

Goal "F : A LeadsTo (A' Un C Un C) ==> F : A LeadsTo (A' Un C)";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "LeadsTo_Un_duplicate2";

val prems = 
Goal "(!!i. i : I ==> F : (A i) LeadsTo B) ==> F : (UN i:I. A i) LeadsTo B";
by (simp_tac (HOL_ss addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs (LeadsTo_Union::prems)) 1);
qed "LeadsTo_UN";

(*Binary union introduction rule*)
Goal "[| F : A LeadsTo C; F : B LeadsTo C |] ==> F : (A Un B) LeadsTo C";
by (stac Un_eq_Union 1);
by (blast_tac (claset() addIs [LeadsTo_Union]) 1);
qed "LeadsTo_Un";

(*Lets us look at the starting state*)
val prems = 
Goal "(!!s. s : A ==> F : {s} LeadsTo B) ==> F : A LeadsTo B";
by (stac (UN_singleton RS sym) 1 THEN rtac LeadsTo_UN 1);
by (blast_tac (claset() addIs prems) 1);
qed "single_LeadsTo_I";

Goal "A <= B ==> F : A LeadsTo B";
by (simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
qed "subset_imp_LeadsTo";

bind_thm ("empty_LeadsTo", empty_subsetI RS subset_imp_LeadsTo);
Addsimps [empty_LeadsTo];

Goal "[| F : A LeadsTo A';  A' <= B' |] ==> F : A LeadsTo B'";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [leadsTo_weaken_R]) 1);
qed_spec_mp "LeadsTo_weaken_R";

Goal "[| F : A LeadsTo A';  B <= A |]  \
\     ==> F : B LeadsTo A'";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [leadsTo_weaken_L]) 1);
qed_spec_mp "LeadsTo_weaken_L";

Goal "[| F : A LeadsTo A';   \
\        B  <= A;   A' <= B' |] \
\     ==> F : B LeadsTo B'";
by (blast_tac (claset() addIs [LeadsTo_weaken_R, LeadsTo_weaken_L,
			       LeadsTo_Trans]) 1);
qed "LeadsTo_weaken";

Goal "[| F : Always C;  F : A LeadsTo A';   \
\        C Int B <= A;   C Int A' <= B' |] \
\     ==> F : B LeadsTo B'";
by (blast_tac (claset() addDs [Always_LeadsToI] addIs[LeadsTo_weaken]
                        addIs [Always_LeadsToD]) 1);
qed "Always_LeadsTo_weaken";

(** Two theorems for "proof lattices" **)

Goal "F : A LeadsTo B ==> F : (A Un B) LeadsTo B";
by (blast_tac (claset() addIs [LeadsTo_Un, subset_imp_LeadsTo]) 1);
qed "LeadsTo_Un_post";

Goal "[| F : A LeadsTo B;  F : B LeadsTo C |] \
\     ==> F : (A Un B) LeadsTo C";
by (blast_tac (claset() addIs [LeadsTo_Un, subset_imp_LeadsTo, 
			       LeadsTo_weaken_L, LeadsTo_Trans]) 1);
qed "LeadsTo_Trans_Un";


(** Distributive laws **)

Goal "(F : (A Un B) LeadsTo C)  = (F : A LeadsTo C & F : B LeadsTo C)";
by (blast_tac (claset() addIs [LeadsTo_Un, LeadsTo_weaken_L]) 1);
qed "LeadsTo_Un_distrib";

Goal "(F : (UN i:I. A i) LeadsTo B)  =  (ALL i : I. F : (A i) LeadsTo B)";
by (blast_tac (claset() addIs [LeadsTo_UN, LeadsTo_weaken_L]) 1);
qed "LeadsTo_UN_distrib";

Goal "(F : (Union S) LeadsTo B)  =  (ALL A : S. F : A LeadsTo B)";
by (blast_tac (claset() addIs [LeadsTo_Union, LeadsTo_weaken_L]) 1);
qed "LeadsTo_Union_distrib";


(** More rules using the premise "Always INV" **)

Goal "F : A Ensures B ==> F : A LeadsTo B";
by (asm_full_simp_tac
    (simpset() addsimps [Ensures_def, LeadsTo_def, leadsTo_Basis]) 1);
qed "LeadsTo_Basis";

Goal "[| F : (A-B) Co (A Un B);  F : transient (A-B) |]   \
\     ==> F : A Ensures B";
by (asm_full_simp_tac
    (simpset() addsimps [Ensures_def, Constrains_eq_constrains]) 1);
by (blast_tac (claset() addIs [ensuresI, constrains_weaken, 
			       transient_strengthen]) 1);
qed "EnsuresI";

Goal "[| F : Always INV;      \
\        F : (INV Int (A-A')) Co (A Un A'); \
\        F : transient (INV Int (A-A')) |]   \
\ ==> F : A LeadsTo A'";
by (rtac Always_LeadsToI 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [EnsuresI, LeadsTo_Basis,
			       Always_ConstrainsD RS Constrains_weaken, 
			       transient_strengthen]) 1);
qed "Always_LeadsTo_Basis";

(*Set difference: maybe combine with leadsTo_weaken_L??
  This is the most useful form of the "disjunction" rule*)
Goal "[| F : (A-B) LeadsTo C;  F : (A Int B) LeadsTo C |] \
\     ==> F : A LeadsTo C";
by (blast_tac (claset() addIs [LeadsTo_Un, LeadsTo_weaken]) 1);
qed "LeadsTo_Diff";


val prems = 
Goal "(!! i. i:I ==> F : (A i) LeadsTo (A' i)) \
\     ==> F : (UN i:I. A i) LeadsTo (UN i:I. A' i)";
by (simp_tac (HOL_ss addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs [LeadsTo_Union, LeadsTo_weaken_R] 
                        addIs prems) 1);
qed "LeadsTo_UN_UN";


(*Version with no index set*)
val prems = 
Goal "(!! i. F : (A i) LeadsTo (A' i)) \
\     ==> F : (UN i. A i) LeadsTo (UN i. A' i)";
by (blast_tac (claset() addIs [LeadsTo_UN_UN] 
                        addIs prems) 1);
qed "LeadsTo_UN_UN_noindex";

(*Version with no index set*)
Goal "ALL i. F : (A i) LeadsTo (A' i) \
\     ==> F : (UN i. A i) LeadsTo (UN i. A' i)";
by (blast_tac (claset() addIs [LeadsTo_UN_UN]) 1);
qed "all_LeadsTo_UN_UN";


(*Binary union version*)
Goal "[| F : A LeadsTo A'; F : B LeadsTo B' |] \
\           ==> F : (A Un B) LeadsTo (A' Un B')";
by (blast_tac (claset() addIs [LeadsTo_Un, 
			       LeadsTo_weaken_R]) 1);
qed "LeadsTo_Un_Un";


(** The cancellation law **)

Goal "[| F : A LeadsTo (A' Un B); F : B LeadsTo B' |]    \
\     ==> F : A LeadsTo (A' Un B')";
by (blast_tac (claset() addIs [LeadsTo_Un_Un, 
			       subset_imp_LeadsTo, LeadsTo_Trans]) 1);
qed "LeadsTo_cancel2";

Goal "[| F : A LeadsTo (A' Un B); F : (B-A') LeadsTo B' |] \
\     ==> F : A LeadsTo (A' Un B')";
by (rtac LeadsTo_cancel2 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "LeadsTo_cancel_Diff2";

Goal "[| F : A LeadsTo (B Un A'); F : B LeadsTo B' |] \
\     ==> F : A LeadsTo (B' Un A')";
by (asm_full_simp_tac (simpset() addsimps [Un_commute]) 1);
by (blast_tac (claset() addSIs [LeadsTo_cancel2]) 1);
qed "LeadsTo_cancel1";

Goal "[| F : A LeadsTo (B Un A'); F : (B-A') LeadsTo B' |] \
\     ==> F : A LeadsTo (B' Un A')";
by (rtac LeadsTo_cancel1 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "LeadsTo_cancel_Diff1";


(** The impossibility law **)

(*The set "A" may be non-empty, but it contains no reachable states*)
Goal "F : A LeadsTo {} ==> F : Always (-A)";
by (full_simp_tac (simpset() addsimps [LeadsTo_def,
				       Always_eq_includes_reachable]) 1);
by (dtac leadsTo_empty 1);
by Auto_tac;
qed "LeadsTo_empty";


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction"*)
Goal "[| F : A LeadsTo A';  F : Stable B |] \
\     ==> F : (A Int B) LeadsTo (A' Int B)";
by (full_simp_tac
    (simpset() addsimps [LeadsTo_eq_leadsTo, Stable_eq_stable]) 1);
by (dtac psp_stable 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps Int_ac) 1);
qed "PSP_Stable";

Goal "[| F : A LeadsTo A'; F : Stable B |] \
\     ==> F : (B Int A) LeadsTo (B Int A')";
by (asm_simp_tac (simpset() addsimps PSP_Stable::Int_ac) 1);
qed "PSP_Stable2";

Goal "[| F : A LeadsTo A'; F : B Co B' |] \
\     ==> F : (A Int B') LeadsTo ((A' Int B) Un (B' - B))";
by (full_simp_tac
    (simpset() addsimps [LeadsTo_def, Constrains_eq_constrains]) 1);
by (blast_tac (claset() addDs [psp] addIs [leadsTo_weaken]) 1);
qed "PSP";

Goal "[| F : A LeadsTo A'; F : B Co B' |] \
\     ==> F : (B' Int A) LeadsTo ((B Int A') Un (B' - B))";
by (asm_simp_tac (simpset() addsimps PSP::Int_ac) 1);
qed "PSP2";

Goalw [Unless_def]
     "[| F : A LeadsTo A'; F : B Unless B' |] \
\     ==> F : (A Int B) LeadsTo ((A' Int B) Un B')";
by (dtac PSP 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [LeadsTo_Diff, LeadsTo_weaken, 
			       subset_imp_LeadsTo]) 1);
qed "PSP_Unless";


Goal "[| F : Stable A;  F : transient C;  \
\        F : Always (-A Un B Un C) |] ==> F : A LeadsTo B";
by (etac Always_LeadsTo_weaken 1);
by (rtac LeadsTo_Diff 1);
by (etac (transient_imp_leadsTo RS leadsTo_imp_LeadsTo RS PSP_Stable2) 2);
by (ALLGOALS (blast_tac (claset() addIs [subset_imp_LeadsTo])));
qed "Stable_transient_Always_LeadsTo";


(*** Induction rules ***)

(** Meta or object quantifier ????? **)
Goal "[| wf r;     \
\        ALL m. F : (A Int f-`{m}) LeadsTo                     \
\                           ((A Int f-`(r^-1 `` {m})) Un B) |] \
\     ==> F : A LeadsTo B";
by (full_simp_tac (simpset() addsimps [LeadsTo_eq_leadsTo]) 1);
by (etac leadsTo_wf_induct 1);
by (blast_tac (claset() addIs [leadsTo_weaken]) 1);
qed "LeadsTo_wf_induct";


Goal "[| wf r;     \
\        ALL m:I. F : (A Int f-`{m}) LeadsTo                   \
\                             ((A Int f-`(r^-1 `` {m})) Un B) |] \
\     ==> F : A LeadsTo ((A - (f-`I)) Un B)";
by (etac LeadsTo_wf_induct 1);
by Safe_tac;
by (case_tac "m:I" 1);
by (blast_tac (claset() addIs [LeadsTo_weaken]) 1);
by (blast_tac (claset() addIs [subset_imp_LeadsTo]) 1);
qed "Bounded_induct";


val prems = 
Goal "(!!m::nat. F : (A Int f-`{m}) LeadsTo ((A Int f-`(lessThan m)) Un B)) \
\     ==> F : A LeadsTo B";
by (rtac (wf_less_than RS LeadsTo_wf_induct) 1);
by (auto_tac (claset() addIs prems, simpset()));
qed "LessThan_induct";

(*Integer version.  Could generalize from #0 to any lower bound*)
val [reach, prem] =
Goal "[| F : Always {s. (#0::int) <= f s};  \
\        !! z. F : (A Int {s. f s = z}) LeadsTo                     \
\                           ((A Int {s. f s < z}) Un B) |] \
\     ==> F : A LeadsTo B";
by (res_inst_tac [("f", "nat o f")] LessThan_induct 1);
by (simp_tac (simpset() addsimps [vimage_def]) 1);
by (rtac ([reach, prem] MRS Always_LeadsTo_weaken) 1);
by (auto_tac (claset(), simpset() addsimps [nat_eq_iff, nat_less_iff]));
qed "integ_0_le_induct";

Goal "!!l::nat. [| ALL m:(greaterThan l). F : (A Int f-`{m}) LeadsTo   \
\                                        ((A Int f-`(lessThan m)) Un B) |] \
\           ==> F : A LeadsTo ((A Int (f-`(atMost l))) Un B)";
by (simp_tac (HOL_ss addsimps [Diff_eq RS sym, vimage_Compl, Compl_greaterThan RS sym]) 1);
by (rtac (wf_less_than RS Bounded_induct) 1);
by (Asm_simp_tac 1);
qed "LessThan_bounded_induct";

Goal "!!l::nat. [| ALL m:(lessThan l). F : (A Int f-`{m}) LeadsTo   \
\                              ((A Int f-`(greaterThan m)) Un B) |] \
\     ==> F : A LeadsTo ((A Int (f-`(atLeast l))) Un B)";
by (res_inst_tac [("f","f"),("f1", "%k. l - k")]
    (wf_less_than RS wf_inv_image RS LeadsTo_wf_induct) 1);
by (simp_tac (simpset() addsimps [inv_image_def, Image_singleton]) 1);
by (Clarify_tac 1);
by (case_tac "m<l" 1);
by (blast_tac (claset() addIs [not_leE, subset_imp_LeadsTo]) 2);
by (blast_tac (claset() addIs [LeadsTo_weaken_R, diff_less_mono2]) 1);
qed "GreaterThan_bounded_induct";


(*** Completion: Binary and General Finite versions ***)

Goal "[| F : A LeadsTo (A' Un C);  F : A' Co (A' Un C); \
\        F : B LeadsTo (B' Un C);  F : B' Co (B' Un C) |] \
\     ==> F : (A Int B) LeadsTo ((A' Int B') Un C)";
by (full_simp_tac
    (simpset() addsimps [LeadsTo_eq_leadsTo, Constrains_eq_constrains,
				       Int_Un_distrib]) 1);
by (blast_tac (claset() addIs [completion, leadsTo_weaken]) 1);
qed "Completion";

Goal "finite I \
\     ==> (ALL i:I. F : (A i) LeadsTo (A' i Un C)) -->  \
\         (ALL i:I. F : (A' i) Co (A' i Un C)) --> \
\         F : (INT i:I. A i) LeadsTo ((INT i:I. A' i) Un C)";
by (etac finite_induct 1);
by Auto_tac;
by (rtac Completion 1);
by (simp_tac (HOL_ss addsimps (INT_simps RL [sym])) 4); 
by (rtac Constrains_INT 4);
by Auto_tac;
val lemma = result();

val prems = Goal
     "[| finite I;  \
\        !!i. i:I ==> F : (A i) LeadsTo (A' i Un C); \
\        !!i. i:I ==> F : (A' i) Co (A' i Un C) |]   \
\     ==> F : (INT i:I. A i) LeadsTo ((INT i:I. A' i) Un C)";
by (blast_tac (claset() addIs (lemma RS mp RS mp)::prems) 1);
qed "Finite_completion";

Goalw [Stable_def]
     "[| F : A LeadsTo A';  F : Stable A';   \
\        F : B LeadsTo B';  F : Stable B' |] \
\     ==> F : (A Int B) LeadsTo (A' Int B')";
by (res_inst_tac [("C1", "{}")] (Completion RS LeadsTo_weaken_R) 1);
by (REPEAT (Force_tac 1));
qed "Stable_completion";

val prems = Goalw [Stable_def]
     "[| finite I;  \
\        !!i. i:I ==> F : (A i) LeadsTo (A' i); \
\        !!i. i:I ==> F : Stable (A' i) |]   \
\     ==> F : (INT i:I. A i) LeadsTo (INT i:I. A' i)";
by (res_inst_tac [("C1", "{}")] (Finite_completion RS LeadsTo_weaken_R) 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (blast_tac (claset() addIs prems)));
qed "Finite_stable_completion";


(*proves "ensures/leadsTo" properties when the program is specified*)
fun ensures_tac sact = 
    SELECT_GOAL
      (EVERY [REPEAT (Always_Int_tac 1),
	      etac Always_LeadsTo_Basis 1 
	          ORELSE   (*subgoal may involve LeadsTo, leadsTo or ensures*)
		  REPEAT (ares_tac [LeadsTo_Basis, leadsTo_Basis,
				    EnsuresI, ensuresI] 1),
	      (*now there are two subgoals: co & transient*)
	      simp_tac (simpset() addsimps !program_defs_ref) 2,
	      res_inst_tac [("act", sact)] transientI 2,
                 (*simplify the command's domain*)
	      simp_tac (simpset() addsimps [Domain_def]) 3,
	      constrains_tac 1,
	      ALLGOALS Clarify_tac,
	      ALLGOALS Asm_full_simp_tac]);
