(*  Title:      HOL/UNITY/SubstAx
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

LeadsTo relation, restricted to the set of reachable states.
*)



(*** Specialized laws for handling invariants ***)

Goal "[| Invariant prg INV;  LeadsTo prg (INV Int A) A' |]   \
\     ==> LeadsTo prg A A'";
by (asm_full_simp_tac
    (simpset() addsimps [LeadsTo_def, reachable_Int_INV,
			 Int_assoc RS sym]) 1);
qed "Invariant_LeadsToI";

Goal "[| Invariant prg INV;  LeadsTo prg A A' |]   \
\     ==> LeadsTo prg A (INV Int A')";
by (asm_full_simp_tac
    (simpset() addsimps [LeadsTo_def, reachable_Int_INV,
			 Int_assoc RS sym]) 1);
qed "Invariant_LeadsToD";


(*** Introduction rules: Basis, Trans, Union ***)

Goal "leadsTo (Acts prg) A B ==> LeadsTo prg A B";
by (simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [psp_stable2, stable_reachable]) 1);
qed "leadsTo_imp_LeadsTo";

Goal "[| LeadsTo prg A B;  LeadsTo prg B C |] ==> LeadsTo prg A C";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [leadsTo_Trans]) 1);
qed "LeadsTo_Trans";

val [prem] = Goalw [LeadsTo_def]
 "(!!A. A : S ==> LeadsTo prg A B) ==> LeadsTo prg (Union S) B";
by (Simp_tac 1);
by (stac Int_Union 1);
by (blast_tac (claset() addIs [leadsTo_UN,
			        simplify (simpset()) prem]) 1);
qed "LeadsTo_Union";


(*** Derived rules ***)

Goal "id: Acts prg ==> LeadsTo prg A UNIV";
by (asm_simp_tac (simpset() addsimps [LeadsTo_def, 
				      Int_lower1 RS subset_imp_leadsTo]) 1);
qed "LeadsTo_UNIV";
Addsimps [LeadsTo_UNIV];

(*Useful with cancellation, disjunction*)
Goal "LeadsTo prg A (A' Un A') ==> LeadsTo prg A A'";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "LeadsTo_Un_duplicate";

Goal "LeadsTo prg A (A' Un C Un C) ==> LeadsTo prg A (A' Un C)";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "LeadsTo_Un_duplicate2";

val prems = 
Goal "(!!i. i : I ==> LeadsTo prg (A i) B) ==> LeadsTo prg (UN i:I. A i) B";
by (simp_tac (simpset() addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs (LeadsTo_Union::prems)) 1);
qed "LeadsTo_UN";

(*Binary union introduction rule*)
Goal "[| LeadsTo prg A C; LeadsTo prg B C |] ==> LeadsTo prg (A Un B) C";
by (stac Un_eq_Union 1);
by (blast_tac (claset() addIs [LeadsTo_Union]) 1);
qed "LeadsTo_Un";

Goal "[| A <= B;  id: Acts prg |] ==> LeadsTo prg A B";
by (simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
qed "subset_imp_LeadsTo";

bind_thm ("empty_LeadsTo", empty_subsetI RS subset_imp_LeadsTo);
Addsimps [empty_LeadsTo];

Goal "[| LeadsTo prg A A';  A' <= B' |] ==> LeadsTo prg A B'";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [leadsTo_weaken_R]) 1);
qed_spec_mp "LeadsTo_weaken_R";


Goal "[| LeadsTo prg A A';  B <= A; id: Acts prg |]  \
\     ==> LeadsTo prg B A'";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [leadsTo_weaken_L]) 1);
qed_spec_mp "LeadsTo_weaken_L";


(*Distributes over binary unions*)
Goal "id: Acts prg ==> \
\       LeadsTo prg (A Un B) C  =  \
\       (LeadsTo prg A C & LeadsTo prg B C)";
by (blast_tac (claset() addIs [LeadsTo_Un, LeadsTo_weaken_L]) 1);
qed "LeadsTo_Un_distrib";

Goal "id: Acts prg ==> \
\       LeadsTo prg (UN i:I. A i) B  =  \
\       (ALL i : I. LeadsTo prg (A i) B)";
by (blast_tac (claset() addIs [LeadsTo_UN, LeadsTo_weaken_L]) 1);
qed "LeadsTo_UN_distrib";

Goal "id: Acts prg ==> \
\       LeadsTo prg (Union S) B  =  \
\       (ALL A : S. LeadsTo prg A B)";
by (blast_tac (claset() addIs [LeadsTo_Union, LeadsTo_weaken_L]) 1);
qed "LeadsTo_Union_distrib";


Goal "[| LeadsTo prg A A'; id: Acts prg;   \
\        B  <= A;   A' <= B' |] \
\     ==> LeadsTo prg B B'";
(*PROOF FAILED*)
by (blast_tac (claset() addIs [LeadsTo_Trans, LeadsTo_weaken_R,
			       LeadsTo_weaken_L]) 1);
qed "LeadsTo_weaken";


(** More rules using the premise "Invariant prg" **)

Goalw [LeadsTo_def, Constrains_def]
     "[| Constrains prg (A-A') (A Un A'); transient  (Acts prg) (A-A') |]   \
\     ==> LeadsTo prg A A'";
by (rtac (ensuresI RS leadsTo_Basis) 1);
by (blast_tac (claset() addIs [transient_strengthen]) 2);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "LeadsTo_Basis";

Goal "[| Invariant prg INV;      \
\        Constrains prg (INV Int (A-A')) (A Un A'); \
\        transient  (Acts prg) (INV Int (A-A')) |]   \
\ ==> LeadsTo prg A A'";
by (rtac Invariant_LeadsToI 1);
by (assume_tac 1);
by (rtac LeadsTo_Basis 1);
by (blast_tac (claset() addIs [transient_strengthen]) 2);
by (blast_tac (claset() addIs [Invariant_ConstrainsD RS Constrains_weaken]) 1);
qed "Invariant_LeadsTo_Basis";

Goal "[| Invariant prg INV;      \
\        LeadsTo prg A A'; id: Acts prg;   \
\        INV Int B  <= A;  INV Int A' <= B' |] \
\     ==> LeadsTo prg B B'";
by (rtac Invariant_LeadsToI 1);
by (assume_tac 1);
by (dtac Invariant_LeadsToD 1);
by (assume_tac 1);
by (blast_tac (claset()addIs [LeadsTo_weaken]) 1);
qed "Invariant_LeadsTo_weaken";


(*Set difference: maybe combine with leadsTo_weaken_L??
  This is the most useful form of the "disjunction" rule*)
Goal "[| LeadsTo prg (A-B) C; LeadsTo prg B C; id: Acts prg |] \
\     ==> LeadsTo prg A C";
by (blast_tac (claset() addIs [LeadsTo_Un, LeadsTo_weaken]) 1);
qed "LeadsTo_Diff";


val prems = 
Goal "(!! i. i:I ==> LeadsTo prg (A i) (A' i)) \
\     ==> LeadsTo prg (UN i:I. A i) (UN i:I. A' i)";
by (simp_tac (simpset() addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs [LeadsTo_Union, LeadsTo_weaken_R] 
                        addIs prems) 1);
qed "LeadsTo_UN_UN";


(*Version with no index set*)
val prems = 
Goal "(!! i. LeadsTo prg (A i) (A' i)) \
\     ==> LeadsTo prg (UN i. A i) (UN i. A' i)";
by (blast_tac (claset() addIs [LeadsTo_UN_UN] 
                        addIs prems) 1);
qed "LeadsTo_UN_UN_noindex";

(*Version with no index set*)
Goal "ALL i. LeadsTo prg (A i) (A' i) \
\     ==> LeadsTo prg (UN i. A i) (UN i. A' i)";
by (blast_tac (claset() addIs [LeadsTo_UN_UN]) 1);
qed "all_LeadsTo_UN_UN";


(*Binary union version*)
Goal "[| LeadsTo prg A A'; LeadsTo prg B B' |] \
\           ==> LeadsTo prg (A Un B) (A' Un B')";
by (blast_tac (claset() addIs [LeadsTo_Un, 
			       LeadsTo_weaken_R]) 1);
qed "LeadsTo_Un_Un";


(** The cancellation law **)

Goal "[| LeadsTo prg A (A' Un B); LeadsTo prg B B'; \
\        id: Acts prg |]    \
\     ==> LeadsTo prg A (A' Un B')";
by (blast_tac (claset() addIs [LeadsTo_Un_Un, 
			       subset_imp_LeadsTo, LeadsTo_Trans]) 1);
qed "LeadsTo_cancel2";

Goal "[| LeadsTo prg A (A' Un B); LeadsTo prg (B-A') B'; id: Acts prg |] \
\     ==> LeadsTo prg A (A' Un B')";
by (rtac LeadsTo_cancel2 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "LeadsTo_cancel_Diff2";

Goal "[| LeadsTo prg A (B Un A'); LeadsTo prg B B'; id: Acts prg |] \
\     ==> LeadsTo prg A (B' Un A')";
by (asm_full_simp_tac (simpset() addsimps [Un_commute]) 1);
by (blast_tac (claset() addSIs [LeadsTo_cancel2]) 1);
qed "LeadsTo_cancel1";

Goal "[| LeadsTo prg A (B Un A'); LeadsTo prg (B-A') B'; id: Acts prg |] \
\     ==> LeadsTo prg A (B' Un A')";
by (rtac LeadsTo_cancel1 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "LeadsTo_cancel_Diff1";



(** The impossibility law **)

(*The set "A" may be non-empty, but it contains no reachable states*)
Goal "LeadsTo prg A {} ==> reachable prg Int A = {}";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (etac leadsTo_empty 1);
qed "LeadsTo_empty";


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction".  Doesn't need id:Acts. *)
Goal
  "[| LeadsTo prg A A';  Stable prg B |] ==> LeadsTo prg (A Int B) (A' Int B)";
by (full_simp_tac (simpset() addsimps [LeadsTo_def, Stable_eq_stable]) 1);
by (dtac psp_stable 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps Int_ac) 1);
qed "PSP_stable";

Goal "[| LeadsTo prg A A'; Stable prg B |] \
\     ==> LeadsTo prg (B Int A) (B Int A')";
by (asm_simp_tac (simpset() addsimps (PSP_stable::Int_ac)) 1);
qed "PSP_stable2";

Goalw [LeadsTo_def, Constrains_def]
     "[| LeadsTo prg A A'; Constrains prg B B'; id: Acts prg |] \
\     ==> LeadsTo prg (A Int B) ((A' Int B) Un (B' - B))";
by (blast_tac (claset() addDs [psp] addIs [leadsTo_weaken]) 1);
qed "PSP";

Goal "[| LeadsTo prg A A'; Constrains prg B B'; id: Acts prg |] \
\     ==> LeadsTo prg (B Int A) ((B Int A') Un (B' - B))";
by (asm_simp_tac (simpset() addsimps (PSP::Int_ac)) 1);
qed "PSP2";

Goalw [Unless_def]
     "[| LeadsTo prg A A'; Unless prg B B'; id: Acts prg |] \
\     ==> LeadsTo prg (A Int B) ((A' Int B) Un B')";
by (dtac PSP 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [LeadsTo_Diff, LeadsTo_weaken, 
			       subset_imp_LeadsTo]) 2);
by (assume_tac 1);
qed "PSP_Unless";


(*** Induction rules ***)

(** Meta or object quantifier ????? **)
Goal "[| wf r;     \
\        ALL m. LeadsTo prg (A Int f-``{m})                     \
\                           ((A Int f-``(r^-1 ^^ {m})) Un B);   \
\        id: Acts prg |] \
\     ==> LeadsTo prg A B";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (etac leadsTo_wf_induct 1);
by (assume_tac 2);
by (blast_tac (claset() addIs [leadsTo_weaken]) 1);
qed "LeadsTo_wf_induct";


Goal "[| wf r;     \
\        ALL m:I. LeadsTo prg (A Int f-``{m})                   \
\                             ((A Int f-``(r^-1 ^^ {m})) Un B);   \
\        id: Acts prg |] \
\     ==> LeadsTo prg A ((A - (f-``I)) Un B)";
by (etac LeadsTo_wf_induct 1);
by Safe_tac;
by (case_tac "m:I" 1);
by (blast_tac (claset() addIs [LeadsTo_weaken]) 1);
by (blast_tac (claset() addIs [subset_imp_LeadsTo]) 1);
qed "Bounded_induct";


Goal "[| ALL m. LeadsTo prg (A Int f-``{m})                     \
\                           ((A Int f-``(lessThan m)) Un B);   \
\        id: Acts prg |] \
\     ==> LeadsTo prg A B";
by (rtac (wf_less_than RS LeadsTo_wf_induct) 1);
by (assume_tac 2);
by (Asm_simp_tac 1);
qed "LessThan_induct";

Goal "[| ALL m:(greaterThan l). LeadsTo prg (A Int f-``{m})   \
\                                        ((A Int f-``(lessThan m)) Un B);   \
\              id: Acts prg |] \
\           ==> LeadsTo prg A ((A Int (f-``(atMost l))) Un B)";
by (simp_tac (HOL_ss addsimps [Diff_eq RS sym, vimage_Compl, Compl_greaterThan RS sym]) 1);
by (rtac (wf_less_than RS Bounded_induct) 1);
by (assume_tac 2);
by (Asm_simp_tac 1);
qed "LessThan_bounded_induct";

Goal "[| ALL m:(lessThan l). LeadsTo prg (A Int f-``{m})   \
\                              ((A Int f-``(greaterThan m)) Un B);   \
\        id: Acts prg |] \
\     ==> LeadsTo prg A ((A Int (f-``(atLeast l))) Un B)";
by (res_inst_tac [("f","f"),("f1", "%k. l - k")]
    (wf_less_than RS wf_inv_image RS LeadsTo_wf_induct) 1);
by (assume_tac 2);
by (simp_tac (simpset() addsimps [inv_image_def, Image_singleton]) 1);
by (Clarify_tac 1);
by (case_tac "m<l" 1);
by (blast_tac (claset() addIs [not_leE, subset_imp_LeadsTo]) 2);
by (blast_tac (claset() addIs [LeadsTo_weaken_R, diff_less_mono2]) 1);
qed "GreaterThan_bounded_induct";


(*** Completion: Binary and General Finite versions ***)

Goal "[| LeadsTo prg A A';  Stable prg A';   \
\        LeadsTo prg B B';  Stable prg B';  id: Acts prg |] \
\     ==> LeadsTo prg (A Int B) (A' Int B')";
by (full_simp_tac (simpset() addsimps [LeadsTo_def, Stable_eq_stable]) 1);
by (blast_tac (claset() addIs [stable_completion, leadsTo_weaken]) 1);
qed "Stable_completion";


Goal "[| finite I;  id: Acts prg |]      \
\     ==> (ALL i:I. LeadsTo prg (A i) (A' i)) -->  \
\         (ALL i:I. Stable prg (A' i)) -->         \
\         LeadsTo prg (INT i:I. A i) (INT i:I. A' i)";
by (etac finite_induct 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [Stable_completion, ball_Stable_INT]) 1);
qed_spec_mp "Finite_stable_completion";


Goal "[| LeadsTo prg A (A' Un C);  Constrains prg A' (A' Un C); \
\        LeadsTo prg B (B' Un C);  Constrains prg B' (B' Un C); \
\        id: Acts prg |] \
\     ==> LeadsTo prg (A Int B) ((A' Int B') Un C)";
by (full_simp_tac (simpset() addsimps [LeadsTo_def, Constrains_def,
				       Int_Un_distrib]) 1);
by (blast_tac (claset() addIs [completion, leadsTo_weaken]) 1);
qed "Completion";


Goal "[| finite I;  id: Acts prg |] \
\     ==> (ALL i:I. LeadsTo prg (A i) (A' i Un C)) -->  \
\         (ALL i:I. Constrains prg (A' i) (A' i Un C)) --> \
\         LeadsTo prg (INT i:I. A i) ((INT i:I. A' i) Un C)";
by (etac finite_induct 1);
by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (dtac ball_Constrains_INT 1);
by (asm_full_simp_tac (simpset() addsimps [Completion]) 1); 
qed "Finite_completion";


(** Constrains/Ensures tactics 
    main_def defines the main program as a set;
    cmd_defs defines the separate commands
**)

(*proves "constrains" properties when the program is specified*)
fun constrains_tac (main_def::cmd_defs) = 
   SELECT_GOAL
      (EVERY [REPEAT (resolve_tac [StableI, stableI,
				   constrains_imp_Constrains] 1),
	      rtac constrainsI 1,
	      full_simp_tac (simpset() addsimps [main_def]) 1,
	      REPEAT_FIRST (etac disjE ),
	      rewrite_goals_tac cmd_defs,
	      ALLGOALS (SELECT_GOAL Auto_tac)]);


(*proves "ensures/leadsTo" properties when the program is specified*)
fun ensures_tac (main_def::cmd_defs) sact = 
    SELECT_GOAL
      (EVERY [REPEAT (Invariant_Int_tac 1),
	      etac Invariant_LeadsTo_Basis 1 
	          ORELSE   (*subgoal may involve LeadsTo, leadsTo or ensures*)
		  REPEAT (ares_tac [LeadsTo_Basis, ensuresI] 1),
	      res_inst_tac [("act", sact)] transient_mem 2,
	      simp_tac (simpset() addsimps (Domain_partial_func::cmd_defs)) 3,
	      simp_tac (simpset() addsimps [main_def]) 2,
	      constrains_tac (main_def::cmd_defs) 1,
	      rewrite_goals_tac cmd_defs,
	      ALLGOALS Clarify_tac,
	      Auto_tac]);


