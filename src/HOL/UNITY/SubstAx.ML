(*  Title:      HOL/UNITY/SubstAx
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak Fairness versions of transient, ensures, LeadsTo.

From Misra, "A Logic for Concurrent Programming", 1994
*)

open SubstAx;

(*constrains Acts B B' ==> constrains Acts (reachable Init Acts Int B)
                                           (reachable Init Acts Int B') *)
bind_thm ("constrains_reachable",
	  rewrite_rule [stable_def] stable_reachable RS constrains_Int);


(*** Introduction rules: Basis, Trans, Union ***)

goalw thy [LeadsTo_def]
    "!!Acts. leadsTo Acts A B ==> LeadsTo Init Acts A B";
by (blast_tac (claset() addIs [PSP_stable2, stable_reachable]) 1);
qed "leadsTo_imp_LeadsTo";

goalw thy [LeadsTo_def]
    "!!Acts. [| constrains Acts (reachable Init Acts Int (A - A'))   \
\                               (A Un A'); \
\               transient  Acts (reachable Init Acts Int (A-A')) |]   \
\           ==> LeadsTo Init Acts A A'";
by (rtac (stable_reachable RS stable_ensures_Int RS leadsTo_Basis) 1);
by (assume_tac 2);
by (asm_simp_tac 
    (simpset() addsimps [Int_Un_distrib RS sym, Diff_Int_distrib RS sym,
			 stable_constrains_Int]) 1);
qed "LeadsTo_Basis";

goalw thy [LeadsTo_def]
    "!!Acts. [| LeadsTo Init Acts A B;  LeadsTo Init Acts B C |] \
\            ==> LeadsTo Init Acts A C";
by (blast_tac (claset() addIs [leadsTo_Trans]) 1);
qed "LeadsTo_Trans";

val prems = goalw thy [LeadsTo_def]
 "(!!A. A : S ==> LeadsTo Init Acts A B) ==> LeadsTo Init Acts (Union S) B";
by (stac Int_Union 1);
by (blast_tac (claset() addIs (leadsTo_UN::prems)) 1);
qed "LeadsTo_Union";


(*** Derived rules ***)

goal thy "!!Acts. id: Acts ==> LeadsTo Init Acts A UNIV";
by (asm_simp_tac (simpset() addsimps [LeadsTo_def, 
				      Int_lower1 RS subset_imp_leadsTo]) 1);
qed "LeadsTo_UNIV";
Addsimps [LeadsTo_UNIV];

(*Useful with cancellation, disjunction*)
goal thy "!!Acts. LeadsTo Init Acts A (A' Un A') ==> LeadsTo Init Acts A A'";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "LeadsTo_Un_duplicate";

goal thy "!!Acts. LeadsTo Init Acts A (A' Un C Un C) ==> LeadsTo Init Acts A (A' Un C)";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "LeadsTo_Un_duplicate2";

val prems = goal thy
   "(!!i. i : I ==> LeadsTo Init Acts (A i) B) \
\   ==> LeadsTo Init Acts (UN i:I. A i) B";
by (simp_tac (simpset() addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs (LeadsTo_Union::prems)) 1);
qed "LeadsTo_UN";

(*Binary union introduction rule*)
goal thy
  "!!C. [| LeadsTo Init Acts A C; LeadsTo Init Acts B C |] ==> LeadsTo Init Acts (A Un B) C";
by (stac Un_eq_Union 1);
by (blast_tac (claset() addIs [LeadsTo_Union]) 1);
qed "LeadsTo_Un";


goalw thy [LeadsTo_def]
    "!!A B. [| reachable Init Acts Int A <= B;  id: Acts |] \
\           ==> LeadsTo Init Acts A B";
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
qed "Int_subset_imp_LeadsTo";

goalw thy [LeadsTo_def]
    "!!A B. [| A <= B;  id: Acts |] \
\           ==> LeadsTo Init Acts A B";
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
qed "subset_imp_LeadsTo";

bind_thm ("empty_LeadsTo", empty_subsetI RS subset_imp_LeadsTo);
Addsimps [empty_LeadsTo];

goal thy
    "!!A B. [| reachable Init Acts Int A = {};  id: Acts |] \
\           ==> LeadsTo Init Acts A B";
by (asm_simp_tac (simpset() addsimps [Int_subset_imp_LeadsTo]) 1);
qed "Int_empty_LeadsTo";


goalw thy [LeadsTo_def]
    "!!Acts. [| LeadsTo Init Acts A A';   \
\               reachable Init Acts Int A' <= B' |] \
\            ==> LeadsTo Init Acts A B'";
by (blast_tac (claset() addIs [leadsTo_weaken_R]) 1);
qed_spec_mp "LeadsTo_weaken_R";


goalw thy [LeadsTo_def]
    "!!Acts. [| LeadsTo Init Acts A A'; \
     \               reachable Init Acts Int B <= A; id: Acts |]  \
\            ==> LeadsTo Init Acts B A'";
by (blast_tac (claset() addIs [leadsTo_weaken_L]) 1);
qed_spec_mp "LeadsTo_weaken_L";


(*Distributes over binary unions*)
goal thy
  "!!C. id: Acts ==> \
\       LeadsTo Init Acts (A Un B) C  =  \
\       (LeadsTo Init Acts A C & LeadsTo Init Acts B C)";
by (blast_tac (claset() addIs [LeadsTo_Un, LeadsTo_weaken_L]) 1);
qed "LeadsTo_Un_distrib";

goal thy
  "!!C. id: Acts ==> \
\       LeadsTo Init Acts (UN i:I. A i) B  =  \
\       (ALL i : I. LeadsTo Init Acts (A i) B)";
by (blast_tac (claset() addIs [LeadsTo_UN, LeadsTo_weaken_L]) 1);
qed "LeadsTo_UN_distrib";

goal thy
  "!!C. id: Acts ==> \
\       LeadsTo Init Acts (Union S) B  =  \
\       (ALL A : S. LeadsTo Init Acts A B)";
by (blast_tac (claset() addIs [LeadsTo_Union, LeadsTo_weaken_L]) 1);
qed "LeadsTo_Union_distrib";


goal thy 
   "!!Acts. [| LeadsTo Init Acts A A'; id: Acts;   \
\               reachable Init Acts Int B  <= A;     \
\               reachable Init Acts Int A' <= B' |] \
\           ==> LeadsTo Init Acts B B'";
(*PROOF FAILED: why?*)
by (blast_tac (claset() addIs [LeadsTo_Trans, LeadsTo_weaken_R,
			       LeadsTo_weaken_L]) 1);
qed "LeadsTo_weaken";


(*Set difference: maybe combine with leadsTo_weaken_L??*)
goal thy
  "!!C. [| LeadsTo Init Acts (A-B) C; LeadsTo Init Acts B C; id: Acts |] \
\       ==> LeadsTo Init Acts A C";
by (blast_tac (claset() addIs [LeadsTo_Un, LeadsTo_weaken]) 1);
qed "LeadsTo_Diff";


(** Meta or object quantifier ???????????????????
    see ball_constrains_UN in UNITY.ML***)

val prems = goal thy
   "(!! i. i:I ==> LeadsTo Init Acts (A i) (A' i)) \
\   ==> LeadsTo Init Acts (UN i:I. A i) (UN i:I. A' i)";
by (simp_tac (simpset() addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs [LeadsTo_Union, LeadsTo_weaken_R] 
                        addIs prems) 1);
qed "LeadsTo_UN_UN";


(*Version with no index set*)
val prems = goal thy
   "(!! i. LeadsTo Init Acts (A i) (A' i)) \
\   ==> LeadsTo Init Acts (UN i. A i) (UN i. A' i)";
by (blast_tac (claset() addIs [LeadsTo_UN_UN] 
                        addIs prems) 1);
qed "LeadsTo_UN_UN_noindex";

(*Version with no index set*)
goal thy
   "!!Acts. ALL i. LeadsTo Init Acts (A i) (A' i) \
\           ==> LeadsTo Init Acts (UN i. A i) (UN i. A' i)";
by (blast_tac (claset() addIs [LeadsTo_UN_UN]) 1);
qed "all_LeadsTo_UN_UN";


(*Binary union version*)
goal thy "!!Acts. [| LeadsTo Init Acts A A'; LeadsTo Init Acts B B' |] \
\                 ==> LeadsTo Init Acts (A Un B) (A' Un B')";
by (blast_tac (claset() addIs [LeadsTo_Un, 
			       LeadsTo_weaken_R]) 1);
qed "LeadsTo_Un_Un";


(** The cancellation law **)

goal thy
   "!!Acts. [| LeadsTo Init Acts A (A' Un B); LeadsTo Init Acts B B'; \
\              id: Acts |]    \
\           ==> LeadsTo Init Acts A (A' Un B')";
by (blast_tac (claset() addIs [LeadsTo_Un_Un, 
			       subset_imp_LeadsTo, LeadsTo_Trans]) 1);
qed "LeadsTo_cancel2";

goal thy
   "!!Acts. [| LeadsTo Init Acts A (A' Un B); LeadsTo Init Acts (B-A') B'; id: Acts |] \
\           ==> LeadsTo Init Acts A (A' Un B')";
by (rtac LeadsTo_cancel2 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "LeadsTo_cancel_Diff2";

goal thy
   "!!Acts. [| LeadsTo Init Acts A (B Un A'); LeadsTo Init Acts B B'; id: Acts |] \
\           ==> LeadsTo Init Acts A (B' Un A')";
by (asm_full_simp_tac (simpset() addsimps [Un_commute]) 1);
by (blast_tac (claset() addSIs [LeadsTo_cancel2]) 1);
qed "LeadsTo_cancel1";

goal thy
   "!!Acts. [| LeadsTo Init Acts A (B Un A'); LeadsTo Init Acts (B-A') B'; id: Acts |] \
\           ==> LeadsTo Init Acts A (B' Un A')";
by (rtac LeadsTo_cancel1 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "LeadsTo_cancel_Diff1";



(** The impossibility law **)

goalw thy [LeadsTo_def]
    "!!Acts. LeadsTo Init Acts A {} ==> reachable Init Acts Int A  = {}";
by (Full_simp_tac 1);
by (etac leadsTo_empty 1);
qed "LeadsTo_empty";


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction".  Doesn't need id:Acts. *)
goalw thy [LeadsTo_def]
   "!!Acts. [| LeadsTo Init Acts A A'; stable Acts B |] \
\           ==> LeadsTo Init Acts (A Int B) (A' Int B)";
by (asm_simp_tac (simpset() addsimps [Int_assoc RS sym, PSP_stable]) 1);
qed "R_PSP_stable";

goal thy
   "!!Acts. [| LeadsTo Init Acts A A'; stable Acts B |] \
\           ==> LeadsTo Init Acts (B Int A) (B Int A')";
by (asm_simp_tac (simpset() addsimps (R_PSP_stable::Int_ac)) 1);
qed "R_PSP_stable2";


goalw thy [LeadsTo_def]
   "!!Acts. [| LeadsTo Init Acts A A'; constrains Acts B B'; id: Acts |] \
\           ==> LeadsTo Init Acts (A Int B) ((A' Int B) Un (B' - B))";
by (dtac PSP 1);
by (etac constrains_reachable 1);
by (etac leadsTo_weaken 2);
by (ALLGOALS Blast_tac);
qed "R_PSP";

goal thy
   "!!Acts. [| LeadsTo Init Acts A A'; constrains Acts B B'; id: Acts |] \
\           ==> LeadsTo Init Acts (B Int A) ((B Int A') Un (B' - B))";
by (asm_simp_tac (simpset() addsimps (R_PSP::Int_ac)) 1);
qed "R_PSP2";

goalw thy [unless_def]
   "!!Acts. [| LeadsTo Init Acts A A'; unless Acts B B'; id: Acts |] \
\           ==> LeadsTo Init Acts (A Int B) ((A' Int B) Un B')";
by (dtac R_PSP 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Un_Diff_Diff, Int_Diff_Un]) 2);
by (asm_full_simp_tac (simpset() addsimps [Diff_Int_distrib]) 2);
by (etac LeadsTo_Diff 2);
by (blast_tac (claset() addIs [subset_imp_LeadsTo]) 2);
by Auto_tac;
qed "R_PSP_unless";


(*** Induction rules ***)

(** Meta or object quantifier ????? **)
goalw thy [LeadsTo_def]
   "!!Acts. [| wf r;     \
\              ALL m. LeadsTo Init Acts (A Int f-``{m})                     \
\                                       ((A Int f-``(r^-1 ^^ {m})) Un B);   \
\              id: Acts |] \
\           ==> LeadsTo Init Acts A B";
by (etac leadsTo_wf_induct 1);
by (assume_tac 2);
by (blast_tac (claset() addIs [leadsTo_weaken]) 1);
qed "LeadsTo_wf_induct";


goal thy
   "!!Acts. [| wf r;     \
\              ALL m:I. LeadsTo Init Acts (A Int f-``{m})                   \
\                                  ((A Int f-``(r^-1 ^^ {m})) Un B);   \
\              id: Acts |] \
\           ==> LeadsTo Init Acts A ((A - (f-``I)) Un B)";
by (etac LeadsTo_wf_induct 1);
by Safe_tac;
by (case_tac "m:I" 1);
by (blast_tac (claset() addIs [LeadsTo_weaken]) 1);
by (blast_tac (claset() addIs [subset_imp_LeadsTo]) 1);
qed "R_bounded_induct";


goal thy
   "!!Acts. [| ALL m. LeadsTo Init Acts (A Int f-``{m})                     \
\                                  ((A Int f-``(lessThan m)) Un B);   \
\              id: Acts |] \
\           ==> LeadsTo Init Acts A B";
by (rtac (wf_less_than RS LeadsTo_wf_induct) 1);
by (assume_tac 2);
by (Asm_simp_tac 1);
qed "R_lessThan_induct";

goal thy
   "!!Acts. [| ALL m:(greaterThan l). LeadsTo Init Acts (A Int f-``{m})   \
\                                        ((A Int f-``(lessThan m)) Un B);   \
\              id: Acts |] \
\           ==> LeadsTo Init Acts A ((A Int (f-``(atMost l))) Un B)";
by (simp_tac (HOL_ss addsimps [Diff_eq RS sym, vimage_Compl, Compl_greaterThan RS sym]) 1);
by (rtac (wf_less_than RS R_bounded_induct) 1);
by (assume_tac 2);
by (Asm_simp_tac 1);
qed "R_lessThan_bounded_induct";

goal thy
   "!!Acts. [| ALL m:(lessThan l). LeadsTo Init Acts (A Int f-``{m})   \
\                                    ((A Int f-``(greaterThan m)) Un B);   \
\              id: Acts |] \
\           ==> LeadsTo Init Acts A ((A Int (f-``(atLeast l))) Un B)";
by (res_inst_tac [("f","f"),("f1", "%k. l - k")]
    (wf_less_than RS wf_inv_image RS LeadsTo_wf_induct) 1);
by (assume_tac 2);
by (simp_tac (simpset() addsimps [inv_image_def, Image_singleton]) 1);
by (Clarify_tac 1);
by (case_tac "m<l" 1);
by (blast_tac (claset() addIs [not_leE, subset_imp_LeadsTo]) 2);
by (blast_tac (claset() addIs [LeadsTo_weaken_R, diff_less_mono2]) 1);
qed "R_greaterThan_bounded_induct";



(*** Completion: Binary and General Finite versions ***)

goalw thy [LeadsTo_def]
   "!!Acts. [| LeadsTo Init Acts A A';  stable Acts A';   \
\              LeadsTo Init Acts B B';  stable Acts B';  id: Acts |] \
\           ==> LeadsTo Init Acts (A Int B) (A' Int B')";
by (blast_tac (claset() addIs [stable_completion RS leadsTo_weaken] 
                        addSIs [stable_Int, stable_reachable]) 1);
qed "R_stable_completion";


goal thy
   "!!Acts. [| finite I;  id: Acts |]                     \
\           ==> (ALL i:I. LeadsTo Init Acts (A i) (A' i)) -->  \
\               (ALL i:I. stable Acts (A' i)) -->         \
\               LeadsTo Init Acts (INT i:I. A i) (INT i:I. A' i)";
by (etac finite_induct 1);
by (Asm_simp_tac 1);
by (asm_simp_tac 
    (simpset() addsimps [R_stable_completion, stable_def, 
			 ball_constrains_INT]) 1);
qed_spec_mp "R_finite_stable_completion";


goalw thy [LeadsTo_def]
 "!!Acts. [| LeadsTo Init Acts A (A' Un C);  constrains Acts A' (A' Un C); \
\            LeadsTo Init Acts B (B' Un C);  constrains Acts B' (B' Un C); \
\            id: Acts |] \
\         ==> LeadsTo Init Acts (A Int B) ((A' Int B') Un C)";

by (full_simp_tac (simpset() addsimps [Int_Un_distrib]) 1);
by (dtac completion 1);
by (assume_tac 2);
by (ALLGOALS 
    (asm_simp_tac 
     (simpset() addsimps [constrains_reachable, Int_Un_distrib RS sym])));
by (blast_tac (claset() addIs [leadsTo_weaken]) 1);
qed "R_completion";


goal thy
   "!!Acts. [| finite I;  id: Acts |] \
\           ==> (ALL i:I. LeadsTo Init Acts (A i) (A' i Un C)) -->  \
\               (ALL i:I. constrains Acts (A' i) (A' i Un C)) --> \
\               LeadsTo Init Acts (INT i:I. A i) ((INT i:I. A' i) Un C)";
by (etac finite_induct 1);
by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (dtac ball_constrains_INT 1);
by (asm_full_simp_tac (simpset() addsimps [R_completion]) 1); 
qed "R_finite_completion";

