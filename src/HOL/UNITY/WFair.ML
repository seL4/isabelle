(*  Title:      HOL/UNITY/WFair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak Fairness versions of transient, ensures, leadsTo.

From Misra, "A Logic for Concurrent Programming", 1994
*)

open WFair;

goal thy "Union(B) Int A = Union((%C. C Int A)``B)";
by (Blast_tac 1);
qed "Int_Union_Union";


(*** transient ***)

goalw thy [stable_def, constrains_def, transient_def]
    "!!A. [| stable Acts A; transient Acts A |] ==> A = {}";
by (Blast_tac 1);
qed "stable_transient_empty";

goalw thy [transient_def]
    "!!A. [| transient Acts A; B<=A |] ==> transient Acts B";
by (Clarify_tac 1);
by (rtac bexI 1 THEN assume_tac 2);
by (Blast_tac 1);
qed "transient_strengthen";

goalw thy [transient_def]
    "!!A. [| act:Acts;  A <= Domain act;  act^^A <= Compl A |] \
\         ==> transient Acts A";
by (Blast_tac 1);
qed "transient_mem";


(*** ensures ***)

goalw thy [ensures_def]
    "!!Acts. [| constrains Acts (A-B) (A Un B); transient Acts (A-B) |] \
\            ==> ensures Acts A B";
by (Blast_tac 1);
qed "ensuresI";

goalw thy [ensures_def]
    "!!Acts. ensures Acts A B  \
\            ==> constrains Acts (A-B) (A Un B) & transient Acts (A-B)";
by (Blast_tac 1);
qed "ensuresD";

(*The L-version (precondition strengthening) doesn't hold for ENSURES*)
goalw thy [ensures_def]
    "!!Acts. [| ensures Acts A A'; A'<=B' |] ==> ensures Acts A B'";
by (blast_tac (claset() addIs [constrains_weaken, transient_strengthen]) 1);
qed "ensures_weaken_R";

goalw thy [ensures_def, constrains_def, transient_def]
    "!!Acts. Acts ~= {} ==> ensures Acts A UNIV";
by (Asm_simp_tac 1);  (*omitting this causes PROOF FAILED, even with Safe_tac*)
by (Blast_tac 1);
qed "ensures_UNIV";

goalw thy [ensures_def]
    "!!Acts. [| stable Acts C; \
\               constrains Acts (C Int (A - A')) (A Un A'); \
\               transient  Acts (C Int (A-A')) |]   \
\           ==> ensures Acts (C Int A) (C Int A')";
by (asm_simp_tac (simpset() addsimps [Int_Un_distrib RS sym,
				      Diff_Int_distrib RS sym,
				      stable_constrains_Int]) 1);
qed "stable_ensures_Int";


(*** leadsTo ***)

(*Synonyms for the theorems produced by the inductive defn package*)
bind_thm ("leadsTo_Basis", leadsto.Basis);
bind_thm ("leadsTo_Trans", leadsto.Trans);

goal thy "!!Acts. act: Acts ==> leadsTo Acts A UNIV";
by (blast_tac (claset() addIs [ensures_UNIV RS leadsTo_Basis]) 1);
qed "leadsTo_UNIV";
Addsimps [leadsTo_UNIV];

(*Useful with cancellation, disjunction*)
goal thy "!!Acts. leadsTo Acts A (A' Un A') ==> leadsTo Acts A A'";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "leadsTo_Un_duplicate";

goal thy "!!Acts. leadsTo Acts A (A' Un C Un C) ==> leadsTo Acts A (A' Un C)";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "leadsTo_Un_duplicate2";

(*The Union introduction rule as we should have liked to state it*)
val prems = goal thy
    "(!!A. A : S ==> leadsTo Acts A B) ==> leadsTo Acts (Union S) B";
by (blast_tac (claset() addIs (leadsto.Union::prems)) 1);
qed "leadsTo_Union";

val prems = goal thy
    "(!!i. i : I ==> leadsTo Acts (A i) B) ==> leadsTo Acts (UN i:I. A i) B";
by (simp_tac (simpset() addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs (leadsto.Union::prems)) 1);
qed "leadsTo_UN";

(*Binary union introduction rule*)
goal thy
  "!!C. [| leadsTo Acts A C; leadsTo Acts B C |] ==> leadsTo Acts (A Un B) C";
by (stac Un_eq_Union 1);
by (blast_tac (claset() addIs [leadsTo_Union]) 1);
qed "leadsTo_Un";


(*The INDUCTION rule as we should have liked to state it*)
val major::prems = goal thy
  "[| leadsTo Acts za zb;  \
\     !!A B. ensures Acts A B ==> P A B; \
\     !!A B C. [| leadsTo Acts A B; P A B; leadsTo Acts B C; P B C |] \
\              ==> P A C; \
\     !!B S. ALL A:S. leadsTo Acts A B & P A B ==> P (Union S) B \
\  |] ==> P za zb";
br (major RS leadsto.induct) 1;
by (REPEAT (blast_tac (claset() addIs prems) 1));
qed "leadsTo_induct";


goal thy "!!A B. [| A<=B;  id: Acts |] ==> leadsTo Acts A B";
by (rtac leadsTo_Basis 1);
by (rewrite_goals_tac [ensures_def, constrains_def, transient_def]);
by (Blast_tac 1);
qed "subset_imp_leadsTo";

bind_thm ("empty_leadsTo", empty_subsetI RS subset_imp_leadsTo);
Addsimps [empty_leadsTo];


(*There's a direct proof by leadsTo_Trans and subset_imp_leadsTo, but it
  needs the extra premise id:Acts*)
goal thy "!!Acts. leadsTo Acts A A' ==> A'<=B' --> leadsTo Acts A B'";
by (etac leadsTo_induct 1);
by (Clarify_tac 3);
by (blast_tac (claset() addIs [leadsTo_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (blast_tac (claset() addIs [leadsTo_Basis, ensures_weaken_R]) 1);
qed_spec_mp "leadsTo_weaken_R";


goal thy "!!Acts. [| leadsTo Acts A A'; B<=A; id: Acts |] ==>  \
\                 leadsTo Acts B A'";
by (blast_tac (claset() addIs [leadsTo_Basis, leadsTo_Trans, 
			       subset_imp_leadsTo]) 1);
qed_spec_mp "leadsTo_weaken_L";

(*Distributes over binary unions*)
goal thy
  "!!C. id: Acts ==> \
\       leadsTo Acts (A Un B) C  =  (leadsTo Acts A C & leadsTo Acts B C)";
by (blast_tac (claset() addIs [leadsTo_Un, leadsTo_weaken_L]) 1);
qed "leadsTo_Un_distrib";

goal thy
  "!!C. id: Acts ==> \
\       leadsTo Acts (UN i:I. A i) B  =  (ALL i : I. leadsTo Acts (A i) B)";
by (blast_tac (claset() addIs [leadsTo_UN, leadsTo_weaken_L]) 1);
qed "leadsTo_UN_distrib";

goal thy
  "!!C. id: Acts ==> \
\       leadsTo Acts (Union S) B  =  (ALL A : S. leadsTo Acts A B)";
by (blast_tac (claset() addIs [leadsTo_Union, leadsTo_weaken_L]) 1);
qed "leadsTo_Union_distrib";


goal thy
   "!!Acts. [| leadsTo Acts A A'; id: Acts; B<=A; A'<=B' |] \
\           ==> leadsTo Acts B B'";
(*PROOF FAILED: why?*)
by (blast_tac (claset() addIs [leadsTo_Trans, leadsTo_weaken_R,
			       leadsTo_weaken_L]) 1);
qed "leadsTo_weaken";


(*Set difference: maybe combine with leadsTo_weaken_L??*)
goal thy
  "!!C. [| leadsTo Acts (A-B) C; leadsTo Acts B C; id: Acts |] \
\       ==> leadsTo Acts A C";
by (blast_tac (claset() addIs [leadsTo_Un, leadsTo_weaken]) 1);
qed "leadsTo_Diff";


(** Meta or object quantifier ???
    see ball_constrains_UN in UNITY.ML***)

val prems = goal thy
   "(!! i. i:I ==> leadsTo Acts (A i) (A' i)) \
\   ==> leadsTo Acts (UN i:I. A i) (UN i:I. A' i)";
by (simp_tac (simpset() addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs [leadsTo_Union, leadsTo_weaken_R] 
                        addIs prems) 1);
qed "leadsTo_UN_UN";


(*Version with no index set*)
val prems = goal thy
   "(!! i. leadsTo Acts (A i) (A' i)) \
\   ==> leadsTo Acts (UN i. A i) (UN i. A' i)";
by (blast_tac (claset() addIs [leadsTo_UN_UN] 
                        addIs prems) 1);
qed "leadsTo_UN_UN_noindex";

(*Version with no index set*)
goal thy
   "!!Acts. ALL i. leadsTo Acts (A i) (A' i) \
\           ==> leadsTo Acts (UN i. A i) (UN i. A' i)";
by (blast_tac (claset() addIs [leadsTo_UN_UN]) 1);
qed "all_leadsTo_UN_UN";


(*Binary union version*)
goal thy "!!Acts. [| leadsTo Acts A A'; leadsTo Acts B B' |] \
\                 ==> leadsTo Acts (A Un B) (A' Un B')";
by (blast_tac (claset() addIs [leadsTo_Un, 
			       leadsTo_weaken_R]) 1);
qed "leadsTo_Un_Un";


(** The cancellation law **)

goal thy
   "!!Acts. [| leadsTo Acts A (A' Un B); leadsTo Acts B B'; id: Acts |] \
\           ==> leadsTo Acts A (A' Un B')";
by (blast_tac (claset() addIs [leadsTo_Un_Un, 
			       subset_imp_leadsTo, leadsTo_Trans]) 1);
qed "leadsTo_cancel2";

goal thy
   "!!Acts. [| leadsTo Acts A (A' Un B); leadsTo Acts (B-A') B'; id: Acts |] \
\           ==> leadsTo Acts A (A' Un B')";
by (rtac leadsTo_cancel2 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "leadsTo_cancel_Diff2";

goal thy
   "!!Acts. [| leadsTo Acts A (B Un A'); leadsTo Acts B B'; id: Acts |] \
\           ==> leadsTo Acts A (B' Un A')";
by (asm_full_simp_tac (simpset() addsimps [Un_commute]) 1);
by (blast_tac (claset() addSIs [leadsTo_cancel2]) 1);
qed "leadsTo_cancel1";

goal thy
   "!!Acts. [| leadsTo Acts A (B Un A'); leadsTo Acts (B-A') B'; id: Acts |] \
\           ==> leadsTo Acts A (B' Un A')";
by (rtac leadsTo_cancel1 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "leadsTo_cancel_Diff1";



(** The impossibility law **)

goal thy "!!Acts. leadsTo Acts A B ==> B={} --> A={}";
by (etac leadsTo_induct 1);
by (ALLGOALS Asm_simp_tac);
by (rewrite_goals_tac [ensures_def, constrains_def, transient_def]);
by (Blast_tac 1);
val lemma = result() RS mp;

goal thy "!!Acts. leadsTo Acts A {} ==> A={}";
by (blast_tac (claset() addSIs [lemma]) 1);
qed "leadsTo_empty";


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction".  Doesn't need id:Acts. *)
goalw thy [stable_def]
   "!!Acts. [| leadsTo Acts A A'; stable Acts B |] \
\           ==> leadsTo Acts (A Int B) (A' Int B)";
by (etac leadsTo_induct 1);
by (simp_tac (simpset() addsimps [Int_Union_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (rtac leadsTo_Basis 1);
by (asm_full_simp_tac
    (simpset() addsimps [ensures_def, 
			 Diff_Int_distrib2 RS sym, Int_Un_distrib2 RS sym]) 1);
by (blast_tac (claset() addIs [transient_strengthen, constrains_Int]) 1);
qed "PSP_stable";

goal thy
   "!!Acts. [| leadsTo Acts A A'; stable Acts B |] \
\           ==> leadsTo Acts (B Int A) (B Int A')";
by (asm_simp_tac (simpset() addsimps (PSP_stable::Int_ac)) 1);
qed "PSP_stable2";


goalw thy [ensures_def]
   "!!Acts. [| ensures Acts A A'; constrains Acts B B' |] \
\           ==> ensures Acts (A Int B) ((A' Int B) Un (B' - B))";
by Safe_tac;
by (blast_tac (claset() addIs [constrainsI] addDs [constrainsD]) 1);
by (etac transient_strengthen 1);
by (Blast_tac 1);
qed "PSP_ensures";


goal thy
   "!!Acts. [| leadsTo Acts A A'; constrains Acts B B'; id: Acts |] \
\           ==> leadsTo Acts (A Int B) ((A' Int B) Un (B' - B))";
by (etac leadsTo_induct 1);
by (simp_tac (simpset() addsimps [Int_Union_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Union]) 3);
(*Transitivity case has a delicate argument involving "cancellation"*)
by (rtac leadsTo_Un_duplicate2 2);
by (etac leadsTo_cancel_Diff1 2);
by (assume_tac 3);
by (asm_full_simp_tac (simpset() addsimps [Int_Diff, Diff_triv]) 2);
(*Basis case*)
by (blast_tac (claset() addIs [leadsTo_Basis, PSP_ensures]) 1);
qed "PSP";

goal thy
   "!!Acts. [| leadsTo Acts A A'; constrains Acts B B'; id: Acts |] \
\           ==> leadsTo Acts (B Int A) ((B Int A') Un (B' - B))";
by (asm_simp_tac (simpset() addsimps (PSP::Int_ac)) 1);
qed "PSP2";


goalw thy [unless_def]
   "!!Acts. [| leadsTo Acts A A'; unless Acts B B'; id: Acts |] \
\           ==> leadsTo Acts (A Int B) ((A' Int B) Un B')";
by (dtac PSP 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Un_Diff_Diff, Int_Diff_Un]) 2);
by (asm_full_simp_tac (simpset() addsimps [Diff_Int_distrib]) 2);
by (etac leadsTo_Diff 2);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 2);
by Auto_tac;
qed "PSP_unless";


(*** Proving the induction rules ***)

goal thy
   "!!Acts. [| wf r;     \
\              ALL m. leadsTo Acts (A Int f-``{m})                     \
\                                  ((A Int f-``(r^-1 ^^ {m})) Un B);   \
\              id: Acts |] \
\           ==> leadsTo Acts (A Int f-``{m}) B";
by (eres_inst_tac [("a","m")] wf_induct 1);
by (subgoal_tac "leadsTo Acts (A Int (f -`` (r^-1 ^^ {x}))) B" 1);
by (stac vimage_eq_UN 2);
by (asm_simp_tac (HOL_ss addsimps (UN_simps RL [sym])) 2);
by (blast_tac (claset() addIs [leadsTo_UN]) 2);
by (blast_tac (claset() addIs [leadsTo_cancel1, leadsTo_Un_duplicate]) 1);
val lemma = result();


(** Meta or object quantifier ????? **)
goal thy
   "!!Acts. [| wf r;     \
\              ALL m. leadsTo Acts (A Int f-``{m})                     \
\                                  ((A Int f-``(r^-1 ^^ {m})) Un B);   \
\              id: Acts |] \
\           ==> leadsTo Acts A B";
by (res_inst_tac [("t", "A")] subst 1);
by (rtac leadsTo_UN 2);
by (etac lemma 2);
by (REPEAT (assume_tac 2));
by (Fast_tac 1);    (*Blast_tac: Function unknown's argument not a parameter*)
qed "leadsTo_wf_induct";


goal thy
   "!!Acts. [| wf r;     \
\              ALL m:I. leadsTo Acts (A Int f-``{m})                   \
\                                  ((A Int f-``(r^-1 ^^ {m})) Un B);   \
\              id: Acts |] \
\           ==> leadsTo Acts A ((A - (f-``I)) Un B)";
by (etac leadsTo_wf_induct 1);
by Safe_tac;
by (case_tac "m:I" 1);
by (blast_tac (claset() addIs [leadsTo_weaken]) 1);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
qed "bounded_induct";


(*Alternative proof is via the lemma leadsTo Acts (A Int f-``(lessThan m)) B*)
goal thy
   "!!Acts. [| ALL m. leadsTo Acts (A Int f-``{m})                     \
\                                  ((A Int f-``(lessThan m)) Un B);   \
\              id: Acts |] \
\           ==> leadsTo Acts A B";
by (rtac (wf_less_than RS leadsTo_wf_induct) 1);
by (assume_tac 2);
by (Asm_simp_tac 1);
qed "lessThan_induct";

goal thy
   "!!Acts. [| ALL m:(greaterThan l). leadsTo Acts (A Int f-``{m})   \
\                                        ((A Int f-``(lessThan m)) Un B);   \
\              id: Acts |] \
\           ==> leadsTo Acts A ((A Int (f-``(atMost l))) Un B)";
by (simp_tac (HOL_ss addsimps [Diff_eq RS sym, vimage_Compl, Compl_greaterThan RS sym]) 1);
by (rtac (wf_less_than RS bounded_induct) 1);
by (assume_tac 2);
by (Asm_simp_tac 1);
qed "lessThan_bounded_induct";

goal thy
   "!!Acts. [| ALL m:(lessThan l). leadsTo Acts (A Int f-``{m})   \
\                                    ((A Int f-``(greaterThan m)) Un B);   \
\              id: Acts |] \
\           ==> leadsTo Acts A ((A Int (f-``(atLeast l))) Un B)";
by (res_inst_tac [("f","f"),("f1", "%k. l - k")]
    (wf_less_than RS wf_inv_image RS leadsTo_wf_induct) 1);
by (assume_tac 2);
by (simp_tac (simpset() addsimps [inv_image_def, Image_singleton]) 1);
by (Clarify_tac 1);
by (case_tac "m<l" 1);
by (blast_tac (claset() addIs [not_leE, subset_imp_leadsTo]) 2);
by (blast_tac (claset() addIs [leadsTo_weaken_R, diff_less_mono2]) 1);
qed "greaterThan_bounded_induct";



(*** wlt ****)

(*Misra's property W3*)
goalw thy [wlt_def] "leadsTo Acts (wlt Acts B) B";
by (blast_tac (claset() addSIs [leadsTo_Union]) 1);
qed "wlt_leadsTo";

goalw thy [wlt_def] "!!Acts. leadsTo Acts A B ==> A <= wlt Acts B";
by (blast_tac (claset() addSIs [leadsTo_Union]) 1);
qed "leadsTo_subset";

(*Misra's property W2*)
goal thy "!!Acts. id: Acts ==> leadsTo Acts A B = (A <= wlt Acts B)";
by (blast_tac (claset() addSIs [leadsTo_subset, 
				wlt_leadsTo RS leadsTo_weaken_L]) 1);
qed "leadsTo_eq_subset_wlt";

(*Misra's property W4*)
goal thy "!!Acts. id: Acts ==> B <= wlt Acts B";
by (asm_simp_tac (simpset() addsimps [leadsTo_eq_subset_wlt RS sym,
				      subset_imp_leadsTo]) 1);
qed "wlt_increasing";


(*Used in the Trans case below*)
goalw thy [constrains_def]
   "!!Acts. [| B <= A2;  \
\              constrains Acts (A1 - B) (A1 Un B); \
\              constrains Acts (A2 - C) (A2 Un C) |] \
\           ==> constrains Acts (A1 Un A2 - C) (A1 Un A2 Un C)";
by (Clarify_tac 1);
by (blast_tac (claset() addSDs [bspec]) 1);
val lemma1 = result();


(*Lemma (1,2,3) of Misra's draft book, Chapter 4, "Progress"*)
goal thy
   "!!Acts. [| leadsTo Acts A A';  id: Acts |] ==> \
\      EX B. A<=B & leadsTo Acts B A' & constrains Acts (B-A') (B Un A')";
by (etac leadsTo_induct 1);
(*Basis*)
by (blast_tac (claset() addIs [leadsTo_Basis]
                        addDs [ensuresD]) 1);
(*Trans*)
by (Clarify_tac 1);
by (res_inst_tac [("x", "Ba Un Bb")] exI 1);
by (blast_tac (claset() addIs [lemma1, leadsTo_Un_Un, leadsTo_cancel1,
			       leadsTo_Un_duplicate]) 1);
(*Union*)
by (clarify_tac (claset() addSDs [ball_conj_distrib RS iffD1,
				  bchoice, ball_constrains_UN]) 1);;
by (res_inst_tac [("x", "UN A:S. f A")] exI 1);
by (blast_tac (claset() addIs [leadsTo_UN, constrains_weaken]) 1);
qed "leadsTo_123";


(*Misra's property W5*)
goal thy "!!Acts. id: Acts ==> constrains Acts (wlt Acts B - B) (wlt Acts B)";
by (forward_tac [wlt_leadsTo RS leadsTo_123] 1);
by (Clarify_tac 1);
by (subgoal_tac "Ba = wlt Acts B" 1);
by (blast_tac (claset() addDs [leadsTo_eq_subset_wlt]) 2);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [wlt_increasing, Un_absorb2]) 1);
qed "wlt_constrains_wlt";


(*** Completion: Binary and General Finite versions ***)

goal thy
   "!!Acts. [| leadsTo Acts A A';  stable Acts A';   \
\              leadsTo Acts B B';  stable Acts B';  id: Acts |] \
\           ==> leadsTo Acts (A Int B) (A' Int B')";
by (subgoal_tac "stable Acts (wlt Acts B')" 1);
by (asm_full_simp_tac (simpset() addsimps [stable_def]) 2);
by (EVERY [etac (constrains_Un RS constrains_weaken) 2,
	   etac wlt_constrains_wlt 2,
	   fast_tac (claset() addEs [wlt_increasing RSN (2,rev_subsetD)]) 3,
	   Blast_tac 2]);
by (subgoal_tac "leadsTo Acts (A Int wlt Acts B') (A' Int wlt Acts B')" 1);
by (blast_tac (claset() addIs [PSP_stable]) 2);
by (subgoal_tac "leadsTo Acts (A' Int wlt Acts B') (A' Int B')" 1);
by (blast_tac (claset() addIs [wlt_leadsTo, PSP_stable2]) 2);
by (subgoal_tac "leadsTo Acts (A Int B) (A Int wlt Acts B')" 1);
by (blast_tac (claset() addIs [leadsTo_subset RS subsetD, 
			       subset_imp_leadsTo]) 2);
(*Blast_tac gives PROOF FAILED*)
by (best_tac (claset() addIs [leadsTo_Trans]) 1);
qed "stable_completion";


goal thy
   "!!Acts. [| finite I;  id: Acts |]                     \
\           ==> (ALL i:I. leadsTo Acts (A i) (A' i)) -->  \
\               (ALL i:I. stable Acts (A' i)) -->         \
\               leadsTo Acts (INT i:I. A i) (INT i:I. A' i)";
by (etac finite_induct 1);
by (Asm_simp_tac 1);
by (asm_simp_tac 
    (simpset() addsimps [stable_completion, stable_def, 
			 ball_constrains_INT]) 1);
qed_spec_mp "finite_stable_completion";


goal thy
   "!!Acts. [| W = wlt Acts (B' Un C);     \
\              leadsTo Acts A (A' Un C);  constrains Acts A' (A' Un C);   \
\              leadsTo Acts B (B' Un C);  constrains Acts B' (B' Un C);   \
\              id: Acts |] \
\           ==> leadsTo Acts (A Int B) ((A' Int B') Un C)";
by (subgoal_tac "constrains Acts (W-C) (W Un B' Un C)" 1);
by (blast_tac (claset() addIs [[asm_rl, wlt_constrains_wlt] 
			       MRS constrains_Un RS constrains_weaken]) 2);
by (subgoal_tac "constrains Acts (W-C) W" 1);
by (asm_full_simp_tac 
    (simpset() addsimps [wlt_increasing, Un_assoc, Un_absorb2]) 2);
by (subgoal_tac "leadsTo Acts (A Int W - C) (A' Int W Un C)" 1);
by (simp_tac (simpset() addsimps [Int_Diff]) 2);
by (blast_tac (claset() addIs [wlt_leadsTo, PSP RS leadsTo_weaken_R]) 2);
by (subgoal_tac "leadsTo Acts (A' Int W Un C) (A' Int B' Un C)" 1);
by (blast_tac (claset() addIs [wlt_leadsTo, leadsTo_Un_Un, 
                               PSP2 RS leadsTo_weaken_R, 
			       subset_refl RS subset_imp_leadsTo, 
			       leadsTo_Un_duplicate2]) 2);
by (dtac leadsTo_Diff 1);
by (assume_tac 2);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
by (subgoal_tac "A Int B <= A Int W" 1);
by (blast_tac (claset() addIs [leadsTo_subset, Int_mono] 
	                delrules [subsetI]) 2);
by (blast_tac (claset() addIs [leadsTo_Trans, subset_imp_leadsTo]) 1);
bind_thm("completion", refl RS result());


goal thy
   "!!Acts. [| finite I;  id: Acts |] \
\           ==> (ALL i:I. leadsTo Acts (A i) (A' i Un C)) -->  \
\               (ALL i:I. constrains Acts (A' i) (A' i Un C)) --> \
\               leadsTo Acts (INT i:I. A i) ((INT i:I. A' i) Un C)";
by (etac finite_induct 1);
by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (dtac ball_constrains_INT 1);
by (asm_full_simp_tac (simpset() addsimps [completion]) 1); 
qed "finite_completion";

