(*  Title:      HOL/UNITY/WFair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak Fairness versions of transient, ensures, leadsTo.

From Misra, "A Logic for Concurrent Programming", 1994
*)


(*** transient ***)

Goalw [stable_def, constrains_def, transient_def]
    "[| stable acts A; transient acts A |] ==> A = {}";
by (Blast_tac 1);
qed "stable_transient_empty";

Goalw [transient_def]
    "[| transient acts A; B<=A |] ==> transient acts B";
by (Clarify_tac 1);
by (rtac bexI 1 THEN assume_tac 2);
by (Blast_tac 1);
qed "transient_strengthen";

Goalw [transient_def]
    "[| act:acts;  A <= Domain act;  act^^A <= Compl A |] \
\         ==> transient acts A";
by (Blast_tac 1);
qed "transient_mem";


(*** ensures ***)

Goalw [ensures_def]
    "[| constrains acts (A-B) (A Un B); transient acts (A-B) |] \
\    ==> ensures acts A B";
by (Blast_tac 1);
qed "ensuresI";

Goalw [ensures_def]
    "ensures acts A B  \
\    ==> constrains acts (A-B) (A Un B) & transient acts (A-B)";
by (Blast_tac 1);
qed "ensuresD";

(*The L-version (precondition strengthening) doesn't hold for ENSURES*)
Goalw [ensures_def]
    "[| ensures acts A A'; A'<=B' |] ==> ensures acts A B'";
by (blast_tac (claset() addIs [constrains_weaken, transient_strengthen]) 1);
qed "ensures_weaken_R";

Goalw [ensures_def, constrains_def, transient_def]
    "acts ~= {} ==> ensures acts A UNIV";
by (Asm_simp_tac 1);  (*omitting this causes PROOF FAILED, even with Safe_tac*)
by (Blast_tac 1);
qed "ensures_UNIV";

Goalw [ensures_def]
    "[| stable acts C; \
\       constrains acts (C Int (A - A')) (A Un A'); \
\       transient  acts (C Int (A-A')) |]   \
\   ==> ensures acts (C Int A) (C Int A')";
by (asm_simp_tac (simpset() addsimps [Int_Un_distrib RS sym,
				      Diff_Int_distrib RS sym,
				      stable_constrains_Int]) 1);
qed "stable_ensures_Int";


(*** leadsTo ***)

(*Synonyms for the theorems produced by the inductive defn package*)
bind_thm ("leadsTo_Basis", leadsto.Basis);
bind_thm ("leadsTo_Trans", leadsto.Trans);

Goal "act: acts ==> leadsTo acts A UNIV";
by (blast_tac (claset() addIs [ensures_UNIV RS leadsTo_Basis]) 1);
qed "leadsTo_UNIV";
Addsimps [leadsTo_UNIV];

(*Useful with cancellation, disjunction*)
Goal "leadsTo acts A (A' Un A') ==> leadsTo acts A A'";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "leadsTo_Un_duplicate";

Goal "leadsTo acts A (A' Un C Un C) ==> leadsTo acts A (A' Un C)";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "leadsTo_Un_duplicate2";

(*The Union introduction rule as we should have liked to state it*)
val prems = goal thy
    "(!!A. A : S ==> leadsTo acts A B) ==> leadsTo acts (Union S) B";
by (blast_tac (claset() addIs (leadsto.Union::prems)) 1);
qed "leadsTo_Union";

val prems = goal thy
    "(!!i. i : I ==> leadsTo acts (A i) B) ==> leadsTo acts (UN i:I. A i) B";
by (simp_tac (simpset() addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs (leadsto.Union::prems)) 1);
qed "leadsTo_UN";

(*Binary union introduction rule*)
Goal "[| leadsTo acts A C; leadsTo acts B C |] ==> leadsTo acts (A Un B) C";
by (stac Un_eq_Union 1);
by (blast_tac (claset() addIs [leadsTo_Union]) 1);
qed "leadsTo_Un";


(*The INDUCTION rule as we should have liked to state it*)
val major::prems = goal thy
  "[| leadsTo acts za zb;  \
\     !!A B. ensures acts A B ==> P A B; \
\     !!A B C. [| leadsTo acts A B; P A B; leadsTo acts B C; P B C |] \
\              ==> P A C; \
\     !!B S. ALL A:S. leadsTo acts A B & P A B ==> P (Union S) B \
\  |] ==> P za zb";
by (rtac (major RS leadsto.induct) 1);
by (REPEAT (blast_tac (claset() addIs prems) 1));
qed "leadsTo_induct";


Goal "[| A<=B;  id: acts |] ==> leadsTo acts A B";
by (rtac leadsTo_Basis 1);
by (rewrite_goals_tac [ensures_def, constrains_def, transient_def]);
by (Blast_tac 1);
qed "subset_imp_leadsTo";

bind_thm ("empty_leadsTo", empty_subsetI RS subset_imp_leadsTo);
Addsimps [empty_leadsTo];


(*There's a direct proof by leadsTo_Trans and subset_imp_leadsTo, but it
  needs the extra premise id:acts*)
Goal "leadsTo acts A A' ==> A'<=B' --> leadsTo acts A B'";
by (etac leadsTo_induct 1);
by (Clarify_tac 3);
by (blast_tac (claset() addIs [leadsTo_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (blast_tac (claset() addIs [leadsTo_Basis, ensures_weaken_R]) 1);
qed_spec_mp "leadsTo_weaken_R";


Goal "[| leadsTo acts A A'; B<=A; id: acts |] ==>  \
\         leadsTo acts B A'";
by (blast_tac (claset() addIs [leadsTo_Basis, leadsTo_Trans, 
			       subset_imp_leadsTo]) 1);
qed_spec_mp "leadsTo_weaken_L";

(*Distributes over binary unions*)
Goal "id: acts ==> \
\       leadsTo acts (A Un B) C  =  (leadsTo acts A C & leadsTo acts B C)";
by (blast_tac (claset() addIs [leadsTo_Un, leadsTo_weaken_L]) 1);
qed "leadsTo_Un_distrib";

Goal "id: acts ==> \
\       leadsTo acts (UN i:I. A i) B  =  (ALL i : I. leadsTo acts (A i) B)";
by (blast_tac (claset() addIs [leadsTo_UN, leadsTo_weaken_L]) 1);
qed "leadsTo_UN_distrib";

Goal "id: acts ==> \
\       leadsTo acts (Union S) B  =  (ALL A : S. leadsTo acts A B)";
by (blast_tac (claset() addIs [leadsTo_Union, leadsTo_weaken_L]) 1);
qed "leadsTo_Union_distrib";


Goal "[| leadsTo acts A A'; id: acts; B<=A; A'<=B' |] \
\   ==> leadsTo acts B B'";
(*PROOF FAILED: why?*)
by (blast_tac (claset() addIs [leadsTo_Trans, leadsTo_weaken_R,
			       leadsTo_weaken_L]) 1);
qed "leadsTo_weaken";


(*Set difference: maybe combine with leadsTo_weaken_L??*)
Goal "[| leadsTo acts (A-B) C; leadsTo acts B C; id: acts |] \
\       ==> leadsTo acts A C";
by (blast_tac (claset() addIs [leadsTo_Un, leadsTo_weaken]) 1);
qed "leadsTo_Diff";


(** Meta or object quantifier ???
    see ball_constrains_UN in UNITY.ML***)

val prems = goal thy
   "(!! i. i:I ==> leadsTo acts (A i) (A' i)) \
\   ==> leadsTo acts (UN i:I. A i) (UN i:I. A' i)";
by (simp_tac (simpset() addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs [leadsTo_Union, leadsTo_weaken_R] 
                        addIs prems) 1);
qed "leadsTo_UN_UN";


(*Version with no index set*)
val prems = goal thy
   "(!! i. leadsTo acts (A i) (A' i)) \
\   ==> leadsTo acts (UN i. A i) (UN i. A' i)";
by (blast_tac (claset() addIs [leadsTo_UN_UN] 
                        addIs prems) 1);
qed "leadsTo_UN_UN_noindex";

(*Version with no index set*)
Goal "ALL i. leadsTo acts (A i) (A' i) \
\   ==> leadsTo acts (UN i. A i) (UN i. A' i)";
by (blast_tac (claset() addIs [leadsTo_UN_UN]) 1);
qed "all_leadsTo_UN_UN";


(*Binary union version*)
Goal "[| leadsTo acts A A'; leadsTo acts B B' |] \
\         ==> leadsTo acts (A Un B) (A' Un B')";
by (blast_tac (claset() addIs [leadsTo_Un, 
			       leadsTo_weaken_R]) 1);
qed "leadsTo_Un_Un";


(** The cancellation law **)

Goal "[| leadsTo acts A (A' Un B); leadsTo acts B B'; id: acts |] \
\   ==> leadsTo acts A (A' Un B')";
by (blast_tac (claset() addIs [leadsTo_Un_Un, 
			       subset_imp_leadsTo, leadsTo_Trans]) 1);
qed "leadsTo_cancel2";

Goal "[| leadsTo acts A (A' Un B); leadsTo acts (B-A') B'; id: acts |] \
\   ==> leadsTo acts A (A' Un B')";
by (rtac leadsTo_cancel2 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "leadsTo_cancel_Diff2";

Goal "[| leadsTo acts A (B Un A'); leadsTo acts B B'; id: acts |] \
\   ==> leadsTo acts A (B' Un A')";
by (asm_full_simp_tac (simpset() addsimps [Un_commute]) 1);
by (blast_tac (claset() addSIs [leadsTo_cancel2]) 1);
qed "leadsTo_cancel1";

Goal "[| leadsTo acts A (B Un A'); leadsTo acts (B-A') B'; id: acts |] \
\   ==> leadsTo acts A (B' Un A')";
by (rtac leadsTo_cancel1 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "leadsTo_cancel_Diff1";



(** The impossibility law **)

Goal "leadsTo acts A B ==> B={} --> A={}";
by (etac leadsTo_induct 1);
by (ALLGOALS Asm_simp_tac);
by (rewrite_goals_tac [ensures_def, constrains_def, transient_def]);
by (Blast_tac 1);
val lemma = result() RS mp;

Goal "leadsTo acts A {} ==> A={}";
by (blast_tac (claset() addSIs [lemma]) 1);
qed "leadsTo_empty";


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction".  Doesn't need id:acts. *)
Goalw [stable_def]
   "[| leadsTo acts A A'; stable acts B |] \
\   ==> leadsTo acts (A Int B) (A' Int B)";
by (etac leadsTo_induct 1);
by (simp_tac (simpset() addsimps [Int_Union_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (rtac leadsTo_Basis 1);
by (asm_full_simp_tac
    (simpset() addsimps [ensures_def, 
			 Diff_Int_distrib2 RS sym, Int_Un_distrib2 RS sym]) 1);
by (blast_tac (claset() addIs [transient_strengthen, constrains_Int]) 1);
qed "psp_stable";

Goal "[| leadsTo acts A A'; stable acts B |] \
\   ==> leadsTo acts (B Int A) (B Int A')";
by (asm_simp_tac (simpset() addsimps (psp_stable::Int_ac)) 1);
qed "psp_stable2";

Goalw [ensures_def, constrains_def]
   "[| ensures acts A A'; constrains acts B B' |] \
\   ==> ensures acts (A Int B) ((A' Int B) Un (B' - B))";
by (blast_tac (claset() addIs [transient_strengthen]) 1);
qed "psp_ensures";

Goal "[| leadsTo acts A A'; constrains acts B B'; id: acts |] \
\           ==> leadsTo acts (A Int B) ((A' Int B) Un (B' - B))";
by (etac leadsTo_induct 1);
by (simp_tac (simpset() addsimps [Int_Union_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Union]) 3);
(*Transitivity case has a delicate argument involving "cancellation"*)
by (rtac leadsTo_Un_duplicate2 2);
by (etac leadsTo_cancel_Diff1 2);
by (assume_tac 3);
by (asm_full_simp_tac (simpset() addsimps [Int_Diff, Diff_triv]) 2);
(*Basis case*)
by (blast_tac (claset() addIs [leadsTo_Basis, psp_ensures]) 1);
qed "psp";

Goal "[| leadsTo acts A A'; constrains acts B B'; id: acts |] \
\   ==> leadsTo acts (B Int A) ((B Int A') Un (B' - B))";
by (asm_simp_tac (simpset() addsimps (psp::Int_ac)) 1);
qed "psp2";


Goalw [unless_def]
   "[| leadsTo acts A A'; unless acts B B'; id: acts |] \
\   ==> leadsTo acts (A Int B) ((A' Int B) Un B')";
by (dtac psp 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Un_Diff_Diff, Int_Diff_Un]) 2);
by (asm_full_simp_tac (simpset() addsimps [Diff_Int_distrib]) 2);
by (etac leadsTo_Diff 2);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 2);
by Auto_tac;
qed "psp_unless";


(*** Proving the induction rules ***)

(** The most general rule: r is any wf relation; f is any variant function **)

Goal "[| wf r;     \
\        ALL m. leadsTo acts (A Int f-``{m})                     \
\                            ((A Int f-``(r^-1 ^^ {m})) Un B);   \
\        id: acts |] \
\     ==> leadsTo acts (A Int f-``{m}) B";
by (eres_inst_tac [("a","m")] wf_induct 1);
by (subgoal_tac "leadsTo acts (A Int (f -`` (r^-1 ^^ {x}))) B" 1);
by (stac vimage_eq_UN 2);
by (asm_simp_tac (HOL_ss addsimps (UN_simps RL [sym])) 2);
by (blast_tac (claset() addIs [leadsTo_UN]) 2);
by (blast_tac (claset() addIs [leadsTo_cancel1, leadsTo_Un_duplicate]) 1);
val lemma = result();


(** Meta or object quantifier ????? **)
Goal "[| wf r;     \
\        ALL m. leadsTo acts (A Int f-``{m})                     \
\                            ((A Int f-``(r^-1 ^^ {m})) Un B);   \
\        id: acts |] \
\     ==> leadsTo acts A B";
by (res_inst_tac [("t", "A")] subst 1);
by (rtac leadsTo_UN 2);
by (etac lemma 2);
by (REPEAT (assume_tac 2));
by (Fast_tac 1);    (*Blast_tac: Function unknown's argument not a parameter*)
qed "leadsTo_wf_induct";


Goal "[| wf r;     \
\        ALL m:I. leadsTo acts (A Int f-``{m})                   \
\                              ((A Int f-``(r^-1 ^^ {m})) Un B);   \
\        id: acts |] \
\     ==> leadsTo acts A ((A - (f-``I)) Un B)";
by (etac leadsTo_wf_induct 1);
by Safe_tac;
by (case_tac "m:I" 1);
by (blast_tac (claset() addIs [leadsTo_weaken]) 1);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
qed "bounded_induct";


(*Alternative proof is via the lemma leadsTo acts (A Int f-``(lessThan m)) B*)
Goal "[| ALL m. leadsTo acts (A Int f-``{m})                     \
\                            ((A Int f-``(lessThan m)) Un B);   \
\        id: acts |] \
\     ==> leadsTo acts A B";
by (rtac (wf_less_than RS leadsTo_wf_induct) 1);
by (assume_tac 2);
by (Asm_simp_tac 1);
qed "lessThan_induct";

Goal "[| ALL m:(greaterThan l). leadsTo acts (A Int f-``{m})   \
\                                  ((A Int f-``(lessThan m)) Un B);   \
\        id: acts |] \
\     ==> leadsTo acts A ((A Int (f-``(atMost l))) Un B)";
by (simp_tac (HOL_ss addsimps [Diff_eq RS sym, vimage_Compl, Compl_greaterThan RS sym]) 1);
by (rtac (wf_less_than RS bounded_induct) 1);
by (assume_tac 2);
by (Asm_simp_tac 1);
qed "lessThan_bounded_induct";

Goal "[| ALL m:(lessThan l). leadsTo acts (A Int f-``{m})   \
\                              ((A Int f-``(greaterThan m)) Un B);   \
\        id: acts |] \
\     ==> leadsTo acts A ((A Int (f-``(atLeast l))) Un B)";
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
Goalw [wlt_def] "leadsTo acts (wlt acts B) B";
by (blast_tac (claset() addSIs [leadsTo_Union]) 1);
qed "wlt_leadsTo";

Goalw [wlt_def] "leadsTo acts A B ==> A <= wlt acts B";
by (blast_tac (claset() addSIs [leadsTo_Union]) 1);
qed "leadsTo_subset";

(*Misra's property W2*)
Goal "id: acts ==> leadsTo acts A B = (A <= wlt acts B)";
by (blast_tac (claset() addSIs [leadsTo_subset, 
				wlt_leadsTo RS leadsTo_weaken_L]) 1);
qed "leadsTo_eq_subset_wlt";

(*Misra's property W4*)
Goal "id: acts ==> B <= wlt acts B";
by (asm_simp_tac (simpset() addsimps [leadsTo_eq_subset_wlt RS sym,
				      subset_imp_leadsTo]) 1);
qed "wlt_increasing";


(*Used in the Trans case below*)
Goalw [constrains_def]
   "[| B <= A2;  \
\      constrains acts (A1 - B) (A1 Un B); \
\      constrains acts (A2 - C) (A2 Un C) |] \
\   ==> constrains acts (A1 Un A2 - C) (A1 Un A2 Un C)";
by (Clarify_tac 1);
by (blast_tac (claset() addSDs [bspec]) 1);
val lemma1 = result();


(*Lemma (1,2,3) of Misra's draft book, Chapter 4, "Progress"*)
Goal "[| leadsTo acts A A';  id: acts |] ==> \
\      EX B. A<=B & leadsTo acts B A' & constrains acts (B-A') (B Un A')";
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
Goal "id: acts ==> constrains acts (wlt acts B - B) (wlt acts B)";
by (forward_tac [wlt_leadsTo RS leadsTo_123] 1);
by (Clarify_tac 1);
by (subgoal_tac "Ba = wlt acts B" 1);
by (blast_tac (claset() addDs [leadsTo_eq_subset_wlt]) 2);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [wlt_increasing, Un_absorb2]) 1);
qed "wlt_constrains_wlt";


(*** Completion: Binary and General Finite versions ***)

Goal "[| leadsTo acts A A';  stable acts A';   \
\      leadsTo acts B B';  stable acts B';  id: acts |] \
\   ==> leadsTo acts (A Int B) (A' Int B')";
by (subgoal_tac "stable acts (wlt acts B')" 1);
by (asm_full_simp_tac (simpset() addsimps [stable_def]) 2);
by (EVERY [etac (constrains_Un RS constrains_weaken) 2,
	   etac wlt_constrains_wlt 2,
	   fast_tac (claset() addEs [wlt_increasing RSN (2,rev_subsetD)]) 3,
	   Blast_tac 2]);
by (subgoal_tac "leadsTo acts (A Int wlt acts B') (A' Int wlt acts B')" 1);
by (blast_tac (claset() addIs [psp_stable]) 2);
by (subgoal_tac "leadsTo acts (A' Int wlt acts B') (A' Int B')" 1);
by (blast_tac (claset() addIs [wlt_leadsTo, psp_stable2]) 2);
by (subgoal_tac "leadsTo acts (A Int B) (A Int wlt acts B')" 1);
by (blast_tac (claset() addIs [leadsTo_subset RS subsetD, 
			       subset_imp_leadsTo]) 2);
(*Blast_tac gives PROOF FAILED*)
by (best_tac (claset() addIs [leadsTo_Trans]) 1);
qed "stable_completion";


Goal "[| finite I;  id: acts |]                     \
\   ==> (ALL i:I. leadsTo acts (A i) (A' i)) -->  \
\       (ALL i:I. stable acts (A' i)) -->         \
\       leadsTo acts (INT i:I. A i) (INT i:I. A' i)";
by (etac finite_induct 1);
by (Asm_simp_tac 1);
by (asm_simp_tac 
    (simpset() addsimps [stable_completion, stable_def, 
			 ball_constrains_INT]) 1);
qed_spec_mp "finite_stable_completion";


Goal "[| W = wlt acts (B' Un C);     \
\      leadsTo acts A (A' Un C);  constrains acts A' (A' Un C);   \
\      leadsTo acts B (B' Un C);  constrains acts B' (B' Un C);   \
\      id: acts |] \
\   ==> leadsTo acts (A Int B) ((A' Int B') Un C)";
by (subgoal_tac "constrains acts (W-C) (W Un B' Un C)" 1);
by (blast_tac (claset() addIs [[asm_rl, wlt_constrains_wlt] 
			       MRS constrains_Un RS constrains_weaken]) 2);
by (subgoal_tac "constrains acts (W-C) W" 1);
by (asm_full_simp_tac 
    (simpset() addsimps [wlt_increasing, Un_assoc, Un_absorb2]) 2);
by (subgoal_tac "leadsTo acts (A Int W - C) (A' Int W Un C)" 1);
by (simp_tac (simpset() addsimps [Int_Diff]) 2);
by (blast_tac (claset() addIs [wlt_leadsTo, psp RS leadsTo_weaken_R]) 2);
by (subgoal_tac "leadsTo acts (A' Int W Un C) (A' Int B' Un C)" 1);
by (blast_tac (claset() addIs [wlt_leadsTo, leadsTo_Un_Un, 
                               psp2 RS leadsTo_weaken_R, 
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


Goal "[| finite I;  id: acts |] \
\   ==> (ALL i:I. leadsTo acts (A i) (A' i Un C)) -->  \
\       (ALL i:I. constrains acts (A' i) (A' i Un C)) --> \
\       leadsTo acts (INT i:I. A i) ((INT i:I. A' i) Un C)";
by (etac finite_induct 1);
by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (dtac ball_constrains_INT 1);
by (asm_full_simp_tac (simpset() addsimps [completion]) 1); 
qed "finite_completion";

