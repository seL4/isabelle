(*  Title:      HOL/UNITY/WFair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak Fairness versions of transient, ensures, leadsTo.

From Misra, "A Logic for Concurrent Programming", 1994
*)


overload_1st_set "WFair.transient";
overload_1st_set "WFair.ensures";
overload_1st_set "WFair.op leadsTo";

(*** transient ***)

Goalw [stable_def, constrains_def, transient_def]
    "[| F : stable A; F : transient A |] ==> A = {}";
by (Blast_tac 1);
qed "stable_transient_empty";

Goalw [transient_def]
    "[| F : transient A; B<=A |] ==> F : transient B";
by (Clarify_tac 1);
by (blast_tac (claset() addSIs [rev_bexI]) 1);
qed "transient_strengthen";

Goalw [transient_def]
    "[| act: Acts F;  A <= Domain act;  act^^A <= -A |] ==> F : transient A";
by (Blast_tac 1);
qed "transientI";

val major::prems = 
Goalw [transient_def]
    "[| F : transient A;  \
\       !!act. [| act: Acts F;  A <= Domain act;  act^^A <= -A |] ==> P |] \
\    ==> P";
by (rtac (major RS CollectD RS bexE) 1);
by (blast_tac (claset() addIs prems) 1);
qed "transientE";

Goalw [transient_def] "transient UNIV = {}";
by Auto_tac;
qed "transient_UNIV";

Goalw [transient_def] "transient {} = UNIV";
by Auto_tac;
qed "transient_empty";
Addsimps [transient_UNIV, transient_empty];


(*** ensures ***)

Goalw [ensures_def]
    "[| F : (A-B) co (A Un B); F : transient (A-B) |] ==> F : A ensures B";
by (Blast_tac 1);
qed "ensuresI";

Goalw [ensures_def]
    "F : A ensures B ==> F : (A-B) co (A Un B) & F : transient (A-B)";
by (Blast_tac 1);
qed "ensuresD";

Goalw [ensures_def]
    "[| F : A ensures A'; A'<=B' |] ==> F : A ensures B'";
by (blast_tac (claset() addIs [constrains_weaken, transient_strengthen]) 1);
qed "ensures_weaken_R";

(*The L-version (precondition strengthening) fails, but we have this*)
Goalw [ensures_def]
    "[| F : stable C;  F : A ensures B |]   \
\   ==> F : (C Int A) ensures (C Int B)";
by (auto_tac (claset(),
	      simpset() addsimps [ensures_def,
				  Int_Un_distrib RS sym,
				  Diff_Int_distrib RS sym]));
by (blast_tac (claset() addIs [transient_strengthen]) 2);
by (blast_tac (claset() addIs [stable_constrains_Int, constrains_weaken]) 1);
qed "stable_ensures_Int";

(*NEVER USED*)
Goal "[| F : stable A;  F : transient C;  A <= B Un C |] ==> F : A ensures B";
by (asm_full_simp_tac (simpset() addsimps [ensures_def, stable_def]) 1);
by (blast_tac (claset() addIs [constrains_weaken, transient_strengthen]) 1);
qed "stable_transient_ensures";


(*** leadsTo ***)

Goalw [leadsTo_def] "F : A ensures B ==> F : A leadsTo B";
by (blast_tac (claset() addIs [leads.Basis]) 1);
qed "leadsTo_Basis";

Goalw [leadsTo_def]
     "[| F : A leadsTo B;  F : B leadsTo C |] ==> F : A leadsTo C";
by (blast_tac (claset() addIs [leads.Trans]) 1);
qed "leadsTo_Trans";

Goal "F : transient A ==> F : A leadsTo (-A)";
by (asm_simp_tac 
    (simpset() addsimps [leadsTo_Basis, ensuresI, Compl_partition]) 1);
qed "transient_imp_leadsTo";

(*Useful with cancellation, disjunction*)
Goal "F : A leadsTo (A' Un A') ==> F : A leadsTo A'";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "leadsTo_Un_duplicate";

Goal "F : A leadsTo (A' Un C Un C) ==> F : A leadsTo (A' Un C)";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "leadsTo_Un_duplicate2";

(*The Union introduction rule as we should have liked to state it*)
val prems = Goalw [leadsTo_def]
    "(!!A. A : S ==> F : A leadsTo B) ==> F : (Union S) leadsTo B";
by (blast_tac (claset() addIs [leads.Union] addDs prems) 1);
qed "leadsTo_Union";

val prems = Goalw [leadsTo_def]
 "(!!A. A : S ==> F : (A Int C) leadsTo B) ==> F : (Union S Int C) leadsTo B";
by (simp_tac (HOL_ss addsimps [Int_Union_Union]) 1);
by (blast_tac (claset() addIs [leads.Union] addDs prems) 1);
qed "leadsTo_Union_Int";

val prems = Goal
    "(!!i. i : I ==> F : (A i) leadsTo B) ==> F : (UN i:I. A i) leadsTo B";
by (stac (Union_image_eq RS sym) 1);
by (blast_tac (claset() addIs leadsTo_Union::prems) 1);
qed "leadsTo_UN";

(*Binary union introduction rule*)
Goal "[| F : A leadsTo C; F : B leadsTo C |] ==> F : (A Un B) leadsTo C";
by (stac Un_eq_Union 1);
by (blast_tac (claset() addIs [leadsTo_Union]) 1);
qed "leadsTo_Un";

val prems = 
Goal "(!!x. x : A ==> F : {x} leadsTo B) ==> F : A leadsTo B";
by (stac (UN_singleton RS sym) 1 THEN rtac leadsTo_UN 1);
by (blast_tac (claset() addIs prems) 1);
qed "single_leadsTo_I";


(*The INDUCTION rule as we should have liked to state it*)
val major::prems = Goalw [leadsTo_def]
  "[| F : za leadsTo zb;  \
\     !!A B. F : A ensures B ==> P A B; \
\     !!A B C. [| F : A leadsTo B; P A B; F : B leadsTo C; P B C |] \
\              ==> P A C; \
\     !!B S. ALL A:S. F : A leadsTo B & P A B ==> P (Union S) B \
\  |] ==> P za zb";
by (rtac (major RS CollectD RS leads.induct) 1);
by (REPEAT (blast_tac (claset() addIs prems) 1));
qed "leadsTo_induct";


Goal "A<=B ==> F : A ensures B";
by (rewrite_goals_tac [ensures_def, constrains_def, transient_def]);
by (Blast_tac 1);
qed "subset_imp_ensures";

bind_thm ("subset_imp_leadsTo", subset_imp_ensures RS leadsTo_Basis);

bind_thm ("empty_leadsTo", empty_subsetI RS subset_imp_leadsTo);
Addsimps [empty_leadsTo];

bind_thm ("leadsTo_UNIV", subset_UNIV RS subset_imp_leadsTo);
Addsimps [leadsTo_UNIV];


Goal "[| F : A leadsTo A'; A'<=B' |] ==> F : A leadsTo B'";
by (blast_tac (claset() addIs [subset_imp_leadsTo, leadsTo_Trans]) 1);
qed "leadsTo_weaken_R";

Goal "[| F : A leadsTo A'; B<=A |] ==> F : B leadsTo A'";
by (blast_tac (claset() addIs [leadsTo_Trans, subset_imp_leadsTo]) 1);
qed_spec_mp "leadsTo_weaken_L";

(*Distributes over binary unions*)
Goal "F : (A Un B) leadsTo C  =  (F : A leadsTo C & F : B leadsTo C)";
by (blast_tac (claset() addIs [leadsTo_Un, leadsTo_weaken_L]) 1);
qed "leadsTo_Un_distrib";

Goal "F : (UN i:I. A i) leadsTo B  =  (ALL i : I. F : (A i) leadsTo B)";
by (blast_tac (claset() addIs [leadsTo_UN, leadsTo_weaken_L]) 1);
qed "leadsTo_UN_distrib";

Goal "F : (Union S) leadsTo B  =  (ALL A : S. F : A leadsTo B)";
by (blast_tac (claset() addIs [leadsTo_Union, leadsTo_weaken_L]) 1);
qed "leadsTo_Union_distrib";


Goal "[| F : A leadsTo A'; B<=A; A'<=B' |] ==> F : B leadsTo B'";
by (blast_tac (claset() addIs [leadsTo_weaken_R, leadsTo_weaken_L,
			       leadsTo_Trans]) 1);
qed "leadsTo_weaken";


(*Set difference: maybe combine with leadsTo_weaken_L??*)
Goal "[| F : (A-B) leadsTo C; F : B leadsTo C |]   ==> F : A leadsTo C";
by (blast_tac (claset() addIs [leadsTo_Un, leadsTo_weaken]) 1);
qed "leadsTo_Diff";


(** Meta or object quantifier ???
    see ball_constrains_UN in UNITY.ML***)

val prems = goal thy
   "(!! i. i:I ==> F : (A i) leadsTo (A' i)) \
\   ==> F : (UN i:I. A i) leadsTo (UN i:I. A' i)";
by (simp_tac (HOL_ss addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs [leadsTo_Union, leadsTo_weaken_R] 
                        addIs prems) 1);
qed "leadsTo_UN_UN";

(*Binary union version*)
Goal "[| F : A leadsTo A'; F : B leadsTo B' |] \
\     ==> F : (A Un B) leadsTo (A' Un B')";
by (blast_tac (claset() addIs [leadsTo_Un, 
			       leadsTo_weaken_R]) 1);
qed "leadsTo_Un_Un";


(** The cancellation law **)

Goal "[| F : A leadsTo (A' Un B); F : B leadsTo B' |] \
\     ==> F : A leadsTo (A' Un B')";
by (blast_tac (claset() addIs [leadsTo_Un_Un, 
			       subset_imp_leadsTo, leadsTo_Trans]) 1);
qed "leadsTo_cancel2";

Goal "[| F : A leadsTo (A' Un B); F : (B-A') leadsTo B' |] \
\     ==> F : A leadsTo (A' Un B')";
by (rtac leadsTo_cancel2 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "leadsTo_cancel_Diff2";

Goal "[| F : A leadsTo (B Un A'); F : B leadsTo B' |] \
\   ==> F : A leadsTo (B' Un A')";
by (asm_full_simp_tac (simpset() addsimps [Un_commute]) 1);
by (blast_tac (claset() addSIs [leadsTo_cancel2]) 1);
qed "leadsTo_cancel1";

Goal "[| F : A leadsTo (B Un A'); F : (B-A') leadsTo B' |] \
\   ==> F : A leadsTo (B' Un A')";
by (rtac leadsTo_cancel1 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "leadsTo_cancel_Diff1";



(** The impossibility law **)

Goal "F : A leadsTo B ==> B={} --> A={}";
by (etac leadsTo_induct 1);
by (ALLGOALS Asm_simp_tac);
by (rewrite_goals_tac [ensures_def, constrains_def, transient_def]);
by (Blast_tac 1);
val lemma = result() RS mp;

Goal "F : A leadsTo {} ==> A={}";
by (blast_tac (claset() addSIs [lemma]) 1);
qed "leadsTo_empty";


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction"*)
Goalw [stable_def]
   "[| F : A leadsTo A'; F : stable B |] \
\   ==> F : (A Int B) leadsTo (A' Int B)";
by (etac leadsTo_induct 1);
by (blast_tac (claset() addIs [leadsTo_Union_Int]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (rtac leadsTo_Basis 1);
by (asm_full_simp_tac
    (simpset() addsimps [ensures_def, 
			 Diff_Int_distrib2 RS sym, Int_Un_distrib2 RS sym]) 1);
by (blast_tac (claset() addIs [transient_strengthen, constrains_Int]) 1);
qed "psp_stable";

Goal
   "[| F : A leadsTo A'; F : stable B |] ==> F : (B Int A) leadsTo (B Int A')";
by (asm_simp_tac (simpset() addsimps psp_stable::Int_ac) 1);
qed "psp_stable2";

Goalw [ensures_def, constrains_def]
   "[| F : A ensures A'; F : B co B' |] \
\   ==> F : (A Int B') ensures ((A' Int B) Un (B' - B))";
by (Clarify_tac 1);  (*speeds up the proof*)
by (blast_tac (claset() addIs [transient_strengthen]) 1);
qed "psp_ensures";

Goal "[| F : A leadsTo A'; F : B co B' |] \
\     ==> F : (A Int B') leadsTo ((A' Int B) Un (B' - B))";
by (etac leadsTo_induct 1);
by (blast_tac (claset() addIs [leadsTo_Union_Int]) 3);
(*Transitivity case has a delicate argument involving "cancellation"*)
by (rtac leadsTo_Un_duplicate2 2);
by (etac leadsTo_cancel_Diff1 2);
by (asm_full_simp_tac (simpset() addsimps [Int_Diff, Diff_triv]) 2);
by (blast_tac (claset() addIs [leadsTo_weaken_L] 
                        addDs [constrains_imp_subset]) 2);
(*Basis case*)
by (blast_tac (claset() addIs [leadsTo_Basis, psp_ensures]) 1);
qed "psp";

Goal "[| F : A leadsTo A'; F : B co B' |] \
\   ==> F : (B' Int A) leadsTo ((B Int A') Un (B' - B))";
by (asm_simp_tac (simpset() addsimps psp::Int_ac) 1);
qed "psp2";


Goalw [unless_def]
   "[| F : A leadsTo A';  F : B unless B' |] \
\   ==> F : (A Int B) leadsTo ((A' Int B) Un B')";
by (dtac psp 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [leadsTo_weaken]) 1);
qed "psp_unless";


(*** Proving the induction rules ***)

(** The most general rule: r is any wf relation; f is any variant function **)

Goal "[| wf r;     \
\        ALL m. F : (A Int f-``{m}) leadsTo                     \
\                   ((A Int f-``(r^-1 ^^ {m})) Un B) |] \
\     ==> F : (A Int f-``{m}) leadsTo B";
by (eres_inst_tac [("a","m")] wf_induct 1);
by (subgoal_tac "F : (A Int (f -`` (r^-1 ^^ {x}))) leadsTo B" 1);
by (stac vimage_eq_UN 2);
by (asm_simp_tac (HOL_ss addsimps (UN_simps RL [sym])) 2);
by (blast_tac (claset() addIs [leadsTo_UN]) 2);
by (blast_tac (claset() addIs [leadsTo_cancel1, leadsTo_Un_duplicate]) 1);
val lemma = result();


(** Meta or object quantifier ????? **)
Goal "[| wf r;     \
\        ALL m. F : (A Int f-``{m}) leadsTo                     \
\                   ((A Int f-``(r^-1 ^^ {m})) Un B) |] \
\     ==> F : A leadsTo B";
by (res_inst_tac [("t", "A")] subst 1);
by (rtac leadsTo_UN 2);
by (etac lemma 2);
by (REPEAT (assume_tac 2));
by (Fast_tac 1);    (*Blast_tac: Function unknown's argument not a parameter*)
qed "leadsTo_wf_induct";


Goal "[| wf r;     \
\        ALL m:I. F : (A Int f-``{m}) leadsTo                   \
\                     ((A Int f-``(r^-1 ^^ {m})) Un B) |] \
\     ==> F : A leadsTo ((A - (f-``I)) Un B)";
by (etac leadsTo_wf_induct 1);
by Safe_tac;
by (case_tac "m:I" 1);
by (blast_tac (claset() addIs [leadsTo_weaken]) 1);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
qed "bounded_induct";


(*Alternative proof is via the lemma F : (A Int f-``(lessThan m)) leadsTo B*)
Goal "[| ALL m. F : (A Int f-``{m}) leadsTo                     \
\                   ((A Int f-``(lessThan m)) Un B) |] \
\     ==> F : A leadsTo B";
by (rtac (wf_less_than RS leadsTo_wf_induct) 1);
by (Asm_simp_tac 1);
qed "lessThan_induct";

Goal "[| ALL m:(greaterThan l).    \
\           F : (A Int f-``{m}) leadsTo ((A Int f-``(lessThan m)) Un B) |] \
\     ==> F : A leadsTo ((A Int (f-``(atMost l))) Un B)";
by (simp_tac (HOL_ss addsimps [Diff_eq RS sym, vimage_Compl, 
			       Compl_greaterThan RS sym]) 1);
by (rtac (wf_less_than RS bounded_induct) 1);
by (Asm_simp_tac 1);
qed "lessThan_bounded_induct";

Goal "[| ALL m:(lessThan l).    \
\           F : (A Int f-``{m}) leadsTo ((A Int f-``(greaterThan m)) Un B) |] \
\     ==> F : A leadsTo ((A Int (f-``(atLeast l))) Un B)";
by (res_inst_tac [("f","f"),("f1", "%k. l - k")]
    (wf_less_than RS wf_inv_image RS leadsTo_wf_induct) 1);
by (simp_tac (simpset() addsimps [inv_image_def, Image_singleton]) 1);
by (Clarify_tac 1);
by (case_tac "m<l" 1);
by (blast_tac (claset() addIs [not_leE, subset_imp_leadsTo]) 2);
by (blast_tac (claset() addIs [leadsTo_weaken_R, diff_less_mono2]) 1);
qed "greaterThan_bounded_induct";


(*** wlt ****)

(*Misra's property W3*)
Goalw [wlt_def] "F : (wlt F B) leadsTo B";
by (blast_tac (claset() addSIs [leadsTo_Union]) 1);
qed "wlt_leadsTo";

Goalw [wlt_def] "F : A leadsTo B ==> A <= wlt F B";
by (blast_tac (claset() addSIs [leadsTo_Union]) 1);
qed "leadsTo_subset";

(*Misra's property W2*)
Goal "F : A leadsTo B = (A <= wlt F B)";
by (blast_tac (claset() addSIs [leadsTo_subset, 
				wlt_leadsTo RS leadsTo_weaken_L]) 1);
qed "leadsTo_eq_subset_wlt";

(*Misra's property W4*)
Goal "B <= wlt F B";
by (asm_simp_tac (simpset() addsimps [leadsTo_eq_subset_wlt RS sym,
				      subset_imp_leadsTo]) 1);
qed "wlt_increasing";


(*Used in the Trans case below*)
Goalw [constrains_def]
   "[| B <= A2;  \
\      F : (A1 - B) co (A1 Un B); \
\      F : (A2 - C) co (A2 Un C) |] \
\   ==> F : (A1 Un A2 - C) co (A1 Un A2 Un C)";
by (Clarify_tac 1);
by (Blast_tac 1);
val lemma1 = result();


(*Lemma (1,2,3) of Misra's draft book, Chapter 4, "Progress"*)
Goal "F : A leadsTo A' ==> \
\     EX B. A<=B & F : B leadsTo A' & F : (B-A') co (B Un A')";
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
Goal "F : (wlt F B - B) co (wlt F B)";
by (cut_inst_tac [("F","F")] (wlt_leadsTo RS leadsTo_123) 1);
by (Clarify_tac 1);
by (subgoal_tac "Ba = wlt F B" 1);
by (blast_tac (claset() addDs [leadsTo_eq_subset_wlt RS iffD1]) 2);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [wlt_increasing, Un_absorb2]) 1);
qed "wlt_constrains_wlt";


(*** Completion: Binary and General Finite versions ***)

Goal "[| W = wlt F (B' Un C);     \
\      F : A leadsTo (A' Un C);  F : A' co (A' Un C);   \
\      F : B leadsTo (B' Un C);  F : B' co (B' Un C) |] \
\   ==> F : (A Int B) leadsTo ((A' Int B') Un C)";
by (subgoal_tac "F : (W-C) co (W Un B' Un C)" 1);
by (blast_tac (claset() addIs [[asm_rl, wlt_constrains_wlt] 
			       MRS constrains_Un RS constrains_weaken]) 2);
by (subgoal_tac "F : (W-C) co W" 1);
by (asm_full_simp_tac 
    (simpset() addsimps [wlt_increasing, Un_assoc, Un_absorb2]) 2);
by (subgoal_tac "F : (A Int W - C) leadsTo (A' Int W Un C)" 1);
by (blast_tac (claset() addIs [wlt_leadsTo, psp RS leadsTo_weaken]) 2);
(** LEVEL 6 **)
by (subgoal_tac "F : (A' Int W Un C) leadsTo (A' Int B' Un C)" 1);
by (rtac leadsTo_Un_duplicate2 2);
by (blast_tac (claset() addIs [leadsTo_Un_Un, 
                               wlt_leadsTo RS psp2 RS leadsTo_weaken, 
                               subset_refl RS subset_imp_leadsTo]) 2);
by (dtac leadsTo_Diff 1);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
by (subgoal_tac "A Int B <= A Int W" 1);
by (blast_tac (claset() addSDs [leadsTo_subset]
			addSIs [subset_refl RS Int_mono]) 2);
by (blast_tac (claset() addIs [leadsTo_Trans, subset_imp_leadsTo]) 1);
bind_thm("completion", refl RS result());


Goal "finite I ==> (ALL i:I. F : (A i) leadsTo (A' i Un C)) -->  \
\                  (ALL i:I. F : (A' i) co (A' i Un C)) --> \
\                  F : (INT i:I. A i) leadsTo ((INT i:I. A' i) Un C)";
by (etac finite_induct 1);
by Auto_tac;
by (dtac ball_constrains_INT 1);
by (asm_full_simp_tac (simpset() addsimps [completion]) 1); 
qed_spec_mp "finite_completion";


Goalw [stable_def]
     "[| F : A leadsTo A';  F : stable A';   \
\        F : B leadsTo B';  F : stable B' |] \
\   ==> F : (A Int B) leadsTo (A' Int B')";
by (res_inst_tac [("C1", "{}")] (completion RS leadsTo_weaken_R) 1);
by (REPEAT (Force_tac 1));
qed "stable_completion";

Goalw [stable_def]
     "[| finite I;  \
\        ALL i:I. F : (A i) leadsTo (A' i);  \
\        ALL i:I. F : stable (A' i) |]       \
\     ==> F : (INT i:I. A i) leadsTo (INT i:I. A' i)";
by (res_inst_tac [("C1", "{}")] (finite_completion RS leadsTo_weaken_R) 1);
by (REPEAT (Force_tac 1));
qed_spec_mp "finite_stable_completion";


