(*  Title:      HOL/UNITY/ELT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

leadsTo strengthened with a specification of the allowable sets transient parts
*)

(** Standard leadsTo rules **)

Goalw [leadsETo_def]
     "[| F: A ensures B;  A-B: insert {} CC |] ==> F : A leadsTo[CC] B";
by (blast_tac (claset() addIs [elt.Basis]) 1);
qed "leadsETo_Basis";

Goalw [leadsETo_def]
     "[| F : A leadsTo[CC] B;  F : B leadsTo[CC] C |] ==> F : A leadsTo[CC] C";
by (blast_tac (claset() addIs [elt.Trans]) 1);
qed "leadsETo_Trans";


(*Useful with cancellation, disjunction*)
Goal "F : A leadsTo[CC] (A' Un A') ==> F : A leadsTo[CC] A'";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "leadsETo_Un_duplicate";

Goal "F : A leadsTo[CC] (A' Un C Un C) ==> F : A leadsTo[CC] (A' Un C)";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "leadsETo_Un_duplicate2";

(*The Union introduction rule as we should have liked to state it*)
val prems = Goalw [leadsETo_def]
    "(!!A. A : S ==> F : A leadsTo[CC] B) ==> F : (Union S) leadsTo[CC] B";
by (blast_tac (claset() addIs [elt.Union] addDs prems) 1);
qed "leadsETo_Union";

val prems = Goal
    "(!!i. i : I ==> F : (A i) leadsTo[CC] B) \
\    ==> F : (UN i:I. A i) leadsTo[CC] B";
by (stac (Union_image_eq RS sym) 1);
by (blast_tac (claset() addIs leadsETo_Union::prems) 1);
qed "leadsETo_UN";

(*The INDUCTION rule as we should have liked to state it*)
val major::prems = Goalw [leadsETo_def]
  "[| F : za leadsTo[CC] zb;  \
\     !!A B. [| F : A ensures B;  A-B : insert {} CC |] ==> P A B; \
\     !!A B C. [| F : A leadsTo[CC] B; P A B; F : B leadsTo[CC] C; P B C |] \
\              ==> P A C; \
\     !!B S. ALL A:S. F : A leadsTo[CC] B & P A B ==> P (Union S) B \
\  |] ==> P za zb";
by (rtac (major RS CollectD RS elt.induct) 1);
by (REPEAT (blast_tac (claset() addIs prems) 1));
qed "leadsETo_induct";


(** New facts involving leadsETo **)

Goal "CC' <= CC ==> (A leadsTo[CC'] B) <= (A leadsTo[CC] B)";
by Safe_tac;
by (etac leadsETo_induct 1);
by (blast_tac (claset() addIs [leadsETo_Union]) 3);
by (blast_tac (claset() addIs [leadsETo_Trans]) 2);
by (blast_tac (claset() addIs [leadsETo_Basis]) 1);
qed "leadsETo_mono";

Goal "[| F : A leadsTo[CC] B;  F : B leadsTo[DD] C |] \
\     ==> F : A leadsTo[CC Un DD] C";
by (blast_tac (claset() addIs [impOfSubs leadsETo_mono, leadsETo_Trans]) 1);
qed "leadsETo_Trans_Un";

val prems = Goalw [leadsETo_def]
 "(!!A. A : S ==> F : (A Int C) leadsTo[CC] B) ==> F : (Union S Int C) leadsTo[CC] B";
by (simp_tac (HOL_ss addsimps [Int_Union_Union]) 1);
by (blast_tac (claset() addIs [elt.Union] addDs prems) 1);
qed "leadsETo_Union_Int";

(*Binary union introduction rule*)
Goal "[| F : A leadsTo[CC] C; F : B leadsTo[CC] C |] ==> F : (A Un B) leadsTo[CC] C";
by (stac Un_eq_Union 1);
by (blast_tac (claset() addIs [leadsETo_Union]) 1);
qed "leadsETo_Un";

val prems = 
Goal "(!!x. x : A ==> F : {x} leadsTo[CC] B) ==> F : A leadsTo[CC] B";
by (stac (UN_singleton RS sym) 1 THEN rtac leadsETo_UN 1);
by (blast_tac (claset() addIs prems) 1);
qed "single_leadsETo_I";


Goal "A<=B ==> F : A leadsTo[CC] B";
by (asm_simp_tac (simpset() addsimps [subset_imp_ensures RS leadsETo_Basis,
				      Diff_eq_empty_iff RS iffD2]) 1);
qed "subset_imp_leadsETo";

bind_thm ("empty_leadsETo", empty_subsetI RS subset_imp_leadsETo);
Addsimps [empty_leadsETo];



(** Weakening laws **)

Goal "[| F : A leadsTo[CC] A';  A'<=B' |] ==> F : A leadsTo[CC] B'";
by (blast_tac (claset() addIs [subset_imp_leadsETo, leadsETo_Trans]) 1);
qed "leadsETo_weaken_R";

Goal "[| F : A leadsTo[CC] A'; B<=A |] ==> F : B leadsTo[CC] A'";
by (blast_tac (claset() addIs [leadsETo_Trans, subset_imp_leadsETo]) 1);
qed_spec_mp "leadsETo_weaken_L";

(*Distributes over binary unions*)
Goal "F : (A Un B) leadsTo[CC] C  =  \
\     (F : A leadsTo[CC] C & F : B leadsTo[CC] C)";
by (blast_tac (claset() addIs [leadsETo_Un, leadsETo_weaken_L]) 1);
qed "leadsETo_Un_distrib";

Goal "F : (UN i:I. A i) leadsTo[CC] B  =  \
\     (ALL i : I. F : (A i) leadsTo[CC] B)";
by (blast_tac (claset() addIs [leadsETo_UN, leadsETo_weaken_L]) 1);
qed "leadsETo_UN_distrib";

Goal "F : (Union S) leadsTo[CC] B  =  (ALL A : S. F : A leadsTo[CC] B)";
by (blast_tac (claset() addIs [leadsETo_Union, leadsETo_weaken_L]) 1);
qed "leadsETo_Union_distrib";

Goal "[| F : A leadsTo[CC'] A'; B<=A; A'<=B';  CC' <= CC |] \
\     ==> F : B leadsTo[CC] B'";
by (dtac (impOfSubs leadsETo_mono) 1);
by (assume_tac 1);
by (blast_tac (claset() delrules [subsetCE]
			addIs [leadsETo_weaken_R, leadsETo_weaken_L,
			       leadsETo_Trans]) 1);
qed "leadsETo_weaken";

Goal "[| F : A leadsTo[CC] A';  CC <= givenBy v |] \
\     ==> F : A leadsTo[givenBy v] A'";
by (blast_tac (claset() addIs [empty_mem_givenBy, leadsETo_weaken]) 1);
qed "leadsETo_givenBy";


(*Set difference*)
Goal "[| F : (A-B) leadsTo[CC] C; F : B leadsTo[CC] C |] \
\     ==> F : A leadsTo[CC] C";
by (blast_tac (claset() addIs [leadsETo_Un, leadsETo_weaken]) 1);
qed "leadsETo_Diff";


(** Meta or object quantifier ???
    see ball_constrains_UN in UNITY.ML***)

val prems = goal thy
   "[| !! i. i:I ==> F : (A i) leadsTo[CC] (A' i) |] \
\   ==> F : (UN i:I. A i) leadsTo[CC] (UN i:I. A' i)";
by (simp_tac (HOL_ss addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs [leadsETo_Union, leadsETo_weaken_R] 
                        addIs prems) 1);
qed "leadsETo_UN_UN";

(*Binary union version*)
Goal "[| F : A leadsTo[CC] A';  F : B leadsTo[CC] B' |] \
\     ==> F : (A Un B) leadsTo[CC] (A' Un B')";
by (blast_tac (claset() addIs [leadsETo_Un, 
			       leadsETo_weaken_R]) 1);
qed "leadsETo_Un_Un";


(** The cancellation law **)

Goal "[| F : A leadsTo[CC] (A' Un B); F : B leadsTo[CC] B' |] \
\     ==> F : A leadsTo[CC] (A' Un B')";
by (blast_tac (claset() addIs [leadsETo_Un_Un, 
			       subset_imp_leadsETo, leadsETo_Trans]) 1);
qed "leadsETo_cancel2";

Goal "[| F : A leadsTo[CC] (A' Un B); F : (B-A') leadsTo[CC] B' |] \
\     ==> F : A leadsTo[CC] (A' Un B')";
by (rtac leadsETo_cancel2 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "leadsETo_cancel_Diff2";

Goal "[| F : A leadsTo[CC] (B Un A'); F : B leadsTo[CC] B' |] \
\   ==> F : A leadsTo[CC] (B' Un A')";
by (asm_full_simp_tac (simpset() addsimps [Un_commute]) 1);
by (blast_tac (claset() addSIs [leadsETo_cancel2]) 1);
qed "leadsETo_cancel1";

Goal "[| F : A leadsTo[CC] (B Un A'); F : (B-A') leadsTo[CC] B' |] \
\   ==> F : A leadsTo[CC] (B' Un A')";
by (rtac leadsETo_cancel1 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "leadsETo_cancel_Diff1";


(** The impossibility law **)

Goal "F : A leadsTo[CC] B ==> B={} --> A={}";
by (etac leadsETo_induct 1);
by (ALLGOALS Asm_simp_tac);
by (rewrite_goals_tac [ensures_def, constrains_def, transient_def]);
by (Blast_tac 1);
val lemma = result() RS mp;

Goal "F : A leadsTo[CC] {} ==> A={}";
by (blast_tac (claset() addSIs [lemma]) 1);
qed "leadsETo_empty";


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction"*)
Goalw [stable_def]
   "[| F : A leadsTo[CC] A';  F : stable B;  ALL C:CC. C Int B : CC |] \
\   ==> F : (A Int B) leadsTo[CC] (A' Int B)";
by (etac leadsETo_induct 1);
by (blast_tac (claset() addIs [leadsETo_Union_Int]) 3);
by (blast_tac (claset() addIs [leadsETo_Trans]) 2);
by (rtac leadsETo_Basis 1);
by (force_tac (claset(),
	       simpset() addsimps [Diff_Int_distrib2 RS sym]) 2);
by (asm_full_simp_tac
    (simpset() addsimps [ensures_def, 
			 Diff_Int_distrib2 RS sym, Int_Un_distrib2 RS sym]) 1);
by (blast_tac (claset() addIs [transient_strengthen, constrains_Int]) 1);
qed "e_psp_stable";

Goal "[| F : A leadsTo[CC] A'; F : stable B;  ALL C:CC. C Int B : CC |] \
\     ==> F : (B Int A) leadsTo[CC] (B Int A')";
by (asm_simp_tac (simpset() addsimps e_psp_stable::Int_ac) 1);
qed "e_psp_stable2";

Goal "[| F : A leadsTo[CC] A'; F : B co B';  \
\        ALL C:CC. C Int B Int B' : CC |] \
\     ==> F : (A Int B') leadsTo[CC] ((A' Int B) Un (B' - B))";
by (etac leadsETo_induct 1);
by (blast_tac (claset() addIs [leadsETo_Union_Int]) 3);
(*Transitivity case has a delicate argument involving "cancellation"*)
by (rtac leadsETo_Un_duplicate2 2);
by (etac leadsETo_cancel_Diff1 2);
by (asm_full_simp_tac (simpset() addsimps [Int_Diff, Diff_triv]) 2);
by (blast_tac (claset() addIs [leadsETo_weaken_L] 
                        addDs [constrains_imp_subset]) 2);
(*Basis case*)
by (rtac leadsETo_Basis 1);
by (blast_tac (claset() addIs [psp_ensures]) 1);
by (subgoal_tac "A Int B' - (Ba Int B Un (B' - B)) = (A - Ba) Int B Int B'" 1);
by Auto_tac;
qed "e_psp";

Goal "[| F : A leadsTo[CC] A'; F : B co B';  \
\        ALL C:CC. C Int B Int B' : CC |] \
\     ==> F : (B' Int A) leadsTo[CC] ((B Int A') Un (B' - B))";
by (asm_full_simp_tac (simpset() addsimps e_psp::Int_ac) 1);
qed "e_psp2";


(*** Special properties involving the parameter [CC] ***)

(*??IS THIS NEEDED?? or is it just an example of what's provable??*)
Goal "[| F: (A leadsTo[givenBy v] B);  G : preserves v;  \
\        F Join G : stable C |] \
\     ==> F Join G : ((C Int A) leadsTo[(%D. C Int D) `` givenBy v] B)";
by (etac leadsETo_induct 1);
by (stac Int_Union 3);
by (blast_tac (claset() addIs [leadsETo_UN]) 3);
by (blast_tac (claset() addIs [e_psp_stable2 RS leadsETo_weaken_L, 
			       leadsETo_Trans]) 2);
by (rtac leadsETo_Basis 1);
by (auto_tac (claset(),
	      simpset() addsimps [Diff_eq_empty_iff RS iffD2,
				  Int_Diff, ensures_def,
				  givenBy_eq_Collect, Join_stable,
				  Join_constrains, Join_transient]));
by (blast_tac (claset() addIs [transient_strengthen]) 3);
by (ALLGOALS (dres_inst_tac [("P1","P")] (impOfSubs preserves_subset_stable)));
by (rewtac stable_def);
by (blast_tac (claset() addSEs [equalityE]
			addIs [constrains_Int RS constrains_weaken]) 2);
by (blast_tac (claset() addSEs [equalityE]
			addIs [constrains_Int RS constrains_weaken]) 1);
qed "gen_leadsETo_imp_Join_leadsETo";

(*useful??*)
Goal "[| F Join G : (A leadsTo[CC] B);  ALL C:CC. G : stable C |] \
\     ==> F: (A leadsTo[CC] B)";
by (etac leadsETo_induct 1);
by (blast_tac (claset() addIs [leadsETo_Union]) 3);
by (blast_tac (claset() addIs [leadsETo_Trans]) 2);
by (rtac leadsETo_Basis 1);
by (case_tac "A <= B" 1);
by (etac subset_imp_ensures 1);
by (auto_tac (claset() addIs [constrains_weaken],
              simpset() addsimps [stable_def, ensures_def, 
                                  Join_constrains, Join_transient]));
by (REPEAT (thin_tac "?F : ?A co ?B" 1));
by (etac transientE 1);
by (rewtac constrains_def);
by (blast_tac (claset() addSDs [bspec]) 1);
qed "Join_leadsETo_stable_imp_leadsETo";

(**** Relationship with traditional "leadsTo", strong & weak ****)

(** strong **)

Goal "(A leadsTo[CC] B) <= (A leadsTo B)";
by Safe_tac;
by (etac leadsETo_induct 1);
by (blast_tac (claset() addIs [leadsTo_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (blast_tac (claset() addIs [leadsTo_Basis]) 1);
qed "leadsETo_subset_leadsTo";

Goal "(A leadsTo[UNIV] B) = (A leadsTo B)";
by Safe_tac;
by (etac (impOfSubs leadsETo_subset_leadsTo) 1);
(*right-to-left case*)
by (etac leadsTo_induct 1);
by (blast_tac (claset() addIs [leadsETo_Union]) 3);
by (blast_tac (claset() addIs [leadsETo_Trans]) 2);
by (blast_tac (claset() addIs [leadsETo_Basis]) 1);
qed "leadsETo_UNIV_eq_leadsTo";

(**** weak ****)

Goalw [LeadsETo_def]
     "A LeadsTo[CC] B = \
\       {F. F : (reachable F Int A) leadsTo[(%C. reachable F Int C) `` CC] \
\       (reachable F Int B)}";
by (blast_tac (claset() addDs [e_psp_stable2] addIs [leadsETo_weaken]) 1);
qed "LeadsETo_eq_leadsETo";

(*** Introduction rules: Basis, Trans, Union ***)

Goal "[| F : A LeadsTo[CC] B;  F : B LeadsTo[CC] C |] \
\     ==> F : A LeadsTo[CC] C";
by (asm_full_simp_tac (simpset() addsimps [LeadsETo_eq_leadsETo]) 1);
by (blast_tac (claset() addIs [leadsETo_Trans]) 1);
qed "LeadsETo_Trans";

val prems = Goalw [LeadsETo_def]
     "(!!A. A : S ==> F : A LeadsTo[CC] B) ==> F : (Union S) LeadsTo[CC] B";
by (Simp_tac 1);
by (stac Int_Union 1);
by (blast_tac (claset() addIs [leadsETo_UN] addDs prems) 1);
qed "LeadsETo_Union";

val prems = 
Goal "(!!i. i : I ==> F : (A i) LeadsTo[CC] B) \
\     ==> F : (UN i:I. A i) LeadsTo[CC] B";
by (simp_tac (HOL_ss addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs (LeadsETo_Union::prems)) 1);
qed "LeadsETo_UN";

(*Binary union introduction rule*)
Goal "[| F : A LeadsTo[CC] C; F : B LeadsTo[CC] C |] \
\     ==> F : (A Un B) LeadsTo[CC] C";
by (stac Un_eq_Union 1);
by (blast_tac (claset() addIs [LeadsETo_Union]) 1);
qed "LeadsETo_Un";

(*Lets us look at the starting state*)
val prems = 
Goal "(!!s. s : A ==> F : {s} LeadsTo[CC] B) ==> F : A LeadsTo[CC] B";
by (stac (UN_singleton RS sym) 1 THEN rtac LeadsETo_UN 1);
by (blast_tac (claset() addIs prems) 1);
qed "single_LeadsETo_I";

Goal "A <= B ==> F : A LeadsTo[CC] B";
by (simp_tac (simpset() addsimps [LeadsETo_def]) 1);
by (blast_tac (claset() addIs [subset_imp_leadsETo]) 1);
qed "subset_imp_LeadsETo";

bind_thm ("empty_LeadsETo", empty_subsetI RS subset_imp_LeadsETo);

Goal "[| F : A LeadsTo[CC] A';  A' <= B' |] ==> F : A LeadsTo[CC] B'";
by (full_simp_tac (simpset() addsimps [LeadsETo_def]) 1);
by (blast_tac (claset() addIs [leadsETo_weaken_R]) 1);
qed_spec_mp "LeadsETo_weaken_R";

Goal "[| F : A LeadsTo[CC] A';  B <= A |] ==> F : B LeadsTo[CC] A'";
by (full_simp_tac (simpset() addsimps [LeadsETo_def]) 1);
by (blast_tac (claset() addIs [leadsETo_weaken_L]) 1);
qed_spec_mp "LeadsETo_weaken_L";

Goal "[| F : A LeadsTo[CC'] A';   \
\        B <= A;  A' <= B';  CC' <= CC |] \
\     ==> F : B LeadsTo[CC] B'";
by (full_simp_tac (simpset() addsimps [LeadsETo_def]) 1);
by (blast_tac (claset() addIs [leadsETo_weaken]) 1);
qed "LeadsETo_weaken";

Goalw [LeadsETo_def, LeadsTo_def] "(A LeadsTo[CC] B) <= (A LeadsTo B)";
by (blast_tac (claset() addIs [impOfSubs leadsETo_subset_leadsTo]) 1);
qed "LeadsETo_subset_LeadsTo";

(*Postcondition can be strengthened to (reachable F Int B) *)
Goal "F : A ensures B ==> F : (reachable F Int A) ensures B";
by (rtac (stable_ensures_Int RS ensures_weaken_R) 1);
by Auto_tac;
qed "reachable_ensures";

Goal "F : A leadsTo B ==> F : (reachable F Int A) leadsTo[Pow(reachable F)] B";
by (etac leadsTo_induct 1);
by (stac Int_Union 3);
by (blast_tac (claset() addIs [leadsETo_UN]) 3);
by (blast_tac (claset() addDs [e_psp_stable2] 
                        addIs [leadsETo_Trans, leadsETo_weaken_L]) 2);
by (blast_tac (claset() addIs [reachable_ensures, leadsETo_Basis]) 1);
val lemma = result();

Goal "(A LeadsTo[UNIV] B) = (A LeadsTo B)";
by Safe_tac;
by (etac (impOfSubs LeadsETo_subset_LeadsTo) 1);
(*right-to-left case*)
by (rewrite_goals_tac [LeadsETo_def, LeadsTo_def]);
by (fast_tac (claset() addEs [lemma RS leadsETo_weaken]) 1);
qed "LeadsETo_UNIV_eq_LeadsTo";


(**** EXTEND/PROJECT PROPERTIES ****)

Open_locale "Extend";

Goal "F : A leadsTo[CC] B \
\     ==> extend h F : (extend_set h A) leadsTo[extend_set h `` CC] \
\                      (extend_set h B)";
by (etac leadsETo_induct 1);
by (asm_simp_tac (simpset() addsimps [leadsETo_UN, extend_set_Union]) 3);
by (blast_tac (claset() addIs [leadsETo_Trans]) 2);
by (force_tac (claset() addIs [leadsETo_Basis, subset_imp_ensures],
	       simpset() addsimps [extend_ensures,
				   extend_set_Diff_distrib RS sym]) 1);
qed "leadsETo_imp_extend_leadsETo";



(*NOT USED, but analogous to preserves_project_transient_empty in Project.ML*)
Goal "[| G : preserves (v o f);  project h C G : transient D;  \
\        D : givenBy v |] ==> D={}";
by (rtac stable_transient_empty 1);
by (assume_tac 2);
(*If addIs then PROOF FAILED at depth 2*)
by (blast_tac (claset() addSIs [preserves_givenBy_imp_stable,
				project_preserves_I]) 1);
result();


(*This version's stronger in the "ensures" precondition
  BUT there's no ensures_weaken_L*)
Goal "[| project h C G ~: transient (project_set h C Int (A-B)) | \
\          project_set h C Int (A - B) = {};  \
\        extend h F Join G : stable C;  \
\        F Join project h C G : (project_set h C Int A) ensures B |] \
\     ==> extend h F Join G : (C Int extend_set h A) ensures (extend_set h B)";
by (stac (Int_extend_set_lemma RS sym) 1);
by (rtac Join_project_ensures 1);
by (auto_tac (claset(), simpset() addsimps [Int_Diff]));
qed "Join_project_ensures_strong";

Goal "[| extend h F Join G : stable C;  \
\        F Join project h C G : (project_set h C Int A) leadsTo[(%D. project_set h C Int D)``givenBy v] B;  \
\        G : preserves (v o f) |] \
\     ==> extend h F Join G : \
\           (C Int extend_set h (project_set h C Int A)) \
\           leadsTo[(%D. C Int extend_set h D)``givenBy v]  (extend_set h B)";
by (etac leadsETo_induct 1);
by (asm_simp_tac (simpset() delsimps UN_simps
		  addsimps [Int_UN_distrib, leadsETo_UN, extend_set_Union]) 3);
by (blast_tac (claset() addIs [e_psp_stable2 RS leadsETo_weaken_L, 
			       leadsETo_Trans]) 2);
by Auto_tac;
by (force_tac (claset() addIs [leadsETo_Basis, subset_imp_ensures],
	       simpset()) 1);
by (rtac leadsETo_Basis 1);
by (asm_simp_tac (simpset() addsimps [Int_Diff, Int_extend_set_lemma,
				      extend_set_Diff_distrib RS sym]) 2);
by (rtac Join_project_ensures_strong 1);
by (auto_tac (claset() addDs [preserves_o_project_transient_empty]
		       addIs [project_stable_project_set], 
	      simpset() addsimps [Int_left_absorb, Join_stable]));
by (asm_simp_tac
    (simpset() addsimps [stable_ensures_Int RS ensures_weaken_R,
			 Int_lower2, project_stable_project_set,
			 Join_stable, extend_stable_project_set]) 1);
val lemma = result();

Goal "[| extend h F Join G : stable C;  \
\        F Join project h C G : \
\            (project_set h C Int A) \
\            leadsTo[(%D. project_set h C Int D)``givenBy v] B;  \
\        G : preserves (v o f) |] \
\     ==> extend h F Join G : (C Int extend_set h A) \
\           leadsTo[(%D. C Int extend_set h D)``givenBy v] (extend_set h B)";
by (rtac (lemma RS leadsETo_weaken) 1);
by (auto_tac (claset(), 
	      simpset() addsimps [split_extended_all]));
qed "project_leadsETo_D_lemma";

Goal "[| F Join project h UNIV G : A leadsTo[givenBy v] B;  \
\        G : preserves (v o f) |]  \
\     ==> extend h F Join G : (extend_set h A) \
\           leadsTo[givenBy (v o f)] (extend_set h B)";
by (rtac (make_elim project_leadsETo_D_lemma) 1);
by (stac stable_UNIV 1);
by Auto_tac;
by (etac leadsETo_givenBy 1);
by (rtac (givenBy_o_eq_extend_set RS equalityD2) 1);
qed "project_leadsETo_D";

Goal "[| F Join project h (reachable (extend h F Join G)) G \
\            : A LeadsTo[givenBy v] B;  \
\        G : preserves (v o f) |] \
\     ==> extend h F Join G : \
\           (extend_set h A) LeadsTo[givenBy (v o f)] (extend_set h B)";
by (rtac (make_elim (subset_refl RS stable_reachable RS 
		     project_leadsETo_D_lemma)) 1);
by (auto_tac (claset(), 
	      simpset() addsimps [LeadsETo_def]));
by (asm_full_simp_tac 
    (simpset() addsimps [project_set_reachable_extend_eq RS sym]) 1);
by (etac (impOfSubs leadsETo_mono) 1);
by (blast_tac (claset() addIs [extend_set_givenBy_I]) 1);
qed "project_LeadsETo_D";

Goalw [extending_def]
     "extending (v o f) (%G. UNIV) h F \
\               (extend_set h A leadsTo[givenBy (v o f)] extend_set h B) \
\               (A leadsTo[givenBy v] B)";
by (auto_tac (claset(), simpset() addsimps [project_leadsETo_D]));
qed "extending_leadsETo";


Goalw [extending_def]
     "extending (v o f) (%G. reachable (extend h F Join G)) h F \
\               (extend_set h A LeadsTo[givenBy (v o f)] extend_set h B) \
\               (A LeadsTo[givenBy v]  B)";
by (blast_tac (claset() addIs [project_LeadsETo_D]) 1);
qed "extending_LeadsETo";


(*** leadsETo in the precondition ***)

(*Lemma for the Trans case*)
Goal "[| extend h F Join G : stable C;    \
\        F Join project h C G    \
\          : project_set h C Int project_set h A leadsTo project_set h B |] \
\     ==> F Join project h C G    \
\           : project_set h C Int project_set h A leadsTo    \
\             project_set h C Int project_set h B";
by (rtac (psp_stable2 RS leadsTo_weaken_L) 1);
by (auto_tac (claset(),
	      simpset() addsimps [project_stable_project_set, Join_stable, 
				  extend_stable_project_set]));
val lemma = result();

Goal "[| extend h F Join G : stable C;  \
\        extend h F Join G : \
\          (C Int A) leadsTo[(%D. C Int D)``givenBy f]  B |]  \
\ ==> F Join project h C G  \
\   : (project_set h C Int project_set h (C Int A)) leadsTo (project_set h B)";
by (etac leadsETo_induct 1);
by (asm_simp_tac (HOL_ss addsimps [Int_UN_distrib, project_set_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_UN]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans, lemma]) 2);
by (asm_full_simp_tac 
    (simpset() addsimps [givenBy_eq_extend_set, Join_stable]) 1);
by (rtac leadsTo_Basis 1);
by (blast_tac (claset() addIs [leadsTo_Basis,
			       ensures_extend_set_imp_project_ensures]) 1);

qed "project_leadsETo_I_lemma";

Goal "extend h F Join G : (extend_set h A) leadsTo[givenBy f] (extend_set h B)\
\     ==> F Join project h UNIV G : A leadsTo B";
by (rtac (project_leadsETo_I_lemma RS leadsTo_weaken) 1);
by Auto_tac;
qed "project_leadsETo_I";

Goal "extend h F Join G : (extend_set h A) LeadsTo[givenBy f] (extend_set h B)\
\     ==> F Join project h (reachable (extend h F Join G)) G  \
\          : A LeadsTo B";
by (full_simp_tac (simpset() addsimps [LeadsTo_def, LeadsETo_def]) 1);
by (rtac (project_leadsETo_I_lemma RS leadsTo_weaken) 1);
by (auto_tac (claset(), 
	      simpset() addsimps [project_set_reachable_extend_eq RS sym]));
qed "project_LeadsETo_I";

Goalw [projecting_def]
     "projecting (%G. UNIV) h F \
\                (extend_set h A leadsTo[givenBy f] extend_set h B) \
\                (A leadsTo B)";
by (force_tac (claset() addDs [project_leadsETo_I], simpset()) 1);
qed "projecting_leadsTo";

Goalw [projecting_def]
     "projecting (%G. reachable (extend h F Join G)) h F \
\                (extend_set h A LeadsTo[givenBy f] extend_set h B) \
\                (A LeadsTo B)";
by (force_tac (claset() addDs [project_LeadsETo_I], simpset()) 1);
qed "projecting_LeadsTo";

Close_locale "Extend";


