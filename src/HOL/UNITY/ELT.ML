(*  Title:      HOL/UNITY/ELT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

leadsTo strengthened with a specification of the allowable sets transient parts
*)

Goalw [givenBy_def] "(givenBy v) = {A. ALL x:A. ALL y. v x = v y --> y: A}";
by Safe_tac;
by (res_inst_tac [("x", "v `` ?u")] image_eqI 2);
by Auto_tac;
qed "givenBy_eq_all";

Goal "givenBy v = {A. EX P. A = {s. P(v s)}}";
by (simp_tac (simpset() addsimps [givenBy_eq_all]) 1);
by Safe_tac;
by (res_inst_tac [("x", "%n. EX s. v s = n & s : ?A")] exI 1);
by (Blast_tac 1);
by Auto_tac;
qed "givenBy_eq_Collect";

val prems =
Goal "(!!x y. [|  x:A;  v x = v y |] ==> y: A) ==> A: givenBy v";
by (stac givenBy_eq_all 1);
by (blast_tac (claset() addIs prems) 1);
qed "givenByI";

Goalw [givenBy_def] "[| A: givenBy v;  x:A;  v x = v y |] ==> y: A";
by Auto_tac;
qed "givenByD";

Goal "{} : givenBy v";
by (blast_tac (claset() addSIs [givenByI]) 1);
qed "empty_mem_givenBy";

AddIffs [empty_mem_givenBy];

Goal "A: givenBy v ==> EX P. A = {s. P(v s)}";
by (res_inst_tac [("x", "%n. EX s. v s = n & s : A")] exI 1);
by (full_simp_tac (simpset() addsimps [givenBy_eq_all]) 1);
by (Blast_tac 1);
qed "givenBy_imp_eq_Collect";

Goalw [givenBy_def] "EX P. A = {s. P(v s)} ==> A: givenBy v";
by (Best_tac 1);
qed "eq_Collect_imp_givenBy";

Goal "givenBy v = {A. EX P. A = {s. P(v s)}}";
by (blast_tac (claset() addIs [eq_Collect_imp_givenBy,
			       givenBy_imp_eq_Collect]) 1);
qed "givenBy_eq_eq_Collect";

Goal "(funPair f g) o h = funPair (f o h) (g o h)";
by (simp_tac (simpset() addsimps [funPair_def, o_def]) 1);
qed "funPair_o_distrib";


(** Standard leadsTo rules **)

Goalw [leadsETo_def] "[| F: A ensures B;  A-B: CC |] ==> F : A leadsTo[CC] B";
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
\     !!A B. [| F : A ensures B;  A-B : CC |] ==> P A B; \
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


Goal "[| A<=B;  {}:CC |]  ==> F : A leadsTo[CC] B";
by (asm_simp_tac (simpset() addsimps [subset_imp_ensures RS leadsETo_Basis,
				      Diff_eq_empty_iff RS iffD2]) 1);
qed "subset_imp_leadsETo";

bind_thm ("empty_leadsETo", empty_subsetI RS subset_imp_leadsETo);
Addsimps [empty_leadsETo];


(** Weakening laws all require {}:CC **)

Goal "[| F : A leadsTo[CC] A';  A'<=B';  {}:CC |] ==> F : A leadsTo[CC] B'";
by (blast_tac (claset() addIs [subset_imp_leadsETo, leadsETo_Trans]) 1);
qed "leadsETo_weaken_R";

Goal "[| F : A leadsTo[CC] A'; B<=A;  {}:CC |] ==> F : B leadsTo[CC] A'";
by (blast_tac (claset() addIs [leadsETo_Trans, subset_imp_leadsETo]) 1);
qed_spec_mp "leadsETo_weaken_L";

(*Distributes over binary unions*)
Goal "{} : CC ==> \
\ F : (A Un B) leadsTo[CC] C  =  (F : A leadsTo[CC] C & F : B leadsTo[CC] C)";
by (blast_tac (claset() addIs [leadsETo_Un, leadsETo_weaken_L]) 1);
qed "leadsETo_Un_distrib";

Goal "{} : CC ==> \
\   F : (UN i:I. A i) leadsTo[CC] B  =  (ALL i : I. F : (A i) leadsTo[CC] B)";
by (blast_tac (claset() addIs [leadsETo_UN, leadsETo_weaken_L]) 1);
qed "leadsETo_UN_distrib";

Goal "{} : CC \
\     ==> F : (Union S) leadsTo[CC] B  =  (ALL A : S. F : A leadsTo[CC] B)";
by (blast_tac (claset() addIs [leadsETo_Union, leadsETo_weaken_L]) 1);
qed "leadsETo_Union_distrib";

Goal "[| F : A leadsTo[CC'] A'; B<=A; A'<=B';  CC' <= CC;  {}:CC |] \
\     ==> F : B leadsTo[CC] B'";
by (dtac (impOfSubs leadsETo_mono) 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [leadsETo_weaken_R, leadsETo_weaken_L,
			       leadsETo_Trans]) 1);
qed "leadsETo_weaken";

Goal "[| F : A leadsTo[CC] A';  CC <= givenBy v |] \
\     ==> F : A leadsTo[givenBy v] A'";
by (blast_tac (claset() addIs [empty_mem_givenBy, leadsETo_weaken]) 1);
qed "leadsETo_givenBy";


(*Set difference*)
Goal "[| F : (A-B) leadsTo[CC] C; F : B leadsTo[CC] C;  {}:CC |] \
\     ==> F : A leadsTo[CC] C";
by (blast_tac (claset() addIs [leadsETo_Un, leadsETo_weaken]) 1);
qed "leadsETo_Diff";


(** Meta or object quantifier ???
    see ball_constrains_UN in UNITY.ML***)

val prems = goal thy
   "[| !! i. i:I ==> F : (A i) leadsTo[CC] (A' i);  {}:CC |] \
\   ==> F : (UN i:I. A i) leadsTo[CC] (UN i:I. A' i)";
by (simp_tac (HOL_ss addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs [leadsETo_Union, leadsETo_weaken_R] 
                        addIs prems) 1);
qed "leadsETo_UN_UN";

(*Binary union version*)
Goal "[| F : A leadsTo[CC] A';  F : B leadsTo[CC] B';  {}:CC |] \
\     ==> F : (A Un B) leadsTo[CC] (A' Un B')";
by (blast_tac (claset() addIs [leadsETo_Un, 
			       leadsETo_weaken_R]) 1);
qed "leadsETo_Un_Un";


(** The cancellation law **)

Goal "[| F : A leadsTo[CC] (A' Un B); F : B leadsTo[CC] B';  {}:CC |] \
\     ==> F : A leadsTo[CC] (A' Un B')";
by (blast_tac (claset() addIs [leadsETo_Un_Un, 
			       subset_imp_leadsETo, leadsETo_Trans]) 1);
qed "leadsETo_cancel2";

Goal "[| F : A leadsTo[CC] (A' Un B); F : (B-A') leadsTo[CC] B';  {}:CC |] \
\     ==> F : A leadsTo[CC] (A' Un B')";
by (rtac leadsETo_cancel2 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "leadsETo_cancel_Diff2";

Goal "[| F : A leadsTo[CC] (B Un A'); F : B leadsTo[CC] B';  {}:CC |] \
\   ==> F : A leadsTo[CC] (B' Un A')";
by (asm_full_simp_tac (simpset() addsimps [Un_commute]) 1);
by (blast_tac (claset() addSIs [leadsETo_cancel2]) 1);
qed "leadsETo_cancel1";

Goal "[| F : A leadsTo[CC] (B Un A'); F : (B-A') leadsTo[CC] B';  {}:CC |] \
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
by (asm_full_simp_tac
    (simpset() addsimps [ensures_def, 
			 Diff_Int_distrib2 RS sym, Int_Un_distrib2 RS sym]) 1);
by (asm_simp_tac (simpset() addsimps [Diff_Int_distrib2 RS sym]) 2);
by (blast_tac (claset() addIs [transient_strengthen, constrains_Int]) 1);
qed "e_psp_stable";

Goal "[| F : A leadsTo[CC] A'; F : stable B;  ALL C:CC. C Int B : CC |] \
\     ==> F : (B Int A) leadsTo[CC] (B Int A')";
by (asm_simp_tac (simpset() addsimps e_psp_stable::Int_ac) 1);
qed "e_psp_stable2";

Goal "[| F : A leadsTo[CC] A'; F : B co B';  \
\        ALL C:CC. C Int B Int B' : CC;  {}:CC |] \
\     ==> F : (A Int B') leadsTo[CC] ((A' Int B) Un (B' - B))";
by (etac leadsETo_induct 1);
by (blast_tac (claset() addIs [leadsETo_Union_Int]) 3);
(*Transitivity case has a delicate argument involving "cancellation"*)
by (rtac leadsETo_Un_duplicate2 2);
by (etac leadsETo_cancel_Diff1 2);
by (assume_tac 3);
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
\        ALL C:CC. C Int B Int B' : CC;  {}:CC |] \
\     ==> F : (B' Int A) leadsTo[CC] ((B Int A') Un (B' - B))";
by (asm_full_simp_tac (simpset() addsimps e_psp::Int_ac) 1);
qed "e_psp2";


(*** Special properties involving the parameter [CC] ***)

(*??IS THIS NEEDED?? or is it just an example of what's provable??*)
Goal "[| F: (A leadsTo[givenBy v] B);  F Join G : v localTo[C] F;  \
\        F Join G : stable C |] \
\     ==> F Join G : ((C Int A) leadsTo[(%D. C Int D) `` givenBy v] B)";
by (etac leadsETo_induct 1);
by (stac Int_Union 3);
by (blast_tac (claset() addIs [leadsETo_UN]) 3);
by (blast_tac (claset() addIs [e_psp_stable2 RS leadsETo_weaken_L, 
			       leadsETo_Trans]) 2);
by (rtac leadsETo_Basis 1);
by (auto_tac (claset(),
	      simpset() addsimps [Int_Diff, ensures_def, stable_def,
				  givenBy_eq_Collect,
				  Join_localTo, 
				  Join_constrains, Join_transient]));
by (blast_tac (claset() addIs [transient_strengthen]) 3);
by (blast_tac (claset() addDs [constrains_localTo_constrains]
			addIs [constrains_Int RS constrains_weaken]) 2);
by (blast_tac (claset() addIs [constrains_Int RS constrains_weaken]) 1);
qed "gen_leadsETo_localTo_imp_Join_leadsETo";

(*USED???
  Could replace this proof by instantiation of the one above with C=UNIV*)
Goal "[| F: (A leadsTo[givenBy v] B);  F Join G : v localTo[UNIV] F |] \
\     ==> F Join G : (A leadsTo[givenBy v] B)";
by (etac leadsETo_induct 1);
by (blast_tac (claset() addIs [leadsETo_Union]) 3);
by (blast_tac (claset() addIs [leadsETo_Trans]) 2);
by (rtac leadsETo_Basis 1);
by (auto_tac (claset(),
	      simpset() addsimps [ensures_def, givenBy_eq_Collect,
				  Join_localTo, 
				  Join_constrains, Join_transient]));
by (force_tac (claset() addDs [constrains_localTo_constrains], simpset()) 1);
qed "leadsETo_localTo_imp_Join_leadsETo";

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



(**** EXTEND/PROJECT PROPERTIES ****)

Open_locale "Extend";

(*Here h and f are locale constants*)
Goal "extend_set h `` (givenBy v) <= (givenBy (v o f))";
by (simp_tac (simpset() addsimps [givenBy_eq_all]) 1);
by (Blast_tac 1);
qed "extend_set_givenBy_subset";

Goal "D : givenBy v ==> extend_set h D : givenBy (v o f)";
by (full_simp_tac (simpset() addsimps [givenBy_eq_all]) 1);
by (Blast_tac 1);
qed "extend_set_givenBy_I";


Goal "F : A leadsTo[CC] B \
\     ==> extend h F : (extend_set h A) leadsTo[extend_set h `` CC] \
\                      (extend_set h B)";
by (etac leadsETo_induct 1);
by (asm_simp_tac (simpset() addsimps [leadsETo_UN, extend_set_Union]) 3);
by (blast_tac (claset() addIs [leadsETo_Trans]) 2);
by (asm_simp_tac (simpset() addsimps [leadsETo_Basis, extend_ensures,
				      extend_set_Diff_distrib RS sym]) 1);
qed "leadsETo_imp_extend_leadsETo";

(*NOW OBSOLETE: SEE BELOW !! Generalizes the version proved in Project.ML*)
Goalw [LOCALTO_def, transient_def, Diff_def]
     "[| G : (v o f) localTo[C] extend h F;  project h C G : transient D;  \
\        D : givenBy v |]    \
\     ==> F : transient D";
by (auto_tac (claset(), 
	      simpset() addsimps [givenBy_eq_Collect]));
by (case_tac "Restrict C act : Restrict C ``extend_act h `` Acts F" 1);
by Auto_tac; 
by (rtac bexI 1);
by (assume_tac 2);
by (Blast_tac 1);
by (case_tac "{s. P (v s)} = {}" 1);
by (auto_tac (claset(),
	      simpset() addsimps [stable_def, constrains_def]));
by (subgoal_tac
    "ALL z. Restrict C act ^^ {s. v (f s) = z} <= {s. v (f s) = z}" 1);
by (blast_tac (claset() addSDs [bspec]) 2);
by (thin_tac "ALL z. ?P z" 1);
by (subgoal_tac "project_act h (Restrict C act) ^^ {s. P (v s)} <= {s. P (v s)}" 1);
by (Clarify_tac 2);
by (asm_full_simp_tac (simpset() addsimps [project_act_def]) 2);
by (force_tac (claset() addSDs [spec, ImageI RSN (2, subsetD)], simpset()) 2);
by (blast_tac (claset() addSDs [subsetD]) 1);
qed "localTo_project_transient_transient";


Goal "A Int extend_set h ((project_set h A) Int B) = A Int extend_set h B";
by (auto_tac (claset() addIs [project_set_I], 
	      simpset()));
qed "Int_extend_set_lemma";

Goal "G : C co B ==> project h C G : project_set h C co project_set h B";
by (full_simp_tac (simpset() addsimps [constrains_def, project_def, 
				       project_act_def, project_set_def]) 1);
by (Blast_tac 1);
qed "project_constrains_project_set";

Goal "G : stable C ==> project h C G : stable (project_set h C)";
by (asm_full_simp_tac (simpset() addsimps [stable_def, 
					   project_constrains_project_set]) 1);
qed "project_stable_project_set";

(*!! Generalizes the version proved in Project.ML*)
Goalw [LOCALTO_def, transient_def, Diff_def]
     "[| G : (v o f) localTo[C] extend h F;  \
\        project h C G : transient (C' Int D);  \
\        project h C G : stable C';  \
\        D : givenBy v;  (C' Int D) <= D |]    \
\     ==> F : transient (C' Int D)";
by (auto_tac (claset(), 
	      simpset() addsimps [givenBy_eq_Collect]));
by (case_tac "Restrict C act : Restrict C ``extend_act h `` Acts F" 1);
by Auto_tac; 
by (rtac bexI 1);
by (assume_tac 2);
by (Blast_tac 1);
by (case_tac "(C' Int {s. P (v s)}) = {}" 1);
by (auto_tac (claset(),
	      simpset() addsimps [stable_def, constrains_def]));
by (subgoal_tac
    "ALL z. Restrict C act ^^ {s. v (f s) = z} <= {s. v (f s) = z}" 1);
by (blast_tac (claset() addSDs [bspec]) 2);
by (thin_tac "ALL z. ?P z" 1);
by (subgoal_tac "project_act h (Restrict C act) ^^ (C' Int {s. P (v s)}) <= (C' Int {s. P (v s)})" 1);
by (Clarify_tac 2);
by (asm_full_simp_tac (simpset() addsimps [project_act_def]) 2);
by (thin_tac "(C' Int {s. P (v s)}) <= Domain ?A" 2);
by (thin_tac "?A <= -C' Un ?B" 2);
by (rtac conjI 2);
by (force_tac (claset() addSDs [spec, ImageI RSN (2, subsetD)], simpset()) 3);
by (Blast_tac 2);
by (blast_tac (claset() addSDs [subsetD]) 1);
qed "localTo_project_transient_transient";

(*This version's stronger in the "ensures" precondition
  BUT there's no ensures_weaken_L*)
Goal "[| project h C G : transient (project_set h C Int (A-B)) --> \
\          F : transient (project_set h C Int (A-B));  \
\        extend h F Join G : stable C;  \
\        F Join project h C G : (project_set h C Int A) ensures B |] \
\     ==> extend h F Join G : (C Int extend_set h A) ensures (extend_set h B)";
by (stac (Int_extend_set_lemma RS sym) 1);
by (rtac Join_project_ensures 1);
by (auto_tac (claset(), simpset() addsimps [Int_Diff]));
qed "Join_project_ensures_strong";

Goal "[| extend h F Join G : stable C;  \
\        F Join project h C G : (project_set h C Int A) leadsTo[(%D. project_set h C Int D)``givenBy v] B; \
\        G : (v o f) localTo[C] extend h F |] \
\     ==> extend h F Join G : \
\           (C Int extend_set h (project_set h C Int A)) \
\           leadsTo[(%D. C Int extend_set h D)``givenBy v]  (extend_set h B)";
by (etac leadsETo_induct 1);
by (asm_simp_tac (simpset() delsimps UN_simps
		  addsimps [Int_UN_distrib, leadsETo_UN, extend_set_Union]) 3);
by (blast_tac (claset() addIs [e_psp_stable2 RS leadsETo_weaken_L, 
			       leadsETo_Trans]) 2);
by (Clarify_tac 1);
by (rtac leadsETo_Basis 1);
by (etac rev_image_eqI 2);
by (asm_simp_tac (simpset() addsimps [Int_Diff, Int_extend_set_lemma,
				      extend_set_Diff_distrib RS sym]) 2);
by (rtac Join_project_ensures_strong 1);
by (auto_tac (claset() addIs [localTo_project_transient_transient,
			      project_stable_project_set], 
	      simpset() addsimps [Int_left_absorb, Join_stable]));
by (asm_simp_tac
    (simpset() addsimps [stable_ensures_Int RS ensures_weaken_R,
			 Int_lower2, project_stable_project_set,
			 Join_stable, extend_stable_project_set]) 1);
val lemma = result();

Goal "[| extend h F Join G : stable C;  \
\        F Join project h C G : (project_set h C Int A) leadsTo[(%D. project_set h C Int D)``givenBy v] B; \
\        G : (v o f) localTo[C] extend h F |] \
\     ==> extend h F Join G : (C Int extend_set h A) \
\           leadsTo[(%D. C Int extend_set h D)``givenBy v] (extend_set h B)";
by (rtac (lemma RS leadsETo_weaken) 1);
by (auto_tac (claset() addIs [project_set_I], simpset()));
qed "project_leadsETo_lemma";

Goal "[| F Join project h UNIV G : A leadsTo[givenBy v] B;    \
\        G : (v o f) localTo[UNIV] extend h F |]  \
\     ==> extend h F Join G : (extend_set h A) \
\           leadsTo[givenBy (v o f)] (extend_set h B)";
by (rtac (make_elim project_leadsETo_lemma) 1);
by Auto_tac;
by (etac leadsETo_givenBy 1);
by (rtac extend_set_givenBy_subset 1);
qed "project_leadsETo_D";

Goal "[| F Join project h (reachable (extend h F Join G)) G \
\            : A LeadsTo[givenBy v] B;    \
\        G : (v o f) LocalTo extend h F |] \
\     ==> extend h F Join G : \
\           (extend_set h A) LeadsTo[givenBy (v o f)] (extend_set h B)";
by (rtac (make_elim (subset_refl RS stable_reachable RS 
		     project_leadsETo_lemma)) 1);
by (auto_tac (claset(), 
	      simpset() addsimps [LeadsETo_def, LocalTo_def]));
by (asm_full_simp_tac 
    (simpset() addsimps [project_set_reachable_extend_eq RS sym]) 1);
by (etac (impOfSubs leadsETo_mono) 1);
by (blast_tac (claset() addIs [extend_set_givenBy_I]) 1);
qed "project_LeadsETo_D";

Goalw [extending_def]
     "extending (%G. UNIV) h F \
\               ((v o f) localTo[UNIV] extend h F) \
\               (extend_set h A leadsTo[givenBy (v o f)] extend_set h B) \
\               (A leadsTo[givenBy v] B)";
by (auto_tac (claset(), 
	      simpset() addsimps [project_leadsETo_D, Join_localTo]));
qed "extending_leadsETo";


Goalw [extending_def]
     "extending (%G. reachable (extend h F Join G)) h F \
\               ((v o f) LocalTo extend h F) \
\               (extend_set h A LeadsTo[givenBy (v o f)] extend_set h B) \
\               (A LeadsTo[givenBy v]  B)";

by (force_tac (claset() addIs [project_LeadsETo_D],
	       simpset()addsimps [LocalTo_def, Join_assoc RS sym, 
				  Join_localTo]) 1);
qed "extending_LeadsETo";


Close_locale "Extend";


