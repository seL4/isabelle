(*  Title:      HOL/UNITY/Project.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Projections of state sets (also of actions and programs)

Inheritance of GUARANTEES properties under extension
*)

Open_locale "Extend";

Goal "F : A co B ==> project h C (extend h F) : A co B";
by (auto_tac (claset(), 
      simpset() addsimps [extend_act_def, project_act_def, constrains_def]));
qed "project_extend_constrains_I";


(** Safety **)

(*used below to prove Join_project_ensures*)
Goal "[| G : stable C;  project h C G : A unless B |] \
\     ==> G : (C Int extend_set h A) unless (extend_set h B)";
by (asm_full_simp_tac
    (simpset() addsimps [unless_def, project_constrains]) 1);
by (blast_tac (claset() addDs [stable_constrains_Int]
			addIs [constrains_weaken]) 1);
qed_spec_mp "project_unless";

(*This form's useful with guarantees reasoning*)
Goal "(F Join project h C G : A co B)  =  \
\       (extend h F Join G : (C Int extend_set h A) co (extend_set h B) &  \
\        F : A co B)";
by (simp_tac (simpset() addsimps [Join_constrains, project_constrains]) 1);
by (blast_tac (claset() addIs [extend_constrains RS iffD2 RS constrains_weaken]
                        addDs [constrains_imp_subset]) 1);
qed "Join_project_constrains";

(*The condition is required to prove the left-to-right direction;
  could weaken it to G : (C Int extend_set h A) co C*)
Goalw [stable_def]
     "extend h F Join G : stable C \
\     ==> (F Join project h C G : stable A)  =  \
\         (extend h F Join G : stable (C Int extend_set h A) &  \
\          F : stable A)";
by (simp_tac (simpset() addsimps [Join_project_constrains]) 1);
by (blast_tac (claset() addIs [constrains_weaken] addDs [constrains_Int]) 1);
qed "Join_project_stable";

(*For using project_guarantees in particular cases*)
Goal "extend h F Join G : extend_set h A co extend_set h B \
\     ==> F Join project h C G : A co B";
by (asm_full_simp_tac
    (simpset() addsimps [project_constrains, Join_constrains, 
			 extend_constrains]) 1);
by (blast_tac (claset() addIs [constrains_weaken]
			addDs [constrains_imp_subset]) 1);
qed "project_constrains_I";

Goalw [increasing_def, stable_def]
     "extend h F Join G : increasing (func o f) \
\     ==> F Join project h C G : increasing func";
by (asm_full_simp_tac (simpset() addsimps [project_constrains_I, 
					   extend_set_eq_Collect]) 1);
qed "project_increasing_I";

Goal "(F Join project h UNIV G : increasing func)  =  \
\     (extend h F Join G : increasing (func o f))";
by (rtac iffI 1);
by (etac project_increasing_I 2);
by (asm_full_simp_tac 
    (simpset() addsimps [increasing_def, Join_project_stable]) 1);
by (auto_tac (claset(),
	      simpset() addsimps [Join_stable, extend_set_eq_Collect,
				  extend_stable RS iffD1]));
qed "Join_project_increasing";

(*The UNIV argument is essential*)
Goal "F Join project h UNIV G : A co B \
\     ==> extend h F Join G : extend_set h A co extend_set h B";
by (asm_full_simp_tac
    (simpset() addsimps [project_constrains, Join_constrains, 
			 extend_constrains]) 1);
qed "project_constrains_D";


(*** "projecting" and union/intersection (no converses) ***)

Goalw [projecting_def]
     "[| projecting C h F XA' XA;  projecting C h F XB' XB |] \
\     ==> projecting C h F (XA' Int XB') (XA Int XB)";
by (Blast_tac 1);
qed "projecting_Int";

Goalw [projecting_def]
     "[| projecting C h F XA' XA;  projecting C h F XB' XB |] \
\     ==> projecting C h F (XA' Un XB') (XA Un XB)";
by (Blast_tac 1);
qed "projecting_Un";

val [prem] = Goalw [projecting_def]
     "[| !!i. i:I ==> projecting C h F (X' i) (X i) |] \
\     ==> projecting C h F (INT i:I. X' i) (INT i:I. X i)";
by (blast_tac (claset() addDs [prem RS spec RS mp]) 1);
qed "projecting_INT";

val [prem] = Goalw [projecting_def]
     "[| !!i. i:I ==> projecting C h F (X' i) (X i) |] \
\     ==> projecting C h F (UN i:I. X' i) (UN i:I. X i)";
by (blast_tac (claset() addDs [prem RS spec RS mp]) 1);
qed "projecting_UN";

Goalw [projecting_def]
     "[| projecting C h F X' X;  U'<=X';  X<=U |] ==> projecting C h F U' U";
by Auto_tac;
qed "projecting_weaken";

Goalw [projecting_def]
     "[| projecting C h F X' X;  U'<=X' |] ==> projecting C h F U' X";
by Auto_tac;
qed "projecting_weaken_L";

Goalw [extending_def]
     "[| extending v C h F YA' YA;  extending v C h F YB' YB |] \
\     ==> extending v C h F (YA' Int YB') (YA Int YB)";
by (Blast_tac 1);
qed "extending_Int";

Goalw [extending_def]
     "[| extending v C h F YA' YA;  extending v C h F YB' YB |] \
\     ==> extending v C h F (YA' Un YB') (YA Un YB)";
by (Blast_tac 1);
qed "extending_Un";

val [prem] = Goalw [extending_def]
     "[| !!i. i:I ==> extending v C h F (Y' i) (Y i) |] \
\     ==> extending v C h F (INT i:I. Y' i) (INT i:I. Y i)";
by (blast_tac (claset() addDs [prem RS spec RS mp]) 1);
qed "extending_INT";

val [prem] = Goalw [extending_def]
     "[| !!i. i:I ==> extending v C h F (Y' i) (Y i) |] \
\     ==> extending v C h F (UN i:I. Y' i) (UN i:I. Y i)";
by (blast_tac (claset() addDs [prem RS spec RS mp]) 1);
qed "extending_UN";

Goalw [extending_def]
     "[| extending v C h F Y' Y;  Y'<=V';  V<=Y; \
\        preserves w <= preserves v |] \
\     ==> extending w C h F V' V";
by Auto_tac;
qed "extending_weaken";

Goalw [extending_def]
     "[| extending v C h F Y' Y;  Y'<=V' |] ==> extending v C h F V' Y";
by Auto_tac;
qed "extending_weaken_L";

Goal "projecting C h F X' UNIV";
by (simp_tac (simpset() addsimps [projecting_def]) 1);
qed "projecting_UNIV";

Goalw [projecting_def]
     "projecting C h F (extend_set h A co extend_set h B) (A co B)";
by (blast_tac (claset() addIs [project_constrains_I]) 1);
qed "projecting_constrains";

Goalw [stable_def]
     "projecting C h F (stable (extend_set h A)) (stable A)";
by (rtac projecting_constrains 1);
qed "projecting_stable";

Goalw [projecting_def]
     "projecting C h F (increasing (func o f)) (increasing func)";
by (blast_tac (claset() addIs [project_increasing_I]) 1);
qed "projecting_increasing";

Goal "extending v C h F UNIV Y";
by (simp_tac (simpset() addsimps [extending_def]) 1);
qed "extending_UNIV";

Goalw [extending_def]
     "extending v (%G. UNIV) h F (extend_set h A co extend_set h B) (A co B)";
by (blast_tac (claset() addIs [project_constrains_D]) 1);
qed "extending_constrains";

Goalw [stable_def]
     "extending v (%G. UNIV) h F (stable (extend_set h A)) (stable A)";
by (rtac extending_constrains 1);
qed "extending_stable";

Goalw [extending_def]
     "extending v (%G. UNIV) h F (increasing (func o f)) (increasing func)";
by (simp_tac (simpset() addsimps [Join_project_increasing]) 1);
qed "extending_increasing";


(** Reachability and project **)

Goal "[| reachable (extend h F Join G) <= C;  \
\        z : reachable (extend h F Join G) |] \
\     ==> f z : reachable (F Join project h C G)";
by (etac reachable.induct 1);
by (force_tac (claset() addSIs [reachable.Init],
	       simpset() addsimps [split_extended_all]) 1);
by Auto_tac;
by (force_tac (claset() addIs [project_act_I RSN (3,reachable.Acts)],
	       simpset()) 2);
by (res_inst_tac [("act","x")] reachable.Acts 1);
by Auto_tac;
by (etac extend_act_D 1);
qed "reachable_imp_reachable_project";

Goalw [Constrains_def]
     "F Join project h (reachable (extend h F Join G)) G : A Co B  \
\     ==> extend h F Join G : (extend_set h A) Co (extend_set h B)";
by (full_simp_tac (simpset() addsimps [Join_project_constrains]) 1);
by (Clarify_tac 1);
by (etac constrains_weaken 1);
by (auto_tac (claset() addIs [reachable_imp_reachable_project], simpset()));
qed "project_Constrains_D";

Goalw [Stable_def]
     "F Join project h (reachable (extend h F Join G)) G : Stable A  \
\     ==> extend h F Join G : Stable (extend_set h A)";
by (asm_simp_tac (simpset() addsimps [project_Constrains_D]) 1);
qed "project_Stable_D";

Goalw [Always_def]
     "F Join project h (reachable (extend h F Join G)) G : Always A  \
\     ==> extend h F Join G : Always (extend_set h A)";
by (force_tac (claset() addIs [reachable.Init],
               simpset() addsimps [project_Stable_D, split_extended_all]) 1);
qed "project_Always_D";

Goalw [Increasing_def]
     "F Join project h (reachable (extend h F Join G)) G : Increasing func  \
\     ==> extend h F Join G : Increasing (func o f)";
by Auto_tac;
by (stac (extend_set_eq_Collect RS sym) 1);
by (asm_simp_tac (simpset() addsimps [project_Stable_D]) 1); 
qed "project_Increasing_D";


(** Converse results for weak safety: benefits of the argument C *)

Goal "[| C <= reachable(extend h F Join G);   \
\        x : reachable (F Join project h C G) |] \
\     ==> EX y. h(x,y) : reachable (extend h F Join G)";
by (etac reachable.induct 1);
by (ALLGOALS Asm_full_simp_tac);
(*SLOW: 6.7s*)
by (force_tac (claset() delrules [Id_in_Acts]
		        addIs [reachable.Acts, extend_act_D],
	       simpset() addsimps [project_act_def]) 2);
by (force_tac (claset() addIs [reachable.Init],
	       simpset()) 1);
qed "reachable_project_imp_reachable";

Goal "project_set h (reachable (extend h F Join G)) = \
\     reachable (F Join project h (reachable (extend h F Join G)) G)";
by (auto_tac (claset() addDs [subset_refl RS reachable_imp_reachable_project,
			      subset_refl RS reachable_project_imp_reachable], 
	      simpset()));
qed "project_set_reachable_extend_eq";

Goal "reachable (extend h F Join G) <= C  \
\     ==> reachable (extend h F Join G) <= \
\         extend_set h (reachable (F Join project h C G))";
by (auto_tac (claset() addDs [reachable_imp_reachable_project], 
	      simpset()));
qed "reachable_extend_Join_subset";

Goalw [Constrains_def]
     "extend h F Join G : (extend_set h A) Co (extend_set h B)  \
\     ==> F Join project h (reachable (extend h F Join G)) G : A Co B";
by (full_simp_tac (simpset() addsimps [Join_project_constrains, 
				       extend_set_Int_distrib]) 1);
by (rtac conjI 1);
by (force_tac
    (claset() addEs [constrains_weaken_L]
              addSDs [extend_constrains_project_set,
		      subset_refl RS reachable_project_imp_reachable], 
     simpset() addsimps [Join_constrains]) 2);
by (blast_tac (claset() addIs [constrains_weaken_L]) 1);
qed "project_Constrains_I";

Goalw [Stable_def]
     "extend h F Join G : Stable (extend_set h A)  \
\     ==> F Join project h (reachable (extend h F Join G)) G : Stable A";
by (asm_simp_tac (simpset() addsimps [project_Constrains_I]) 1);
qed "project_Stable_I";

Goalw [Always_def]
     "extend h F Join G : Always (extend_set h A)  \
\     ==> F Join project h (reachable (extend h F Join G)) G : Always A";
by (auto_tac (claset(), simpset() addsimps [project_Stable_I]));
by (rewtac extend_set_def);
by (Blast_tac 1);
qed "project_Always_I";

Goalw [Increasing_def]
    "extend h F Join G : Increasing (func o f)  \
\    ==> F Join project h (reachable (extend h F Join G)) G : Increasing func";
by Auto_tac;
by (asm_simp_tac (simpset() addsimps [extend_set_eq_Collect,
				      project_Stable_I]) 1); 
qed "project_Increasing_I";

Goal "(F Join project h (reachable (extend h F Join G)) G : A Co B)  =  \
\     (extend h F Join G : (extend_set h A) Co (extend_set h B))";
by (blast_tac (claset() addIs [project_Constrains_I, project_Constrains_D]) 1);
qed "project_Constrains";

Goalw [Stable_def]
     "(F Join project h (reachable (extend h F Join G)) G : Stable A)  =  \
\     (extend h F Join G : Stable (extend_set h A))";
by (rtac project_Constrains 1);
qed "project_Stable";

Goal
   "(F Join project h (reachable (extend h F Join G)) G : Increasing func)  = \
\   (extend h F Join G : Increasing (func o f))";
by (asm_simp_tac (simpset() addsimps [Increasing_def, project_Stable,
				      extend_set_eq_Collect]) 1);
qed "project_Increasing";

(** A lot of redundant theorems: all are proved to facilitate reasoning
    about guarantees. **)

Goalw [projecting_def]
     "projecting (%G. reachable (extend h F Join G)) h F \
\                (extend_set h A Co extend_set h B) (A Co B)";
by (blast_tac (claset() addIs [project_Constrains_I]) 1);
qed "projecting_Constrains";

Goalw [Stable_def]
     "projecting (%G. reachable (extend h F Join G)) h F \
\                (Stable (extend_set h A)) (Stable A)";
by (rtac projecting_Constrains 1);
qed "projecting_Stable";

Goalw [projecting_def]
     "projecting (%G. reachable (extend h F Join G)) h F \
\                (Always (extend_set h A)) (Always A)";
by (blast_tac (claset() addIs [project_Always_I]) 1);
qed "projecting_Always";

Goalw [projecting_def]
     "projecting (%G. reachable (extend h F Join G)) h F \
\                (Increasing (func o f)) (Increasing func)";
by (blast_tac (claset() addIs [project_Increasing_I]) 1);
qed "projecting_Increasing";

Goalw [extending_def]
     "extending v (%G. reachable (extend h F Join G)) h F \
\                 (extend_set h A Co extend_set h B) (A Co B)";
by (blast_tac (claset() addIs [project_Constrains_D]) 1);
qed "extending_Constrains";

Goalw [extending_def]
     "extending v (%G. reachable (extend h F Join G)) h F \
\                 (Stable (extend_set h A)) (Stable A)";
by (blast_tac (claset() addIs [project_Stable_D]) 1);
qed "extending_Stable";

Goalw [extending_def]
     "extending v (%G. reachable (extend h F Join G)) h F \
\                 (Always (extend_set h A)) (Always A)";
by (blast_tac (claset() addIs [project_Always_D]) 1);
qed "extending_Always";

Goalw [extending_def]
     "extending v (%G. reachable (extend h F Join G)) h F \
\                 (Increasing (func o f)) (Increasing func)";
by (blast_tac (claset() addIs [project_Increasing_D]) 1);
qed "extending_Increasing";


(*** leadsETo in the precondition (??) ***)

(** transient **)

Goalw [transient_def]
     "[| G : transient (C Int extend_set h A);  G : stable C |]  \
\     ==> project h C G : transient (project_set h C Int A)";
by (auto_tac (claset(), simpset() addsimps [Domain_project_act]));
by (subgoal_tac "act ^^ (C Int extend_set h A) <= - extend_set h A" 1);
by (asm_full_simp_tac 
    (simpset() addsimps [stable_def, constrains_def]) 2);
by (Blast_tac 2);
(*back to main goal*)
by (thin_tac "?AA <= -C Un ?BB" 1);
by (ball_tac 1);
by (asm_full_simp_tac 
    (simpset() addsimps [extend_set_def, project_act_def]) 1);
by (Blast_tac 1);
qed "transient_extend_set_imp_project_transient";

(*converse might hold too?*)
Goalw [transient_def]
     "project h C (extend h F) : transient (project_set h C Int D) \
\     ==> F : transient (project_set h C Int D)";
by (auto_tac (claset(), simpset() addsimps [Domain_project_act]));
by (rtac bexI 1);
by (assume_tac 2);
by Auto_tac;
by (rewtac extend_act_def);
by (Blast_tac 1);
qed "project_extend_transient_D";


(** ensures -- a primitive combining progress with safety **)

(*Used to prove project_leadsETo_I*)
Goal "[| extend h F : stable C;  G : stable C;  \
\        extend h F Join G : A ensures B;  A-B = C Int extend_set h D |]  \
\     ==> F Join project h C G  \
\           : (project_set h C Int project_set h A) ensures (project_set h B)";
by (asm_full_simp_tac
    (simpset() addsimps [ensures_def, Join_constrains, project_constrains, 
			 Join_transient, extend_transient]) 1);
by (Clarify_tac 1);
by (REPEAT_FIRST (rtac conjI));
(*first subgoal*)
by (blast_tac (claset() addIs [extend_stable_project_set RS stableD RS 
			       constrains_Int RS constrains_weaken]
	                addSDs [extend_constrains_project_set]
			addSDs [equalityD1]) 1);
(*2nd subgoal*)
by (etac (stableD RS constrains_Int RS constrains_weaken) 1);
by (assume_tac 1);
by (Blast_tac 3);
by (full_simp_tac (simpset() addsimps [extend_set_Int_distrib,
				       extend_set_Un_distrib]) 2);
by (blast_tac (claset() addSIs [impOfSubs extend_set_project_set]) 2);
by (full_simp_tac (simpset() addsimps [extend_set_def]) 1);
by (Blast_tac 1);
(*The transient part*)
by Auto_tac;
by (force_tac (claset() addSDs [equalityD1]
	                addIs [transient_extend_set_imp_project_transient RS
			       transient_strengthen], 
              simpset()) 2);
by (full_simp_tac (simpset() addsimps [Int_Diff]) 1);
by (force_tac (claset() addSDs [equalityD1]
	                addIs [transient_extend_set_imp_project_transient RS 
			 project_extend_transient_D RS transient_strengthen], 
              simpset()) 1);
qed "ensures_extend_set_imp_project_ensures";

(*Used to prove project_leadsETo_D*)
Goal "[| project h C G ~: transient (A-B) | A<=B;  \
\        extend h F Join G : stable C;  \
\        F Join project h C G : A ensures B |] \
\     ==> extend h F Join G : (C Int extend_set h A) ensures (extend_set h B)";
by (etac disjE 1);
by (blast_tac (claset() addIs [subset_imp_ensures]) 2);
by (auto_tac (claset() addDs [extend_transient RS iffD2] 
                       addIs [transient_strengthen, project_set_I,
			      project_unless RS unlessD, unlessI, 
			      project_extend_constrains_I], 
	      simpset() addsimps [ensures_def, Join_constrains,
				  Join_stable, Join_transient]));
qed_spec_mp "Join_project_ensures";

(** Lemma useful for both STRONG and WEAK progress, but the transient
    condition's very strong **)

(*The strange induction formula allows induction over the leadsTo
  assumption's non-atomic precondition*)
Goal "[| ALL D. project h C G : transient D --> D={};  \
\        extend h F Join G : stable C;  \
\        F Join project h C G : (project_set h C Int A) leadsTo B |] \
\     ==> extend h F Join G : \
\         C Int extend_set h (project_set h C Int A) leadsTo (extend_set h B)";
by (etac leadsTo_induct 1);
by (asm_simp_tac (simpset() delsimps UN_simps
		  addsimps [Int_UN_distrib, leadsTo_UN, extend_set_Union]) 3);
by (blast_tac (claset() addIs [psp_stable2 RS leadsTo_weaken_L, 
			       leadsTo_Trans]) 2);
by (blast_tac (claset() addIs [leadsTo_Basis, Join_project_ensures]) 1);
val lemma = result();

Goal "[| ALL D. project h C G : transient D --> D={};  \
\        extend h F Join G : stable C;  \
\        F Join project h C G : (project_set h C Int A) leadsTo B |] \
\     ==> extend h F Join G : (C Int extend_set h A) leadsTo (extend_set h B)";
by (rtac (lemma RS leadsTo_weaken) 1);
by (auto_tac (claset(), simpset() addsimps [split_extended_all]));
qed "project_leadsTo_D_lemma";

Goal "[| C = (reachable (extend h F Join G)); \
\        ALL D. project h C G : transient D --> D={};  \
\        F Join project h C G : A LeadsTo B |] \
\     ==> extend h F Join G : (extend_set h A) LeadsTo (extend_set h B)";
by (asm_full_simp_tac 
    (simpset() addsimps [LeadsTo_def, project_leadsTo_D_lemma, 
			 project_set_reachable_extend_eq]) 1);
qed "Join_project_LeadsTo";


(*** Towards project_Ensures_D ***)



Goalw [project_set_def, extend_set_def, project_act_def]
     "act ^^ (C Int extend_set h A) <= B \
\     ==> project_act h (Restrict C act) ^^ (project_set h C Int A) \
\         <= project_set h B";
by (Blast_tac 1);
qed "act_subset_imp_project_act_subset";


Goal "[| G : stable ((C Int extend_set h A) - (extend_set h B));  \
\        project h C G : transient (project_set h C Int A - B) |]  \
\     ==> G : transient (C Int extend_set h A - extend_set h B)";
by (case_tac "C Int extend_set h A <= extend_set h B" 1);
by (asm_simp_tac (simpset() addsimps [Diff_eq_empty_iff RS iffD2]) 1);
by (auto_tac (claset(), 
	      simpset() addsimps [transient_def, subset_Compl_self_eq,
				  Domain_project_act, split_extended_all]));
by (Blast_tac 1);
by (auto_tac (claset(), 
	      simpset() addsimps [stable_def, constrains_def]));
by (ball_tac 1);
by (thin_tac "ALL act: Acts G. ?P act" 1);
by (auto_tac (claset(), 
	      simpset() addsimps [Int_Diff,
				  extend_set_Diff_distrib RS sym]));
by (dtac act_subset_imp_project_act_subset 1);
by (subgoal_tac
    "project_act h (Restrict C act) ^^ (project_set h C Int (A - B)) <= {}" 1);
by (rewrite_goals_tac [project_set_def, extend_set_def, project_act_def]);
(*using Int_greatest actually slows the next step!*)
by (Blast_tac 2);
by (rtac ccontr 1);
by (dtac subsetD 1);
by (Blast_tac 1);  
by (force_tac (claset(), simpset() addsimps [split_extended_all]) 1);
qed "stable_project_transient";


Goal "[| G : stable C;  project h C G : (project_set h C Int A) unless B |] \
\     ==> G : (C Int extend_set h A) unless (extend_set h B)";
by (auto_tac
    (claset() addDs [stable_constrains_Int]
              addIs [constrains_weaken],
     simpset() addsimps [unless_def, project_constrains, Diff_eq, 
			 Int_assoc, Int_extend_set_lemma]));
qed_spec_mp "project_unless2";

Goal "[| G : stable ((C Int extend_set h A) - (extend_set h B));  \
\        F Join project h C G : (project_set h C Int A) ensures B;  \
\        extend h F Join G : stable C |] \
\     ==> extend h F Join G : (C Int extend_set h A) ensures (extend_set h B)";
(*unless*)
by (auto_tac (claset() addSIs [rewrite_rule [unless_def] project_unless2] 
                       addIs [project_extend_constrains_I], 
	      simpset() addsimps [ensures_def, Join_constrains,
				  Join_stable]));
(*transient*)
by (auto_tac (claset(), simpset() addsimps [Join_transient]));
by (blast_tac (claset() addIs [stable_project_transient]) 2);
by (force_tac (claset() addSEs [extend_transient RS iffD2 RS 
				transient_strengthen], 
	       simpset() addsimps [Join_transient, split_extended_all]) 1);
qed "project_ensures_D_lemma";

Goal "[| F Join project h UNIV G : A ensures B;  \
\        G : stable (extend_set h A - extend_set h B) |] \
\     ==> extend h F Join G : (extend_set h A) ensures (extend_set h B)";
by (rtac (project_ensures_D_lemma RS revcut_rl) 1);
by (stac stable_UNIV 3);
by Auto_tac;
qed "project_ensures_D";

Goalw [Ensures_def]
     "[| F Join project h (reachable (extend h F Join G)) G : A Ensures B;  \
\        G : stable (reachable (extend h F Join G) Int extend_set h A - \
\                    extend_set h B) |] \
\     ==> extend h F Join G : (extend_set h A) Ensures (extend_set h B)";
by (rtac (project_ensures_D_lemma RS revcut_rl) 1);
by (auto_tac (claset(), 
	      simpset() addsimps [project_set_reachable_extend_eq RS sym]));
qed "project_Ensures_D";


(*** Guarantees ***)

(*Weak precondition and postcondition
  Not clear that it has a converse [or that we want one!]*)

(*The raw version*)
val [xguary,project,extend] =
Goal "[| F : X guarantees[v] Y;  \
\        !!G. extend h F Join G : X' ==> F Join project h (C G) G : X;  \
\        !!G. [| F Join project h (C G) G : Y; extend h F Join G : X'; \
\                G : preserves (v o f) |] \
\             ==> extend h F Join G : Y' |] \
\     ==> extend h F : X' guarantees[v o f] Y'";
by (rtac (xguary RS guaranteesD RS extend RS guaranteesI) 1);
by (etac project_preserves_I 1);
by (etac project 1);
by Auto_tac;
qed "project_guarantees_raw";

Goal "[| F : X guarantees[v] Y;  \
\        projecting C h F X' X;  extending w C h F Y' Y; \
\        preserves w <= preserves (v o f) |] \
\     ==> extend h F : X' guarantees[w] Y'";
by (rtac guaranteesI 1);
by (auto_tac (claset(), 
        simpset() addsimps [project_preserves_I, guaranteesD, projecting_def,
			    extending_def]));
qed "project_guarantees";


(*It seems that neither "guarantees" law can be proved from the other.*)


(*** guarantees corollaries ***)

(** Some could be deleted: the required versions are easy to prove **)

Goal "F : UNIV guarantees[v] increasing func \
\     ==> extend h F : X' guarantees[v o f] increasing (func o f)";
by (etac project_guarantees 1);
by (rtac extending_increasing 2);
by (rtac projecting_UNIV 1);
by Auto_tac;
qed "extend_guar_increasing";

Goal "F : UNIV guarantees[v] Increasing func \
\     ==> extend h F : X' guarantees[v o f] Increasing (func o f)";
by (etac project_guarantees 1);
by (rtac extending_Increasing 2);
by (rtac projecting_UNIV 1);
by Auto_tac;
qed "extend_guar_Increasing";

Goal "F : Always A guarantees[v] Always B \
\     ==> extend h F : Always(extend_set h A) guarantees[v o f] \
\                      Always(extend_set h B)";
by (etac project_guarantees 1);
by (rtac extending_Always 2);
by (rtac projecting_Always 1);
by Auto_tac;
qed "extend_guar_Always";

Goal "[| G : preserves f;  project h C G : transient D |] ==> D={}";
by (rtac stable_transient_empty 1);
by (assume_tac 2);
by (blast_tac (claset() addIs [project_preserves_id_I,
			 impOfSubs preserves_id_subset_stable]) 1);
qed "preserves_project_transient_empty";


(** Guarantees with a leadsTo postcondition 
    THESE ARE ALL TOO WEAK because G can't affect F's variables at all**)

Goal "[| F Join project h UNIV G : A leadsTo B;    \
\        G : preserves f |]  \
\     ==> extend h F Join G : (extend_set h A) leadsTo (extend_set h B)";
by (res_inst_tac [("C1", "UNIV")] 
    (project_leadsTo_D_lemma RS leadsTo_weaken) 1);
by (auto_tac (claset() addDs [preserves_project_transient_empty], 
	      simpset()));
qed "project_leadsTo_D";

Goal "[| F Join project h (reachable (extend h F Join G)) G : A LeadsTo B; \
\         G : preserves f |]  \
\      ==> extend h F Join G : (extend_set h A) LeadsTo (extend_set h B)";
by (rtac (refl RS Join_project_LeadsTo) 1);
by (auto_tac (claset() addDs [preserves_project_transient_empty], 
	      simpset()));
qed "project_LeadsTo_D";

Goalw [extending_def]
     "extending f (%G. UNIV) h F \
\                 (extend_set h A leadsTo extend_set h B) (A leadsTo B)";
by (blast_tac (claset() addIs [project_leadsTo_D]) 1);
qed "extending_leadsTo";

Goalw [extending_def]
     "extending f (%G. reachable (extend h F Join G)) h F \
\                 (extend_set h A LeadsTo extend_set h B) (A LeadsTo B)";
by (blast_tac (claset() addIs [project_LeadsTo_D]) 1);
qed "extending_LeadsTo";

(*STRONG precondition and postcondition*)
Goal "F : (A co A') guarantees[v] (B leadsTo B')  \
\ ==> extend h F : (extend_set h A co extend_set h A') \
\                  guarantees[f] (extend_set h B leadsTo extend_set h B')";
by (etac project_guarantees 1);
by (rtac subset_preserves_o 3);
by (rtac extending_leadsTo 2);
by (rtac projecting_constrains 1);
qed "extend_co_guar_leadsTo";

(*WEAK precondition and postcondition*)
Goal "F : (A Co A') guarantees[v] (B LeadsTo B')  \
\ ==> extend h F : (extend_set h A Co extend_set h A') \
\                  guarantees[f] (extend_set h B LeadsTo extend_set h B')";
by (etac project_guarantees 1);
by (rtac subset_preserves_o 3);
by (rtac extending_LeadsTo 2);
by (rtac projecting_Constrains 1);
qed "extend_Co_guar_LeadsTo";

Close_locale "Extend";
