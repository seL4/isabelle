(*  Title:      HOL/UNITY/Project.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Projections of state sets (also of actions and programs)

Inheritance of GUARANTEES properties under extension
*)

Open_locale "Extend";

(** projection: monotonicity for safety **)

Goal "D <= C ==> project_act D h act <= project_act C h act";
by (auto_tac (claset(), simpset() addsimps [project_act_def]));
qed "project_act_mono";

Goal "[| D <= C; project C h F : A co B |] ==> project D h F : A co B";
by (auto_tac (claset(), simpset() addsimps [constrains_def]));
by (dtac project_act_mono 1);
by (Blast_tac 1);
qed "project_constrains_mono";

Goal "[| D <= C;  project C h F : stable A |] ==> project D h F : stable A";
by (asm_full_simp_tac
    (simpset() addsimps [stable_def, project_constrains_mono]) 1);
qed "project_stable_mono";

Goal "F : A co B ==> project C h (extend h F) : A co B";
by (auto_tac (claset(), 
      simpset() addsimps [extend_act_def, project_act_def, constrains_def]));
qed "project_extend_constrains_I";

Goal "UNIV <= project_set h C \
\     ==> project C h ((extend h F) Join G) = F Join (project C h G)";
by (rtac program_equalityI 1);
by (asm_simp_tac (simpset() addsimps [image_Un, image_image,
			subset_UNIV RS subset_trans RS extend_act_inverse]) 2);
by (simp_tac (simpset() addsimps [project_set_extend_set_Int]) 1);
qed "project_extend_Join";

Goal "UNIV <= project_set h C \
\     ==> (extend h F) Join G = extend h H ==> H = F Join (project C h G)";
by (dres_inst_tac [("f", "project C h")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [project_extend_Join]) 1);
qed "extend_Join_eq_extend_D";


(** Safety **)

Goalw [constrains_def]
     "(project C h F : A co B)  =  \
\     (F : (C Int extend_set h A) co (extend_set h B) & A <= B)";
by (auto_tac (claset() addSIs [project_act_I], simpset() addsimps [ball_Un]));
by (force_tac (claset() addSIs [project_act_I] addSDs [subsetD], simpset()) 1);
(*the <== direction*)
by (rewtac project_act_def);
by (force_tac (claset() addSDs [subsetD], simpset()) 1);
qed "project_constrains";

Goalw [stable_def]
     "(project UNIV h F : stable A) = (F : stable (extend_set h A))";
by (simp_tac (simpset() addsimps [project_constrains]) 1);
qed "project_stable";

Goal "F : stable (extend_set h A) ==> project C h F : stable A";
by (dtac (project_stable RS iffD2) 1);
by (blast_tac (claset() addIs [project_stable_mono]) 1);
qed "project_stable_I";

(*used below to prove Join_project_ensures*)
Goal "[| G : stable C;  project C h G : A unless B |] \
\     ==> G : (C Int extend_set h A) unless (extend_set h B)";
by (asm_full_simp_tac
    (simpset() addsimps [unless_def, project_constrains]) 1);
by (blast_tac (claset() addDs [stable_constrains_Int]
			addIs [constrains_weaken]) 1);
qed_spec_mp "project_unless";

(*This form's useful with guarantees reasoning*)
Goal "(F Join project C h G : A co B)  =  \
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
\     ==> (F Join project C h G : stable A)  =  \
\         (extend h F Join G : stable (C Int extend_set h A) &  \
\          F : stable A)";
by (simp_tac (simpset() addsimps [Join_project_constrains]) 1);
by (blast_tac (claset() addIs [constrains_weaken] addDs [constrains_Int]) 1);
qed "Join_project_stable";

Goal "(F Join project UNIV h G : increasing func)  =  \
\     (extend h F Join G : increasing (func o f))";
by (simp_tac (simpset() addsimps [increasing_def, Join_project_stable]) 1);
by (auto_tac (claset(),
	      simpset() addsimps [Join_stable, Collect_eq_extend_set RS sym,
				  extend_stable RS iffD1]));
qed "Join_project_increasing";

(*For using project_guarantees in particular cases*)
Goal "extend h F Join G : extend_set h A co extend_set h B \
\     ==> F Join project C h G : A co B";
by (asm_full_simp_tac
    (simpset() addsimps [project_constrains, Join_constrains, 
			 extend_constrains]) 1);
by (blast_tac (claset() addIs [constrains_weaken]
			addDs [constrains_imp_subset]) 1);
qed "project_constrains_I";

(*The UNIV argument is essential*)
Goal "F Join project UNIV h G : A co B \
\     ==> extend h F Join G : extend_set h A co extend_set h B";
by (asm_full_simp_tac
    (simpset() addsimps [project_constrains, Join_constrains, 
			 extend_constrains]) 1);
qed "project_constrains_D";

Goalw [projecting_def]
     "[| ALL i:I. projecting C h F (X' i) (X i) |] \
\     ==> projecting C h F (INT i:I. X' i) (INT i:I. X i)";
by Auto_tac;
qed "projecting_INT";

Goalw [projecting_def]
     "[| ALL i:I. projecting C h F (X' i) (X i) |] \
\     ==> projecting C h F (UN i:I. X' i) (UN i:I. X i)";
by Auto_tac;
qed "projecting_UN";

Goalw [projecting_def]
     "[| projecting C h F X' X;  U'<=X';  X<=U |] ==> projecting C h F U' U";
by Auto_tac;
qed "projecting_weaken";

(*Is this the right way to handle the X' argument?*)
Goalw [extending_def]
     "[| ALL i:I. extending C h F (X' i) (Y' i) (Y i) |] \
\     ==> extending C h F (INT i:I. X' i) (INT i:I. Y' i) (INT i:I. Y i)";
by Auto_tac;
qed "extending_INT";

Goalw [extending_def]
     "[| ALL i:I. extending C h F X' (Y' i) (Y i) |] \
\     ==> extending C h F X' (UN i:I. Y' i) (UN i:I. Y i)";
by Auto_tac;
qed "extending_UN";

Goalw [extending_def]
     "[| extending C h F X' Y' Y;  U'<= X';  Y'<=V';  V<=Y |] \
\     ==> extending C h F U' V' V";
by Auto_tac;
qed "extending_weaken";

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
     "projecting (%G. UNIV) h F (increasing (func o f)) (increasing func)";
by (simp_tac (simpset() addsimps [Join_project_increasing]) 1);
qed "projecting_increasing";

Goal "extending C h F X' UNIV Y";
by (simp_tac (simpset() addsimps [extending_def]) 1);
qed "extending_UNIV";

Goalw [extending_def]
     "extending (%G. UNIV) h F X' (extend_set h A co extend_set h B) (A co B)";
by (blast_tac (claset() addIs [project_constrains_D]) 1);
qed "extending_constrains";

Goalw [stable_def]
     "extending (%G. UNIV) h F X' (stable (extend_set h A)) (stable A)";
by (rtac extending_constrains 1);
qed "extending_stable";

Goalw [extending_def]
     "extending (%G. UNIV) h F X' (increasing (func o f)) (increasing func)";
by (simp_tac (simpset() addsimps [Join_project_increasing]) 1);
qed "extending_increasing";


(*** Diff, needed for localTo ***)

(*Opposite direction fails because Diff in the extended state may remove
  fewer actions, i.e. those that affect other state variables.*)
Goal "(UN act:acts. Domain act) <= project_set h C \
\     ==> Diff (project C h G) acts <= \
\         project C h (Diff G (extend_act h `` acts))";
by (asm_full_simp_tac (simpset() addsimps [component_eq_subset, Diff_def,
					   UN_subset_iff]) 1);
by (force_tac (claset() addSIs [image_diff_subset RS subsetD], 
	       simpset() addsimps [image_image_eq_UN]) 1);
qed "Diff_project_component_project_Diff";

Goal
   "[| (UN act:acts. Domain act) <= project_set h C; \
\      Diff G (extend_act h `` acts) : (extend_set h A) co (extend_set h B) |]\
\   ==> Diff (project C h G) acts : A co B";
by (etac (Diff_project_component_project_Diff RS component_constrains) 1);
by (rtac (project_constrains RS iffD2) 1);
by (ftac constrains_imp_subset 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "Diff_project_constrains";

Goalw [stable_def]
     "[| (UN act:acts. Domain act) <= project_set h C; \
\        Diff G (extend_act h `` acts) : stable (extend_set h A) |] \
\     ==> Diff (project C h G) acts : stable A";
by (etac Diff_project_constrains 1);
by (assume_tac 1);
qed "Diff_project_stable";

(*Converse fails: even if the conclusion holds, H could modify (v o f) 
  simultaneously with other variables, and this action would not be 
  superseded by anything in (extend h G) *)
Goal "[| UNIV <= project_set h C;  H : (func o f) localTo extend h G |] \
\     ==> project C h H : func localTo G";
by (asm_full_simp_tac 
    (simpset() addsimps [localTo_def, 
			 project_extend_Join RS sym,
			 subset_UNIV RS subset_trans RS Diff_project_stable,
			 Collect_eq_extend_set RS sym]) 1);
qed "project_localTo_lemma";

Goal "extend h F Join G : (v o f) localTo extend h H \
\     ==> F Join project UNIV h G : v localTo H";
by (stac (project_set_UNIV RS project_extend_Join RS sym) 1);
by (asm_simp_tac 
    (simpset() addsimps [project_set_UNIV RS project_localTo_lemma]) 1);
qed "project_localTo_I";

Goalw [projecting_def]
     "projecting (%G. UNIV) h F ((v o f) localTo extend h H) (v localTo H)";
by (blast_tac (claset() addIs [project_localTo_I]) 1);
qed "projecting_localTo";


(** Reachability and project **)

Goal "[| reachable (extend h F Join G) <= C;  \
\        z : reachable (extend h F Join G) |] \
\     ==> f z : reachable (F Join project C h G)";
by (etac reachable.induct 1);
by (force_tac (claset() addIs [reachable.Init, project_set_I],
	       simpset()) 1);
by Auto_tac;
by (force_tac (claset() addIs [project_act_I RSN (3,reachable.Acts)],
	       simpset()) 2);
by (res_inst_tac [("act","x")] reachable.Acts 1);
by Auto_tac;
by (etac extend_act_D 1);
qed "reachable_imp_reachable_project";

(*The extra generality in the first premise allows guarantees with STRONG
  preconditions (localTo) and WEAK postconditions.*)
Goalw [Constrains_def]
     "[| reachable (extend h F Join G) <= C;    \
\        F Join project C h G : A Co B |] \
\     ==> extend h F Join G : (extend_set h A) Co (extend_set h B)";
by (full_simp_tac (simpset() addsimps [Join_project_constrains]) 1);
by (Clarify_tac 1);
by (etac constrains_weaken 1);
by (auto_tac (claset() addDs [reachable_imp_reachable_project], simpset()));
qed "project_Constrains_D";

Goalw [Stable_def]
     "[| reachable (extend h F Join G) <= C;  \
\        F Join project C h G : Stable A |]   \
\     ==> extend h F Join G : Stable (extend_set h A)";
by (asm_simp_tac (simpset() addsimps [project_Constrains_D]) 1);
qed "project_Stable_D";

Goalw [Always_def]
     "[| reachable (extend h F Join G) <= C;  \
\        F Join project C h G : Always A |]   \
\     ==> extend h F Join G : Always (extend_set h A)";
by (force_tac (claset() addIs [reachable.Init, project_set_I],
               simpset() addsimps [project_Stable_D]) 1);
qed "project_Always_D";

Goalw [Increasing_def]
     "[| reachable (extend h F Join G) <= C;  \
\        F Join project C h G : Increasing func |] \
\     ==> extend h F Join G : Increasing (func o f)";
by Auto_tac;
by (stac Collect_eq_extend_set 1);
by (asm_simp_tac (simpset() addsimps [project_Stable_D]) 1); 
qed "project_Increasing_D";


(** Converse results for weak safety: benefits of the argument C *)

Goal "[| C <= reachable(extend h F Join G);   \
\        x : reachable (F Join project C h G) |] \
\     ==> EX y. h(x,y) : reachable (extend h F Join G)";
by (etac reachable.induct 1);
by (ALLGOALS Asm_full_simp_tac);
(*SLOW: 6.7s*)
by (force_tac (claset() delrules [Id_in_Acts]
		        addIs [reachable.Acts, extend_act_D],
	       simpset() addsimps [project_act_def]) 2);
by (force_tac (claset() addIs [reachable.Init],
	       simpset() addsimps [project_set_def]) 1);
qed "reachable_project_imp_reachable";


Goal "project_set h (reachable (extend h F Join G)) = \
\     reachable (F Join project (reachable (extend h F Join G)) h G)";
by (auto_tac (claset() addDs [subset_refl RS reachable_imp_reachable_project,
			      subset_refl RS reachable_project_imp_reachable], 
	      simpset() addsimps [project_set_def]));
qed "project_set_reachable_extend_eq";

(*Perhaps should replace C by reachable...*)
Goalw [Constrains_def]
     "[| C <= reachable (extend h F Join G);  \
\        extend h F Join G : (extend_set h A) Co (extend_set h B) |] \
\     ==> F Join project C h G : A Co B";
by (full_simp_tac (simpset() addsimps [Join_project_constrains, 
				       extend_set_Int_distrib]) 1);
by (rtac conjI 1);
by (etac constrains_weaken 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [Join_constrains]) 1);
(*Some generalization of constrains_weaken_L would be better, but what is it?*)
by (rewtac constrains_def);
by Auto_tac;
by (thin_tac "ALL act : Acts G. ?P act" 1);
by (force_tac (claset() addSDs [reachable_project_imp_reachable], 
	       simpset()) 1);
qed "project_Constrains_I";

Goalw [Stable_def]
     "[| C <= reachable (extend h F Join G);  \
\        extend h F Join G : Stable (extend_set h A) |] \
\     ==> F Join project C h G : Stable A";
by (asm_simp_tac (simpset() addsimps [project_Constrains_I]) 1);
qed "project_Stable_I";

Goalw [Always_def]
     "[| C <= reachable (extend h F Join G);  \
\        extend h F Join G : Always (extend_set h A) |]   \
\     ==> F Join project C h G : Always A";
by (auto_tac (claset(), simpset() addsimps [project_Stable_I]));
by (rewrite_goals_tac [project_set_def, extend_set_def]);
by (Blast_tac 1);
qed "project_Always_I";

Goalw [Increasing_def]
     "[| C <= reachable (extend h F Join G);  \
\        extend h F Join G : Increasing (func o f) |] \
\     ==> F Join project C h G : Increasing func";
by Auto_tac;
by (asm_simp_tac (simpset() addsimps [Collect_eq_extend_set RS sym,
				      project_Stable_I]) 1); 
qed "project_Increasing_I";

Goal "(F Join project (reachable (extend h F Join G)) h G : A Co B)  =  \
\     (extend h F Join G : (extend_set h A) Co (extend_set h B))";
by (blast_tac (claset() addIs [project_Constrains_I, project_Constrains_D]) 1);
qed "project_Constrains";

Goalw [Stable_def]
     "(F Join project (reachable (extend h F Join G)) h G : Stable A)  =  \
\     (extend h F Join G : Stable (extend_set h A))";
by (rtac project_Constrains 1);
qed "project_Stable";

Goal
   "(F Join project (reachable (extend h F Join G)) h G : Increasing func)  = \
\   (extend h F Join G : Increasing (func o f))";
by (asm_simp_tac (simpset() addsimps [Increasing_def, project_Stable,
				      Collect_eq_extend_set RS sym]) 1);
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
     "extending (%G. reachable (extend h F Join G)) h F X' \
\               (extend_set h A Co extend_set h B) (A Co B)";
by (blast_tac (claset() addIs [project_Constrains_D]) 1);
qed "extending_Constrains";

Goalw [extending_def]
     "extending (%G. reachable (extend h F Join G)) h F X' \
\               (Stable (extend_set h A)) (Stable A)";
by (blast_tac (claset() addIs [project_Stable_D]) 1);
qed "extending_Stable";

Goalw [extending_def]
     "extending (%G. reachable (extend h F Join G)) h F X' \
\               (Always (extend_set h A)) (Always A)";
by (blast_tac (claset() addIs [project_Always_D]) 1);
qed "extending_Always";

val [prem] = 
Goalw [extending_def]
     "(!!G. reachable (extend h F Join G) <= C G)  \
\     ==> extending C h F X' \
\                   (Increasing (func o f)) (Increasing func)";
by (blast_tac (claset() addIs [prem RS project_Increasing_D]) 1);
qed "extending_Increasing";


(** Progress includes safety in the definition of ensures **)

(*** Progress for (project C h F) ***)

(** transient **)

(*Premise is that C includes the domains of all actions that could be the
  transient one.  Could have C=UNIV of course*)
Goalw [transient_def]
     "[| ALL act: Acts F. act ^^ extend_set h A <= - extend_set h A --> \
\                      Domain act <= C;    \
\        F : transient (extend_set h A) |] \
\     ==> project C h F : transient A";
by (auto_tac (claset() delrules [ballE],
              simpset() addsimps [Domain_project_act, Int_absorb2]));
by (REPEAT (ball_tac 1));
by (auto_tac (claset(),
              simpset() addsimps [extend_set_def, project_set_def, 
				  project_act_def]));
by (ALLGOALS Blast_tac);
qed "transient_extend_set_imp_project_transient";


(*UNUSED.  WHY??
  Converse of the above...it requires a strong assumption about actions
  being enabled for all possible values of the new variables.*)
Goalw [transient_def]
     "[| project C h F : transient A;  \
\        ALL act: Acts F. project_act C h act ^^ A <= - A --> \
\                         Domain act <= C \
\             & extend_set h (project_set h (Domain act)) <= Domain act |]  \
\     ==> F : transient (extend_set h A)";
by (auto_tac (claset() delrules [ballE],
	      simpset() addsimps [Domain_project_act]));
by (ball_tac 1);
by (rtac bexI 1);
by (assume_tac 2);
by Auto_tac;
by (eres_inst_tac [("P", "A <= ?B")] rev_mp 1);
by (force_tac (claset(), simpset() addsimps [Int_absorb2]) 1);
(*The Domain requirement's proved; must prove the Image requirement*)
by (res_inst_tac [("y1", "x")] (surj_h RS surjD RS exE) 1);
by (res_inst_tac [("y1", "xa")] (surj_h RS surjD RS exE) 1);
by Auto_tac;
by (thin_tac "A <= ?B" 1);
by (force_tac (claset() addSIs [ImageI, project_act_I], simpset()) 1);
qed "project_transient_imp_transient_extend_set";


(** ensures **)

(*For simplicity, the complicated condition on C is eliminated
  NOT SURE THIS IS GOOD FOR ANYTHING: CAN'T PROVE LEADSTO THEOREM*)
Goal "F : (extend_set h A) ensures (extend_set h B) \
\     ==> project UNIV h F : A ensures B";
by (asm_full_simp_tac
    (simpset() addsimps [ensures_def, project_constrains, 
			 transient_extend_set_imp_project_transient,
			 extend_set_Un_distrib RS sym, 
			 extend_set_Diff_distrib RS sym]) 1);
by (Blast_tac 1);
qed "ensures_extend_set_imp_project_ensures";

(*A strong condition: F can do anything that project G can.*)
Goal "[| ALL D. project C h G : transient D --> F : transient D;  \
\        extend h F Join G : stable C;  \
\        F Join project C h G : A ensures B |] \
\     ==> extend h F Join G : (C Int extend_set h A) ensures (extend_set h B)";
by (case_tac "A <= B" 1);
by (blast_tac (claset() addIs [subset_imp_ensures] addDs [extend_set_mono]) 1);
by (full_simp_tac (simpset() addsimps [ensures_def, Join_constrains,
				       Join_stable, Join_transient]) 1);
by (REPEAT_FIRST (rtac conjI));
by (blast_tac (claset() addDs [extend_transient RS iffD2] 
                        addIs [transient_strengthen]) 3);
by (REPEAT (force_tac (claset() addIs [project_unless RS unlessD, unlessI, 
				       project_extend_constrains_I], 
		       simpset()) 1));
qed_spec_mp "Join_project_ensures";

Goal "[| ALL D. project C h G : transient D --> F : transient D;  \
\        extend h F Join G : stable C;  \
\        F Join project C h G : A leadsTo B |] \
\     ==> extend h F Join G : (C Int extend_set h A) leadsTo (extend_set h B)";
by (etac leadsTo_induct 1);
by (asm_simp_tac (simpset() delsimps UN_simps
		  addsimps [Int_UN_distrib, leadsTo_UN, extend_set_Union]) 3);
by (blast_tac (claset() addIs [psp_stable RS leadsTo_weaken, 
			       leadsTo_Trans]) 2);
by (blast_tac (claset() addIs [leadsTo_Basis, Join_project_ensures]) 1);
qed "project_leadsTo_lemma";

(*Instance of the previous theorem for STRONG progress*)
Goal "[| ALL D. project UNIV h G : transient D --> F : transient D;  \
\        F Join project UNIV h G : A leadsTo B |] \
\     ==> extend h F Join G : (extend_set h A) leadsTo (extend_set h B)";
by (dtac project_leadsTo_lemma 1);
by Auto_tac;
qed "project_UNIV_leadsTo_lemma";

(** Towards the analogous theorem for WEAK progress*)

Goal "[| ALL D. project C h G : transient D --> F : transient D;  \
\        extend h F Join G : stable C;  \
\        F Join project C h G : (project_set h C Int A) leadsTo B |] \
\     ==> extend h F Join G : C Int extend_set h (project_set h C Int A) leadsTo (extend_set h B)";
by (etac leadsTo_induct 1);
by (asm_simp_tac (simpset() delsimps UN_simps
		  addsimps [Int_UN_distrib, leadsTo_UN, extend_set_Union]) 3);
by (blast_tac (claset() addIs [psp_stable RS leadsTo_weaken, 
			       leadsTo_Trans]) 2);
by (blast_tac (claset() addIs [leadsTo_Basis, Join_project_ensures]) 1);
val lemma = result();

Goal "[| ALL D. project C h G : transient D --> F : transient D;  \
\        extend h F Join G : stable C;  \
\        F Join project C h G : (project_set h C Int A) leadsTo B |] \
\     ==> extend h F Join G : (C Int extend_set h A) leadsTo (extend_set h B)";
by (rtac (lemma RS leadsTo_weaken) 1);
by (auto_tac (claset() addIs [project_set_I], simpset()));
val lemma2 = result();

Goal "[| C = (reachable (extend h F Join G)); \
\        ALL D. project C h G : transient D --> F : transient D;  \
\        F Join project C h G : A LeadsTo B |] \
\     ==> extend h F Join G : (extend_set h A) LeadsTo (extend_set h B)";
by (asm_full_simp_tac 
    (simpset() addsimps [LeadsTo_def, lemma2, stable_reachable, 
			 project_set_reachable_extend_eq]) 1);
qed "Join_project_LeadsTo";


(*** GUARANTEES and EXTEND ***)

(** Strong precondition and postcondition; doesn't seem very useful. **)

Goal "F : X guarantees Y ==> \
\     extend h F : (extend h `` X) guarantees (extend h `` Y)";
by (rtac guaranteesI 1);
by Auto_tac;
by (blast_tac (claset() addDs [project_set_UNIV RS extend_Join_eq_extend_D, 
			       guaranteesD]) 1);
qed "guarantees_imp_extend_guarantees";

Goal "extend h F : (extend h `` X) guarantees (extend h `` Y) \
\    ==> F : X guarantees Y";
by (auto_tac (claset(), simpset() addsimps [guarantees_eq]));
by (dres_inst_tac [("x", "extend h G")] spec 1);
by (asm_full_simp_tac 
    (simpset() delsimps [extend_Join] 
           addsimps [extend_Join RS sym, inj_extend RS inj_image_mem_iff]) 1);
qed "extend_guarantees_imp_guarantees";

Goal "(extend h F : (extend h `` X) guarantees (extend h `` Y)) = \
\    (F : X guarantees Y)";
by (blast_tac (claset() addIs [guarantees_imp_extend_guarantees,
			       extend_guarantees_imp_guarantees]) 1);
qed "extend_guarantees_eq";


(*Weak precondition and postcondition; this is the good one!
  Not clear that it has a converse [or that we want one!]*)
Goal "[| F : X guarantees Y;  \
\        projecting C h F X' X;  extending C h F X' Y' Y |] \
\     ==> extend h F : X' guarantees Y'";
by (rtac guaranteesI 1);
by (auto_tac (claset(), 
        simpset() addsimps [guaranteesD, projecting_def, extending_def]));
qed "project_guarantees";

(** It seems that neither "guarantees" law can be proved from the other. **)


(*** guarantees corollaries ***)

(** Most could be deleted: the required versions are easy to prove **)

Goal "F : UNIV guarantees increasing func \
\     ==> extend h F : X' guarantees increasing (func o f)";
by (etac project_guarantees 1);
by (rtac extending_increasing 2);
by (rtac projecting_UNIV 1);
qed "extend_guar_increasing";

Goal "F : UNIV guarantees Increasing func \
\     ==> extend h F : X' guarantees Increasing (func o f)";
by (etac project_guarantees 1);
by (rtac extending_Increasing 2);
by (rtac projecting_UNIV 1);
by Auto_tac;
qed "extend_guar_Increasing";

Goal "F : (v localTo G) guarantees increasing func  \
\     ==> extend h F : (v o f) localTo (extend h G)  \
\                      guarantees increasing (func o f)";
by (etac project_guarantees 1);
by (rtac extending_increasing 2);
by (rtac projecting_localTo 1);
qed "extend_localTo_guar_increasing";

Goal "F : (v localTo G) guarantees Increasing func  \
\     ==> extend h F : (v o f) localTo (extend h G)  \
\                      guarantees Increasing (func o f)";
by (etac project_guarantees 1);
by (rtac extending_Increasing 2);
by (rtac projecting_localTo 1);
by Auto_tac;
qed "extend_localTo_guar_Increasing";

Goal "F : Always A guarantees Always B \
\ ==> extend h F : Always(extend_set h A) guarantees Always(extend_set h B)";
by (etac project_guarantees 1);
by (rtac extending_Always 2);
by (rtac projecting_Always 1);
qed "extend_guar_Always";


(** Guarantees with a leadsTo postcondition **)

(*Bridges the gap between the "old" and "new" condition of the leadsTo rules*)
Goal "[| ALL x. project C h G ~: transient {x}; project C h G: transient D |] \
\     ==> F : transient D";
by (case_tac "D={}" 1);
by (auto_tac (claset() addIs [transient_strengthen], simpset()));
qed "transient_lemma";


(*Previously tried to prove
[| G : f localTo extend h F; project C h G : transient D |] ==> F : transient D
but it can fail if C removes some parts of an action of G.*)


Goal "[| G : f localTo extend h F; \
\        Disjoint (extend h F) G |] ==> project C h G : stable {x}";
by (asm_full_simp_tac
    (simpset() addsimps [localTo_imp_stable,
			 extend_set_sing, project_stable_I]) 1);
qed "localTo_imp_project_stable";

Goal "F : stable{s} ==> F ~: transient {s}";
by (auto_tac (claset(), 
	      simpset() addsimps [FP_def, transient_def,
				  stable_def, constrains_def]));
qed "stable_sing_imp_not_transient";

by (auto_tac (claset(), 
	      simpset() addsimps [FP_def, transient_def,
				  stable_def, constrains_def]));
qed "stable_sing_imp_not_transient";

Goal "[| F Join project UNIV h G : A leadsTo B;    \
\        G : f localTo extend h F; \
\        Disjoint (extend h F) G |]  \
\     ==> extend h F Join G : (extend_set h A) leadsTo (extend_set h B)";
by (rtac project_UNIV_leadsTo_lemma 1);
by (Clarify_tac 1);
by (rtac transient_lemma 1);
by (auto_tac (claset(), 
	      simpset() addsimps [localTo_imp_project_stable, 
				  stable_sing_imp_not_transient]));
qed "project_leadsTo_D";

Goal "[| F Join project (reachable (extend h F Join G)) h G : A LeadsTo B; \
\         G : f localTo extend h F; \
\         Disjoint (extend h F) G |]  \
\      ==> extend h F Join G : (extend_set h A) LeadsTo (extend_set h B)";
by (rtac (refl RS Join_project_LeadsTo) 1);
by (Clarify_tac 1);
by (rtac transient_lemma 1);
by (auto_tac (claset(), 
	      simpset() addsimps [localTo_imp_project_stable, 
				  stable_sing_imp_not_transient]));
qed "project_LeadsTo_D";

Goalw [extending_def]
     "extending (%G. UNIV) h F \
\                (f localTo extend h F) \
\                (extend_set h A leadsTo extend_set h B) (A leadsTo B)";
by (blast_tac (claset() addSDs [Join_localTo RS iffD1]
			addIs [project_leadsTo_D]) 1);
qed "extending_leadsTo";

Goalw [extending_def]
     "extending (%G. reachable (extend h F Join G)) h F \
\                (f localTo extend h F) \
\                (extend_set h A LeadsTo extend_set h B) (A LeadsTo B)";
by (blast_tac (claset() addSDs [Join_localTo RS iffD1]
			addIs [project_LeadsTo_D]) 1);
qed "extending_LeadsTo";

(*STRONG precondition and postcondition*)
Goal "F : (A co A') guarantees (B leadsTo B')  \
\ ==> extend h F : ((extend_set h A) co (extend_set h A'))  \
\                   Int (f localTo (extend h F)) \
\                  guarantees ((extend_set h B) leadsTo (extend_set h B'))";
by (etac project_guarantees 1);
by (rtac (extending_leadsTo RS extending_weaken) 2);
by (rtac (projecting_constrains RS projecting_weaken) 1);
by Auto_tac;
qed "extend_co_guar_leadsTo";

(*WEAK precondition and postcondition*)
Goal "F : (A Co A') guarantees (B LeadsTo B')  \
\ ==> extend h F : ((extend_set h A) Co (extend_set h A'))  \
\                   Int (f localTo (extend h F)) \
\                  guarantees ((extend_set h B) LeadsTo (extend_set h B'))";
by (etac project_guarantees 1);
by (rtac (extending_LeadsTo RS extending_weaken) 2);
by (rtac (projecting_Constrains RS projecting_weaken) 1);
by Auto_tac;
qed "extend_Co_guar_LeadsTo";

Close_locale "Extend";
