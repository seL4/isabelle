(*  Title:      HOL/UNITY/Project.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Projections of state sets (also of actions and programs)

Inheritance of GUARANTEES properties under extension
*)

Open_locale "Extend";

Goalw [restr_def] "Init (restr C h F) = Init F";
by Auto_tac;
qed "Init_restr";

Goalw [restr_act_def, extend_act_def, project_act_def]
     "((x,x') : restr_act C h act) = ((x,x') : act & (EX y. h(x,y) : C))";
by (Blast_tac 1);
qed "restr_act_iff";
Addsimps [restr_act_iff];

Goal "Acts (restr C h F) = insert Id (restr_act C h `` Acts F)";
by (auto_tac (claset(), 
	      simpset() addsimps [restr_def, symmetric restr_act_def, 
				  image_image_eq_UN]));
qed "Acts_restr";

Addsimps [Init_restr, Acts_restr];

(*The definitions are RE-ORIENTED*)
Addsimps [symmetric restr_act_def, symmetric restr_def];

Goal "project C h ((extend h F) Join G) = (restr C h F) Join (project C h G)";
by (rtac program_equalityI 1);
by (asm_simp_tac (simpset() addsimps [symmetric restr_act_def,
				      image_Un, image_image]) 2);
by (simp_tac (simpset() addsimps [project_set_extend_set_Int]) 1);
qed "project_extend_Join_restr";

Goalw [project_set_def]
 "Domain act <= project_set h C ==> restr_act C h act = act";
by (Force_tac 1);
qed "restr_act_ident";
Addsimps [restr_act_ident];

Goal "F : A co B ==> restr C h F : A co B";
by (auto_tac (claset(), simpset() addsimps [constrains_def]));
by (Blast_tac 1);
qed "restr_constrains";

Goal "F : stable A ==> restr C h F : stable A";
by (asm_full_simp_tac (simpset() addsimps [stable_def, restr_constrains]) 1);
qed "restr_stable";

Goal "UNIV <= project_set h C ==> restr C h F = F";
by (rtac program_equalityI 1);
by (force_tac (claset(),
	       simpset() addsimps [image_def,
                   subset_UNIV RS subset_trans RS restr_act_ident]) 2);
by (Simp_tac 1);
qed "restr_ident";

(*Ideally, uses of this should be eliminated.  But often we see it re-oriented
  as project_extend_Join RS sym*)
Goal "UNIV <= project_set h C \
\     ==> project C h ((extend h F) Join G) = F Join (project C h G)";
by (asm_simp_tac (simpset() addsimps [project_extend_Join_restr, 
				      restr_ident]) 1);
qed "project_extend_Join";

Goal "UNIV <= project_set h C \
\     ==> (extend h F) Join G = extend h H ==> H = F Join (project C h G)";
by (dres_inst_tac [("f", "project C h")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [project_extend_Join_restr, 
					   restr_ident]) 1);
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
qed "Diff_project_co";

Goalw [stable_def]
     "[| (UN act:acts. Domain act) <= project_set h C; \
\        Diff G (extend_act h `` acts) : stable (extend_set h A) |] \
\     ==> Diff (project C h G) acts : stable A";
by (etac Diff_project_co 1);
by (assume_tac 1);
qed "Diff_project_stable";

(*Converse appears to fail*)
Goal "[| UNIV <= project_set h C;  (H : (func o f) localTo extend h G) |] \
\     ==> (project C h H : func localTo G)";
by (asm_full_simp_tac 
    (simpset() addsimps [localTo_def, 
			 project_extend_Join RS sym,
			 subset_UNIV RS subset_trans RS Diff_project_stable,
			 Collect_eq_extend_set RS sym]) 1);
qed "project_localTo_I";


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

(*A super-strong condition: G is not allowed to affect the
  shared variables at all.*)
Goal "[| ALL x. project UNIV h G ~: transient {x};  \
\        F Join project UNIV h G : A ensures B |] \
\     ==> extend h F Join G : (extend_set h A) ensures (extend_set h B)";
by (case_tac "A <= B" 1);
by (etac (extend_set_mono RS subset_imp_ensures) 1);
by (asm_full_simp_tac
    (simpset() addsimps [ensures_def, extend_constrains, extend_transient, 
			 extend_set_Un_distrib RS sym, 
			 extend_set_Diff_distrib RS sym,
			 Join_transient, Join_constrains,
			 project_constrains, Int_absorb1]) 1);
by (blast_tac (claset() addIs [transient_strengthen]) 1);
qed_spec_mp "Join_project_ensures";

Goal "[| ALL x. project UNIV h G ~: transient {x};  \
\        F Join project UNIV h G : A leadsTo B |] \
\     ==> extend h F Join G : (extend_set h A) leadsTo (extend_set h B)";
by (etac leadsTo_induct 1);
by (asm_simp_tac (simpset() addsimps [leadsTo_UN, extend_set_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (blast_tac (claset() addIs [leadsTo_Basis, Join_project_ensures]) 1);
qed "Join_project_leadsTo_I";


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
by (rtac guaranteesI 1);
by (auto_tac (claset(), simpset() addsimps [guar_def, component_def]));
by (dtac spec 1);
by (dtac (mp RS mp) 1);
by (Blast_tac 2);
by (blast_tac (claset() addSDs [inj_extend RS inj_image_mem_iff RS iffD1]) 2);
by Auto_tac;
qed "extend_guarantees_imp_guarantees";

Goal "(extend h F : (extend h `` X) guarantees (extend h `` Y)) = \
\    (F : X guarantees Y)";
by (blast_tac (claset() addIs [guarantees_imp_extend_guarantees,
			       extend_guarantees_imp_guarantees]) 1);
qed "extend_guarantees_eq";


(*Weak precondition and postcondition; this is the good one!
  Not clear that it has a converse [or that we want one!]*)
val [xguary,project,extend] =
Goal "[| F : X guarantees Y;  \
\        !!G. extend h F Join G : X' ==> F Join proj G h G : X;  \
\        !!G. [| F Join proj G h G : Y; extend h F Join G : X'; \
\                Disjoint (extend h F) G |] \
\             ==> extend h F Join G : Y' |] \
\     ==> extend h F : X' guarantees Y'";
by (rtac (xguary RS guaranteesD RS extend RS guaranteesI) 1);
by (etac project 1);
by (assume_tac 1);
by (assume_tac 1);
qed "project_guarantees";

(** It seems that neither "guarantees" law can be proved from the other. **)


(*** guarantees corollaries ***)

Goal "F : UNIV guarantees increasing func \
\     ==> extend h F : UNIV guarantees increasing (func o f)";
by (etac project_guarantees 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [Join_project_increasing RS sym])));
qed "extend_guar_increasing";

Goal "F : UNIV guarantees Increasing func \
\     ==> extend h F : UNIV guarantees Increasing (func o f)";
by (etac project_guarantees 1);
by (rtac (subset_UNIV RS project_Increasing_D) 2);
by Auto_tac;
qed "extend_guar_Increasing";

Goal "F : (func localTo G) guarantees increasing func  \
\     ==> extend h F : (func o f) localTo (extend h G)  \
\                      guarantees increasing (func o f)";
by (etac project_guarantees 1);
(*the "increasing" guarantee*)
by (asm_simp_tac
    (simpset() addsimps [Join_project_increasing RS sym]) 2);
(*the "localTo" requirement*)
by (stac (project_set_UNIV RS project_extend_Join RS sym) 1);
by (asm_simp_tac 
    (simpset() addsimps [project_set_UNIV RS project_localTo_I]) 1);
qed "extend_localTo_guar_increasing";

Goal "F : (func localTo G) guarantees Increasing func  \
\     ==> extend h F : (func o f) localTo (extend h G)  \
\                      guarantees Increasing (func o f)";
by (etac project_guarantees 1);
(*the "Increasing" guarantee*)
by (etac (subset_UNIV RS project_Increasing_D) 2);
(*the "localTo" requirement*)
by (stac (project_set_UNIV RS project_extend_Join RS sym) 1);
by (asm_simp_tac 
    (simpset() addsimps [project_set_UNIV RS project_localTo_I]) 1);
qed "extend_localTo_guar_Increasing";


(** Guarantees with a leadsTo postcondition **)

Goal "[| G : f localTo extend h F; \
\        Disjoint (extend h F) G |] ==> project UNIV h G : stable {x}";
by (asm_full_simp_tac
    (simpset() addsimps [localTo_imp_stable,
			 extend_set_sing, project_stable]) 1);
qed "localTo_imp_project_stable";


Goal "F : stable{s} ==> F ~: transient {s}";
by (auto_tac (claset(), 
	      simpset() addsimps [FP_def, transient_def,
				  stable_def, constrains_def]));
qed "stable_sing_imp_not_transient";

Goal "F : (A co A') guarantees (B leadsTo B')  \
\ ==> extend h F : ((extend_set h A) co (extend_set h A'))  \
\                   Int (f localTo (extend h F)) \
\                  guarantees ((extend_set h B) leadsTo (extend_set h B'))";
by (etac project_guarantees 1);
(*the safety precondition*)
by (stac (project_set_UNIV RS project_extend_Join RS sym) 1);
by (asm_full_simp_tac
    (simpset() addsimps [project_constrains, Join_constrains, 
			 extend_constrains]) 1);
by (fast_tac (claset() addDs [constrains_imp_subset]) 1);
(*the liveness postcondition*)
by (rtac Join_project_leadsTo_I 1);
by Auto_tac;
by (asm_full_simp_tac
    (simpset() addsimps [Join_localTo, self_localTo,
			 localTo_imp_project_stable, 
			 stable_sing_imp_not_transient]) 1);
qed "extend_co_guar_leadsTo";

Close_locale "Extend";
