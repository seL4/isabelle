(*  Title:      HOL/UNITY/Project.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Projections of state sets (also of actions and programs)

Inheritance of GUARANTEES properties under extension

POSSIBLY CAN DELETE Restrict_image_Diff
*)

Open_locale "Extend";

(** projection: monotonicity for safety **)

Goal "D <= C ==> \
\     project_act h (Restrict D act) <= project_act h (Restrict C act)";
by (auto_tac (claset(), simpset() addsimps [project_act_def]));
qed "project_act_mono";

Goal "[| D <= C; project h C F : A co B |] ==> project h D F : A co B";
by (auto_tac (claset(), simpset() addsimps [constrains_def]));
by (dtac project_act_mono 1);
by (Blast_tac 1);
qed "project_constrains_mono";

Goal "[| D <= C;  project h C F : stable A |] ==> project h D F : stable A";
by (asm_full_simp_tac
    (simpset() addsimps [stable_def, project_constrains_mono]) 1);
qed "project_stable_mono";

Goal "F : A co B ==> project h C (extend h F) : A co B";
by (auto_tac (claset(), 
      simpset() addsimps [extend_act_def, project_act_def, constrains_def]));
qed "project_extend_constrains_I";

Goal "UNIV <= project_set h C \
\     ==> project h C ((extend h F) Join G) = F Join (project h C G)";
by (rtac program_equalityI 1);
by (asm_simp_tac (simpset() addsimps [image_eq_UN, UN_Un,
			subset_UNIV RS subset_trans RS Restrict_triv]) 2);
by (simp_tac (simpset() addsimps [project_set_extend_set_Int]) 1);
qed "project_extend_Join";

Goal "UNIV <= project_set h C \
\     ==> (extend h F) Join G = extend h H ==> H = F Join (project h C G)";
by (dres_inst_tac [("f", "project h C")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [project_extend_Join]) 1);
qed "extend_Join_eq_extend_D";


(** Safety **)

Goalw [constrains_def]
     "(project h C F : A co B)  =  \
\     (F : (C Int extend_set h A) co (extend_set h B) & A <= B)";
by (auto_tac (claset() addSIs [project_act_I], simpset() addsimps [ball_Un]));
by (force_tac (claset() addSIs [project_act_I] addSDs [subsetD], simpset()) 1);
(*the <== direction*)
by (rewtac project_act_def);
by (force_tac (claset() addSDs [subsetD], simpset()) 1);
qed "project_constrains";

Goalw [stable_def]
     "(project h UNIV F : stable A) = (F : stable (extend_set h A))";
by (simp_tac (simpset() addsimps [project_constrains]) 1);
qed "project_stable";

Goal "F : stable (extend_set h A) ==> project h C F : stable A";
by (dtac (project_stable RS iffD2) 1);
by (blast_tac (claset() addIs [project_stable_mono]) 1);
qed "project_stable_I";

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
					   Collect_eq_extend_set RS sym]) 1);
qed "project_increasing_I";

Goal "(F Join project h UNIV G : increasing func)  =  \
\     (extend h F Join G : increasing (func o f))";
by (rtac iffI 1);
by (etac project_increasing_I 2);
by (asm_full_simp_tac 
    (simpset() addsimps [increasing_def, Join_project_stable]) 1);
by (auto_tac (claset(),
	      simpset() addsimps [Join_stable, Collect_eq_extend_set RS sym,
				  extend_stable RS iffD1]));
qed "Join_project_increasing";

(*The UNIV argument is essential*)
Goal "F Join project h UNIV G : A co B \
\     ==> extend h F Join G : extend_set h A co extend_set h B";
by (asm_full_simp_tac
    (simpset() addsimps [project_constrains, Join_constrains, 
			 extend_constrains]) 1);
qed "project_constrains_D";

(** "projecting" and union/intersection (no converses) **)

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

(*The extra generality in the first premise allows guarantees with STRONG
  preconditions (localT) and WEAK postconditions.*)
(*LOCALTO NO LONGER EXISTS: replace C by reachable...??*)
Goalw [Constrains_def]
     "[| reachable (extend h F Join G) <= C;    \
\        F Join project h C G : A Co B |] \
\     ==> extend h F Join G : (extend_set h A) Co (extend_set h B)";
by (full_simp_tac (simpset() addsimps [Join_project_constrains]) 1);
by (Clarify_tac 1);
by (etac constrains_weaken 1);
by (auto_tac (claset() addDs [reachable_imp_reachable_project], simpset()));
qed "project_Constrains_D";

Goalw [Stable_def]
     "[| reachable (extend h F Join G) <= C;  \
\        F Join project h C G : Stable A |]   \
\     ==> extend h F Join G : Stable (extend_set h A)";
by (asm_simp_tac (simpset() addsimps [project_Constrains_D]) 1);
qed "project_Stable_D";

Goalw [Always_def]
     "[| reachable (extend h F Join G) <= C;  \
\        F Join project h C G : Always A |]   \
\     ==> extend h F Join G : Always (extend_set h A)";
by (force_tac (claset() addIs [reachable.Init],
               simpset() addsimps [project_Stable_D, split_extended_all]) 1);
qed "project_Always_D";

Goalw [Increasing_def]
     "[| reachable (extend h F Join G) <= C;  \
\        F Join project h C G : Increasing func |] \
\     ==> extend h F Join G : Increasing (func o f)";
by Auto_tac;
by (stac Collect_eq_extend_set 1);
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

(*Perhaps should replace C by reachable...*)
Goalw [Constrains_def]
     "[| C <= reachable (extend h F Join G);  \
\        extend h F Join G : (extend_set h A) Co (extend_set h B) |] \
\     ==> F Join project h C G : A Co B";
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
\     ==> F Join project h C G : Stable A";
by (asm_simp_tac (simpset() addsimps [project_Constrains_I]) 1);
qed "project_Stable_I";

Goalw [Always_def]
     "[| C <= reachable (extend h F Join G);  \
\        extend h F Join G : Always (extend_set h A) |]   \
\     ==> F Join project h C G : Always A";
by (auto_tac (claset(), simpset() addsimps [project_Stable_I]));
by (rewtac extend_set_def);
by (Blast_tac 1);
qed "project_Always_I";

Goalw [Increasing_def]
     "[| C <= reachable (extend h F Join G);  \
\        extend h F Join G : Increasing (func o f) |] \
\     ==> F Join project h C G : Increasing func";
by Auto_tac;
by (asm_simp_tac (simpset() addsimps [Collect_eq_extend_set RS sym,
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

val [prem] = 
Goalw [extending_def]
     "(!!G. reachable (extend h F Join G) <= C G)  \
\     ==> extending v C h F (Increasing (func o f)) (Increasing func)";
by (blast_tac (claset() addIs [prem RS project_Increasing_D]) 1);
qed "extending_Increasing";


(** Progress includes safety in the definition of ensures **)

(*** Progress for (project h C F) ***)

(** transient **)

(*Premise is that C includes the domains of all actions that could be the
  transient one.  Could have C=UNIV of course*)
Goalw [transient_def]
     "[| ALL act: Acts F. act ^^ extend_set h A <= - extend_set h A --> \
\                      Domain act <= C;    \
\        F : transient (extend_set h A) |] \
\     ==> project h C F : transient A";
by (auto_tac (claset() delrules [ballE],
              simpset() addsimps [Domain_project_act, Int_absorb1]));
by (REPEAT (ball_tac 1));
by (auto_tac (claset(),
              simpset() addsimps [extend_set_def, project_act_def]));
by (ALLGOALS Blast_tac);
qed "transient_extend_set_imp_project_transient";


(** ensures **)

(*For simplicity, the complicated condition on C is eliminated
  NOT SURE THIS IS GOOD FOR ANYTHING: CAN'T PROVE LEADSTO THEOREM*)
Goal "F : (extend_set h A) ensures (extend_set h B) \
\     ==> project h UNIV F : A ensures B";
by (asm_full_simp_tac
    (simpset() addsimps [ensures_def, project_constrains, 
			 transient_extend_set_imp_project_transient,
			 extend_set_Un_distrib RS sym, 
			 extend_set_Diff_distrib RS sym]) 1);
by (Blast_tac 1);
qed "ensures_extend_set_imp_project_ensures";

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

(** Lemma useful for both STRONG and WEAK progress*)

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
qed "project_leadsTo_lemma";

Goal "[| C = (reachable (extend h F Join G)); \
\        ALL D. project h C G : transient D --> D={};  \
\        F Join project h C G : A LeadsTo B |] \
\     ==> extend h F Join G : (extend_set h A) LeadsTo (extend_set h B)";
by (asm_full_simp_tac 
    (simpset() addsimps [LeadsTo_def, project_leadsTo_lemma, 
			 project_set_reachable_extend_eq]) 1);
qed "Join_project_LeadsTo";


(*** GUARANTEES and EXTEND ***)

(** preserves **)

Goal "G : preserves (v o f) ==> project h C G : preserves v";
by (auto_tac (claset(),
	      simpset() addsimps [preserves_def, project_stable_I,
				  Collect_eq_extend_set RS sym]));
qed "project_preserves_I";

(*to preserve f is to preserve the whole original state*)
Goal "G : preserves f ==> project h C G : preserves id";
by (asm_simp_tac (simpset() addsimps [project_preserves_I]) 1);
qed "project_preserves_id_I";

Goal "(extend h G : preserves (v o f)) = (G : preserves v)";
by (auto_tac (claset(),
	      simpset() addsimps [preserves_def, extend_stable RS sym,
				  Collect_eq_extend_set RS sym]));
qed "extend_preserves";

Goal "inj h ==> (extend h G : preserves g)";
by (auto_tac (claset(),
	      simpset() addsimps [preserves_def, extend_def, extend_act_def, 
				  stable_def, constrains_def, g_def]));
qed "inj_extend_preserves";

(** Strong precondition and postcondition; doesn't seem very useful. **)

Goal "F : X guarantees[v] Y ==> \
\     extend h F : (extend h `` X) guarantees[v o f] (extend h `` Y)";
by (rtac guaranteesI 1);
by Auto_tac;
by (blast_tac (claset() addIs [project_preserves_I]
			addDs [project_set_UNIV RS equalityD2 RS 
			       extend_Join_eq_extend_D, 
			       guaranteesD]) 1);
qed "guarantees_imp_extend_guarantees";

Goal "extend h F : (extend h `` X) guarantees[v o f] (extend h `` Y) \
\     ==> F : X guarantees[v] Y";
by (auto_tac (claset(), simpset() addsimps [guar_def]));
by (dres_inst_tac [("x", "extend h G")] spec 1);
by (asm_full_simp_tac 
    (simpset() delsimps [extend_Join] 
           addsimps [extend_Join RS sym, extend_preserves,
		     inj_extend RS inj_image_mem_iff]) 1);
qed "extend_guarantees_imp_guarantees";

Goal "(extend h F : (extend h `` X) guarantees[v o f] (extend h `` Y)) = \
\    (F : X guarantees[v] Y)";
by (blast_tac (claset() addIs [guarantees_imp_extend_guarantees,
			       extend_guarantees_imp_guarantees]) 1);
qed "extend_guarantees_eq";


(*Weak precondition and postcondition; this is the good one!
  Not clear that it has a converse [or that we want one!]*)

(*The raw version*)
val [xguary,project,extend] =
Goal "[| F : X guarantees[v] Y;  \
\        !!G. extend h F Join G : X' ==> F Join project h C G : X;  \
\        !!G. [| F Join project h C G : Y; extend h F Join G : X' |] \
\             ==> extend h F Join G : Y' |] \
\     ==> extend h F : X' guarantees[v o f] Y'";
by (rtac (xguary RS guaranteesD RS extend RS guaranteesI) 1);
by (etac project_preserves_I 1);
by (etac project 1);
by (assume_tac 1);
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
by (res_inst_tac [("C1", "UNIV")] (project_leadsTo_lemma RS leadsTo_weaken) 1);
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
