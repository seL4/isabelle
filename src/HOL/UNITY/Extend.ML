(*  Title:      HOL/UNITY/Extend.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Extending of state sets
  function f (forget)    maps the extended state to the original state
  function g (forgotten) maps the extended state to the "extending part"

*)

Open_locale "Extend";

val slice_def = thm "slice_def";
val f_act_def = thm "f_act_def";

(*** Trivial properties of f, g, h ***)

val inj_h = thm "inj_h";
val surj_h = thm "surj_h";
Addsimps [inj_h, inj_h RS inj_eq, surj_h];

val f_def = thm "f_def";
val g_def = thm "g_def";

Goal "f(h(x,y)) = x";
by (simp_tac (simpset() addsimps [f_def]) 1);
qed "f_h_eq";
Addsimps [f_h_eq];

Goal "g(h(x,y)) = y";
by (simp_tac (simpset() addsimps [g_def]) 1);
qed "g_h_eq";
Addsimps [g_h_eq];

Goal "h(f z, g z) = z";
by (cut_inst_tac [("y", "z")] (surj_h RS surjD) 1);
by Auto_tac;
qed "h_f_g_eq";


(*** extend_set: basic properties ***)

Goalw [extend_set_def]
     "z : extend_set h A = (f z : A)";
by (force_tac (claset() addIs  [h_f_g_eq RS sym], simpset()) 1);
qed "mem_extend_set_iff";
AddIffs [mem_extend_set_iff]; 

(*Converse appears to fail*)
Goalw [project_set_def] "z : C ==> f z : project_set h C";
by (auto_tac (claset() addIs [h_f_g_eq RS ssubst], 
	      simpset()));
qed "project_set_I";

Goalw [extend_set_def, project_set_def] "project_set h (extend_set h F) = F";
by Auto_tac;
qed "extend_set_inverse";
Addsimps [extend_set_inverse];

Goal "inj (extend_set h)";
by (rtac inj_on_inverseI 1);
by (rtac extend_set_inverse 1);
qed "inj_extend_set";

(*Because A and B could differ on the "other" part of the state, 
   cannot generalize result to 
      project_set h (A Int B) = project_set h A Int project_set h B
*)
Goalw [project_set_def]
     "project_set h ((extend_set h A) Int B) = A Int (project_set h B)";
by Auto_tac;
qed "project_set_extend_set_Int";

Goal "extend_set h (A Un B) = extend_set h A Un extend_set h B";
by Auto_tac;
qed "extend_set_Un_distrib";

Goal "extend_set h (A Int B) = extend_set h A Int extend_set h B";
by Auto_tac;
qed "extend_set_Int_distrib";

Goal "extend_set h (INTER A B) = (INT x:A. extend_set h (B x))";
by Auto_tac;
qed "extend_set_INT_distrib";

Goal "extend_set h (A - B) = extend_set h A - extend_set h B";
by Auto_tac;
qed "extend_set_Diff_distrib";

Goal "extend_set h (Union A) = (UN X:A. extend_set h X)";
by (Blast_tac 1);
qed "extend_set_Union";

Goalw [extend_set_def] "(extend_set h A <= - extend_set h B) = (A <= - B)";
by Auto_tac;
qed "extend_set_subset_Compl_eq";

Goalw [extend_set_def] "f `` extend_set h A = A";
by Auto_tac;
by (blast_tac (claset() addIs [f_h_eq RS sym]) 1);
qed "f_image_extend_set";
Addsimps [f_image_extend_set];


(*** project_set: basic properties ***)

Goalw [project_set_def] "project_set h C = f `` C";
by (auto_tac (claset() addIs [f_h_eq RS sym, h_f_g_eq RS ssubst], 
	      simpset()));
qed "project_set_eq";


(*** extend_act ***)

(*Actions could affect the g-part, so result Cannot be strengthened to
   ((z, z') : extend_act h act) = ((f z, f z') : act)
*)
Goalw [extend_act_def]
     "((h(s,y), h(s',y)) : extend_act h act) = ((s, s') : act)";
by Auto_tac;
qed "mem_extend_act_iff";
AddIffs [mem_extend_act_iff]; 

Goalw [extend_act_def]
     "(z, z') : extend_act h act ==> (f z, f z') : act";
by Auto_tac;
qed "extend_act_D";

Goalw [extend_act_def, project_act_def]
     "project_act h (extend_act h act) = act";
by Auto_tac;
by (Blast_tac 1);
qed "extend_act_inverse";
Addsimps [extend_act_inverse];

Goal "inj (extend_act h)";
by (rtac inj_on_inverseI 1);
by (rtac extend_act_inverse 1);
qed "inj_extend_act";

Goalw [extend_set_def, extend_act_def]
     "extend_act h act ^^ (extend_set h A) = extend_set h (act ^^ A)";
by (Force_tac 1);
qed "extend_act_Image";
Addsimps [extend_act_Image];

Goalw [extend_set_def, extend_act_def]
    "(extend_set h A <= extend_set h B) = (A <= B)";
by (Force_tac 1);
qed "extend_set_strict_mono";
Addsimps [extend_set_strict_mono];

Goalw [extend_set_def, extend_act_def]
    "Domain (extend_act h act) = extend_set h (Domain act)";
by (Force_tac 1);
qed "Domain_extend_act"; 

Goalw [extend_act_def]
    "extend_act h Id = Id";
by (force_tac (claset() addIs  [h_f_g_eq RS sym], simpset()) 1);
qed "extend_act_Id";

Goalw [project_act_def]
     "(z, z') : act ==> (f z, f z') : project_act h act";
by (auto_tac (claset() addSIs [exI] addIs [h_f_g_eq RS ssubst], 
	      simpset()));
qed "project_act_I";

Goalw [project_set_def, project_act_def]
    "project_act h Id = Id";
by (Force_tac 1);
qed "project_act_Id";

Addsimps [extend_act_Id, project_act_Id];

Goal "Id : extend_act h `` Acts F";
by (auto_tac (claset() addSIs [extend_act_Id RS sym], 
	      simpset() addsimps [image_iff]));
qed "Id_mem_extend_act";


(**** extend ****)

(*** Basic properties ***)

Goalw [extend_def] "Init (extend h F) = extend_set h (Init F)";
by Auto_tac;
qed "Init_extend";

Goalw [project_def] "Init (project h F) = project_set h (Init F)";
by Auto_tac;
qed "Init_project";

Goal "Acts (extend h F) = (extend_act h `` Acts F)";
by (auto_tac (claset() addSIs [extend_act_Id RS sym], 
	      simpset() addsimps [extend_def, image_iff]));
qed "Acts_extend";

Goal "Acts (project h F) = (project_act h `` Acts F)";
by (auto_tac (claset() addSIs [project_act_Id RS sym], 
	      simpset() addsimps [project_def, image_iff]));
qed "Acts_project";

Addsimps [Init_extend, Init_project, Acts_extend, Acts_project];

Goalw [SKIP_def] "extend h SKIP = SKIP";
by (rtac program_equalityI 1);
by Auto_tac;
qed "extend_SKIP";

Goalw [SKIP_def] "project h SKIP = SKIP";
by (rtac program_equalityI 1);
by (auto_tac (claset() addIs  [h_f_g_eq RS sym], 
	      simpset() addsimps [project_set_def]));
qed "project_SKIP";

Goal "project h (extend h F) = F";
by (simp_tac (simpset() addsimps [extend_def, project_def]) 1);
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [image_compose RS sym, o_def]) 2);
by (Simp_tac 1);
qed "extend_inverse";
Addsimps [extend_inverse];

Goal "inj (extend h)";
by (rtac inj_on_inverseI 1);
by (rtac extend_inverse 1);
qed "inj_extend";

Goal "extend h (F Join G) = extend h F Join extend h G";
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [image_Un, Acts_Join]) 2);
by (simp_tac (simpset() addsimps [extend_set_Int_distrib]) 1);
qed "extend_Join";
Addsimps [extend_Join];

Goal "extend h (JOIN I F) = (JN i:I. extend h (F i))";
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [image_UN, Acts_JN]) 2);
by (simp_tac (simpset() addsimps [extend_set_INT_distrib]) 1);
qed "extend_JN";
Addsimps [extend_JN];


(*** Safety: co, stable ***)

Goal "(extend h F : (extend_set h A) co (extend_set h B)) = \
\     (F : A co B)";
by (simp_tac (simpset() addsimps [constrains_def]) 1);
qed "extend_constrains";

Goal "(extend h F : stable (extend_set h A)) = (F : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, extend_constrains]) 1);
qed "extend_stable";

Goal "(extend h F : invariant (extend_set h A)) = (F : invariant A)";
by (asm_simp_tac (simpset() addsimps [invariant_def, extend_stable]) 1);
qed "extend_invariant";

(** Safety and project **)

Goalw [constrains_def]
     "(project h F : A co B)  =  (F : (extend_set h A) co (extend_set h B))";
by Auto_tac;
by (force_tac (claset(), simpset() addsimps [project_act_def]) 2);
by (auto_tac (claset() addSIs [project_act_I], simpset()));
qed "project_constrains";

Goal "(project h F : stable A)  =  (F : stable (extend_set h A))";
by (simp_tac (simpset() addsimps [stable_def, project_constrains]) 1);
qed "project_stable";


(*** Diff, needed for localTo ***)

Goal "Diff G (extend_act h `` Acts F) : (extend_set h A) co (extend_set h B)  \
\     ==> Diff (project h G) (Acts F) : A co B";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, Diff_def]));
by (dtac bspec 1);
by (Force_tac 1);
by (auto_tac (claset(), simpset() addsimps [project_act_def]));
by (Force_tac 1);
qed "Diff_project_co";

Goalw [stable_def]
     "Diff G (extend_act h `` Acts F) : stable (extend_set h A)  \
\     ==> Diff (project h G) (Acts F) : stable A";
by (etac Diff_project_co 1);
qed "Diff_project_stable";

Goal "Diff G (Acts F) : A co B  \
\     ==> Diff (extend h G) (extend_act h `` Acts F) \
\         : (extend_set h A) co (extend_set h B)";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, Diff_def]));
by (blast_tac (claset() addDs [extend_act_D]) 1);
qed "Diff_extend_co";

Goalw [stable_def]
   "Diff G (Acts F) : stable A  \
\   ==> Diff (extend h G) (extend_act h `` Acts F) : stable (extend_set h A)";
by (etac Diff_extend_co 1);
qed "Diff_extend_stable";


(*** Weak safety primitives: Co, Stable ***)

Goal "p : reachable (extend h F) ==> f p : reachable F";
by (etac reachable.induct 1);
by (auto_tac
    (claset() addIs reachable.intrs,
     simpset() addsimps [extend_act_def, image_iff]));
qed "reachable_extend_f";

Goal "h(s,y) : reachable (extend h F) ==> s : reachable F";
by (force_tac (claset() addSDs [reachable_extend_f], simpset()) 1);
qed "h_reachable_extend";

Goalw [extend_set_def]
     "reachable (extend h F) = extend_set h (reachable F)";
by (rtac equalityI 1);
by (force_tac (claset() addIs  [h_f_g_eq RS sym]
			addSDs [reachable_extend_f], 
	       simpset()) 1);
by (Clarify_tac 1);
by (etac reachable.induct 1);
by (ALLGOALS (force_tac (claset() addIs reachable.intrs, 
			 simpset())));
qed "reachable_extend_eq";

Goal "(extend h F : (extend_set h A) Co (extend_set h B)) =  \
\     (F : A Co B)";
by (simp_tac
    (simpset() addsimps [Constrains_def, reachable_extend_eq, 
			 extend_constrains, extend_set_Int_distrib RS sym]) 1);
qed "extend_Constrains";

Goal "(extend h F : Stable (extend_set h A)) = (F : Stable A)";
by (simp_tac (simpset() addsimps [Stable_def, extend_Constrains]) 1);
qed "extend_Stable";

Goal "(extend h F : Always (extend_set h A)) = (F : Always A)";
by (asm_simp_tac (simpset() addsimps [Always_def, extend_Stable]) 1);
qed "extend_Always";


(** Reachability and project **)

Goal "z : reachable F ==> f z : reachable (project h F)";
by (etac reachable.induct 1);
by (force_tac (claset() addIs [reachable.Acts, project_act_I],
	       simpset()) 2);
by (force_tac (claset() addIs [reachable.Init, project_set_I],
	       simpset()) 1);
qed "reachable_imp_reachable_project";

(*Converse fails (?) *)
Goalw [Constrains_def]
     "project h F : A Co B ==> F : (extend_set h A) Co (extend_set h B)";
by (full_simp_tac (simpset() addsimps [project_constrains]) 1);
by (etac constrains_weaken_L 1);
by (auto_tac (claset() addDs [reachable_imp_reachable_project], simpset()));
qed "project_Constrains_D";

Goalw [Stable_def]
     "project h F : Stable A ==> F : Stable (extend_set h A)";
by (asm_simp_tac (simpset() addsimps [project_Constrains_D]) 1);
qed "project_Stable_D";


(*** Programs of the form  ((extend h F) Join G)
     in other words programs containing an extended component ***)

Goal "project h ((extend h F) Join G) = F Join (project h G)";
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [Acts_Join, image_Un,
				  image_compose RS sym, o_def]) 2);
by (simp_tac (simpset() addsimps [project_set_extend_set_Int]) 1);
qed "project_extend_Join";

Goal "(extend h F) Join G = extend h H ==> H = F Join (project h G)";
by (dres_inst_tac [("f", "project h")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [project_extend_Join]) 1);
by (etac sym 1);
qed "extend_Join_eq_extend_D";

Goal "z : reachable (extend h F Join G)  \
\     ==> f z : reachable (F Join project h G)";
by (etac reachable.induct 1);
by (force_tac (claset() addIs [reachable.Init, project_set_I], simpset()) 1);
(*By case analysis on whether the action is of extend h F  or  G*)
by (rtac reachable.Acts 1);
by (etac project_act_I 3);
by (auto_tac (claset(), simpset() addsimps [Acts_Join]));
qed "reachable_extend_Join_D";

(*Opposite inclusion fails, even for the initial state: extend_set h includes
  ALL functions determined only by their value at h.*)
Goal "reachable (extend h F Join G) <= \
\     extend_set h (reachable (F Join project h G))";
by Auto_tac;
by (etac reachable_extend_Join_D 1);
qed "reachable_extend_Join_subset";

Goalw [Constrains_def]
     "F Join project h G : A Co B    \
\     ==> extend h F Join G : (extend_set h A) Co (extend_set h B)";
by (subgoal_tac 
    "extend h F Join G : extend_set h (reachable (F Join project h G)) Int \
\                           extend_set h A \
\    co extend_set h B" 1);
by (asm_full_simp_tac 
    (simpset() addsimps [extend_set_Int_distrib RS sym,
			 extend_constrains,
			 project_constrains RS sym,
			 project_extend_Join]) 2);
by (blast_tac (claset() addIs [constrains_weaken, 
			       reachable_extend_Join_D]) 1);
qed "extend_Join_Constrains";

Goal "F Join project h G : Stable A    \
\     ==> extend h F Join G : Stable (extend_set h A)";
by (asm_full_simp_tac (simpset() addsimps [Stable_def, 
					   extend_Join_Constrains]) 1);
qed "extend_Join_Stable";


(*** Progress: transient, ensures ***)

Goal "(extend h F : transient (extend_set h A)) = (F : transient A)";
by (auto_tac (claset(),
	      simpset() addsimps [transient_def, extend_set_subset_Compl_eq,
				  Domain_extend_act]));
qed "extend_transient";

Goal "(extend h F : (extend_set h A) ensures (extend_set h B)) = \
\     (F : A ensures B)";
by (simp_tac
    (simpset() addsimps [ensures_def, extend_constrains, extend_transient, 
			 extend_set_Un_distrib RS sym, 
			 extend_set_Diff_distrib RS sym]) 1);
qed "extend_ensures";

Goal "F : A leadsTo B \
\     ==> extend h F : (extend_set h A) leadsTo (extend_set h B)";
by (etac leadsTo_induct 1);
by (asm_simp_tac (simpset() addsimps [leadsTo_UN, extend_set_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (asm_simp_tac (simpset() addsimps [leadsTo_Basis, extend_ensures]) 1);
qed "leadsTo_imp_extend_leadsTo";

(*** Proving the converse takes some doing! ***)

Goalw [slice_def] "slice (Union S) y = (UN x:S. slice x y)";
by Auto_tac;
qed "slice_Union";

Goalw [slice_def] "slice (extend_set h A) y = A";
by Auto_tac;
qed "slice_extend_set";

Goalw [slice_def] "f``A = (UN y. slice A y)";
by Auto_tac;
by (blast_tac (claset() addIs [f_h_eq RS sym]) 2);
by (best_tac (claset() addIs [h_f_g_eq RS ssubst]) 1);
qed "image_is_UN_slice";

Goalw [slice_def, transient_def]
    "extend h F : transient A ==> F : transient (slice A y)";
by Auto_tac;
by (rtac bexI 1);
by Auto_tac;
by (force_tac (claset(), simpset() addsimps [extend_act_def]) 1);
qed "extend_transient_slice";

Goal "extend h F : A ensures B ==> F : (slice A y) ensures (f `` B)";
by (full_simp_tac
    (simpset() addsimps [ensures_def, extend_constrains, extend_transient, 
			 image_Un RS sym,
			 extend_set_Un_distrib RS sym, 
			 extend_set_Diff_distrib RS sym]) 1);
by Safe_tac;
by (full_simp_tac (simpset() addsimps [constrains_def, extend_act_def, 
				       extend_set_def]) 1);
by (Clarify_tac 1);
by (ball_tac 1); 
by (full_simp_tac (simpset() addsimps [slice_def, image_iff, Image_iff]) 1);
by (force_tac (claset() addSIs [h_f_g_eq RS sym], simpset()) 1);
(*transient*)
by (dtac extend_transient_slice 1);
by (etac transient_strengthen 1);
by (force_tac (claset() addIs [f_h_eq RS sym], 
	       simpset() addsimps [slice_def]) 1);
qed "extend_ensures_slice";

Goal "ALL y. F : (slice B y) leadsTo CU ==> F : (f `` B) leadsTo CU";
by (simp_tac (simpset() addsimps [image_is_UN_slice]) 1);
by (blast_tac (claset() addIs [leadsTo_UN]) 1);
qed "leadsTo_slice_image";


Goal "extend h F : AU leadsTo BU \
\     ==> ALL y. F : (slice AU y) leadsTo (f `` BU)";
by (etac leadsTo_induct 1);
by (full_simp_tac (simpset() addsimps [slice_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_UN]) 3);
by (blast_tac (claset() addIs [leadsTo_slice_image, leadsTo_Trans]) 2);
by (blast_tac (claset() addIs [extend_ensures_slice, leadsTo_Basis]) 1);
qed_spec_mp "extend_leadsTo_slice";

Goal "(extend h F : (extend_set h A) leadsTo (extend_set h B)) = \
\     (F : A leadsTo B)";
by Safe_tac;
by (etac leadsTo_imp_extend_leadsTo 2);
by (dtac extend_leadsTo_slice 1);
by (full_simp_tac (simpset() addsimps [slice_extend_set]) 1);
qed "extend_leadsto";

Goal "(extend h F : (extend_set h A) LeadsTo (extend_set h B)) =  \
\     (F : A LeadsTo B)";
by (simp_tac
    (simpset() addsimps [LeadsTo_def, reachable_extend_eq, 
			 extend_leadsto, extend_set_Int_distrib RS sym]) 1);
qed "extend_LeadsTo";


(*** guarantees properties ***)

Goalw [f_act_def, extend_act_def] "f_act (extend_act h act1) = act1";
by (force_tac
    (claset() addSIs [rev_bexI],
     simpset() addsimps [image_iff]) 1);
qed "f_act_extend_act";
Addsimps [f_act_extend_act];

Goalw [extend_set_def]
     "f `` (extend_set h A Int B) = (f `` extend_set h A) Int (f``B)";
by (force_tac (claset() addIs  [h_f_g_eq RS sym], simpset()) 1);
qed "image_extend_set_Int_eq";

Goal "(extend h F) Join G = extend h H ==> EX J. H = F Join J";
by (etac program_equalityE 1);
by (auto_tac (claset(), simpset() addsimps [Acts_Join]));
by (res_inst_tac [("x", "mk_program(f``(Init G), f_act``Acts G)")] exI 1);
by (rtac program_equalityI 1);
(*Init*)
by (REPEAT (dres_inst_tac [("f", "op `` f")] arg_cong 1));
by (asm_full_simp_tac (simpset() addsimps [image_extend_set_Int_eq]) 1);
(*Now for the Actions*)
by (dres_inst_tac [("f", "op `` f_act")] arg_cong 1);
by (asm_full_simp_tac 
    (simpset() addsimps [Acts_Join, image_Un, image_compose RS sym, o_def]) 1);
qed "extend_Join_eq_extend_D";

(** Strong precondition and postcondition; doesn't seem very useful. **)

Goal "F : X guarantees Y ==> \
\     extend h F : (extend h `` X) guarantees (extend h `` Y)";
by (rtac guaranteesI 1);
by Auto_tac;
by (blast_tac (claset() addDs [extend_Join_eq_extend_D, guaranteesD]) 1);
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
  Not clear that it has a converse [or that we want one!]
  Can trivially satisfy the constraint on X by taking X = project h `` XX*)
val [xguary,project,extend] =
Goal "[| F : X guarantees Y;  \
\        !!H. H : XX ==> project h H : X;  \
\        !!G. F Join project h G : Y ==> extend h F Join G : YY |] \
\     ==> extend h F : XX guarantees YY";
by (rtac (xguary RS guaranteesD RS extend RS guaranteesI) 1);
by (dtac project 1);
by (full_simp_tac (simpset() addsimps [project_extend_Join]) 1);
qed "project_guarantees";

(** It seems that neither "guarantees" law can be proved from the other. **)



(*** guarantees corollaries ***)

Goal "{s. P (f s)} = extend_set h {s. P s}";
by Auto_tac;
qed "Collect_eq_extend_set";

Goalw [increasing_def]
     "F : UNIV guarantees increasing func \
\     ==> extend h F : UNIV guarantees increasing (func o f)";
by (etac project_guarantees 1);
by Auto_tac;
by (stac Collect_eq_extend_set 1); 
by (asm_full_simp_tac
    (simpset() addsimps [extend_stable, project_stable, 
			 stable_Join]) 1);
qed "extend_guar_increasing";

Goalw [Increasing_def]
     "F : UNIV guarantees Increasing func \
\     ==> extend h F : UNIV guarantees Increasing (func o f)";
by (etac project_guarantees 1);
by Auto_tac;
by (stac Collect_eq_extend_set 1); 
by (asm_simp_tac (simpset() addsimps [extend_Join_Stable]) 1);
qed "extend_guar_Increasing";

Goalw [localTo_def, increasing_def]
     "F : (func localTo F) guarantees increasing func  \
\     ==> extend h F : (func o f) localTo (extend h F)  \
\                         guarantees increasing (func o f)";
by (etac project_guarantees 1);
by Auto_tac;
by (stac Collect_eq_extend_set 2); 
(*the "increasing" guarantee*)
by (asm_full_simp_tac
    (simpset() addsimps [extend_stable, project_stable, 
			 stable_Join]) 2);
(*the "localTo" requirement*)
by (asm_simp_tac
    (simpset() addsimps [Diff_project_stable, 
			 Collect_eq_extend_set RS sym]) 1); 
qed "extend_localTo_guar_increasing";

Goalw [localTo_def, Increasing_def]
     "F : (func localTo F) guarantees Increasing func  \
\     ==> extend h F : (func o f) localTo (extend h F)  \
\                         guarantees Increasing (func o f)";
by (etac project_guarantees 1);
by Auto_tac;
by (stac Collect_eq_extend_set 2); 
(*the "Increasing" guarantee*)
by (asm_simp_tac (simpset() addsimps [extend_Join_Stable]) 2);
(*the "localTo" requirement*)
by (asm_simp_tac
    (simpset() addsimps [Diff_project_stable, 
			 Collect_eq_extend_set RS sym]) 1); 
qed "extend_localTo_guar_Increasing";

Close_locale "Extend";
