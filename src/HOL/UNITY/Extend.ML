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
     "(h(x,y)) : extend_set h A = (x : A)";
by Auto_tac;
qed "mem_extend_set_iff";
AddIffs [mem_extend_set_iff]; 

Goal "inj (extend_set h)";
by (rtac injI 1);
by (rewtac extend_set_def);
by (etac equalityE 1);
by (blast_tac (claset() addSDs [inj_h RS inj_image_mem_iff RS iffD1]) 1);
qed "inj_extend_set";

Goalw [extend_set_def]
    "extend_set h (A Un B) = extend_set h A Un extend_set h B";
by Auto_tac;
qed "extend_set_Un_distrib";

Goalw [extend_set_def]
    "extend_set h (A Int B) = extend_set h A Int extend_set h B";
by Auto_tac;
qed "extend_set_Int_distrib";

Goalw [extend_set_def]
    "extend_set h (INTER A B) = (INT x:A. extend_set h (B x))";
by (force_tac (claset() addIs  [h_f_g_eq RS sym], simpset()) 1);
qed "extend_set_INT_distrib";

Goalw [extend_set_def]
    "extend_set h (A - B) = extend_set h A - extend_set h B";
by Auto_tac;
qed "extend_set_Diff_distrib";

Goalw [extend_set_def] "extend_set h (Union A) = (UN X:A. extend_set h X)";
by (Blast_tac 1);
qed "extend_set_Union";

Goalw [extend_set_def]
     "(extend_set h A <= - extend_set h B) = (A <= - B)";
by Auto_tac;
qed "extend_set_subset_Compl_eq";


Goalw [extend_set_def] "f `` extend_set h A = A";
by Auto_tac;
by (blast_tac (claset() addIs [f_h_eq RS sym]) 1);
qed "f_image_extend_set";
Addsimps [f_image_extend_set];


(*** extend_act ***)

Goalw [extend_act_def]
     "((h(s,y), h(s',y)) : extend_act h act) = ((s, s') : act)";
by Auto_tac;
qed "mem_extend_act_iff";
AddIffs [mem_extend_act_iff]; 

Goal "inj (extend_act h)";
by (rtac injI 1);
by (rewtac extend_act_def);
by (force_tac (claset() addSEs [equalityE]
			addIs  [h_f_g_eq RS sym], 
	       simpset()) 1);
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

Goalw [extend_set_def, extend_act_def]
    "extend_act h Id = Id";
by (force_tac (claset() addIs  [h_f_g_eq RS sym], simpset()) 1);
qed "extend_act_Id";
Addsimps [extend_act_Id];

Goal "Id : extend_act h `` Acts F";
by (auto_tac (claset() addSIs [extend_act_Id RS sym], 
	      simpset() addsimps [image_iff]));
qed "Id_mem_extend_act";


(**** extend ****)

(*** Basic properties ***)

Goalw [extend_set_def, extend_def]
     "Init (extend h F) = extend_set h (Init F)";
by Auto_tac;
qed "Init_extend";

Goal "Acts (extend h F) = (extend_act h `` Acts F)";
by (auto_tac (claset() addSIs [extend_act_Id RS sym], 
	      simpset() addsimps [extend_def, image_iff]));
qed "Acts_extend";

Addsimps [Init_extend, Acts_extend];

Goalw [SKIP_def] "extend h SKIP = SKIP";
by (rtac program_equalityI 1);
by (auto_tac (claset() addIs  [h_f_g_eq RS sym], 
	      simpset() addsimps [extend_set_def]));
qed "extend_SKIP";
Addsimps [extend_SKIP];

Goal "inj (extend h)";
by (rtac injI 1);
by (rewtac extend_def);
by (etac program_equalityE 1);
by (full_simp_tac
    (simpset() addsimps [inj_extend_set RS inj_eq,
			 inj_extend_act RS inj_image_eq_iff,
			 Id_mem_extend_act RS insert_absorb]) 1);
by (blast_tac (claset() addIs [program_equalityI]) 1);
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

(** Substitution Axiom versions: Co, Stable **)

Goal "p : reachable (extend h F) ==> f p : reachable F";
by (etac reachable.induct 1);
by (auto_tac
    (claset() addIs reachable.intrs,
     simpset() addsimps [extend_set_def, extend_act_def, image_iff]));
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

Goal "F : X guar Y ==> extend h F : (extend h `` X) guar (extend h `` Y)";
by (rtac guaranteesI 1);
by Auto_tac;
by (blast_tac (claset() addDs [extend_Join_eq_extend_D, guaranteesD]) 1);
qed "guarantees_imp_extend_guarantees";

Goal "extend h F : (extend h `` X) guar (extend h `` Y) ==> F : X guar Y";
by (rtac guaranteesI 1);
by (rewrite_goals_tac [guarantees_def, component_def]);
by Auto_tac;
by (dtac spec 1);
by (dtac (mp RS mp) 1);
by (Blast_tac 2);
by (blast_tac (claset() addSDs [inj_extend RS inj_image_mem_iff RS iffD1]) 2);
by Auto_tac;
qed "extend_guarantees_imp_guarantees";

Goal "(extend h F : (extend h `` X) guar (extend h `` Y)) = (F : X guar Y)";
by (blast_tac (claset() addIs [guarantees_imp_extend_guarantees,
			       extend_guarantees_imp_guarantees]) 1);
qed "extend_guarantees_eq";


Close_locale "Extend";
