(*  Title:      HOL/UNITY/Extend.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Extending of state sets
  function f (forget)    maps the extended state to the original state
  function g (forgotten) maps the extended state to the "extending part"
*)

(** These we prove OUTSIDE the locale. **)

(*Possibly easier than reasoning about "inv h"*)
val [surj_h,prem] = 
Goalw [good_map_def]
     "[| surj h; !! x x' y y'. h(x,y) = h(x',y') ==> x=x' |] ==> good_map h";
by (safe_tac (claset() addSIs [surj_h]));
by (rtac prem 1);
by (stac (surjective_pairing RS sym) 1);
by (stac (surj_h RS surj_f_inv_f) 1);
by (rtac refl 1);
qed "good_mapI";

Goalw [good_map_def] "good_map h ==> surj h";
by Auto_tac;
qed "good_map_is_surj";

(*A convenient way of finding a closed form for inv h*)
val [surj,prem] = Goalw [inv_def]
     "[| surj h;  !! x y. g (h(x,y)) = x |] ==> fst (inv h z) = g z";
by (res_inst_tac [("y1", "z")] (surj RS surjD RS exE) 1);
by (rtac selectI2 1);
by (dres_inst_tac [("f", "g")] arg_cong 2);
by (auto_tac (claset(), simpset() addsimps [prem]));
qed "fst_inv_equalityI";


Open_locale "Extend";

val slice_def = thm "slice_def";

(*** Trivial properties of f, g, h ***)

val good_h = rewrite_rule [good_map_def] (thm "good_h");
val surj_h = good_h RS conjunct1;

val f_def = thm "f_def";
val g_def = thm "g_def";

Goal "f(h(x,y)) = x";
by (simp_tac (simpset() addsimps [f_def, good_h RS conjunct2]) 1);
qed "f_h_eq";
Addsimps [f_h_eq];

Goal "h(x,y) = h(x',y') ==> x=x'";
by (dres_inst_tac [("f", "fst o inv h")] arg_cong 1);
(*FIXME: If locales worked properly we could put just "f" above*)
by (full_simp_tac (simpset() addsimps [f_def, good_h RS conjunct2]) 1);
qed "h_inject1";
AddSDs [h_inject1];

Goal "h(f z, g z) = z";
by (simp_tac (simpset() addsimps [f_def, g_def, surjective_pairing RS sym,
				  surj_h RS surj_f_inv_f]) 1);
qed "h_f_g_eq";

(*** extend_set: basic properties ***)

Goalw [extend_set_def] "A<=B ==> extend_set h A <= extend_set h B";
by (Blast_tac 1);
qed "extend_set_mono";

Goalw [extend_set_def]
     "z : extend_set h A = (f z : A)";
by (force_tac (claset() addIs  [h_f_g_eq RS sym], simpset()) 1);
qed "mem_extend_set_iff";
AddIffs [mem_extend_set_iff]; 

Goal "{s. P (f s)} = extend_set h {s. P s}";
by Auto_tac;
qed "Collect_eq_extend_set";

Goal "extend_set h {x} = {s. f s = x}";
by Auto_tac;
qed "extend_set_sing";

Goalw [extend_set_def, project_set_def]
     "project_set h (extend_set h C) = C";
by Auto_tac;
qed "extend_set_inverse";
Addsimps [extend_set_inverse];

Goal "inj (extend_set h)";
by (rtac inj_on_inverseI 1);
by (rtac extend_set_inverse 1);
qed "inj_extend_set";

Goalw [extend_set_def] "extend_set h UNIV = UNIV";
by Auto_tac;
by (res_inst_tac [("y1", "x")] (surj_h RS surjD RS exE) 1);
by Auto_tac;
qed "extend_set_UNIV_eq";
Addsimps [standard extend_set_UNIV_eq];

(*** project_set: basic properties ***)

(*project_set is simply image!*)
Goalw [project_set_def] "project_set h C = f `` C";
by (auto_tac (claset() addIs [f_h_eq RS sym, h_f_g_eq RS ssubst], 
	      simpset()));
qed "project_set_eq";

(*Converse appears to fail*)
Goalw [project_set_def] "z : C ==> f z : project_set h C";
by (auto_tac (claset() addIs [h_f_g_eq RS ssubst], 
	      simpset()));
qed "project_set_I";


(*** More laws ***)

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

(*Premise is still undesirably strong, since Domain act can include
  non-reachable states, but it seems necessary for this result.*)
Goalw [extend_act_def, project_set_def, project_act_def]
 "Domain act <= project_set h C ==> project_act C h (extend_act h act) = act";
by (Force_tac 1);
qed "extend_act_inverse";
Addsimps [extend_act_inverse];

Goal "inj (extend_act h)";
by (rtac inj_on_inverseI 1);
by (rtac extend_act_inverse 1);
by (force_tac (claset(), simpset() addsimps [project_set_def]) 1);
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
     "[| (z, z') : act;  z: C |] \
\     ==> (f z, f z') : project_act C h act";
by (auto_tac (claset() addSIs [exI] addIs [h_f_g_eq RS ssubst], 
	      simpset()));
qed "project_act_I";

Goalw [project_set_def, project_act_def]
    "UNIV <= project_set h C ==> project_act C h Id = Id";
by (Force_tac 1);
qed "project_act_Id";

Goalw [project_set_def, project_act_def]
    "Domain (project_act C h act) = project_set h (Domain act Int C)";
by Auto_tac;
by (res_inst_tac [("y1", "ya")] (surj_h RS surjD RS exE) 1);
by Auto_tac;
qed "Domain_project_act";

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

Goalw [project_def] "Init (project C h F) = project_set h (Init F)";
by Auto_tac;
qed "Init_project";

Goal "Acts (extend h F) = (extend_act h `` Acts F)";
by (auto_tac (claset() addSIs [extend_act_Id RS sym], 
	      simpset() addsimps [extend_def, image_iff]));
qed "Acts_extend";

Goal "Acts (project C h F) = insert Id (project_act C h `` Acts F)";
by (auto_tac (claset(), 
	      simpset() addsimps [project_def, image_iff]));
qed "Acts_project";

Addsimps [Init_extend, Init_project, Acts_extend, Acts_project];

Goalw [SKIP_def] "extend h SKIP = SKIP";
by (rtac program_equalityI 1);
by Auto_tac;
qed "extend_SKIP";

Goalw [project_set_def] "UNIV <= project_set h UNIV";
by Auto_tac;
qed "project_set_UNIV";

(*ALL act: Acts F. Domain act is MUCH TOO STRONG since Domain Id = UNIV!*)
Goal "UNIV <= project_set h C \
\     ==> project C h (extend h F) = F";
by (simp_tac (simpset() addsimps [extend_def, project_def]) 1);
by (rtac program_equalityI 1);
by (asm_simp_tac (simpset() addsimps [image_image_eq_UN,
                   subset_UNIV RS subset_trans RS extend_act_inverse]) 2);
by (Simp_tac 1);
qed "extend_inverse";
Addsimps [extend_inverse];

Goal "inj (extend h)";
by (rtac inj_on_inverseI 1);
by (rtac extend_inverse 1);
by (force_tac (claset(), simpset() addsimps [project_set_def]) 1);
qed "inj_extend";

Goal "extend h (F Join G) = extend h F Join extend h G";
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [image_Un]) 2);
by (simp_tac (simpset() addsimps [extend_set_Int_distrib]) 1);
qed "extend_Join";
Addsimps [extend_Join];

Goal "extend h (JOIN I F) = (JN i:I. extend h (F i))";
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [image_UN]) 2);
by (simp_tac (simpset() addsimps [extend_set_INT_distrib]) 1);
qed "extend_JN";
Addsimps [extend_JN];


(** These monotonicity results look natural but are UNUSED **)

Goal "F <= G ==> extend h F <= extend h G";
by (full_simp_tac (simpset() addsimps [component_eq_subset]) 1);
by Auto_tac;
qed "extend_mono";

Goal "F <= G ==> project C h F <= project C h G";
by (full_simp_tac
    (simpset() addsimps [component_eq_subset, project_set_def]) 1);
by Auto_tac;
qed "project_mono";


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


(*** Diff, needed for localTo ***)

Goal "(Diff (extend h G) (extend_act h `` acts)) = extend h (Diff G acts)";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [Diff_def,
				  inj_extend_act RS image_set_diff RS sym]));
qed "Diff_extend_eq";

Goal "(Diff (extend h G) (extend_act h `` acts) \
\         : (extend_set h A) co (extend_set h B)) \
\     = (Diff G acts : A co B)";
by (simp_tac (simpset() addsimps [Diff_extend_eq, extend_constrains]) 1);
qed "Diff_extend_co";

Goal "(Diff (extend h G) (extend_act h `` acts) : stable (extend_set h A)) \
\     = (Diff G acts : stable A)";
by (simp_tac (simpset() addsimps [Diff_extend_co, stable_def]) 1);
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

Goalw [slice_def, project_set_def] "project_set h A = (UN y. slice A y)";
by Auto_tac;
qed "project_set_is_UN_slice";

Goalw [slice_def, transient_def]
    "extend h F : transient A ==> F : transient (slice A y)";
by Auto_tac;
by (rtac bexI 1);
by Auto_tac;
by (force_tac (claset(), simpset() addsimps [extend_act_def]) 1);
qed "extend_transient_slice";

Goal "extend h F : A ensures B ==> F : (slice A y) ensures (project_set h B)";
by (full_simp_tac
    (simpset() addsimps [ensures_def, extend_constrains, extend_transient, 
			 project_set_eq, image_Un RS sym,
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

Goal "ALL y. F : (slice B y) leadsTo CU ==> F : (project_set h B) leadsTo CU";
by (simp_tac (simpset() addsimps [project_set_is_UN_slice]) 1);
by (blast_tac (claset() addIs [leadsTo_UN]) 1);
qed "leadsTo_slice_image";


Goal "extend h F : AU leadsTo BU \
\     ==> ALL y. F : (slice AU y) leadsTo (project_set h BU)";
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


Close_locale "Extend";

(*Close_locale should do this!
Delsimps [f_h_eq, extend_set_inverse, f_image_extend_set, extend_act_inverse,
	  extend_act_Image];
Delrules [make_elim h_inject1];
*)
