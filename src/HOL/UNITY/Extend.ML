(*  Title:      HOL/UNITY/Extend.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Extending of state sets
  function f (forget)    maps the extended state to the original state
  function g (forgotten) maps the extended state to the "extending part"
*)

(** These we prove OUTSIDE the locale. **)


(****************UNITY.ML****************)
Goalw [stable_def, constrains_def] "stable UNIV = UNIV";
by Auto_tac;
qed "stable_UNIV";
Addsimps [stable_UNIV];


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

Goalw [extend_set_def]
     "z : extend_set h A = (f z : A)";
by (force_tac (claset() addIs  [h_f_g_eq RS sym], simpset()) 1);
qed "mem_extend_set_iff";
AddIffs [mem_extend_set_iff]; 

Goal "{s. P (f s)} = extend_set h {s. P s}";
by Auto_tac;
qed "Collect_eq_extend_set";

Goalw [extend_set_def, project_set_def]
     "project_set h (extend_set h F) = F";
by Auto_tac;
qed "extend_set_inverse";
Addsimps [extend_set_inverse];

Goal "inj (extend_set h)";
by (rtac inj_on_inverseI 1);
by (rtac extend_set_inverse 1);
qed "inj_extend_set";

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
Goalw [extend_act_def,project_set_def, project_act_def]
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
     "[| (z, z') : act;  f z = f z' | z: C |] \
\     ==> (f z, f z') : project_act C h act";
by (auto_tac (claset() addSIs [exI] addIs [h_f_g_eq RS ssubst], 
	      simpset()));
qed "project_act_I";

Goalw [project_set_def, project_act_def]
    "project_act C h Id = Id";
by (Force_tac 1);
qed "project_act_Id";

(*premise can be weakened*)
Goalw [project_set_def, project_act_def]
    "Domain act <= C \
\    ==> Domain (project_act C h act) = project_set h (Domain act)";
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

Goal "Acts (project C h F) = (project_act C h `` Acts F)";
by (auto_tac (claset() addSIs [project_act_Id RS sym], 
	      simpset() addsimps [project_def, image_iff]));
qed "Acts_project";

Addsimps [Init_extend, Init_project, Acts_extend, Acts_project];

Goalw [SKIP_def] "extend h SKIP = SKIP";
by (rtac program_equalityI 1);
by Auto_tac;
qed "extend_SKIP";

Goalw [SKIP_def] "project C h SKIP = SKIP";
by (rtac program_equalityI 1);
by (auto_tac (claset() addIs  [h_f_g_eq RS sym], 
	      simpset() addsimps [project_set_def]));
qed "project_SKIP";

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

Goal "UNIV <= project_set h C \
\     ==> project C h ((extend h F) Join G) = F Join (project C h G)";
by (rtac program_equalityI 1);
by (asm_simp_tac (simpset() addsimps [image_Un, image_image_eq_UN,
                   subset_UNIV RS subset_trans RS extend_act_inverse]) 2);
by (simp_tac (simpset() addsimps [project_set_extend_set_Int]) 1);
qed "project_extend_Join";

Goal "UNIV <= project_set h C \
\     ==> (extend h F) Join G = extend h H ==> H = F Join (project C h G)";
by (dres_inst_tac [("f", "project C h")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [project_extend_Join]) 1);
qed "extend_Join_eq_extend_D";


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
     "(F Join project C h G : A co B)  =  \
\       (extend h F Join G : (C Int extend_set h A) co (extend_set h B) &  \
\        F : A co B)";
by (auto_tac (claset() addSIs [project_act_I], simpset() addsimps [ball_Un]));
by (force_tac (claset() addIs [extend_act_D], simpset()) 1);
by (force_tac (claset() addSIs [project_act_I] addSDs [subsetD], simpset()) 1);
(*the <== direction*)
by (ball_tac 1);
by (rewtac project_act_def);
by Auto_tac;
by (force_tac (claset() addSDs [Id_in_Acts RSN (2,bspec)], simpset()) 1);
by (force_tac (claset() addSDs [subsetD], simpset()) 1);
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

Goal "(project C h F : A co B)  =  \
\     (F : (C Int extend_set h A) co (extend_set h B) & A <= B)";
by (cut_inst_tac [("F", "SKIP")] Join_project_constrains 1);
by (asm_full_simp_tac (simpset() addsimps [extend_SKIP]) 1);
qed "project_constrains";


(*** Diff, needed for localTo ***)

(** project versions **)

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

(** extend versions **)

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

(*Converse appears to fail*)
Goal "[| UNIV <= project_set h C;  (H : (func o f) localTo extend h G) |] \
\     ==> (project C h H : func localTo G)";
by (asm_full_simp_tac 
    (simpset() addsimps [localTo_def, 
			 project_extend_Join RS sym,
			 subset_UNIV RS subset_trans RS Diff_project_stable,
			 Collect_eq_extend_set RS sym]) 1);
qed "project_localTo_I";


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

Goal "[| reachable (extend h F Join G) <= C;  \
\        z : reachable (extend h F Join G) |] \
\     ==> f z : reachable (F Join project C h G)";
by (etac reachable.induct 1);
by (force_tac (claset() delrules [Id_in_Acts]
		        addIs [reachable.Acts, project_act_I, extend_act_D],
	       simpset()) 2);
by (force_tac (claset() addIs [reachable.Init, project_set_I],
	       simpset()) 1);
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
  Not clear that it has a converse [or that we want one!] 
  Can generalize project (C G) to the function variable "proj"*)
val [xguary,project,extend] =
Goal "[| F : X guarantees Y;  \
\        !!G. extend h F Join G : X' ==> F Join project (C G) h G : X;  \
\        !!G. F Join project (C G) h G : Y ==> extend h F Join G : Y' |] \
\     ==> extend h F : X' guarantees Y'";
by (rtac (xguary RS guaranteesD RS extend RS guaranteesI) 1);
by (etac project 1);
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

Close_locale "Extend";

(*Close_locale should do this!
Delsimps [f_h_eq, extend_set_inverse, f_image_extend_set, extend_act_inverse,
	  extend_act_Image];
Delrules [make_elim h_inject1];
*)
