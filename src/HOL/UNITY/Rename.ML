(*  Title:      HOL/UNITY/Rename.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

*)

Addsimps [image_inv_f_f, image_surj_f_inv_f];

Goal "bij h ==> good_map (%(x,u). h x)";
by (rtac good_mapI 1);
by (rewrite_goals_tac [bij_def, inj_on_def, surj_def]);
by Auto_tac;
qed "good_map_bij";
Addsimps [good_map_bij];

fun bij_export th = good_map_bij RS export th |> simplify (simpset());

Goalw [bij_def, split_def] "bij h ==> fst (inv (%(x,u). h x) s) = inv h s";
by (Clarify_tac 1);
by (subgoal_tac "surj (%p. h (fst p))" 1);
by (asm_full_simp_tac (simpset() addsimps [surj_def]) 2);
by (etac injD 1);
by (asm_simp_tac (simpset() addsimps [surj_f_inv_f]) 1);
by (etac surj_f_inv_f 1);
qed "fst_o_inv_eq_inv";

Goal "bij h ==> z : h``A = (inv h z : A)";
by (auto_tac (claset() addSIs [image_eqI],
	      simpset() addsimps [bij_is_inj, bij_is_surj RS surj_f_inv_f]));
qed "mem_rename_set_iff";

Goal "extend_set (%(x,u). h x) A = h``A";
by (auto_tac (claset() addSIs [image_eqI],
	      simpset() addsimps [extend_set_def]));
qed "extend_set_eq_image";
Addsimps [extend_set_eq_image];

Goalw [rename_def] "Init (rename h F) = h``(Init F)";
by (Simp_tac 1);
qed "Init_rename";

Addsimps [Init_rename];


(*** inverse properties ***)

Goalw [bij_def]
     "bij h \
\     ==> extend_set (%(x,u::'c). inv h x) = project_set (%(x,u::'c). h x)";
by (rtac ext 1);
by (auto_tac (claset() addSIs [image_eqI], 
	      simpset() addsimps [extend_set_def, project_set_def,
				  surj_f_inv_f]));
qed "extend_set_inv";

(** for "rename" (programs) **)

Goal "bij h \
\     ==> extend_act (%(x,u::'c). inv h x) = project_act (%(x,u::'c). h x)";
by (rtac ext 1);
by (auto_tac (claset() addSIs [image_eqI], 
	      simpset() addsimps [extend_act_def, project_act_def, bij_def,
				  surj_f_inv_f]));
qed "extend_act_inv";

Goal "bij h  \
\     ==> extend (%(x,u::'c). inv h x) = project (%(x,u::'c). h x) UNIV";
by (ftac bij_imp_bij_inv 1);
by (rtac ext 1);
by (rtac program_equalityI 1);
by (asm_simp_tac
    (simpset() addsimps [export project_act_Id, export Acts_extend,
			 insert_Id_image_Acts, extend_act_inv]) 2);
by (asm_simp_tac (simpset() addsimps [extend_set_inv]) 1);
qed "extend_inv";

Goal "bij h ==> rename (inv h) (rename h F) = F";
by (asm_simp_tac (simpset() addsimps [rename_def, extend_inv, 
				      export extend_inverse]) 1);
qed "rename_inv_rename";
Addsimps [rename_inv_rename];

Goal "bij h ==> rename h (rename (inv h) F) = F";
by (ftac bij_imp_bij_inv 1);
by (etac (inv_inv_eq RS subst) 1 THEN etac rename_inv_rename 1);
qed "rename_rename_inv";
Addsimps [rename_rename_inv];

Goal "bij h ==> rename (inv h) = inv (rename h)";
by (rtac (inv_equality RS sym) 1);
by Auto_tac;
qed "rename_inv_eq";

(** (rename h) is bijective <=> h is bijective **)

Goal "bij h ==> inj (rename h)";
by (asm_simp_tac (simpset() addsimps [inj_iff, expand_fun_eq, o_def, 
				      rename_inv_eq RS sym]) 1);
qed "inj_rename";

Goal "bij h ==> surj (rename h)";
by (asm_simp_tac (simpset() addsimps [surj_iff, expand_fun_eq, o_def, 
				      rename_inv_eq RS sym]) 1);
qed "surj_rename";

Goal "bij h ==> bij (rename h)";
by (blast_tac (claset() addIs [bijI, inj_rename, surj_rename]) 1);
qed "bij_rename";

Goalw [inj_on_def] "inj (rename h) ==> inj h";
by Auto_tac;
by (dres_inst_tac [("x", "mk_program ({x}, {})")] spec 1);
by (dres_inst_tac [("x", "mk_program ({y}, {})")] spec 1);
by (auto_tac (claset(), 
	      simpset() addsimps [program_equality_iff, 
                                  rename_def, extend_def]));
qed "inj_rename_imp_inj";

Goalw [surj_def] "surj (rename h) ==> surj h";
by Auto_tac;
by (dres_inst_tac [("x", "mk_program ({y}, {})")] spec 1);
by (auto_tac (claset(), 
	      simpset() addsimps [program_equality_iff, 
                                  rename_def, extend_def]));
qed "surj_rename_imp_surj";

Goalw [bij_def] "bij (rename h) ==> bij h";
by (asm_simp_tac
    (simpset() addsimps [inj_rename_imp_inj, surj_rename_imp_surj]) 1);
qed "bij_rename_imp_bij";

Goal "bij (rename h) = bij h";
by (blast_tac (claset() addIs [bij_rename, bij_rename_imp_bij]) 1);
qed "bij_rename_iff";
AddIffs [bij_rename_iff];

(*** the lattice operations ***)

Goalw [rename_def] "bij h ==> rename h SKIP = SKIP";
by (Asm_simp_tac 1);
qed "rename_SKIP";
Addsimps [rename_SKIP];

Goalw [rename_def]
     "bij h ==> rename h (F Join G) = rename h F Join rename h G";
by (asm_simp_tac (simpset() addsimps [export extend_Join]) 1);
qed "rename_Join";
Addsimps [rename_Join];

Goalw [rename_def] "bij h ==> rename h (JOIN I F) = (JN i:I. rename h (F i))";
by (asm_simp_tac (simpset() addsimps [export extend_JN]) 1);
qed "rename_JN";
Addsimps [rename_JN];


(*** Strong Safety: co, stable ***)

Goalw [rename_def]
     "bij h ==> (rename h F : (h``A) co (h``B)) = (F : A co B)";
by (REPEAT (stac (extend_set_eq_image RS sym) 1));
by (etac (good_map_bij RS export extend_constrains) 1);
qed "rename_constrains";

Goalw [stable_def]
     "bij h ==> (rename h F : stable (h``A)) = (F : stable A)";
by (asm_simp_tac (simpset() addsimps [rename_constrains]) 1);
qed "rename_stable";

Goal "bij h ==> (rename h F : invariant (h``A)) = (F : invariant A)";
by (asm_simp_tac (simpset() addsimps [invariant_def, rename_stable,
				      bij_is_inj RS inj_image_subset_iff]) 1);
qed "rename_invariant";

Goal "bij h ==> (rename h F : increasing func) = (F : increasing (func o h))";
by (asm_simp_tac 
    (simpset() addsimps [increasing_def, rename_stable RS sym,
  		 bij_image_Collect_eq, bij_is_surj RS surj_f_inv_f]) 1);
qed "rename_increasing";


(*** Weak Safety: Co, Stable ***)

Goalw [rename_def]
     "bij h ==> reachable (rename h F) = h `` (reachable F)";
by (asm_simp_tac (simpset() addsimps [export reachable_extend_eq]) 1);
qed "reachable_rename_eq";

Goal "bij h ==> (rename h F : (h``A) Co (h``B)) = (F : A Co B)";
by (asm_simp_tac
    (simpset() addsimps [Constrains_def, reachable_rename_eq, 
			 rename_constrains, bij_is_inj, image_Int RS sym]) 1);
qed "rename_Constrains";

Goalw [Stable_def]
     "bij h ==> (rename h F : Stable (h``A)) = (F : Stable A)";
by (asm_simp_tac (simpset() addsimps [rename_Constrains]) 1);
qed "rename_Stable";

Goal "bij h ==> (rename h F : Always (h``A)) = (F : Always A)";
by (asm_simp_tac (simpset() addsimps [Always_def, rename_Stable,
				      bij_is_inj RS inj_image_subset_iff]) 1);
qed "rename_Always";

Goal "bij h ==> (rename h F : Increasing func) = (F : Increasing (func o h))";
by (asm_simp_tac 
    (simpset() addsimps [Increasing_def, rename_Stable RS sym,
  		 bij_image_Collect_eq, bij_is_surj RS surj_f_inv_f]) 1);
qed "rename_Increasing";


(*** Progress: transient, ensures ***)

Goalw [rename_def]
     "bij h ==> (rename h F : transient (h``A)) = (F : transient A)";
by (stac (extend_set_eq_image RS sym) 1);
by (etac (good_map_bij RS export extend_transient) 1);
qed "rename_transient";

Goalw [rename_def]
     "bij h ==> (rename h F : (h``A) ensures (h``B)) = (F : A ensures B)";
by (REPEAT (stac (extend_set_eq_image RS sym) 1));
by (etac (good_map_bij RS export extend_ensures) 1);
qed "rename_ensures";

Goalw [rename_def]
     "bij h ==> (rename h F : (h``A) leadsTo (h``B)) = (F : A leadsTo B)";
by (REPEAT (stac (extend_set_eq_image RS sym) 1));
by (etac (good_map_bij RS export extend_leadsTo) 1);
qed "rename_leadsTo";

Goalw [rename_def]
     "bij h ==> (rename h F : (h``A) LeadsTo (h``B)) = (F : A LeadsTo B)";
by (REPEAT (stac (extend_set_eq_image RS sym) 1));
by (etac (good_map_bij RS export extend_LeadsTo) 1);
qed "rename_LeadsTo";

Goalw [rename_def]
     "bij h ==> (rename h F : (rename h `` X) guarantees[v o inv h] \
\                             (rename h `` Y)) = \
\               (F : X guarantees[v] Y)";
by (stac (good_map_bij RS export extend_guarantees_eq RS sym) 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [fst_o_inv_eq_inv, o_def]) 1);
qed "rename_rename_guarantees_eq";

Goal "bij h ==> (rename h F : X guarantees[v] Y) = \
\               (F : (rename (inv h) `` X) guarantees[v o h] \
\                    (rename (inv h) `` Y))";
by (stac (rename_rename_guarantees_eq RS sym) 1);
by (assume_tac 1);
by (asm_simp_tac
    (simpset() addsimps [image_eq_UN, o_def, bij_is_surj RS surj_f_inv_f]) 1);
qed "rename_guarantees_eq_rename_inv";

Goal "bij h ==> (rename h G : preserves v) = (G : preserves (v o h))";
by (stac (good_map_bij RS export extend_preserves RS sym) 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [o_def, fst_o_inv_eq_inv, rename_def,
				      bij_is_surj RS surj_f_inv_f]) 1);
qed "rename_preserves";


(*** "image" versions of the rules, for lifting "guarantees" properties ***)


(*Tactic used in all the proofs.  Better would have been to prove one 
  meta-theorem, but how can we handle the polymorphism?  E.g. in 
  rename_constrains the two appearances of "co" have different types!*)
fun rename_image_tac ths =
  EVERY [Auto_tac,
	 (rename_tac "F" 2),
	 (subgoal_tac "EX G. F = rename h G" 2),
	 (auto_tac (claset() addSIs [surj_rename RS surj_f_inv_f RS sym],
	      simpset() addsimps ths))];

Goal "bij h ==> rename h `` (A co B) = (h `` A) co (h``B)";
by (rename_image_tac [rename_constrains]);
qed "rename_image_constrains";

Goal "bij h ==> rename h `` stable A = stable (h `` A)";
by (rename_image_tac [rename_stable]);
qed "rename_image_stable";

Goal "bij h ==> rename h `` increasing func = increasing (func o inv h)";
by (rename_image_tac [rename_increasing, o_def, bij_is_inj]);
qed "rename_image_increasing";

Goal "bij h ==> rename h `` invariant A = invariant (h `` A)";
by (rename_image_tac [rename_invariant]);
qed "rename_image_invariant";

Goal "bij h ==> rename h `` (A Co B) = (h `` A) Co (h``B)";
by (rename_image_tac [rename_Constrains]);
qed "rename_image_Constrains";

Goal "bij h ==> rename h `` Stable A = Stable (h `` A)";
by (rename_image_tac [rename_Stable]);
qed "rename_image_Stable";

Goal "bij h ==> rename h `` Increasing func = Increasing (func o inv h)";
by (rename_image_tac [rename_Increasing, o_def, bij_is_inj]);
qed "rename_image_Increasing";

Goal "bij h ==> rename h `` Always A = Always (h `` A)";
by (rename_image_tac [rename_Always]);
qed "rename_image_Always";

Goal "bij h ==> rename h `` (A leadsTo B) = (h `` A) leadsTo (h``B)";
by (rename_image_tac [rename_leadsTo]);
qed "rename_image_leadsTo";

Goal "bij h ==> rename h `` (A LeadsTo B) = (h `` A) LeadsTo (h``B)";
by (rename_image_tac [rename_LeadsTo]);
qed "rename_image_LeadsTo";
