(*  Title:      HOL/UNITY/Lift_prog.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Arrays of processes. 
*)

Addsimps [insert_map_def, delete_map_def];

Goal "delete_map i (insert_map i x f) = f";
by (rtac ext 1);
by (Simp_tac 1);
qed "insert_map_inverse";

Goal "(insert_map i x (delete_map i g)) = g(i:=x)";
by (rtac ext 1);
by (auto_tac (claset(), simpset() addsplits [nat_diff_split]));
by (cases_tac "d" 1);
by (ALLGOALS Asm_simp_tac);
qed "insert_map_delete_map_eq";

(*** Injectiveness proof ***)

Goal "(insert_map i x f) = (insert_map i y g) ==> x=y";
by (dres_inst_tac [("x","i")] fun_cong 1);
by (Full_simp_tac 1);
qed "insert_map_inject1";

Goal "(insert_map i x f) = (insert_map i y g) ==> f=g";
by (dres_inst_tac [("f", "delete_map i")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [insert_map_inverse]) 1);
qed "insert_map_inject2";

Goal "(insert_map i x f) = (insert_map i y g) ==> x=y & f=g";
by (blast_tac (claset() addDs [insert_map_inject1, insert_map_inject2]) 1);
bind_thm ("insert_map_inject", result() RS conjE);
AddSEs [insert_map_inject];

(*The general case: we don't assume i=i'*)
Goalw [lift_map_def]
     "(lift_map i (s,(f,uu)) = lift_map i' (s',(f',uu'))) \
\     = (uu = uu' & insert_map i s f = insert_map i' s' f')"; 
by Auto_tac;
qed "lift_map_eq_iff";
AddIffs [lift_map_eq_iff];

Goalw [lift_map_def, drop_map_def] "!!s. drop_map i (lift_map i s) = s";
by (force_tac (claset() addIs [insert_map_inverse], simpset()) 1);
qed "drop_map_lift_map_eq";

Goalw [lift_map_def] "inj (lift_map i)";
by (rtac injI 1);
by Auto_tac;
qed "inj_lift_map";

(*** Surjectiveness proof ***)

Goalw [lift_map_def, drop_map_def] "!!s. lift_map i (drop_map i s) = s";
by (force_tac (claset(), simpset() addsimps [insert_map_delete_map_eq]) 1);
qed "lift_map_drop_map_eq";

Goal "(drop_map i s) = (drop_map i s') ==> s=s'";
by (dres_inst_tac [("f", "lift_map i")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [lift_map_drop_map_eq]) 1);
qed "drop_map_inject";
AddSDs [drop_map_inject];

Goal "surj (lift_map i)";
by (rtac surjI 1);
by (rtac lift_map_drop_map_eq 1);
qed "surj_lift_map";

Goal "bij (lift_map i)";
by (simp_tac (simpset() addsimps [bij_def, inj_lift_map, surj_lift_map]) 1);
qed "bij_lift_map";
AddIffs [bij_lift_map];

AddIffs [bij_lift_map RS mem_rename_act_iff];

Goal "inv (lift_map i) = drop_map i";
by (rtac inv_equality 1);
by (rtac lift_map_drop_map_eq 2);
by (rtac drop_map_lift_map_eq 1);
qed "inv_lift_map_eq";
Addsimps [inv_lift_map_eq];

Goal "inv (drop_map i) = lift_map i";
by (rtac inv_equality 1);
by (rtac drop_map_lift_map_eq 2);
by (rtac lift_map_drop_map_eq 1);
qed "inv_drop_map_eq";
Addsimps [inv_drop_map_eq];

Goal "bij (drop_map i)";
by (simp_tac (simpset() delsimps [inv_lift_map_eq]
                        addsimps [inv_lift_map_eq RS sym, bij_imp_bij_inv]) 1);
qed "bij_drop_map";
AddIffs [bij_drop_map];

(*** sub ***)

Goal "sub i f = f i";
by (simp_tac (simpset() addsimps [sub_def]) 1);
qed "sub_apply";
Addsimps [sub_apply];

Goal "lift_set i {s. P s} = {s. P (drop_map i s)}";
by (rtac set_ext 1);
by (asm_simp_tac (simpset() delsimps [image_Collect]
			    addsimps [lift_set_def, rename_set_eq_Collect]) 1);
qed "lift_set_eq_Collect";

Goalw [lift_set_def] "lift_set i {} = {}";
by Auto_tac;
qed "lift_set_empty";
Addsimps [lift_set_empty];

Goalw [lift_set_def] "(lift_map i x : lift_set i A) = (x : A)";
by (rtac (inj_lift_map RS inj_image_mem_iff) 1);
qed "lift_set_iff";
AddIffs [lift_set_iff];

(*Do we really need both this one and its predecessor?*)
Goal "((f,uu) : lift_set i A) = ((f i, (delete_map i f, uu)) : A)";
by (asm_simp_tac (simpset() addsimps [lift_set_def, 
				      mem_rename_set_iff, drop_map_def]) 1);
qed "lift_set_iff2";
AddIffs [lift_set_iff2];

Goalw [lift_set_def] "A<=B ==> lift_set i A <= lift_set i B";
by (etac image_mono 1);
qed "lift_set_mono";

Goalw [lift_set_def] "lift_set i (A Un B) = lift_set i A Un lift_set i B";
by (asm_simp_tac (simpset() addsimps [image_Un]) 1);
qed "lift_set_Un_distrib";

Goalw [lift_set_def] "lift_set i (A-B) = lift_set i A - lift_set i B";
by (rtac (inj_lift_map RS image_set_diff) 1);
qed "lift_set_Diff_distrib";


(*** the lattice operations ***)

Goalw [lift_def] "lift i SKIP = SKIP";
by (Asm_simp_tac 1);
qed "lift_SKIP";
Addsimps [lift_SKIP];

Goalw [lift_def] "lift i (F Join G) = lift i F Join lift i G";
by (Asm_simp_tac 1);
qed "lift_Join";
Addsimps [lift_Join];

Goalw [lift_def] "lift j (JOIN I F) = (JN i:I. lift j (F i))";
by (Asm_simp_tac 1);
qed "lift_JN";
Addsimps [lift_JN];

(*** Safety: co, stable, invariant ***)

Goalw [lift_def, lift_set_def]
     "(lift i F : (lift_set i A) co (lift_set i B)) = (F : A co B)";
by (asm_simp_tac (simpset() addsimps [rename_constrains]) 1);
qed "lift_constrains";

Goalw [lift_def, lift_set_def]
     "(lift i F : stable (lift_set i A)) = (F : stable A)";
by (asm_simp_tac (simpset() addsimps [rename_stable]) 1);
qed "lift_stable";

Goalw [lift_def, lift_set_def]
     "(lift i F : invariant (lift_set i A)) = (F : invariant A)";
by (asm_simp_tac (simpset() addsimps [rename_invariant]) 1);
qed "lift_invariant";

Goalw [lift_def, lift_set_def]
     "(lift i F : (lift_set i A) Co (lift_set i B)) = (F : A Co B)";
by (asm_simp_tac (simpset() addsimps [rename_Constrains]) 1);
qed "lift_Constrains";

Goalw [lift_def, lift_set_def]
     "(lift i F : Stable (lift_set i A)) = (F : Stable A)";
by (asm_simp_tac (simpset() addsimps [rename_Stable]) 1);
qed "lift_Stable";

Goalw [lift_def, lift_set_def]
     "(lift i F : Always (lift_set i A)) = (F : Always A)";
by (asm_simp_tac (simpset() addsimps [rename_Always]) 1);
qed "lift_Always";

(*** Progress: transient, ensures ***)

Goalw [lift_def, lift_set_def]
     "(lift i F : transient (lift_set i A)) = (F : transient A)";
by (asm_simp_tac (simpset() addsimps [rename_transient]) 1);
qed "lift_transient";

Goalw [lift_def, lift_set_def]
     "(lift i F : (lift_set i A) ensures (lift_set i B)) = \
\     (F : A ensures B)";
by (asm_simp_tac (simpset() addsimps [rename_ensures]) 1);
qed "lift_ensures";

Goalw [lift_def, lift_set_def]
     "(lift i F : (lift_set i A) leadsTo (lift_set i B)) = \
\     (F : A leadsTo B)";
by (asm_simp_tac (simpset() addsimps [rename_leadsTo]) 1);
qed "lift_leadsTo";

Goalw [lift_def, lift_set_def]
     "(lift i F : (lift_set i A) LeadsTo (lift_set i B)) =  \
\     (F : A LeadsTo B)";
by (asm_simp_tac (simpset() addsimps [rename_LeadsTo]) 1);
qed "lift_LeadsTo";


(** guarantees **)

Goalw [lift_def]
     "(lift i F : (lift i `` X) guarantees[v o drop_map i] (lift i `` Y)) = \
\     (F : X guarantees[v] Y)";
by (stac (bij_lift_map RS rename_rename_guarantees_eq RS sym) 1);
by (asm_simp_tac (simpset() addsimps [o_def]) 1);
qed "lift_lift_guarantees_eq";

Goal "(lift i F : X guarantees[v] Y) = \
\     (F : (rename (drop_map i) `` X) guarantees[v o lift_map i] \
\          (rename (drop_map i) `` Y))";
by (asm_simp_tac 
    (simpset() addsimps [bij_lift_map RS rename_guarantees_eq_rename_inv,
			 lift_def]) 1);
qed "lift_guarantees_eq_lift_inv";


(*To preserve snd means that the second component is there just to allow
  guarantees properties to be stated.  Converse fails, for lift i F can 
  change function components other than i*)
Goal "F : preserves snd ==> lift i F : preserves snd";
by (dres_inst_tac [("w1", "snd")] (impOfSubs subset_preserves_o) 1);
by (asm_simp_tac (simpset() addsimps [lift_def, rename_preserves]) 1);
by (full_simp_tac (simpset() addsimps [lift_map_def, o_def, split_def]) 1);
qed "lift_preserves_snd_I";

Goal "(delete_map i g) = (delete_map i g') ==> EX x. g = g'(i:=x)";
by (dres_inst_tac [("f", "insert_map i (g i)")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [insert_map_delete_map_eq]) 1);
by (etac exI 1);
bind_thm ("delete_map_eqE", result() RS exE);
AddSEs [delete_map_eqE];

Goal "[| delete_map j g = delete_map j g';  i~=j |] ==> g i = g' i";
by (Force_tac 1);
qed "delete_map_neq_apply";

(*A set of the form (A Times UNIV) ignores the second (dummy) state component*)

Goal "(f o fst) -`` A = (f-``A) Times UNIV";
by Auto_tac;
qed "vimage_o_fst_eq";

Goal "(sub i -``A) Times UNIV = lift_set i (A Times UNIV)";
by Auto_tac;
qed "vimage_sub_eq_lift_set";

Addsimps [vimage_o_fst_eq, vimage_sub_eq_lift_set];

Goal "[| F : preserves snd;  i~=j |] \
\     ==> lift j F : stable (lift_set i (A Times UNIV))";
by (auto_tac (claset(),
	      simpset() addsimps [lift_def, lift_set_def, 
				  stable_def, constrains_def, 
				  mem_rename_act_iff, mem_rename_set_iff]));
by (auto_tac (claset() addSDs [preserves_imp_eq],
	      simpset() addsimps [lift_map_def, drop_map_def]));
by (dres_inst_tac [("x", "i")] fun_cong 1);
by Auto_tac;
qed "preserves_snd_lift_stable";

(*If i~=j then lift j F  does nothing to lift_set i, and the 
  premise ensures A<=B.*)
Goal "[| F i : (A Times UNIV) co (B Times UNIV);  \
\        F j : preserves snd |]  \
\  ==> lift j (F j) : (lift_set i (A Times UNIV)) co (lift_set i (B Times UNIV))";
by (case_tac "i=j" 1);
by (asm_full_simp_tac (simpset() addsimps [lift_def, lift_set_def, 
					   rename_constrains]) 1);
by (etac (preserves_snd_lift_stable RS stableD RS constrains_weaken_R) 1);
by (assume_tac 1);
by (etac (constrains_imp_subset RS lift_set_mono) 1);
qed "constrains_imp_lift_constrains";

(** Lemmas for the transient theorem **)

Goal "(insert_map i t f)(i := s) = insert_map i s f";
by (rtac ext 1);
by Auto_tac;
qed "insert_map_upd_same";

Goal "(insert_map j t f)(i := s) = \
\     (if i=j then insert_map i s f \
\      else if i<j then insert_map j t (f(i:=s)) \
\      else insert_map j t (f(i-1:=s)))";
by (rtac ext 1);
by (auto_tac (claset(), simpset() addsplits [nat_diff_split']));
by (ALLGOALS arith_tac);
qed "insert_map_upd";

Goal "[| insert_map i s f = insert_map j t g;  i~=j |] \
\     ==> EX g'. insert_map i s' f = insert_map j t g'";
by (stac (insert_map_upd_same RS sym) 1);
by (etac ssubst 1);
by (asm_simp_tac (HOL_ss addsimps [insert_map_upd]) 1);
by (Blast_tac 1);
qed "insert_map_eq_diff";

Goalw [lift_map_def]
     "[| lift_map i (s,(f,uu)) = lift_map j (t,(g,vv));  i~=j |] \
\     ==> EX g'. lift_map i (s',(f,uu)) = lift_map j (t,(g',vv))";
by Auto_tac;
by (blast_tac (claset() addDs [insert_map_eq_diff]) 1);
qed "lift_map_eq_diff";

Goal "F : preserves snd \
\     ==> (lift i F : transient (lift_set j (A Times UNIV))) = \
\         (i=j & F : transient (A Times UNIV) | A={})";
by (case_tac "i=j" 1);
by (auto_tac (claset(), simpset() addsimps [lift_transient]));
by (auto_tac (claset(),
	      simpset() addsimps [lift_def, transient_def,
				  Domain_rename_act]));
by (dtac subsetD 1);
by (Blast_tac 1);
by Auto_tac;
ren "s f uu s' f' uu'" 1;
by (subgoal_tac "f'=f & uu'=uu" 1);
by (force_tac (claset() addSDs [preserves_imp_eq], simpset()) 2);
by Auto_tac;
by (dtac sym 1);
by (dtac subsetD 1);
by (rtac ImageI 1);
by (etac rename_actI 1);
by (force_tac (claset(), simpset() addsimps [lift_set_def]) 1);
by (etac (lift_map_eq_diff RS exE) 1);
by (assume_tac 1);
by (dtac ComplD 1);
by (etac notE 1 THEN etac ssubst 1 THEN Fast_tac 1);
qed "lift_transient_eq_disj";

(*USELESS??*)
Goal "lift_map i `` (A Times UNIV) = \
\     (UN s:A. UN f. {insert_map i s f}) Times UNIV";
by (auto_tac (claset() addSIs [bexI, image_eqI],
              simpset() addsimps [lift_map_def]));
by (rtac (split RS sym) 1);
qed "lift_map_image_Times";

Goal "(lift i F : preserves v) = (F : preserves (v o lift_map i))";
by (simp_tac (simpset() addsimps [lift_def, rename_preserves]) 1);
qed "lift_preserves_eq";

(*A useful rewrite.  If o, sub have been rewritten out already then can also
  use it as   rewrite_rule [sub_def, o_def] lift_preserves_sub*)
Goal "F : preserves snd \
\     ==> lift i F : preserves (v o sub j o fst) = \
\         (if i=j then F : preserves (v o fst) else True)";
by (dtac (impOfSubs subset_preserves_o) 1);
by (full_simp_tac (simpset() addsimps [lift_preserves_eq, o_def,
				       drop_map_lift_map_eq]) 1);
by (asm_simp_tac (simpset() delcongs [if_weak_cong]
			    addsimps [lift_map_def, 
				      eq_commute, split_def, o_def]) 1);
by Auto_tac;
qed "lift_preserves_sub";


(*** Lemmas to handle function composition (o) more consistently ***)

(*Lets us prove one version of a theorem and store others*)
Goal "f o g = h ==> f' o f o g = f' o h";
by (asm_full_simp_tac (simpset() addsimps [expand_fun_eq, o_def]) 1);
qed "o_equiv_assoc";

Goal "f o g = h ==> ALL x. f(g x) = h x";
by (asm_full_simp_tac (simpset() addsimps [expand_fun_eq, o_def]) 1);
qed "o_equiv_apply";

fun make_o_equivs th = 
    [th, 
     th RS o_equiv_assoc |> simplify (HOL_ss addsimps [o_assoc]), 
     th RS o_equiv_apply |> simplify (HOL_ss addsimps [o_def, sub_def])];

Addsimps (make_o_equivs fst_o_funPair @ make_o_equivs snd_o_funPair);

Goal "sub i o fst o lift_map i = fst";
by (rtac ext 1);
by (auto_tac (claset(), simpset() addsimps [o_def, lift_map_def, sub_def]));
qed "fst_o_lift_map";

Goal "snd o lift_map i = snd o snd";
by (rtac ext 1);
by (auto_tac (claset(), simpset() addsimps [o_def, lift_map_def]));
qed "snd_o_lift_map";

Addsimps (make_o_equivs fst_o_lift_map @ make_o_equivs snd_o_lift_map);



