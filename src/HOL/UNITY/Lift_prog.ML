(*  Title:      HOL/UNITY/Lift_prog.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Arrays of processes.  Many results are instances of those in Extend & Project.
*)


(*** Basic properties ***)

(** lift_set and drop_set **)

Goalw [lift_set_def] "(f : lift_set i A) = (f i : A)";
by Auto_tac;
qed "lift_set_iff";
AddIffs [lift_set_iff];

Goalw [lift_set_def] "lift_set i A Int lift_set i B = lift_set i (A Int B)";
by Auto_tac;
qed "Int_lift_set";

Goalw [lift_set_def] "lift_set i A Un lift_set i B = lift_set i (A Un B)";
by Auto_tac;
qed "Un_lift_set";

Goalw [lift_set_def] "lift_set i A - lift_set i B = lift_set i (A-B)";
by Auto_tac;
qed "Diff_lift_set";

Addsimps [Int_lift_set, Un_lift_set, Diff_lift_set];

(*Converse fails*)
Goalw [drop_set_def] "f : A ==> f i : drop_set i A";
by Auto_tac;
qed "drop_set_I";

(** lift_act and drop_act **)

Goalw [lift_act_def] "lift_act i Id = Id";
by Auto_tac;
by (etac rev_mp 1);
by (dtac sym 1);
by (asm_simp_tac (simpset() addsimps [fun_upd_idem_iff]) 1);
qed "lift_act_Id";
Addsimps [lift_act_Id];

(*For compatibility with the original definition and perhaps simpler proofs*)
Goalw [lift_act_def]
    "((f,f') : lift_act i act) = (EX s'. f' = f(i := s') & (f i, s') : act)";
by Auto_tac;
by (rtac exI 1);
by Auto_tac;
qed "lift_act_eq";
AddIffs [lift_act_eq];

Goalw [drop_set_def, drop_act_def]
     "UNIV <= drop_set i C ==> drop_act i (Restrict C Id) = Id";
by (Blast_tac 1);
qed "drop_act_Id";
Addsimps [drop_act_Id];

(** lift_prog and drop_prog **)

Goalw [lift_prog_def] "Init (lift_prog i F) = lift_set i (Init F)";
by Auto_tac;
qed "Init_lift_prog";
Addsimps [Init_lift_prog];

Goalw [lift_prog_def] "Acts (lift_prog i F) = lift_act i `` Acts F";
by (auto_tac (claset() addIs [Id_in_Acts RSN (2,image_eqI)], simpset()));
qed "Acts_lift_prog";
Addsimps [Acts_lift_prog];

Goalw [drop_prog_def] "Init (drop_prog C i F) = drop_set i (Init F)";
by Auto_tac;
qed "Init_drop_prog";
Addsimps [Init_drop_prog];

Goal "Acts (drop_prog C i F) = insert Id (drop_act i `` Restrict C `` Acts F)";
by (auto_tac (claset() addIs [Id_in_Acts RSN (2,image_eqI)], 
	      simpset() addsimps [drop_prog_def]));
qed "Acts_drop_prog";
Addsimps [Acts_drop_prog];


(*** sub ***)

Addsimps [sub_def];

Goal "lift_set i {s. P s} = {s. P (sub i s)}";
by (asm_simp_tac (simpset() addsimps [lift_set_def]) 1);
qed "lift_set_sub";

Goal "{s. P (s i)} = lift_set i {s. P s}";
by (asm_simp_tac (simpset() addsimps [lift_set_def]) 1);
qed "Collect_eq_lift_set";

Goal "sub i -`` A = lift_set i A";
by (Force_tac 1);
qed "sub_vimage";
Addsimps [sub_vimage];



(*** lift_prog and the lattice operations ***)

Goal "lift_prog i SKIP = SKIP";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [SKIP_def, lift_prog_def]));
qed "lift_prog_SKIP";

Goal "lift_prog i (F Join G) = (lift_prog i F) Join (lift_prog i G)";
by (rtac program_equalityI 1);
by Auto_tac;
qed "lift_prog_Join";

Goal "lift_prog i (JOIN J F) = (JN j:J. lift_prog i (F j))";
by (rtac program_equalityI 1);
by Auto_tac;
qed "lift_prog_JN";


(*** Equivalence with "extend" version ***)

Goalw [lift_map_def] "good_map (lift_map i)";
by (rtac good_mapI 1);
by (res_inst_tac [("f", "%f. (f i, f)")] surjI 1);
by Auto_tac;
by (dres_inst_tac [("f", "%f. f i")] arg_cong 1);
by Auto_tac;
qed "good_map_lift_map";

fun lift_export th = good_map_lift_map RS export th;

Goal "fst (inv (lift_map i) g) = g i";
by (rtac (good_map_lift_map RS good_map_is_surj RS fst_inv_equalityI) 1);
by (auto_tac (claset(), simpset() addsimps [lift_map_def]));
qed "fst_inv_lift_map";
Addsimps [fst_inv_lift_map];


Goal "lift_set i A = extend_set (lift_map i) A";
by (auto_tac (claset(), 
     simpset() addsimps [lift_export mem_extend_set_iff]));
qed "lift_set_correct";

Goalw [drop_set_def, project_set_def, lift_map_def]
     "drop_set i A = project_set (lift_map i) A";
by Auto_tac;
by (rtac image_eqI 2);
by (rtac exI 1);
by (stac (refl RS fun_upd_idem) 1);
by Auto_tac;
qed "drop_set_correct";

Goal "lift_act i = extend_act (lift_map i)";
by (rtac ext 1);
by Auto_tac;
by (forward_tac [lift_export extend_act_D] 2);
by (auto_tac (claset(), simpset() addsimps [extend_act_def]));
by (auto_tac (claset(), simpset() addsimps [extend_act_def, lift_map_def]));
by (rtac bexI 1);
by (auto_tac (claset() addSIs [exI], simpset()));
qed "lift_act_correct";

Goal "drop_act i = project_act (lift_map i)";
by (rtac ext 1);
by (rewrite_goals_tac [project_act_def, drop_act_def, lift_map_def]);
by Auto_tac;
by (REPEAT_FIRST (ares_tac [exI, conjI]));
by Auto_tac;
by (REPEAT_FIRST (assume_tac ORELSE' stac (refl RS fun_upd_idem)));
qed "drop_act_correct";

Goal "lift_prog i = extend (lift_map i)";
by (rtac (program_equalityI RS ext) 1);
by (simp_tac (simpset() addsimps [lift_set_correct]) 1);
by (simp_tac (simpset() 
	      addsimps [lift_export Acts_extend, 
			lift_act_correct]) 1);
qed "lift_prog_correct";

Goal "drop_prog C i = project C (lift_map i)";
by (rtac (program_equalityI RS ext) 1);
by (simp_tac (simpset() addsimps [drop_set_correct]) 1);
by (simp_tac (simpset() 
	      addsimps [Acts_project, drop_act_correct]) 1);
qed "drop_prog_correct";


(** Injectivity of lift_set, lift_act, lift_prog **)

Goalw [lift_set_def, drop_set_def] "drop_set i (lift_set i F) = F";
by Auto_tac;
qed "lift_set_inverse";
Addsimps [lift_set_inverse];

Goal "inj (lift_set i)";
by (rtac inj_on_inverseI 1);
by (rtac lift_set_inverse 1);
qed "inj_lift_set";

(*Because A and B could differ outside i, cannot generalize result to 
   drop_set i (A Int B) = drop_set i A Int drop_set i B
*)
Goalw [lift_set_def, drop_set_def]
     "drop_set i ((lift_set i A) Int B) = A Int (drop_set i B)";
by Auto_tac;
qed "drop_set_Int_lift_set";

Goalw [lift_set_def, drop_set_def]
     "drop_set i (B Int (lift_set i A)) = (drop_set i B) Int A";
by Auto_tac;
qed "drop_set_Int_lift_set2";

Goalw [drop_set_def]
     "i : I ==> drop_set i (INT j:I. lift_set j A) = A";
by Auto_tac;
qed "drop_set_INT";

Goal "lift_set i UNIV = UNIV";
by (simp_tac
    (simpset() addsimps [lift_set_correct, lift_export extend_set_UNIV_eq]) 1);
qed "lift_set_UNIV_eq";
Addsimps [lift_set_UNIV_eq];

(*
Goal "Domain act <= drop_set i C ==> drop_act i (Restrict C (lift_act i act)) = act";
by (asm_full_simp_tac
    (simpset() addsimps [drop_set_correct, drop_act_correct, 
			 lift_act_correct, lift_export extend_act_inverse]) 1);
qed "lift_act_inverse";
Addsimps [lift_act_inverse];
*)

Goal "UNIV <= drop_set i C ==> drop_prog C i (lift_prog i F) = F";
by (asm_full_simp_tac
    (simpset() addsimps [drop_set_correct, drop_prog_correct, 
			 lift_prog_correct, lift_export extend_inverse]) 1);
qed "lift_prog_inverse";
Addsimps [lift_prog_inverse];

Goal "inj (lift_prog i)";
by (simp_tac
    (simpset() addsimps [lift_prog_correct, lift_export inj_extend]) 1);
qed "inj_lift_prog";


(*** More Lemmas ***)

Goal "lift_act i act ^^ lift_set i A = lift_set i (act^^A)";
by (asm_simp_tac (simpset() addsimps [lift_set_correct, lift_act_correct,
				      lift_export extend_act_Image]) 1);
qed "lift_act_Image";
Addsimps [lift_act_Image];



(*** Safety: co, stable, invariant ***)

(** Safety and lift_prog **)

Goal "(lift_prog i F : (lift_set i A) co (lift_set i B))  =  \
\     (F : A co B)";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def]));
by (Force_tac 1);
qed "lift_prog_constrains";

Goal "(lift_prog i F : stable (lift_set i A)) = (F : stable A)";
by (simp_tac (simpset() addsimps [stable_def, lift_prog_constrains]) 1);
qed "lift_prog_stable";

Goal "(lift_prog i F : invariant (lift_set i A)) = (F : invariant A)";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def, lift_prog_stable]));
qed "lift_prog_invariant";

Goal "[| lift_prog i F : A co B |] \
\     ==> F : (drop_set i A) co (drop_set i B)";
by (asm_full_simp_tac
    (simpset() addsimps [drop_set_correct, lift_prog_correct, 
			 lift_export extend_constrains_project_set]) 1);
qed "lift_prog_constrains_drop_set";

(*This one looks strange!  Proof probably is by case analysis on i=j.
  If i~=j then lift_prog j (F j) does nothing to lift_set i, and the 
  premise ensures A<=B.*)
Goal "F i : A co B  \
\     ==> lift_prog j (F j) : (lift_set i A) co (lift_set i B)";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def]));
by (REPEAT (Blast_tac 1));
qed "constrains_imp_lift_prog_constrains";


(** Safety and drop_prog **)

Goal "(drop_prog C i F : A co B)  =  \
\     (F : (C Int lift_set i A) co (lift_set i B) & A <= B)";
by (simp_tac
    (simpset() addsimps [drop_prog_correct, 
			 lift_set_correct, lift_export project_constrains]) 1);
qed "drop_prog_constrains";

Goal "(drop_prog UNIV i F : stable A)  =  (F : stable (lift_set i A))";
by (simp_tac (simpset() addsimps [stable_def, drop_prog_constrains]) 1);
qed "drop_prog_stable";


(*** Diff, needed for localTo ***)

Goal "[| Diff C G (lift_act i `` acts) : (lift_set i A) co (lift_set i B) |] \
\     ==> Diff (drop_set i C) (drop_prog C i G) acts : A co B";
by (asm_full_simp_tac
    (simpset() addsimps [drop_set_correct, drop_prog_correct, 
			 lift_set_correct, lift_act_correct, 
			 lift_export Diff_project_constrains]) 1);
qed "Diff_drop_prog_constrains";

Goalw [stable_def]
     "[| Diff C G (lift_act i `` acts) : stable (lift_set i A) |]  \
\     ==> Diff (drop_set i C) (drop_prog C i G) acts : stable A";
by (blast_tac (claset() addIs [Diff_drop_prog_constrains]) 1);
qed "Diff_drop_prog_stable";


(*** Weak safety primitives: Co, Stable ***)

(** Reachability **)

Goal "reachable (lift_prog i F) = lift_set i (reachable F)";
by (simp_tac
    (simpset() addsimps [lift_prog_correct, lift_set_correct, 
			 lift_export reachable_extend_eq]) 1);
qed "reachable_lift_prog";

Goal "(lift_prog i F : (lift_set i A) Co (lift_set i B))  =  \
\     (F : A Co B)";
by (simp_tac (simpset() addsimps [Constrains_def, reachable_lift_prog,
				  lift_prog_constrains]) 1);
qed "lift_prog_Constrains";

Goal "(lift_prog i F : Stable (lift_set i A)) = (F : Stable A)";
by (simp_tac (simpset() addsimps [Stable_def, lift_prog_Constrains]) 1);
qed "lift_prog_Stable";

Goal "[| reachable (lift_prog i F Join G) <= C;    \
\        F Join drop_prog C i G : A Co B |] \
\     ==> lift_prog i F Join G : (lift_set i A) Co (lift_set i B)";
by (asm_full_simp_tac
    (simpset() addsimps [lift_prog_correct, drop_prog_correct, 
		     lift_set_correct, lift_export project_Constrains_D]) 1);
qed "drop_prog_Constrains_D";

Goalw [Stable_def]
     "[| reachable (lift_prog i F Join G) <= C;    \
\        F Join drop_prog C i G : Stable A |]  \
\     ==> lift_prog i F Join G : Stable (lift_set i A)";
by (asm_simp_tac (simpset() addsimps [drop_prog_Constrains_D]) 1);
qed "drop_prog_Stable_D";

Goal "[| reachable (lift_prog i F Join G) <= C;  \
\        F Join drop_prog C i G : Always A |]   \
\     ==> lift_prog i F Join G : Always (lift_set i A)";
by (asm_full_simp_tac
    (simpset() addsimps [lift_prog_correct, drop_prog_correct, 
		     lift_set_correct, lift_export project_Always_D]) 1);
qed "drop_prog_Always_D";

Goalw [Increasing_def]
     "[| reachable (lift_prog i F Join G) <= C;  \
\        F Join drop_prog C i G : Increasing func |] \
\     ==> lift_prog i F Join G : Increasing (func o (sub i))";
by Auto_tac;
by (stac Collect_eq_lift_set 1);
by (asm_simp_tac (simpset() addsimps [drop_prog_Stable_D]) 1); 
qed "project_Increasing_D";


(*UNUSED*)
Goal "UNIV <= drop_set i C \
\     ==> drop_prog C i ((lift_prog i F) Join G) = F Join (drop_prog C i G)";
by (asm_full_simp_tac
    (simpset() addsimps [lift_prog_correct, drop_prog_correct, 
		     drop_set_correct, lift_export project_extend_Join]) 1);
qed "drop_prog_lift_prog_Join";


(*** Progress: transient, ensures ***)

Goal "(lift_prog i F : transient (lift_set i A)) = (F : transient A)";
by (simp_tac (simpset() addsimps [lift_set_correct, lift_prog_correct,
			  lift_export extend_transient]) 1);
qed "lift_prog_transient";

Goal "(lift_prog i F : transient (lift_set j A)) = \
\     (i=j & F : transient A | A={})";
by (case_tac "i=j" 1);
by (auto_tac (claset(), simpset() addsimps [lift_prog_transient]));
by (auto_tac (claset(), simpset() addsimps [lift_prog_def, transient_def]));
by (Force_tac 1);
qed "lift_prog_transient_eq_disj";


(*** guarantees properties ***)

Goal "[| F : X guarantees Y;  \
\        projecting C (lift_map i) F X' X;  \
\        extending  C (lift_map i) F X' Y' Y |] \
\     ==> lift_prog i F : X' guarantees Y'";
by (asm_simp_tac 
    (simpset() addsimps [lift_prog_correct, project_guarantees]) 1);
qed "drop_prog_guarantees";


(** Are these two useful?? **)

(*The other direction fails: having FF : Stable {s. z <= f (s i)} does not
  ensure that F has the form lift_prog i F for some F.*)
Goal "lift_prog i `` Stable {s. P (f s)} <= Stable {s. P (f (s i))}";
by Auto_tac;
by (stac Collect_eq_lift_set 1); 
by (asm_simp_tac (simpset() addsimps [lift_prog_Stable]) 1);
qed "image_lift_prog_Stable";

Goal "lift_prog i `` Increasing f <= Increasing (f o sub i)";
by (simp_tac (simpset() addsimps [Increasing_def,
				  inj_lift_prog RS image_INT]) 1);
by (blast_tac (claset() addIs [impOfSubs image_lift_prog_Stable]) 1);
qed "image_lift_prog_Increasing";


(*** guarantees corollaries ***)

Goal "F : UNIV guarantees increasing f \
\     ==> lift_prog i F : UNIV guarantees increasing (f o sub i)";
by (dtac (lift_export extend_guar_increasing) 1);
by (asm_full_simp_tac (simpset() addsimps [lift_prog_correct, o_def]) 1);
qed "lift_prog_guar_increasing";

Goal "F : UNIV guarantees Increasing f \
\     ==> lift_prog i F : UNIV guarantees Increasing (f o sub i)";
by (dtac (lift_export extend_guar_Increasing) 1);
by (asm_full_simp_tac (simpset() addsimps [lift_prog_correct, o_def]) 1);
qed "lift_prog_guar_Increasing";

Goal "F : (v localTo[UNIV] G) guarantees increasing func  \
\     ==> lift_prog i F : (v o sub i) localTo[UNIV] (lift_prog i G)  \
\                         guarantees increasing (func o sub i)";
by (dtac (lift_export extend_localTo_guar_increasing) 1);
by (asm_full_simp_tac (simpset() addsimps [lift_prog_correct, o_def]) 1);
qed "lift_prog_localTo_guar_increasing";

Goal "F : (v LocalTo G) guarantees Increasing func  \
\     ==> lift_prog i F : (v o sub i) LocalTo (lift_prog i G)  \
\                         guarantees Increasing (func o sub i)";
by (dtac (lift_export extend_LocalTo_guar_Increasing) 1);
by (asm_full_simp_tac (simpset() addsimps [lift_prog_correct, o_def]) 1);
qed "lift_prog_LocalTo_guar_Increasing";

Goal "F : Always A guarantees Always B \
\ ==> lift_prog i F : Always(lift_set i A) guarantees Always (lift_set i B)";
by (asm_simp_tac
    (simpset() addsimps [lift_set_correct, lift_prog_correct, 
			 lift_export extend_guar_Always]) 1);
qed "lift_prog_guar_Always";
