(*  Title:      HOL/UNITY/Lift_prog.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

THESE PROOFS CAN BE REPLACED BY INVOCATIONS OF RESULTS FROM EXTEND.ML
*)


val image_eqI' = read_instantiate_sg (sign_of thy)
                     [("x", "?ff(i := ?u)")] image_eqI;

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

Goalw [drop_act_def] "(s, s') : act ==> (s i, s' i) : drop_act i act";
by (auto_tac (claset() addSIs [image_eqI], simpset()));
qed "drop_act_I";

Goalw [drop_act_def] "drop_act i Id = Id";
by Auto_tac;
by (res_inst_tac [("x", "((%u. x), (%u. x))")] image_eqI 1);
by Auto_tac;
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

Goalw [drop_prog_def] "Init (drop_prog i F) = drop_set i (Init F)";
by Auto_tac;
qed "Init_drop_prog";
Addsimps [Init_drop_prog];

Goalw [drop_prog_def] "Acts (drop_prog i F) = drop_act i `` Acts F";
by (auto_tac (claset() addIs [Id_in_Acts RSN (2,image_eqI)], simpset()));
qed "Acts_drop_prog";
Addsimps [Acts_drop_prog];

(** These monotonicity results look natural but are UNUSED **)

Goal "F <= G ==> lift_prog i F <= lift_prog i G";
by (full_simp_tac (simpset() addsimps [component_eq_subset]) 1);
by Auto_tac;
qed "lift_prog_mono";

Goal "F <= G ==> drop_prog i F <= drop_prog i G";
by (full_simp_tac (simpset() addsimps [component_eq_subset, drop_set_def]) 1);
by Auto_tac;
qed "drop_prog_mono";

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

Goal "drop_prog i SKIP = SKIP";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [SKIP_def, drop_set_def, drop_prog_def]));
qed "drop_prog_SKIP";


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

Goalw [lift_act_def, drop_act_def] "drop_act i (lift_act i act) = act";
by Auto_tac;
by (res_inst_tac [("x", "f(i:=a)")] exI 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("x", "f(i:=b)")] exI 1);
by (Asm_simp_tac 1);
qed "lift_act_inverse";
Addsimps [lift_act_inverse];

Goal "inj (lift_act i)";
by (rtac inj_on_inverseI 1);
by (rtac lift_act_inverse 1);
qed "inj_lift_act";

Goal "drop_prog i (lift_prog i F) = F";
by (simp_tac (simpset() addsimps [lift_prog_def, drop_prog_def]) 1);
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [image_image_eq_UN]) 2);
by (Simp_tac 1);
qed "lift_prog_inverse";
Addsimps [lift_prog_inverse];

Goal "inj (lift_prog i)";
by (rtac inj_on_inverseI 1);
by (rtac lift_prog_inverse 1);
qed "inj_lift_prog";


(*For compatibility with the original definition and perhaps simpler proofs*)
Goalw [lift_act_def]
    "((f,f') : lift_act i act) = (EX s'. f' = f(i := s') & (f i, s') : act)";
by Auto_tac;
by (rtac exI 1);
by Auto_tac;
qed "lift_act_eq";
AddIffs [lift_act_eq];


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
by (auto_tac (claset(), simpset() addsimps [extend_act_def, lift_map_def]));
by (rtac bexI 1);
by (auto_tac (claset() addSIs [exI], simpset()));
qed "lift_act_correct";

Goal "drop_act i = project_act UNIV (lift_map i)";
by (rtac ext 1);
by (rewrite_goals_tac [project_act_def, drop_act_def, lift_map_def]);
by Auto_tac;
by (rtac image_eqI 2);
by (REPEAT (rtac exI 1 ORELSE stac (refl RS fun_upd_idem) 1));
by Auto_tac;
qed "drop_act_correct";

Goal "lift_prog i F = extend (lift_map i) F";
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [lift_set_correct]) 1);
by (simp_tac (simpset() 
	      addsimps [lift_export Acts_extend, 
			lift_act_correct]) 1);
qed "lift_prog_correct";

Goal "drop_prog i F = project UNIV (lift_map i) F";
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [drop_set_correct]) 1);
by (simp_tac (simpset() 
	      addsimps [lift_export Acts_project,
			drop_act_correct]) 1);
qed "drop_prog_correct";


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

Goalw [constrains_def]
     "(drop_prog i F : A co B)  =  (F : (lift_set i A) co (lift_set i B))";
by Auto_tac;
by (force_tac (claset(), 
	       simpset() addsimps [drop_act_def]) 2);
by (blast_tac (claset() addIs [drop_act_I]) 1);
qed "drop_prog_constrains";

Goal "(drop_prog i F : stable A)  =  (F : stable (lift_set i A))";
by (simp_tac (simpset() addsimps [stable_def, drop_prog_constrains]) 1);
qed "drop_prog_stable";


(*** Diff, needed for localTo ***)

(** THESE PROOFS CAN BE GENERALIZED AS IN EXTEND.ML **)

Goal "Diff G (lift_act i `` Acts F) : (lift_set i A) co (lift_set i B)  \
\     ==> Diff (drop_prog i G) (Acts F) : A co B";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, Diff_def]));
by (dtac bspec 1);
by (Force_tac 1);
by (auto_tac (claset(), simpset() addsimps [drop_act_def]));
by (auto_tac (claset(), simpset() addsimps [lift_set_def]));
qed "Diff_drop_prog_co";

Goalw [stable_def]
     "Diff G (lift_act i `` Acts F) : stable (lift_set i A)  \
\     ==> Diff (drop_prog i G) (Acts F) : stable A";
by (etac Diff_drop_prog_co 1);
qed "Diff_drop_prog_stable";

Goalw [constrains_def, Diff_def]
     "Diff G (Acts F) : A co B  \
\     ==> Diff (lift_prog i G) (lift_act i `` Acts F) \
\         : (lift_set i A) co (lift_set i B)";
by Auto_tac;
by (Blast_tac 1);
qed "Diff_lift_prog_co";

Goalw [stable_def]
     "Diff G (Acts F) : stable A  \
\     ==> Diff (lift_prog i G) (lift_act i `` Acts F) : stable (lift_set i A)";
by (etac Diff_lift_prog_co 1);
qed "Diff_lift_prog_stable";


(*** Weak safety primitives: Co, Stable ***)

(** Reachability **)

Goal "s : reachable F ==> f(i:=s) : reachable (lift_prog i F)";
by (etac reachable.induct 1);
by (force_tac (claset() addIs [reachable.Acts, ext], 
	       simpset()) 2);
by (force_tac (claset() addIs [reachable.Init], simpset()) 1);
qed "reachable_lift_progI";

Goal "f : reachable (lift_prog i F) ==> f i : reachable F";
by (etac reachable.induct 1);
by Auto_tac;
by (ALLGOALS (blast_tac (claset() addIs reachable.intrs)));
qed "reachable_lift_progD";

Goal "reachable (lift_prog i F) = lift_set i (reachable F)";
by Auto_tac;
by (etac reachable_lift_progD 1);
ren "f" 1;
by (dres_inst_tac [("f","f"),("i","i")] reachable_lift_progI 1);
by Auto_tac;
qed "reachable_lift_prog";

Goal "(lift_prog i F : (lift_set i A) Co (lift_set i B))  =  \
\     (F : A Co B)";
by (simp_tac (simpset() addsimps [Constrains_def, reachable_lift_prog,
				  lift_prog_constrains]) 1);
qed "lift_prog_Constrains";

Goal "(lift_prog i F : Stable (lift_set i A)) = (F : Stable A)";
by (simp_tac (simpset() addsimps [Stable_def, lift_prog_Constrains]) 1);
qed "lift_prog_Stable";

(** Reachability and drop_prog **)

Goal "f : reachable F ==> f i : reachable (drop_prog i F)";
by (etac reachable.induct 1);
by (force_tac (claset() addIs [reachable.Acts, drop_act_I],
	       simpset()) 2);
by (force_tac (claset() addIs [reachable.Init, drop_set_I],
	       simpset()) 1);
qed "reachable_imp_reachable_drop_prog";

(*Converse fails because it would require
  [| s i : reachable (drop_prog i F); s i : A |] ==> s : reachable F
*)
Goalw [Constrains_def]
     "drop_prog i F : A Co B ==> F : (lift_set i A) Co (lift_set i B)";
by (full_simp_tac (simpset() addsimps [drop_prog_constrains]) 1);
by (etac constrains_weaken_L 1);
by Auto_tac;
by (etac reachable_imp_reachable_drop_prog 1);
qed "drop_prog_Constrains_D";

Goalw [Stable_def]
     "drop_prog i F : Stable A ==> F : Stable (lift_set i A)";
by (asm_simp_tac (simpset() addsimps [drop_prog_Constrains_D]) 1);
qed "drop_prog_Stable_D";


(*** Programs of the form lift_prog i F Join G
     in other words programs containing a replicated component ***)

Goal "drop_prog i ((lift_prog i F) Join G) = F Join (drop_prog i G)";
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [image_Un, image_image_eq_UN]) 2);
by (simp_tac (simpset() addsimps [drop_set_Int_lift_set]) 1);
qed "drop_prog_lift_prog_Join";

Goal "(lift_prog i F) Join G = lift_prog i H \
\     ==> H = F Join (drop_prog i G)";
by (dres_inst_tac [("f", "drop_prog i")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);
by (etac sym 1);
qed "lift_prog_Join_eq_lift_prog_D";

Goal "f : reachable (lift_prog i F Join G)  \
\     ==> f i : reachable (F Join drop_prog i G)";
by (etac reachable.induct 1);
by (force_tac (claset() addIs [reachable.Init, drop_set_I], simpset()) 1);
(*By case analysis on whether the action is of lift_prog i F  or  G*)
by (force_tac (claset() addIs [reachable.Acts, drop_act_I], 
	       simpset() addsimps [image_iff]) 1);
qed "reachable_lift_prog_Join_D";

(*Opposite inclusion fails, even for the initial state: lift_set i includes
  ALL functions determined only by their value at i.*)
Goal "reachable (lift_prog i F Join G) <= \
\     lift_set i (reachable (F Join drop_prog i G))";
by Auto_tac;
by (etac reachable_lift_prog_Join_D 1);
qed "reachable_lift_prog_Join_subset";

Goalw [Constrains_def]
     "F Join drop_prog i G : A Co B    \
\     ==> lift_prog i F Join G : (lift_set i A) Co (lift_set i B)";
by (subgoal_tac 
    "lift_prog i F Join G : lift_set i (reachable (F Join drop_prog i G)) Int \
\                           lift_set i A \
\    co lift_set i B" 1);
by (asm_full_simp_tac 
    (simpset() addsimps [Int_lift_set,
			 lift_prog_constrains,
			 drop_prog_constrains RS sym,
			 drop_prog_lift_prog_Join]) 2);
by (blast_tac (claset() addIs [constrains_weaken, 
			       reachable_lift_prog_Join_D]) 1);
qed "lift_prog_Join_Constrains";

Goal "F Join drop_prog i G : Stable A    \
\     ==> lift_prog i F Join G : Stable (lift_set i A)";
by (asm_full_simp_tac (simpset() addsimps [Stable_def, 
					   lift_prog_Join_Constrains]) 1);
qed "lift_prog_Join_Stable";


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

(** It seems that neither of these can be proved from the other. **)

(*Strong precondition and postcondition; doesn't seem very useful.
  Probably can be strengthened to an equivalance.*)
Goal "F : X guarantees Y \
\     ==> lift_prog i F : (lift_prog i `` X) guarantees (lift_prog i `` Y)";
by (rtac guaranteesI 1);
by Auto_tac;
by (blast_tac (claset() addDs [lift_prog_Join_eq_lift_prog_D, guaranteesD]) 1);
qed "lift_prog_guarantees";

(*Weak precondition and postcondition; this is the good one!
CAN WEAKEN 2ND PREMISE TO  
      !!G. extend h F Join G : XX ==> F Join project h G : X; 
*)
val [xguary,drop_prog,lift_prog] =
Goal "[| F : X guarantees Y;  \
\        !!H. H : XX ==> drop_prog i H : X;  \
\        !!G. F Join drop_prog i G : Y ==> lift_prog i F Join G : YY |] \
\     ==> lift_prog i F : XX guarantees YY";
by (rtac (xguary RS guaranteesD RS lift_prog RS guaranteesI) 1);
by (dtac drop_prog 1);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);
qed "drop_prog_guarantees";


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

Goalw [increasing_def]
     "F : UNIV guarantees increasing f \
\     ==> lift_prog i F : UNIV guarantees increasing (f o sub i)";
by (etac drop_prog_guarantees 1);
by Auto_tac;
by (stac Collect_eq_lift_set 1); 
by (asm_full_simp_tac
    (simpset() addsimps [lift_prog_stable, drop_prog_stable, 
			 Join_stable]) 1);
qed "lift_prog_guar_increasing";

Goalw [Increasing_def]
     "F : UNIV guarantees Increasing f \
\     ==> lift_prog i F : UNIV guarantees Increasing (f o sub i)";
by (etac drop_prog_guarantees 1);
by Auto_tac;
by (stac Collect_eq_lift_set 1); 
by (asm_simp_tac (simpset() addsimps [lift_prog_Join_Stable]) 1);
qed "lift_prog_guar_Increasing";

Goalw [localTo_def, increasing_def]
     "F : (f localTo F) guarantees increasing f  \
\     ==> lift_prog i F : (f o sub i) localTo (lift_prog i F)  \
\                         guarantees increasing (f o sub i)";
by (etac drop_prog_guarantees 1);
by Auto_tac;
by (stac Collect_eq_lift_set 2); 
(*the "increasing" guarantee*)
by (asm_full_simp_tac
    (simpset() addsimps [lift_prog_stable, drop_prog_stable, 
			 Join_stable]) 2);
(*the "localTo" requirement*)
by (asm_simp_tac
    (simpset() addsimps [Diff_drop_prog_stable, 
			 Collect_eq_lift_set RS sym]) 1); 
qed "lift_prog_localTo_guar_increasing";

Goalw [localTo_def, Increasing_def]
     "F : (f localTo F) guarantees Increasing f  \
\     ==> lift_prog i F : (f o sub i) localTo (lift_prog i F)  \
\                         guarantees Increasing (f o sub i)";
by (etac drop_prog_guarantees 1);
by Auto_tac;
by (stac Collect_eq_lift_set 2); 
(*the "Increasing" guarantee*)
by (asm_simp_tac (simpset() addsimps [lift_prog_Join_Stable]) 2);
(*the "localTo" requirement*)
by (asm_simp_tac
    (simpset() addsimps [Diff_drop_prog_stable, 
			 Collect_eq_lift_set RS sym]) 1); 
qed "lift_prog_localTo_guar_Increasing";

(*Converse fails.  Useful?*)
Goal "lift_prog i `` (f localTo F) <= (f o sub i) localTo (lift_prog i F)";
by (simp_tac (simpset() addsimps [localTo_def]) 1);
by Auto_tac;
by (stac Collect_eq_lift_set 1); 
by (asm_simp_tac (simpset() addsimps [Diff_lift_prog_stable]) 1); 
qed "localTo_lift_prog_I";

(*No analogue of this in Extend.ML!*)
Goal "[| lift_prog i F : AA co BB |] \
\     ==> F : (drop_set i AA) co (drop_set i BB)";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, drop_set_def]));
by (force_tac (claset() addSIs [image_eqI'], simpset()) 1);
qed "lift_prog_constrains_drop_set";
