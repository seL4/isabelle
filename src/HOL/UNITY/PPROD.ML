(*  Title:      HOL/UNITY/PPROD.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)


val rinst = read_instantiate_sg (sign_of thy);

(**** PPROD ****)

(*** Basic properties ***)

Goalw [lift_set_def] "(f : lift_set i A) = (f i : A)";
by Auto_tac;
qed "lift_set_iff";
AddIffs [lift_set_iff];

Goalw [lift_act_def] "lift_act i Id = Id";
by Auto_tac;
qed "lift_act_Id";
Addsimps [lift_act_Id];

Goalw [lift_prog_def] "Init (lift_prog i F) = lift_set i (Init F)";
by Auto_tac;
qed "Init_lift_prog";
Addsimps [Init_lift_prog];

Goalw [lift_prog_def] "Acts (lift_prog i F) = lift_act i `` Acts F";
by (auto_tac (claset() addIs [Id_in_Acts RSN (2,image_eqI)], simpset()));
qed "Acts_lift_prog";

Goalw [PPROD_def] "Init (PPROD I F) = (INT i:I. lift_set i (Init (F i)))";
by Auto_tac;
qed "Init_PPROD";
Addsimps [Init_PPROD];

Goalw [lift_act_def]
    "((f,f') : lift_act i act) = (EX s'. f' = f(i := s') & (f i, s') : act)";
by (Blast_tac 1);
qed "lift_act_eq";
AddIffs [lift_act_eq];

Goal "Acts (PPROD I F) = insert Id (UN i:I. lift_act i `` Acts (F i))";
by (auto_tac (claset(),
	      simpset() addsimps [PPROD_def, Acts_lift_prog, Acts_JN]));
qed "Acts_PPROD";

Goal "PPROD {} F = SKIP";
by (simp_tac (simpset() addsimps [PPROD_def]) 1);
qed "PPROD_empty";

Goal "(PPI i: I. SKIP) = SKIP";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [Acts_lift_prog, SKIP_def, Acts_PPROD]));
qed "PPROD_SKIP";

Addsimps [PPROD_SKIP, PPROD_empty];

Goalw [PPROD_def]
    "PPROD (insert i I) F = (lift_prog i (F i)) Join (PPROD I F)";
by Auto_tac;
qed "PPROD_insert";

Goalw [PPROD_def] "i : I ==> component (lift_prog i (F i)) (PPROD I F)";
(*blast_tac doesn't use HO unification*)
by (fast_tac (claset() addIs [component_JN]) 1);
qed "component_PPROD";


(*** Safety: co, stable, invariant ***)

(** 1st formulation of lifting **)

Goal "(lift_prog i F : (lift_set i A) co (lift_set i B))  =  \
\     (F : A co B)";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, Acts_lift_prog]));
by (Blast_tac 2);
by (Force_tac 1);
qed "lift_prog_constrains_eq";

Goal "(lift_prog i F : stable (lift_set i A)) = (F : stable A)";
by (simp_tac (simpset() addsimps [stable_def, lift_prog_constrains_eq]) 1);
qed "lift_prog_stable_eq";

(*This one looks strange!  Proof probably is by case analysis on i=j.*)
Goal "F i : A co B  \
\     ==> lift_prog j (F j) : (lift_set i A) co (lift_set i B)";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, Acts_lift_prog]));
by (REPEAT (Blast_tac 1));
qed "constrains_imp_lift_prog_constrains";

Goal "i : I ==>  \
\     (PPROD I F : (lift_set i A) co (lift_set i B))  =  \
\     (F i : A co B)";
by (asm_simp_tac (simpset() addsimps [PPROD_def, constrains_JN]) 1);
by (blast_tac (claset() addIs [lift_prog_constrains_eq RS iffD1, 
			       constrains_imp_lift_prog_constrains]) 1);
qed "PPROD_constrains";

Goal "i : I ==> (PPROD I F : stable (lift_set i A)) = (F i : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, PPROD_constrains]) 1);
qed "PPROD_stable";


(** 2nd formulation of lifting **)

Goal "[| lift_prog i F : AA co BB |] \
\     ==> F : (Applyall AA i) co (Applyall BB i)";
by (auto_tac (claset(), 
	      simpset() addsimps [Applyall_def, constrains_def, 
				  Acts_lift_prog]));
by (force_tac (claset() addSIs [rinst [("x", "?ff(i := ?u)")] image_eqI],
	       simpset()) 1);
qed "lift_prog_constrains_projection";

Goal "[| PPROD I F : AA co BB;  i: I |] \
\     ==> F i : (Applyall AA i) co (Applyall BB i)";
by (rtac lift_prog_constrains_projection 1);
(*rotate this assumption to be last*)
by (dres_inst_tac [("psi", "PPROD I F : ?C")] asm_rl 1);
by (asm_full_simp_tac (simpset() addsimps [PPROD_def, constrains_JN]) 1);
qed "PPROD_constrains_projection";


(** invariant **)

(*UNUSED*)
Goal "(lift_prog i F : invariant (lift_set i A)) = (F : invariant A)";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def, lift_prog_stable_eq]));
qed "lift_prog_invariant_eq";

Goal "[| F i : invariant A;  i : I |] \
\     ==> PPROD I F : invariant (lift_set i A)";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def, PPROD_stable]));
qed "invariant_imp_PPROD_invariant";

(*The f0 premise ensures that the product is well-defined.*)
Goal "[| PPROD I F : invariant (lift_set i A);  i : I;  \
\        f0: Init (PPROD I F) |] ==> F i : invariant A";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def, PPROD_stable]));
by (dres_inst_tac [("c", "f0(i:=x)")] subsetD 1);
by Auto_tac;
qed "PPROD_invariant_imp_invariant";

Goal "[| i : I;  f0: Init (PPROD I F) |] \
\     ==> (PPROD I F : invariant (lift_set i A)) = (F i : invariant A)";
by (blast_tac (claset() addIs [invariant_imp_PPROD_invariant, 
			       PPROD_invariant_imp_invariant]) 1);
qed "PPROD_invariant";

(*The f0 premise isn't needed if F is a constant program because then
  we get an initial state by replicating that of F*)
Goal "i : I \
\     ==> ((PPI x:I. F) : invariant (lift_set i A)) = (F : invariant A)";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def, PPROD_stable]));
qed "PFUN_invariant";


(*** Substitution Axiom versions: Co, Stable ***)

(** Reachability **)

Goal "[| f : reachable (PPROD I F);  i : I |] ==> f i : reachable (F i)";
by (etac reachable.induct 1);
by (auto_tac
    (claset() addIs reachable.intrs,
     simpset() addsimps [Acts_PPROD]));
qed "reachable_PPROD";

Goal "reachable (PPROD I F) <= {f. ALL i:I. f i : reachable (F i)}";
by (force_tac (claset() addSDs [reachable_PPROD], simpset()) 1);
qed "reachable_PPROD_subset1";

Goal "[| i ~: I;  A : reachable (F i) |]     \
\  ==> ALL f. f : reachable (PPROD I F)      \
\             --> f(i:=A) : reachable (lift_prog i (F i) Join PPROD I F)";
by (etac reachable.induct 1);
by (ALLGOALS Clarify_tac);
by (etac reachable.induct 1);
(*Init, Init case*)
by (force_tac (claset() addIs reachable.intrs,
	       simpset() addsimps [Acts_lift_prog]) 1);
(*Init of F, action of PPROD F case*)
by (rtac reachable.Acts 1);
by (force_tac (claset(), simpset() addsimps [Acts_Join]) 1);
by (assume_tac 1);
by (force_tac (claset() addIs [ext], simpset() addsimps [Acts_PPROD]) 1);
(*induction over the 2nd "reachable" assumption*)
by (eres_inst_tac [("xa","f")] reachable.induct 1);
(*Init of PPROD F, action of F case*)
by (res_inst_tac [("act","lift_act i act")] reachable.Acts 1);
by (force_tac (claset(), simpset() addsimps [Acts_lift_prog, Acts_Join]) 1);
by (force_tac (claset() addIs [reachable.Init], simpset()) 1);
by (force_tac (claset() addIs [ext], simpset() addsimps [lift_act_def]) 1);
(*last case: an action of PPROD I F*)
by (rtac reachable.Acts 1);
by (force_tac (claset(), simpset() addsimps [Acts_Join]) 1);
by (assume_tac 1);
by (force_tac (claset() addIs [ext], simpset() addsimps [Acts_PPROD]) 1);
qed_spec_mp "reachable_lift_Join_PPROD";


(*The index set must be finite: otherwise infinitely many copies of F can
  perform actions, and PPROD can never catch up in finite time.*)
Goal "finite I \
\     ==> {f. ALL i:I. f i : reachable (F i)} <= reachable (PPROD I F)";
by (etac finite_induct 1);
by (Simp_tac 1);
by (force_tac (claset() addDs [reachable_lift_Join_PPROD], 
	       simpset() addsimps [PPROD_insert]) 1);
qed "reachable_PPROD_subset2";

Goal "finite I ==> \
\     reachable (PPROD I F) = {f. ALL i:I. f i : reachable (F i)}";
by (REPEAT_FIRST (ares_tac [equalityI,
			    reachable_PPROD_subset1, 
			    reachable_PPROD_subset2]));
qed "reachable_PPROD_eq";


(** Co **)

Goal "[| F i : A Co B;  i: I;  finite I |]  \
\     ==> PPROD I F : (lift_set i A) Co (lift_set i B)";
by (auto_tac
    (claset(),
     simpset() addsimps [Constrains_def, Collect_conj_eq RS sym,
			 reachable_PPROD_eq]));
by (auto_tac (claset(), 
              simpset() addsimps [constrains_def, Acts_lift_prog, PPROD_def,
                                  Acts_JN]));
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "Constrains_imp_PPROD_Constrains";

Goal "[| ALL i:I. f0 i : R i;   i: I |] \
\     ==> Applyall ({f. (ALL i:I. f i : R i)} Int lift_set i A) i = R i Int A";
by (force_tac (claset() addSIs [rinst [("x", "?ff(i := ?u)")] image_eqI],
	       simpset() addsimps [Applyall_def, lift_set_def]) 1);
qed "Applyall_Int_depend";

(*Again, we need the f0 premise because otherwise holds Co trivially
  for PPROD I F.*)
Goal "[| PPROD I F : (lift_set i A) Co (lift_set i B);  \
\        i: I;  finite I;  f0: Init (PPROD I F) |]  \
\     ==> F i : A Co B";
by (full_simp_tac (simpset() addsimps [Constrains_def]) 1);
by (subgoal_tac "ALL i:I. f0 i : reachable (F i)" 1);
by (blast_tac (claset() addIs [reachable.Init]) 2);
by (dtac PPROD_constrains_projection 1);
by (assume_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [Applyall_Int_depend, reachable_PPROD_eq]) 1);
qed "PPROD_Constrains_imp_Constrains";


Goal "[| i: I;  finite I;  f0: Init (PPROD I F) |]  \
\     ==> (PPROD I F : (lift_set i A) Co (lift_set i B)) =  \
\         (F i : A Co B)";
by (blast_tac (claset() addIs [Constrains_imp_PPROD_Constrains, 
			       PPROD_Constrains_imp_Constrains]) 1);
qed "PPROD_Constrains";

Goal "[| i: I;  finite I;  f0: Init (PPROD I F) |]  \
\     ==> (PPROD I F : Stable (lift_set i A)) = (F i : Stable A)";
by (asm_simp_tac (simpset() delsimps [Init_PPROD]
			    addsimps [Stable_def, PPROD_Constrains]) 1);
qed "PPROD_Stable";


(** PFUN (no dependence on i) doesn't require the f0 premise **)

Goal "i: I \
\     ==> Applyall ({f. (ALL i:I. f i : R)} Int lift_set i A) i = R Int A";
by (force_tac (claset(), simpset() addsimps [Applyall_def]) 1);
qed "Applyall_Int";

Goal "[| (PPI x:I. F) : (lift_set i A) Co (lift_set i B);  \
\        i: I;  finite I |]  \
\     ==> F : A Co B";
by (full_simp_tac (simpset() addsimps [Constrains_def]) 1);
by (dtac PPROD_constrains_projection 1);
by (assume_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [Applyall_Int, Collect_conj_eq RS sym,
			 reachable_PPROD_eq]) 1);
qed "PFUN_Constrains_imp_Constrains";

Goal "[| i: I;  finite I |]  \
\     ==> ((PPI x:I. F) : (lift_set i A) Co (lift_set i B)) =  \
\         (F : A Co B)";
by (blast_tac (claset() addIs [Constrains_imp_PPROD_Constrains, 
			       PFUN_Constrains_imp_Constrains]) 1);
qed "PFUN_Constrains";

Goal "[| i: I;  finite I |]  \
\     ==> ((PPI x:I. F) : Stable (lift_set i A)) = (F : Stable A)";
by (asm_simp_tac (simpset() addsimps [Stable_def, PFUN_Constrains]) 1);
qed "PFUN_Stable";



(*** guarantees properties ***)


Goal "drop_act i (lift_act i act) = act";
by (force_tac (claset() addSIs [rinst [("x", "?ff(i := ?u)")] exI],
	       simpset() addsimps [drop_act_def, lift_act_def]) 1);
qed "lift_act_inverse";
Addsimps [lift_act_inverse];


Goal "(lift_prog i F) Join G = lift_prog i H \
\     ==> EX J. H = F Join J";
by (etac program_equalityE 1);
by (auto_tac (claset(), simpset() addsimps [Acts_lift_prog, Acts_Join]));
by (res_inst_tac [("x", 
		   "mk_program(Applyall(Init G) i, drop_act i `` Acts G)")] 
    exI 1);
by (rtac program_equalityI 1);
(*Init*)
by (simp_tac (simpset() addsimps [Applyall_def]) 1);
(*Blast_tac can't do HO unification, needed to invent function states*)
by (fast_tac (claset() addEs [equalityE]) 1);
(*Now for the Actions*)
by (dres_inst_tac [("f", "op `` (drop_act i)")] arg_cong 1);
by (asm_full_simp_tac 
    (simpset() addsimps [insert_absorb, Acts_Join,
			 image_Un, image_compose RS sym, o_def]) 1);
qed "lift_prog_Join_eq_lift_prog_D";


Goal "F : X guarantees Y \
\     ==> lift_prog i F : (lift_prog i `` X) guarantees (lift_prog i `` Y)";
by (rtac guaranteesI 1);
by Auto_tac;
by (blast_tac (claset() addDs [lift_prog_Join_eq_lift_prog_D, guaranteesD]) 1);
qed "lift_prog_guarantees";


