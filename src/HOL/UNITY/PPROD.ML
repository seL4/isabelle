(*  Title:      HOL/UNITY/PPROD.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)


val rinst = read_instantiate_sg (sign_of thy);

(**** PPROD ****)

(*** Basic properties ***)

(** lift_set and drop_set **)

Goalw [lift_set_def] "(f : lift_set i A) = (f i : A)";
by Auto_tac;
qed "lift_set_iff";
AddIffs [lift_set_iff];

Goalw [lift_set_def] "lift_set i (A Int B) = lift_set i A Int lift_set i B";
by Auto_tac;
qed "lift_set_Int";

(*USED?? converse fails*)
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

Goal "F component G ==> lift_prog i F component lift_prog i G";
by (full_simp_tac (simpset() addsimps [component_eq_subset]) 1);
by Auto_tac;
qed "lift_prog_mono";

Goal "F component G ==> drop_prog i F component drop_prog i G";
by (full_simp_tac (simpset() addsimps [component_eq_subset, drop_set_def]) 1);
by Auto_tac;
qed "drop_prog_mono";

Goal "lift_prog i SKIP = SKIP";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [SKIP_def, lift_prog_def]));
qed "lift_prog_SKIP";

Goal "lift_prog i (F Join G) = (lift_prog i F) Join (lift_prog i G)";
by (rtac program_equalityI 1);
by (auto_tac (claset(), simpset() addsimps [Acts_Join]));
qed "lift_prog_Join";

Goal "lift_prog i (JOIN I F) = (JN j:I. lift_prog i (F j))";
by (rtac program_equalityI 1);
by (auto_tac (claset(), simpset() addsimps [Acts_JN]));
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
qed "drop_set_lift_set_Int";

Goalw [lift_set_def, drop_set_def]
     "drop_set i (B Int (lift_set i A)) = (drop_set i B) Int A";
by Auto_tac;
qed "drop_set_lift_set_Int2";

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
by (rtac ext 1);
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
by (simp_tac (simpset() addsimps [image_compose RS sym, o_def]) 2);
by (Simp_tac 1);
qed "lift_prog_inverse";
Addsimps [lift_prog_inverse];

Goal "inj (lift_prog i)";
by (rtac inj_on_inverseI 1);
by (rtac lift_prog_inverse 1);
qed "inj_lift_prog";


(** PLam **)

Goalw [PLam_def] "Init (PLam I F) = (INT i:I. lift_set i (Init (F i)))";
by Auto_tac;
qed "Init_PLam";
Addsimps [Init_PLam];

(*For compatibility with the original definition and perhaps simpler proofs*)
Goalw [lift_act_def]
    "((f,f') : lift_act i act) = (EX s'. f' = f(i := s') & (f i, s') : act)";
by Auto_tac;
by (rtac exI 1);
by Auto_tac;
qed "lift_act_eq";
AddIffs [lift_act_eq];


Goal "Acts (PLam I F) = insert Id (UN i:I. lift_act i `` Acts (F i))";
by (auto_tac (claset(),
	      simpset() addsimps [PLam_def, Acts_JN]));
qed "Acts_PLam";

Goal "PLam {} F = SKIP";
by (simp_tac (simpset() addsimps [PLam_def]) 1);
qed "PLam_empty";

Goal "(plam i: I. SKIP) = SKIP";
by (simp_tac (simpset() addsimps [PLam_def,lift_prog_SKIP,JN_constant]) 1);
qed "PLam_SKIP";

Addsimps [PLam_SKIP, PLam_empty];

Goalw [PLam_def]
    "PLam (insert i I) F = (lift_prog i (F i)) Join (PLam I F)";
by Auto_tac;
qed "PLam_insert";

Goalw [PLam_def] "i : I ==> (lift_prog i (F i)) component (PLam I F)";
(*blast_tac doesn't use HO unification*)
by (fast_tac (claset() addIs [component_JN]) 1);
qed "component_PLam";


(*** Safety: co, stable, invariant ***)

(** Safety and lift_prog **)

Goal "(lift_prog i F : (lift_set i A) co (lift_set i B))  =  \
\     (F : A co B)";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def]));
by (Blast_tac 2);
by (Force_tac 1);
qed "lift_prog_constrains_eq";

Goal "(lift_prog i F : stable (lift_set i A)) = (F : stable A)";
by (simp_tac (simpset() addsimps [stable_def, lift_prog_constrains_eq]) 1);
qed "lift_prog_stable_eq";

(*This one looks strange!  Proof probably is by case analysis on i=j.
  If i~=j then lift_prog j (F j) does nothing to lift_set i, and the 
  premise ensures A<=B.*)
Goal "F i : A co B  \
\     ==> lift_prog j (F j) : (lift_set i A) co (lift_set i B)";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def]));
by (REPEAT (Blast_tac 1));
qed "constrains_imp_lift_prog_constrains";

(** safety properties for program unit j hold trivially of unit i **)
Goalw [constrains_def]
     "[| i~=j;  A<= B|] ==> lift_prog i F : (lift_set j A) co (lift_set j B)";
by Auto_tac;
qed "neq_imp_lift_prog_constrains";

Goalw [stable_def]
     "i~=j ==> lift_prog i F : stable (lift_set j A)";
by (blast_tac (claset() addIs [neq_imp_lift_prog_constrains]) 1);
qed "neq_imp_lift_prog_stable";

bind_thm ("neq_imp_lift_prog_Constrains",
	  neq_imp_lift_prog_constrains RS constrains_imp_Constrains);

bind_thm ("neq_imp_lift_prog_Stable",
	  neq_imp_lift_prog_stable RS stable_imp_Stable);


(** Safety and PLam **)

Goal "i : I ==>  \
\     (PLam I F : (lift_set i A) co (lift_set i B))  =  \
\     (F i : A co B)";
by (asm_simp_tac (simpset() addsimps [PLam_def, constrains_JN]) 1);
by (blast_tac (claset() addIs [lift_prog_constrains_eq RS iffD1, 
			       constrains_imp_lift_prog_constrains]) 1);
qed "PLam_constrains";

Goal "i : I ==> (PLam I F : stable (lift_set i A)) = (F i : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, PLam_constrains]) 1);
qed "PLam_stable";


(** Safety, lift_prog + drop_set **)

Goal "[| lift_prog i F : AA co BB |] \
\     ==> F : (drop_set i AA) co (drop_set i BB)";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, drop_set_def]));
by (force_tac (claset() addSIs [rinst [("x", "?ff(i := ?u)")] image_eqI],
	       simpset()) 1);
qed "lift_prog_constrains_projection";

Goal "[| PLam I F : AA co BB;  i: I |] \
\     ==> F i : (drop_set i AA) co (drop_set i BB)";
by (rtac lift_prog_constrains_projection 1);
(*rotate this assumption to be last*)
by (dres_inst_tac [("psi", "PLam I F : ?C")] asm_rl 1);
by (asm_full_simp_tac (simpset() addsimps [PLam_def, constrains_JN]) 1);
qed "PLam_constrains_projection";


(** invariant **)

Goal "(lift_prog i F : invariant (lift_set i A)) = (F : invariant A)";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def, lift_prog_stable_eq]));
qed "lift_prog_invariant_eq";

Goal "[| F i : invariant A;  i : I |] \
\     ==> PLam I F : invariant (lift_set i A)";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def, PLam_stable]));
qed "invariant_imp_PLam_invariant";

(*The f0 premise ensures that the product is well-defined.*)
Goal "[| PLam I F : invariant (lift_set i A);  i : I;  \
\        f0: Init (PLam I F) |] ==> F i : invariant A";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def, PLam_stable]));
by (dres_inst_tac [("c", "f0(i:=x)")] subsetD 1);
by Auto_tac;
qed "PLam_invariant_imp_invariant";

Goal "[| i : I;  f0: Init (PLam I F) |] \
\     ==> (PLam I F : invariant (lift_set i A)) = (F i : invariant A)";
by (blast_tac (claset() addIs [invariant_imp_PLam_invariant, 
			       PLam_invariant_imp_invariant]) 1);
qed "PLam_invariant";

(*The f0 premise isn't needed if F is a constant program because then
  we get an initial state by replicating that of F*)
Goal "i : I \
\     ==> ((plam x:I. F) : invariant (lift_set i A)) = (F : invariant A)";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def, PLam_stable]));
qed "const_PLam_invariant";


(*** Substitution Axiom versions: Co, Stable ***)

(*** Reachability ***)

(** for lift_prog **)

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
				  lift_set_Int RS sym,
				  lift_prog_constrains_eq]) 1);
qed "lift_prog_Constrains_eq";

Goal "(lift_prog i F : Stable (lift_set i A)) = (F : Stable A)";
by (simp_tac (simpset() addsimps [Stable_def, lift_prog_Constrains_eq]) 1);
qed "lift_prog_Stable_eq";


(** Reachability for PLam **)

Goal "[| f : reachable (PLam I F);  i : I |] ==> f i : reachable (F i)";
by (etac reachable.induct 1);
by (auto_tac
    (claset() addIs reachable.intrs,
     simpset() addsimps [Acts_PLam]));
qed "reachable_PLam";

(*Result to justify a re-organization of this file*)
Goal "{f. ALL i:I. f i : R i} = (INT i:I. lift_set i (R i))";
by Auto_tac;
result();

Goal "reachable (PLam I F) <= (INT i:I. lift_set i (reachable (F i)))";
by (force_tac (claset() addSDs [reachable_PLam], simpset()) 1);
qed "reachable_PLam_subset1";

(*simplify using reachable_lift_prog??*)
Goal "[| i ~: I;  A : reachable (F i) |]     \
\  ==> ALL f. f : reachable (PLam I F)      \
\             --> f(i:=A) : reachable (lift_prog i (F i) Join PLam I F)";
by (etac reachable.induct 1);
by (ALLGOALS Clarify_tac);
by (etac reachable.induct 1);
(*Init, Init case*)
by (force_tac (claset() addIs reachable.intrs, simpset()) 1);
(*Init of F, action of PLam F case*)
by (rtac reachable.Acts 1);
by (force_tac (claset(), simpset() addsimps [Acts_Join]) 1);
by (assume_tac 1);
by (force_tac (claset() addIs [ext], simpset() addsimps [Acts_PLam]) 1);
(*induction over the 2nd "reachable" assumption*)
by (eres_inst_tac [("xa","f")] reachable.induct 1);
(*Init of PLam F, action of F case*)
by (res_inst_tac [("act","lift_act i act")] reachable.Acts 1);
by (force_tac (claset(), simpset() addsimps [Acts_Join]) 1);
by (force_tac (claset() addIs [reachable.Init], simpset()) 1);
by (force_tac (claset() addIs [ext], simpset() addsimps [lift_act_def]) 1);
(*last case: an action of PLam I F*)
by (rtac reachable.Acts 1);
by (force_tac (claset(), simpset() addsimps [Acts_Join]) 1);
by (assume_tac 1);
by (force_tac (claset() addIs [ext], simpset() addsimps [Acts_PLam]) 1);
qed_spec_mp "reachable_lift_Join_PLam";


(*The index set must be finite: otherwise infinitely many copies of F can
  perform actions, and PLam can never catch up in finite time.*)
Goal "finite I \
\     ==> (INT i:I. lift_set i (reachable (F i))) <= reachable (PLam I F)";
by (etac finite_induct 1);
by (Simp_tac 1);
by (force_tac (claset() addDs [reachable_lift_Join_PLam], 
	       simpset() addsimps [PLam_insert]) 1);
qed "reachable_PLam_subset2";

Goal "finite I ==> \
\     reachable (PLam I F) = (INT i:I. lift_set i (reachable (F i)))";
by (REPEAT_FIRST (ares_tac [equalityI,
			    reachable_PLam_subset1, 
			    reachable_PLam_subset2]));
qed "reachable_PLam_eq";


(** Co **)

Goal "[| F i : A Co B;  i: I;  finite I |]  \
\     ==> PLam I F : (lift_set i A) Co (lift_set i B)";
by (auto_tac
    (claset(),
     simpset() addsimps [Constrains_def, Collect_conj_eq RS sym,
			 reachable_PLam_eq]));
by (auto_tac (claset(), 
              simpset() addsimps [constrains_def, PLam_def, Acts_JN]));
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "Constrains_imp_PLam_Constrains";

Goal "[| ALL j:I. f0 j : A j;   i: I |] \
\     ==> drop_set i (INT j:I. lift_set j (A j)) = A i";
by (force_tac (claset() addSIs [rinst [("x", "?ff(i := ?u)")] image_eqI],
	       simpset() addsimps [drop_set_def]) 1);
qed "drop_set_INT_lift_set";

(*Again, we need the f0 premise so that PLam I F has an initial state;
  otherwise its Co-property is vacuous.*)
Goal "[| PLam I F : (lift_set i A) Co (lift_set i B);  \
\        i: I;  finite I;  f0: Init (PLam I F) |]  \
\     ==> F i : A Co B";
by (full_simp_tac (simpset() addsimps [Constrains_eq_constrains]) 1);
by (subgoal_tac "ALL i:I. f0 i : reachable (F i)" 1);
by (blast_tac (claset() addIs [reachable.Init]) 2);
by (dtac PLam_constrains_projection 1);
by (assume_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [drop_set_lift_set_Int2,
			 drop_set_INT_lift_set, reachable_PLam_eq]) 1);
qed "PLam_Constrains_imp_Constrains";


Goal "[| i: I;  finite I;  f0: Init (PLam I F) |]  \
\     ==> (PLam I F : (lift_set i A) Co (lift_set i B)) =  \
\         (F i : A Co B)";
by (blast_tac (claset() addIs [Constrains_imp_PLam_Constrains, 
			       PLam_Constrains_imp_Constrains]) 1);
qed "PLam_Constrains";

Goal "[| i: I;  finite I;  f0: Init (PLam I F) |]  \
\     ==> (PLam I F : Stable (lift_set i A)) = (F i : Stable A)";
by (asm_simp_tac (simpset() delsimps [Init_PLam]
			    addsimps [Stable_def, PLam_Constrains]) 1);
qed "PLam_Stable";


(** const_PLam (no dependence on i) doesn't require the f0 premise **)

Goal "[| (plam x:I. F) : (lift_set i A) Co (lift_set i B);  \
\        i: I;  finite I |]  \
\     ==> F : A Co B";
by (full_simp_tac (simpset() addsimps [Constrains_eq_constrains]) 1);
by (dtac PLam_constrains_projection 1);
by (assume_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [drop_set_INT,
			 drop_set_lift_set_Int2, Collect_conj_eq RS sym,
			 reachable_PLam_eq]) 1);
qed "const_PLam_Constrains_imp_Constrains";

Goal "[| i: I;  finite I |]  \
\     ==> ((plam x:I. F) : (lift_set i A) Co (lift_set i B)) =  \
\         (F : A Co B)";
by (blast_tac (claset() addIs [Constrains_imp_PLam_Constrains, 
			       const_PLam_Constrains_imp_Constrains]) 1);
qed "const_PLam_Constrains";

Goal "[| i: I;  finite I |]  \
\     ==> ((plam x:I. F) : Stable (lift_set i A)) = (F : Stable A)";
by (asm_simp_tac (simpset() addsimps [Stable_def, const_PLam_Constrains]) 1);
qed "const_PLam_Stable";



(*** guarantees properties ***)

Goal "drop_prog i ((lift_prog i F) Join G) = F Join (drop_prog i G)";
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [Acts_Join, image_Un,
				  image_compose RS sym, o_def]) 2);
by (simp_tac (simpset() addsimps [drop_set_lift_set_Int]) 1);
qed "drop_prog_lift_prog_Join";

Goal "(lift_prog i F) Join G = lift_prog i H \
\     ==> H = F Join (drop_prog i G)";
by (dres_inst_tac [("f", "drop_prog i")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);
by (etac sym 1);
qed "lift_prog_Join_eq_lift_prog_D";

Goal "F : X guar Y \
\     ==> lift_prog i F : (lift_prog i `` X) guar (lift_prog i `` Y)";
by (rtac guaranteesI 1);
by Auto_tac;
by (blast_tac (claset() addDs [lift_prog_Join_eq_lift_prog_D, guaranteesD]) 1);
qed "lift_prog_guarantees";

Goalw [PLam_def]
    "[| ALL i:I. F i : X guar Y |] \
\    ==> (PLam I F) : (INT i: I. lift_prog i `` X) \
\                 guar (INT i: I. lift_prog i `` Y)";
by (blast_tac (claset() addIs [guarantees_JN_INT, lift_prog_guarantees]) 1);
qed "guarantees_PLam_INT";

Goalw [PLam_def]
    "[| ALL i:I. F i : X guar Y |] \
\    ==> (PLam I F) : (UN i: I. lift_prog i `` X) \
\                 guar (UN i: I. lift_prog i `` Y)";
by (blast_tac (claset() addIs [guarantees_JN_UN, lift_prog_guarantees]) 1);
qed "guarantees_PLam_UN";
