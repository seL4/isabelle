(*  Title:      HOL/UNITY/PPROD.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)


val rinst = read_instantiate_sg (sign_of thy);

    (*** General lemmas ***)

Goalw [sharing_def] "((x,y): sharing Rsh A) = (x: A & y : range (Rsh x))";
by Auto_tac;
qed "sharing_iff";
AddIffs [sharing_iff]; 

Goalw [sharing_def] "(sharing Rsh A <= sharing Rsh B) = (A <= B)";
by Auto_tac;
qed "sharing_subset_iff";
AddIffs [sharing_subset_iff]; 

Goalw [sharing_def] "sharing Rsh (A Un B) = sharing Rsh A Un sharing Rsh B";
by Auto_tac;
qed "sharing_Un_distrib";

Goalw [sharing_def] "sharing Rsh (A Int B) = sharing Rsh A Int sharing Rsh B";
by Auto_tac;
qed "sharing_Int_distrib";

Goalw [sharing_def] "sharing Rsh (A - B) = sharing Rsh A - sharing Rsh B";
by Auto_tac;
qed "sharing_Diff_distrib";

Goalw [sharing_def] "sharing Rsh (Union A) = (UN X:A. sharing Rsh X)";
by (Blast_tac 1);
qed "sharing_Union";

Goal "(sharing Rsh A <= - sharing Rsh B) = (A <= - B)";
by (force_tac (claset(),simpset() addsimps [sharing_def, Image_iff]) 1);
qed "Lcopy_subset_Compl_eq";

Goal "(((a,b), (a',b')) : Lcopy_act Rsh act) = \
\     ((a,a'):act & Rsh a b = b & Rsh a' b = b')";
by (simp_tac (simpset() addsimps [Lcopy_act_def]) 1);
qed "mem_Lcopy_act_iff";
AddIffs [mem_Lcopy_act_iff]; 

(*NEEDED????????????????*)
Goal "[| (a,a'):act; Rsh a b = b |] ==> (((a,b), (a', Rsh a' b)) : Lcopy_act Rsh act)";
by Auto_tac;
qed "mem_Lcopy_actI";


Goal "act : Acts F \
\     ==> Lcopy_act Rsh act <= \
\         sharing Rsh (States F) Times sharing Rsh (States F)";
by (auto_tac (claset() addIs [range_eqI, sym]
                       addDs [impOfSubs Acts_subset_Pow_States], 
              simpset()));
qed "Lcopy_act_subset_Times";



Open_locale "Share";

val overwrite = thm "overwrite";
Addsimps [overwrite];

Goal "Lcopy_act Rsh act ^^ sharing Rsh A = sharing Rsh (act ^^ A)";
by (force_tac (claset(),simpset() addsimps [sharing_def, Image_iff]) 1);
qed "Lcopy_act_Image";
Addsimps [Lcopy_act_Image];



Goal "(Lcopy_act Rsh act ^^ sharing Rsh A <= sharing Rsh B) = (act ^^ A <= B)";
by (force_tac (claset(),simpset() addsimps [sharing_def, Image_iff]) 1);
qed "Lcopy_act_Image_subset_eq";

Goal "Domain (Lcopy_act Rsh act) = sharing Rsh (Domain act)";
by (auto_tac (claset() addIs [sym], simpset() addsimps [Domain_iff]));
qed "Domain_Lcopy_act"; 

(*?? needed??
Goal "(Lcopy_act Rsh act) ^^ (SIGMA x:A. B Int range(Rsh x)) = (SIGMA x: act^^A. Rsh x `` B)";
by (auto_tac (claset(), simpset() addsimps [Image_iff]));
qed "Image_Lcopy_act"; 
**)

Goal "Lcopy_act Rsh (diag A) = diag (sharing Rsh A)";
by (auto_tac (claset() addIs [sym], simpset()));
qed "Lcopy_diag";

Addsimps [Lcopy_diag];


(**** Lcopy ****)

(*** Basic properties ***)

Goalw [Lcopy_def] "States (Lcopy Rsh F) = sharing Rsh (States F)";
by Auto_tac;
qed "States_Lcopy";

Goalw [Lcopy_def] "Init (Lcopy Rsh F) = sharing Rsh (Init F)";
by (auto_tac (claset() addIs [impOfSubs Init_subset_States], simpset()));
qed "Init_Lcopy";

Goal "diag (sharing Rsh (States F)) : Lcopy_act Rsh `` Acts F";
by (rtac image_eqI 1);
by (rtac diag_in_Acts 2);
by Auto_tac;
val lemma = result();

Goal "Acts (Lcopy Rsh F) = (Lcopy_act Rsh `` Acts F)";
by (auto_tac (claset() addSIs [lemma] 
                       addDs [impOfSubs Acts_subset_Pow_States], 
	      simpset() addsimps [Lcopy_def, Lcopy_act_subset_Times, 
				  image_subset_iff]));
qed "Acts_Lcopy";

Addsimps [States_Lcopy, Init_Lcopy, Acts_Lcopy];

Goalw [SKIP_def] "Lcopy Rsh (SKIP A) = SKIP(sharing Rsh A)";
by (rtac program_equalityI 1);
by Auto_tac;
qed "Lcopy_SKIP";


(*** Safety: constrains, stable ***)

Goal "(Lcopy Rsh F : constrains (sharing Rsh A) (sharing Rsh B)) = \
\     (F : constrains A B)";
by (simp_tac (simpset() addsimps [constrains_def, 
				  Lcopy_act_Image_subset_eq]) 1);
qed "Lcopy_constrains";

Goal "[| Lcopy Rsh F : constrains A B;  A <= States (Lcopy Rsh F) |]  \
\     ==> F : constrains (Domain A) (Domain B)";
by (force_tac (claset() addIs [rev_bexI], 
	       simpset() addsimps [constrains_def, sharing_def, Image_iff]) 1);
qed "Lcopy_constrains_Domain";

Goal "(Lcopy Rsh F : stable (sharing Rsh A)) = (F : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, Lcopy_constrains]) 1);
qed "Lcopy_stable";

Goal "(Lcopy Rsh F : invariant (sharing Rsh A)) = (F : invariant A)";
by (asm_simp_tac (simpset() addsimps [invariant_def, Lcopy_stable]) 1);
qed "Lcopy_invariant";

(** Substitution Axiom versions: Constrains, Stable **)

Goal "p : reachable (Lcopy Rsh F) \
\     ==> (%(a,b). a : reachable F & b : range (Rsh a)) p";
by (etac reachable.induct 1);
by (auto_tac
    (claset() addIs reachable.intrs,
     simpset() addsimps [Acts_Lcopy]));
qed "reachable_Lcopy_fst";

Goal "(a,b) : reachable (Lcopy Rsh F) \
\     ==> a : reachable F & b : range (Rsh a)";
by (force_tac (claset() addSDs [reachable_Lcopy_fst], simpset()) 1);
qed "reachable_LcopyD";

Goal "reachable (Lcopy Rsh F) = sharing Rsh (reachable F)";
by (rtac equalityI 1);
by (force_tac (claset() addSDs [reachable_LcopyD], simpset()) 1);
by (Clarify_tac 1);
by (etac reachable.induct 1);
by (ALLGOALS (force_tac (claset() addIs reachable.intrs, 
			 simpset())));
qed "reachable_Lcopy_eq";

Goal "(Lcopy Rsh F : Constrains (sharing Rsh A) (sharing Rsh B)) =  \
\     (F : Constrains A B)";
by (simp_tac
    (simpset() addsimps [Constrains_def, reachable_Lcopy_eq, 
			 Lcopy_constrains, sharing_Int_distrib RS sym]) 1);
qed "Lcopy_Constrains";

Goal "(Lcopy Rsh F : Stable (sharing Rsh A)) = (F : Stable A)";
by (simp_tac (simpset() addsimps [Stable_def, Lcopy_Constrains]) 1);
qed "Lcopy_Stable";


(*** Progress: transient, ensures ***)

Goal "(Lcopy Rsh F : transient (sharing Rsh A)) = (F : transient A)";
by (auto_tac (claset(),
	      simpset() addsimps [transient_def, Lcopy_subset_Compl_eq,
				  Domain_Lcopy_act]));
qed "Lcopy_transient";

Goal "(Lcopy Rsh F : ensures (sharing Rsh A) (sharing Rsh B)) = \
\     (F : ensures A B)";
by (simp_tac
    (simpset() addsimps [ensures_def, Lcopy_constrains, Lcopy_transient, 
			 sharing_Un_distrib RS sym, 
			 sharing_Diff_distrib RS sym]) 1);
qed "Lcopy_ensures";

Goal "F : leadsTo A B \
\     ==> Lcopy Rsh F : leadsTo (sharing Rsh A) (sharing Rsh B)";
by (etac leadsTo_induct 1);
by (asm_simp_tac (simpset() addsimps [leadsTo_UN, sharing_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (asm_simp_tac (simpset() addsimps [leadsTo_Basis, Lcopy_ensures]) 1);
qed "leadsTo_imp_Lcopy_leadsTo";

(**
    Goal "Lcopy Rsh F : ensures A B ==> F : ensures (Domain A) (Domain B)";
    by (full_simp_tac
	(simpset() addsimps [ensures_def, Lcopy_constrains, Lcopy_transient, 
			     Domain_Un_eq RS sym,
			     sharing_Un_distrib RS sym, 
			     sharing_Diff_distrib RS sym]) 1);
    by (safe_tac (claset() addSDs [Lcopy_constrains_Domain]));
    by (etac constrains_weaken_L 1);
    by (Blast_tac 1);
    (*NOT able to prove this:
    Lcopy Rsh F : ensures A B ==> F : ensures (Domain A) (Domain B)
     1. [| Lcopy Rsh F : transient (A - B);
	   F : constrains (Domain (A - B)) (Domain (A Un B)) |]
	==> F : transient (Domain A - Domain B)
    **)


    Goal "Lcopy Rsh F : leadsTo AU BU ==> F : leadsTo (Domain AU) (Domain BU)";
    by (etac leadsTo_induct 1);
    by (full_simp_tac (simpset() addsimps [Domain_Union]) 3);
    by (blast_tac (claset() addIs [leadsTo_UN]) 3);
    by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
    by (rtac leadsTo_Basis 1);
    (*...and so CANNOT PROVE THIS*)


    (*This also seems impossible to prove??*)
    Goal "(Lcopy Rsh F : leadsTo (sharing Rsh A) (sharing Rsh B)) = \
    \     (F : leadsTo A B)";
**)


(**** PPROD ****)

(*** Basic properties ***)

Goalw [lift_set_def] "(f : lift_set i A) = (f i : A)";
by Auto_tac;
qed "lift_set_iff";
AddIffs [lift_set_iff];

Goalw [lift_act_def] "lift_act i (diag A) = (diag (lift_set i A))";
by Auto_tac;
qed "lift_act_diag";
Addsimps [lift_act_diag];

Goalw [lift_prog_def] "States (lift_prog i F) = (lift_set i (States F))";
by Auto_tac;
qed "States_lift_prog";
Addsimps [States_lift_prog];

Goalw [lift_prog_def] "Init (lift_prog i F) = (lift_set i (Init F))";
by (auto_tac (claset() addIs [impOfSubs Init_subset_States], simpset()));
qed "Init_lift_prog";
Addsimps [Init_lift_prog];

Goalw [lift_act_def]
     "act : Acts F \
\     ==> lift_act i act <= lift_set i (States F) Times lift_set i (States F)";
by (force_tac (claset()  addIs [range_eqI, sym]
                    addDs [impOfSubs Acts_subset_Pow_States], 
              simpset()) 1);
qed "lift_act_subset_Times";

Goalw [lift_prog_def] "Acts (lift_prog i F) = lift_act i `` Acts F";
by (auto_tac (claset() addIs [diag_in_Acts RSN (2,image_eqI)], 
	      simpset() addsimps [lift_act_subset_Times, 
				  image_subset_iff]));
qed "Acts_lift_prog";

Goalw [PPROD_def] "States (PPROD I F) = (INT i:I. lift_set i (States (F i)))";
by Auto_tac;
qed "States_PPROD";
Addsimps [States_PPROD];

Goalw [PPROD_def] "Init (PPROD I F) = (INT i:I. lift_set i (Init (F i)))";
by Auto_tac;
qed "Init_PPROD";
Addsimps [Init_PPROD];

Goalw [lift_act_def]
    "((f,f') : lift_act i act) = (EX s'. f' = f(i := s') & (f i, s') : act)";
by (Blast_tac 1);
qed "lift_act_eq";
AddIffs [lift_act_eq];

Goalw [eqStates_def] "eqStates I (%i. lift_prog i F)";

Goalw [eqStates_def] "eqStates I (%i. lift_prog i (F i))";

Goal "[| eqStates I (%i. lift_prog i (F i));  i: I |] \
\     ==> Acts (PPROD I F) = (UN i:I. lift_act i `` Acts (F i))";
by (auto_tac (claset(),
	      simpset() addsimps [PPROD_def, Acts_lift_prog, Acts_JN]));
qed "Acts_PPROD";

Goal "PPROD {} F = SKIP UNIV";
by (simp_tac (simpset() addsimps [PPROD_def]) 1);
qed "Acts_PPROD";

Goal "i : I ==> (PPI i: I. SKIP A) = SKIP (INT i:I. lift_set i A)";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [eqStates_def, Acts_lift_prog, 
				  SKIP_def, Acts_PPROD]));
qed "PPROD_SKIP";

Goal "PPROD {} F = SKIP";
by (simp_tac (simpset() addsimps [PPROD_def]) 1);
qed "PPROD_empty";

Addsimps [PPROD_SKIP, PPROD_empty];

Goalw [PPROD_def]
    "PPROD (insert i I) F = (lift_prog i (F i)) Join (PPROD I F)";
by Auto_tac;
qed "PPROD_insert";

Goalw [PPROD_def] "i : I ==> component (lift_prog i (F i)) (PPROD I F)";
(*blast_tac doesn't use HO unification*)
by (fast_tac (claset() addIs [component_JN]) 1);
qed "component_PPROD";


(*** Safety: constrains, stable, invariant ***)

(** 1st formulation of lifting **)

Goal "(lift_prog i F : constrains (lift_set i A) (lift_set i B))  =  \
\     (F : constrains A B)";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, Acts_lift_prog]));
by (Blast_tac 2);
by (Force_tac 1);
qed "lift_prog_constrains_eq";

Goal "(lift_prog i F : stable (lift_set i A)) = (F : stable A)";
by (simp_tac (simpset() addsimps [stable_def, lift_prog_constrains_eq]) 1);
qed "lift_prog_stable_eq";

(*This one looks strange!  Proof probably is by case analysis on i=j.*)
Goal "F i : constrains A B  \
\     ==> lift_prog j (F j) : constrains (lift_set i A) (lift_set i B)";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, Acts_lift_prog]));
by (REPEAT (Blast_tac 1));
qed "constrains_imp_lift_prog_constrains";

Goal "i : I ==>  \
\     (PPROD I F : constrains (lift_set i A) (lift_set i B))  =  \
\     (F i : constrains A B)";
by (asm_simp_tac (simpset() addsimps [PPROD_def, constrains_JN]) 1);
by (blast_tac (claset() addIs [lift_prog_constrains_eq RS iffD1, 
			       constrains_imp_lift_prog_constrains]) 1);
qed "PPROD_constrains";

Goal "i : I ==> (PPROD I F : stable (lift_set i A)) = (F i : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, PPROD_constrains]) 1);
qed "PPROD_stable";


(** 2nd formulation of lifting **)

Goal "[| lift_prog i F : constrains AA BB |] \
\     ==> F : constrains (Applyall AA i) (Applyall BB i)";
by (auto_tac (claset(), 
	      simpset() addsimps [Applyall_def, constrains_def, 
				  Acts_lift_prog]));
by (force_tac (claset() addSIs [rinst [("x", "?ff(i := ?u)")] image_eqI],
	       simpset()) 1);
qed "lift_prog_constrains_projection";

Goal "[| PPROD I F : constrains AA BB;  i: I |] \
\     ==> F i : constrains (Applyall AA i) (Applyall BB i)";
by (rtac lift_prog_constrains_projection 1);
(*rotate this assumption to be last*)
by (dres_inst_tac [("psi", "PPROD I F : ?C")] asm_rl 1);
by (asm_full_simp_tac (simpset() addsimps [PPROD_def, constrains_JN]) 1);
qed "PPROD_constrains_projection";


(** invariant **)

Goal "F : invariant A ==> lift_prog i F : invariant (lift_set i A)";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def, lift_prog_stable_eq]));
qed "invariant_imp_lift_prog_invariant";

Goal "[| lift_prog i F : invariant (lift_set i A) |] ==> F : invariant A";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def, lift_prog_stable_eq]));
qed "lift_prog_invariant_imp_invariant";

(*NOT clear that the previous lemmas help in proving this one.*)
Goal "[| F i : invariant A;  i : I |] ==> PPROD I F : invariant (lift_set i A)";
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


(*** Substitution Axiom versions: Constrains, Stable ***)

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


(** Constrains **)

Goal "[| F i : Constrains A B;  i: I;  finite I |]  \
\     ==> PPROD I F : Constrains (lift_set i A) (lift_set i B)";
by (auto_tac
    (claset(),
     simpset() addsimps [Constrains_def, Collect_conj_eq RS sym,
			 reachable_PPROD_eq]));
by (auto_tac (claset(), 
              simpset() addsimps [constrains_def, Acts_lift_prog, PPROD_def,
                                  Acts_JN]));
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "Constrains_imp_PPROD_Constrains";

Goal "[| ALL i:I. f0 i : R i;  i: I |] \
\     ==> Applyall {f. (ALL i:I. f i : R i) & f i : A} i = R i Int A";
by (force_tac (claset() addSIs [rinst [("x", "?ff(i := ?u)")] exI],
	       simpset() addsimps [Applyall_def]) 1);
qed "Applyall_Int_depend";

(*Again, we need the f0 premise because otherwise Constrains holds trivially
  for PPROD I F.*)
Goal "[| PPROD I F : Constrains (lift_set i A) (lift_set i B);  \
\        i: I;  finite I;  f0: Init (PPROD I F) |]  \
\     ==> F i : Constrains A B";
by (full_simp_tac (simpset() addsimps [Constrains_def]) 1);
by (subgoal_tac "ALL i:I. f0 i : reachable (F i)" 1);
by (blast_tac (claset() addIs [reachable.Init]) 2);
by (dtac PPROD_constrains_projection 1);
by (assume_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [Applyall_Int_depend, Collect_conj_eq RS sym,
			 reachable_PPROD_eq]) 1);
qed "PPROD_Constrains_imp_Constrains";


Goal "[| i: I;  finite I;  f0: Init (PPROD I F) |]  \
\     ==> (PPROD I F : Constrains (lift_set i A) (lift_set i B)) =  \
\         (F i : Constrains A B)";
by (blast_tac (claset() addIs [Constrains_imp_PPROD_Constrains, 
			       PPROD_Constrains_imp_Constrains]) 1);
qed "PPROD_Constrains";

Goal "[| i: I;  finite I;  f0: Init (PPROD I F) |]  \
\     ==> (PPROD I F : Stable (lift_set i A)) = (F i : Stable A)";
by (asm_simp_tac (simpset() delsimps [Init_PPROD]
			    addsimps [Stable_def, PPROD_Constrains]) 1);
qed "PPROD_Stable";


(** PFUN (no dependence on i) doesn't require the f0 premise **)

Goal "i: I ==> Applyall {f. (ALL i:I. f i : R) & f i : A} i = R Int A";
by (force_tac (claset(), simpset() addsimps [Applyall_def]) 1);
qed "Applyall_Int";

Goal "[| (PPI x:I. F) : Constrains (lift_set i A) (lift_set i B);  \
\        i: I;  finite I |]  \
\     ==> F : Constrains A B";
by (full_simp_tac (simpset() addsimps [Constrains_def]) 1);
by (dtac PPROD_constrains_projection 1);
by (assume_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [Applyall_Int, Collect_conj_eq RS sym,
			 reachable_PPROD_eq]) 1);
qed "PFUN_Constrains_imp_Constrains";

Goal "[| i: I;  finite I |]  \
\     ==> ((PPI x:I. F) : Constrains (lift_set i A) (lift_set i B)) =  \
\         (F : Constrains A B)";
by (blast_tac (claset() addIs [Constrains_imp_PPROD_Constrains, 
			       PFUN_Constrains_imp_Constrains]) 1);
qed "PFUN_Constrains";

Goal "[| i: I;  finite I |]  \
\     ==> ((PPI x:I. F) : Stable (lift_set i A)) = (F : Stable A)";
by (asm_simp_tac (simpset() addsimps [Stable_def, PFUN_Constrains]) 1);
qed "PFUN_Stable";



(*** guarantees properties ***)

(*We only need act2=Id but the condition used is very weak*)
Goal "(x,y): act2 ==> fst_act (act1 Lcopy_act act2) = act1";
by (auto_tac (claset(), simpset() addsimps [fst_act_def, Lcopy_act_def]));
qed "fst_act_Lcopy_act";
Addsimps [fst_act_Lcopy_act];


Goal "(Lcopy Rsh F) Join G = Lcopy H ==> EX J. H = F Join J";
by (etac program_equalityE 1);
by (auto_tac (claset(), simpset() addsimps [Acts_Join]));
by (res_inst_tac 
     [("x", "mk_program(Domain (Init G), fst_act `` Acts G)")] exI 1);
by (rtac program_equalityI 1);
(*Init*)
by (simp_tac (simpset() addsimps [Acts_Join]) 1);
by (blast_tac (claset() addEs [equalityE]) 1);
(*Now for the Actions*)
by (dres_inst_tac [("f", "op `` fst_act")] arg_cong 1);
by (asm_full_simp_tac 
    (simpset() addsimps [insert_absorb, Acts_Lcopy, Acts_Join,
			 image_Un, image_compose RS sym, o_def]) 1);
qed "Lcopy_Join_eq_Lcopy_D";


Goal "F : X guarantees Y \
\     ==> Lcopy Rsh F : (Lcopy `` X) guarantees (Lcopy `` Y)";
by (rtac guaranteesI 1);
by Auto_tac;
by (blast_tac (claset() addDs [Lcopy_Join_eq_Lcopy_D, guaranteesD]) 1);
qed "Lcopy_guarantees";


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


