(*  Title:      HOL/UNITY/PPROD.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Abstraction over replicated components (PLam)
General products of programs (Pi operation)

Some dead wood here!
*)

(*** Basic properties ***)

Goal "Init (PLam I F) = (INT i:I. lift_set i (Init (F i)))";
by (simp_tac (simpset() addsimps [PLam_def, lift_def, lift_set_def]) 1);
qed "Init_PLam";

Addsimps [Init_PLam];

Goal "PLam {} F = SKIP";
by (simp_tac (simpset() addsimps [PLam_def]) 1);
qed "PLam_empty";

Goal "(plam i: I. SKIP) = SKIP";
by (simp_tac (simpset() addsimps [PLam_def,lift_SKIP,JN_constant]) 1);
qed "PLam_SKIP";

Addsimps [PLam_SKIP, PLam_empty];

Goalw [PLam_def] "PLam (insert i I) F = (lift i (F i)) Join (PLam I F)";
by Auto_tac;
qed "PLam_insert";

Goal "((PLam I F) <= H) = (ALL i: I. lift i (F i) <= H)";
by (simp_tac (simpset() addsimps [PLam_def, JN_component_iff]) 1);
qed "PLam_component_iff";

Goalw [PLam_def] "i : I ==> lift i (F i) <= (PLam I F)";
(*blast_tac doesn't use HO unification*)
by (fast_tac (claset() addIs [component_JN]) 1);
qed "component_PLam";


(** Safety & Progress: but are they used anywhere? **)

Goal "[| i : I;  ALL j. F j : preserves snd |] ==>  \
\     (PLam I F : (lift_set i (A <*> UNIV)) co \
\                 (lift_set i (B <*> UNIV)))  =  \
\     (F i : (A <*> UNIV) co (B <*> UNIV))";
by (asm_simp_tac (simpset() addsimps [PLam_def, JN_constrains]) 1);
by (stac (insert_Diff RS sym) 1 THEN assume_tac 1);
by (asm_simp_tac (simpset() addsimps [lift_constrains]) 1);
by (blast_tac (claset() addIs [constrains_imp_lift_constrains]) 1);
qed "PLam_constrains";

Goal "[| i : I;  ALL j. F j : preserves snd |]  \
\     ==> (PLam I F : stable (lift_set i (A <*> UNIV))) = \
\         (F i : stable (A <*> UNIV))";
by (asm_simp_tac (simpset() addsimps [stable_def, PLam_constrains]) 1);
qed "PLam_stable";

Goal "i : I ==> \
\   PLam I F : transient A = (EX i:I. lift i (F i) : transient A)";
by (asm_simp_tac (simpset() addsimps [JN_transient, PLam_def]) 1);
qed "PLam_transient";

(*This holds because the F j cannot change (lift_set i)*)
Goal "[| i : I;  F i : (A <*> UNIV) ensures (B <*> UNIV);  \
\        ALL j. F j : preserves snd |] ==>  \
\     PLam I F : lift_set i (A <*> UNIV) ensures lift_set i (B <*> UNIV)";
by (auto_tac (claset(), 
    simpset() addsimps [ensures_def, PLam_constrains, PLam_transient,
	                lift_transient_eq_disj,
			lift_set_Un_distrib RS sym,
			lift_set_Diff_distrib RS sym,
			Times_Un_distrib1 RS sym,
			Times_Diff_distrib1 RS sym]));
qed "PLam_ensures";

Goal "[| i : I;  \
\        F i : ((A <*> UNIV) - (B <*> UNIV)) co \
\              ((A <*> UNIV) Un (B <*> UNIV));  \
\        F i : transient ((A <*> UNIV) - (B <*> UNIV));  \
\        ALL j. F j : preserves snd |] ==>  \
\     PLam I F : lift_set i (A <*> UNIV) leadsTo lift_set i (B <*> UNIV)";
by (rtac (PLam_ensures RS leadsTo_Basis) 1);
by (rtac ensuresI 2);
by (ALLGOALS assume_tac);
qed "PLam_leadsTo_Basis";


(** invariant **)

Goal "[| F i : invariant (A <*> UNIV);  i : I;  \
\        ALL j. F j : preserves snd |] \
\     ==> PLam I F : invariant (lift_set i (A <*> UNIV))";
by (auto_tac (claset(),
	      simpset() addsimps [PLam_stable, invariant_def]));
qed "invariant_imp_PLam_invariant";


Goal "ALL j. F j : preserves snd \
\     ==> (PLam I F : preserves (v o sub j o fst)) = \
\         (if j: I then F j : preserves (v o fst) else True)";
by (asm_simp_tac (simpset() addsimps [PLam_def, lift_preserves_sub]) 1);
by (Blast_tac 1);
qed "PLam_preserves_fst";
Addsimps [PLam_preserves_fst];

Goal "ALL j. F j : preserves snd ==> PLam I F : preserves snd";
by (asm_simp_tac (simpset() addsimps [PLam_def, lift_preserves_snd_I]) 1);
qed "PLam_preserves_snd";
Addsimps [PLam_preserves_snd];
AddIs [PLam_preserves_snd];


(*** guarantees properties ***)

(*This rule looks unsatisfactory because it refers to "lift".  One must use
  lift_guarantees_eq_lift_inv to rewrite the first subgoal and
  something like lift_preserves_sub to rewrite the third.  However there's
  no obvious way to alternative for the third premise.*)
Goalw [PLam_def]
    "[| lift i (F i): X guarantees Y;  i : I;  \
\       OK I (%i. lift i (F i)) |]  \
\    ==> (PLam I F) : X guarantees Y"; 
by (asm_simp_tac (simpset() addsimps [guarantees_JN_I]) 1);
qed "guarantees_PLam_I";

Goal "Allowed (PLam I F) = (INT i:I. lift i ` Allowed(F i))";
by (simp_tac (simpset() addsimps [PLam_def]) 1); 
qed "Allowed_PLam";
Addsimps [Allowed_PLam];

Goal "(PLam I F) : preserves v = (ALL i:I. F i : preserves (v o lift_map i))";
by (simp_tac (simpset() addsimps [PLam_def, lift_def, rename_preserves]) 1); 
qed "PLam_preserves";
Addsimps [PLam_preserves];

(**UNUSED
    (*The f0 premise ensures that the product is well-defined.*)
    Goal "[| PLam I F : invariant (lift_set i A);  i : I;  \
    \        f0: Init (PLam I F) |] ==> F i : invariant A";
    by (auto_tac (claset(),
		  simpset() addsimps [invariant_def]));
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
		  simpset() addsimps [invariant_def]));
    qed "const_PLam_invariant";
**)


(**UNUSED
    (** Reachability **)

    Goal "[| f : reachable (PLam I F);  i : I |] ==> f i : reachable (F i)";
    by (etac reachable.induct 1);
    by (auto_tac (claset() addIs reachable.intrs, simpset()));
    qed "reachable_PLam";

    (*Result to justify a re-organization of this file*)
    Goal "{f. ALL i:I. f i : R i} = (INT i:I. lift_set i (R i))";
    by Auto_tac;
    result();

    Goal "reachable (PLam I F) <= (INT i:I. lift_set i (reachable (F i)))";
    by (force_tac (claset() addSDs [reachable_PLam], simpset()) 1);
    qed "reachable_PLam_subset1";

    (*simplify using reachable_lift??*)
    Goal "[| i ~: I;  A : reachable (F i) |]     \
    \  ==> ALL f. f : reachable (PLam I F)      \
    \             --> f(i:=A) : reachable (lift i (F i) Join PLam I F)";
    by (etac reachable.induct 1);
    by (ALLGOALS Clarify_tac);
    by (etac reachable.induct 1);
    (*Init, Init case*)
    by (force_tac (claset() addIs reachable.intrs, simpset()) 1);
    (*Init of F, action of PLam F case*)
    by (res_inst_tac [("act","act")] reachable.Acts 1);
    by (Force_tac 1);
    by (assume_tac 1);
    by (force_tac (claset() addIs [ext], simpset()) 1);
    (*induction over the 2nd "reachable" assumption*)
    by (eres_inst_tac [("xa","f")] reachable.induct 1);
    (*Init of PLam F, action of F case*)
    by (res_inst_tac [("act","lift_act i act")] reachable.Acts 1);
    by (Force_tac 1);
    by (force_tac (claset() addIs [reachable.Init], simpset()) 1);
    by (force_tac (claset() addIs [ext], simpset() addsimps [lift_act_def]) 1);
    (*last case: an action of PLam I F*)
    by (res_inst_tac [("act","acta")] reachable.Acts 1);
    by (Force_tac 1);
    by (assume_tac 1);
    by (force_tac (claset() addIs [ext], simpset()) 1);
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
		  simpset() addsimps [constrains_def, PLam_def]));
    by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
    qed "Constrains_imp_PLam_Constrains";



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

    Goalw [Increasing_def]
	 "[| i: I;  finite I |]  \
    \     ==> ((plam x:I. F) : Increasing (f o sub i)) = (F : Increasing f)";
    by (subgoal_tac "ALL z. {s. z <= (f o sub i) s} = lift_set i {s. z <= f s}" 1);
    by (asm_simp_tac (simpset() addsimps [lift_set_sub]) 2);
    by (asm_full_simp_tac
	(simpset() addsimps [finite_lessThan, const_PLam_Stable]) 1);
    qed "const_PLam_Increasing";
**)

