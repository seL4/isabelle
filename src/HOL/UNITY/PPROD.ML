(*  Title:      HOL/UNITY/PPROD.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Abstraction over replicated components (PLam)
General products of programs (Pi operation)

It is not clear that any of this is good for anything.
*)


(*** Basic properties ***)

Goalw [PLam_def] "Init (PLam I F) = (INT i:I. lift_set i (Init (F i)))";
by Auto_tac;
qed "Init_PLam";
Addsimps [Init_PLam];

Goal "Acts (PLam I F) = insert Id (UN i:I. lift_act i `` Acts (F i))";
by (auto_tac (claset(),
	      simpset() addsimps [PLam_def]));
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

Goalw [PLam_def] "i : I ==> lift_prog i (F i) <= (PLam I F)";
(*blast_tac doesn't use HO unification*)
by (fast_tac (claset() addIs [component_JN]) 1);
qed "component_PLam";


(** Safety & Progress **)

Goal "i : I ==>  \
\     (PLam I F : (lift_set i A) co (lift_set i B))  =  \
\     (F i : A co B)";
by (asm_simp_tac (simpset() addsimps [PLam_def, JN_constrains]) 1);
by (blast_tac (claset() addIs [lift_prog_constrains RS iffD1, 
			       constrains_imp_lift_prog_constrains]) 1);
qed "PLam_constrains";

Goal "i : I ==> (PLam I F : stable (lift_set i A)) = (F i : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, PLam_constrains]) 1);
qed "PLam_stable";

Goal "i : I ==> \
\   PLam I F : transient A = (EX i:I. lift_prog i (F i) : transient A)";
by (asm_simp_tac (simpset() addsimps [JN_transient, PLam_def]) 1);
qed "PLam_transient";

Addsimps [PLam_constrains, PLam_stable, PLam_transient];

Goal "[| i : I;  F i : A ensures B |] ==>  \
\     PLam I F : (lift_set i A) ensures lift_set i B";
by (auto_tac (claset(), 
	      simpset() addsimps [ensures_def, lift_prog_transient_eq_disj]));
qed "PLam_ensures";

Goal "[| i : I;  F i : (A-B) co (A Un B);  F i : transient (A-B) |] ==>  \
\     PLam I F : (lift_set i A) leadsTo lift_set i B";
by (rtac (PLam_ensures RS leadsTo_Basis) 1);
by (rtac ensuresI 2);
by (ALLGOALS assume_tac);
qed "PLam_leadsTo_Basis";

Goal "[| PLam I F : AA co BB;  i: I |] \
\     ==> F i : (drop_set i AA) co (drop_set i BB)";
by (rtac lift_prog_constrains_drop_set 1);
(*rotate this assumption to be last*)
by (dres_inst_tac [("psi", "PLam I F : ?C")] asm_rl 1);
by (asm_full_simp_tac (simpset() addsimps [PLam_def, JN_constrains]) 1);
qed "PLam_constrains_drop_set";


(** invariant **)

Goal "[| F i : invariant A;  i : I |] \
\     ==> PLam I F : invariant (lift_set i A)";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def]));
qed "invariant_imp_PLam_invariant";

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


(** Reachability **)

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
by (Force_tac 1);
by (assume_tac 1);
by (force_tac (claset() addIs [ext], simpset() addsimps [Acts_PLam]) 1);
(*induction over the 2nd "reachable" assumption*)
by (eres_inst_tac [("xa","f")] reachable.induct 1);
(*Init of PLam F, action of F case*)
by (res_inst_tac [("act","lift_act i act")] reachable.Acts 1);
by (Force_tac 1);
by (force_tac (claset() addIs [reachable.Init], simpset()) 1);
by (force_tac (claset() addIs [ext], simpset() addsimps [lift_act_def]) 1);
(*last case: an action of PLam I F*)
by (rtac reachable.Acts 1);
by (Force_tac 1);
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
              simpset() addsimps [constrains_def, PLam_def]));
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "Constrains_imp_PLam_Constrains";

Goal "[| ALL j:I. f0 j : A j;   i: I |] \
\     ==> drop_set i (INT j:I. lift_set j (A j)) = A i";
by (force_tac (claset() addSIs [image_eqI'],
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
by (dtac PLam_constrains_drop_set 1);
by (assume_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [drop_set_Int_lift_set2,
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
by (dtac PLam_constrains_drop_set 1);
by (assume_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [drop_set_INT,
			 drop_set_Int_lift_set2, Collect_conj_eq RS sym,
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

Goalw [Increasing_def]
     "[| i: I;  finite I |]  \
\     ==> ((plam x:I. F) : Increasing (f o sub i)) = (F : Increasing f)";
by (subgoal_tac "ALL z. {s. z <= (f o sub i) s} = lift_set i {s. z <= f s}" 1);
by (asm_simp_tac (simpset() addsimps [lift_set_sub]) 2);
by (asm_full_simp_tac
    (simpset() addsimps [finite_lessThan, const_PLam_Stable]) 1);
qed "const_PLam_Increasing";


(*** guarantees properties ***)

Goalw [PLam_def]
    "[| i : I;  lift_prog i (F i): X guarantees Y |]  \
\    ==> (PLam I F) : X guarantees Y";
by (asm_simp_tac (simpset() addsimps [guarantees_JN_I]) 1);
qed "guarantees_PLam_I";

Goalw [PLam_def]
    "[| ALL i:I. F i : X guarantees Y |] \
\    ==> (PLam I F) : (INT i: I. lift_prog i `` X) \
\                 guarantees (INT i: I. lift_prog i `` Y)";
by (blast_tac (claset() addIs [guarantees_JN_INT, lift_prog_guarantees]) 1);
bind_thm ("guarantees_PLam_INT", ballI RS result());

Goalw [PLam_def]
    "[| ALL i:I. F i : X guarantees Y |] \
\    ==> (PLam I F) : (UN i: I. lift_prog i `` X) \
\                 guarantees (UN i: I. lift_prog i `` Y)";
by (blast_tac (claset() addIs [guarantees_JN_UN, lift_prog_guarantees]) 1);
bind_thm ("guarantees_PLam_UN", ballI RS result());
