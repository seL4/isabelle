(*  Title: 	ZF/IMP/Denotation.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

open Denotation;

(**** Rewrite Rules fuer A,B,C ****)

val A_rewrite_rules =
     [A_nat_def,A_loc_def,A_op1_def,A_op2_def];

val B_rewrite_rules =
     [B_true_def,B_false_def,B_op_def,B_not_def,B_and_def,B_or_def]

val C_rewrite_rules = 
     [C_skip_def,C_assign_def,C_comp_def,C_if_def,C_while_def]; 

(**** Type_intr for A ****)

val A_type = prove_goal Denotation.thy
	"!!a.[|a:aexp; sigma:loc->nat|] ==> A(a,sigma):nat"
   (fn _ => [(etac Aexp.induct 1),
             (rewrite_goals_tac A_rewrite_rules),
             (ALLGOALS (fast_tac (ZF_cs addSIs [apply_type])))]);

(**** Type_intr for B ****)

val B_type = prove_goal Denotation.thy
	"!!b. [|b:bexp; sigma:loc->nat|] ==> B(b,sigma):bool"
   (fn _ => [(etac Bexp.induct 1),
             (rewrite_goals_tac B_rewrite_rules),
             (ALLGOALS (fast_tac (ZF_cs 
                          addSIs [apply_type,A_type]@bool_typechecks)))]);

(**** C_subset ****)

val C_subset = prove_goal Denotation.thy 
	"!!c. c:com ==> C(c) <= (loc->nat)*(loc->nat)"
   (fn _ => [(etac Com.induct 1),
             (rewrite_tac C_rewrite_rules),
             (ALLGOALS (fast_tac (comp_cs addDs [lfp_subset RS subsetD])))]);

(**** Type_elims for C ****)

val C_type = prove_goal Denotation.thy
	"[| <x,y>:C(c); c:com; 					\
\	     !!c. [| x:loc->nat; y:loc->nat |]  ==> R |]	\
\	  ==> R"
     (fn prems => [(cut_facts_tac prems 1),
                   (fast_tac (ZF_cs addSIs prems 
                                    addDs  [(C_subset RS subsetD)]) 1)]);

val C_type_fst = prove_goal Denotation.thy
	"[| x:C(c); c:com; 					\
\	     !!c. [| fst(x):loc->nat |]  ==> R |]	\
\	  ==> R"
     (fn prems => [(cut_facts_tac prems 1),
                   (resolve_tac prems 1),
                   (dtac (C_subset RS subsetD) 1),
                   (atac 1),
                   (etac SigmaE 1),
                   (asm_simp_tac ZF_ss 1)]);


(**** bnd_mono (nat->nat*nat->nat,Gamma(b,c) ****)

val Gamma_bnd_mono = prove_goalw Denotation.thy [bnd_mono_def,Gamma_def]
	"!!c. c:com ==> bnd_mono ((loc->nat)*(loc->nat),Gamma(b,c))"
     (fn prems => [(fast_tac (comp_cs addSIs [compI] addEs [C_type]) 1)]);

(**** End ***)
