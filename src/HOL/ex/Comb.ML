(*  Title:      HOL/ex/comb.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1996  University of Cambridge

Combinatory Logic example: the Church-Rosser Theorem
Curiously, combinators do not include free variables.

Example taken from
    J. Camilleri and T. F. Melham.
    Reasoning with Inductively Defined Relations in the HOL Theorem Prover.
    Report 265, University of Cambridge Computer Laboratory, 1992.

HOL system proofs may be found in
/usr/groups/theory/hvg-aftp/contrib/rule-induction/cl.ml
*)

open Comb;


(*** Reflexive/Transitive closure preserves the Church-Rosser property 
     So does the Transitive closure; use r_into_trancl instead of rtrancl_refl
***)

val [_, spec_mp] = [spec] RL [mp];

(*Strip lemma.  The induction hyp is all but the last diamond of the strip.*)
goalw Comb.thy [diamond_def]
    "!!r. [| diamond(r);  (x,y):r^* |] ==> \ 
\         ALL y'. (x,y'):r --> (EX z. (y',z): r^* & (y,z): r)";
by (etac rtrancl_induct 1);
by (fast_tac (HOL_cs addIs [rtrancl_refl]) 1);
by (slow_best_tac (set_cs addIs [r_into_rtrancl RSN (2, rtrancl_trans)]
                          addSDs [spec_mp]) 1);
val diamond_strip_lemmaE = result() RS spec RS mp RS exE;

val [major] = goal Comb.thy "diamond(r) ==> diamond(r^*)";
by (rewtac diamond_def);  (*unfold only in goal, not in premise!*)
by (rtac (impI RS allI RS allI) 1);
by (etac rtrancl_induct 1);
by (fast_tac (set_cs addIs [rtrancl_refl]) 1);
by (ALLGOALS
    (slow_best_tac (set_cs addIs [r_into_rtrancl, rtrancl_trans]
                           addEs [major RS diamond_strip_lemmaE])));
qed "diamond_rtrancl";


(*** Results about Contraction ***)

(** Non-contraction results **)

(*Derive a case for each combinator constructor*)
val K_contractE = contract.mk_cases comb.simps "K -1-> z";
val S_contractE = contract.mk_cases comb.simps "S -1-> z";
val Ap_contractE = contract.mk_cases comb.simps "x#y -1-> z";

val contract_cs =
    HOL_cs addIs  contract.intrs
	   addSEs [K_contractE, S_contractE, Ap_contractE]
	   addss  (HOL_ss addsimps comb.simps);

goalw Comb.thy [I_def] "!!z. I -1-> z ==> P";
by (fast_tac contract_cs 1);
qed "I_contract_E";

(*Unused*)
goal Comb.thy "!!x z. K#x -1-> z ==> (EX y. z = K#y & x -1-> y)";
by (fast_tac contract_cs 1);
qed "K1_contractD";

goal Comb.thy "!!x z. x ---> y ==> x#z ---> y#z";
by (etac rtrancl_induct 1);
by (rtac rtrancl_refl 1);
by (fast_tac (contract_cs addIs [r_into_rtrancl, rtrancl_trans]) 1);
qed "Ap_reduce1";

goal Comb.thy "!!x z. x ---> y ==> z#x ---> z#y";
by (etac rtrancl_induct 1);
by (rtac rtrancl_refl 1);
by (fast_tac (contract_cs addIs [r_into_rtrancl, rtrancl_trans]) 1);
qed "Ap_reduce2";

(** Counterexample to the diamond property for -1-> **)

goal Comb.thy "K#I#(I#I) -1-> I";
by (rtac contract.K 1);
qed "KIII_contract1";

goalw Comb.thy [I_def] "K#I#(I#I) -1-> K#I#((K#I)#(K#I))";
by (fast_tac contract_cs 1);
qed "KIII_contract2";

goal Comb.thy "K#I#((K#I)#(K#I)) -1-> I";
by (fast_tac contract_cs 1);
qed "KIII_contract3";

goalw Comb.thy [diamond_def] "~ diamond(contract)";
by (fast_tac (HOL_cs addIs [KIII_contract1,KIII_contract2,KIII_contract3]
                     addSEs [I_contract_E]) 1);
qed "not_diamond_contract";



(*** Results about Parallel Contraction ***)

bind_thm ("parcontract_induct",
    (parcontract.mutual_induct RS spec RS spec RSN (2,rev_mp)));

(*Derive a case for each combinator constructor*)
val K_parcontractE = parcontract.mk_cases comb.simps "K =1=> z";
val S_parcontractE = parcontract.mk_cases comb.simps "S =1=> z";
val Ap_parcontractE = parcontract.mk_cases comb.simps "x#y =1=> z";

val parcontract_cs =
    HOL_cs addIs  parcontract.intrs
	   addSEs [K_parcontractE, S_parcontractE, 
		   Ap_parcontractE]
	   addss  (HOL_ss addsimps comb.simps);

(*** Basic properties of parallel contraction ***)

goal Comb.thy "!!x z. K#x =1=> z ==> (EX x'. z = K#x' & x =1=> x')";
by (fast_tac parcontract_cs 1);
qed "K1_parcontractD";

goal Comb.thy "!!x z. S#x =1=> z ==> (EX x'. z = S#x' & x =1=> x')";
by (fast_tac parcontract_cs 1);
qed "S1_parcontractD";

goal Comb.thy
 "!!x y z. S#x#y =1=> z ==> (EX x' y'. z = S#x'#y' & x =1=> x' & y =1=> y')";
by (fast_tac (parcontract_cs addSDs [S1_parcontractD]) 1);
     (*the extra rule makes the proof more than twice as fast*)
qed "S2_parcontractD";

(*Church-Rosser property for parallel contraction*)
goalw Comb.thy [diamond_def] "diamond(parcontract)";
by (rtac (impI RS allI RS allI) 1);
by (etac parcontract_induct 1);
by (ALLGOALS 
    (fast_tac (parcontract_cs addSDs [K1_parcontractD,S2_parcontractD])));
qed "diamond_parcontract";


(*** Equivalence of x--->y and x===>y ***)

goal Comb.thy "contract <= parcontract";
by (rtac subsetI 1);
by (etac contract.induct 1);
by (ALLGOALS (fast_tac (parcontract_cs)));
qed "contract_subset_parcontract";

(*Reductions: simply throw together reflexivity, transitivity and
  the one-step reductions*)
val reduce_cs = contract_cs
                addIs [rtrancl_refl, r_into_rtrancl,
		       contract.K, contract.S, Ap_reduce1, Ap_reduce2,
		       rtrancl_trans];

(*Example only: not used*)
goalw Comb.thy [I_def] "I#x ---> x";
by (best_tac reduce_cs 1);
qed "reduce_I";

goal Comb.thy "parcontract <= contract^*";
by (rtac subsetI 1);
by (etac parcontract.induct 1);
by (ALLGOALS (deepen_tac reduce_cs 0));
qed "parcontract_subset_reduce";

goal Comb.thy "contract^* = parcontract^*";
by (REPEAT 
    (resolve_tac [equalityI, 
		  contract_subset_parcontract RS rtrancl_mono, 
		  parcontract_subset_reduce RS rtrancl_subset_rtrancl] 1));
qed "reduce_eq_parreduce";

goal Comb.thy "diamond(contract^*)";
by (simp_tac (HOL_ss addsimps [reduce_eq_parreduce, diamond_rtrancl, 
			       diamond_parcontract]) 1);

qed "diamond_reduce";


writeln"Reached end of file.";
