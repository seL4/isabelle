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

(*** Reflexive/Transitive closure preserves the Church-Rosser property 
     So does the Transitive closure; use r_into_trancl instead of rtrancl_refl
***)

val [_, spec_mp] = [spec] RL [mp];

(*Strip lemma.  The induction hyp is all but the last diamond of the strip.*)
Goalw [diamond_def]
    "[| diamond(r);  (x,y):r^* |] ==> \ 
\         ALL y'. (x,y'):r --> (EX z. (y',z): r^* & (y,z): r)";
by (etac rtrancl_induct 1);
by (Blast_tac 1);
by (slow_best_tac (set_cs addIs [r_into_rtrancl RSN (2, rtrancl_trans)]
                          addSDs [spec_mp]) 1);
qed_spec_mp "diamond_strip_lemmaE";

Goal "diamond(r) ==> diamond(r^*)";
by (stac diamond_def 1);  (*unfold only in goal, not in premise!*)
by (rtac (impI RS allI RS allI) 1);
by (etac rtrancl_induct 1);
by (Blast_tac 1);
by (best_tac  (*Seems to be a brittle, undirected search*)
    (set_cs addIs [r_into_rtrancl RSN (2, rtrancl_trans)]
            addEs [diamond_strip_lemmaE RS exE]) 1);
qed "diamond_rtrancl";


(*** Results about Contraction ***)

(*Derive a case for each combinator constructor*)
val K_contractE  = contract.mk_cases "K -1-> z";
val S_contractE  = contract.mk_cases "S -1-> z";
val Ap_contractE = contract.mk_cases "x#y -1-> z";

AddSIs [contract.K, contract.S];
AddIs  [contract.Ap1, contract.Ap2];
AddSEs [K_contractE, S_contractE, Ap_contractE];

Goalw [I_def] "I -1-> z ==> P";
by (Blast_tac 1);
qed "I_contract_E";
AddSEs [I_contract_E];

Goal "K#x -1-> z ==> (EX x'. z = K#x' & x -1-> x')";
by (Blast_tac 1);
qed "K1_contractD";
AddSEs [K1_contractD];

Goal "x ---> y ==> x#z ---> y#z";
by (etac rtrancl_induct 1);
by (ALLGOALS (blast_tac (claset() addIs [rtrancl_trans])));
qed "Ap_reduce1";

Goal "x ---> y ==> z#x ---> z#y";
by (etac rtrancl_induct 1);
by (ALLGOALS (blast_tac (claset() addIs [rtrancl_trans])));
qed "Ap_reduce2";

(** Counterexample to the diamond property for -1-> **)

Goal "K#I#(I#I) -1-> I";
by (rtac contract.K 1);
qed "KIII_contract1";

Goalw [I_def] "K#I#(I#I) -1-> K#I#((K#I)#(K#I))";
by (Blast_tac 1);
qed "KIII_contract2";

Goal "K#I#((K#I)#(K#I)) -1-> I";
by (Blast_tac 1);
qed "KIII_contract3";

Goalw [diamond_def] "~ diamond(contract)";
by (blast_tac (claset() addIs [KIII_contract1,KIII_contract2,KIII_contract3]) 1);
qed "not_diamond_contract";



(*** Results about Parallel Contraction ***)

(*Derive a case for each combinator constructor*)
val K_parcontractE  = parcontract.mk_cases "K =1=> z";
val S_parcontractE  = parcontract.mk_cases "S =1=> z";
val Ap_parcontractE = parcontract.mk_cases "x#y =1=> z";

AddSIs [parcontract.refl, parcontract.K, parcontract.S];
AddIs  [parcontract.Ap];
AddSEs [K_parcontractE, S_parcontractE,Ap_parcontractE];

(*** Basic properties of parallel contraction ***)

Goal "K#x =1=> z ==> (EX x'. z = K#x' & x =1=> x')";
by (Blast_tac 1);
qed "K1_parcontractD";
AddSDs [K1_parcontractD];

Goal "S#x =1=> z ==> (EX x'. z = S#x' & x =1=> x')";
by (Blast_tac 1);
qed "S1_parcontractD";
AddSDs [S1_parcontractD];

Goal "S#x#y =1=> z ==> (EX x' y'. z = S#x'#y' & x =1=> x' & y =1=> y')";
by (Blast_tac 1);
qed "S2_parcontractD";
AddSDs [S2_parcontractD];

(*The rules above are not essential but make proofs much faster*)


(*Church-Rosser property for parallel contraction*)
Goalw [diamond_def] "diamond parcontract";
by (rtac (impI RS allI RS allI) 1);
by (etac parcontract.induct 1 THEN prune_params_tac);
by Safe_tac;
by (ALLGOALS Blast_tac);
qed "diamond_parcontract";


(*** Equivalence of x--->y and x===>y ***)

Goal "contract <= parcontract";
by (rtac subsetI 1);
by (split_all_tac 1);
by (etac contract.induct 1);
by (ALLGOALS Blast_tac);
qed "contract_subset_parcontract";

(*Reductions: simply throw together reflexivity, transitivity and
  the one-step reductions*)

AddIs [Ap_reduce1, Ap_reduce2, r_into_rtrancl, rtrancl_trans];

(*Example only: not used*)
Goalw [I_def] "I#x ---> x";
by (Blast_tac 1);
qed "reduce_I";

Goal "parcontract <= contract^*";
by (rtac subsetI 1);
by (split_all_tac 1);
by (etac parcontract.induct 1 THEN prune_params_tac);
by (ALLGOALS Blast_tac);
qed "parcontract_subset_reduce";

Goal "contract^* = parcontract^*";
by (REPEAT 
    (resolve_tac [equalityI, 
                  contract_subset_parcontract RS rtrancl_mono, 
                  parcontract_subset_reduce RS rtrancl_subset_rtrancl] 1));
qed "reduce_eq_parreduce";

Goal "diamond(contract^*)";
by (simp_tac (simpset() addsimps [reduce_eq_parreduce, diamond_rtrancl, 
                                 diamond_parcontract]) 1);
qed "diamond_reduce";


writeln"Reached end of file.";
