(*  Title:      ZF/ex/comb.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1993  University of Cambridge

Combinatory Logic example: the Church-Rosser Theorem
Curiously, combinators do not include free variables.

Example taken from
    J. Camilleri and T. F. Melham.
    Reasoning with Inductively Defined Relations in the HOL Theorem Prover.
    Report 265, University of Cambridge Computer Laboratory, 1992.

HOL system proofs may be found in
/usr/groups/theory/hvg-aftp/contrib/rule-induction/cl.ml
*)

(*** Transitive closure preserves the Church-Rosser property ***)

Goalw [diamond_def]
    "!!x y r. [| diamond(r);  <x,y>:r^+ |] ==> \
\    \\<forall>y'. <x,y'>:r --> (\\<exists>z. <y',z>: r^+ & <y,z>: r)";
by (etac trancl_induct 1);
by (blast_tac (claset() addIs [r_into_trancl]) 1);
by (slow_best_tac (claset() addSDs [spec RS mp]
                           addIs  [r_into_trancl, trans_trancl RS transD]) 1);
val diamond_strip_lemmaE = result() RS spec RS mp RS exE;

val [major] = goal Comb.thy "diamond(r) ==> diamond(r^+)";
by (rewtac diamond_def);  (*unfold only in goal, not in premise!*)
by (rtac (impI RS allI RS allI) 1);
by (etac trancl_induct 1);
by (ALLGOALS (*Seems to be a brittle, undirected search*)
    (slow_best_tac (claset() addIs [r_into_trancl, trans_trancl RS transD]
                            addEs [major RS diamond_strip_lemmaE])));
qed "diamond_trancl";


val [_,_,comb_Ap] = comb.intrs;
val Ap_E = comb.mk_cases "p#q \\<in> comb";

AddSIs comb.intrs;


(*** Results about Contraction ***)

(*For type checking: replaces a-1->b by a,b \\<in> comb *)
val contract_combE2 = contract.dom_subset RS subsetD RS SigmaE2;
val contract_combD1 = contract.dom_subset RS subsetD RS SigmaD1;
val contract_combD2 = contract.dom_subset RS subsetD RS SigmaD2;

Goal "field(contract) = comb";
by (blast_tac (claset() addIs [contract.K] addSEs [contract_combE2]) 1);
qed "field_contract_eq";

bind_thm ("reduction_refl",
    (field_contract_eq RS equalityD2 RS subsetD RS rtrancl_refl));

bind_thm ("rtrancl_into_rtrancl2",
    (r_into_rtrancl RS (trans_rtrancl RS transD)));

AddSIs [reduction_refl, contract.K, contract.S];

val reduction_rls = [contract.K RS rtrancl_into_rtrancl2,
                     contract.S RS rtrancl_into_rtrancl2,
                     contract.Ap1 RS rtrancl_into_rtrancl2,
                     contract.Ap2 RS rtrancl_into_rtrancl2];

(*Example only: not used*)
Goalw [I_def] "p \\<in> comb ==> I#p ---> p";
by (blast_tac (claset() addIs reduction_rls) 1);
qed "reduce_I";

Goalw [I_def] "I \\<in> comb";
by (Blast_tac 1);
qed "comb_I";

(** Non-contraction results **)

(*Derive a case for each combinator constructor*)
val K_contractE = contract.mk_cases "K -1-> r";
val S_contractE = contract.mk_cases "S -1-> r";
val Ap_contractE = contract.mk_cases "p#q -1-> r";

AddIs  [contract.Ap1, contract.Ap2];
AddSEs [K_contractE, S_contractE, Ap_contractE];

Goalw [I_def] "I -1-> r ==> P";
by Auto_tac;
qed "I_contract_E";

Goal "K#p -1-> r ==> (\\<exists>q. r = K#q & p -1-> q)";
by Auto_tac;
qed "K1_contractD";

Goal "[| p ---> q;  r \\<in> comb |] ==> p#r ---> q#r";
by (forward_tac [rtrancl_type RS subsetD RS SigmaD1] 1);
by (dtac (field_contract_eq RS equalityD1 RS subsetD) 1);
by (etac rtrancl_induct 1);
by (blast_tac (claset() addIs reduction_rls) 1);
by (etac (trans_rtrancl RS transD) 1);
by (blast_tac (claset() addIs (contract_combD2::reduction_rls)) 1);
qed "Ap_reduce1";

Goal "[| p ---> q;  r \\<in> comb |] ==> r#p ---> r#q";
by (forward_tac [rtrancl_type RS subsetD RS SigmaD1] 1);
by (dtac (field_contract_eq RS equalityD1 RS subsetD) 1);
by (etac rtrancl_induct 1);
by (blast_tac (claset() addIs reduction_rls) 1);
by (etac (trans_rtrancl RS transD) 1);
by (blast_tac (claset() addIs (contract_combD2::reduction_rls)) 1);
qed "Ap_reduce2";

(** Counterexample to the diamond property for -1-> **)

Goal "K#I#(I#I) -1-> I";
by (REPEAT (ares_tac [contract.K, comb_I, comb_Ap] 1));
qed "KIII_contract1";

Goalw [I_def] "K#I#(I#I) -1-> K#I#((K#I)#(K#I))";
by (DEPTH_SOLVE (resolve_tac (comb.intrs @ contract.intrs) 1));
qed "KIII_contract2";

Goal "K#I#((K#I)#(K#I)) -1-> I";
by (REPEAT (ares_tac (comb.intrs @ [contract.K, comb_I]) 1));
qed "KIII_contract3";

Goalw [diamond_def] "~ diamond(contract)";
by (blast_tac (claset() addIs [KIII_contract1,KIII_contract2,KIII_contract3]
                       addSEs [I_contract_E]) 1);
qed "not_diamond_contract";



(*** Results about Parallel Contraction ***)

(*For type checking: replaces a=1=>b by a,b \\<in> comb *)
val parcontract_combE2 = parcontract.dom_subset RS subsetD RS SigmaE2;
val parcontract_combD1 = parcontract.dom_subset RS subsetD RS SigmaD1;
val parcontract_combD2 = parcontract.dom_subset RS subsetD RS SigmaD2;

Goal "field(parcontract) = comb";
by (blast_tac (claset() addIs [parcontract.K] 
                      addSEs [parcontract_combE2]) 1);
qed "field_parcontract_eq";

(*Derive a case for each combinator constructor*)
val K_parcontractE = parcontract.mk_cases "K =1=> r";
val S_parcontractE = parcontract.mk_cases "S =1=> r";
val Ap_parcontractE = parcontract.mk_cases "p#q =1=> r";

AddIs  parcontract.intrs;
AddSEs [Ap_E, K_parcontractE, S_parcontractE, Ap_parcontractE];

(*** Basic properties of parallel contraction ***)

Goal "K#p =1=> r ==> (\\<exists>p'. r = K#p' & p =1=> p')";
by Auto_tac;
qed "K1_parcontractD";
AddSDs [K1_parcontractD];

Goal "S#p =1=> r ==> (\\<exists>p'. r = S#p' & p =1=> p')";
by Auto_tac;
qed "S1_parcontractD";
AddSDs [S1_parcontractD];

Goal "S#p#q =1=> r ==> (\\<exists>p' q'. r = S#p'#q' & p =1=> p' & q =1=> q')";
by Auto_tac;
qed "S2_parcontractD";
AddSDs [S2_parcontractD];

(*Church-Rosser property for parallel contraction*)
Goalw [diamond_def] "diamond(parcontract)";
by (rtac (impI RS allI RS allI) 1);
by (etac parcontract.induct 1);
by (ALLGOALS 
    (blast_tac (claset() addSEs comb.free_SEs
			 addIs [parcontract_combD2])));
qed "diamond_parcontract";

(*** Equivalence of p--->q and p===>q ***)

Goal "p-1->q ==> p=1=>q";
by (etac contract.induct 1);
by Auto_tac;
qed "contract_imp_parcontract";

Goal "p--->q ==> p===>q";
by (forward_tac [rtrancl_type RS subsetD RS SigmaD1] 1);
by (dtac (field_contract_eq RS equalityD1 RS subsetD) 1);
by (etac rtrancl_induct 1);
by (blast_tac (claset() addIs [r_into_trancl]) 1);
by (blast_tac (claset() addIs [contract_imp_parcontract, 
			       r_into_trancl, trans_trancl RS transD]) 1);
qed "reduce_imp_parreduce";


Goal "p=1=>q ==> p--->q";
by (etac parcontract.induct 1);
by (blast_tac (claset() addIs reduction_rls) 1);
by (blast_tac (claset() addIs reduction_rls) 1);
by (blast_tac (claset() addIs reduction_rls) 1);
by (blast_tac 
    (claset() addIs [trans_rtrancl RS transD,
		     Ap_reduce1, Ap_reduce2, parcontract_combD1,
		     parcontract_combD2]) 1);
qed "parcontract_imp_reduce";

Goal "p===>q ==> p--->q";
by (forward_tac [trancl_type RS subsetD RS SigmaD1] 1);
by (dtac (field_parcontract_eq RS equalityD1 RS subsetD) 1);
by (etac trancl_induct 1);
by (etac parcontract_imp_reduce 1);
by (etac (trans_rtrancl RS transD) 1);
by (etac parcontract_imp_reduce 1);
qed "parreduce_imp_reduce";

Goal "p===>q <-> p--->q";
by (blast_tac (claset() addIs [parreduce_imp_reduce, reduce_imp_parreduce]) 1);
qed "parreduce_iff_reduce";

writeln"Reached end of file.";
