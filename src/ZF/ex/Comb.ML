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

open Comb;

val [_,_,comb_Ap] = comb.intrs;
val Ap_E = comb.mk_cases comb.con_defs "p#q : comb";


(*** Results about Contraction ***)

bind_thm ("contract_induct",
    (contract.mutual_induct RS spec RS spec RSN (2,rev_mp)));

(*For type checking: replaces a-1->b by a,b:comb *)
val contract_combE2 = contract.dom_subset RS subsetD RS SigmaE2;
val contract_combD1 = contract.dom_subset RS subsetD RS SigmaD1;
val contract_combD2 = contract.dom_subset RS subsetD RS SigmaD2;

goal Comb.thy "field(contract) = comb";
by (fast_tac (ZF_cs addIs [equalityI,contract.K] addSEs [contract_combE2]) 1);
qed "field_contract_eq";

bind_thm ("reduction_refl",
    (field_contract_eq RS equalityD2 RS subsetD RS rtrancl_refl));

bind_thm ("rtrancl_into_rtrancl2",
    (r_into_rtrancl RS (trans_rtrancl RS transD)));

val reduction_rls = [reduction_refl, contract.K, contract.S, 
                     contract.K RS rtrancl_into_rtrancl2,
                     contract.S RS rtrancl_into_rtrancl2,
                     contract.Ap1 RS rtrancl_into_rtrancl2,
                     contract.Ap2 RS rtrancl_into_rtrancl2];

(*Example only: not used*)
goalw Comb.thy [I_def] "!!p. p:comb ==> I#p ---> p";
by (REPEAT (ares_tac (comb.intrs @ reduction_rls) 1));
qed "reduce_I";

goalw Comb.thy [I_def] "I: comb";
by (REPEAT (ares_tac comb.intrs 1));
qed "comb_I";

(** Non-contraction results **)

(*Derive a case for each combinator constructor*)
val K_contractE = contract.mk_cases comb.con_defs "K -1-> r";
val S_contractE = contract.mk_cases comb.con_defs "S -1-> r";
val Ap_contractE = contract.mk_cases comb.con_defs "p#q -1-> r";

val contract_cs =
    ZF_cs addSIs comb.intrs
          addIs  contract.intrs
          addSEs [contract_combD1,contract_combD2]     (*type checking*)
          addSEs [K_contractE, S_contractE, Ap_contractE]
          addSEs comb.free_SEs;

goalw Comb.thy [I_def] "!!r. I -1-> r ==> P";
by (fast_tac contract_cs 1);
qed "I_contract_E";

goal Comb.thy "!!p r. K#p -1-> r ==> (EX q. r = K#q & p -1-> q)";
by (fast_tac contract_cs 1);
qed "K1_contractD";

goal Comb.thy "!!p r. [| p ---> q;  r: comb |] ==> p#r ---> q#r";
by (forward_tac [rtrancl_type RS subsetD RS SigmaD1] 1);
by (dtac (field_contract_eq RS equalityD1 RS subsetD) 1);
by (etac rtrancl_induct 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
by (etac (trans_rtrancl RS transD) 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
qed "Ap_reduce1";

goal Comb.thy "!!p r. [| p ---> q;  r: comb |] ==> r#p ---> r#q";
by (forward_tac [rtrancl_type RS subsetD RS SigmaD1] 1);
by (dtac (field_contract_eq RS equalityD1 RS subsetD) 1);
by (etac rtrancl_induct 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
by (etac (trans_rtrancl RS transD) 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
qed "Ap_reduce2";

(** Counterexample to the diamond property for -1-> **)

goal Comb.thy "K#I#(I#I) -1-> I";
by (REPEAT (ares_tac [contract.K, comb_I, comb_Ap] 1));
qed "KIII_contract1";

goalw Comb.thy [I_def] "K#I#(I#I) -1-> K#I#((K#I)#(K#I))";
by (DEPTH_SOLVE (resolve_tac (comb.intrs @ contract.intrs) 1));
qed "KIII_contract2";

goal Comb.thy "K#I#((K#I)#(K#I)) -1-> I";
by (REPEAT (ares_tac (comb.intrs @ [contract.K, comb_I]) 1));
qed "KIII_contract3";

goalw Comb.thy [diamond_def] "~ diamond(contract)";
by (fast_tac (ZF_cs addIs [KIII_contract1,KIII_contract2,KIII_contract3]
                    addSEs [I_contract_E]) 1);
qed "not_diamond_contract";



(*** Results about Parallel Contraction ***)

bind_thm ("parcontract_induct",
    (parcontract.mutual_induct RS spec RS spec RSN (2,rev_mp)));

(*For type checking: replaces a=1=>b by a,b:comb *)
val parcontract_combE2 = parcontract.dom_subset RS subsetD RS SigmaE2;
val parcontract_combD1 = parcontract.dom_subset RS subsetD RS SigmaD1;
val parcontract_combD2 = parcontract.dom_subset RS subsetD RS SigmaD2;

goal Comb.thy "field(parcontract) = comb";
by (fast_tac (ZF_cs addIs [equalityI, parcontract.K] 
                    addSEs [parcontract_combE2]) 1);
qed "field_parcontract_eq";

(*Derive a case for each combinator constructor*)
val K_parcontractE = parcontract.mk_cases comb.con_defs "K =1=> r";
val S_parcontractE = parcontract.mk_cases comb.con_defs "S =1=> r";
val Ap_parcontractE = parcontract.mk_cases comb.con_defs "p#q =1=> r";

val parcontract_cs =
    ZF_cs addSIs comb.intrs
          addIs  parcontract.intrs
          addSEs [Ap_E, K_parcontractE, S_parcontractE, 
                  Ap_parcontractE]
          addSEs [parcontract_combD1, parcontract_combD2]     (*type checking*)
          addSEs comb.free_SEs;

(*** Basic properties of parallel contraction ***)

goal Comb.thy "!!p r. K#p =1=> r ==> (EX p'. r = K#p' & p =1=> p')";
by (fast_tac parcontract_cs 1);
qed "K1_parcontractD";

goal Comb.thy "!!p r. S#p =1=> r ==> (EX p'. r = S#p' & p =1=> p')";
by (fast_tac parcontract_cs 1);
qed "S1_parcontractD";

goal Comb.thy
 "!!p q r. S#p#q =1=> r ==> (EX p' q'. r = S#p'#q' & p =1=> p' & q =1=> q')";
by (fast_tac (parcontract_cs addSDs [S1_parcontractD]) 1);
qed "S2_parcontractD";

(*Church-Rosser property for parallel contraction*)
goalw Comb.thy [diamond_def] "diamond(parcontract)";
by (rtac (impI RS allI RS allI) 1);
by (etac parcontract_induct 1);
by (ALLGOALS 
    (fast_tac (parcontract_cs addSDs [K1_parcontractD,S2_parcontractD])));
qed "diamond_parcontract";

(*** Transitive closure preserves the Church-Rosser property ***)

goalw Comb.thy [diamond_def]
    "!!x y r. [| diamond(r);  <x,y>:r^+ |] ==> \
\    ALL y'. <x,y'>:r --> (EX z. <y',z>: r^+ & <y,z>: r)";
by (etac trancl_induct 1);
by (fast_tac (ZF_cs addIs [r_into_trancl]) 1);
by (slow_best_tac (ZF_cs addSDs [spec RS mp]
                         addIs  [r_into_trancl, trans_trancl RS transD]) 1);
qed "diamond_trancl_lemma";

val diamond_lemmaE = diamond_trancl_lemma RS spec RS mp RS exE;

val [major] = goal Comb.thy "diamond(r) ==> diamond(r^+)";
by (rewtac diamond_def);  (*unfold only in goal, not in premise!*)
by (rtac (impI RS allI RS allI) 1);
by (etac trancl_induct 1);
by (ALLGOALS
    (slow_best_tac (ZF_cs addIs [r_into_trancl, trans_trancl RS transD]
                          addEs [major RS diamond_lemmaE])));
qed "diamond_trancl";


(*** Equivalence of p--->q and p===>q ***)

goal Comb.thy "!!p q. p-1->q ==> p=1=>q";
by (etac contract_induct 1);
by (ALLGOALS (fast_tac (parcontract_cs)));
qed "contract_imp_parcontract";

goal Comb.thy "!!p q. p--->q ==> p===>q";
by (forward_tac [rtrancl_type RS subsetD RS SigmaD1] 1);
by (dtac (field_contract_eq RS equalityD1 RS subsetD) 1);
by (etac rtrancl_induct 1);
by (fast_tac (parcontract_cs addIs [r_into_trancl]) 1);
by (fast_tac (ZF_cs addIs [contract_imp_parcontract, 
                           r_into_trancl, trans_trancl RS transD]) 1);
qed "reduce_imp_parreduce";


goal Comb.thy "!!p q. p=1=>q ==> p--->q";
by (etac parcontract_induct 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
by (rtac (trans_rtrancl RS transD) 1);
by (ALLGOALS 
    (fast_tac 
     (contract_cs addIs [Ap_reduce1, Ap_reduce2]
                  addSEs [parcontract_combD1,parcontract_combD2])));
qed "parcontract_imp_reduce";

goal Comb.thy "!!p q. p===>q ==> p--->q";
by (forward_tac [trancl_type RS subsetD RS SigmaD1] 1);
by (dtac (field_parcontract_eq RS equalityD1 RS subsetD) 1);
by (etac trancl_induct 1);
by (etac parcontract_imp_reduce 1);
by (etac (trans_rtrancl RS transD) 1);
by (etac parcontract_imp_reduce 1);
qed "parreduce_imp_reduce";

goal Comb.thy "p===>q <-> p--->q";
by (REPEAT (ares_tac [iffI, parreduce_imp_reduce, reduce_imp_parreduce] 1));
qed "parreduce_iff_reduce";

writeln"Reached end of file.";
