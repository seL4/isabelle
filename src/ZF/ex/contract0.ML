(*  Title: 	ZF/ex/contract.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson
    Copyright   1993  University of Cambridge

For ex/contract.thy.
*)

open Contract0;

structure Contract = Inductive_Fun
 (val thy = Contract0.thy;
  val rec_doms = [("contract","comb*comb")];
  val sintrs = 
      ["[| p:comb;  q:comb |] ==> K#p#q -1-> p",
       "[| p:comb;  q:comb;  r:comb |] ==> S#p#q#r -1-> (p#r)#(q#r)",
       "[| p-1->q;  r:comb |] ==> p#r -1-> q#r",
       "[| p-1->q;  r:comb |] ==> r#p -1-> r#q"];
  val monos = [];
  val con_defs = [];
  val type_intrs = Comb.intrs@[SigmaI];
  val type_elims = [SigmaE2]);

val [K_contract,S_contract,Ap_contract1,Ap_contract2] = Contract.intrs;

val contract_induct = standard
    (Contract.mutual_induct RS spec RS spec RSN (2,rev_mp));

(*For type checking: replaces a-1->b by a,b:comb *)
val contract_combE2 = Contract.dom_subset RS subsetD RS SigmaE2;
val contract_combD1 = Contract.dom_subset RS subsetD RS SigmaD1;
val contract_combD2 = Contract.dom_subset RS subsetD RS SigmaD2;

goal Contract.thy "field(contract) = comb";
by (fast_tac (ZF_cs addIs [equalityI,K_contract] addSEs [contract_combE2]) 1);
val field_contract_eq = result();

val reduction_refl = standard
    (field_contract_eq RS equalityD2 RS subsetD RS rtrancl_refl);

val rtrancl_into_rtrancl2 = standard
    (r_into_rtrancl RS (trans_rtrancl RS transD));

val reduction_rls = [reduction_refl, K_contract, S_contract, 
		     K_contract RS rtrancl_into_rtrancl2,
		     S_contract RS rtrancl_into_rtrancl2,
		     Ap_contract1 RS rtrancl_into_rtrancl2,
		     Ap_contract2 RS rtrancl_into_rtrancl2];

goalw Contract.thy [I_def] "!!p. p:comb ==> I#p ---> p";
by (REPEAT (ares_tac (Comb.intrs @ reduction_rls) 1));
val I_reduce = result();

goalw Contract.thy [I_def] "I: comb";
by (REPEAT (ares_tac Comb.intrs 1));
val I_comb = result();

(** Non-contraction results **)

(*Derive a case for each combinator constructor*)
val K_contract_case = Contract.mk_cases Comb.con_defs "K -1-> r";
val S_contract_case = Contract.mk_cases Comb.con_defs "S -1-> r";
val Ap_contract_case = Contract.mk_cases Comb.con_defs "p#q -1-> r";

val contract_cs =
    ZF_cs addSIs Comb.intrs
	  addIs  Contract.intrs
	  addSEs [contract_combD1,contract_combD2]     (*type checking*)
	  addSEs [K_contract_case, S_contract_case, Ap_contract_case]
	  addSEs Comb.free_SEs;

goalw Contract.thy [I_def] "!!r. I -1-> r ==> P";
by (fast_tac contract_cs 1);
val I_contract_case = result();

goal Contract.thy "!!p r. K#p -1-> r ==> (EX q. r = K#q & p -1-> q)";
by (fast_tac contract_cs 1);
val K1_contractD = result();

goal Contract.thy "!!p r. [| p ---> q;  r: comb |] ==> p#r ---> q#r";
by (forward_tac [rtrancl_type RS subsetD RS SigmaD1] 1);
by (dtac (field_contract_eq RS equalityD1 RS subsetD) 1);
by (etac rtrancl_induct 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
by (etac (trans_rtrancl RS transD) 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
val Ap_reduce1 = result();

goal Contract.thy "!!p r. [| p ---> q;  r: comb |] ==> r#p ---> r#q";
by (forward_tac [rtrancl_type RS subsetD RS SigmaD1] 1);
by (dtac (field_contract_eq RS equalityD1 RS subsetD) 1);
by (etac rtrancl_induct 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
by (etac (trans_rtrancl RS transD) 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
val Ap_reduce2 = result();

(** Counterexample to the diamond property for -1-> **)

goal Contract.thy "K#I#(I#I) -1-> I";
by (REPEAT (ares_tac [K_contract, I_comb, Ap_comb] 1));
val KIII_contract1 = result();

goalw Contract.thy [I_def] "K#I#(I#I) -1-> K#I#((K#I)#(K#I))";
by (DEPTH_SOLVE (resolve_tac (Comb.intrs @ Contract.intrs) 1));
val KIII_contract2 = result();

goal Contract.thy "K#I#((K#I)#(K#I)) -1-> I";
by (REPEAT (ares_tac (Comb.intrs @ [K_contract, I_comb]) 1));
val KIII_contract3 = result();

goalw Contract.thy [diamond_def] "~ diamond(contract)";
by (fast_tac (ZF_cs addIs [KIII_contract1,KIII_contract2,KIII_contract3]
                    addSEs [I_contract_case]) 1);
val not_diamond_contract = result();

writeln"Reached end of file.";
