(*  Title: 	ZF/ex/parcontract.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson
    Copyright   1993  University of Cambridge

Parallel contraction

HOL system proofs may be found in
/usr/groups/theory/hvg-aftp/contrib/rule-induction/cl.ml
*)

structure ParContract = Inductive_Fun
 (val thy = Contract.thy;
  val thy_name = "ParContract";
  val rec_doms = [("parcontract","comb*comb")];
  val sintrs = 
      ["[| p:comb |] ==> p =1=> p",
       "[| p:comb;  q:comb |] ==> K#p#q =1=> p",
       "[| p:comb;  q:comb;  r:comb |] ==> S#p#q#r =1=> (p#r)#(q#r)",
       "[| p=1=>q;  r=1=>s |] ==> p#r =1=> q#s"];
  val monos = [];
  val con_defs = [];
  val type_intrs = Comb.intrs@[SigmaI];
  val type_elims = [SigmaE2]);

val [parcontract_refl,K_parcontract,S_parcontract,Ap_parcontract] = 
    ParContract.intrs;

val parcontract_induct = standard
    (ParContract.mutual_induct RS spec RS spec RSN (2,rev_mp));

(*For type checking: replaces a=1=>b by a,b:comb *)
val parcontract_combE2 = ParContract.dom_subset RS subsetD RS SigmaE2;
val parcontract_combD1 = ParContract.dom_subset RS subsetD RS SigmaD1;
val parcontract_combD2 = ParContract.dom_subset RS subsetD RS SigmaD2;

goal ParContract.thy "field(parcontract) = comb";
by (fast_tac (ZF_cs addIs [equalityI,K_parcontract] 
	            addSEs [parcontract_combE2]) 1);
val field_parcontract_eq = result();

val parcontract_caseE = standard
     (ParContract.unfold RS equalityD1 RS subsetD RS CollectE);

(*Derive a case for each combinator constructor*)
val K_parcontract_case = ParContract.mk_cases Comb.con_defs "K =1=> r";
val S_parcontract_case = ParContract.mk_cases Comb.con_defs "S =1=> r";
val Ap_parcontract_case = ParContract.mk_cases Comb.con_defs "p#q =1=> r";

val parcontract_cs =
    ZF_cs addSIs Comb.intrs
	  addIs  ParContract.intrs
	  addSEs [Ap_E, K_parcontract_case, S_parcontract_case, 
		  Ap_parcontract_case]
	  addSEs [parcontract_combD1, parcontract_combD2]     (*type checking*)
          addSEs Comb.free_SEs;

(*** Basic properties of parallel contraction ***)

goal ParContract.thy "!!p r. K#p =1=> r ==> (EX p'. r = K#p' & p =1=> p')";
by (fast_tac parcontract_cs 1);
val K1_parcontractD = result();

goal ParContract.thy "!!p r. S#p =1=> r ==> (EX p'. r = S#p' & p =1=> p')";
by (fast_tac parcontract_cs 1);
val S1_parcontractD = result();

goal ParContract.thy
 "!!p q r. S#p#q =1=> r ==> (EX p' q'. r = S#p'#q' & p =1=> p' & q =1=> q')";
by (fast_tac (parcontract_cs addSDs [S1_parcontractD]) 1);
val S2_parcontractD = result();

(*Church-Rosser property for parallel contraction*)
goalw ParContract.thy [diamond_def] "diamond(parcontract)";
by (rtac (impI RS allI RS allI) 1);
by (etac parcontract_induct 1);
by (ALLGOALS 
    (fast_tac (parcontract_cs addSDs [K1_parcontractD,S2_parcontractD])));
val diamond_parcontract = result();

(*** Transitive closure preserves the Church-Rosser property ***)

goalw ParContract.thy [diamond_def]
    "!!x y r. [| diamond(r);  <x,y>:r^+ |] ==> \
\    ALL y'. <x,y'>:r --> (EX z. <y',z>: r^+ & <y,z>: r)";
by (etac trancl_induct 1);
by (fast_tac (ZF_cs addIs [r_into_trancl]) 1);
by (slow_best_tac (ZF_cs addSDs [spec RS mp]
		         addIs  [r_into_trancl, trans_trancl RS transD]) 1);
val diamond_trancl_lemma = result();

val diamond_lemmaE = diamond_trancl_lemma RS spec RS mp RS exE;

val [major] = goal ParContract.thy "diamond(r) ==> diamond(r^+)";
bw diamond_def;  (*unfold only in goal, not in premise!*)
by (rtac (impI RS allI RS allI) 1);
by (etac trancl_induct 1);
by (ALLGOALS
    (slow_best_tac (ZF_cs addIs [r_into_trancl, trans_trancl RS transD]
		          addEs [major RS diamond_lemmaE])));
val diamond_trancl = result();


(*** Equivalence of p--->q and p===>q ***)

goal ParContract.thy "!!p q. p-1->q ==> p=1=>q";
by (etac contract_induct 1);
by (ALLGOALS (fast_tac (parcontract_cs)));
val contract_imp_parcontract = result();

goal ParContract.thy "!!p q. p--->q ==> p===>q";
by (forward_tac [rtrancl_type RS subsetD RS SigmaD1] 1);
by (dtac (field_contract_eq RS equalityD1 RS subsetD) 1);
by (etac rtrancl_induct 1);
by (fast_tac (parcontract_cs addIs [r_into_trancl]) 1);
by (fast_tac (ZF_cs addIs [contract_imp_parcontract, 
			   r_into_trancl, trans_trancl RS transD]) 1);
val reduce_imp_parreduce = result();


goal ParContract.thy "!!p q. p=1=>q ==> p--->q";
by (etac parcontract_induct 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
by (fast_tac (contract_cs addIs reduction_rls) 1);
by (rtac (trans_rtrancl RS transD) 1);
by (ALLGOALS 
    (fast_tac 
     (contract_cs addIs [Ap_reduce1, Ap_reduce2]
                  addSEs [parcontract_combD1,parcontract_combD2])));
val parcontract_imp_reduce = result();

goal ParContract.thy "!!p q. p===>q ==> p--->q";
by (forward_tac [trancl_type RS subsetD RS SigmaD1] 1);
by (dtac (field_parcontract_eq RS equalityD1 RS subsetD) 1);
by (etac trancl_induct 1);
by (etac parcontract_imp_reduce 1);
by (etac (trans_rtrancl RS transD) 1);
by (etac parcontract_imp_reduce 1);
val parreduce_imp_reduce = result();

goal ParContract.thy "p===>q <-> p--->q";
by (REPEAT (ares_tac [iffI, parreduce_imp_reduce, reduce_imp_parreduce] 1));
val parreduce_iff_reduce = result();

writeln"Reached end of file.";
