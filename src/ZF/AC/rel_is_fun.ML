(*  Title: 	ZF/AC/rel_is_fun.ML
    ID:         $Id$
    Author: 	Krzysztof Grabczewski

Lemmas needed to state when a finite relation is a function.

The criteria are cardinalities of the relation and its domain.
Used in WO6WO1.ML
*)

(*Using AC we could trivially prove, for all u, domain(u) lepoll u*)
goalw Cardinal.thy [lepoll_def]
     "!!m. [| m:nat; u lepoll m |] ==> domain(u) lepoll m";
by (etac exE 1);
by (res_inst_tac [("x",
	"lam x:domain(u). LEAST i. EX y. <x,y> : u & f`<x,y> = i")] exI 1);
by (res_inst_tac [("d","%y. fst(converse(f)`y)")] lam_injective 1);
by (fast_tac (ZF_cs addIs [LeastI2, nat_into_Ord RS Ord_in_Ord,
			inj_is_fun RS apply_type]) 1);
by (etac domainE 1);
by (forward_tac [inj_is_fun RS apply_type] 1 THEN (atac 1));
by (rtac LeastI2 1);
by (REPEAT (fast_tac (ZF_cs addIs [fst_conv, left_inverse RS ssubst]
			addSEs [nat_into_Ord RS Ord_in_Ord]) 1));
val lepoll_m_imp_domain_lepoll_m = result();

goal ZF.thy "!!r. [| <a,c> : r; c~=b |] ==> domain(r-{<a,b>}) = domain(r)";
by (rtac equalityI 1);
by (fast_tac (ZF_cs addSIs [domain_mono]) 1);
by (rtac subsetI 1);
by (excluded_middle_tac "x = a" 1);
by (REPEAT (fast_tac (ZF_cs addSIs [domainI] addSEs [domainE]) 1));
val domain_Diff_eq_domain = result();

goalw Cardinal.thy [function_def]
    "!!r. [| succ(m) lepoll domain(r); r lepoll succ(m); m:nat |] ==> \
\	  function(r)";
by (safe_tac ZF_cs);
by (resolve_tac [excluded_middle RS disjE] 1 THEN (atac 2));
by (fast_tac (ZF_cs addSEs [lepoll_trans RS succ_lepoll_natE, 
			Diff_sing_lepoll RSN (2, lepoll_m_imp_domain_lepoll_m)]
		addEs [not_sym RSN (2, domain_Diff_eq_domain) RS subst]) 1);
val rel_domain_ex1 = result();

goal Cardinal.thy
    "!!r. [| succ(m) lepoll domain(r);  r lepoll succ(m);  m:nat;  \
\	     r<=A*B; A=domain(r) |] ==> r: A->B";
by (hyp_subst_tac 1);
by (asm_simp_tac (ZF_ss addsimps [Pi_iff, rel_domain_ex1]) 1);
val rel_is_fun = result();
