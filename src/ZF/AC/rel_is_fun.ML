(*  Title: 	ZF/AC/rel_is_fun.ML
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

Lemmas needed to state when a finite relation is a function.

The criteria are cardinalities of the relation and its domain.
Used in WO6WO1.ML
*)

goalw Cardinal.thy [lepoll_def]
     "!!m. [| m:nat; u lepoll m |] ==> domain(u) lepoll m";
by (eresolve_tac [exE] 1);
by (res_inst_tac [("x",
	"lam x:domain(u). LEAST i. EX y. <x,y> : u & f`<x,y> = i")] exI 1);
by (res_inst_tac [("d","%y. fst(converse(f)`y)")] lam_injective 1);
by (fast_tac (ZF_cs addIs [LeastI2, nat_into_Ord RS Ord_in_Ord,
			inj_is_fun RS apply_type]) 1);
by (eresolve_tac [domainE] 1);
by (forward_tac [inj_is_fun RS apply_type] 1 THEN (atac 1));
by (resolve_tac [LeastI2] 1);
by (REPEAT (fast_tac (ZF_cs addIs [fst_conv, left_inverse RS ssubst]
			addSEs [nat_into_Ord RS Ord_in_Ord]) 1));
val lepoll_m_imp_domain_lepoll_m = result();

goal ZF.thy "!!r. [| <a,c> : r; c~=b |] ==> domain(r-{<a,b>}) = domain(r)";
by (resolve_tac [equalityI] 1);
by (fast_tac (ZF_cs addSIs [domain_mono]) 1);
by (resolve_tac [subsetI] 1);
by (excluded_middle_tac "x = a" 1);
by (REPEAT (fast_tac (ZF_cs addSIs [domainI] addSEs [domainE]) 1));
val domain_diff_eq_domain = result();

goal Cardinal.thy
    "!!r. [| succ(m) lepoll domain(r); r lepoll succ(m); m:nat |] ==> \
\	  ALL a:domain(r). EX! b. <a, b> : r";
by (resolve_tac [ballI] 1);
by (eresolve_tac [domainE] 1);
by (resolve_tac [ex1I] 1 THEN (atac 1));
by (resolve_tac [excluded_middle RS disjE] 1 THEN (atac 2));
by (fast_tac (ZF_cs addSEs [lepoll_trans RS succ_lepoll_natE, 
			diff_sing_lepoll RSN (2, lepoll_m_imp_domain_lepoll_m)]
		addEs [not_sym RSN (2, domain_diff_eq_domain) RS subst]) 1);
val rel_domain_ex1 = result();

goal ZF.thy "!! r. [| ALL a:A. EX! b. <a,b> : r; r<=A*B |]  \
\		==> r = (lam a:A. THE b. <a,b> : r)";
by (resolve_tac [equalityI] 1);
by (resolve_tac [subsetI] 1);
by (dresolve_tac [subsetD] 1 THEN (atac 1));
by (eresolve_tac [SigmaE] 1);
by (hyp_subst_tac 1);
by (dresolve_tac [bspec] 1 THEN (atac 1));
by (eresolve_tac [lamI RS subst_elem] 1);
by (forward_tac [theI] 1);
by (asm_simp_tac ZF_ss 1);
by (fast_tac (ZF_cs addIs [theI] addSEs [bspec] addSEs [lamE]) 2);
by (eresolve_tac [ex1_equalsE] 1 THEN (REPEAT (atac 1)));
val rel_is_lam = result();

goal ZF.thy "!! r. [| ALL a:A. EX! b. <a,b> : r; r<=A*B |]  \
\		==> (lam a:A. THE b. <a,b> : r) : A->B";
by (fast_tac (ZF_cs addSIs [lam_type] addSEs [Pair_inject]
		addSDs [bspec, theI]) 1);
val lam_the_type = result();

goal Cardinal.thy
    "!!r. [| succ(m) lepoll domain(r);  r lepoll succ(m);  m:nat;  \
\	     r<=A*B; A=domain(r) |] ==> r: A->B";
by (hyp_subst_tac 1);
by (resolve_tac [rel_domain_ex1 RS 
		(rel_domain_ex1 RS rel_is_lam RSN (3,
		lam_the_type RS subst_elem))] 1
	THEN (TRYALL atac));
val rel_is_fun = result();
