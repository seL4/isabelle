(*  Title:      ZF/AC/DC_lemmas.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

More general lemmas used in the proofs concerning DC

*)

val [prem] = goalw thy [lepoll_def]
        "Ord(a) ==> {P(b). b:a} lepoll a";
by (res_inst_tac [("x","lam z:RepFun(a,P). LEAST i. z=P(i)")] exI 1);
by (res_inst_tac [("d","%z. P(z)")] (sym RSN (2, lam_injective)) 1);
by (fast_tac (claset() addSIs [Least_in_Ord, prem]) 1);
by (REPEAT (eresolve_tac [RepFunE, LeastI, prem RS Ord_in_Ord] 1));
qed "RepFun_lepoll";

Goalw [lesspoll_def] "n:nat ==> n lesspoll nat";
by (rtac conjI 1);
by (eresolve_tac [Ord_nat RSN (2, OrdmemD) RS subset_imp_lepoll] 1);
by (rtac notI 1);
by (etac eqpollE 1);
by (rtac succ_lepoll_natE 1 THEN (assume_tac 2));
by (eresolve_tac [nat_succI RS (Ord_nat RSN (2, OrdmemD) RS
        subset_imp_lepoll) RS lepoll_trans] 1
        THEN (assume_tac 1));
qed "n_lesspoll_nat";

Goalw [lepoll_def]
        "[| f:X->Y; Ord(X) |] ==> f``X lepoll X";
by (res_inst_tac [("x","lam x:f``X. LEAST y. f`y = x")] exI 1);
by (res_inst_tac [("d","%z. f`z")] lam_injective 1);
by (fast_tac (claset() addSIs [Least_in_Ord, apply_equality]) 1);
by (fast_tac (claset() addSEs [Ord_in_Ord] addSIs [LeastI, apply_equality]) 1);
qed "image_Ord_lepoll";

val [major, minor] = goal thy
        "[| (!!g. g:X ==> EX u. <g,u>:R); R<=X*X  \
\       |] ==> range(R) <= domain(R)";
by (rtac subsetI 1);
by (etac rangeE 1);
by (dresolve_tac [minor RS subsetD RS SigmaD2 RS major] 1);
by (Fast_tac 1);
qed "range_subset_domain";

val prems = goal thy "!!k. k:n ==> k~=n";
by (fast_tac (claset() addSEs [mem_irrefl]) 1);
qed "mem_not_eq";

Goalw [succ_def] "g:n->X ==> cons(<n,x>, g) : succ(n) -> cons(x, X)";
by (fast_tac (claset() addSIs [fun_extend] addSEs [mem_irrefl]) 1);
qed "cons_fun_type";

Goal "[| g:n->X; x:X |] ==> cons(<n,x>, g) : succ(n) -> X";
by (etac (cons_absorb RS subst) 1 THEN etac cons_fun_type 1);
qed "cons_fun_type2";

Goal "n: nat ==> cons(<n,x>, g)``n = g``n";
by (fast_tac (claset() addSEs [mem_irrefl]) 1);
qed "cons_image_n";

Goal "g:n->X ==> cons(<n,x>, g)`n = x";
by (fast_tac (claset() addSIs [apply_equality] addSEs [cons_fun_type]) 1);
qed "cons_val_n";

Goal "k : n ==> cons(<n,x>, g)``k = g``k";
by (fast_tac (claset() addEs [mem_asym]) 1);
qed "cons_image_k";

Goal "[| k:n; g:n->X |] ==> cons(<n,x>, g)`k = g`k";
by (fast_tac (claset() addSIs [apply_equality, consI2] addSEs [cons_fun_type, apply_Pair]) 1);
qed "cons_val_k";

Goal "domain(f)=x ==> domain(cons(<x,y>, f)) = succ(x)";
by (asm_full_simp_tac (simpset() addsimps [domain_cons, succ_def]) 1);
qed "domain_cons_eq_succ";

Goalw [restrict_def] "g:n->X ==> restrict(cons(<n,x>, g), n)=g";
by (rtac fun_extension 1);
by (rtac lam_type 1);
by (eresolve_tac [cons_fun_type RS apply_type] 1);
by (etac succI2 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [cons_val_k]) 1);
qed "restrict_cons_eq";

Goal "[| Ord(k); i:k |] ==> succ(i) : succ(k)";
by (resolve_tac [Ord_linear RS disjE] 1 THEN (assume_tac 3));
by (REPEAT (fast_tac (claset() addEs [Ord_in_Ord, mem_irrefl, mem_asym]) 1));
qed "succ_in_succ";

Goalw [restrict_def]
        "[| restrict(f, domain(g)) = g; x: domain(g) |] ==> f`x = g`x";
by (etac subst 1);
by (Asm_full_simp_tac 1);
qed "restrict_eq_imp_val_eq";

Goal "[| domain(f)=A; f:B->C |] ==> f:A->C";
by (ftac domain_of_fun 1);
by (Fast_tac 1);
qed "domain_eq_imp_fun_type";

Goal "[| R <= A * B; R ~= 0 |] ==> EX x. x:domain(R)";
by (fast_tac (claset() addSEs [not_emptyE]) 1);
qed "ex_in_domain";

