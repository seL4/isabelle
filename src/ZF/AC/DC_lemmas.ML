(*  Title: 	ZF/AC/DC_lemmas.ML
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

More general lemmas used in the proofs concerning DC

*)

val [prem] = goalw thy [lepoll_def]
	"Ord(a) ==> {P(b). b:a} lepoll a";
by (res_inst_tac [("x","lam z:RepFun(a,P). LEAST i. z=P(i)")] exI 1);
by (res_inst_tac [("d","%z. P(z)")] (sym RSN (2, lam_injective)) 1);
by (fast_tac (AC_cs addSEs [RepFunE] addSIs [Least_in_Ord, prem]) 1);
by (REPEAT (eresolve_tac [RepFunE, LeastI, prem RS Ord_in_Ord] 1));
val RepFun_lepoll = result();

goalw thy [lesspoll_def] "!!n. n:nat ==> n lesspoll nat";
by (resolve_tac [conjI] 1);
by (eresolve_tac [Ord_nat RSN (2, OrdmemD) RS subset_imp_lepoll] 1);
by (resolve_tac [notI] 1);
by (eresolve_tac [eqpollE] 1);
by (resolve_tac [succ_lepoll_natE] 1 THEN (assume_tac 2));
by (eresolve_tac [nat_succI RS (Ord_nat RSN (2, OrdmemD) RS
	subset_imp_lepoll) RS lepoll_trans] 1
	THEN (assume_tac 1));
val n_lesspoll_nat = result();

goalw thy [lepoll_def]
	"!!f. [| f:X->Y; Ord(X) |] ==> f``X lepoll X";
by (res_inst_tac [("x","lam x:f``X. LEAST y. f`y = x")] exI 1);
by (res_inst_tac [("d","%z. f`z")] lam_injective 1);
by (fast_tac (AC_cs addSIs [Least_in_Ord, apply_equality]) 1);
by (fast_tac (AC_cs addSEs [Ord_in_Ord] addSIs [LeastI, apply_equality]) 1);
val image_Ord_lepoll = result();

val apply_singleton_eq = [singletonI, singleton_fun] MRS apply_equality;

goal thy "restrict(f, 0) = 0";
by (resolve_tac [singleton_iff RS iffD1] 1);
by (resolve_tac [Pi_empty1 RS subst] 1);
by (fast_tac (AC_cs addSIs [restrict_type]) 1);
val restrict_0 = result();

val [major, minor] = goal thy
	"[| (!!g. g:X ==> EX u. <g,u>:R); R<=X*X  \
\	|] ==> range(R) <= domain(R)";
by (resolve_tac [subsetI] 1);
by (eresolve_tac [rangeE] 1);
by (dresolve_tac [minor RS subsetD RS SigmaD2 RS major] 1);
by (fast_tac AC_cs 1);
val range_subset_domain = result();

goal thy "domain({<x,y>}) = {x}";
by (fast_tac (AC_cs addSIs [equalityI, singletonI] addSEs [singletonE]) 1);
val domain_sing = result();

val prems = goal thy "!!k. k:n ==> k~=n";
by (fast_tac (AC_cs addSEs [mem_irrefl]) 1);
val mem_not_eq = result();

goal thy "!!a. [| a:B; A<=B |] ==> cons(a, A) <= B";
by (fast_tac AC_cs 1);
val cons_subset = result();

goal thy "!!g. g:n->X ==> cons(<n,x>, g) : succ(n) -> cons(x, X)";
by (resolve_tac [Pi_iff_old RS iffD2] 1);
by (resolve_tac [conjI] 1);
by (fast_tac (AC_cs addSIs [cons_subset, succI1]
	addEs [fun_is_rel RS subset_trans RS subsetD, succI2]) 1);
by (resolve_tac [ballI] 1);
by (eresolve_tac [succE] 1);
by (fast_tac (AC_cs addDs [domain_of_fun, domainI] addSEs [mem_irrefl]) 1);
by (fast_tac (AC_cs addDs [fun_unique_Pair] addSEs [mem_irrefl]) 1);
val cons_fun_type = result();

goal thy "!!x. x:X ==> cons(x, X) = X";
by (fast_tac (AC_cs addSIs [equalityI]) 1);
val cons_eq_self = result();

val [g_type, x_in] = goal thy "[| g:n->X; x:X |] ==> cons(<n,x>, g) : succ(n) -> X";
by (resolve_tac [x_in RS cons_eq_self RS subst] 1);
by (resolve_tac [g_type RS cons_fun_type] 1);
val cons_fun_type2 = result();

goal thy "!!n. n: nat ==> cons(<n,x>, g)``n = g``n";
by (fast_tac (AC_cs addSIs [equalityI] addSEs [mem_irrefl]) 1);
val cons_image_n = result();

goal thy "!!n. g:n->X ==> cons(<n,x>, g)`n = x";
by (fast_tac (AC_cs addSIs [apply_equality] addSEs [cons_fun_type]) 1);
val cons_val_n = result();

goal thy "!!k. k : n ==> cons(<n,x>, g)``k = g``k";
by (fast_tac (AC_cs addSIs [equalityI] addEs [mem_asym]) 1);
val cons_image_k = result();

goal thy "!!k. [| k:n; g:n->X |] ==> cons(<n,x>, g)`k = g`k";
by (fast_tac (AC_cs addSIs [apply_equality, consI2] addSEs [cons_fun_type, apply_Pair]) 1);
val cons_val_k = result();

goal thy "!!f. domain(f)=x ==> domain(cons(<x,y>, f)) = succ(x)";
by (asm_full_simp_tac (AC_ss addsimps [domain_cons, succ_def]) 1);
val domain_cons_eq_succ = result();

goalw thy [restrict_def] "!!g. g:n->X ==> restrict(cons(<n,x>, g), n)=g";
by (resolve_tac [fun_extension] 1);
by (resolve_tac [lam_type] 1);
by (eresolve_tac [cons_fun_type RS apply_type] 1);
by (eresolve_tac [succI2] 1);
by (assume_tac 1);
by (asm_full_simp_tac (AC_ss addsimps [cons_val_k]) 1);
val restrict_cons_eq = result();

goal thy "!!k. [| Ord(k); i:k |] ==> succ(i) : succ(k)";
by (resolve_tac [Ord_linear RS disjE] 1 THEN (assume_tac 3));
by (REPEAT (fast_tac (AC_cs addSIs [Ord_succ]
	addEs [Ord_in_Ord, mem_irrefl, mem_asym]
	addSDs [succ_inject]) 1));
val succ_in_succ = result();

goalw thy [restrict_def]
	"!!f. [| restrict(f, domain(g)) = g; x: domain(g) |] ==> f`x = g`x";
by (eresolve_tac [subst] 1);
by (asm_full_simp_tac AC_ss 1);
val restrict_eq_imp_val_eq = result();

goal thy "!!a. succ(a) = succ(b) ==> a = b";
by (eresolve_tac [equalityE] 1);
by (resolve_tac [equalityI] 1);
by (fast_tac (AC_cs addSEs [mem_irrefl] addEs [mem_asym]) 1);
by (fast_tac (AC_cs addSEs [mem_irrefl] addEs [mem_asym]) 1);
val succ_eqD = result();

goal thy "!!n. n:nat ==> 0:succ(n)";
by (fast_tac (AC_cs addSDs [[Ord_0, nat_into_Ord] MRS Ord_linear]) 1);
val nat_0_in_succ = result();

goal thy "!!f. [| domain(f)=A; f:B->C |] ==> f:A->C";
by (forward_tac [domain_of_fun] 1);
by (fast_tac AC_cs 1);
val domain_eq_imp_fun_type = result();

goal thy "!!R. [| R <= A * B; R ~= 0 |] ==> EX x. x:domain(R)";
by (fast_tac (AC_cs addSEs [not_emptyE]) 1);
val ex_in_domain = result();

