(*  Title: 	ZF/epsilon.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For epsilon.thy.  Epsilon induction and recursion
*)

open Epsilon;

(*** Basic closure properties ***)

goalw Epsilon.thy [eclose_def] "A <= eclose(A)";
by (rtac (nat_rec_0 RS equalityD2 RS subset_trans) 1);
br (nat_0I RS UN_upper) 1;
val arg_subset_eclose = result();

val arg_into_eclose = arg_subset_eclose RS subsetD;

goalw Epsilon.thy [eclose_def,Transset_def] "Transset(eclose(A))";
by (rtac (subsetI RS ballI) 1);
by (etac UN_E 1);
by (rtac (nat_succI RS UN_I) 1);
by (assume_tac 1);
by (etac (nat_rec_succ RS ssubst) 1);
by (etac UnionI 1);
by (assume_tac 1);
val Transset_eclose = result();

(* x : eclose(A) ==> x <= eclose(A) *)
val eclose_subset = 
    standard (rewrite_rule [Transset_def] Transset_eclose RS bspec);

(* [| A : eclose(B); c : A |] ==> c : eclose(B) *)
val ecloseD = standard (eclose_subset RS subsetD);

val arg_in_eclose_sing = arg_subset_eclose RS singleton_subsetD;
val arg_into_eclose_sing = arg_in_eclose_sing RS ecloseD;

(* This is epsilon-induction for eclose(A); see also eclose_induct_down...
   [| a: eclose(A);  !!x. [| x: eclose(A); ALL y:x. P(y) |] ==> P(x) 
   |] ==> P(a) 
*)
val eclose_induct = standard (Transset_eclose RSN (2, Transset_induct));

(*Epsilon induction*)
val prems = goal Epsilon.thy
    "[| !!x. ALL y:x. P(y) ==> P(x) |]  ==>  P(a)";
by (rtac (arg_in_eclose_sing RS eclose_induct) 1);
by (eresolve_tac prems 1);
val eps_induct = result();

(*Perform epsilon-induction on i. *)
fun eps_ind_tac a = 
    EVERY' [res_inst_tac [("a",a)] eps_induct,
	    rename_last_tac a ["1"]];


(*** Leastness of eclose ***)

(** eclose(A) is the least transitive set including A as a subset. **)

goalw Epsilon.thy [Transset_def]
    "!!X A n. [| Transset(X);  A<=X;  n: nat |] ==> \
\             nat_rec(n, A, %m r. Union(r)) <= X";
by (etac nat_induct 1);
by (asm_simp_tac (ZF_ss addsimps [nat_rec_0]) 1);
by (asm_simp_tac (ZF_ss addsimps [nat_rec_succ]) 1);
by (fast_tac ZF_cs 1);
val eclose_least_lemma = result();

goalw Epsilon.thy [eclose_def]
     "!!X A. [| Transset(X);  A<=X |] ==> eclose(A) <= X";
br (eclose_least_lemma RS UN_least) 1;
by (REPEAT (assume_tac 1));
val eclose_least = result();

(*COMPLETELY DIFFERENT induction principle from eclose_induct!!*)
val [major,base,step] = goal Epsilon.thy
    "[| a: eclose(b);						\
\       !!y.   [| y: b |] ==> P(y);				\
\       !!y z. [| y: eclose(b);  P(y);  z: y |] ==> P(z)	\
\    |] ==> P(a)";
by (rtac (major RSN (3, eclose_least RS subsetD RS CollectD2)) 1);
by (rtac (CollectI RS subsetI) 2);
by (etac (arg_subset_eclose RS subsetD) 2);
by (etac base 2);
by (rewtac Transset_def);
by (fast_tac (ZF_cs addEs [step,ecloseD]) 1);
val eclose_induct_down = result();

goal Epsilon.thy "!!X. Transset(X) ==> eclose(X) = X";
be ([eclose_least, arg_subset_eclose] MRS equalityI) 1;
br subset_refl 1;
val Transset_eclose_eq_arg = result();


(*** Epsilon recursion ***)

(*Unused...*)
goal Epsilon.thy "!!A B C. [| A: eclose(B);  B: eclose(C) |] ==> A: eclose(C)";
by (rtac ([Transset_eclose, eclose_subset] MRS eclose_least RS subsetD) 1);
by (REPEAT (assume_tac 1));
val mem_eclose_trans = result();

(*Variant of the previous lemma in a useable form for the sequel*)
goal Epsilon.thy
    "!!A B C. [| A: eclose({B});  B: eclose({C}) |] ==> A: eclose({C})";
by (rtac ([Transset_eclose, singleton_subsetI] MRS eclose_least RS subsetD) 1);
by (REPEAT (assume_tac 1));
val mem_eclose_sing_trans = result();

goalw Epsilon.thy [Transset_def]
    "!!i j. [| Transset(i);  j:i |] ==> Memrel(i)-``{j} = j";
by (fast_tac (eq_cs addSIs [MemrelI] addSEs [MemrelE]) 1);
val under_Memrel = result();

(* j : eclose(A) ==> Memrel(eclose(A)) -`` j = j *)
val under_Memrel_eclose = Transset_eclose RS under_Memrel;

val wfrec_ssubst = standard (wf_Memrel RS wfrec RS ssubst);

val [kmemj,jmemi] = goal Epsilon.thy
    "[| k:eclose({j});  j:eclose({i}) |] ==> \
\    wfrec(Memrel(eclose({i})), k, H) = wfrec(Memrel(eclose({j})), k, H)";
by (rtac (kmemj RS eclose_induct) 1);
by (rtac wfrec_ssubst 1);
by (rtac wfrec_ssubst 1);
by (asm_simp_tac (ZF_ss addsimps [under_Memrel_eclose,
				  jmemi RSN (2,mem_eclose_sing_trans)]) 1);
val wfrec_eclose_eq = result();

val [prem] = goal Epsilon.thy
    "k: i ==> wfrec(Memrel(eclose({i})),k,H) = wfrec(Memrel(eclose({k})),k,H)";
by (rtac (arg_in_eclose_sing RS wfrec_eclose_eq) 1);
by (rtac (prem RS arg_into_eclose_sing) 1);
val wfrec_eclose_eq2 = result();

goalw Epsilon.thy [transrec_def]
    "transrec(a,H) = H(a, lam x:a. transrec(x,H))";
by (rtac wfrec_ssubst 1);
by (simp_tac (ZF_ss addsimps [wfrec_eclose_eq2, arg_in_eclose_sing,
			      under_Memrel_eclose]) 1);
val transrec = result();

(*Avoids explosions in proofs; resolve it with a meta-level definition.*)
val rew::prems = goal Epsilon.thy
    "[| !!x. f(x)==transrec(x,H) |] ==> f(a) = H(a, lam x:a. f(x))";
by (rewtac rew);
by (REPEAT (resolve_tac (prems@[transrec]) 1));
val def_transrec = result();

val prems = goal Epsilon.thy
    "[| !!x u. [| x:eclose({a});  u: Pi(x,B) |] ==> H(x,u) : B(x)   \
\    |]  ==> transrec(a,H) : B(a)";
by (res_inst_tac [("i", "a")] (arg_in_eclose_sing RS eclose_induct) 1);
by (rtac (transrec RS ssubst) 1);
by (REPEAT (ares_tac (prems @ [lam_type]) 1 ORELSE etac bspec 1));
val transrec_type = result();

goal Epsilon.thy "!!i. Ord(i) ==> eclose({i}) <= succ(i)";
by (etac (Ord_is_Transset RS Transset_succ RS eclose_least) 1);
by (rtac (succI1 RS singleton_subsetI) 1);
val eclose_sing_Ord = result();

val prems = goal Epsilon.thy
    "[| j: i;  Ord(i);  \
\       !!x u. [| x: i;  u: Pi(x,B) |] ==> H(x,u) : B(x)   \
\    |]  ==> transrec(j,H) : B(j)";
by (rtac transrec_type 1);
by (resolve_tac prems 1);
by (rtac (Ord_in_Ord RS eclose_sing_Ord RS subsetD RS succE) 1);
by (DEPTH_SOLVE (ares_tac prems 1 ORELSE eresolve_tac [ssubst,Ord_trans] 1));
val Ord_transrec_type = result();

(*** Rank ***)

(*NOT SUITABLE FOR REWRITING -- RECURSIVE!*)
goal Epsilon.thy "rank(a) = (UN y:a. succ(rank(y)))";
by (rtac (rank_def RS def_transrec RS ssubst) 1);
by (simp_tac ZF_ss 1);
val rank = result();

goal Epsilon.thy "Ord(rank(a))";
by (eps_ind_tac "a" 1);
by (rtac (rank RS ssubst) 1);
by (rtac (Ord_succ RS Ord_UN) 1);
by (etac bspec 1);
by (assume_tac 1);
val Ord_rank = result();

val [major] = goal Epsilon.thy "Ord(i) ==> rank(i) = i";
by (rtac (major RS trans_induct) 1);
by (rtac (rank RS ssubst) 1);
by (asm_simp_tac (ZF_ss addsimps [Ord_equality]) 1);
val rank_of_Ord = result();

val [prem] = goal Epsilon.thy "a:b ==> rank(a) : rank(b)";
by (res_inst_tac [("a1","b")] (rank RS ssubst) 1);
by (rtac (prem RS UN_I) 1);
by (rtac succI1 1);
val rank_lt = result();

val [major] = goal Epsilon.thy "a: eclose(b) ==> rank(a) : rank(b)";
by (rtac (major RS eclose_induct_down) 1);
by (etac rank_lt 1);
by (etac (rank_lt RS Ord_trans) 1);
by (assume_tac 1);
by (rtac Ord_rank 1);
val eclose_rank_lt = result();

goal Epsilon.thy "!!a b. a<=b ==> rank(a) <= rank(b)";
by (rtac (rank RS ssubst) 1);
by (rtac (rank RS ssubst) 1);
by (etac UN_mono 1);
by (rtac subset_refl 1);
val rank_mono = result();

goal Epsilon.thy "rank(Pow(a)) = succ(rank(a))";
by (rtac (rank RS trans) 1);
by (rtac equalityI 1);
by (fast_tac ZF_cs 2);
by (rtac UN_least 1);
by (etac (PowD RS rank_mono RS Ord_succ_mono) 1);
by (rtac Ord_rank 1);
by (rtac Ord_rank 1);
val rank_Pow = result();

goal Epsilon.thy "rank(0) = 0";
by (rtac (rank RS trans) 1);
by (fast_tac (ZF_cs addSIs [equalityI]) 1);
val rank_0 = result();

goal Epsilon.thy "rank(succ(x)) = succ(rank(x))";
by (rtac (rank RS trans) 1);
br ([UN_least, succI1 RS UN_upper] MRS equalityI) 1;
be succE 1;
by (fast_tac ZF_cs 1);
by (REPEAT (ares_tac [Ord_succ_mono,Ord_rank,OrdmemD,rank_lt] 1));
val rank_succ = result();

goal Epsilon.thy "rank(Union(A)) = (UN x:A. rank(x))";
by (rtac equalityI 1);
by (rtac (rank_mono RS UN_least) 2);
by (etac Union_upper 2);
by (rtac (rank RS ssubst) 1);
by (rtac UN_least 1);
by (etac UnionE 1);
by (rtac subset_trans 1);
by (etac (RepFunI RS Union_upper) 2);
by (etac (rank_lt RS Ord_succ_subsetI) 1);
by (rtac Ord_rank 1);
val rank_Union = result();

goal Epsilon.thy "rank(eclose(a)) = rank(a)";
by (rtac equalityI 1);
by (rtac (arg_subset_eclose RS rank_mono) 2);
by (res_inst_tac [("a1","eclose(a)")] (rank RS ssubst) 1);
by (rtac UN_least 1);
by (etac ([eclose_rank_lt, Ord_rank] MRS Ord_succ_subsetI) 1);
val rank_eclose = result();

(*  [| i: j; j: rank(a) |] ==> i: rank(a)  *)
val rank_trans = Ord_rank RSN (3, Ord_trans);

goalw Epsilon.thy [Pair_def] "rank(a) : rank(<a,b>)";
by (rtac (consI1 RS rank_lt RS Ord_trans) 1);
by (rtac (consI1 RS consI2 RS rank_lt) 1);
by (rtac Ord_rank 1);
val rank_pair1 = result();

goalw Epsilon.thy [Pair_def] "rank(b) : rank(<a,b>)";
by (rtac (consI1 RS consI2 RS rank_lt RS Ord_trans) 1);
by (rtac (consI1 RS consI2 RS rank_lt) 1);
by (rtac Ord_rank 1);
val rank_pair2 = result();

goalw (merge_theories(Epsilon.thy,Sum.thy)) [Inl_def] "rank(a) : rank(Inl(a))";
by (rtac rank_pair2 1);
val rank_Inl = result();

goalw (merge_theories(Epsilon.thy,Sum.thy)) [Inr_def] "rank(a) : rank(Inr(a))";
by (rtac rank_pair2 1);
val rank_Inr = result();

val [major] = goal Epsilon.thy "i: rank(a) ==> (EX x:a. i<=rank(x))";
by (resolve_tac ([major] RL [rank RS subst] RL [UN_E]) 1);
by (rtac bexI 1);
by (etac member_succD 1);
by (rtac Ord_rank 1);
by (assume_tac 1);
val rank_implies_mem = result();


(*** Corollaries of leastness ***)

goal Epsilon.thy "!!A B. A:B ==> eclose(A)<=eclose(B)";
by (rtac (Transset_eclose RS eclose_least) 1);
by (etac (arg_into_eclose RS eclose_subset) 1);
val mem_eclose_subset = result();

goal Epsilon.thy "!!A B. A<=B ==> eclose(A) <= eclose(B)";
by (rtac (Transset_eclose RS eclose_least) 1);
by (etac subset_trans 1);
by (rtac arg_subset_eclose 1);
val eclose_mono = result();

(** Idempotence of eclose **)

goal Epsilon.thy "eclose(eclose(A)) = eclose(A)";
by (rtac equalityI 1);
by (rtac ([Transset_eclose, subset_refl] MRS eclose_least) 1);
by (rtac arg_subset_eclose 1);
val eclose_idem = result();
