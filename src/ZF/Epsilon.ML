(*  Title:      ZF/epsilon.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For epsilon.thy.  Epsilon induction and recursion
*)

open Epsilon;

(*** Basic closure properties ***)

goalw Epsilon.thy [eclose_def] "A <= eclose(A)";
by (rtac (nat_rec_0 RS equalityD2 RS subset_trans) 1);
by (rtac (nat_0I RS UN_upper) 1);
qed "arg_subset_eclose";

val arg_into_eclose = arg_subset_eclose RS subsetD;

goalw Epsilon.thy [eclose_def,Transset_def] "Transset(eclose(A))";
by (rtac (subsetI RS ballI) 1);
by (etac UN_E 1);
by (rtac (nat_succI RS UN_I) 1);
by (assume_tac 1);
by (etac (nat_rec_succ RS ssubst) 1);
by (etac UnionI 1);
by (assume_tac 1);
qed "Transset_eclose";

(* x : eclose(A) ==> x <= eclose(A) *)
bind_thm ("eclose_subset",
    rewrite_rule [Transset_def] Transset_eclose RS bspec);

(* [| A : eclose(B); c : A |] ==> c : eclose(B) *)
bind_thm ("ecloseD", eclose_subset RS subsetD);

val arg_in_eclose_sing = arg_subset_eclose RS singleton_subsetD;
val arg_into_eclose_sing = arg_in_eclose_sing RS ecloseD;

(* This is epsilon-induction for eclose(A); see also eclose_induct_down...
   [| a: eclose(A);  !!x. [| x: eclose(A); ALL y:x. P(y) |] ==> P(x) 
   |] ==> P(a) 
*)
bind_thm ("eclose_induct", Transset_eclose RSN (2, Transset_induct));

(*Epsilon induction*)
val prems = goal Epsilon.thy
    "[| !!x. ALL y:x. P(y) ==> P(x) |]  ==>  P(a)";
by (rtac (arg_in_eclose_sing RS eclose_induct) 1);
by (eresolve_tac prems 1);
qed "eps_induct";

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
qed "eclose_least_lemma";

goalw Epsilon.thy [eclose_def]
     "!!X A. [| Transset(X);  A<=X |] ==> eclose(A) <= X";
by (rtac (eclose_least_lemma RS UN_least) 1);
by (REPEAT (assume_tac 1));
qed "eclose_least";

(*COMPLETELY DIFFERENT induction principle from eclose_induct!!*)
val [major,base,step] = goal Epsilon.thy
    "[| a: eclose(b);                                           \
\       !!y.   [| y: b |] ==> P(y);                             \
\       !!y z. [| y: eclose(b);  P(y);  z: y |] ==> P(z)        \
\    |] ==> P(a)";
by (rtac (major RSN (3, eclose_least RS subsetD RS CollectD2)) 1);
by (rtac (CollectI RS subsetI) 2);
by (etac (arg_subset_eclose RS subsetD) 2);
by (etac base 2);
by (rewtac Transset_def);
by (fast_tac (ZF_cs addEs [step,ecloseD]) 1);
qed "eclose_induct_down";

goal Epsilon.thy "!!X. Transset(X) ==> eclose(X) = X";
by (etac ([eclose_least, arg_subset_eclose] MRS equalityI) 1);
by (rtac subset_refl 1);
qed "Transset_eclose_eq_arg";


(*** Epsilon recursion ***)

(*Unused...*)
goal Epsilon.thy "!!A B C. [| A: eclose(B);  B: eclose(C) |] ==> A: eclose(C)";
by (rtac ([Transset_eclose, eclose_subset] MRS eclose_least RS subsetD) 1);
by (REPEAT (assume_tac 1));
qed "mem_eclose_trans";

(*Variant of the previous lemma in a useable form for the sequel*)
goal Epsilon.thy
    "!!A B C. [| A: eclose({B});  B: eclose({C}) |] ==> A: eclose({C})";
by (rtac ([Transset_eclose, singleton_subsetI] MRS eclose_least RS subsetD) 1);
by (REPEAT (assume_tac 1));
qed "mem_eclose_sing_trans";

goalw Epsilon.thy [Transset_def]
    "!!i j. [| Transset(i);  j:i |] ==> Memrel(i)-``{j} = j";
by (fast_tac (eq_cs addSIs [MemrelI] addSEs [MemrelE]) 1);
qed "under_Memrel";

(* j : eclose(A) ==> Memrel(eclose(A)) -`` j = j *)
val under_Memrel_eclose = Transset_eclose RS under_Memrel;

bind_thm ("wfrec_ssubst", wf_Memrel RS wfrec RS ssubst);

val [kmemj,jmemi] = goal Epsilon.thy
    "[| k:eclose({j});  j:eclose({i}) |] ==> \
\    wfrec(Memrel(eclose({i})), k, H) = wfrec(Memrel(eclose({j})), k, H)";
by (rtac (kmemj RS eclose_induct) 1);
by (rtac wfrec_ssubst 1);
by (rtac wfrec_ssubst 1);
by (asm_simp_tac (ZF_ss addsimps [under_Memrel_eclose,
                                  jmemi RSN (2,mem_eclose_sing_trans)]) 1);
qed "wfrec_eclose_eq";

val [prem] = goal Epsilon.thy
    "k: i ==> wfrec(Memrel(eclose({i})),k,H) = wfrec(Memrel(eclose({k})),k,H)";
by (rtac (arg_in_eclose_sing RS wfrec_eclose_eq) 1);
by (rtac (prem RS arg_into_eclose_sing) 1);
qed "wfrec_eclose_eq2";

goalw Epsilon.thy [transrec_def]
    "transrec(a,H) = H(a, lam x:a. transrec(x,H))";
by (rtac wfrec_ssubst 1);
by (simp_tac (ZF_ss addsimps [wfrec_eclose_eq2, arg_in_eclose_sing,
                              under_Memrel_eclose]) 1);
qed "transrec";

(*Avoids explosions in proofs; resolve it with a meta-level definition.*)
val rew::prems = goal Epsilon.thy
    "[| !!x. f(x)==transrec(x,H) |] ==> f(a) = H(a, lam x:a. f(x))";
by (rewtac rew);
by (REPEAT (resolve_tac (prems@[transrec]) 1));
qed "def_transrec";

val prems = goal Epsilon.thy
    "[| !!x u. [| x:eclose({a});  u: Pi(x,B) |] ==> H(x,u) : B(x)   \
\    |]  ==> transrec(a,H) : B(a)";
by (res_inst_tac [("i", "a")] (arg_in_eclose_sing RS eclose_induct) 1);
by (rtac (transrec RS ssubst) 1);
by (REPEAT (ares_tac (prems @ [lam_type]) 1 ORELSE etac bspec 1));
qed "transrec_type";

goal Epsilon.thy "!!i. Ord(i) ==> eclose({i}) <= succ(i)";
by (etac (Ord_is_Transset RS Transset_succ RS eclose_least) 1);
by (rtac (succI1 RS singleton_subsetI) 1);
qed "eclose_sing_Ord";

val prems = goal Epsilon.thy
    "[| j: i;  Ord(i);  \
\       !!x u. [| x: i;  u: Pi(x,B) |] ==> H(x,u) : B(x)   \
\    |]  ==> transrec(j,H) : B(j)";
by (rtac transrec_type 1);
by (resolve_tac prems 1);
by (rtac (Ord_in_Ord RS eclose_sing_Ord RS subsetD RS succE) 1);
by (DEPTH_SOLVE (ares_tac prems 1 ORELSE eresolve_tac [ssubst,Ord_trans] 1));
qed "Ord_transrec_type";

(*** Rank ***)

(*NOT SUITABLE FOR REWRITING -- RECURSIVE!*)
goal Epsilon.thy "rank(a) = (UN y:a. succ(rank(y)))";
by (rtac (rank_def RS def_transrec RS ssubst) 1);
by (simp_tac ZF_ss 1);
qed "rank";

goal Epsilon.thy "Ord(rank(a))";
by (eps_ind_tac "a" 1);
by (rtac (rank RS ssubst) 1);
by (rtac (Ord_succ RS Ord_UN) 1);
by (etac bspec 1);
by (assume_tac 1);
qed "Ord_rank";

val [major] = goal Epsilon.thy "Ord(i) ==> rank(i) = i";
by (rtac (major RS trans_induct) 1);
by (rtac (rank RS ssubst) 1);
by (asm_simp_tac (ZF_ss addsimps [Ord_equality]) 1);
qed "rank_of_Ord";

goal Epsilon.thy "!!a b. a:b ==> rank(a) < rank(b)";
by (res_inst_tac [("a1","b")] (rank RS ssubst) 1);
by (etac (UN_I RS ltI) 1);
by (rtac succI1 1);
by (REPEAT (ares_tac [Ord_UN, Ord_succ, Ord_rank] 1));
qed "rank_lt";

val [major] = goal Epsilon.thy "a: eclose(b) ==> rank(a) < rank(b)";
by (rtac (major RS eclose_induct_down) 1);
by (etac rank_lt 1);
by (etac (rank_lt RS lt_trans) 1);
by (assume_tac 1);
qed "eclose_rank_lt";

goal Epsilon.thy "!!a b. a<=b ==> rank(a) le rank(b)";
by (rtac subset_imp_le 1);
by (rtac (rank RS ssubst) 1);
by (rtac (rank RS ssubst) 1);
by (etac UN_mono 1);
by (REPEAT (resolve_tac [subset_refl, Ord_rank] 1));
qed "rank_mono";

goal Epsilon.thy "rank(Pow(a)) = succ(rank(a))";
by (rtac (rank RS trans) 1);
by (rtac le_anti_sym 1);
by (DO_GOAL [rtac (Ord_rank RS Ord_succ RS UN_least_le),
             etac (PowD RS rank_mono RS succ_leI)] 1);
by (DO_GOAL [rtac ([Pow_top, le_refl] MRS UN_upper_le),
             REPEAT o rtac (Ord_rank RS Ord_succ)] 1);
qed "rank_Pow";

goal Epsilon.thy "rank(0) = 0";
by (rtac (rank RS trans) 1);
by (fast_tac (ZF_cs addSIs [equalityI]) 1);
qed "rank_0";

goal Epsilon.thy "rank(succ(x)) = succ(rank(x))";
by (rtac (rank RS trans) 1);
by (rtac ([UN_least, succI1 RS UN_upper] MRS equalityI) 1);
by (etac succE 1);
by (fast_tac ZF_cs 1);
by (etac (rank_lt RS leI RS succ_leI RS le_imp_subset) 1);
qed "rank_succ";

goal Epsilon.thy "rank(Union(A)) = (UN x:A. rank(x))";
by (rtac equalityI 1);
by (rtac (rank_mono RS le_imp_subset RS UN_least) 2);
by (etac Union_upper 2);
by (rtac (rank RS ssubst) 1);
by (rtac UN_least 1);
by (etac UnionE 1);
by (rtac subset_trans 1);
by (etac (RepFunI RS Union_upper) 2);
by (etac (rank_lt RS succ_leI RS le_imp_subset) 1);
qed "rank_Union";

goal Epsilon.thy "rank(eclose(a)) = rank(a)";
by (rtac le_anti_sym 1);
by (rtac (arg_subset_eclose RS rank_mono) 2);
by (res_inst_tac [("a1","eclose(a)")] (rank RS ssubst) 1);
by (rtac (Ord_rank RS UN_least_le) 1);
by (etac (eclose_rank_lt RS succ_leI) 1);
qed "rank_eclose";

goalw Epsilon.thy [Pair_def] "rank(a) < rank(<a,b>)";
by (rtac (consI1 RS rank_lt RS lt_trans) 1);
by (rtac (consI1 RS consI2 RS rank_lt) 1);
qed "rank_pair1";

goalw Epsilon.thy [Pair_def] "rank(b) < rank(<a,b>)";
by (rtac (consI1 RS consI2 RS rank_lt RS lt_trans) 1);
by (rtac (consI1 RS consI2 RS rank_lt) 1);
qed "rank_pair2";

goalw (merge_theories(Epsilon.thy,Sum.thy)) [Inl_def] "rank(a) < rank(Inl(a))";
by (rtac rank_pair2 1);
val rank_Inl = result();

goalw (merge_theories(Epsilon.thy,Sum.thy)) [Inr_def] "rank(a) < rank(Inr(a))";
by (rtac rank_pair2 1);
val rank_Inr = result();

(*** Corollaries of leastness ***)

goal Epsilon.thy "!!A B. A:B ==> eclose(A)<=eclose(B)";
by (rtac (Transset_eclose RS eclose_least) 1);
by (etac (arg_into_eclose RS eclose_subset) 1);
qed "mem_eclose_subset";

goal Epsilon.thy "!!A B. A<=B ==> eclose(A) <= eclose(B)";
by (rtac (Transset_eclose RS eclose_least) 1);
by (etac subset_trans 1);
by (rtac arg_subset_eclose 1);
qed "eclose_mono";

(** Idempotence of eclose **)

goal Epsilon.thy "eclose(eclose(A)) = eclose(A)";
by (rtac equalityI 1);
by (rtac ([Transset_eclose, subset_refl] MRS eclose_least) 1);
by (rtac arg_subset_eclose 1);
qed "eclose_idem";
