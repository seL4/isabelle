(*  Title:      ZF/Univ
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

The cumulative hierarchy and a small universe for recursive types
*)

open Univ;

(*NOT SUITABLE FOR REWRITING -- RECURSIVE!*)
goal Univ.thy "Vfrom(A,i) = A Un (UN j:i. Pow(Vfrom(A,j)))";
by (stac (Vfrom_def RS def_transrec) 1);
by (Simp_tac 1);
qed "Vfrom";

(** Monotonicity **)

goal Univ.thy "!!A B. A<=B ==> ALL j. i<=j --> Vfrom(A,i) <= Vfrom(B,j)";
by (eps_ind_tac "i" 1);
by (rtac (impI RS allI) 1);
by (stac Vfrom 1);
by (stac Vfrom 1);
by (etac Un_mono 1);
by (rtac UN_mono 1);
by (assume_tac 1);
by (rtac Pow_mono 1);
by (etac (bspec RS spec RS mp) 1);
by (assume_tac 1);
by (rtac subset_refl 1);
qed "Vfrom_mono_lemma";

(*  [| A<=B; i<=x |] ==> Vfrom(A,i) <= Vfrom(B,x)  *)
bind_thm ("Vfrom_mono", (Vfrom_mono_lemma RS spec RS mp));


(** A fundamental equality: Vfrom does not require ordinals! **)

goal Univ.thy "Vfrom(A,x) <= Vfrom(A,rank(x))";
by (eps_ind_tac "x" 1);
by (stac Vfrom 1);
by (stac Vfrom 1);
by (fast_tac (!claset addSIs [rank_lt RS ltD]) 1);
qed "Vfrom_rank_subset1";

goal Univ.thy "Vfrom(A,rank(x)) <= Vfrom(A,x)";
by (eps_ind_tac "x" 1);
by (stac Vfrom 1);
by (stac Vfrom 1);
by (rtac (subset_refl RS Un_mono) 1);
by (rtac UN_least 1);
(*expand rank(x1) = (UN y:x1. succ(rank(y))) in assumptions*)
by (etac (rank RS equalityD1 RS subsetD RS UN_E) 1);
by (rtac subset_trans 1);
by (etac UN_upper 2);
by (rtac (subset_refl RS Vfrom_mono RS subset_trans RS Pow_mono) 1);
by (etac (ltI RS le_imp_subset) 1);
by (rtac (Ord_rank RS Ord_succ) 1);
by (etac bspec 1);
by (assume_tac 1);
qed "Vfrom_rank_subset2";

goal Univ.thy "Vfrom(A,rank(x)) = Vfrom(A,x)";
by (rtac equalityI 1);
by (rtac Vfrom_rank_subset2 1);
by (rtac Vfrom_rank_subset1 1);
qed "Vfrom_rank_eq";


(*** Basic closure properties ***)

goal Univ.thy "!!x y. y:x ==> 0 : Vfrom(A,x)";
by (stac Vfrom 1);
by (Fast_tac 1);
qed "zero_in_Vfrom";

goal Univ.thy "i <= Vfrom(A,i)";
by (eps_ind_tac "i" 1);
by (stac Vfrom 1);
by (Fast_tac 1);
qed "i_subset_Vfrom";

goal Univ.thy "A <= Vfrom(A,i)";
by (stac Vfrom 1);
by (rtac Un_upper1 1);
qed "A_subset_Vfrom";

bind_thm ("A_into_Vfrom", A_subset_Vfrom RS subsetD);

goal Univ.thy "!!A a i. a <= Vfrom(A,i) ==> a: Vfrom(A,succ(i))";
by (stac Vfrom 1);
by (Fast_tac 1);
qed "subset_mem_Vfrom";

(** Finite sets and ordered pairs **)

goal Univ.thy "!!a. a: Vfrom(A,i) ==> {a} : Vfrom(A,succ(i))";
by (rtac subset_mem_Vfrom 1);
by (safe_tac (!claset));
qed "singleton_in_Vfrom";

goal Univ.thy
    "!!A. [| a: Vfrom(A,i);  b: Vfrom(A,i) |] ==> {a,b} : Vfrom(A,succ(i))";
by (rtac subset_mem_Vfrom 1);
by (safe_tac (!claset));
qed "doubleton_in_Vfrom";

goalw Univ.thy [Pair_def]
    "!!A. [| a: Vfrom(A,i);  b: Vfrom(A,i) |] ==> \
\         <a,b> : Vfrom(A,succ(succ(i)))";
by (REPEAT (ares_tac [doubleton_in_Vfrom] 1));
qed "Pair_in_Vfrom";

val [prem] = goal Univ.thy
    "a<=Vfrom(A,i) ==> succ(a) : Vfrom(A,succ(succ(i)))";
by (REPEAT (resolve_tac [subset_mem_Vfrom, succ_subsetI] 1));
by (rtac (Vfrom_mono RSN (2,subset_trans)) 2);
by (REPEAT (resolve_tac [prem, subset_refl, subset_succI] 1));
qed "succ_in_Vfrom";

(*** 0, successor and limit equations fof Vfrom ***)

goal Univ.thy "Vfrom(A,0) = A";
by (stac Vfrom 1);
by (Fast_tac 1);
qed "Vfrom_0";

goal Univ.thy "!!i. Ord(i) ==> Vfrom(A,succ(i)) = A Un Pow(Vfrom(A,i))";
by (rtac (Vfrom RS trans) 1);
by (rtac (succI1 RS RepFunI RS Union_upper RSN
              (2, equalityI RS subst_context)) 1);
by (rtac UN_least 1);
by (rtac (subset_refl RS Vfrom_mono RS Pow_mono) 1);
by (etac (ltI RS le_imp_subset) 1);
by (etac Ord_succ 1);
qed "Vfrom_succ_lemma";

goal Univ.thy "Vfrom(A,succ(i)) = A Un Pow(Vfrom(A,i))";
by (res_inst_tac [("x1", "succ(i)")] (Vfrom_rank_eq RS subst) 1);
by (res_inst_tac [("x1", "i")] (Vfrom_rank_eq RS subst) 1);
by (stac rank_succ 1);
by (rtac (Ord_rank RS Vfrom_succ_lemma) 1);
qed "Vfrom_succ";

(*The premise distinguishes this from Vfrom(A,0);  allowing X=0 forces
  the conclusion to be Vfrom(A,Union(X)) = A Un (UN y:X. Vfrom(A,y)) *)
val [prem] = goal Univ.thy "y:X ==> Vfrom(A,Union(X)) = (UN y:X. Vfrom(A,y))";
by (stac Vfrom 1);
by (rtac equalityI 1);
(*first inclusion*)
by (rtac Un_least 1);
by (rtac (A_subset_Vfrom RS subset_trans) 1);
by (rtac (prem RS UN_upper) 1);
by (rtac UN_least 1);
by (etac UnionE 1);
by (rtac subset_trans 1);
by (etac UN_upper 2);
by (stac Vfrom 1);
by (etac ([UN_upper, Un_upper2] MRS subset_trans) 1);
(*opposite inclusion*)
by (rtac UN_least 1);
by (stac Vfrom 1);
by (Fast_tac 1);
qed "Vfrom_Union";

(*** Vfrom applied to Limit ordinals ***)

(*NB. limit ordinals are non-empty;
                        Vfrom(A,0) = A = A Un (UN y:0. Vfrom(A,y)) *)
val [limiti] = goal Univ.thy
    "Limit(i) ==> Vfrom(A,i) = (UN y:i. Vfrom(A,y))";
by (rtac (limiti RS (Limit_has_0 RS ltD) RS Vfrom_Union RS subst) 1);
by (stac (limiti RS Limit_Union_eq) 1);
by (rtac refl 1);
qed "Limit_Vfrom_eq";

goal Univ.thy "!!a. [| a: Vfrom(A,j);  Limit(i);  j<i |] ==> a : Vfrom(A,i)";
by (rtac (Limit_Vfrom_eq RS equalityD2 RS subsetD) 1);
by (REPEAT (ares_tac [ltD RS UN_I] 1));
qed "Limit_VfromI";

val prems = goal Univ.thy
    "[| a: Vfrom(A,i);  Limit(i);               \
\       !!x. [| x<i;  a: Vfrom(A,x) |] ==> R    \
\    |] ==> R";
by (rtac (Limit_Vfrom_eq RS equalityD1 RS subsetD RS UN_E) 1);
by (REPEAT (ares_tac (prems @ [ltI, Limit_is_Ord]) 1));
qed "Limit_VfromE";

val zero_in_VLimit = Limit_has_0 RS ltD RS zero_in_Vfrom;

val [major,limiti] = goal Univ.thy
    "[| a: Vfrom(A,i);  Limit(i) |] ==> {a} : Vfrom(A,i)";
by (rtac ([major,limiti] MRS Limit_VfromE) 1);
by (etac ([singleton_in_Vfrom, limiti] MRS Limit_VfromI) 1);
by (etac (limiti RS Limit_has_succ) 1);
qed "singleton_in_VLimit";

val Vfrom_UnI1 = Un_upper1 RS (subset_refl RS Vfrom_mono RS subsetD)
and Vfrom_UnI2 = Un_upper2 RS (subset_refl RS Vfrom_mono RS subsetD);

(*Hard work is finding a single j:i such that {a,b}<=Vfrom(A,j)*)
val [aprem,bprem,limiti] = goal Univ.thy
    "[| a: Vfrom(A,i);  b: Vfrom(A,i);  Limit(i) |] ==> \
\    {a,b} : Vfrom(A,i)";
by (rtac ([aprem,limiti] MRS Limit_VfromE) 1);
by (rtac ([bprem,limiti] MRS Limit_VfromE) 1);
by (rtac ([doubleton_in_Vfrom, limiti] MRS Limit_VfromI) 1);
by (etac Vfrom_UnI1 1);
by (etac Vfrom_UnI2 1);
by (REPEAT (ares_tac [limiti, Limit_has_succ, Un_least_lt] 1));
qed "doubleton_in_VLimit";

val [aprem,bprem,limiti] = goal Univ.thy
    "[| a: Vfrom(A,i);  b: Vfrom(A,i);  Limit(i) |] ==> \
\    <a,b> : Vfrom(A,i)";
(*Infer that a, b occur at ordinals x,xa < i.*)
by (rtac ([aprem,limiti] MRS Limit_VfromE) 1);
by (rtac ([bprem,limiti] MRS Limit_VfromE) 1);
by (rtac ([Pair_in_Vfrom, limiti] MRS Limit_VfromI) 1);
(*Infer that succ(succ(x Un xa)) < i *)
by (etac Vfrom_UnI1 1);
by (etac Vfrom_UnI2 1);
by (REPEAT (ares_tac [limiti, Limit_has_succ, Un_least_lt] 1));
qed "Pair_in_VLimit";

goal Univ.thy "!!i. Limit(i) ==> Vfrom(A,i)*Vfrom(A,i) <= Vfrom(A,i)";
by (REPEAT (ares_tac [subsetI,Pair_in_VLimit] 1
     ORELSE eresolve_tac [SigmaE, ssubst] 1));
qed "product_VLimit";

bind_thm ("Sigma_subset_VLimit",
          [Sigma_mono, product_VLimit] MRS subset_trans);

bind_thm ("nat_subset_VLimit", 
          [nat_le_Limit RS le_imp_subset, i_subset_Vfrom] MRS subset_trans);

goal Univ.thy "!!i. [| n: nat;  Limit(i) |] ==> n : Vfrom(A,i)";
by (REPEAT (ares_tac [nat_subset_VLimit RS subsetD] 1));
qed "nat_into_VLimit";

(** Closure under disjoint union **)

bind_thm ("zero_in_VLimit", Limit_has_0 RS ltD RS zero_in_Vfrom);

goal Univ.thy "!!i. Limit(i) ==> 1 : Vfrom(A,i)";
by (REPEAT (ares_tac [nat_into_VLimit, nat_0I, nat_succI] 1));
qed "one_in_VLimit";

goalw Univ.thy [Inl_def]
    "!!A a. [| a: Vfrom(A,i); Limit(i) |] ==> Inl(a) : Vfrom(A,i)";
by (REPEAT (ares_tac [zero_in_VLimit, Pair_in_VLimit] 1));
qed "Inl_in_VLimit";

goalw Univ.thy [Inr_def]
    "!!A b. [| b: Vfrom(A,i); Limit(i) |] ==> Inr(b) : Vfrom(A,i)";
by (REPEAT (ares_tac [one_in_VLimit, Pair_in_VLimit] 1));
qed "Inr_in_VLimit";

goal Univ.thy "!!i. Limit(i) ==> Vfrom(C,i)+Vfrom(C,i) <= Vfrom(C,i)";
by (fast_tac (!claset addSIs [Inl_in_VLimit, Inr_in_VLimit]) 1);
qed "sum_VLimit";

bind_thm ("sum_subset_VLimit", [sum_mono, sum_VLimit] MRS subset_trans);



(*** Properties assuming Transset(A) ***)

goal Univ.thy "!!i A. Transset(A) ==> Transset(Vfrom(A,i))";
by (eps_ind_tac "i" 1);
by (stac Vfrom 1);
by (fast_tac (!claset addSIs [Transset_Union_family, Transset_Un,
                            Transset_Pow]) 1);
qed "Transset_Vfrom";

goal Univ.thy "!!A i. Transset(A) ==> Vfrom(A, succ(i)) = Pow(Vfrom(A,i))";
by (rtac (Vfrom_succ RS trans) 1);
by (rtac (Un_upper2 RSN (2,equalityI)) 1);
by (rtac (subset_refl RSN (2,Un_least)) 1);
by (rtac (A_subset_Vfrom RS subset_trans) 1);
by (etac (Transset_Vfrom RS (Transset_iff_Pow RS iffD1)) 1);
qed "Transset_Vfrom_succ";

goalw Ordinal.thy [Pair_def,Transset_def]
    "!!C. [| <a,b> <= C; Transset(C) |] ==> a: C & b: C";
by (Best_tac 1);
qed "Transset_Pair_subset";

goal Univ.thy
    "!!a b.[| <a,b> <= Vfrom(A,i);  Transset(A);  Limit(i) |] ==> \
\          <a,b> : Vfrom(A,i)";
by (etac (Transset_Pair_subset RS conjE) 1);
by (etac Transset_Vfrom 1);
by (REPEAT (ares_tac [Pair_in_VLimit] 1));
qed "Transset_Pair_subset_VLimit";


(*** Closure under product/sum applied to elements -- thus Vfrom(A,i) 
     is a model of simple type theory provided A is a transitive set
     and i is a limit ordinal
***)

(*General theorem for membership in Vfrom(A,i) when i is a limit ordinal*)
val [aprem,bprem,limiti,step] = goal Univ.thy
  "[| a: Vfrom(A,i);  b: Vfrom(A,i);  Limit(i);                 \
\     !!x y j. [| j<i; 1:j; x: Vfrom(A,j); y: Vfrom(A,j) \
\              |] ==> EX k. h(x,y): Vfrom(A,k) & k<i |] ==>     \
\  h(a,b) : Vfrom(A,i)";
(*Infer that a, b occur at ordinals x,xa < i.*)
by (rtac ([aprem,limiti] MRS Limit_VfromE) 1);
by (rtac ([bprem,limiti] MRS Limit_VfromE) 1);
by (res_inst_tac [("j1", "x Un xa Un 2")] (step RS exE) 1);
by (DO_GOAL [etac conjE, etac Limit_VfromI, rtac limiti, atac] 5);
by (etac (Vfrom_UnI2 RS Vfrom_UnI1) 4);
by (etac (Vfrom_UnI1 RS Vfrom_UnI1) 3);
by (rtac (succI1 RS UnI2) 2);
by (REPEAT (ares_tac [limiti, Limit_has_0, Limit_has_succ, Un_least_lt] 1));
qed "in_VLimit";

(** products **)

goal Univ.thy
    "!!A. [| a: Vfrom(A,j);  b: Vfrom(A,j);  Transset(A) |] ==> \
\         a*b : Vfrom(A, succ(succ(succ(j))))";
by (dtac Transset_Vfrom 1);
by (rtac subset_mem_Vfrom 1);
by (rewtac Transset_def);
by (fast_tac (!claset addIs [Pair_in_Vfrom]) 1);
qed "prod_in_Vfrom";

val [aprem,bprem,limiti,transset] = goal Univ.thy
  "[| a: Vfrom(A,i);  b: Vfrom(A,i);  Limit(i);  Transset(A) |] ==> \
\  a*b : Vfrom(A,i)";
by (rtac ([aprem,bprem,limiti] MRS in_VLimit) 1);
by (REPEAT (ares_tac [exI, conjI, prod_in_Vfrom, transset,
                      limiti RS Limit_has_succ] 1));
qed "prod_in_VLimit";

(** Disjoint sums, aka Quine ordered pairs **)

goalw Univ.thy [sum_def]
    "!!A. [| a: Vfrom(A,j);  b: Vfrom(A,j);  Transset(A);  1:j |] ==> \
\         a+b : Vfrom(A, succ(succ(succ(j))))";
by (dtac Transset_Vfrom 1);
by (rtac subset_mem_Vfrom 1);
by (rewtac Transset_def);
by (fast_tac (!claset addIs [zero_in_Vfrom, Pair_in_Vfrom, 
                           i_subset_Vfrom RS subsetD]) 1);
qed "sum_in_Vfrom";

val [aprem,bprem,limiti,transset] = goal Univ.thy
  "[| a: Vfrom(A,i);  b: Vfrom(A,i);  Limit(i);  Transset(A) |] ==> \
\  a+b : Vfrom(A,i)";
by (rtac ([aprem,bprem,limiti] MRS in_VLimit) 1);
by (REPEAT (ares_tac [exI, conjI, sum_in_Vfrom, transset,
                      limiti RS Limit_has_succ] 1));
qed "sum_in_VLimit";

(** function space! **)

goalw Univ.thy [Pi_def]
    "!!A. [| a: Vfrom(A,j);  b: Vfrom(A,j);  Transset(A) |] ==> \
\         a->b : Vfrom(A, succ(succ(succ(succ(j)))))";
by (dtac Transset_Vfrom 1);
by (rtac subset_mem_Vfrom 1);
by (rtac (Collect_subset RS subset_trans) 1);
by (stac Vfrom 1);
by (rtac (subset_trans RS subset_trans) 1);
by (rtac Un_upper2 3);
by (rtac (succI1 RS UN_upper) 2);
by (rtac Pow_mono 1);
by (rewtac Transset_def);
by (fast_tac (!claset addIs [Pair_in_Vfrom]) 1);
qed "fun_in_Vfrom";

val [aprem,bprem,limiti,transset] = goal Univ.thy
  "[| a: Vfrom(A,i);  b: Vfrom(A,i);  Limit(i);  Transset(A) |] ==> \
\  a->b : Vfrom(A,i)";
by (rtac ([aprem,bprem,limiti] MRS in_VLimit) 1);
by (REPEAT (ares_tac [exI, conjI, fun_in_Vfrom, transset,
                      limiti RS Limit_has_succ] 1));
qed "fun_in_VLimit";


(*** The set Vset(i) ***)

goal Univ.thy "Vset(i) = (UN j:i. Pow(Vset(j)))";
by (stac Vfrom 1);
by (Fast_tac 1);
qed "Vset";

val Vset_succ = Transset_0 RS Transset_Vfrom_succ;

val Transset_Vset = Transset_0 RS Transset_Vfrom;

(** Characterisation of the elements of Vset(i) **)

val [ordi] = goal Univ.thy "Ord(i) ==> ALL b. b : Vset(i) --> rank(b) < i";
by (rtac (ordi RS trans_induct) 1);
by (stac Vset 1);
by (safe_tac (!claset));
by (stac rank 1);
by (rtac UN_succ_least_lt 1);
by (Fast_tac 2);
by (REPEAT (ares_tac [ltI] 1));
qed "Vset_rank_imp1";

(*  [| Ord(i); x : Vset(i) |] ==> rank(x) < i  *)
bind_thm ("VsetD", (Vset_rank_imp1 RS spec RS mp));

val [ordi] = goal Univ.thy "Ord(i) ==> ALL b. rank(b) : i --> b : Vset(i)";
by (rtac (ordi RS trans_induct) 1);
by (rtac allI 1);
by (stac Vset 1);
by (fast_tac (!claset addSIs [rank_lt RS ltD]) 1);
qed "Vset_rank_imp2";

goal Univ.thy "!!x i. rank(x)<i ==> x : Vset(i)";
by (etac ltE 1);
by (etac (Vset_rank_imp2 RS spec RS mp) 1);
by (assume_tac 1);
qed "VsetI";

goal Univ.thy "!!i. Ord(i) ==> b : Vset(i) <-> rank(b) < i";
by (rtac iffI 1);
by (REPEAT (eresolve_tac [asm_rl, VsetD, VsetI] 1));
qed "Vset_Ord_rank_iff";

goal Univ.thy "b : Vset(a) <-> rank(b) < rank(a)";
by (rtac (Vfrom_rank_eq RS subst) 1);
by (rtac (Ord_rank RS Vset_Ord_rank_iff) 1);
qed "Vset_rank_iff";

goal Univ.thy "!!i. Ord(i) ==> rank(Vset(i)) = i";
by (stac rank 1);
by (rtac equalityI 1);
by (safe_tac (!claset));
by (EVERY' [rtac UN_I, 
            etac (i_subset_Vfrom RS subsetD),
            etac (Ord_in_Ord RS rank_of_Ord RS ssubst),
            assume_tac,
            rtac succI1] 3);
by (REPEAT (eresolve_tac [asm_rl, VsetD RS ltD, Ord_trans] 1));
qed "rank_Vset";

(** Lemmas for reasoning about sets in terms of their elements' ranks **)

goal Univ.thy "a <= Vset(rank(a))";
by (rtac subsetI 1);
by (etac (rank_lt RS VsetI) 1);
qed "arg_subset_Vset_rank";

val [iprem] = goal Univ.thy
    "[| !!i. Ord(i) ==> a Int Vset(i) <= b |] ==> a <= b";
by (rtac ([subset_refl, arg_subset_Vset_rank] MRS 
          Int_greatest RS subset_trans) 1);
by (rtac (Ord_rank RS iprem) 1);
qed "Int_Vset_subset";

(** Set up an environment for simplification **)

val rank_rls = [rank_Inl, rank_Inr, rank_pair1, rank_pair2];
val rank_trans_rls = rank_rls @ (rank_rls RLN (2, [lt_trans]));

val rank_ss = !simpset addsimps [VsetI] addsimps rank_trans_rls;

(** Recursion over Vset levels! **)

(*NOT SUITABLE FOR REWRITING: recursive!*)
goalw Univ.thy [Vrec_def] "Vrec(a,H) = H(a, lam x:Vset(rank(a)). Vrec(x,H))";
by (stac transrec 1);
by (simp_tac (!simpset addsimps [Ord_rank, Ord_succ, VsetD RS ltD RS beta, 
                              VsetI RS beta, le_refl]) 1);
qed "Vrec";

(*This form avoids giant explosions in proofs.  NOTE USE OF == *)
val rew::prems = goal Univ.thy
    "[| !!x. h(x)==Vrec(x,H) |] ==> \
\    h(a) = H(a, lam x: Vset(rank(a)). h(x))";
by (rewtac rew);
by (rtac Vrec 1);
qed "def_Vrec";


(*** univ(A) ***)

goalw Univ.thy [univ_def] "!!A B. A<=B ==> univ(A) <= univ(B)";
by (etac Vfrom_mono 1);
by (rtac subset_refl 1);
qed "univ_mono";

goalw Univ.thy [univ_def] "!!A. Transset(A) ==> Transset(univ(A))";
by (etac Transset_Vfrom 1);
qed "Transset_univ";

(** univ(A) as a limit **)

goalw Univ.thy [univ_def] "univ(A) = (UN i:nat. Vfrom(A,i))";
by (rtac (Limit_nat RS Limit_Vfrom_eq) 1);
qed "univ_eq_UN";

goal Univ.thy "!!c. c <= univ(A) ==> c = (UN i:nat. c Int Vfrom(A,i))";
by (rtac (subset_UN_iff_eq RS iffD1) 1);
by (etac (univ_eq_UN RS subst) 1);
qed "subset_univ_eq_Int";

val [aprem, iprem] = goal Univ.thy
    "[| a <= univ(X);                           \
\       !!i. i:nat ==> a Int Vfrom(X,i) <= b    \
\    |] ==> a <= b";
by (stac (aprem RS subset_univ_eq_Int) 1);
by (rtac UN_least 1);
by (etac iprem 1);
qed "univ_Int_Vfrom_subset";

val prems = goal Univ.thy
    "[| a <= univ(X);   b <= univ(X);   \
\       !!i. i:nat ==> a Int Vfrom(X,i) = b Int Vfrom(X,i) \
\    |] ==> a = b";
by (rtac equalityI 1);
by (ALLGOALS
    (resolve_tac (prems RL [univ_Int_Vfrom_subset]) THEN'
     eresolve_tac (prems RL [equalityD1,equalityD2] RL [subset_trans]) THEN'
     rtac Int_lower1));
qed "univ_Int_Vfrom_eq";

(** Closure properties **)

goalw Univ.thy [univ_def] "0 : univ(A)";
by (rtac (nat_0I RS zero_in_Vfrom) 1);
qed "zero_in_univ";

goalw Univ.thy [univ_def] "A <= univ(A)";
by (rtac A_subset_Vfrom 1);
qed "A_subset_univ";

val A_into_univ = A_subset_univ RS subsetD;

(** Closure under unordered and ordered pairs **)

goalw Univ.thy [univ_def] "!!A a. a: univ(A) ==> {a} : univ(A)";
by (REPEAT (ares_tac [singleton_in_VLimit, Limit_nat] 1));
qed "singleton_in_univ";

goalw Univ.thy [univ_def] 
    "!!A a. [| a: univ(A);  b: univ(A) |] ==> {a,b} : univ(A)";
by (REPEAT (ares_tac [doubleton_in_VLimit, Limit_nat] 1));
qed "doubleton_in_univ";

goalw Univ.thy [univ_def]
    "!!A a. [| a: univ(A);  b: univ(A) |] ==> <a,b> : univ(A)";
by (REPEAT (ares_tac [Pair_in_VLimit, Limit_nat] 1));
qed "Pair_in_univ";

goalw Univ.thy [univ_def] "univ(A)*univ(A) <= univ(A)";
by (rtac (Limit_nat RS product_VLimit) 1);
qed "product_univ";


(** The natural numbers **)

goalw Univ.thy [univ_def] "nat <= univ(A)";
by (rtac i_subset_Vfrom 1);
qed "nat_subset_univ";

(* n:nat ==> n:univ(A) *)
bind_thm ("nat_into_univ", (nat_subset_univ RS subsetD));

(** instances for 1 and 2 **)

goalw Univ.thy [univ_def] "1 : univ(A)";
by (rtac (Limit_nat RS one_in_VLimit) 1);
qed "one_in_univ";

(*unused!*)
goal Univ.thy "2 : univ(A)";
by (REPEAT (ares_tac [nat_into_univ, nat_0I, nat_succI] 1));
qed "two_in_univ";

goalw Univ.thy [bool_def] "bool <= univ(A)";
by (fast_tac (!claset addSIs [zero_in_univ,one_in_univ]) 1);
qed "bool_subset_univ";

bind_thm ("bool_into_univ", (bool_subset_univ RS subsetD));


(** Closure under disjoint union **)

goalw Univ.thy [univ_def] "!!A a. a: univ(A) ==> Inl(a) : univ(A)";
by (etac (Limit_nat RSN (2,Inl_in_VLimit)) 1);
qed "Inl_in_univ";

goalw Univ.thy [univ_def] "!!A b. b: univ(A) ==> Inr(b) : univ(A)";
by (etac (Limit_nat RSN (2,Inr_in_VLimit)) 1);
qed "Inr_in_univ";

goalw Univ.thy [univ_def] "univ(C)+univ(C) <= univ(C)";
by (rtac (Limit_nat RS sum_VLimit) 1);
qed "sum_univ";

bind_thm ("sum_subset_univ", [sum_mono, sum_univ] MRS subset_trans);


(** Closure under binary union -- use Un_least **)
(** Closure under Collect -- use  (Collect_subset RS subset_trans)  **)
(** Closure under RepFun -- use   RepFun_subset  **)


(*** Finite Branching Closure Properties ***)

(** Closure under finite powerset **)

goal Univ.thy
   "!!i. [| b: Fin(Vfrom(A,i));  Limit(i) |] ==> EX j. b <= Vfrom(A,j) & j<i";
by (etac Fin_induct 1);
by (fast_tac (!claset addSDs [Limit_has_0]) 1);
by (safe_tac (!claset));
by (etac Limit_VfromE 1);
by (assume_tac 1);
by (res_inst_tac [("x", "xa Un j")] exI 1);
by (best_tac (!claset addIs [subset_refl RS Vfrom_mono RS subsetD, 
                           Un_least_lt]) 1);
val Fin_Vfrom_lemma = result();

goal Univ.thy "!!i. Limit(i) ==> Fin(Vfrom(A,i)) <= Vfrom(A,i)";
by (rtac subsetI 1);
by (dtac Fin_Vfrom_lemma 1);
by (safe_tac (!claset));
by (resolve_tac [Vfrom RS ssubst] 1);
by (fast_tac (!claset addSDs [ltD]) 1);
val Fin_VLimit = result();

bind_thm ("Fin_subset_VLimit", [Fin_mono, Fin_VLimit] MRS subset_trans);

goalw Univ.thy [univ_def] "Fin(univ(A)) <= univ(A)";
by (rtac (Limit_nat RS Fin_VLimit) 1);
val Fin_univ = result();

(** Closure under finite powers (functions from a fixed natural number) **)

goal Univ.thy
    "!!i. [| n: nat;  Limit(i) |] ==> n -> Vfrom(A,i) <= Vfrom(A,i)";
by (eresolve_tac [nat_fun_subset_Fin RS subset_trans] 1);
by (REPEAT (ares_tac [Fin_subset_VLimit, Sigma_subset_VLimit,
                      nat_subset_VLimit, subset_refl] 1));
val nat_fun_VLimit = result();

bind_thm ("nat_fun_subset_VLimit", [Pi_mono, nat_fun_VLimit] MRS subset_trans);

goalw Univ.thy [univ_def] "!!i. n: nat ==> n -> univ(A) <= univ(A)";
by (etac (Limit_nat RSN (2,nat_fun_VLimit)) 1);
val nat_fun_univ = result();


(** Closure under finite function space **)

(*General but seldom-used version; normally the domain is fixed*)
goal Univ.thy
    "!!i. Limit(i) ==> Vfrom(A,i) -||> Vfrom(A,i) <= Vfrom(A,i)";
by (resolve_tac [FiniteFun.dom_subset RS subset_trans] 1);
by (REPEAT (ares_tac [Fin_subset_VLimit, Sigma_subset_VLimit, subset_refl] 1));
val FiniteFun_VLimit1 = result();

goalw Univ.thy [univ_def] "univ(A) -||> univ(A) <= univ(A)";
by (rtac (Limit_nat RS FiniteFun_VLimit1) 1);
val FiniteFun_univ1 = result();

(*Version for a fixed domain*)
goal Univ.thy
   "!!i.  [| W <= Vfrom(A,i); Limit(i) |] ==> W -||> Vfrom(A,i) <= Vfrom(A,i)";
by (eresolve_tac [subset_refl RSN (2, FiniteFun_mono) RS subset_trans] 1);
by (etac FiniteFun_VLimit1 1);
val FiniteFun_VLimit = result();

goalw Univ.thy [univ_def]
    "!!W. W <= univ(A) ==> W -||> univ(A) <= univ(A)";
by (etac (Limit_nat RSN (2, FiniteFun_VLimit)) 1);
val FiniteFun_univ = result();

goal Univ.thy
    "!!W. [| f: W -||> univ(A);  W <= univ(A) |] ==> f : univ(A)";
by (eresolve_tac [FiniteFun_univ RS subsetD] 1);
by (assume_tac 1);
val FiniteFun_in_univ = result();

(*Remove <= from the rule above*)
val FiniteFun_in_univ' = subsetI RSN (2, FiniteFun_in_univ);


