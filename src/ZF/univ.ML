(*  Title: 	ZF/univ
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The cumulative hierarchy and a small universe for recursive types
*)

open Univ;

(*NOT SUITABLE FOR REWRITING -- RECURSIVE!*)
goal Univ.thy "Vfrom(A,i) = A Un (UN j:i. Pow(Vfrom(A,j)))";
by (rtac (Vfrom_def RS def_transrec RS ssubst) 1);
by (simp_tac ZF_ss 1);
val Vfrom = result();

(** Monotonicity **)

goal Univ.thy "!!A B. A<=B ==> ALL j. i<=j --> Vfrom(A,i) <= Vfrom(B,j)";
by (eps_ind_tac "i" 1);
by (rtac (impI RS allI) 1);
by (rtac (Vfrom RS ssubst) 1);
by (rtac (Vfrom RS ssubst) 1);
by (etac Un_mono 1);
by (rtac UN_mono 1);
by (assume_tac 1);
by (rtac Pow_mono 1);
by (etac (bspec RS spec RS mp) 1);
by (assume_tac 1);
by (rtac subset_refl 1);
val Vfrom_mono_lemma = result();

(*  [| A<=B; i<=x |] ==> Vfrom(A,i) <= Vfrom(B,x)  *)
val Vfrom_mono = standard (Vfrom_mono_lemma RS spec RS mp);


(** A fundamental equality: Vfrom does not require ordinals! **)

goal Univ.thy "Vfrom(A,x) <= Vfrom(A,rank(x))";
by (eps_ind_tac "x" 1);
by (rtac (Vfrom RS ssubst) 1);
by (rtac (Vfrom RS ssubst) 1);
by (fast_tac (ZF_cs addSIs [rank_lt]) 1);
val Vfrom_rank_subset1 = result();

goal Univ.thy "Vfrom(A,rank(x)) <= Vfrom(A,x)";
by (eps_ind_tac "x" 1);
by (rtac (Vfrom RS ssubst) 1);
by (rtac (Vfrom RS ssubst) 1);
br (subset_refl RS Un_mono) 1;
br UN_least 1;
by (etac (rank_implies_mem RS bexE) 1);
br subset_trans 1;
be UN_upper 2;
by (etac (subset_refl RS Vfrom_mono RS subset_trans RS Pow_mono) 1);
by (etac bspec 1);
by (assume_tac 1);
val Vfrom_rank_subset2 = result();

goal Univ.thy "Vfrom(A,rank(x)) = Vfrom(A,x)";
by (rtac equalityI 1);
by (rtac Vfrom_rank_subset2 1);
by (rtac Vfrom_rank_subset1 1);
val Vfrom_rank_eq = result();


(*** Basic closure properties ***)

goal Univ.thy "!!x y. y:x ==> 0 : Vfrom(A,x)";
by (rtac (Vfrom RS ssubst) 1);
by (fast_tac ZF_cs 1);
val zero_in_Vfrom = result();

goal Univ.thy "i <= Vfrom(A,i)";
by (eps_ind_tac "i" 1);
by (rtac (Vfrom RS ssubst) 1);
by (fast_tac ZF_cs 1);
val i_subset_Vfrom = result();

goal Univ.thy "A <= Vfrom(A,i)";
by (rtac (Vfrom RS ssubst) 1);
by (rtac Un_upper1 1);
val A_subset_Vfrom = result();

goal Univ.thy "!!A a i. a <= Vfrom(A,i) ==> a: Vfrom(A,succ(i))";
by (rtac (Vfrom RS ssubst) 1);
by (fast_tac ZF_cs 1);
val subset_mem_Vfrom = result();

(** Finite sets and ordered pairs **)

goal Univ.thy "!!a. a: Vfrom(A,i) ==> {a} : Vfrom(A,succ(i))";
by (rtac subset_mem_Vfrom 1);
by (safe_tac ZF_cs);
val singleton_in_Vfrom = result();

goal Univ.thy
    "!!A. [| a: Vfrom(A,i);  b: Vfrom(A,i) |] ==> {a,b} : Vfrom(A,succ(i))";
by (rtac subset_mem_Vfrom 1);
by (safe_tac ZF_cs);
val doubleton_in_Vfrom = result();

goalw Univ.thy [Pair_def]
    "!!A. [| a: Vfrom(A,i);  b: Vfrom(A,i) |] ==> \
\         <a,b> : Vfrom(A,succ(succ(i)))";
by (REPEAT (ares_tac [doubleton_in_Vfrom] 1));
val Pair_in_Vfrom = result();

val [prem] = goal Univ.thy
    "a<=Vfrom(A,i) ==> succ(a) : Vfrom(A,succ(succ(i)))";
by (REPEAT (resolve_tac [subset_mem_Vfrom, succ_subsetI] 1));
by (rtac (Vfrom_mono RSN (2,subset_trans)) 2);
by (REPEAT (resolve_tac [prem, subset_refl, subset_succI] 1));
val succ_in_Vfrom = result();

(*** 0, successor and limit equations fof Vfrom ***)

goal Univ.thy "Vfrom(A,0) = A";
by (rtac (Vfrom RS ssubst) 1);
by (fast_tac eq_cs 1);
val Vfrom_0 = result();

goal Univ.thy "!!i. Ord(i) ==> Vfrom(A,succ(i)) = A Un Pow(Vfrom(A,i))";
by (rtac (Vfrom RS trans) 1);
by (rtac (succI1 RS RepFunI RS Union_upper RSN
	      (2, equalityI RS subst_context)) 1);
by (rtac UN_least 1);
by (rtac (subset_refl RS Vfrom_mono RS Pow_mono) 1);
by (etac member_succD 1);
by (assume_tac 1);
val Vfrom_succ_lemma = result();

goal Univ.thy "Vfrom(A,succ(i)) = A Un Pow(Vfrom(A,i))";
by (res_inst_tac [("x1", "succ(i)")] (Vfrom_rank_eq RS subst) 1);
by (res_inst_tac [("x1", "i")] (Vfrom_rank_eq RS subst) 1);
by (rtac (rank_succ RS ssubst) 1);
by (rtac (Ord_rank RS Vfrom_succ_lemma) 1);
val Vfrom_succ = result();

(*The premise distinguishes this from Vfrom(A,0);  allowing X=0 forces
  the conclusion to be Vfrom(A,Union(X)) = A Un (UN y:X. Vfrom(A,y)) *)
val [prem] = goal Univ.thy "y:X ==> Vfrom(A,Union(X)) = (UN y:X. Vfrom(A,y))";
by (rtac (Vfrom RS ssubst) 1);
by (rtac equalityI 1);
(*first inclusion*)
by (rtac Un_least 1);
br (A_subset_Vfrom RS subset_trans) 1;
br (prem RS UN_upper) 1;
br UN_least 1;
be UnionE 1;
br subset_trans 1;
be UN_upper 2;
by (rtac (Vfrom RS ssubst) 1);
be ([UN_upper, Un_upper2] MRS subset_trans) 1;
(*opposite inclusion*)
br UN_least 1;
by (rtac (Vfrom RS ssubst) 1);
by (fast_tac ZF_cs 1);
val Vfrom_Union = result();

(*** Limit ordinals -- general properties ***)

goalw Univ.thy [Limit_def] "!!i. Limit(i) ==> Union(i) = i";
by (fast_tac (eq_cs addEs [Ord_trans]) 1);
val Limit_Union_eq = result();

goalw Univ.thy [Limit_def] "!!i. Limit(i) ==> Ord(i)";
by (etac conjunct1 1);
val Limit_is_Ord = result();

goalw Univ.thy [Limit_def] "!!i. Limit(i) ==> 0 : i";
by (fast_tac ZF_cs 1);
val Limit_has_0 = result();

goalw Univ.thy [Limit_def] "!!i. [| Limit(i);  j:i |] ==> succ(j) : i";
by (fast_tac ZF_cs 1);
val Limit_has_succ = result();

goalw Univ.thy [Limit_def] "Limit(nat)";
by (REPEAT (ares_tac [conjI, ballI, nat_0I, nat_succI, Ord_nat] 1));
val Limit_nat = result();

goalw Univ.thy [Limit_def]
    "!!i. [| Ord(i);  0:i;  ALL y. ~ succ(y)=i |] ==> Limit(i)";
by (safe_tac subset_cs);
br Ord_member 1;
by (REPEAT_FIRST (eresolve_tac [asm_rl, Ord_in_Ord RS Ord_succ]
          ORELSE' dresolve_tac [Ord_succ_subsetI]));
by (fast_tac (subset_cs addSIs [equalityI]) 1);
val non_succ_LimitI = result();

goal Univ.thy "!!i. Ord(i) ==> i=0 | (EX j. i=succ(j)) | Limit(i)";
by (fast_tac (ZF_cs addSIs [non_succ_LimitI, Ord_0_member_iff RS iffD2]) 1);
val Ord_cases_lemma = result();

val major::prems = goal Univ.thy
    "[| Ord(i);			\
\       i=0            ==> P;	\
\       !!j. i=succ(j) ==> P;	\
\       Limit(i)       ==> P	\
\    |] ==> P";
by (cut_facts_tac [major RS Ord_cases_lemma] 1);
by (REPEAT (eresolve_tac (prems@[disjE, exE]) 1));
val Ord_cases = result();


(*** Vfrom applied to Limit ordinals ***)

(*NB. limit ordinals are non-empty;
                        Vfrom(A,0) = A = A Un (UN y:0. Vfrom(A,y)) *)
val [limiti] = goal Univ.thy
    "Limit(i) ==> Vfrom(A,i) = (UN y:i. Vfrom(A,y))";
by (rtac (limiti RS Limit_has_0 RS Vfrom_Union RS subst) 1);
by (rtac (limiti RS Limit_Union_eq RS ssubst) 1);
by (rtac refl 1);
val Limit_Vfrom_eq = result();

val Limit_VfromE = standard (Limit_Vfrom_eq RS equalityD1 RS subsetD RS UN_E);

val [major,limiti] = goal Univ.thy
    "[| a: Vfrom(A,i);  Limit(i) |] ==> {a} : Vfrom(A,i)";
by (rtac (limiti RS Limit_VfromE) 1);
by (rtac major 1);
by (rtac (limiti RS Limit_Vfrom_eq RS ssubst) 1);
by (rtac UN_I 1);
by (etac singleton_in_Vfrom 2);
by (etac (limiti RS Limit_has_succ) 1);
val singleton_in_Vfrom_limit = result();

val Vfrom_UnI1 = Un_upper1 RS (subset_refl RS Vfrom_mono RS subsetD)
and Vfrom_UnI2 = Un_upper2 RS (subset_refl RS Vfrom_mono RS subsetD);

(*Hard work is finding a single j:i such that {a,b}<=Vfrom(A,j)*)
val [aprem,bprem,limiti] = goal Univ.thy
    "[| a: Vfrom(A,i);  b: Vfrom(A,i);  Limit(i) |] ==> \
\    {a,b} : Vfrom(A,i)";
by (rtac (aprem RS (limiti RS Limit_VfromE)) 1);
by (rtac (bprem RS (limiti RS Limit_VfromE)) 1);
by (rtac (limiti RS Limit_Vfrom_eq RS ssubst) 1);
by (rtac UN_I 1);
by (rtac doubleton_in_Vfrom 2);
by (etac Vfrom_UnI1 2);
by (etac Vfrom_UnI2 2);
by (REPEAT (ares_tac[limiti, Limit_has_succ, Ord_member_UnI, Limit_is_Ord] 1));
val doubleton_in_Vfrom_limit = result();

val [aprem,bprem,limiti] = goal Univ.thy
    "[| a: Vfrom(A,i);  b: Vfrom(A,i);  Limit(i) |] ==> \
\    <a,b> : Vfrom(A,i)";
(*Infer that a, b occur at ordinals x,xa < i.*)
by (rtac (aprem RS (limiti RS Limit_VfromE)) 1);
by (rtac (bprem RS (limiti RS Limit_VfromE)) 1);
by (rtac (limiti RS Limit_Vfrom_eq RS ssubst) 1);
by (rtac UN_I 1);
by (rtac Pair_in_Vfrom 2);
(*Infer that succ(succ(x Un xa)) < i *)
by (etac Vfrom_UnI1 2);
by (etac Vfrom_UnI2 2);
by (REPEAT (ares_tac[limiti, Limit_has_succ, Ord_member_UnI, Limit_is_Ord] 1));
val Pair_in_Vfrom_limit = result();


(*** Properties assuming Transset(A) ***)

goal Univ.thy "!!i A. Transset(A) ==> Transset(Vfrom(A,i))";
by (eps_ind_tac "i" 1);
by (rtac (Vfrom RS ssubst) 1);
by (fast_tac (ZF_cs addSIs [Transset_Union_family, Transset_Un,
			    Transset_Pow]) 1);
val Transset_Vfrom = result();

goal Univ.thy "!!A i. Transset(A) ==> Vfrom(A, succ(i)) = Pow(Vfrom(A,i))";
by (rtac (Vfrom_succ RS trans) 1);
br (Un_upper2 RSN (2,equalityI)) 1;;
br (subset_refl RSN (2,Un_least)) 1;;
br (A_subset_Vfrom RS subset_trans) 1;
be (Transset_Vfrom RS (Transset_iff_Pow RS iffD1)) 1;
val Transset_Vfrom_succ = result();

goalw Ord.thy [Pair_def,Transset_def]
    "!!C. [| <a,b> <= C; Transset(C) |] ==> a: C & b: C";
by (fast_tac ZF_cs 1);
val Transset_Pair_subset = result();

goal Univ.thy
    "!!a b.[| <a,b> <= Vfrom(A,i);  Transset(A);  Limit(i) |] ==> \
\          <a,b> : Vfrom(A,i)";
be (Transset_Pair_subset RS conjE) 1;
be Transset_Vfrom 1;
by (REPEAT (ares_tac [Pair_in_Vfrom_limit] 1));
val Transset_Pair_subset_Vfrom_limit = result();


(*** Closure under product/sum applied to elements -- thus Vfrom(A,i) 
     is a model of simple type theory provided A is a transitive set
     and i is a limit ordinal
***)

(*There are three nearly identical proofs below -- needs a general theorem
  for proving  ...a...b : Vfrom(A,i) where i is a limit ordinal*)

(** products **)

goal Univ.thy
    "!!A. [| a: Vfrom(A,i);  b: Vfrom(A,i);  Transset(A) |] ==> \
\         a*b : Vfrom(A, succ(succ(succ(i))))";
by (dtac Transset_Vfrom 1);
by (rtac subset_mem_Vfrom 1);
by (rewtac Transset_def);
by (fast_tac (ZF_cs addIs [Pair_in_Vfrom]) 1);
val prod_in_Vfrom = result();

val [aprem,bprem,limiti,transset] = goal Univ.thy
  "[| a: Vfrom(A,i);  b: Vfrom(A,i);  Limit(i);  Transset(A) |] ==> \
\  a*b : Vfrom(A,i)";
(*Infer that a, b occur at ordinals x,xa < i.*)
by (rtac (aprem RS (limiti RS Limit_VfromE)) 1);
by (rtac (bprem RS (limiti RS Limit_VfromE)) 1);
by (rtac (limiti RS Limit_Vfrom_eq RS ssubst) 1);
by (rtac UN_I 1);
by (rtac prod_in_Vfrom 2);
(*Infer that succ(succ(succ(x Un xa))) < i *)
by (etac (Vfrom_UnI1 RS Vfrom_UnI2) 2);
by (etac (Vfrom_UnI2 RS Vfrom_UnI2) 2);
by (REPEAT (ares_tac [limiti RS Limit_has_succ,
		      Ord_member_UnI, limiti RS Limit_is_Ord, transset] 1));
val prod_in_Vfrom_limit = result();

(** Disjoint sums, aka Quine ordered pairs **)

goalw Univ.thy [sum_def]
    "!!A. [| a: Vfrom(A,i);  b: Vfrom(A,i);  Transset(A);  1:i |] ==> \
\         a+b : Vfrom(A, succ(succ(succ(i))))";
by (dtac Transset_Vfrom 1);
by (rtac subset_mem_Vfrom 1);
by (rewtac Transset_def);
by (fast_tac (ZF_cs addIs [zero_in_Vfrom, Pair_in_Vfrom, 
			   i_subset_Vfrom RS subsetD]) 1);
val sum_in_Vfrom = result();

val [aprem,bprem,limiti,transset] = goal Univ.thy
  "[| a: Vfrom(A,i);  b: Vfrom(A,i);  Limit(i);  Transset(A) |] ==> \
\  a+b : Vfrom(A,i)";
(*Infer that a, b occur at ordinals x,xa < i.*)
by (rtac (aprem RS (limiti RS Limit_VfromE)) 1);
by (rtac (bprem RS (limiti RS Limit_VfromE)) 1);
by (rtac (limiti RS Limit_Vfrom_eq RS ssubst) 1);
by (rtac UN_I 1);
by (rtac (rewrite_rule [one_def] sum_in_Vfrom) 2);
by (rtac (succI1 RS UnI1) 5);
(*Infer that succ(succ(succ(x Un xa))) < i *)
by (etac (Vfrom_UnI1 RS Vfrom_UnI2) 2);
by (etac (Vfrom_UnI2 RS Vfrom_UnI2) 2);
by (REPEAT (ares_tac [limiti RS Limit_has_0, 
		      limiti RS Limit_has_succ,
		      Ord_member_UnI, limiti RS Limit_is_Ord, transset] 1));
val sum_in_Vfrom_limit = result();

(** function space! **)

goalw Univ.thy [Pi_def]
    "!!A. [| a: Vfrom(A,i);  b: Vfrom(A,i);  Transset(A) |] ==> \
\         a->b : Vfrom(A, succ(succ(succ(succ(i)))))";
by (dtac Transset_Vfrom 1);
by (rtac subset_mem_Vfrom 1);
by (rtac (Collect_subset RS subset_trans) 1);
by (rtac (Vfrom RS ssubst) 1);
by (rtac (subset_trans RS subset_trans) 1);
by (rtac Un_upper2 3);
by (rtac (succI1 RS UN_upper) 2);
by (rtac Pow_mono 1);
by (rewtac Transset_def);
by (fast_tac (ZF_cs addIs [Pair_in_Vfrom]) 1);
val fun_in_Vfrom = result();

val [aprem,bprem,limiti,transset] = goal Univ.thy
  "[| a: Vfrom(A,i);  b: Vfrom(A,i);  Limit(i);  Transset(A) |] ==> \
\  a->b : Vfrom(A,i)";
(*Infer that a, b occur at ordinals x,xa < i.*)
by (rtac (aprem RS (limiti RS Limit_VfromE)) 1);
by (rtac (bprem RS (limiti RS Limit_VfromE)) 1);
by (rtac (limiti RS Limit_Vfrom_eq RS ssubst) 1);
by (rtac UN_I 1);
by (rtac fun_in_Vfrom 2);
(*Infer that succ(succ(succ(x Un xa))) < i *)
by (etac (Vfrom_UnI1 RS Vfrom_UnI2) 2);
by (etac (Vfrom_UnI2 RS Vfrom_UnI2) 2);
by (REPEAT (ares_tac [limiti RS Limit_has_succ,
		      Ord_member_UnI, limiti RS Limit_is_Ord, transset] 1));
val fun_in_Vfrom_limit = result();


(*** The set Vset(i) ***)

goal Univ.thy "Vset(i) = (UN j:i. Pow(Vset(j)))";
by (rtac (Vfrom RS ssubst) 1);
by (fast_tac eq_cs 1);
val Vset = result();

val Vset_succ = Transset_0 RS Transset_Vfrom_succ;

val Transset_Vset = Transset_0 RS Transset_Vfrom;

(** Characterisation of the elements of Vset(i) **)

val [ordi] = goal Univ.thy "Ord(i) ==> ALL b. b : Vset(i) --> rank(b) : i";
by (rtac (ordi RS trans_induct) 1);
by (rtac (Vset RS ssubst) 1);
by (safe_tac ZF_cs);
by (rtac (rank RS ssubst) 1);
by (rtac sup_least2 1);
by (assume_tac 1);
by (assume_tac 1);
by (fast_tac ZF_cs 1);
val Vset_rank_imp1 = result();

(*  [| Ord(i); x : Vset(i) |] ==> rank(x) : i  *)
val Vset_D = standard (Vset_rank_imp1 RS spec RS mp);

val [ordi] = goal Univ.thy "Ord(i) ==> ALL b. rank(b) : i --> b : Vset(i)";
by (rtac (ordi RS trans_induct) 1);
by (rtac allI 1);
by (rtac (Vset RS ssubst) 1);
by (fast_tac (ZF_cs addSIs [rank_lt]) 1);
val Vset_rank_imp2 = result();

(*  [| Ord(i); rank(x) : i |] ==> x : Vset(i)  *)
val VsetI = standard (Vset_rank_imp2 RS spec RS mp);

val [ordi] = goal Univ.thy "Ord(i) ==> b : Vset(i) <-> rank(b) : i";
by (rtac iffI 1);
by (etac (ordi RS Vset_D) 1);
by (etac (ordi RS VsetI) 1);
val Vset_Ord_rank_iff = result();

goal Univ.thy "b : Vset(a) <-> rank(b) : rank(a)";
by (rtac (Vfrom_rank_eq RS subst) 1);
by (rtac (Ord_rank RS Vset_Ord_rank_iff) 1);
val Vset_rank_iff = result();

goal Univ.thy "!!i. Ord(i) ==> rank(Vset(i)) = i";
by (rtac (rank RS ssubst) 1);
by (rtac equalityI 1);
by (safe_tac ZF_cs);
by (EVERY' [rtac UN_I, 
	    etac (i_subset_Vfrom RS subsetD),
	    etac (Ord_in_Ord RS rank_of_Ord RS ssubst),
	    assume_tac,
	    rtac succI1] 3);
by (REPEAT (eresolve_tac [asm_rl,Vset_D,Ord_trans] 1));
val rank_Vset = result();

(** Lemmas for reasoning about sets in terms of their elements' ranks **)

(*  rank(x) : rank(a) ==> x : Vset(rank(a))  *)
val Vset_rankI = Ord_rank RS VsetI;

goal Univ.thy "a <= Vset(rank(a))";
br subsetI 1;
be (rank_lt RS Vset_rankI) 1;
val arg_subset_Vset_rank = result();

val [iprem] = goal Univ.thy
    "[| !!i. Ord(i) ==> a Int Vset(i) <= b |] ==> a <= b";
br ([subset_refl, arg_subset_Vset_rank] MRS Int_greatest RS subset_trans) 1;
br (Ord_rank RS iprem) 1;
val Int_Vset_subset = result();

(** Set up an environment for simplification **)

val rank_rls = [rank_Inl, rank_Inr, rank_pair1, rank_pair2];
val rank_trans_rls = rank_rls @ (rank_rls RLN (2, [rank_trans]));

val rank_ss = ZF_ss 
    addsimps [case_Inl, case_Inr, Vset_rankI]
    addsimps rank_trans_rls;

(** Recursion over Vset levels! **)

(*NOT SUITABLE FOR REWRITING: recursive!*)
goalw Univ.thy [Vrec_def] "Vrec(a,H) = H(a, lam x:Vset(rank(a)). Vrec(x,H))";
by (rtac (transrec RS ssubst) 1);
by (simp_tac (ZF_ss addsimps [Ord_rank, Ord_succ, Vset_D RS beta, 
			      VsetI RS beta]) 1);
val Vrec = result();

(*This form avoids giant explosions in proofs.  NOTE USE OF == *)
val rew::prems = goal Univ.thy
    "[| !!x. h(x)==Vrec(x,H) |] ==> \
\    h(a) = H(a, lam x: Vset(rank(a)). h(x))";
by (rewtac rew);
by (rtac Vrec 1);
val def_Vrec = result();


(*** univ(A) ***)

goalw Univ.thy [univ_def] "!!A B. A<=B ==> univ(A) <= univ(B)";
by (etac Vfrom_mono 1);
by (rtac subset_refl 1);
val univ_mono = result();

goalw Univ.thy [univ_def] "!!A. Transset(A) ==> Transset(univ(A))";
by (etac Transset_Vfrom 1);
val Transset_univ = result();

(** univ(A) as a limit **)

goalw Univ.thy [univ_def] "univ(A) = (UN i:nat. Vfrom(A,i))";
br (Limit_nat RS Limit_Vfrom_eq) 1;
val univ_eq_UN = result();

goal Univ.thy "!!c. c <= univ(A) ==> c = (UN i:nat. c Int Vfrom(A,i))";
br (subset_UN_iff_eq RS iffD1) 1;
be (univ_eq_UN RS subst) 1;
val subset_univ_eq_Int = result();

val [aprem, iprem] = goal Univ.thy
    "[| a <= univ(X);			 	\
\       !!i. i:nat ==> a Int Vfrom(X,i) <= b 	\
\    |] ==> a <= b";
br (aprem RS subset_univ_eq_Int RS ssubst) 1;
br UN_least 1;
be iprem 1;
val univ_Int_Vfrom_subset = result();

val prems = goal Univ.thy
    "[| a <= univ(X);   b <= univ(X);   \
\       !!i. i:nat ==> a Int Vfrom(X,i) = b Int Vfrom(X,i) \
\    |] ==> a = b";
br equalityI 1;
by (ALLGOALS
    (resolve_tac (prems RL [univ_Int_Vfrom_subset]) THEN'
     eresolve_tac (prems RL [equalityD1,equalityD2] RL [subset_trans]) THEN'
     rtac Int_lower1));
val univ_Int_Vfrom_eq = result();

(** Closure properties **)

goalw Univ.thy [univ_def] "0 : univ(A)";
by (rtac (nat_0I RS zero_in_Vfrom) 1);
val zero_in_univ = result();

goalw Univ.thy [univ_def] "A <= univ(A)";
by (rtac A_subset_Vfrom 1);
val A_subset_univ = result();

val A_into_univ = A_subset_univ RS subsetD;

(** Closure under unordered and ordered pairs **)

goalw Univ.thy [univ_def] "!!A a. a: univ(A) ==> {a} : univ(A)";
by (rtac singleton_in_Vfrom_limit 1);
by (REPEAT (ares_tac [Ord_nat,Limit_nat] 1));
val singleton_in_univ = result();

goalw Univ.thy [univ_def] 
    "!!A a. [| a: univ(A);  b: univ(A) |] ==> {a,b} : univ(A)";
by (rtac doubleton_in_Vfrom_limit 1);
by (REPEAT (ares_tac [Ord_nat,Limit_nat] 1));
val doubleton_in_univ = result();

goalw Univ.thy [univ_def]
    "!!A a. [| a: univ(A);  b: univ(A) |] ==> <a,b> : univ(A)";
by (rtac Pair_in_Vfrom_limit 1);
by (REPEAT (ares_tac [Ord_nat,Limit_nat] 1));
val Pair_in_univ = result();

goal Univ.thy "univ(A)*univ(A) <= univ(A)";
by (REPEAT (ares_tac [subsetI,Pair_in_univ] 1
     ORELSE eresolve_tac [SigmaE, ssubst] 1));
val product_univ = result();

val Sigma_subset_univ = standard
    (Sigma_mono RS (product_univ RSN (2,subset_trans)));

goalw Univ.thy [univ_def]
    "!!a b.[| <a,b> <= univ(A);  Transset(A) |] ==> <a,b> : univ(A)";
be Transset_Pair_subset_Vfrom_limit 1;
by (REPEAT (ares_tac [Ord_nat,Limit_nat] 1));
val Transset_Pair_subset_univ = result();


(** The natural numbers **)

goalw Univ.thy [univ_def] "nat <= univ(A)";
by (rtac i_subset_Vfrom 1);
val nat_subset_univ = result();

(* n:nat ==> n:univ(A) *)
val nat_into_univ = standard (nat_subset_univ RS subsetD);

(** instances for 1 and 2 **)

goalw Univ.thy [one_def] "1 : univ(A)";
by (REPEAT (ares_tac [nat_into_univ, nat_0I, nat_succI] 1));
val one_in_univ = result();

(*unused!*)
goal Univ.thy "succ(succ(0)) : univ(A)";
by (REPEAT (ares_tac [nat_into_univ, nat_0I, nat_succI] 1));
val two_in_univ = result();

goalw Univ.thy [bool_def] "bool <= univ(A)";
by (fast_tac (ZF_cs addSIs [zero_in_univ,one_in_univ]) 1);
val bool_subset_univ = result();

val bool_into_univ = standard (bool_subset_univ RS subsetD);


(** Closure under disjoint union **)

goalw Univ.thy [Inl_def] "!!A a. a: univ(A) ==> Inl(a) : univ(A)";
by (REPEAT (ares_tac [zero_in_univ,Pair_in_univ] 1));
val Inl_in_univ = result();

goalw Univ.thy [Inr_def] "!!A b. b: univ(A) ==> Inr(b) : univ(A)";
by (REPEAT (ares_tac [one_in_univ, Pair_in_univ] 1));
val Inr_in_univ = result();

goal Univ.thy "univ(C)+univ(C) <= univ(C)";
by (REPEAT (ares_tac [subsetI,Inl_in_univ,Inr_in_univ] 1
     ORELSE eresolve_tac [sumE, ssubst] 1));
val sum_univ = result();

val sum_subset_univ = standard
    (sum_mono RS (sum_univ RSN (2,subset_trans)));


(** Closure under binary union -- use Un_least **)
(** Closure under Collect -- use  (Collect_subset RS subset_trans)  **)
(** Closure under RepFun -- use   RepFun_subset  **)


