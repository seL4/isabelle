(*  Title: 	ZF/InfDatatype.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype Definitions involving ->
	Even infinite-branching!
*)

(*** Closure under finite powerset ***)

val Fin_Univ_thy = merge_theories (Univ.thy,Finite.thy);

goal Fin_Univ_thy
   "!!i. [| b: Fin(Vfrom(A,i));  Limit(i) |] ==> EX j. b <= Vfrom(A,j) & j<i";
by (eresolve_tac [Fin_induct] 1);
by (fast_tac (ZF_cs addSDs [Limit_has_0]) 1);
by (safe_tac ZF_cs);
by (eresolve_tac [Limit_VfromE] 1);
by (assume_tac 1);
by (res_inst_tac [("x", "xa Un j")] exI 1);
by (best_tac (ZF_cs addIs [subset_refl RS Vfrom_mono RS subsetD, 
			   Un_least_lt]) 1);
val Fin_Vfrom_lemma = result();

goal Fin_Univ_thy "!!i. Limit(i) ==> Fin(Vfrom(A,i)) <= Vfrom(A,i)";
by (rtac subsetI 1);
by (dresolve_tac [Fin_Vfrom_lemma] 1);
by (safe_tac ZF_cs);
by (resolve_tac [Vfrom RS ssubst] 1);
by (fast_tac (ZF_cs addSDs [ltD]) 1);
val Fin_VLimit = result();

val Fin_subset_VLimit = 
    [Fin_mono, Fin_VLimit] MRS subset_trans |> standard;

goal Fin_Univ_thy
    "!!i. [| n: nat;  Limit(i) |] ==> n -> Vfrom(A,i) <= Vfrom(A,i)";
by (eresolve_tac [nat_fun_subset_Fin RS subset_trans] 1);
by (REPEAT (ares_tac [Fin_subset_VLimit, Sigma_subset_VLimit,
		      nat_subset_VLimit, subset_refl] 1));
val nat_fun_VLimit = result();

val nat_fun_subset_VLimit = 
    [Pi_mono, nat_fun_VLimit] MRS subset_trans |> standard;


goalw Fin_Univ_thy [univ_def] "Fin(univ(A)) <= univ(A)";
by (rtac (Limit_nat RS Fin_VLimit) 1);
val Fin_univ = result();

val Fin_subset_univ = [Fin_mono, Fin_univ] MRS subset_trans |> standard;

goalw Fin_Univ_thy [univ_def] "!!i. n: nat ==> n -> univ(A) <= univ(A)";
by (etac (Limit_nat RSN (2,nat_fun_VLimit)) 1);
val nat_fun_univ = result();

val nat_fun_subset_univ = [Pi_mono, nat_fun_univ] MRS subset_trans |> standard;

goal Fin_Univ_thy
    "!!f. [| f: n -> B;  B <= univ(A);  n : nat |] ==> f : univ(A)";
by (REPEAT (ares_tac [nat_fun_subset_univ RS subsetD] 1));
val nat_fun_into_univ = result();


(*** Infinite branching ***)

val fun_Limit_VfromE = 
    [apply_funtype, InfCard_csucc RS InfCard_is_Limit] MRS Limit_VfromE
	|> standard;

goal InfDatatype.thy
    "!!K. [| f: I -> Vfrom(A,csucc(K));  |I| le K;  InfCard(K)	\
\         |] ==> EX j. f: I -> Vfrom(A,j) & j < csucc(K)";
by (res_inst_tac [("x", "UN x:I. LEAST i. f`x : Vfrom(A,i)")] exI 1);
by (resolve_tac [conjI] 1);
by (resolve_tac [ballI RSN (2,cardinal_UN_Ord_lt_csucc)] 2);
by (eresolve_tac [fun_Limit_VfromE] 3 THEN REPEAT_SOME assume_tac);
by (fast_tac (ZF_cs addEs [Least_le RS lt_trans1, ltE]) 2);
by (resolve_tac [Pi_type] 1);
by (rename_tac "k" 2);
by (eresolve_tac [fun_Limit_VfromE] 2 THEN REPEAT_SOME assume_tac);
by (subgoal_tac "f`k : Vfrom(A, LEAST i. f`k : Vfrom(A,i))" 1);
by (fast_tac (ZF_cs addEs [LeastI, ltE]) 2);
by (eresolve_tac [[subset_refl, UN_upper] MRS Vfrom_mono RS subsetD] 1);
by (assume_tac 1);
val fun_Vcsucc_lemma = result();

goal InfDatatype.thy
    "!!K. [| f: K -> Vfrom(A,csucc(K));  InfCard(K)	\
\         |] ==> EX j. f: K -> Vfrom(A,j) & j < csucc(K)";
by (res_inst_tac [("x", "UN k:K. LEAST i. f`k : Vfrom(A,i)")] exI 1);
by (resolve_tac [conjI] 1);
by (resolve_tac [ballI RSN (2,cardinal_UN_Ord_lt_csucc)] 2);
by (eresolve_tac [fun_Limit_VfromE] 3 THEN REPEAT_SOME assume_tac);
by (fast_tac (ZF_cs addEs [Least_le RS lt_trans1, ltE]) 2);
by (resolve_tac [Pi_type] 1);
by (rename_tac "k" 2);
by (eresolve_tac [fun_Limit_VfromE] 2 THEN REPEAT_SOME assume_tac);
by (subgoal_tac "f`k : Vfrom(A, LEAST i. f`k : Vfrom(A,i))" 1);
by (fast_tac (ZF_cs addEs [LeastI, ltE]) 2);
by (eresolve_tac [[subset_refl, UN_upper] MRS Vfrom_mono RS subsetD] 1);
by (assume_tac 1);
val fun_Vcsucc_lemma = result();

goal InfDatatype.thy
    "!!K. InfCard(K) ==> K -> Vfrom(A,csucc(K)) <= Vfrom(A,csucc(K))";
by (safe_tac (ZF_cs addSDs [fun_Vcsucc_lemma]));
by (resolve_tac [Vfrom RS ssubst] 1);
by (eresolve_tac [PiE] 1);
(*This level includes the function, and is below csucc(K)*)
by (res_inst_tac [("a1", "succ(succ(K Un j))")] (UN_I RS UnI2) 1);
by (eresolve_tac [subset_trans RS PowI] 2);
by (safe_tac (ZF_cs addSIs [Pair_in_Vfrom]));
by (fast_tac (ZF_cs addIs [i_subset_Vfrom RS subsetD]) 2);
by (eresolve_tac [[subset_refl, Un_upper2] MRS Vfrom_mono RS subsetD] 2);
by (REPEAT (ares_tac [ltD, InfCard_csucc, InfCard_is_Limit, 
		      Limit_has_succ, Un_least_lt] 1));
by (eresolve_tac [InfCard_is_Card RS Card_is_Ord RS lt_csucc] 1);
by (assume_tac 1);
val fun_Vcsucc = result();

goal InfDatatype.thy
    "!!K. [| f: K -> Vfrom(A, csucc(K));  InfCard(K) \
\         |] ==> f: Vfrom(A,csucc(K))";
by (REPEAT (ares_tac [fun_Vcsucc RS subsetD] 1));
val fun_in_Vcsucc = result();

val fun_subset_Vcsucc = 
	[Pi_mono, fun_Vcsucc] MRS subset_trans |> standard;

goal InfDatatype.thy
    "!!f. [| f: K -> B;  B <= Vfrom(A,csucc(K));  InfCard(K) \
\         |] ==> f: Vfrom(A,csucc(K))";
by (REPEAT (ares_tac [fun_subset_Vcsucc RS subsetD] 1));
val fun_into_Vcsucc = result();

val Limit_csucc = InfCard_csucc RS InfCard_is_Limit |> standard;

val Pair_in_Vcsucc = Limit_csucc RSN (3, Pair_in_VLimit) |> standard;
val Inl_in_Vcsucc  = Limit_csucc RSN (2, Inl_in_VLimit) |> standard;
val Inr_in_Vcsucc  = Limit_csucc RSN (2, Inr_in_VLimit) |> standard;
val zero_in_Vcsucc = Limit_csucc RS zero_in_VLimit |> standard;
val nat_into_Vcsucc = Limit_csucc RSN (2, nat_into_VLimit) |> standard;

(*For most K-branching datatypes with domain Vfrom(A, csucc(K)) *)
val inf_datatype_intrs =  
    [fun_in_Vcsucc, InfCard_nat, Pair_in_Vcsucc, 
     Inl_in_Vcsucc, Inr_in_Vcsucc, 
     zero_in_Vcsucc, A_into_Vfrom, nat_into_Vcsucc] @ datatype_intrs;

