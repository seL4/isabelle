(*  Title: 	ZF/InfDatatype.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype Definitions involving function space and/or infinite-branching
*)

(*** FINITE BRANCHING ***)

(** Closure under finite powerset **)

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

goalw Fin_Univ_thy [univ_def] "Fin(univ(A)) <= univ(A)";
by (rtac (Limit_nat RS Fin_VLimit) 1);
val Fin_univ = result();

(** Closure under finite powers (functions from a fixed natural number) **)

goal Fin_Univ_thy
    "!!i. [| n: nat;  Limit(i) |] ==> n -> Vfrom(A,i) <= Vfrom(A,i)";
by (eresolve_tac [nat_fun_subset_Fin RS subset_trans] 1);
by (REPEAT (ares_tac [Fin_subset_VLimit, Sigma_subset_VLimit,
		      nat_subset_VLimit, subset_refl] 1));
val nat_fun_VLimit = result();

val nat_fun_subset_VLimit = 
    [Pi_mono, nat_fun_VLimit] MRS subset_trans |> standard;

goalw Fin_Univ_thy [univ_def] "!!i. n: nat ==> n -> univ(A) <= univ(A)";
by (etac (Limit_nat RSN (2,nat_fun_VLimit)) 1);
val nat_fun_univ = result();


(** Closure under finite function space **)

(*General but seldom-used version; normally the domain is fixed*)
goal Fin_Univ_thy
    "!!i. Limit(i) ==> Vfrom(A,i) -||> Vfrom(A,i) <= Vfrom(A,i)";
by (resolve_tac [FiniteFun.dom_subset RS subset_trans] 1);
by (REPEAT (ares_tac [Fin_subset_VLimit, Sigma_subset_VLimit, subset_refl] 1));
val FiniteFun_VLimit1 = result();

goalw Fin_Univ_thy [univ_def] "univ(A) -||> univ(A) <= univ(A)";
by (rtac (Limit_nat RS FiniteFun_VLimit1) 1);
val FiniteFun_univ1 = result();

(*Version for a fixed domain*)
goal Fin_Univ_thy
   "!!i.  [| W <= Vfrom(A,i); Limit(i) |] ==> W -||> Vfrom(A,i) <= Vfrom(A,i)";
by (eresolve_tac [subset_refl RSN (2, FiniteFun_mono) RS subset_trans] 1);
by (eresolve_tac [FiniteFun_VLimit1] 1);
val FiniteFun_VLimit = result();

goalw Fin_Univ_thy [univ_def]
    "!!W. W <= univ(A) ==> W -||> univ(A) <= univ(A)";
by (etac (Limit_nat RSN (2, FiniteFun_VLimit)) 1);
val FiniteFun_univ = result();

goal Fin_Univ_thy
    "!!W. [| f: W -||> univ(A);  W <= univ(A) |] ==> f : univ(A)";
by (eresolve_tac [FiniteFun_univ RS subsetD] 1);
by (assume_tac 1);
val FiniteFun_in_univ = result();

(*Remove <= from the rule above*)
val FiniteFun_in_univ' = subsetI RSN (2, FiniteFun_in_univ);


(*** INFINITE BRANCHING ***)

val fun_Limit_VfromE = 
    [apply_funtype, InfCard_csucc RS InfCard_is_Limit] MRS Limit_VfromE
	|> standard;

goal InfDatatype.thy
    "!!K. [| f: W -> Vfrom(A,csucc(K));  |W| le K;  InfCard(K)	\
\         |] ==> EX j. f: W -> Vfrom(A,j) & j < csucc(K)";
by (res_inst_tac [("x", "UN w:W. LEAST i. f`w : Vfrom(A,i)")] exI 1);
by (resolve_tac [conjI] 1);
by (resolve_tac [le_UN_Ord_lt_csucc] 2);
by (rtac ballI 4  THEN
    eresolve_tac [fun_Limit_VfromE] 4 THEN REPEAT_SOME assume_tac);
by (fast_tac (ZF_cs addEs [Least_le RS lt_trans1, ltE]) 2);
by (resolve_tac [Pi_type] 1);
by (rename_tac "w" 2);
by (eresolve_tac [fun_Limit_VfromE] 2 THEN REPEAT_SOME assume_tac);
by (subgoal_tac "f`w : Vfrom(A, LEAST i. f`w : Vfrom(A,i))" 1);
by (fast_tac (ZF_cs addEs [LeastI, ltE]) 2);
by (eresolve_tac [[subset_refl, UN_upper] MRS Vfrom_mono RS subsetD] 1);
by (assume_tac 1);
val fun_Vcsucc_lemma = result();

goal InfDatatype.thy
    "!!K. [| W <= Vfrom(A,csucc(K));  |W| le K;  InfCard(K)	\
\         |] ==> EX j. W <= Vfrom(A,j) & j < csucc(K)";
by (asm_full_simp_tac (ZF_ss addsimps [subset_iff_id, fun_Vcsucc_lemma]) 1);
val subset_Vcsucc = result();

(*Version for arbitrary index sets*)
goal InfDatatype.thy
    "!!K. [| |W| le K;  InfCard(K);  W <= Vfrom(A,csucc(K)) |] ==> \
\         W -> Vfrom(A,csucc(K)) <= Vfrom(A,csucc(K))";
by (safe_tac (ZF_cs addSDs [fun_Vcsucc_lemma, subset_Vcsucc]));
by (resolve_tac [Vfrom RS ssubst] 1);
by (eresolve_tac [PiE] 1);
(*This level includes the function, and is below csucc(K)*)
by (res_inst_tac [("a1", "succ(succ(j Un ja))")] (UN_I RS UnI2) 1);
by (eresolve_tac [subset_trans RS PowI] 2);
by (fast_tac (ZF_cs addIs [Pair_in_Vfrom, Vfrom_UnI1, Vfrom_UnI2]) 2);
by (REPEAT (ares_tac [ltD, InfCard_csucc, InfCard_is_Limit, 
		      Limit_has_succ, Un_least_lt] 1));
val fun_Vcsucc = result();

goal InfDatatype.thy
    "!!K. [| f: W -> Vfrom(A, csucc(K));  |W| le K;  InfCard(K);	\
\            W <= Vfrom(A,csucc(K)) 					\
\         |] ==> f: Vfrom(A,csucc(K))";
by (REPEAT (ares_tac [fun_Vcsucc RS subsetD] 1));
val fun_in_Vcsucc = result();

(*Remove <= from the rule above*)
val fun_in_Vcsucc' = subsetI RSN (4, fun_in_Vcsucc);

(** Version where K itself is the index set **)

goal InfDatatype.thy
    "!!K. InfCard(K) ==> K -> Vfrom(A,csucc(K)) <= Vfrom(A,csucc(K))";
by (forward_tac [InfCard_is_Card RS Card_is_Ord] 1);
by (REPEAT (ares_tac [fun_Vcsucc, Ord_cardinal_le,
		      i_subset_Vfrom,
		      lt_csucc RS leI RS le_imp_subset RS subset_trans] 1));
val Card_fun_Vcsucc = result();

goal InfDatatype.thy
    "!!K. [| f: K -> Vfrom(A, csucc(K));  InfCard(K) \
\         |] ==> f: Vfrom(A,csucc(K))";
by (REPEAT (ares_tac [Card_fun_Vcsucc RS subsetD] 1));
val Card_fun_in_Vcsucc = result();

val Pair_in_Vcsucc = Limit_csucc RSN (3, Pair_in_VLimit) |> standard;
val Inl_in_Vcsucc  = Limit_csucc RSN (2, Inl_in_VLimit) |> standard;
val Inr_in_Vcsucc  = Limit_csucc RSN (2, Inr_in_VLimit) |> standard;
val zero_in_Vcsucc = Limit_csucc RS zero_in_VLimit |> standard;
val nat_into_Vcsucc = Limit_csucc RSN (2, nat_into_VLimit) |> standard;

(*For handling Cardinals of the form  (nat Un |X|) *)

val InfCard_nat_Un_cardinal = [InfCard_nat, Card_cardinal] MRS InfCard_Un
                              |> standard;

val le_nat_Un_cardinal = 
    [Ord_nat, Card_cardinal RS Card_is_Ord] MRS Un_upper2_le  |> standard;

val UN_upper_cardinal = UN_upper RS subset_imp_lepoll RS lepoll_imp_le 
                        |> standard;

(*For most K-branching datatypes with domain Vfrom(A, csucc(K)) *)
val inf_datatype_intrs =  
    [InfCard_nat, InfCard_nat_Un_cardinal,
     Pair_in_Vcsucc, Inl_in_Vcsucc, Inr_in_Vcsucc, 
     zero_in_Vcsucc, A_into_Vfrom, nat_into_Vcsucc,
     Card_fun_in_Vcsucc, fun_in_Vcsucc', UN_I] @ datatype_intrs;
