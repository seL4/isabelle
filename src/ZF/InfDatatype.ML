(*  Title: 	ZF/InfDatatype.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Infinite-Branching Datatype Definitions
*)

val fun_Limit_VfromE = 
    [apply_funtype, InfCard_csucc RS InfCard_is_Limit] MRS Limit_VfromE
	|> standard;

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
val fun_Vfrom_csucc_lemma = result();

goal InfDatatype.thy
    "!!K. InfCard(K) ==> K -> Vfrom(A,csucc(K)) <= Vfrom(A,csucc(K))";
by (safe_tac (ZF_cs addSDs [fun_Vfrom_csucc_lemma]));
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
val fun_Vfrom_csucc = result();

goal InfDatatype.thy
    "!!K. [| f: K -> Vfrom(A, csucc(K));  InfCard(K) \
\         |] ==> f: Vfrom(A,csucc(K))";
by (REPEAT (ares_tac [fun_Vfrom_csucc RS subsetD] 1));
val fun_in_Vfrom_csucc = result();

val fun_subset_Vfrom_csucc = 
	[Pi_mono, fun_Vfrom_csucc] MRS subset_trans |> standard;

goal InfDatatype.thy
    "!!f. [| f: K -> B;  B <= Vfrom(A,csucc(K));  InfCard(K) \
\         |] ==> f: Vfrom(A,csucc(K))";
by (REPEAT (ares_tac [fun_subset_Vfrom_csucc RS subsetD] 1));
val fun_into_Vfrom_csucc = result();

val Limit_csucc = InfCard_csucc RS InfCard_is_Limit |> standard;

val Pair_in_Vfrom_csucc = Limit_csucc RSN (3, Pair_in_Vfrom_Limit) |> standard;
val Inl_in_Vfrom_csucc  = Limit_csucc RSN (2, Inl_in_Vfrom_Limit) |> standard;
val Inr_in_Vfrom_csucc  = Limit_csucc RSN (2, Inr_in_Vfrom_Limit) |> standard;
val zero_in_Vfrom_csucc = Limit_csucc RS zero_in_Vfrom_Limit |> standard;
val nat_into_Vfrom_csucc = Limit_csucc RSN (2, nat_into_Vfrom_Limit) 
			   |> standard;

(*For most K-branching datatypes with domain Vfrom(A, csucc(K)) *)
val inf_datatype_intrs =  
    [fun_in_Vfrom_csucc, InfCard_nat, Pair_in_Vfrom_csucc, 
     Inl_in_Vfrom_csucc, Inr_in_Vfrom_csucc, 
     zero_in_Vfrom_csucc, A_into_Vfrom, nat_into_Vfrom_csucc] @ datatype_intrs;

