(*  Title:      ZF/InfDatatype.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Infinite-branching datatype definitions
*)

bind_thm ("fun_Limit_VfromE",
   [apply_funtype, InfCard_csucc RS InfCard_is_Limit] MRS
     transfer (the_context ()) Limit_VfromE 
   |> standard);

Goal "[| f: D -> Vfrom(A,csucc(K));  |D| le K;  InfCard(K) |]  \
\     ==> EX j. f: D -> Vfrom(A,j) & j < csucc(K)";
by (res_inst_tac [("x", "UN d:D. LEAST i. f`d : Vfrom(A,i)")] exI 1);
by (rtac conjI 1);
by (rtac le_UN_Ord_lt_csucc 2);
by (rtac ballI 4  THEN
    etac fun_Limit_VfromE 4 THEN REPEAT_SOME assume_tac);
by (fast_tac (claset() addEs [Least_le RS lt_trans1, ltE]) 2);
by (rtac Pi_type 1);
by (rename_tac "d" 2);
by (etac fun_Limit_VfromE 2 THEN REPEAT_SOME assume_tac);
by (subgoal_tac "f`d : Vfrom(A, LEAST i. f`d : Vfrom(A,i))" 1);
by (fast_tac (claset() addEs [LeastI, ltE]) 2);
by (eresolve_tac [[subset_refl, UN_upper] MRS Vfrom_mono RS subsetD] 1);
by (assume_tac 1);
qed "fun_Vcsucc_lemma";

Goal "[| D <= Vfrom(A,csucc(K));  |D| le K;  InfCard(K) |]    \
\     ==> EX j. D <= Vfrom(A,j) & j < csucc(K)";
by (asm_full_simp_tac (simpset() addsimps [subset_iff_id,fun_Vcsucc_lemma]) 1);
qed "subset_Vcsucc";

(*Version for arbitrary index sets*)
Goal "[| |D| le K;  InfCard(K);  D <= Vfrom(A,csucc(K)) |] ==> \
\         D -> Vfrom(A,csucc(K)) <= Vfrom(A,csucc(K))";
by (safe_tac (claset() addSDs [fun_Vcsucc_lemma, subset_Vcsucc]));
by (resolve_tac [Vfrom RS ssubst] 1);
by (dtac fun_is_rel 1);
(*This level includes the function, and is below csucc(K)*)
by (res_inst_tac [("a1", "succ(succ(j Un ja))")] (UN_I RS UnI2) 1);
by (eresolve_tac [subset_trans RS PowI] 2);
by (fast_tac (claset() addIs [Pair_in_Vfrom, Vfrom_UnI1, Vfrom_UnI2]) 2);
by (REPEAT (ares_tac [ltD, InfCard_csucc, InfCard_is_Limit, 
                      Limit_has_succ, Un_least_lt] 1));
qed "fun_Vcsucc";

Goal "[| f: D -> Vfrom(A, csucc(K));  |D| le K;  InfCard(K);        \
\        D <= Vfrom(A,csucc(K)) |]                                  \
\      ==> f: Vfrom(A,csucc(K))";
by (REPEAT (ares_tac [fun_Vcsucc RS subsetD] 1));
qed "fun_in_Vcsucc";

(*Remove <= from the rule above*)
bind_thm ("fun_in_Vcsucc'", subsetI RSN (4, fun_in_Vcsucc));

(** Version where K itself is the index set **)

Goal "InfCard(K) ==> K -> Vfrom(A,csucc(K)) <= Vfrom(A,csucc(K))";
by (forward_tac [InfCard_is_Card RS Card_is_Ord] 1);
by (REPEAT (ares_tac [fun_Vcsucc, Ord_cardinal_le,
                      i_subset_Vfrom,
                      lt_csucc RS leI RS le_imp_subset RS subset_trans] 1));
qed "Card_fun_Vcsucc";

Goal "[| f: K -> Vfrom(A, csucc(K));  InfCard(K) \
\         |] ==> f: Vfrom(A,csucc(K))";
by (REPEAT (ares_tac [Card_fun_Vcsucc RS subsetD] 1));
qed "Card_fun_in_Vcsucc";

(*Proved explicitly, in theory InfDatatype, to allow the bind_thm calls below*)
Goal "InfCard(K) ==> Limit(csucc(K))";
by (etac (InfCard_csucc RS InfCard_is_Limit) 1);
qed "Limit_csucc";

bind_thm ("Pair_in_Vcsucc",  Limit_csucc RSN (3, Pair_in_VLimit));
bind_thm ("Inl_in_Vcsucc",   Limit_csucc RSN (2, Inl_in_VLimit));
bind_thm ("Inr_in_Vcsucc",   Limit_csucc RSN (2, Inr_in_VLimit));
bind_thm ("zero_in_Vcsucc",  Limit_csucc RS zero_in_VLimit);
bind_thm ("nat_into_Vcsucc", Limit_csucc RSN (2, nat_into_VLimit));

(*For handling Cardinals of the form  (nat Un |X|) *)

bind_thm ("InfCard_nat_Un_cardinal",
          [InfCard_nat, Card_cardinal] MRS InfCard_Un);

bind_thm ("le_nat_Un_cardinal",
          [Ord_nat, Card_cardinal RS Card_is_Ord] MRS Un_upper2_le);

bind_thm ("UN_upper_cardinal",
          UN_upper RS subset_imp_lepoll RS lepoll_imp_Card_le);

(*For most K-branching datatypes with domain Vfrom(A, csucc(K)) *)
bind_thms ("inf_datatype_intrs",
    [InfCard_nat, InfCard_nat_Un_cardinal,
     Pair_in_Vcsucc, Inl_in_Vcsucc, Inr_in_Vcsucc, 
     zero_in_Vcsucc, A_into_Vfrom, nat_into_Vcsucc,
     Card_fun_in_Vcsucc, fun_in_Vcsucc', UN_I] @ Data_Arg.intrs);
