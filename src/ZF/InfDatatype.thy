(*  Title:      ZF/InfDatatype.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Infinite-branching datatype definitions
*)

theory InfDatatype = Datatype + Univ + Finite + Cardinal_AC:

lemmas fun_Limit_VfromE = 
    Limit_VfromE [OF apply_funtype InfCard_csucc [THEN InfCard_is_Limit]]

lemma fun_Vcsucc_lemma:
     "[| f: D -> Vfrom(A,csucc(K));  |D| le K;  InfCard(K) |]   
      ==> EX j. f: D -> Vfrom(A,j) & j < csucc(K)"
apply (rule_tac x = "UN d:D. LEAST i. f`d : Vfrom (A,i) " in exI)
apply (rule conjI)
apply (rule_tac [2] le_UN_Ord_lt_csucc) 
apply (rule_tac [4] ballI, erule_tac [4] fun_Limit_VfromE)
apply (simp_all add: ) 
 prefer 2 apply (fast elim: Least_le [THEN lt_trans1] ltE)
apply (rule Pi_type)
apply (rename_tac [2] d)
apply (erule_tac [2] fun_Limit_VfromE, simp_all)
apply (subgoal_tac "f`d : Vfrom (A, LEAST i. f`d : Vfrom (A,i))")
 apply (erule Vfrom_mono [OF subset_refl UN_upper, THEN subsetD])
 apply assumption
apply (fast elim: LeastI ltE)
done

lemma subset_Vcsucc:
     "[| D <= Vfrom(A,csucc(K));  |D| le K;  InfCard(K) |]     
      ==> EX j. D <= Vfrom(A,j) & j < csucc(K)"
by (simp add: subset_iff_id fun_Vcsucc_lemma)

(*Version for arbitrary index sets*)
lemma fun_Vcsucc:
     "[| |D| le K;  InfCard(K);  D <= Vfrom(A,csucc(K)) |] ==>  
          D -> Vfrom(A,csucc(K)) <= Vfrom(A,csucc(K))"
apply (safe dest!: fun_Vcsucc_lemma subset_Vcsucc)
apply (rule Vfrom [THEN ssubst])
apply (drule fun_is_rel)
(*This level includes the function, and is below csucc(K)*)
apply (rule_tac a1 = "succ (succ (j Un ja))" in UN_I [THEN UnI2])
apply (blast intro: ltD InfCard_csucc InfCard_is_Limit Limit_has_succ
                    Un_least_lt); 
apply (erule subset_trans [THEN PowI])
apply (fast intro: Pair_in_Vfrom Vfrom_UnI1 Vfrom_UnI2)
done

lemma fun_in_Vcsucc:
     "[| f: D -> Vfrom(A, csucc(K));  |D| le K;  InfCard(K);         
         D <= Vfrom(A,csucc(K)) |]                                   
       ==> f: Vfrom(A,csucc(K))"
by (blast intro: fun_Vcsucc [THEN subsetD])

(*Remove <= from the rule above*)
lemmas fun_in_Vcsucc' = fun_in_Vcsucc [OF _ _ _ subsetI]

(** Version where K itself is the index set **)

lemma Card_fun_Vcsucc:
     "InfCard(K) ==> K -> Vfrom(A,csucc(K)) <= Vfrom(A,csucc(K))"
apply (frule InfCard_is_Card [THEN Card_is_Ord])
apply (blast del: subsetI
	     intro: fun_Vcsucc Ord_cardinal_le i_subset_Vfrom 
                   lt_csucc [THEN leI, THEN le_imp_subset, THEN subset_trans]) 
done

lemma Card_fun_in_Vcsucc:
     "[| f: K -> Vfrom(A, csucc(K));  InfCard(K) |] ==> f: Vfrom(A,csucc(K))"
by (blast intro: Card_fun_Vcsucc [THEN subsetD]) 

lemma Limit_csucc: "InfCard(K) ==> Limit(csucc(K))"
by (erule InfCard_csucc [THEN InfCard_is_Limit])

lemmas Pair_in_Vcsucc = Pair_in_VLimit [OF _ _ Limit_csucc]
lemmas Inl_in_Vcsucc = Inl_in_VLimit [OF _ Limit_csucc]
lemmas Inr_in_Vcsucc = Inr_in_VLimit [OF _ Limit_csucc]
lemmas zero_in_Vcsucc = Limit_csucc [THEN zero_in_VLimit]
lemmas nat_into_Vcsucc = nat_into_VLimit [OF _ Limit_csucc]

(*For handling Cardinals of the form  (nat Un |X|) *)

lemmas InfCard_nat_Un_cardinal = InfCard_Un [OF InfCard_nat Card_cardinal]

lemmas le_nat_Un_cardinal =
     Un_upper2_le [OF Ord_nat Card_cardinal [THEN Card_is_Ord]]

lemmas UN_upper_cardinal = UN_upper [THEN subset_imp_lepoll, THEN lepoll_imp_Card_le]

(*The new version of Data_Arg.intrs, declared in Datatype.ML*)
lemmas Data_Arg_intros =
       SigmaI InlI InrI
       Pair_in_univ Inl_in_univ Inr_in_univ 
       zero_in_univ A_into_univ nat_into_univ UnCI

(*For most K-branching datatypes with domain Vfrom(A, csucc(K)) *)
lemmas inf_datatype_intros =
     InfCard_nat InfCard_nat_Un_cardinal
     Pair_in_Vcsucc Inl_in_Vcsucc Inr_in_Vcsucc 
     zero_in_Vcsucc A_into_Vfrom nat_into_Vcsucc
     Card_fun_in_Vcsucc fun_in_Vcsucc' UN_I 

end

