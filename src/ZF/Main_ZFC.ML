structure Main_ZFC =
struct
  val thy = the_context ();
end;

(* legacy ML bindings *)

(* from AC *)
val AC_Pi = thm "AC_Pi";
val AC_ball_Pi = thm "AC_ball_Pi";
val AC_Pi_Pow = thm "AC_Pi_Pow";
val AC_func = thm "AC_func";
val non_empty_family = thm "non_empty_family";
val AC_func0 = thm "AC_func0";
val AC_func_Pow = thm "AC_func_Pow";
val AC_Pi0 = thm "AC_Pi0";
val choice_Diff = thm "choice_Diff";

(* from Zorn *)
val Union_lemma0 = thm "Union_lemma0";
val Inter_lemma0 = thm "Inter_lemma0";
val increasingD1 = thm "increasingD1";
val increasingD2 = thm "increasingD2";
val TFin_UnionI = thm "TFin_UnionI";
val TFin_is_subset = thm "TFin_is_subset";
val TFin_induct = thm "TFin_induct";
val increasing_trans = thm "increasing_trans";
val TFin_linear_lemma1 = thm "TFin_linear_lemma1";
val TFin_linear_lemma2 = thm "TFin_linear_lemma2";
val TFin_subsetD = thm "TFin_subsetD";
val TFin_subset_linear = thm "TFin_subset_linear";
val equal_next_upper = thm "equal_next_upper";
val equal_next_Union = thm "equal_next_Union";
val chain_subset_Pow = thm "chain_subset_Pow";
val super_subset_chain = thm "super_subset_chain";
val maxchain_subset_chain = thm "maxchain_subset_chain";
val choice_super = thm "choice_super";
val choice_not_equals = thm "choice_not_equals";
val Hausdorff_next_exists = thm "Hausdorff_next_exists";
val TFin_chain_lemma4 = thm "TFin_chain_lemma4";
val Hausdorff = thm "Hausdorff";
val chain_extend = thm "chain_extend";
val Zorn = thm "Zorn";
val TFin_well_lemma5 = thm "TFin_well_lemma5";
val well_ord_TFin_lemma = thm "well_ord_TFin_lemma";
val well_ord_TFin = thm "well_ord_TFin";
val Zermelo_next_exists = thm "Zermelo_next_exists";
val choice_imp_injection = thm "choice_imp_injection";
val AC_well_ord = thm "AC_well_ord";

(* from Cardinal_AC *)
val cardinal_eqpoll = thm "cardinal_eqpoll";
val cardinal_idem = thm "cardinal_idem";
val cardinal_eqE = thm "cardinal_eqE";
val cardinal_eqpoll_iff = thm "cardinal_eqpoll_iff";
val cardinal_disjoint_Un = thm "cardinal_disjoint_Un";
val lepoll_imp_Card_le = thm "lepoll_imp_Card_le";
val cadd_assoc = thm "cadd_assoc";
val cmult_assoc = thm "cmult_assoc";
val cadd_cmult_distrib = thm "cadd_cmult_distrib";
val InfCard_square_eq = thm "InfCard_square_eq";
val Card_le_imp_lepoll = thm "Card_le_imp_lepoll";
val le_Card_iff = thm "le_Card_iff";
val surj_implies_inj = thm "surj_implies_inj";
val surj_implies_cardinal_le = thm "surj_implies_cardinal_le";
val cardinal_UN_le = thm "cardinal_UN_le";
val cardinal_UN_lt_csucc = thm "cardinal_UN_lt_csucc";
val cardinal_UN_Ord_lt_csucc = thm "cardinal_UN_Ord_lt_csucc";
val inj_UN_subset = thm "inj_UN_subset";
val le_UN_Ord_lt_csucc = thm "le_UN_Ord_lt_csucc";

(* from InfDatatype *)
val fun_Limit_VfromE = thm "fun_Limit_VfromE";
val fun_Vcsucc_lemma = thm "fun_Vcsucc_lemma";
val subset_Vcsucc = thm "subset_Vcsucc";
val fun_Vcsucc = thm "fun_Vcsucc";
val fun_in_Vcsucc = thm "fun_in_Vcsucc";
val fun_in_Vcsucc' = thm "fun_in_Vcsucc'";
val Card_fun_Vcsucc = thm "Card_fun_Vcsucc";
val Card_fun_in_Vcsucc = thm "Card_fun_in_Vcsucc";
val Limit_csucc = thm "Limit_csucc";
val Pair_in_Vcsucc = thm "Pair_in_Vcsucc";
val Inl_in_Vcsucc = thm "Inl_in_Vcsucc";
val Inr_in_Vcsucc = thm "Inr_in_Vcsucc";
val zero_in_Vcsucc = thm "zero_in_Vcsucc";
val nat_into_Vcsucc = thm "nat_into_Vcsucc";
val InfCard_nat_Un_cardinal = thm "InfCard_nat_Un_cardinal";
val le_nat_Un_cardinal = thm "le_nat_Un_cardinal";
val UN_upper_cardinal = thm "UN_upper_cardinal";

val inf_datatype_intrs = thms "inf_datatype_intros";

