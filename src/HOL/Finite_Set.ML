
(* legacy ML bindings *)

structure Finites =
struct
  val intrs = thms "Finites.intros";
  val elims = thms "Finites.cases";
  val elim = thm "Finites.cases";
  val induct = thm "Finites.induct";
  val mk_cases = InductivePackage.the_mk_cases (the_context ()) "Finite_Set.Finites";
  val [emptyI, insertI] = thms "Finites.intros";
end;

structure cardR =
struct
  val intrs = thms "cardR.intros";
  val elims = thms "cardR.cases";
  val elim = thm "cardR.cases";
  val induct = thm "cardR.induct";
  val mk_cases = InductivePackage.the_mk_cases (the_context ()) "Finite_Set.cardR";
  val [EmptyI, InsertI] = thms "cardR.intros";
end;

structure foldSet =
struct
  val intrs = thms "foldSet.intros";
  val elims = thms "foldSet.cases";
  val elim = thm "foldSet.cases";
  val induct = thm "foldSet.induct";
  val mk_cases = InductivePackage.the_mk_cases (the_context ()) "Finite_Set.foldSet";
  val [emptyI, insertI] = thms "foldSet.intros";
end;

val Diff1_foldSet = thm "Diff1_foldSet";
val cardR_SucD = thm "cardR_SucD";
val cardR_determ = thm "cardR_determ";
val cardR_emptyE = thm "cardR_emptyE";
val cardR_imp_finite = thm "cardR_imp_finite";
val cardR_insertE = thm "cardR_insertE";
val card_0_eq = thm "card_0_eq";
val card_Diff1_le = thm "card_Diff1_le";
val card_Diff1_less = thm "card_Diff1_less";
val card_Diff2_less = thm "card_Diff2_less";
val card_Diff_singleton = thm "card_Diff_singleton";
val card_Diff_singleton_if = thm "card_Diff_singleton_if";
val card_Diff_subset = thm "card_Diff_subset";
val card_Pow = thm "card_Pow";
val card_Suc_Diff1 = thm "card_Suc_Diff1";
val card_Un_Int = thm "card_Un_Int";
val card_Un_disjoint = thm "card_Un_disjoint";
val card_bij_eq = thm "card_bij_eq";
val card_def = thm "card_def";
val card_empty = thm "card_empty";
val card_eq_setsum = thm "card_eq_setsum";
val card_equality = thm "card_equality";
val card_image = thm "card_image";
val card_image_le = thm "card_image_le";
val card_inj_on_le = thm "card_inj_on_le";
val card_insert = thm "card_insert";
val card_insert_disjoint = thm "card_insert_disjoint";
val card_insert_if = thm "card_insert_if";
val card_insert_le = thm "card_insert_le";
val card_mono = thm "card_mono";
val card_psubset = thm "card_psubset";
val card_s_0_eq_empty = thm "card_s_0_eq_empty";
val card_seteq = thm "card_seteq";
val choose_deconstruct = thm "choose_deconstruct";
val constr_bij = thm "constr_bij";
val dvd_partition = thm "dvd_partition";
val empty_foldSetE = thm "empty_foldSetE";
val endo_inj_surj = thm "endo_inj_surj";
val finite = thm "finite";
val finiteI = thm "finiteI";
val finite_Diff = thm "finite_Diff";
val finite_Diff_insert = thm "finite_Diff_insert";
val finite_Field = thm "finite_Field";
val finite_Int = thm "finite_Int";
val finite_Pow_iff = thm "finite_Pow_iff";
val finite_Prod_UNIV = thm "finite_Prod_UNIV";
val finite_SigmaI = thm "finite_SigmaI";
val finite_UN = thm "finite_UN";
val finite_UN_I = thm "finite_UN_I";
val finite_Un = thm "finite_Un";
val finite_UnI = thm "finite_UnI";
val finite_converse = thm "finite_converse";
val finite_empty_induct = thm "finite_empty_induct";
val finite_imageD = thm "finite_imageD";
val finite_imageI = thm "finite_imageI";
val finite_imp_cardR = thm "finite_imp_cardR";
val finite_imp_foldSet = thm "finite_imp_foldSet";
val finite_induct = thm "finite_induct";
val finite_insert = thm "finite_insert";
val finite_range_imageI = thm "finite_range_imageI";
val finite_subset = thm "finite_subset";
val finite_subset_induct = thm "finite_subset_induct";
val finite_trancl = thm "finite_trancl";
val foldSet_determ = thm "LC.foldSet_determ";
val foldSet_imp_finite = thm "foldSet_imp_finite";
val fold_Un_Int = thm "ACe.fold_Un_Int";
val fold_Un_disjoint = thm "ACe.fold_Un_disjoint";
val fold_Un_disjoint2 = thm "ACe.fold_Un_disjoint2";
val fold_commute = thm "LC.fold_commute";
val fold_def = thm "fold_def";
val fold_empty = thm "fold_empty";
val fold_equality = thm "LC.fold_equality";
val fold_insert = thm "LC.fold_insert";
val fold_nest_Un_Int = thm "LC.fold_nest_Un_Int";
val fold_nest_Un_disjoint = thm "LC.fold_nest_Un_disjoint";
val n_sub_lemma = thm "n_sub_lemma";
val n_subsets = thm "n_subsets";
val psubset_card_mono = thm "psubset_card_mono";
val setsum_0 = thm "setsum_0";
val setsum_SucD = thm "setsum_SucD";
val setsum_UN_disjoint = thm "setsum_UN_disjoint";
val setsum_Un = thm "setsum_Un";
val setsum_Un_Int = thm "setsum_Un_Int";
val setsum_Un_disjoint = thm "setsum_Un_disjoint";
val setsum_addf = thm "setsum_addf";
val setsum_cong = thm "setsum_cong";
val setsum_def = thm "setsum_def";
val setsum_diff1 = thm "setsum_diff1";
val setsum_empty = thm "setsum_empty";
val setsum_eq_0_iff = thm "setsum_eq_0_iff";
val setsum_insert = thm "setsum_insert";
val trancl_subset_Field2 = thm "trancl_subset_Field2";
