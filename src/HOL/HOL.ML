(* legacy ML bindings *)

val HOL_cs = HOL.claset;
val HOL_basic_ss = HOL.simpset_basic;
val HOL_ss = HOL.simpset;
val HOL_css = (HOL.claset, HOL.simpset);
val hol_simplify = HOL.simplify;

val split_tac        = Splitter.split_tac;
val split_inside_tac = Splitter.split_inside_tac;
val split_asm_tac    = Splitter.split_asm_tac;
val op addsplits     = Splitter.addsplits;
val op delsplits     = Splitter.delsplits;
val Addsplits        = Splitter.Addsplits;
val Delsplits        = Splitter.Delsplits;

open HOL;
val claset = Classical.claset;
val simpset = Simplifier.simpset;
val simplify = Simplifier.simplify;
open Hypsubst;
open BasicClassical;
open Clasimp;

val ext = thm "ext"
val True_def = thm "True_def"
val All_def = thm "All_def"
val Ex_def = thm "Ex_def"
val False_def = thm "False_def"
val not_def = thm "not_def"
val and_def = thm "and_def"
val or_def = thm "or_def"
val Ex1_def = thm "Ex1_def"
val iff = thm "iff"
val True_or_False = thm "True_or_False"
val Let_def = thm "Let_def"
val if_def = thm "if_def"
val ssubst = thm "ssubst"
val box_equals = thm "box_equals"
val fun_cong = thm "fun_cong"
val cong = thm "cong"
val rev_iffD2 = thm "rev_iffD2"
val rev_iffD1 = thm "rev_iffD1"
val iffE = thm "iffE"
val eqTrueI = thm "eqTrueI"
val eqTrueE = thm "eqTrueE"
val all_dupE = thm "all_dupE"
val FalseE = thm "FalseE"
val False_neq_True = thm "False_neq_True"
val False_not_True = thm "False_not_True"
val True_not_False = thm "True_not_False"
val notI2 = thm "notI2"
val impE = thm "impE"
val not_sym = thm "not_sym"
val rev_contrapos = thm "rev_contrapos"
val conjE = thm "conjE"
val context_conjI = thm "context_conjI"
val disjI1 = thm "disjI1"
val disjI2 = thm "disjI2"
val rev_notE = thm "rev_notE"
val ex1I = thm "ex1I"
val ex1E = thm "ex1E"
val ex1_implies_ex = thm "ex1_implies_ex"
val the_equality = thm "the_equality"
val theI = thm "theI"
val theI' = thm "theI'"
val theI2 = thm "theI2"
val the1_equality = thm "the1_equality"
val excluded_middle = thm "excluded_middle"
val case_split_thm = thm "case_split_thm"
val exCI = thm "exCI"
val choice_eq = thm "choice_eq"
val eq_cong2 = thm "eq_cong2"
val if_cong = thm "if_cong"
val if_weak_cong = thm "if_weak_cong"
val let_weak_cong = thm "let_weak_cong"
val eq_cong2 = thm "eq_cong2"
val if_distrib = thm "if_distrib"
val expand_case = thm "expand_case"
val restrict_to_left = thm "restrict_to_left"
val all_conj_distrib = thm "all_conj_distrib";
val atomize_not = thm "atomize_not";
val split_if = thm "split_if";
val split_if_asm = thm "split_if_asm";
val rev_conj_cong = thm "rev_conj_cong";
val not_all = thm "not_all";
val not_ex = thm "not_ex";
val not_iff = thm "not_iff";
val not_imp = thm "not_imp";
val not_not = thm "not_not";
val eta_contract_eq = thm "eta_contract_eq";
val eq_ac = thms "eq_ac";
val eq_commute = thm "eq_commute";
val eq_sym_conv = thm "eq_commute";
val neq_commute = thm "neq_commute";
val conj_comms = thms "conj_comms";
val conj_commute = thm "conj_commute";
val conj_cong = thm "conj_cong";
val conj_disj_distribL = thm "conj_disj_distribL";
val conj_disj_distribR = thm "conj_disj_distribR";
val conj_left_commute = thm "conj_left_commute";
val disj_comms = thms "disj_comms";
val disj_commute = thm "disj_commute";
val disj_cong = thm "disj_cong";
val disj_conj_distribL = thm "disj_conj_distribL";
val disj_conj_distribR = thm "disj_conj_distribR";
val disj_left_commute = thm "disj_left_commute";
val eq_assoc = thm "eq_assoc";
val eq_left_commute = thm "eq_left_commute";
val ex_disj_distrib = thm "ex_disj_distrib";
val if_P = thm "if_P";
val if_bool_eq_disj = thm "if_bool_eq_disj";
val if_def2 = thm "if_bool_eq_conj";
val if_not_P = thm "if_not_P";
val if_splits = thms "if_splits";
val imp_all = thm "imp_all";
val imp_conjL = thm "imp_conjL";
val imp_conjR = thm "imp_conjR";
val imp_disj_not1 = thm "imp_disj_not1";
val imp_disj_not2 = thm "imp_disj_not2";
val imp_ex = thm "imp_ex";
val meta_eq_to_obj_eq = thm "def_imp_eq";
val ex_simps = thms "ex_simps";
val all_simps = thms "all_simps";
val simp_thms = thms "simp_thms";
val Eq_FalseI = thm "Eq_FalseI";
val Eq_TrueI = thm "Eq_TrueI";
val cases_simp = thm "cases_simp";
val conj_assoc = thm "conj_assoc";
val de_Morgan_conj = thm "de_Morgan_conj";
val de_Morgan_disj = thm "de_Morgan_disj";
val disj_assoc = thm "disj_assoc";
val disj_not1 = thm "disj_not1";
val disj_not2 = thm "disj_not2";
val if_False = thm "if_False";
val if_True = thm "if_True";
val if_bool_eq_conj = thm "if_bool_eq_conj";
val if_cancel = thm "if_cancel";
val if_eq_cancel = thm "if_eq_cancel";
val iff_conv_conj_imp = thm "iff_conv_conj_imp";
val imp_cong = thm "imp_cong";
val imp_conv_disj = thm "imp_conv_disj";
val imp_disj1 = thm "imp_disj1";
val imp_disj2 = thm "imp_disj2";
val imp_disjL = thm "imp_disjL";
val simp_impliesI = thm "simp_impliesI";
val simp_implies_cong = thm "simp_implies_cong";
val simp_implies_def = thm "simp_implies_def";
val True_implies_equals = thm "True_implies_equals";

structure HOL =
struct

open HOL;

val thy = the_context ();

end;
