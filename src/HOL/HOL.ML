(* legacy ML bindings *)

val Blast_tac = Blast.Blast_tac;
val blast_tac = Blast.blast_tac;

(* combination of (spec RS spec RS ...(j times) ... spec RS mp) *)
local
  fun wrong_prem (Const ("All", _) $ (Abs (_, _, t))) = wrong_prem t
    | wrong_prem (Bound _) = true
    | wrong_prem _ = false;
  val filter_right = filter (not o wrong_prem o HOLogic.dest_Trueprop o hd o Thm.prems_of);
  val spec = thm "spec"
  val mp = thm "mp"
in
  fun smp i = funpow i (fn m => filter_right ([spec] RL m)) ([mp]);
  fun smp_tac j = EVERY'[dresolve_tac (smp j), atac];
end;

fun strip_tac i = REPEAT (resolve_tac [thm "impI", thm "allI"] i);

val split_tac        = Splitter.split_tac;
val split_inside_tac = Splitter.split_inside_tac;

val op addsplits     = Splitter.addsplits;
val op delsplits     = Splitter.delsplits;
val Addsplits        = Splitter.Addsplits;
val Delsplits        = Splitter.Delsplits;

val HOL_basic_ss = Simpdata.simpset_basic;
val hol_simplify = Simpdata.simplify;

open Simpdata;
val claset = Classical.claset;
val simpset = Simplifier.simpset;
val simplify = Simplifier.simplify;
open Hypsubst;
open BasicClassical;
open Clasimp;

val all_conj_distrib = thm "all_conj_distrib";
val all_dupE = thm "all_dupE"
val allE = thm "allE";
val allI = thm "allI";
val all_simps = thms "all_simps";
val arg_cong = thm "arg_cong";
val atomize_not = thm "atomize_not";
val box_equals = thm "box_equals"
val case_split = thm "case_split_thm";
val case_split_thm = thm "case_split_thm"
val cases_simp = thm "cases_simp";
val ccontr = thm "ccontr";
val choice_eq = thm "choice_eq"
val classical = thm "classical";
val cong = thm "cong"
val conj_comms = thms "conj_comms";
val conj_cong = thm "conj_cong";
val conjE = thm "conjE"
val conjE = thm "conjE";
val conjI = thm "conjI";
val conjunct1 = thm "conjunct1";
val conjunct2 = thm "conjunct2";
val def_imp_eq = thm "def_imp_eq";
val de_Morgan_conj = thm "de_Morgan_conj";
val de_Morgan_disj = thm "de_Morgan_disj";
val disj_assoc = thm "disj_assoc";
val disjCI = thm "disjCI";
val disj_comms = thms "disj_comms";
val disj_cong = thm "disj_cong";
val disjE = thm "disjE";
val disjI1 = thm "disjI1"
val disjI2 = thm "disjI2"
val eq_ac = thms "eq_ac";
val eq_cong2 = thm "eq_cong2"
val Eq_FalseI = thm "Eq_FalseI";
val eq_reflection = thm "eq_reflection";
val Eq_TrueI = thm "Eq_TrueI";
val Ex1_def = thm "Ex1_def"
val ex1E = thm "ex1E"
val ex1_implies_ex = thm "ex1_implies_ex"
val ex1I = thm "ex1I"
val excluded_middle = thm "excluded_middle"
val ex_disj_distrib = thm "ex_disj_distrib";
val exE = thm "exE";
val exI = thm "exI";
val ex_simps = thms "ex_simps";
val ext = thm "ext"
val FalseE = thm "FalseE"
val FalseE = thm "FalseE";
val fun_cong = thm "fun_cong"
val if_cancel = thm "if_cancel";
val if_eq_cancel = thm "if_eq_cancel";
val if_False = thm "if_False";
val iff_conv_conj_imp = thm "iff_conv_conj_imp";
val iffD1 = thm "iffD1";
val iffD2 = thm "iffD2";
val iffI = thm "iffI";
val iff = thm "iff"
val if_splits = thms "if_splits";
val if_True = thm "if_True";
val if_weak_cong = thm "if_weak_cong"
val imp_all = thm "imp_all";
val imp_cong = thm "imp_cong";
val imp_conjL = thm "imp_conjL";
val imp_conjR = thm "imp_conjR";
val imp_conv_disj = thm "imp_conv_disj";
val impE = thm "impE"
val impI = thm "impI";
val Let_def = thm "Let_def"
val meta_eq_to_obj_eq = thm "def_imp_eq";
val meta_eq_to_obj_eq = thm "meta_eq_to_obj_eq";
val mp = thm "mp";
val not_all = thm "not_all";
val notE = thm "notE";
val not_ex = thm "not_ex";
val not_iff = thm "not_iff";
val notI = thm "notI";
val not_not = thm "not_not";
val not_sym = thm "not_sym"
val refl = thm "refl";
val rev_mp = thm "rev_mp"
val simp_implies_def = thm "simp_implies_def";
val simp_thms = thms "simp_thms";
val spec = thm "spec";
val split_if = thm "split_if";
val ssubst = thm "ssubst"
val subst = thm "subst";
val sym = thm "sym";
val the1_equality = thm "the1_equality"
val theI = thm "theI"
val theI' = thm "theI'"
val trans = thm "trans";
val True_implies_equals = thm "True_implies_equals";
val TrueI = thm "TrueI";

structure HOL =
struct

val thy = the_context ();

end;
