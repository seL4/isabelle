(*  Title:      TFL/thms.ML
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

structure Thms =
struct
  val WFREC_COROLLARY = thm "tfl_wfrec";
  val WF_INDUCTION_THM = thm "tfl_wf_induct";
  val CUT_DEF = thm "cut_def";
  val SELECT_AX = thm "tfl_some";
  val eqT = thm "tfl_eq_True";
  val rev_eq_mp = thm "tfl_rev_eq_mp";
  val simp_thm = thm "tfl_simp_thm";
  val P_imp_P_iff_True = thm "tfl_P_imp_P_iff_True";
  val imp_trans = thm "tfl_imp_trans";
  val disj_assoc = thm "tfl_disj_assoc";
  val tfl_disjE = thm "tfl_disjE";
  val choose_thm = thm "tfl_exE";
end;
