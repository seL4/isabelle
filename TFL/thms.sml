(*  Title:      TFL/thms.sml
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

signature Thms_sig =
sig
   val WF_INDUCTION_THM: thm
   val WFREC_COROLLARY: thm
   val CUT_DEF: thm
   val SELECT_AX: thm
   val eqT: thm
   val rev_eq_mp: thm
   val simp_thm: thm
end;

structure Thms: Thms_sig =
struct
   val WFREC_COROLLARY = get_thm Wellfounded_Recursion.thy "tfl_wfrec";
   val WF_INDUCTION_THM = get_thm Wellfounded_Recursion.thy "tfl_wf_induct";
   val CUT_DEF = get_thm Wellfounded_Recursion.thy "cut_def";

   val SELECT_AX = prove_goal HOL.thy "!P x. P x --> P (Eps P)"
     (fn _ => [strip_tac 1, rtac someI 1, assume_tac 1]);

   fun prove s = prove_goal HOL.thy s (fn _ => [fast_tac HOL_cs 1]);

   val eqT = prove"(x = True) --> x";
   val rev_eq_mp = prove"(x = y) --> y --> x";
   val simp_thm = prove"(x-->y) --> (x = x') --> (x' --> y)";
end;
