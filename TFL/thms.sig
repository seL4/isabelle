(*  Title:      TFL/thms
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

signature Thms_sig =
sig
   val WF_INDUCTION_THM:thm
   val WFREC_COROLLARY :thm
   val CUT_DEF         :thm
   val CUT_LEMMA       :thm
   val SELECT_AX       :thm
   
   val COND_CONG :thm
   val LET_CONG  :thm

   val eqT       :thm
   val rev_eq_mp :thm
   val simp_thm  :thm
end;
