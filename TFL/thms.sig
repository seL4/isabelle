signature Thms_sig =
sig
   type Thm
   val WF_INDUCTION_THM:Thm
   val WFREC_COROLLARY :Thm
   val CUT_DEF         :Thm
   val CUT_LEMMA       :Thm
   val SELECT_AX       :Thm
   
   val COND_CONG :Thm
   val LET_CONG  :Thm

   val eqT       :Thm
   val rev_eq_mp :Thm
   val simp_thm  :Thm
end;
