structure Thms : Thms_sig =
struct
   type Thm = Thm.thm

   val WFREC_COROLLARY = get_thm WF_Rel.thy "tfl_wfrec"
   val WF_INDUCTION_THM = get_thm WF_Rel.thy "tfl_wf_induct"
   val CUT_LEMMA = get_thm WF_Rel.thy "tfl_cut_apply"
   val CUT_DEF = cut_def

   local val _ = goal HOL.thy "!P x. P x --> P (Eps P)"
         val _ = by (strip_tac 1)
         val _ = by (rtac selectI 1)
         val _ = by (assume_tac 1)
   in val SELECT_AX = result()
   end;

  (*-------------------------------------------------------------------------
   *  A useful congruence rule
   *-------------------------------------------------------------------------*)
   local val [p1,p2] = goal HOL.thy "(M = N) ==> \
                          \ (!!x. ((x = N) ==> (f x = g x))) ==> \
                          \ (Let M f = Let N g)";
         val _ = by (simp_tac (HOL_ss addsimps[Let_def,p1]) 1);
         val _ = by (rtac p2 1);
         val _ = by (rtac refl 1);
   in val LET_CONG = result() RS eq_reflection
   end;

   val COND_CONG = if_cong RS eq_reflection;

   fun C f x y = f y x;
   fun prover thl = [fast_tac HOL_cs 1];
   val P = C (prove_goal HOL.thy) prover;

   val eqT       = P"(x = True) --> x"
   val rev_eq_mp = P"(x = y) --> y --> x"
   val simp_thm  = P"(x-->y) --> (x = x') --> (x' --> y)"

end;
