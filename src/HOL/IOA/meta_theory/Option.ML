(*  Title:      Option.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994  TU Muenchen

Derived rules
*)

val option_rws = Let_def :: Option.option.simps;
val SS = arith_ss addsimps option_rws;

val [prem] = goal Option.thy "P(opt) ==> P(None) | (? x. P(Some(x)))";
 br (prem RS rev_mp) 1;
 by (Option.option.induct_tac "opt" 1);
 by (ALLGOALS(fast_tac HOL_cs));
val optE = store_thm("optE", standard(result() RS disjE));
