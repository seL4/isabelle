(*  Title:      Option.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994  TU Muenchen

Derived rules
*)

Addsimps [Let_def];

val [prem] = goal Option.thy "P(opt) ==> P(None) | (? x. P(Some(x)))";
 br (prem RS rev_mp) 1;
 by (Option.option.induct_tac "opt" 1);
 by (ALLGOALS(Fast_tac));
val optE = store_thm("optE", standard(result() RS disjE));

goal Option.thy "x=None | (? y.x=Some(y))"; 
by (Option.option.induct_tac "x" 1);
by (Asm_full_simp_tac 1);
by (rtac disjI2 1);
by (rtac exI 1);
by (Asm_full_simp_tac 1);
qed"opt_cases";
