(*  Title:      Option.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen

Derived rules
*)

open Option;

val [prem] = goal Option.thy "P(opt) ==> P(None) | (? x. P(Some(x)))";
 br (prem RS rev_mp) 1;
 by (option.induct_tac "opt" 1);
 by (ALLGOALS(Fast_tac));
bind_thm("optionE", standard(result() RS disjE));
(*
goal Option.thy "opt=None | (? x.opt=Some(x))"; 
by (option.induct_tac "opt" 1);
by (Simp_tac 1);
by (rtac disjI2 1);
by (rtac exI 1);
by (Asm_full_simp_tac 1);
qed"option_cases";
*)
goal Option.thy "P(case opt of None => a | Some(x) => b(x)) = \
\                ((opt = None --> P a) & (!x. opt = Some x --> P(b(x))))";
by (option.induct_tac "opt" 1);
by (Simp_tac 1);
by (Asm_full_simp_tac 1);
by (Fast_tac 1);
qed"expand_option_case";
