(*  Title:      Option.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen

Derived rules
*)

open Option;

goal Option.thy "P(case opt of None => a | Some(x) => b x) = \
\                ((opt = None --> P a) & (!x. opt = Some x --> P(b x)))";
by (option.induct_tac "opt" 1);
by (Simp_tac 1);
by (Asm_full_simp_tac 1);
qed "expand_option_case";
