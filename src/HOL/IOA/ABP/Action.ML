(*  Title:      HOL/IOA/ABP/Action.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Olaf Mueller
    Copyright   1995  TU Muenchen

Derived rules for actions
*)

goal Action.thy "!!x. x = y ==> action_case a b c d e f g x =     \
\                               action_case a b c d e f g y";
by (asm_simp_tac HOL_ss 1);

val action_ss = arith_ss addcongs [result()] addsimps Action.action.simps;
