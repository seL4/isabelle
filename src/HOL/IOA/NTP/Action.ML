(*  Title:      HOL/IOA/NTP/Action.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

Derived rules for actions
*)

goal Action.thy "!!x. x = y ==> action_case a b c d e f g h i j x =     \
\                               action_case a b c d e f g h i j y";
by (asm_simp_tac HOL_ss 1);

val action_ss = arith_ss addcongs [result()] addsimps Action.action.simps;
