(*  Title:      HOL/IOA/NTP/Action.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

Derived rules for actions
*)

Goal "!!x. x = y ==> action_case a b c d e f g h i j x =     \
\                               action_case a b c d e f g h i j y";
by (Asm_simp_tac 1);

Addcongs [result()];
