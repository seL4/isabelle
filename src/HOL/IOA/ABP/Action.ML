(*  Title:      HOL/IOA/example/Action.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

Derived rules for actions
*)

goal Action.thy "!!x. x = y ==> action_case a b c d e f g x =     \
\                               action_case a b c d e f g y";
by (Asm_simp_tac 1);

Addcongs [result()];
