(*  Title:      HOLCF/IOA/ABP/Action.ML
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Derived rules for actions.
*)

Goal "!!x. x = y ==> action_case a b c x =     \
\                        action_case a b c y";
by (Asm_simp_tac 1);

Addcongs [result()];
