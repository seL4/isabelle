(*  Title:      HOL/Nat.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TU Muenchen

Nat is a partial order
*)

Nat = NatDef +

instance nat :: order (le_refl,le_trans,le_anti_sym,nat_less_le)

end
