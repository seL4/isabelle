(*  Title:      HOL/Nat.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TU Muenchen

Type "nat" is a linear order, and a datatype
*)

Nat = NatDef + Inductive +

rep_datatype nat
  distinct Suc_not_Zero, Zero_not_Suc
  inject   Suc_Suc_eq
  induct   nat_induct

instance nat :: order (le_refl,le_trans,le_anti_sym,nat_less_le)
instance nat :: linorder (nat_le_linear)

consts
  "^"           :: ['a::power,nat] => 'a            (infixr 80)

end
