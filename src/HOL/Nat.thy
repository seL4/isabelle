(*  Title:      HOL/Nat.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Lawrence C Paulson

Type "nat" is a linear order, and a datatype; arithmetic operators + -
and * (for div, mod and dvd, see theory Divides).
*)

Nat = NatDef + 

(* type "nat" is a wellfounded linear order, and a datatype *)

rep_datatype nat
  distinct Suc_not_Zero, Zero_not_Suc
  inject   Suc_Suc_eq
  induct   nat_induct

instance nat :: order (le_refl,le_trans,le_anti_sym,nat_less_le)
instance nat :: linorder (nat_le_linear)
instance nat :: wellorder (wf_less)

axclass power < type

consts
  power :: ['a::power, nat] => 'a            (infixr "^" 80)


(* arithmetic operators + - and * *)

instance
  nat :: {plus, minus, times, power}

(* size of a datatype value; overloaded *)
consts size :: 'a => nat

primrec
  add_0    "0 + n = n"
  add_Suc  "Suc m + n = Suc(m + n)"

primrec
  diff_0   "m - 0 = m"
  diff_Suc "m - Suc n = (case m - n of 0 => 0 | Suc k => k)"

primrec
  mult_0   "0 * n = 0"
  mult_Suc "Suc m * n = n + (m * n)"

end
