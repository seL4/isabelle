(*  Title:      HOL/ex/Group.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TU Muenchen

A little bit of group theory leading up to rings. Hence groups are additive.
*)

Group = Set +

(* 0 already used in Nat *)
axclass  zero < term
consts   zero :: "'a::zero"

(* additive semigroups *)

axclass  add_semigroup < plus
  plus_assoc   "(x + y) + z = x + (y + z)"


(* additive monoids *)

axclass  add_monoid < add_semigroup, zero
  zeroL    "zero + x = x"
  zeroR    "x + zero = x"

(* additive groups *)

axclass  add_group < add_monoid, minus
  left_inv  "(zero-x)+x = zero"
  minus_inv "x-y = x + (zero-y)"

(* additive abelian groups *)

axclass  add_agroup < add_group
  plus_commute  "x + y = y + x"

end
