(*  Title:      HOL/Integ/Group.thy
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
(*
The inverse is the binary `-'. Groups with unary and binary inverse are
interdefinable: x-y := x+(zero-y) and -x := zero-x. The law left_inv is
simply the translation of (-x)+x = zero. This characterizes groups already,
provided we only allow (zero-x). Law minus_inv `defines' the general x-y in
terms of the specific zero-y.
*)
axclass  add_group < add_monoid, minus
  left_inv  "(zero-x)+x = zero"
  minus_inv "x-y = x + (zero-y)"

(* additive abelian groups *)

axclass  add_agroup < add_group
  plus_commute  "x + y = y + x"

end
