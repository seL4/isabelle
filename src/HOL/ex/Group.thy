(*  Title:      HOL/Integ/Group.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TU Muenchen

A little bit of group theory leading up to rings. Hence groups are additive.
*)

Group = Main +

(* additive semigroups *)

axclass  add_semigroup < plus
  plus_assoc   "(x + y) + z = x + (y + z)"


(* additive monoids *)

axclass  add_monoid < add_semigroup, zero
  zeroL    "0 + x = x"
  zeroR    "x + 0 = x"

(* additive groups *)
(*
The inverse is the binary `-'. Groups with unary and binary inverse are
interdefinable: x-y := x+(0-y) and -x := 0-x. The law left_inv is
simply the translation of (-x)+x = 0. This characterizes groups already,
provided we only allow (0-x). Law minus_inv `defines' the general x-y in
terms of the specific 0-y.
*)
axclass  add_group < add_monoid, minus
  left_inv  "(0-x)+x = 0"
  minus_inv "x-y = x + (0-y)"

(* additive abelian groups *)

axclass  add_agroup < add_group
  plus_commute  "x + y = y + x"

end
