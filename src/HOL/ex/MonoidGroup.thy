(*  Title:      HOL/ex/MonoidGroup.thy
    ID:         $Id$
    Author:     Markus Wenzel
    Copyright   1996 TU Muenchen

Monoids and Groups as predicates over record schemes.
*)

MonoidGroup = HOL + Record +


record 'a monoid_sig =
  times :: "['a, 'a] => 'a"
  one :: 'a

record 'a group_sig = 'a monoid_sig +
  inv :: "'a => 'a"

constdefs
  monoid :: "(| times :: ['a, 'a] => 'a, one :: 'a, ... :: 'more::more |) => bool"
  "monoid M == ALL x y z.
    times M (times M x y) z = times M x (times M y z) &
    times M (one M) x = x & times M x (one M) = x"

  group :: "(| times :: ['a, 'a] => 'a, one :: 'a, inv :: 'a => 'a, ... :: 'more::more |) => bool"
  "group G == monoid G & (ALL x. times G (inv G x) x = one G)"

  reverse :: "(| times :: ['a, 'a] => 'a, one :: 'a, ... :: 'more::more |) =>
    (| times :: ['a, 'a] => 'a, one :: 'a, ... :: 'more |)"
  "reverse M == M (| times := %x y. times M y x |)"


end
