(*  Title:      HOL/ex/MonoidGroup.thy
    ID:         $Id$
    Author:     Markus Wenzel
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Monoids and Groups as predicates over record schemes.
*)

header {* Monoids and Groups *}

theory MonoidGroup = Main:

record 'a monoid_sig =
  times :: "'a => 'a => 'a"
  one :: 'a

record 'a group_sig = "'a monoid_sig" +
  inv :: "'a => 'a"

constdefs
  monoid :: "(| times :: 'a => 'a => 'a, one :: 'a, ... :: 'b::more |) => bool"
  "monoid M == \<forall>x y z.
    times M (times M x y) z = times M x (times M y z) \<and>
    times M (one M) x = x \<and> times M x (one M) = x"

  group :: "(| times :: 'a => 'a => 'a, one :: 'a, inv :: 'a => 'a, ... :: 'b::more |) => bool"
  "group G == monoid G \<and> (\<forall>x. times G (inv G x) x = one G)"

  reverse :: "(| times :: 'a => 'a => 'a, one :: 'a, ... :: 'b::more |) =>
    (| times :: 'a => 'a => 'a, one :: 'a, ... :: 'b |)"
  "reverse M == M (| times := \<lambda>x y. times M y x |)"

end
