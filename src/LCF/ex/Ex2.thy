
(* $Id$ *)

header {* Example 3.8 *}

theory Ex2
imports LCF
begin

consts
  P     :: "'a => tr"
  F     :: "'a => 'a"
  G     :: "'a => 'a"
  H     :: "'a => 'b => 'b"
  K     :: "('a => 'b => 'b) => ('a => 'b => 'b)"

axioms
  F_strict:     "F(UU) = UU"
  K:            "K = (%h x y. P(x) => y | F(h(G(x),y)))"
  H:            "H = FIX(K)"

ML {* use_legacy_bindings (the_context ()) *}

end
