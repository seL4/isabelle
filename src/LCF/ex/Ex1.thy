
(* $Id$ *)

header {*  Section 10.4 *}

theory Ex1
imports LCF
begin

consts
  P     :: "'a => tr"
  G     :: "'a => 'a"
  H     :: "'a => 'a"
  K     :: "('a => 'a) => ('a => 'a)"

axioms
  P_strict:     "P(UU) = UU"
  K:            "K = (%h x. P(x) => x | h(h(G(x))))"
  H:            "H = FIX(K)"

ML {* use_legacy_bindings (the_context ()) *}

end
