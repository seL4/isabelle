
(* $Id$ *)

header {* Addition with fixpoint of successor *}

theory Ex3
imports LCF
begin

consts
  s     :: "'a => 'a"
  p     :: "'a => 'a => 'a"

axioms
  p_strict:     "p(UU) = UU"
  p_s:          "p(s(x),y) = s(p(x,y))"

ML {* use_legacy_bindings (the_context ()) *}

end
