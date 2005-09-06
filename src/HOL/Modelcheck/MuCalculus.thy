(*  Title:      HOL/Modelcheck/MuCalculus.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

theory MuCalculus
imports Main
begin

types
 'a pred = "'a=>bool"

constdefs
  Charfun :: "'a set => 'a pred"
  "Charfun == (% A.% x. x:A)"

  monoP  :: "('a pred => 'a pred) => bool"
  "monoP f == mono(Collect o f o Charfun)"

  mu :: "('a pred => 'a pred) => 'a pred"    (binder "Mu " 10)
  "mu f == Charfun(lfp(Collect o f o Charfun))"

  nu :: "('a pred => 'a pred) => 'a pred"    (binder "Nu " 10)
  "nu f == Charfun(gfp(Collect o f o Charfun))"

ML {* use_legacy_bindings (the_context ()) *}

end
