(*  Title:      HOL/Modelcheck/MuCalculus.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

MuCalculus = Main +

types
 'a pred = "'a=>bool"

consts

  Charfun :: "'a set => 'a pred"
  mu     :: "('a pred => 'a pred) => 'a pred"  (binder "Mu " 10)
  nu     :: "('a pred => 'a pred) => 'a pred"  (binder "Nu " 10)
  monoP  :: "('a pred => 'a pred) => bool"

defs

Charfun_def      "Charfun     == (% A.% x. x:A)"
monoP_def        "monoP f     == mono(Collect o f o Charfun)"
mu_def           "mu f        == Charfun(lfp(Collect o f o Charfun))"
nu_def           "nu f        == Charfun(gfp(Collect o f o Charfun))"

end
