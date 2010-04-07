(*  Title:      HOL/Modelcheck/MuCalculus.thy
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

theory MuCalculus
imports Main
begin

types
 'a pred = "'a=>bool"

definition Charfun :: "'a set => 'a pred" where
  "Charfun == (% A.% x. x:A)"

definition monoP  :: "('a pred => 'a pred) => bool" where
  "monoP f == mono(Collect o f o Charfun)"

definition mu :: "('a pred => 'a pred) => 'a pred" (binder "Mu " 10) where
  "mu f == Charfun(lfp(Collect o f o Charfun))"

definition nu :: "('a pred => 'a pred) => 'a pred" (binder "Nu " 10) where
  "nu f == Charfun(gfp(Collect o f o Charfun))"

end
