(*  Title:      HOL/Modelcheck/CTL.thy
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

theory CTL
imports MuCalculus
begin

types
  'a trans  = "('a * 'a) set"

definition CEX :: "['a trans,'a pred, 'a]=>bool" where
  "CEX N f u == (? v. (f v & (u,v):N))"

definition EG ::"['a trans,'a pred]=> 'a pred" where
  "EG N f == nu (% Q. % u.(f u & CEX N Q u))"

end
