(*  Title:      HOL/Modelcheck/CTL.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

CTL = MuCalculus + 


types
  'a trans  = "('a * 'a) set"

consts
  CEX   ::"['a trans,'a pred, 'a]=>bool"
  EG    ::"['a trans,'a pred]=> 'a pred"

defs
  CEX_def  "CEX N f u == (? v. (f v & (u,v):N))"
  EG_def   "EG N f == nu (% Q. % u.(f u & CEX N Q u))"

end
