(*  Title:      HOL/Modelcheck/CTL.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

theory CTL
imports MuCalculus
begin

types
  'a trans  = "('a * 'a) set"

constdefs
  CEX ::"['a trans,'a pred, 'a]=>bool"
  "CEX N f u == (? v. (f v & (u,v):N))"
  EG ::"['a trans,'a pred]=> 'a pred"
  "EG N f == nu (% Q. % u.(f u & CEX N Q u))"

ML {* use_legacy_bindings (the_context ()) *}

end
