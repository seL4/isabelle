(*  Title:      HOL/Lfp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The Knaster-Tarski Theorem
*)

Lfp = mono + Prod +

constdefs
  lfp :: ['a set=>'a set] => 'a set
  "lfp(f) == Inter({u. f(u) <= u})"    (*least fixed point*)

end
