(*  Title:      HOL/gfp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Greatest fixed points (requires Lfp too!)
*)

Gfp = Lfp +

constdefs
  gfp :: ['a set=>'a set] => 'a set
  "gfp(f) == Union({u. u <= f(u)})"    (*greatest fixed point*)

end
