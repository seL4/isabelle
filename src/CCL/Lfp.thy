(*  Title:      HOL/lfp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The Knaster-Tarski Theorem
*)

Lfp = Set +
consts lfp :: "['a set=>'a set] => 'a set"
rules
 (*least fixed point*)
 lfp_def "lfp(f) == Inter({u. f(u) <= u})"
end
