(*  Title: 	HOL/gfp.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Greatest fixed points
*)

Gfp = Lfp +
consts gfp :: "['a set=>'a set] => 'a set"
rules
 (*greatest fixed point*)
 gfp_def "gfp(f) == Union({u. u <= f(u)})"
end
