(*  Title:      CCL/Gfp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Greatest fixed points *}

theory Gfp
imports Lfp
begin

constdefs
  gfp :: "['a set=>'a set] => 'a set"    (*greatest fixed point*)
  "gfp(f) == Union({u. u <= f(u)})"

ML {* use_legacy_bindings (the_context ()) *}

end
