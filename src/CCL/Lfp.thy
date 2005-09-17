(*  Title:      CCL/Lfp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* The Knaster-Tarski Theorem *}

theory Lfp
imports Set
uses "subset.ML" "equalities.ML" "mono.ML"
begin

constdefs
  lfp :: "['a set=>'a set] => 'a set"     (*least fixed point*)
  "lfp(f) == Inter({u. f(u) <= u})"

ML {* use_legacy_bindings (the_context ()) *}

end
