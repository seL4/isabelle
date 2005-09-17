(*  Title:      CCL/Hered.thy
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1993  University of Cambridge
*)

header {* Hereditary Termination -- cf. Martin Lo\"f *}

theory Hered
imports Type
uses "coinduction.ML"
begin

text {*
  Note that this is based on an untyped equality and so @{text "lam
  x. b(x)"} is only hereditarily terminating if @{text "ALL x. b(x)"}
  is.  Not so useful for functions!
*}

consts
      (*** Predicates ***)
  HTTgen     ::       "i set => i set"
  HTT        ::       "i set"

axioms
  (*** Definitions of Hereditary Termination ***)

  HTTgen_def:
  "HTTgen(R) == {t. t=true | t=false | (EX a b. t=<a,b>      & a : R & b : R) |
                                      (EX f.  t=lam x. f(x) & (ALL x. f(x) : R))}"
  HTT_def:       "HTT == gfp(HTTgen)"

ML {* use_legacy_bindings (the_context ()) *}

end
