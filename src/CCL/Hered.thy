(*  Title: 	CCL/hered.thy
    ID:         $Id$
    Author: 	Martin Coen
    Copyright   1993  University of Cambridge

Hereditary Termination - cf. Martin Lo\"f

Note that this is based on an untyped equality and so lam x.b(x) is only 
hereditarily terminating if ALL x.b(x) is.  Not so useful for functions!

*)

Hered = Type +

consts
      (*** Predicates ***)
  HTTgen     ::       "i set => i set"
  HTT        ::       "i set"


rules

  (*** Definitions of Hereditary Termination ***)

  HTTgen_def 
  "HTTgen(R) == {t. t=true | t=false | (EX a b.t=<a,b>      & a : R & b : R) | \
\                                      (EX f.  t=lam x.f(x) & (ALL x.f(x) : R))}"
  HTT_def       "HTT == gfp(HTTgen)"

end
