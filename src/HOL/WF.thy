(*  Title:      HOL/wf.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1992  University of Cambridge

Well-founded Recursion
*)

WF = Trancl +
consts
 wf         :: "('a * 'a)set => bool"
 cut        :: "('a => 'b) => ('a * 'a)set => 'a => 'a => 'b"
 is_recfun  :: "('a * 'a)set => (('a=>'b) => ('a=>'b)) =>'a=>('a=>'b) => bool"
 the_recfun :: "('a * 'a)set => (('a=>'b) => ('a=>'b)) => 'a => 'a => 'b"
 wfrec      :: "('a * 'a)set => (('a=>'b) => ('a=>'b)) => 'a => 'b"

defs
  wf_def  "wf(r) == (!P. (!x. (!y. (y,x):r --> P(y)) --> P(x)) --> (!x.P(x)))"
  
  cut_def        "cut f r x == (%y. if (y,x):r then f y else @z.True)"

  is_recfun_def  "is_recfun r H a f == (f = cut (%x. H (cut f r x) x) r a)"

  the_recfun_def "the_recfun r H a  == (@f. is_recfun r H a f)"

  wfrec_def
    "wfrec r H == (%x. H (cut (the_recfun (trancl r) (%f v. H (cut f r v) v) x)
                              r x)  x)"
end
