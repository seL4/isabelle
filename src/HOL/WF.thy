(*  Title: 	HOL/wf.ML
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1992  University of Cambridge

Well-founded Recursion
*)

WF = Trancl +
consts
   wf		:: "('a * 'a)set => bool"
   cut		:: "['a => 'b, ('a * 'a)set, 'a] => 'a => 'b"
   wftrec,wfrec	:: "[('a * 'a)set, 'a, ['a,'a=>'b]=>'b] => 'b"
   is_recfun	:: "[('a * 'a)set, 'a, ['a,'a=>'b]=>'b, 'a=>'b] => bool"
   the_recfun	:: "[('a * 'a)set, 'a, ['a,'a=>'b]=>'b] => 'a=>'b"

defs
  wf_def  "wf(r) == (!P. (!x. (!y. (y,x):r --> P(y)) --> P(x)) --> (!x.P(x)))"
  
  cut_def 	 "cut f r x == (%y. if (y,x):r then f y else @z.True)"

  is_recfun_def  "is_recfun r a H f == (f = cut (%x.(H x (cut f r x))) r a)"

  the_recfun_def "the_recfun r a H == (@f.is_recfun r a H f)"

  wftrec_def     "wftrec r a H == H a (the_recfun r a H)"

  (*version not requiring transitivity*)
  wfrec_def	"wfrec r a H == wftrec (trancl r) a (%x f.(H x (cut f r x)))"
end
