(*  Title: 	ZF/wf.thy
    ID:         $Id$
    Author: 	Tobias Nipkow and Lawrence C Paulson
    Copyright   1992  University of Cambridge

Well-founded Recursion
*)

WF = Trancl + "mono" +
consts
    wf		 ::      "i=>o"
    wftrec,wfrec ::      "[i, i, [i,i]=>i] =>i"
    is_recfun    ::      "[i, i, [i,i]=>i, i] =>o"
    the_recfun   ::      "[i, i, [i,i]=>i] =>i"

rules
  (*r is a well-founded relation*)
  wf_def	 "wf(r) == ALL Z. Z=0 | (EX x:Z. ALL y. <y,x>:r --> ~ y:Z)"

  is_recfun_def  "is_recfun(r,a,H,f) == \
\   			(f = (lam x: r-``{a}. H(x, restrict(f, r-``{x}))))"

  the_recfun_def "the_recfun(r,a,H) == (THE f.is_recfun(r,a,H,f))"

  wftrec_def  	 "wftrec(r,a,H) == H(a, the_recfun(r,a,H))"

  (*public version.  Does not require r to be transitive*)
  wfrec_def "wfrec(r,a,H) == wftrec(r^+, a, %x f. H(x, restrict(f,r-``{x})))"

end
