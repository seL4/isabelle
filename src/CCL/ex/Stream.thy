(*  Title:      CCL/ex/stream.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Programs defined over streams.
*)

Stream = List + 

consts

  iter1,iter2   ::  "[i=>i,i]=>i"

rules 

  iter1_def   "iter1(f,a) == letrec iter x be x$iter(f(x)) in iter(a)"
  iter2_def   "iter2(f,a) == letrec iter x be x$map(f,iter(x)) in iter(a)"

end
