(*  Title:      ZF/IntDiv.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

The division operators div, mod
*)

IntDiv = IntArith + OrderArith + 

constdefs
  quorem :: "[i,i] => o"
    "quorem == %<a,b> <q,r>.
                      a = b$*q $+ r &
                      (#0$<b & #0$<=r & r$<b | ~(#0$<b) & b$<r & r $<= #0)"

  adjust :: "[i,i,i] => i"
    "adjust(a,b) == %<q,r>. if #0 $<= r$-b then <#2$*q $+ #1,r$-b>
                            else <#2$*q,r>"


(** the division algorithm **)

constdefs posDivAlg :: "i => i"
(*for the case a>=0, b>0*)
(*recdef posDivAlg "inv_image less_than (%(a,b). nat_of(a $- b $+ #1))"*)
    "posDivAlg(ab) ==
       wfrec(measure(int*int, %<a,b>. nat_of (a $- b $+ #1)),
	     ab,
	     %<a,b> f. if (a$<b | b$<=#0) then <#0,a>
                       else adjust(a, b, f ` <a,#2$*b>))"

(**TO BE COMPLETED**)

end
