(*  Title:      ZF/IntDiv.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

The division operators div, mod
*)

IntDiv = IntArith + 

constdefs
  quorem :: "[i,i] => o"
    "quorem == %<a,b> <q,r>.
                      a = b$*q $+ r &
                      (#0$<b & #0$<=r & r$<b | ~(#0$<b) & b$<r & r $<= #0)"

  adjust :: "[i,i,i] => i"
    "adjust(a,b) == %<q,r>. if #0 $<= r$-b then <#2$*q $+ #1,r$-b>
                            else <#2$*q,r>"


end
