(*  Title:      ZF/upair.thy
    ID:         $Id$
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1993  University of Cambridge

Definitions involving unordered pairing
*)

upair = ZF +

defs
  (* Definite descriptions -- via Replace over the set "1" *)
  the_def       "The(P)    == Union({y . x:{0}, P(y)})"
  if_def        "if(P,a,b) == THE z. P & z=a | ~P & z=b"

  (*Set difference; binary union and intersection*)
  Diff_def      "A - B    == { x:A . ~(x:B) }"
  Un_def        "A Un  B  == Union(Upair(A,B))"
  Int_def       "A Int B  == Inter(Upair(A,B))"

end
