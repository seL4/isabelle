(*  Title:      ZF/AC/WO1_WO7.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, CU Computer Laboratory
    Copyright   1998  University of Cambridge

WO7 <-> LEMMA <-> WO1 (Rubin & Rubin p. 5)
LEMMA is the sentence denoted by (**)
*)

WO1_WO7 = AC_Equiv +

constdefs
  LEMMA :: o
    "LEMMA ==
     \\<forall>X. ~Finite(X) --> (\\<exists>R. well_ord(X,R) & ~well_ord(X,converse(R)))"

end
