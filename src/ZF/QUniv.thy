(*  Title:      ZF/QUniv.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

A small universe for lazy recursive types.
*)

QUniv = Univ + QPair + mono + equalities +

constdefs
  quniv :: i => i
  "quniv(A) == Pow(univ(eclose(A)))"

end
