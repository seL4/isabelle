(*  Title: 	ZF/univ.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

A small universe for lazy recursive types
*)

QUniv = Univ + QPair +
consts
    quniv        :: "i=>i"

rules
    quniv_def    "quniv(A) == Pow(univ(eclose(A)))"

end
