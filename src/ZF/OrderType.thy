(*  Title: 	ZF/OrderType.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Order types.  

The order type of a well-ordering is the least ordinal isomorphic to it.
*)

OrderType = OrderArith + Ordinal + 
consts
  ordermap  :: "[i,i]=>i"
  ordertype :: "[i,i]=>i"

defs
  ordermap_def
      "ordermap(A,r) == lam x:A. wfrec[A](r, x, %x f. f `` pred(A,x,r))"

  ordertype_def "ordertype(A,r) == ordermap(A,r)``A"

end
