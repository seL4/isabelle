(*  Title:      ZF/ex/Rmap
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Inductive definition of an operator to "map" a relation over a list
*)

Rmap = List +

consts
  rmap :: i=>i

inductive
  domains "rmap(r)" <= "list(domain(r))*list(range(r))"
  intrs
    NilI  "<Nil,Nil> \\<in> rmap(r)"

    ConsI "[| <x,y>: r;  <xs,ys> \\<in> rmap(r) |] ==> 
          <Cons(x,xs), Cons(y,ys)> \\<in> rmap(r)"

  type_intrs "[domainI,rangeI] @ list.intrs"

end
  
