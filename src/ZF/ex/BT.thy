(*  Title:      ZF/ex/BT.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Binary trees
*)

BT = Main +
consts
    bt          :: i=>i

datatype
  "bt(A)" = Lf  |  Br ("a \\<in> A",  "t1: bt(A)",  "t2: bt(A)")

consts
    n_nodes     :: i=>i
    n_leaves    :: i=>i
    bt_reflect  :: i=>i

primrec
  "n_nodes(Lf) = 0"
  "n_nodes(Br(a,l,r)) = succ(n_nodes(l) #+ n_nodes(r))"

primrec
  "n_leaves(Lf) = 1"
  "n_leaves(Br(a,l,r)) = n_leaves(l) #+ n_leaves(r)"

primrec
  "bt_reflect(Lf) = Lf"
  "bt_reflect(Br(a,l,r)) = Br(a, bt_reflect(r), bt_reflect(l))"

end
