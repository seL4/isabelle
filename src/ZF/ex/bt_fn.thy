(*  Title: 	ZF/ex/bt-fn.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Binary trees
*)

BT_Fn = BT +
consts
    bt_rec    	:: "[i, i, [i,i,i,i,i]=>i] => i"
    n_nodes	:: "i=>i"
    n_leaves   	:: "i=>i"
    bt_reflect 	:: "i=>i"

rules
  bt_rec_def
    "bt_rec(t,c,h) == Vrec(t, %t g.bt_case(c, %x y z. h(x,y,z,g`y,g`z), t))"

  n_nodes_def	"n_nodes(t) == bt_rec(t,  0,  %x y z r s. succ(r#+s))"
  n_leaves_def	"n_leaves(t) == bt_rec(t,  succ(0),  %x y z r s. r#+s)"
  bt_reflect_def "bt_reflect(t) == bt_rec(t,  Lf,  %x y z r s. Br(x,s,r))"

end
