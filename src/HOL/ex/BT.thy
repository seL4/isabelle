(*  Title: 	HOL/ex/BT.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Binary trees (based on the ZF version)
*)

BT = List +

datatype 'a bt = Lf  |  Br 'a ('a bt) ('a bt)
  
consts
    n_nodes	:: 'a bt => nat
    n_leaves   	:: 'a bt => nat
    reflect 	:: 'a bt => 'a bt
    bt_map      :: ('a=>'b) => ('a bt => 'b bt)
    preorder    :: 'a bt => 'a list
    inorder     :: 'a bt => 'a list
    postorder   :: 'a bt => 'a list

primrec n_nodes bt
  n_nodes_Lf "n_nodes (Lf) = 0"
  n_nodes_Br "n_nodes (Br a t1 t2) = Suc(n_nodes t1 + n_nodes t2)"

primrec n_leaves bt
  n_leaves_Lf "n_leaves (Lf) = Suc 0"
  n_leaves_Br "n_leaves (Br a t1 t2) = n_leaves t1 + n_leaves t2"

primrec reflect bt
  reflect_Lf "reflect (Lf) = Lf"
  reflect_Br "reflect (Br a t1 t2) = Br a (reflect t2) (reflect t1)"

primrec bt_map bt
  bt_map_Lf  "bt_map f Lf = Lf"
  bt_map_Br  "bt_map f (Br a t1 t2) = Br (f a) (bt_map f t1) (bt_map f t2)"

primrec preorder bt
  preorder_Lf "preorder (Lf) = []"
  preorder_Br "preorder (Br a t1 t2) = [a] @ (preorder t1) @ (preorder t2)"

primrec inorder bt
  inorder_Lf "inorder (Lf) = []"
  inorder_Br "inorder (Br a t1 t2) = (inorder t1) @ [a] @ (inorder t2)"

primrec postorder bt
  postorder_Lf "postorder (Lf) = []"
  postorder_Br "postorder (Br a t1 t2) = (postorder t1) @ (postorder t2) @ [a]"

end
