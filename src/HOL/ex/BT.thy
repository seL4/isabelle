(*  Title:      HOL/ex/BT.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Binary trees (based on the ZF version).
*)

header {* Binary trees *}

theory BT = Main:

datatype 'a bt =
    Lf
  | Br 'a  "'a bt"  "'a bt"

consts
  n_nodes :: "'a bt => nat"
  n_leaves :: "'a bt => nat"
  reflect :: "'a bt => 'a bt"
  bt_map :: "('a => 'b) => ('a bt => 'b bt)"
  preorder :: "'a bt => 'a list"
  inorder :: "'a bt => 'a list"
  postorder :: "'a bt => 'a list"

primrec
  "n_nodes (Lf) = 0"
  "n_nodes (Br a t1 t2) = Suc (n_nodes t1 + n_nodes t2)"

primrec
  "n_leaves (Lf) = Suc 0"
  "n_leaves (Br a t1 t2) = n_leaves t1 + n_leaves t2"

primrec
  "reflect (Lf) = Lf"
  "reflect (Br a t1 t2) = Br a (reflect t2) (reflect t1)"

primrec
  "bt_map f Lf = Lf"
  "bt_map f (Br a t1 t2) = Br (f a) (bt_map f t1) (bt_map f t2)"

primrec
  "preorder (Lf) = []"
  "preorder (Br a t1 t2) = [a] @ (preorder t1) @ (preorder t2)"

primrec
  "inorder (Lf) = []"
  "inorder (Br a t1 t2) = (inorder t1) @ [a] @ (inorder t2)"

primrec
  "postorder (Lf) = []"
  "postorder (Br a t1 t2) = (postorder t1) @ (postorder t2) @ [a]"


text {* \medskip BT simplification *}

lemma n_leaves_reflect: "n_leaves (reflect t) = n_leaves t"
  apply (induct t)
   apply auto
  done

lemma n_nodes_reflect: "n_nodes (reflect t) = n_nodes t"
  apply (induct t)
   apply auto
  done

text {*
  The famous relationship between the numbers of leaves and nodes.
*}

lemma n_leaves_nodes: "n_leaves t = Suc (n_nodes t)"
  apply (induct t)
   apply auto
  done

lemma reflect_reflect_ident: "reflect (reflect t) = t"
  apply (induct t)
   apply auto
  done

lemma bt_map_reflect: "bt_map f (reflect t) = reflect (bt_map f t)"
  apply (induct t)
   apply simp_all
  done

lemma inorder_bt_map: "inorder (bt_map f t) = map f (inorder t)"
  apply (induct t)
   apply simp_all
  done

lemma preorder_reflect: "preorder (reflect t) = rev (postorder t)"
  apply (induct t)
   apply simp_all
  done

lemma inorder_reflect: "inorder (reflect t) = rev (inorder t)"
  apply (induct t)
   apply simp_all
  done

lemma postorder_reflect: "postorder (reflect t) = rev (preorder t)"
  apply (induct t)
   apply simp_all
  done

end
