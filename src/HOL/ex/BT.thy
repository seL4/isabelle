(*  Title:      HOL/ex/BT.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Binary trees
*)

header {* Binary trees *}

theory BT imports Main begin

datatype 'a bt =
    Lf
  | Br 'a  "'a bt"  "'a bt"

primrec n_nodes :: "'a bt => nat" where
  "n_nodes Lf = 0"
| "n_nodes (Br a t1 t2) = Suc (n_nodes t1 + n_nodes t2)"

primrec n_leaves :: "'a bt => nat" where
  "n_leaves Lf = Suc 0"
| "n_leaves (Br a t1 t2) = n_leaves t1 + n_leaves t2"

primrec depth :: "'a bt => nat" where
  "depth Lf = 0"
| "depth (Br a t1 t2) = Suc (max (depth t1) (depth t2))"

primrec reflect :: "'a bt => 'a bt" where
  "reflect Lf = Lf"
| "reflect (Br a t1 t2) = Br a (reflect t2) (reflect t1)"

primrec bt_map :: "('a => 'b) => ('a bt => 'b bt)" where
  "bt_map f Lf = Lf"
| "bt_map f (Br a t1 t2) = Br (f a) (bt_map f t1) (bt_map f t2)"

primrec preorder :: "'a bt => 'a list" where
  "preorder Lf = []"
| "preorder (Br a t1 t2) = [a] @ (preorder t1) @ (preorder t2)"

primrec inorder :: "'a bt => 'a list" where
  "inorder Lf = []"
| "inorder (Br a t1 t2) = (inorder t1) @ [a] @ (inorder t2)"

primrec postorder :: "'a bt => 'a list" where
  "postorder Lf = []"
| "postorder (Br a t1 t2) = (postorder t1) @ (postorder t2) @ [a]"

primrec append :: "'a bt => 'a bt => 'a bt" where
  "append Lf t = t"
| "append (Br a t1 t2) t = Br a (append t1 t) (append t2 t)"

text {* \medskip BT simplification *}

lemma n_leaves_reflect: "n_leaves (reflect t) = n_leaves t"
  apply (induct t)
   apply auto
  done

lemma n_nodes_reflect: "n_nodes (reflect t) = n_nodes t"
  apply (induct t)
   apply auto
  done

lemma depth_reflect: "depth (reflect t) = depth t"
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

lemma preorder_bt_map: "preorder (bt_map f t) = map f (preorder t)"
  apply (induct t)
   apply simp_all
  done

lemma inorder_bt_map: "inorder (bt_map f t) = map f (inorder t)"
  apply (induct t)
   apply simp_all
  done

lemma postorder_bt_map: "postorder (bt_map f t) = map f (postorder t)"
  apply (induct t)
   apply simp_all
  done

lemma depth_bt_map [simp]: "depth (bt_map f t) = depth t"
  apply (induct t)
   apply simp_all
  done

lemma n_leaves_bt_map [simp]: "n_leaves (bt_map f t) = n_leaves t"
  apply (induct t)
   apply (simp_all add: distrib_right)
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

text {*
 Analogues of the standard properties of the append function for lists.
*}

lemma append_assoc [simp]:
     "append (append t1 t2) t3 = append t1 (append t2 t3)"
  apply (induct t1)
   apply simp_all
  done

lemma append_Lf2 [simp]: "append t Lf = t"
  apply (induct t)
   apply simp_all
  done

lemma depth_append [simp]: "depth (append t1 t2) = depth t1 + depth t2"
  apply (induct t1)
   apply (simp_all add: max_add_distrib_left)
  done

lemma n_leaves_append [simp]:
     "n_leaves (append t1 t2) = n_leaves t1 * n_leaves t2"
  apply (induct t1)
   apply (simp_all add: distrib_right)
  done

lemma bt_map_append:
     "bt_map f (append t1 t2) = append (bt_map f t1) (bt_map f t2)"
  apply (induct t1)
   apply simp_all
  done

end
