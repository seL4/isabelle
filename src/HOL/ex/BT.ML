(*  Title:      HOL/ex/BT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Datatype definition of binary trees
*)

(** BT simplification **)

Goal "n_leaves(reflect(t)) = n_leaves(t)";
by (induct_tac "t" 1);
by Auto_tac;
qed "n_leaves_reflect";

Goal "n_nodes(reflect(t)) = n_nodes(t)";
by (induct_tac "t" 1);
by Auto_tac;
qed "n_nodes_reflect";

(*The famous relationship between the numbers of leaves and nodes*)
Goal "n_leaves(t) = Suc(n_nodes(t))";
by (induct_tac "t" 1);
by Auto_tac;
qed "n_leaves_nodes";

Goal "reflect(reflect(t))=t";
by (induct_tac "t" 1);
by Auto_tac;
qed "reflect_reflect_ident";

Goal "bt_map f (reflect t) = reflect (bt_map f t)";
by (induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "bt_map_reflect";

Goal "inorder (bt_map f t) = map f (inorder t)";
by (induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "inorder_bt_map";

Goal "preorder (reflect t) = rev (postorder t)";
by (induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "preorder_reflect";

Goal "inorder (reflect t) = rev (inorder t)";
by (induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "inorder_reflect";

Goal "postorder (reflect t) = rev (preorder t)";
by (induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "postorder_reflect";


