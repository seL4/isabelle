(*  Title: 	HOL/ex/BT.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Datatype definition of binary trees
*)

open BT;

(** BT simplification **)

val bt_ss = list_ss
    addsimps [n_nodes_Lf, n_nodes_Br,
	      n_leaves_Lf, n_leaves_Br,
	      reflect_Lf, reflect_Br,
	      bt_map_Lf, bt_map_Br,
	      preorder_Lf, preorder_Br,
	      inorder_Lf, inorder_Br,
	      postorder_Lf, postorder_Br];


goal BT.thy "n_leaves(reflect(t)) = n_leaves(t)";
by (bt.induct_tac "t" 1);
by (ALLGOALS (asm_simp_tac (bt_ss addsimps [add_commute])));
qed "n_leaves_reflect";

goal BT.thy "n_nodes(reflect(t)) = n_nodes(t)";
by (bt.induct_tac "t" 1);
by (ALLGOALS (asm_simp_tac (bt_ss addsimps [add_commute])));
qed "n_nodes_reflect";

(*The famous relationship between the numbers of leaves and nodes*)
goal BT.thy "n_leaves(t) = Suc(n_nodes(t))";
by (bt.induct_tac "t" 1);
by (ALLGOALS (asm_simp_tac bt_ss));
qed "n_leaves_nodes";

goal BT.thy "reflect(reflect(t))=t";
by (bt.induct_tac "t" 1);
by (ALLGOALS (asm_simp_tac bt_ss));
qed "reflect_reflect_ident";

goal BT.thy "bt_map f (reflect t) = reflect (bt_map f t)";
by (bt.induct_tac "t" 1);
by (ALLGOALS (asm_simp_tac bt_ss));
qed "bt_map_reflect";

goal BT.thy "inorder (bt_map f t) = map f (inorder t)";
by (bt.induct_tac "t" 1);
by (ALLGOALS (asm_simp_tac bt_ss));
qed "inorder_bt_map";

goal BT.thy "preorder (reflect t) = rev (postorder t)";
by (bt.induct_tac "t" 1);
by (ALLGOALS (asm_simp_tac (bt_ss addsimps [rev_append])));
qed "preorder_reflect";

goal BT.thy "inorder (reflect t) = rev (inorder t)";
by (bt.induct_tac "t" 1);
by (ALLGOALS (asm_simp_tac (bt_ss addsimps [rev_append])));
qed "inorder_reflect";

goal BT.thy "postorder (reflect t) = rev (preorder t)";
by (bt.induct_tac "t" 1);
by (ALLGOALS (asm_simp_tac (bt_ss addsimps [rev_append])));
qed "postorder_reflect";


