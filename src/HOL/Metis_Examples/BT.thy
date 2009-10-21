(*  Title:      HOL/MetisTest/BT.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Testing the metis method
*)

header {* Binary trees *}

theory BT
imports Main
begin


datatype 'a bt =
    Lf
  | Br 'a  "'a bt"  "'a bt"

consts
  n_nodes   :: "'a bt => nat"
  n_leaves  :: "'a bt => nat"
  depth     :: "'a bt => nat"
  reflect   :: "'a bt => 'a bt"
  bt_map    :: "('a => 'b) => ('a bt => 'b bt)"
  preorder  :: "'a bt => 'a list"
  inorder   :: "'a bt => 'a list"
  postorder :: "'a bt => 'a list"
  appnd    :: "'a bt => 'a bt => 'a bt"

primrec
  "n_nodes Lf = 0"
  "n_nodes (Br a t1 t2) = Suc (n_nodes t1 + n_nodes t2)"

primrec
  "n_leaves Lf = Suc 0"
  "n_leaves (Br a t1 t2) = n_leaves t1 + n_leaves t2"

primrec
  "depth Lf = 0"
  "depth (Br a t1 t2) = Suc (max (depth t1) (depth t2))"

primrec
  "reflect Lf = Lf"
  "reflect (Br a t1 t2) = Br a (reflect t2) (reflect t1)"

primrec
  "bt_map f Lf = Lf"
  "bt_map f (Br a t1 t2) = Br (f a) (bt_map f t1) (bt_map f t2)"

primrec
  "preorder Lf = []"
  "preorder (Br a t1 t2) = [a] @ (preorder t1) @ (preorder t2)"

primrec
  "inorder Lf = []"
  "inorder (Br a t1 t2) = (inorder t1) @ [a] @ (inorder t2)"

primrec
  "postorder Lf = []"
  "postorder (Br a t1 t2) = (postorder t1) @ (postorder t2) @ [a]"

primrec
  "appnd Lf t = t"
  "appnd (Br a t1 t2) t = Br a (appnd t1 t) (appnd t2 t)"


text {* \medskip BT simplification *}

declare [[ atp_problem_prefix = "BT__n_leaves_reflect" ]]
lemma n_leaves_reflect: "n_leaves (reflect t) = n_leaves t"
  apply (induct t)
  apply (metis add_right_cancel n_leaves.simps(1) reflect.simps(1))
  apply (metis add_commute n_leaves.simps(2) reflect.simps(2))
  done

declare [[ atp_problem_prefix = "BT__n_nodes_reflect" ]]
lemma n_nodes_reflect: "n_nodes (reflect t) = n_nodes t"
  apply (induct t)
  apply (metis reflect.simps(1))
  apply (metis n_nodes.simps(2) nat_add_commute reflect.simps(2))
  done

declare [[ atp_problem_prefix = "BT__depth_reflect" ]]
lemma depth_reflect: "depth (reflect t) = depth t"
  apply (induct t)
  apply (metis depth.simps(1) reflect.simps(1))
  apply (metis depth.simps(2) min_max.sup_commute reflect.simps(2))
  done

text {*
  The famous relationship between the numbers of leaves and nodes.
*}

declare [[ atp_problem_prefix = "BT__n_leaves_nodes" ]]
lemma n_leaves_nodes: "n_leaves t = Suc (n_nodes t)"
  apply (induct t)
  apply (metis n_leaves.simps(1) n_nodes.simps(1))
  apply auto
  done

declare [[ atp_problem_prefix = "BT__reflect_reflect_ident" ]]
lemma reflect_reflect_ident: "reflect (reflect t) = t"
  apply (induct t)
  apply (metis add_right_cancel reflect.simps(1));
  apply (metis reflect.simps(2))
  done

declare [[ atp_problem_prefix = "BT__bt_map_ident" ]]
lemma bt_map_ident: "bt_map (%x. x) = (%y. y)"
apply (rule ext) 
apply (induct_tac y)
  apply (metis bt_map.simps(1))
txt{*BUG involving flex-flex pairs*}
(*  apply (metis bt_map.simps(2)) *)
apply auto
done


declare [[ atp_problem_prefix = "BT__bt_map_appnd" ]]
lemma bt_map_appnd: "bt_map f (appnd t u) = appnd (bt_map f t) (bt_map f u)"
apply (induct t)
  apply (metis appnd.simps(1) bt_map.simps(1))
  apply (metis appnd.simps(2) bt_map.simps(2))  (*slow!!*)
done


declare [[ atp_problem_prefix = "BT__bt_map_compose" ]]
lemma bt_map_compose: "bt_map (f o g) t = bt_map f (bt_map g t)"
apply (induct t) 
  apply (metis bt_map.simps(1))
txt{*Metis runs forever*}
(*  apply (metis bt_map.simps(2) o_apply)*)
apply auto
done


declare [[ atp_problem_prefix = "BT__bt_map_reflect" ]]
lemma bt_map_reflect: "bt_map f (reflect t) = reflect (bt_map f t)"
  apply (induct t)
  apply (metis add_right_cancel bt_map.simps(1) reflect.simps(1))
  apply (metis add_right_cancel bt_map.simps(2) reflect.simps(2))
  done

declare [[ atp_problem_prefix = "BT__preorder_bt_map" ]]
lemma preorder_bt_map: "preorder (bt_map f t) = map f (preorder t)"
  apply (induct t)
  apply (metis bt_map.simps(1) map.simps(1) preorder.simps(1))
   apply simp
  done

declare [[ atp_problem_prefix = "BT__inorder_bt_map" ]]
lemma inorder_bt_map: "inorder (bt_map f t) = map f (inorder t)"
  apply (induct t)
  apply (metis bt_map.simps(1) inorder.simps(1) map.simps(1))
  apply simp
  done

declare [[ atp_problem_prefix = "BT__postorder_bt_map" ]]
lemma postorder_bt_map: "postorder (bt_map f t) = map f (postorder t)"
  apply (induct t)
  apply (metis bt_map.simps(1) map.simps(1) postorder.simps(1))
   apply simp
  done

declare [[ atp_problem_prefix = "BT__depth_bt_map" ]]
lemma depth_bt_map [simp]: "depth (bt_map f t) = depth t"
  apply (induct t)
  apply (metis bt_map.simps(1) depth.simps(1))
   apply simp
  done

declare [[ atp_problem_prefix = "BT__n_leaves_bt_map" ]]
lemma n_leaves_bt_map [simp]: "n_leaves (bt_map f t) = n_leaves t"
  apply (induct t)
  apply (metis One_nat_def Suc_eq_plus1 bt_map.simps(1) less_add_one less_antisym linorder_neq_iff n_leaves.simps(1))
  apply (metis bt_map.simps(2) n_leaves.simps(2))
  done


declare [[ atp_problem_prefix = "BT__preorder_reflect" ]]
lemma preorder_reflect: "preorder (reflect t) = rev (postorder t)"
  apply (induct t)
  apply (metis postorder.simps(1) preorder.simps(1) reflect.simps(1) rev_is_Nil_conv)
  apply (metis append_Nil Cons_eq_append_conv postorder.simps(2) preorder.simps(2) reflect.simps(2) rev.simps(2) rev_append rev_rev_ident)
  done

declare [[ atp_problem_prefix = "BT__inorder_reflect" ]]
lemma inorder_reflect: "inorder (reflect t) = rev (inorder t)"
  apply (induct t)
  apply (metis inorder.simps(1) reflect.simps(1) rev.simps(1))
  apply simp
  done

declare [[ atp_problem_prefix = "BT__postorder_reflect" ]]
lemma postorder_reflect: "postorder (reflect t) = rev (preorder t)"
  apply (induct t)
  apply (metis postorder.simps(1) preorder.simps(1) reflect.simps(1) rev.simps(1))
  apply (metis Cons_eq_appendI postorder.simps(2) preorder.simps(2) reflect.simps(2) rev.simps(2) rev_append self_append_conv2)
  done

text {*
 Analogues of the standard properties of the append function for lists.
*}

declare [[ atp_problem_prefix = "BT__appnd_assoc" ]]
lemma appnd_assoc [simp]:
     "appnd (appnd t1 t2) t3 = appnd t1 (appnd t2 t3)"
  apply (induct t1)
  apply (metis appnd.simps(1))
  apply (metis appnd.simps(2))
  done

declare [[ atp_problem_prefix = "BT__appnd_Lf2" ]]
lemma appnd_Lf2 [simp]: "appnd t Lf = t"
  apply (induct t)
  apply (metis appnd.simps(1))
  apply (metis appnd.simps(2))
  done

declare [[ atp_problem_prefix = "BT__depth_appnd" ]]
  declare max_add_distrib_left [simp]
lemma depth_appnd [simp]: "depth (appnd t1 t2) = depth t1 + depth t2"
  apply (induct t1)
  apply (metis add_0 appnd.simps(1) depth.simps(1))
apply (simp add: ); 
  done

declare [[ atp_problem_prefix = "BT__n_leaves_appnd" ]]
lemma n_leaves_appnd [simp]:
     "n_leaves (appnd t1 t2) = n_leaves t1 * n_leaves t2"
  apply (induct t1)
  apply (metis One_nat_def appnd.simps(1) less_irrefl less_linear n_leaves.simps(1) nat_mult_1) 
  apply (simp add: left_distrib)
  done

declare [[ atp_problem_prefix = "BT__bt_map_appnd" ]]
lemma (*bt_map_appnd:*)
     "bt_map f (appnd t1 t2) = appnd (bt_map f t1) (bt_map f t2)"
  apply (induct t1)
  apply (metis appnd.simps(1) bt_map_appnd)
  apply (metis bt_map_appnd)
  done

end
