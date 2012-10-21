(*  Title:      HOL/Metis_Examples/Binary_Tree.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Metis example featuring binary trees.
*)

header {* Metis Example Featuring Binary Trees *}

theory Binary_Tree
imports Main
begin

declare [[metis_new_skolemizer]]

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
proof (induct t)
  case Lf thus ?case
  proof -
    let "?p\<^isub>1 x\<^isub>1" = "x\<^isub>1 \<noteq> n_leaves (reflect (Lf::'a bt))"
    have "\<not> ?p\<^isub>1 (Suc 0)" by (metis reflect.simps(1) n_leaves.simps(1))
    hence "\<not> ?p\<^isub>1 (n_leaves (Lf::'a bt))" by (metis n_leaves.simps(1))
    thus "n_leaves (reflect (Lf::'a bt)) = n_leaves (Lf::'a bt)" by metis
  qed
next
  case (Br a t1 t2) thus ?case
    by (metis n_leaves.simps(2) nat_add_commute reflect.simps(2))
qed

lemma n_nodes_reflect: "n_nodes (reflect t) = n_nodes t"
proof (induct t)
  case Lf thus ?case by (metis reflect.simps(1))
next
  case (Br a t1 t2) thus ?case
    by (metis add_commute n_nodes.simps(2) reflect.simps(2))
qed

lemma depth_reflect: "depth (reflect t) = depth t"
apply (induct t)
 apply (metis depth.simps(1) reflect.simps(1))
by (metis depth.simps(2) min_max.inf_sup_aci(5) reflect.simps(2))

text {*
The famous relationship between the numbers of leaves and nodes.
*}

lemma n_leaves_nodes: "n_leaves t = Suc (n_nodes t)"
apply (induct t)
 apply (metis n_leaves.simps(1) n_nodes.simps(1))
by auto

lemma reflect_reflect_ident: "reflect (reflect t) = t"
apply (induct t)
 apply (metis reflect.simps(1))
proof -
  fix a :: 'a and t1 :: "'a bt" and t2 :: "'a bt"
  assume A1: "reflect (reflect t1) = t1"
  assume A2: "reflect (reflect t2) = t2"
  have "\<And>V U. reflect (Br U V (reflect t1)) = Br U t1 (reflect V)"
    using A1 by (metis reflect.simps(2))
  hence "\<And>V U. Br U t1 (reflect (reflect V)) = reflect (reflect (Br U t1 V))"
    by (metis reflect.simps(2))
  hence "\<And>U. reflect (reflect (Br U t1 t2)) = Br U t1 t2"
    using A2 by metis
  thus "reflect (reflect (Br a t1 t2)) = Br a t1 t2" by blast
qed

lemma bt_map_ident: "bt_map (%x. x) = (%y. y)"
apply (rule ext)
apply (induct_tac y)
 apply (metis bt_map.simps(1))
by (metis bt_map.simps(2))

lemma bt_map_append: "bt_map f (append t u) = append (bt_map f t) (bt_map f u)"
apply (induct t)
 apply (metis append.simps(1) bt_map.simps(1))
by (metis append.simps(2) bt_map.simps(2))

lemma bt_map_compose: "bt_map (f o g) t = bt_map f (bt_map g t)"
apply (induct t)
 apply (metis bt_map.simps(1))
by (metis bt_map.simps(2) o_eq_dest_lhs)

lemma bt_map_reflect: "bt_map f (reflect t) = reflect (bt_map f t)"
apply (induct t)
 apply (metis bt_map.simps(1) reflect.simps(1))
by (metis bt_map.simps(2) reflect.simps(2))

lemma preorder_bt_map: "preorder (bt_map f t) = map f (preorder t)"
apply (induct t)
 apply (metis bt_map.simps(1) map.simps(1) preorder.simps(1))
by simp

lemma inorder_bt_map: "inorder (bt_map f t) = map f (inorder t)"
proof (induct t)
  case Lf thus ?case
  proof -
    have "map f [] = []" by (metis map.simps(1))
    hence "map f [] = inorder Lf" by (metis inorder.simps(1))
    hence "inorder (bt_map f Lf) = map f []" by (metis bt_map.simps(1))
    thus "inorder (bt_map f Lf) = map f (inorder Lf)" by (metis inorder.simps(1))
  qed
next
  case (Br a t1 t2) thus ?case by simp
qed

lemma postorder_bt_map: "postorder (bt_map f t) = map f (postorder t)"
apply (induct t)
 apply (metis Nil_is_map_conv bt_map.simps(1) postorder.simps(1))
by simp

lemma depth_bt_map [simp]: "depth (bt_map f t) = depth t"
apply (induct t)
 apply (metis bt_map.simps(1) depth.simps(1))
by simp

lemma n_leaves_bt_map [simp]: "n_leaves (bt_map f t) = n_leaves t"
apply (induct t)
 apply (metis bt_map.simps(1) n_leaves.simps(1))
proof -
  fix a :: 'b and t1 :: "'b bt" and t2 :: "'b bt"
  assume A1: "n_leaves (bt_map f t1) = n_leaves t1"
  assume A2: "n_leaves (bt_map f t2) = n_leaves t2"
  have "\<And>V U. n_leaves (Br U (bt_map f t1) V) = n_leaves t1 + n_leaves V"
    using A1 by (metis n_leaves.simps(2))
  hence "\<And>V U. n_leaves (bt_map f (Br U t1 V)) = n_leaves t1 + n_leaves (bt_map f V)"
    by (metis bt_map.simps(2))
  hence F1: "\<And>U. n_leaves (bt_map f (Br U t1 t2)) = n_leaves t1 + n_leaves t2"
    using A2 by metis
  have "n_leaves t1 + n_leaves t2 = n_leaves (Br a t1 t2)"
    by (metis n_leaves.simps(2))
  thus "n_leaves (bt_map f (Br a t1 t2)) = n_leaves (Br a t1 t2)"
    using F1 by metis
qed

lemma preorder_reflect: "preorder (reflect t) = rev (postorder t)"
apply (induct t)
 apply (metis Nil_is_rev_conv postorder.simps(1) preorder.simps(1)
              reflect.simps(1))
apply simp
done

lemma inorder_reflect: "inorder (reflect t) = rev (inorder t)"
apply (induct t)
 apply (metis Nil_is_rev_conv inorder.simps(1) reflect.simps(1))
by simp
(* Slow:
by (metis append.simps(1) append_eq_append_conv2 inorder.simps(2)
          reflect.simps(2) rev.simps(2) rev_append)
*)

lemma postorder_reflect: "postorder (reflect t) = rev (preorder t)"
apply (induct t)
 apply (metis Nil_is_rev_conv postorder.simps(1) preorder.simps(1)
              reflect.simps(1))
by (metis preorder_reflect reflect_reflect_ident rev_swap)

text {*
Analogues of the standard properties of the append function for lists.
*}

lemma append_assoc [simp]: "append (append t1 t2) t3 = append t1 (append t2 t3)"
apply (induct t1)
 apply (metis append.simps(1))
by (metis append.simps(2))

lemma append_Lf2 [simp]: "append t Lf = t"
apply (induct t)
 apply (metis append.simps(1))
by (metis append.simps(2))

declare max_add_distrib_left [simp]

lemma depth_append [simp]: "depth (append t1 t2) = depth t1 + depth t2"
apply (induct t1)
 apply (metis append.simps(1) depth.simps(1) plus_nat.simps(1))
by simp

lemma n_leaves_append [simp]:
     "n_leaves (append t1 t2) = n_leaves t1 * n_leaves t2"
apply (induct t1)
 apply (metis append.simps(1) n_leaves.simps(1) nat_mult_1 plus_nat.simps(1)
              Suc_eq_plus1)
by (simp add: distrib_right)

lemma (*bt_map_append:*)
     "bt_map f (append t1 t2) = append (bt_map f t1) (bt_map f t2)"
apply (induct t1)
 apply (metis append.simps(1) bt_map.simps(1))
by (metis bt_map_append)

end
