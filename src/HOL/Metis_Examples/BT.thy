(*  Title:      HOL/MetisTest/BT.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

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

declare [[ atp_problem_prefix = "BT__n_nodes_reflect" ]]

lemma n_nodes_reflect: "n_nodes (reflect t) = n_nodes t"
proof (induct t)
  case Lf thus ?case by (metis reflect.simps(1))
next
  case (Br a t1 t2) thus ?case
    by (metis class_semiring.semiring_rules(24) n_nodes.simps(2) reflect.simps(2))
qed

declare [[ atp_problem_prefix = "BT__depth_reflect" ]]

lemma depth_reflect: "depth (reflect t) = depth t"
apply (induct t)
 apply (metis depth.simps(1) reflect.simps(1))
by (metis depth.simps(2) min_max.inf_sup_aci(5) reflect.simps(2))

text {*
The famous relationship between the numbers of leaves and nodes.
*}

declare [[ atp_problem_prefix = "BT__n_leaves_nodes" ]]

lemma n_leaves_nodes: "n_leaves t = Suc (n_nodes t)"
apply (induct t)
 apply (metis n_leaves.simps(1) n_nodes.simps(1))
by auto

declare [[ atp_problem_prefix = "BT__reflect_reflect_ident" ]]

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

declare [[ atp_problem_prefix = "BT__bt_map_ident" ]]

lemma bt_map_ident: "bt_map (%x. x) = (%y. y)"
apply (rule ext) 
apply (induct_tac y)
 apply (metis bt_map.simps(1))
by (metis COMBI_def bt_map.simps(2))

declare [[ atp_problem_prefix = "BT__bt_map_appnd" ]]

lemma bt_map_appnd: "bt_map f (appnd t u) = appnd (bt_map f t) (bt_map f u)"
apply (induct t)
 apply (metis appnd.simps(1) bt_map.simps(1))
by (metis appnd.simps(2) bt_map.simps(2))

declare [[ atp_problem_prefix = "BT__bt_map_compose" ]]

lemma bt_map_compose: "bt_map (f o g) t = bt_map f (bt_map g t)"
apply (induct t)
 apply (metis bt_map.simps(1))
by (metis bt_map.simps(2) o_eq_dest_lhs)

declare [[ atp_problem_prefix = "BT__bt_map_reflect" ]]

lemma bt_map_reflect: "bt_map f (reflect t) = reflect (bt_map f t)"
apply (induct t)
 apply (metis bt_map.simps(1) reflect.simps(1))
by (metis bt_map.simps(2) reflect.simps(2))

declare [[ atp_problem_prefix = "BT__preorder_bt_map" ]]

lemma preorder_bt_map: "preorder (bt_map f t) = map f (preorder t)"
apply (induct t)
 apply (metis bt_map.simps(1) map.simps(1) preorder.simps(1))
by simp

declare [[ atp_problem_prefix = "BT__inorder_bt_map" ]]

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

declare [[ atp_problem_prefix = "BT__postorder_bt_map" ]]

lemma postorder_bt_map: "postorder (bt_map f t) = map f (postorder t)"
apply (induct t)
 apply (metis Nil_is_map_conv bt_map.simps(1) postorder.simps(1))
by simp

declare [[ atp_problem_prefix = "BT__depth_bt_map" ]]

lemma depth_bt_map [simp]: "depth (bt_map f t) = depth t"
apply (induct t)
 apply (metis bt_map.simps(1) depth.simps(1))
by simp

declare [[ atp_problem_prefix = "BT__n_leaves_bt_map" ]]

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

declare [[ atp_problem_prefix = "BT__preorder_reflect" ]]

lemma preorder_reflect: "preorder (reflect t) = rev (postorder t)"
apply (induct t)
 apply (metis Nil_is_rev_conv postorder.simps(1) preorder.simps(1)
              reflect.simps(1))
by (metis append.simps(1) append.simps(2) postorder.simps(2) preorder.simps(2)
          reflect.simps(2) rev.simps(2) rev_append rev_swap)

declare [[ atp_problem_prefix = "BT__inorder_reflect" ]]

lemma inorder_reflect: "inorder (reflect t) = rev (inorder t)"
apply (induct t)
 apply (metis Nil_is_rev_conv inorder.simps(1) reflect.simps(1))
by simp
(* Slow:
by (metis append.simps(1) append_eq_append_conv2 inorder.simps(2)
          reflect.simps(2) rev.simps(2) rev_append)
*)

declare [[ atp_problem_prefix = "BT__postorder_reflect" ]]

lemma postorder_reflect: "postorder (reflect t) = rev (preorder t)"
apply (induct t)
 apply (metis Nil_is_rev_conv postorder.simps(1) preorder.simps(1)
              reflect.simps(1))
by (metis preorder_reflect reflect_reflect_ident rev_swap)

text {*
Analogues of the standard properties of the append function for lists.
*}

declare [[ atp_problem_prefix = "BT__appnd_assoc" ]]

lemma appnd_assoc [simp]: "appnd (appnd t1 t2) t3 = appnd t1 (appnd t2 t3)"
apply (induct t1)
 apply (metis appnd.simps(1))
by (metis appnd.simps(2))

declare [[ atp_problem_prefix = "BT__appnd_Lf2" ]]

lemma appnd_Lf2 [simp]: "appnd t Lf = t"
apply (induct t)
 apply (metis appnd.simps(1))
by (metis appnd.simps(2))

declare max_add_distrib_left [simp]

declare [[ atp_problem_prefix = "BT__depth_appnd" ]]

lemma depth_appnd [simp]: "depth (appnd t1 t2) = depth t1 + depth t2"
apply (induct t1)
 apply (metis appnd.simps(1) depth.simps(1) plus_nat.simps(1))
by simp

declare [[ atp_problem_prefix = "BT__n_leaves_appnd" ]]

lemma n_leaves_appnd [simp]:
     "n_leaves (appnd t1 t2) = n_leaves t1 * n_leaves t2"
apply (induct t1)
 apply (metis appnd.simps(1) n_leaves.simps(1) nat_mult_1 plus_nat.simps(1)
              semiring_norm(111))
by (simp add: left_distrib)

declare [[ atp_problem_prefix = "BT__bt_map_appnd" ]]

lemma (*bt_map_appnd:*)
     "bt_map f (appnd t1 t2) = appnd (bt_map f t1) (bt_map f t2)"
apply (induct t1)
 apply (metis appnd.simps(1) bt_map.simps(1))
by (metis bt_map_appnd)

end
