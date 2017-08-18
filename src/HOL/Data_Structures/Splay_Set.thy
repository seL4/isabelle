(*
Author: Tobias Nipkow
Function follow AFP entry Splay_Tree, proofs are new.
*)

section "Splay Tree Implementation of Sets"

theory Splay_Set
imports
  "HOL-Library.Tree"
  Set_by_Ordered
  Cmp
begin

function splay :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"splay a Leaf = Leaf" |
"splay a (Node t1 a t2) = Node t1 a t2" |
"a<b \<Longrightarrow> splay a (Node (Node t1 a t2) b t3) = Node t1 a (Node t2 b t3)" |
"x<a \<Longrightarrow> splay x (Node Leaf a t) = Node Leaf a t" |
"x<a \<Longrightarrow> x<b \<Longrightarrow> splay x (Node (Node Leaf a t1) b t2) = Node Leaf a (Node t1 b t2)" |
"x<a \<Longrightarrow> x<b \<Longrightarrow> t1 \<noteq> Leaf \<Longrightarrow>
 splay x (Node (Node t1 a t2) b t3) =
 (case splay x t1 of Node t11 y t12 \<Rightarrow> Node t11 y (Node t12 a (Node t2 b t3)))" |
"a<x \<Longrightarrow> x<b \<Longrightarrow> splay x (Node (Node t1 a Leaf) b t2) = Node t1 a (Node Leaf b t2)" |
"a<x \<Longrightarrow> x<b \<Longrightarrow> t2 \<noteq> Leaf \<Longrightarrow>
 splay x (Node (Node t1 a t2) b t3) =
 (case splay x t2 of Node t21 y t22 \<Rightarrow> Node (Node t1 a t21) y (Node t22 b t3))" |
"a<b \<Longrightarrow> splay b (Node t1 a (Node t2 b t3)) = Node (Node t1 a t2) b t3" |
"a<x \<Longrightarrow> splay x (Node t a Leaf) = Node t a Leaf" |
"a<x \<Longrightarrow> x<b \<Longrightarrow>  t2 \<noteq> Leaf \<Longrightarrow>
 splay x (Node t1 a (Node t2 b t3)) =
 (case splay x t2 of Node t21 y t22 \<Rightarrow> Node (Node t1 a t21) y (Node t22 b t3))" |
"a<x \<Longrightarrow> x<b \<Longrightarrow> splay x (Node t1 a (Node Leaf b t2)) = Node (Node t1 a Leaf) b t2" |
"a<x \<Longrightarrow> b<x \<Longrightarrow> splay x (Node t1 a (Node t2 b Leaf)) = Node (Node t1 a t2) b Leaf" |
"a<x \<Longrightarrow> b<x \<Longrightarrow>  t3 \<noteq> Leaf \<Longrightarrow>
 splay x (Node t1 a (Node t2 b t3)) =
 (case splay x t3 of Node t31 y t32 \<Rightarrow> Node (Node (Node t1 a t2) b t31) y t32)"
apply(atomize_elim)
apply(auto)
(* 1 subgoal *)
apply (subst (asm) neq_Leaf_iff)
apply(auto)
apply (metis tree.exhaust less_linear)+
done

termination splay
by lexicographic_order

(* no idea why this speeds things up below *)
lemma case_tree_cong:
  "\<lbrakk> x = x'; y = y'; z = z' \<rbrakk> \<Longrightarrow> case_tree x y z = case_tree x' y' z'"
by auto

lemma splay_code: "splay (x::_::linorder) t = (case t of Leaf \<Rightarrow> Leaf |
  Node al a ar \<Rightarrow> (case cmp x a of
    EQ \<Rightarrow> t |
    LT \<Rightarrow> (case al of
      Leaf \<Rightarrow> t |
      Node bl b br \<Rightarrow> (case cmp x b of
        EQ \<Rightarrow> Node bl b (Node br a ar) |
        LT \<Rightarrow> if bl = Leaf then Node bl b (Node br a ar)
              else case splay x bl of
                Node bll y blr \<Rightarrow> Node bll y (Node blr b (Node br a ar)) |
        GT \<Rightarrow> if br = Leaf then Node bl b (Node br a ar)
              else case splay x br of
                Node brl y brr \<Rightarrow> Node (Node bl b brl) y (Node brr a ar))) |
    GT \<Rightarrow> (case ar of
      Leaf \<Rightarrow> t |
      Node bl b br \<Rightarrow> (case cmp x b of
        EQ \<Rightarrow> Node (Node al a bl) b br |
        LT \<Rightarrow> if bl = Leaf then Node (Node al a bl) b br
              else case splay x bl of
                Node bll y blr \<Rightarrow> Node (Node al a bll) y (Node blr b br) |
        GT \<Rightarrow> if br=Leaf then Node (Node al a bl) b br
              else case splay x br of
                Node bll y blr \<Rightarrow> Node (Node (Node al a bl) b bll) y blr))))"
by(auto cong: case_tree_cong split: tree.split)

definition is_root :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool" where
"is_root x t = (case t of Leaf \<Rightarrow> False | Node l a r \<Rightarrow> x = a)"

definition "isin t x = is_root x (splay x t)"

hide_const (open) insert

fun insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert x t =
  (if t = Leaf then Node Leaf x Leaf
   else case splay x t of
     Node l a r \<Rightarrow>
      case cmp x a of
        EQ \<Rightarrow> Node l a r |
        LT \<Rightarrow> Node l x (Node Leaf a r) |
        GT \<Rightarrow> Node (Node l a Leaf) x r)"


fun splay_max :: "'a tree \<Rightarrow> 'a tree" where
"splay_max Leaf = Leaf" |
"splay_max (Node l b Leaf) = Node l b Leaf" |
"splay_max (Node l b (Node rl c rr)) =
  (if rr = Leaf then Node (Node l b rl) c Leaf
   else case splay_max rr of
     Node rrl m rrr \<Rightarrow> Node (Node (Node l b rl) c rrl) m rrr)"


definition delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"delete x t =
  (if t = Leaf then Leaf
   else case splay x t of Node l a r \<Rightarrow>
     if x = a
     then if l = Leaf then r else case splay_max l of Node l' m r' \<Rightarrow> Node l' m r
     else Node l a r)"


subsection "Functional Correctness Proofs"

lemma splay_Leaf_iff: "(splay a t = Leaf) = (t = Leaf)"
by(induction a t rule: splay.induct) (auto split: tree.splits)

lemma splay_max_Leaf_iff: "(splay_max t = Leaf) = (t = Leaf)"
by(induction t rule: splay_max.induct)(auto split: tree.splits)


subsubsection "Proofs for isin"

lemma
  "splay x t = Node l a r \<Longrightarrow> sorted(inorder t) \<Longrightarrow>
  x \<in> elems (inorder t) \<longleftrightarrow> x=a"
by(induction x t arbitrary: l a r rule: splay.induct)
  (auto simp: elems_simps1 splay_Leaf_iff ball_Un split: tree.splits)

lemma splay_elemsD:
  "splay x t = Node l a r \<Longrightarrow> sorted(inorder t) \<Longrightarrow>
  x \<in> elems (inorder t) \<longleftrightarrow> x=a"
by(induction x t arbitrary: l a r rule: splay.induct)
  (auto simp: elems_simps2 splay_Leaf_iff split: tree.splits)

lemma isin_set: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> elems (inorder t))"
by (auto simp: isin_def is_root_def splay_elemsD splay_Leaf_iff split: tree.splits)


subsubsection "Proofs for insert"

lemma inorder_splay: "inorder(splay x t) = inorder t"
by(induction x t rule: splay.induct)
  (auto simp: neq_Leaf_iff split: tree.split)

lemma sorted_splay:
  "sorted(inorder t) \<Longrightarrow> splay x t = Node l a r \<Longrightarrow>
  sorted(inorder l @ x # inorder r)"
unfolding inorder_splay[of x t, symmetric]
by(induction x t arbitrary: l a r rule: splay.induct)
  (auto simp: sorted_lems sorted_Cons_le sorted_snoc_le splay_Leaf_iff split: tree.splits)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
using inorder_splay[of x t, symmetric] sorted_splay[of t x]
by(auto simp: ins_list_simps ins_list_Cons ins_list_snoc neq_Leaf_iff split: tree.split)


subsubsection "Proofs for delete"

lemma inorder_splay_maxD:
  "splay_max t = Node l a r \<Longrightarrow> sorted(inorder t) \<Longrightarrow>
  inorder l @ [a] = inorder t \<and> r = Leaf"
by(induction t arbitrary: l a r rule: splay_max.induct)
  (auto simp: sorted_lems splay_max_Leaf_iff split: tree.splits if_splits)

lemma inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
using inorder_splay[of x t, symmetric] sorted_splay[of t x]
by (auto simp: del_list_simps del_list_sorted_app delete_def
  del_list_notin_Cons inorder_splay_maxD splay_Leaf_iff splay_max_Leaf_iff
  split: tree.splits)


subsubsection "Overall Correctness"

interpretation Set_by_Ordered
where empty = Leaf and isin = isin and insert = insert
and delete = delete and inorder = inorder and inv = "\<lambda>_. True"
proof (standard, goal_cases)
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert del: insert.simps)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed auto

end
