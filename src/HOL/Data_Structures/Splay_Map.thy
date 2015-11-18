(* Author: Tobias Nipkow *)

section "Splay Tree Implementation of Maps"

theory Splay_Map
imports
  Splay_Set
  Map_by_Ordered
begin

function splay :: "'a::linorder \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree" where
"splay x Leaf = Leaf" |
"x = fst a \<Longrightarrow> splay x (Node t1 a t2) = Node t1 a t2" |
"x = fst a \<Longrightarrow> x < fst b \<Longrightarrow> splay x (Node (Node t1 a t2) b t3) = Node t1 a (Node t2 b t3)" |
"x < fst a \<Longrightarrow> splay x (Node Leaf a t) = Node Leaf a t" |
"x < fst a \<Longrightarrow> x < fst b \<Longrightarrow> splay x (Node (Node Leaf a t1) b t2) = Node Leaf a (Node t1 b t2)" |
"x < fst a \<Longrightarrow> x < fst b \<Longrightarrow> t1 \<noteq> Leaf \<Longrightarrow>
 splay x (Node (Node t1 a t2) b t3) =
 (case splay x t1 of Node t11 y t12 \<Rightarrow> Node t11 y (Node t12 a (Node t2 b t3)))" |
"fst a < x \<Longrightarrow> x < fst b \<Longrightarrow> splay x (Node (Node t1 a Leaf) b t2) = Node t1 a (Node Leaf b t2)" |
"fst a < x \<Longrightarrow> x < fst b \<Longrightarrow> t2 \<noteq> Leaf \<Longrightarrow>
 splay x (Node (Node t1 a t2) b t3) =
 (case splay x t2 of Node t21 y t22 \<Rightarrow> Node (Node t1 a t21) y (Node t22 b t3))" |
"fst a < x \<Longrightarrow> x = fst b \<Longrightarrow> splay x (Node t1 a (Node t2 b t3)) = Node (Node t1 a t2) b t3" |
"fst a < x \<Longrightarrow> splay x (Node t a Leaf) = Node t a Leaf" |
"fst a < x \<Longrightarrow> x < fst b \<Longrightarrow>  t2 \<noteq> Leaf \<Longrightarrow>
 splay x (Node t1 a (Node t2 b t3)) =
 (case splay x t2 of Node t21 y t22 \<Rightarrow> Node (Node t1 a t21) y (Node t22 b t3))" |
"fst a < x \<Longrightarrow> x < fst b \<Longrightarrow> splay x (Node t1 a (Node Leaf b t2)) = Node (Node t1 a Leaf) b t2" |
"fst a < x \<Longrightarrow> fst b < x \<Longrightarrow> splay x (Node t1 a (Node t2 b Leaf)) = Node (Node t1 a t2) b Leaf" |
"fst a < x \<Longrightarrow> fst b < x \<Longrightarrow> t3 \<noteq> Leaf \<Longrightarrow>
 splay x (Node t1 a (Node t2 b t3)) =
 (case splay x t3 of Node t31 y t32 \<Rightarrow> Node (Node (Node t1 a t2) b t31) y t32)"
apply(atomize_elim)
apply(auto)
(* 1 subgoal *)
apply (subst (asm) neq_Leaf_iff)
apply(auto)
apply (metis tree.exhaust surj_pair less_linear)+
done

termination splay
by lexicographic_order

lemma splay_code: "splay (x::_::cmp) t = (case t of Leaf \<Rightarrow> Leaf |
  Node al a ar \<Rightarrow> (case cmp x (fst a) of
    EQ \<Rightarrow> t |
    LT \<Rightarrow> (case al of
      Leaf \<Rightarrow> t |
      Node bl b br \<Rightarrow> (case cmp x (fst b) of
        EQ \<Rightarrow> Node bl b (Node br a ar) |
        LT \<Rightarrow> if bl = Leaf then Node bl b (Node br a ar)
              else case splay x bl of
                Node bll y blr \<Rightarrow> Node bll y (Node blr b (Node br a ar)) |
        GT \<Rightarrow> if br = Leaf then Node bl b (Node br a ar)
              else case splay x br of
                Node brl y brr \<Rightarrow> Node (Node bl b brl) y (Node brr a ar))) |
    GT \<Rightarrow> (case ar of
      Leaf \<Rightarrow> t |
      Node bl b br \<Rightarrow> (case cmp x (fst b) of
        EQ \<Rightarrow> Node (Node al a bl) b br |
        LT \<Rightarrow> if bl = Leaf then Node (Node al a bl) b br
              else case splay x bl of
                Node bll y blr \<Rightarrow> Node (Node al a bll) y (Node blr b br) |
        GT \<Rightarrow> if br=Leaf then Node (Node al a bl) b br
              else case splay x br of
                Node bll y blr \<Rightarrow> Node (Node (Node al a bl) b bll) y blr))))"
by(auto cong: case_tree_cong split: tree.split)

definition lookup :: "('a*'b)tree \<Rightarrow> 'a::linorder \<Rightarrow> 'b option" where "lookup t x =
  (case splay x t of Leaf \<Rightarrow> None | Node _ (a,b) _ \<Rightarrow> if x=a then Some b else None)"

hide_const (open) insert

fun update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree" where
"update x y t =  (if t = Leaf then Node Leaf (x,y) Leaf
  else case splay x t of
    Node l a r \<Rightarrow> if x = fst a then Node l (x,y) r
      else if x < fst a then Node l (x,y) (Node Leaf a r) else Node (Node l a Leaf) (x,y) r)"

definition delete :: "'a::linorder \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree" where
"delete x t = (if t = Leaf then Leaf
  else case splay x t of Node l a r \<Rightarrow>
    if x = fst a
    then if l = Leaf then r else case splay_max l of Node l' m r' \<Rightarrow> Node l' m r
    else Node l a r)"


subsection "Functional Correctness Proofs"

lemma splay_Leaf_iff: "(splay x t = Leaf) = (t = Leaf)"
by(induction x t rule: splay.induct) (auto split: tree.splits)


subsubsection "Proofs for lookup"

lemma splay_map_of_inorder:
  "splay x t = Node l a r \<Longrightarrow> sorted1(inorder t) \<Longrightarrow>
   map_of (inorder t) x = (if x = fst a then Some(snd a) else None)"
by(induction x t arbitrary: l a r rule: splay.induct)
  (auto simp: map_of_simps splay_Leaf_iff split: tree.splits)

lemma lookup_eq:
  "sorted1(inorder t) \<Longrightarrow> lookup t x = map_of (inorder t) x"
by(auto simp: lookup_def splay_Leaf_iff splay_map_of_inorder split: tree.split)


subsubsection "Proofs for update"

lemma inorder_splay: "inorder(splay x t) = inorder t"
by(induction x t rule: splay.induct)
  (auto simp: neq_Leaf_iff split: tree.split)

lemma sorted_splay:
  "sorted1(inorder t) \<Longrightarrow> splay x t = Node l a r \<Longrightarrow>
  sorted(map fst (inorder l) @ x # map fst (inorder r))"
unfolding inorder_splay[of x t, symmetric]
by(induction x t arbitrary: l a r rule: splay.induct)
  (auto simp: sorted_lems sorted_Cons_le sorted_snoc_le splay_Leaf_iff split: tree.splits)

lemma inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update x y t) = upd_list x y (inorder t)"
using inorder_splay[of x t, symmetric] sorted_splay[of t x]
by(auto simp: upd_list_simps upd_list_Cons upd_list_snoc neq_Leaf_iff split: tree.split)


subsubsection "Proofs for delete"

lemma inorder_splay_maxD:
  "splay_max t = Node l a r \<Longrightarrow> sorted1(inorder t) \<Longrightarrow>
  inorder l @ [a] = inorder t \<and> r = Leaf"
by(induction t arbitrary: l a r rule: splay_max.induct)
  (auto simp: sorted_lems splay_max_Leaf_iff split: tree.splits if_splits)

lemma inorder_delete:
  "sorted1(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
using inorder_splay[of x t, symmetric] sorted_splay[of t x]
by (auto simp: del_list_simps del_list_sorted_app delete_def
  del_list_notin_Cons inorder_splay_maxD splay_Leaf_iff splay_max_Leaf_iff
  split: tree.splits)


subsubsection "Overall Correctness"

interpretation Map_by_Ordered
where empty = Leaf and lookup = lookup and update = update
and delete = delete and inorder = inorder and inv = "\<lambda>_. True"
proof (standard, goal_cases)
  case 2 thus ?case by(simp add: lookup_eq)
next
  case 3 thus ?case by(simp add: inorder_update del: update.simps)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed auto

end
