(* Author: Tobias Nipkow *)

section \<open>A 2-3-4 Tree Implementation of Maps\<close>

theory Tree234_Map
imports
  Tree234_Set
  "../Data_Structures/Map_by_Ordered"
begin

subsection \<open>Map operations on 2-3-4 trees\<close>

fun lookup :: "('a::linorder * 'b) tree234 \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup Leaf x = None" |
"lookup (Node2 l (a,b) r) x =
  (if x < a then lookup l x else
  if a < x then lookup r x else Some b)" |
"lookup (Node3 l (a1,b1) m (a2,b2) r) x =
  (if x < a1 then lookup l x else
   if x = a1 then Some b1 else
   if x < a2 then lookup m x else
   if x = a2 then Some b2
   else lookup r x)" |
"lookup (Node4 l (a1,b1) m (a2,b2) n (a3,b3) r) x =
  (if x < a2 then
     if x = a1 then Some b1 else
     if x < a1 then lookup l x else lookup m x
   else
     if x = a2 then Some b2 else
     if x = a3 then Some b3 else
     if x < a3 then lookup n x
     else lookup r x)"

fun upd :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) tree234 \<Rightarrow> ('a*'b) up\<^sub>i" where
"upd x y Leaf = Up\<^sub>i Leaf (x,y) Leaf" |
"upd x y (Node2 l ab r) =
   (if x < fst ab then
        (case upd x y l of
           T\<^sub>i l' => T\<^sub>i (Node2 l' ab r)
         | Up\<^sub>i l1 q l2 => T\<^sub>i (Node3 l1 q l2 ab r))
    else if x = fst ab then T\<^sub>i (Node2 l (x,y) r)
    else
        (case upd x y r of
           T\<^sub>i r' => T\<^sub>i (Node2 l ab r')
         | Up\<^sub>i r1 q r2 => T\<^sub>i (Node3 l ab r1 q r2)))" |
"upd x y (Node3 l ab1 m ab2 r) =
   (if x < fst ab1 then
        (case upd x y l of
           T\<^sub>i l' => T\<^sub>i (Node3 l' ab1 m ab2 r)
         | Up\<^sub>i l1 q l2 => Up\<^sub>i (Node2 l1 q l2) ab1 (Node2 m ab2 r))
    else if x = fst ab1 then T\<^sub>i (Node3 l (x,y) m ab2 r)
    else if x < fst ab2 then
             (case upd x y m of
                T\<^sub>i m' => T\<^sub>i (Node3 l ab1 m' ab2 r)
              | Up\<^sub>i m1 q m2 => Up\<^sub>i (Node2 l ab1 m1) q (Node2 m2 ab2 r))
         else if x = fst ab2 then T\<^sub>i (Node3 l ab1 m (x,y) r)
         else
             (case upd x y r of
                T\<^sub>i r' => T\<^sub>i (Node3 l ab1 m ab2 r')
              | Up\<^sub>i r1 q r2 => Up\<^sub>i (Node2 l ab1 m) ab2 (Node2 r1 q r2)))" |
"upd x y (Node4 l ab1 m ab2 n ab3 r) =
   (if x < fst ab2 then
      if x < fst ab1 then
        (case upd x y l of
           T\<^sub>i l' => T\<^sub>i (Node4 l' ab1 m ab2 n ab3 r)
         | Up\<^sub>i l1 q l2 => Up\<^sub>i (Node2 l1 q l2) ab1 (Node3 m ab2 n ab3 r))
      else
      if x = fst ab1 then T\<^sub>i (Node4 l (x,y) m ab2 n ab3 r)
      else
        (case upd x y m of
           T\<^sub>i m' => T\<^sub>i (Node4 l ab1 m' ab2 n ab3 r)
         | Up\<^sub>i m1 q m2 => Up\<^sub>i (Node2 l ab1 m1) q (Node3 m2 ab2 n ab3 r))
    else
    if x = fst ab2 then T\<^sub>i (Node4 l ab1 m (x,y) n ab3 r) else
    if x < fst ab3 then
      (case upd x y n of
         T\<^sub>i n' => T\<^sub>i (Node4 l ab1 m ab2 n' ab3 r)
       | Up\<^sub>i n1 q n2 => Up\<^sub>i (Node2 l ab1 m) ab2(*q*) (Node3 n1 q n2 ab3 r))
    else
    if x = fst ab3 then T\<^sub>i (Node4 l ab1 m ab2 n (x,y) r)
    else
      (case upd x y r of
         T\<^sub>i r' => T\<^sub>i (Node4 l ab1 m ab2 n ab3 r')
       | Up\<^sub>i r1 q r2 => Up\<^sub>i (Node2 l ab1 m) ab2 (Node3 n ab3 r1 q r2)))"

definition update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) tree234 \<Rightarrow> ('a*'b) tree234" where
"update a b t = tree\<^sub>i(upd a b t)"

fun del :: "'a::linorder \<Rightarrow> ('a*'b) tree234 \<Rightarrow> ('a*'b) up\<^sub>d"
where
"del k Leaf = T\<^sub>d Leaf" |
"del k (Node2 Leaf p Leaf) = (if k=fst p then Up\<^sub>d Leaf else T\<^sub>d(Node2 Leaf p Leaf))" |
"del k (Node3 Leaf p Leaf q Leaf) =
  T\<^sub>d(if k=fst p then Node2 Leaf q Leaf else
     if k=fst q then Node2 Leaf p Leaf
     else Node3 Leaf p Leaf q Leaf)" |
"del k (Node4 Leaf ab1 Leaf ab2 Leaf ab3 Leaf) =
  T\<^sub>d(if k=fst ab1 then Node3 Leaf ab2 Leaf ab3 Leaf else
     if k=fst ab2 then Node3 Leaf ab1 Leaf ab3 Leaf else
     if k=fst ab3 then Node3 Leaf ab1 Leaf ab2 Leaf
     else Node4 Leaf ab1 Leaf ab2 Leaf ab3 Leaf)" |
"del k (Node2 l a r) =
  (if k<fst a then node21 (del k l) a r else
   if k > fst a then node22 l a (del k r)
   else let (a',t) = del_min r in node22 l a' t)" |
"del k (Node3 l a m b r) =
  (if k<fst a then node31 (del k l) a m b r else
   if k = fst a then let (a',m') = del_min m in node32 l a' m' b r else
   if k < fst b then node32 l a (del k m) b r else
   if k = fst b then let (b',r') = del_min r in node33 l a m b' r'
   else node33 l a m b (del k r))" |
"del x (Node4 l ab1 m ab2 n ab3 r) =
  (if x < fst ab2 then
     if x < fst ab1 then node41 (del x l) ab1 m ab2 n ab3 r else
     if x = fst ab1 then let (ab',m') = del_min m in node42 l ab' m' ab2 n ab3 r
     else node42 l ab1 (del x m) ab2 n ab3 r
   else
     if x = fst ab2 then let (ab',n') = del_min n in node43 l ab1 m ab' n' ab3 r else
     if x < fst ab3 then node43 l ab1 m ab2 (del x n) ab3 r else
     if x = fst ab3 then let (ab',r') = del_min r in node44 l ab1 m ab2 n ab' r'
     else node44 l ab1 m ab2 n ab3 (del x r))"

definition delete :: "'a::linorder \<Rightarrow> ('a*'b) tree234 \<Rightarrow> ('a*'b) tree234" where
"delete k t = tree\<^sub>d(del k t)"


subsection "Functional correctness"

lemma lookup: "sorted1(inorder t) \<Longrightarrow> lookup t x = map_of (inorder t) x"
by (induction t) (auto simp: map_of_simps split: option.split)


lemma inorder_upd:
  "sorted1(inorder t) \<Longrightarrow> inorder(tree\<^sub>i(upd a b t)) = upd_list a b (inorder t)"
by(induction t)
  (auto simp: upd_list_simps, auto simp: upd_list_simps split: up\<^sub>i.splits)

lemma inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update a b t) = upd_list a b (inorder t)"
by(simp add: update_def inorder_upd)


lemma inorder_del: "\<lbrakk> bal t ; sorted1(inorder t) \<rbrakk> \<Longrightarrow>
  inorder(tree\<^sub>d (del x t)) = del_list x (inorder t)"
by(induction t rule: del.induct)
  ((auto simp: del_list_simps inorder_nodes del_minD split: prod.splits)[1])+
(* 290 secs (2015) *)

lemma inorder_delete: "\<lbrakk> bal t ; sorted1(inorder t) \<rbrakk> \<Longrightarrow>
  inorder(delete x t) = del_list x (inorder t)"
by(simp add: delete_def inorder_del)


subsection \<open>Balancedness\<close>

lemma bal_upd: "bal t \<Longrightarrow> bal (tree\<^sub>i(upd x y t)) \<and> height(upd x y t) = height t"
by (induct t) (auto, auto split: up\<^sub>i.split) (* 33 secs (2015) *)

lemma bal_update: "bal t \<Longrightarrow> bal (update x y t)"
by (simp add: update_def bal_upd)


lemma height_del: "bal t \<Longrightarrow> height(del x t) = height t"
by(induction x t rule: del.induct)
  (auto simp add: heights height_del_min split: prod.split)

lemma bal_tree\<^sub>d_del: "bal t \<Longrightarrow> bal(tree\<^sub>d(del x t))"
by(induction x t rule: del.induct)
  (auto simp: bals bal_del_min height_del height_del_min split: prod.split)
(* 110 secs (2015) *)

corollary bal_delete: "bal t \<Longrightarrow> bal(delete x t)"
by(simp add: delete_def bal_tree\<^sub>d_del)


subsection \<open>Overall Correctness\<close>

interpretation T234_Map: Map_by_Ordered
where empty = Leaf and lookup = lookup and update = update and delete = delete
and inorder = inorder and wf = bal
proof (standard, goal_cases)
  case 2 thus ?case by(simp add: lookup)
next
  case 3 thus ?case by(simp add: inorder_update)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 6 thus ?case by(simp add: bal_update)
next
  case 7 thus ?case by(simp add: bal_delete)
qed simp+

end
