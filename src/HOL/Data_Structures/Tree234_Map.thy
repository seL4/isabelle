(* Author: Tobias Nipkow *)

section \<open>2-3-4 Tree Implementation of Maps\<close>

theory Tree234_Map
imports
  Tree234_Set
  Map_Specs
begin

subsection \<open>Map operations on 2-3-4 trees\<close>

fun lookup :: "('a::linorder * 'b) tree234 \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup Leaf x = None" |
"lookup (Node2 l (a,b) r) x = (case cmp x a of
  LT \<Rightarrow> lookup l x |
  GT \<Rightarrow> lookup r x |
  EQ \<Rightarrow> Some b)" |
"lookup (Node3 l (a1,b1) m (a2,b2) r) x = (case cmp x a1 of
  LT \<Rightarrow> lookup l x |
  EQ \<Rightarrow> Some b1 |
  GT \<Rightarrow> (case cmp x a2 of
          LT \<Rightarrow> lookup m x |
          EQ \<Rightarrow> Some b2 |
          GT \<Rightarrow> lookup r x))" |
"lookup (Node4 t1 (a1,b1) t2 (a2,b2) t3 (a3,b3) t4) x = (case cmp x a2 of
  LT \<Rightarrow> (case cmp x a1 of
           LT \<Rightarrow> lookup t1 x | EQ \<Rightarrow> Some b1 | GT \<Rightarrow> lookup t2 x) |
  EQ \<Rightarrow> Some b2 |
  GT \<Rightarrow> (case cmp x a3 of
           LT \<Rightarrow> lookup t3 x | EQ \<Rightarrow> Some b3 | GT \<Rightarrow> lookup t4 x))"

fun upd :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) tree234 \<Rightarrow> ('a*'b) up\<^sub>i" where
"upd x y Leaf = Up\<^sub>i Leaf (x,y) Leaf" |
"upd x y (Node2 l ab r) = (case cmp x (fst ab) of
   LT \<Rightarrow> (case upd x y l of
           T\<^sub>i l' => T\<^sub>i (Node2 l' ab r)
         | Up\<^sub>i l1 ab' l2 => T\<^sub>i (Node3 l1 ab' l2 ab r)) |
   EQ \<Rightarrow> T\<^sub>i (Node2 l (x,y) r) |
   GT \<Rightarrow> (case upd x y r of
           T\<^sub>i r' => T\<^sub>i (Node2 l ab r')
         | Up\<^sub>i r1 ab' r2 => T\<^sub>i (Node3 l ab r1 ab' r2)))" |
"upd x y (Node3 l ab1 m ab2 r) = (case cmp x (fst ab1) of
   LT \<Rightarrow> (case upd x y l of
           T\<^sub>i l' => T\<^sub>i (Node3 l' ab1 m ab2 r)
         | Up\<^sub>i l1 ab' l2 => Up\<^sub>i (Node2 l1 ab' l2) ab1 (Node2 m ab2 r)) |
   EQ \<Rightarrow> T\<^sub>i (Node3 l (x,y) m ab2 r) |
   GT \<Rightarrow> (case cmp x (fst ab2) of
           LT \<Rightarrow> (case upd x y m of
                   T\<^sub>i m' => T\<^sub>i (Node3 l ab1 m' ab2 r)
                 | Up\<^sub>i m1 ab' m2 => Up\<^sub>i (Node2 l ab1 m1) ab' (Node2 m2 ab2 r)) |
           EQ \<Rightarrow> T\<^sub>i (Node3 l ab1 m (x,y) r) |
           GT \<Rightarrow> (case upd x y r of
                   T\<^sub>i r' => T\<^sub>i (Node3 l ab1 m ab2 r')
                 | Up\<^sub>i r1 ab' r2 => Up\<^sub>i (Node2 l ab1 m) ab2 (Node2 r1 ab' r2))))" |
"upd x y (Node4 t1 ab1 t2 ab2 t3 ab3 t4) = (case cmp x (fst ab2) of
   LT \<Rightarrow> (case cmp x (fst ab1) of
            LT \<Rightarrow> (case upd x y t1 of
                     T\<^sub>i t1' => T\<^sub>i (Node4 t1' ab1 t2 ab2 t3 ab3 t4)
                  | Up\<^sub>i t11 q t12 => Up\<^sub>i (Node2 t11 q t12) ab1 (Node3 t2 ab2 t3 ab3 t4)) |
            EQ \<Rightarrow> T\<^sub>i (Node4 t1 (x,y) t2 ab2 t3 ab3 t4) |
            GT \<Rightarrow> (case upd x y t2 of
                    T\<^sub>i t2' => T\<^sub>i (Node4 t1 ab1 t2' ab2 t3 ab3 t4)
                  | Up\<^sub>i t21 q t22 => Up\<^sub>i (Node2 t1 ab1 t21) q (Node3 t22 ab2 t3 ab3 t4))) |
   EQ \<Rightarrow> T\<^sub>i (Node4 t1 ab1 t2 (x,y) t3 ab3 t4) |
   GT \<Rightarrow> (case cmp x (fst ab3) of
            LT \<Rightarrow> (case upd x y t3 of
                    T\<^sub>i t3' \<Rightarrow> T\<^sub>i (Node4 t1 ab1 t2 ab2 t3' ab3 t4)
                  | Up\<^sub>i t31 q t32 => Up\<^sub>i (Node2 t1 ab1 t2) ab2(*q*) (Node3 t31 q t32 ab3 t4)) |
            EQ \<Rightarrow> T\<^sub>i (Node4 t1 ab1 t2 ab2 t3 (x,y) t4) |
            GT \<Rightarrow> (case upd x y t4 of
                    T\<^sub>i t4' => T\<^sub>i (Node4 t1 ab1 t2 ab2 t3 ab3 t4')
                  | Up\<^sub>i t41 q t42 => Up\<^sub>i (Node2 t1 ab1 t2) ab2 (Node3 t3 ab3 t41 q t42))))"

definition update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) tree234 \<Rightarrow> ('a*'b) tree234" where
"update x y t = tree\<^sub>i(upd x y t)"

fun del :: "'a::linorder \<Rightarrow> ('a*'b) tree234 \<Rightarrow> ('a*'b) up\<^sub>d" where
"del x Leaf = T\<^sub>d Leaf" |
"del x (Node2 Leaf ab1 Leaf) = (if x=fst ab1 then Up\<^sub>d Leaf else T\<^sub>d(Node2 Leaf ab1 Leaf))" |
"del x (Node3 Leaf ab1 Leaf ab2 Leaf) = T\<^sub>d(if x=fst ab1 then Node2 Leaf ab2 Leaf
  else if x=fst ab2 then Node2 Leaf ab1 Leaf else Node3 Leaf ab1 Leaf ab2 Leaf)" |
"del x (Node4 Leaf ab1 Leaf ab2 Leaf ab3 Leaf) =
  T\<^sub>d(if x = fst ab1 then Node3 Leaf ab2 Leaf ab3 Leaf else
     if x = fst ab2 then Node3 Leaf ab1 Leaf ab3 Leaf else
     if x = fst ab3 then Node3 Leaf ab1 Leaf ab2 Leaf
     else Node4 Leaf ab1 Leaf ab2 Leaf ab3 Leaf)" |
"del x (Node2 l ab1 r) = (case cmp x (fst ab1) of
  LT \<Rightarrow> node21 (del x l) ab1 r |
  GT \<Rightarrow> node22 l ab1 (del x r) |
  EQ \<Rightarrow> let (ab1',t) = split_min r in node22 l ab1' t)" |
"del x (Node3 l ab1 m ab2 r) = (case cmp x (fst ab1) of
  LT \<Rightarrow> node31 (del x l) ab1 m ab2 r |
  EQ \<Rightarrow> let (ab1',m') = split_min m in node32 l ab1' m' ab2 r |
  GT \<Rightarrow> (case cmp x (fst ab2) of
           LT \<Rightarrow> node32 l ab1 (del x m) ab2 r |
           EQ \<Rightarrow> let (ab2',r') = split_min r in node33 l ab1 m ab2' r' |
           GT \<Rightarrow> node33 l ab1 m ab2 (del x r)))" |
"del x (Node4 t1 ab1 t2 ab2 t3 ab3 t4) = (case cmp x (fst ab2) of
  LT \<Rightarrow> (case cmp x (fst ab1) of
           LT \<Rightarrow> node41 (del x t1) ab1 t2 ab2 t3 ab3 t4 |
           EQ \<Rightarrow> let (ab',t2') = split_min t2 in node42 t1 ab' t2' ab2 t3 ab3 t4 |
           GT \<Rightarrow> node42 t1 ab1 (del x t2) ab2 t3 ab3 t4) |
  EQ \<Rightarrow> let (ab',t3') = split_min t3 in node43 t1 ab1 t2 ab' t3' ab3 t4 |
  GT \<Rightarrow> (case cmp x (fst ab3) of
          LT \<Rightarrow> node43 t1 ab1 t2 ab2 (del x t3) ab3 t4 |
          EQ \<Rightarrow> let (ab',t4') = split_min t4 in node44 t1 ab1 t2 ab2 t3 ab' t4' |
          GT \<Rightarrow> node44 t1 ab1 t2 ab2 t3 ab3 (del x t4)))"

definition delete :: "'a::linorder \<Rightarrow> ('a*'b) tree234 \<Rightarrow> ('a*'b) tree234" where
"delete x t = tree\<^sub>d(del x t)"


subsection "Functional correctness"

lemma lookup_map_of:
  "sorted1(inorder t) \<Longrightarrow> lookup t x = map_of (inorder t) x"
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
  (auto simp: del_list_simps inorder_nodes split_minD split!: if_splits prod.splits)
(* 30 secs (2016) *)

lemma inorder_delete: "\<lbrakk> bal t ; sorted1(inorder t) \<rbrakk> \<Longrightarrow>
  inorder(delete x t) = del_list x (inorder t)"
by(simp add: delete_def inorder_del)


subsection \<open>Balancedness\<close>

lemma bal_upd: "bal t \<Longrightarrow> bal (tree\<^sub>i(upd x y t)) \<and> height(upd x y t) = height t"
by (induct t) (auto, auto split!: if_split up\<^sub>i.split) (* 20 secs (2015) *)

lemma bal_update: "bal t \<Longrightarrow> bal (update x y t)"
by (simp add: update_def bal_upd)

lemma height_del: "bal t \<Longrightarrow> height(del x t) = height t"
by(induction x t rule: del.induct)
  (auto simp add: heights height_split_min split!: if_split prod.split)

lemma bal_tree\<^sub>d_del: "bal t \<Longrightarrow> bal(tree\<^sub>d(del x t))"
by(induction x t rule: del.induct)
  (auto simp: bals bal_split_min height_del height_split_min split!: if_split prod.split)

corollary bal_delete: "bal t \<Longrightarrow> bal(delete x t)"
by(simp add: delete_def bal_tree\<^sub>d_del)


subsection \<open>Overall Correctness\<close>

interpretation Map_by_Ordered
where empty = Leaf and lookup = lookup and update = update and delete = delete
and inorder = inorder and inv = bal
proof (standard, goal_cases)
  case 2 thus ?case by(simp add: lookup_map_of)
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
