(* Author: Tobias Nipkow *)

section \<open>2-3 Tree Implementation of Maps\<close>

theory Tree23_Map
imports
  Tree23_Set
  Map_Specs
begin

fun lookup :: "('a::linorder * 'b) tree23 \<Rightarrow> 'a \<Rightarrow> 'b option" where
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
          GT \<Rightarrow> lookup r x))"

fun upd :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) tree23 \<Rightarrow> ('a*'b) upI" where
"upd x y Leaf = OF Leaf (x,y) Leaf" |
"upd x y (Node2 l ab r) = (case cmp x (fst ab) of
   LT \<Rightarrow> (case upd x y l of
           TI l' => TI (Node2 l' ab r)
         | OF l1 ab' l2 => TI (Node3 l1 ab' l2 ab r)) |
   EQ \<Rightarrow> TI (Node2 l (x,y) r) |
   GT \<Rightarrow> (case upd x y r of
           TI r' => TI (Node2 l ab r')
         | OF r1 ab' r2 => TI (Node3 l ab r1 ab' r2)))" |
"upd x y (Node3 l ab1 m ab2 r) = (case cmp x (fst ab1) of
   LT \<Rightarrow> (case upd x y l of
           TI l' => TI (Node3 l' ab1 m ab2 r)
         | OF l1 ab' l2 => OF (Node2 l1 ab' l2) ab1 (Node2 m ab2 r)) |
   EQ \<Rightarrow> TI (Node3 l (x,y) m ab2 r) |
   GT \<Rightarrow> (case cmp x (fst ab2) of
           LT \<Rightarrow> (case upd x y m of
                   TI m' => TI (Node3 l ab1 m' ab2 r)
                 | OF m1 ab' m2 => OF (Node2 l ab1 m1) ab' (Node2 m2 ab2 r)) |
           EQ \<Rightarrow> TI (Node3 l ab1 m (x,y) r) |
           GT \<Rightarrow> (case upd x y r of
                   TI r' => TI (Node3 l ab1 m ab2 r')
                 | OF r1 ab' r2 => OF (Node2 l ab1 m) ab2 (Node2 r1 ab' r2))))"

definition update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) tree23 \<Rightarrow> ('a*'b) tree23" where
"update a b t = treeI(upd a b t)"

fun del :: "'a::linorder \<Rightarrow> ('a*'b) tree23 \<Rightarrow> ('a*'b) upD" where
"del x Leaf = TD Leaf" |
"del x (Node2 Leaf ab1 Leaf) = (if x=fst ab1 then UF Leaf else TD(Node2 Leaf ab1 Leaf))" |
"del x (Node3 Leaf ab1 Leaf ab2 Leaf) = TD(if x=fst ab1 then Node2 Leaf ab2 Leaf
  else if x=fst ab2 then Node2 Leaf ab1 Leaf else Node3 Leaf ab1 Leaf ab2 Leaf)" |
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
           GT \<Rightarrow> node33 l ab1 m ab2 (del x r)))"

definition delete :: "'a::linorder \<Rightarrow> ('a*'b) tree23 \<Rightarrow> ('a*'b) tree23" where
"delete x t = treeD(del x t)"


subsection \<open>Functional Correctness\<close>

lemma lookup_map_of:
  "sorted1(inorder t) \<Longrightarrow> lookup t x = map_of (inorder t) x"
by (induction t) (auto simp: map_of_simps split: option.split)


lemma inorder_upd:
  "sorted1(inorder t) \<Longrightarrow> inorder(treeI(upd x y t)) = upd_list x y (inorder t)"
by(induction t) (auto simp: upd_list_simps split: upI.splits)

corollary inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update x y t) = upd_list x y (inorder t)"
by(simp add: update_def inorder_upd)


lemma inorder_del: "\<lbrakk> complete t ; sorted1(inorder t) \<rbrakk> \<Longrightarrow>
  inorder(treeD (del x t)) = del_list x (inorder t)"
by(induction t rule: del.induct)
  (auto simp: del_list_simps inorder_nodes split_minD split!: if_split prod.splits)

corollary inorder_delete: "\<lbrakk> complete t ; sorted1(inorder t) \<rbrakk> \<Longrightarrow>
  inorder(delete x t) = del_list x (inorder t)"
by(simp add: delete_def inorder_del)


subsection \<open>Balancedness\<close>

lemma complete_upd: "complete t \<Longrightarrow> complete (treeI(upd x y t)) \<and> hI(upd x y t) = height t"
by (induct t) (auto split!: if_split upI.split)(* 16 secs in 2015 *)

corollary complete_update: "complete t \<Longrightarrow> complete (update x y t)"
by (simp add: update_def complete_upd)


lemma height_del: "complete t \<Longrightarrow> hD(del x t) = height t"
by(induction x t rule: del.induct)
  (auto simp add: heights max_def height_split_min split: prod.split)

lemma complete_treeD_del: "complete t \<Longrightarrow> complete(treeD(del x t))"
by(induction x t rule: del.induct)
  (auto simp: completes complete_split_min height_del height_split_min split: prod.split)

corollary complete_delete: "complete t \<Longrightarrow> complete(delete x t)"
by(simp add: delete_def complete_treeD_del)


subsection \<open>Overall Correctness\<close>

interpretation M: Map_by_Ordered
where empty = empty and lookup = lookup and update = update and delete = delete
and inorder = inorder and inv = complete
proof (standard, goal_cases)
  case 1 thus ?case by(simp add: empty_def)
next
  case 2 thus ?case by(simp add: lookup_map_of)
next
  case 3 thus ?case by(simp add: inorder_update)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 5 thus ?case by(simp add: empty_def)
next
  case 6 thus ?case by(simp add: complete_update)
next
  case 7 thus ?case by(simp add: complete_delete)
qed

end
