(* Author: Tobias Nipkow *)

section "AA Implementation of Maps"

theory AA_Map
imports
  AA_Set
  Lookup2
begin

fun update :: "'a::cmp \<Rightarrow> 'b \<Rightarrow> ('a*'b) aa_tree \<Rightarrow> ('a*'b) aa_tree" where
"update x y Leaf = Node 1 Leaf (x,y) Leaf" |
"update x y (Node lv t1 (a,b) t2) =
  (case cmp x a of
     LT \<Rightarrow> split (skew (Node lv (update x y t1) (a,b) t2)) |
     GT \<Rightarrow> split (skew (Node lv t1 (a,b) (update x y t2))) |
     EQ \<Rightarrow> Node lv t1 (x,y) t2)"

fun delete :: "'a::cmp \<Rightarrow> ('a*'b) aa_tree \<Rightarrow> ('a*'b) aa_tree" where
"delete _ Leaf = Leaf" |
"delete x (Node lv l (a,b) r) =
  (case cmp x a of
     LT \<Rightarrow> adjust (Node lv (delete x l) (a,b) r) |
     GT \<Rightarrow> adjust (Node lv l (a,b) (delete x r)) |
     EQ \<Rightarrow> (if l = Leaf then r
            else let (l',ab') = del_max l in adjust (Node lv l' ab' r)))"


subsection {* Functional Correctness Proofs *}

theorem inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update x y t) = upd_list x y (inorder t)"
by (induct t) (auto simp: upd_list_simps inorder_split inorder_skew)


theorem inorder_delete:
  "sorted1(inorder t) \<Longrightarrow> inorder (delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_adjust del_maxD split: prod.splits)

interpretation Map_by_Ordered
where empty = Leaf and lookup = lookup and update = update and delete = delete
and inorder = inorder and inv = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: lookup_map_of)
next
  case 3 thus ?case by(simp add: inorder_update)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed auto

end
