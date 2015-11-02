(* Author: Tobias Nipkow *)

section {* Unbalanced Tree as Map *}

theory Tree_Map
imports
  Tree_Set
  Map_by_Ordered
begin

fun lookup :: "('a::linorder*'b) tree \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup Leaf x = None" |
"lookup (Node l (a,b) r) x = (if x < a then lookup l x else
  if x > a then lookup r x else Some b)"

fun update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree" where
"update x y Leaf = Node Leaf (x,y) Leaf" |
"update x y (Node l (a,b) r) =
   (if x < a then Node (update x y l) (a,b) r
    else if x = a then Node l (x,y) r
    else Node l (a,b) (update x y r))"

fun delete :: "'a::linorder \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree" where
"delete x Leaf = Leaf" |
"delete x (Node l (a,b) r) = (if x < a then Node (delete x l) (a,b) r else
  if x > a then Node l (a,b) (delete x r) else
  if r = Leaf then l else let (ab',r') = del_min r in Node l ab' r')"


subsection "Functional Correctness Proofs"

lemma lookup_eq:
  "sorted1(inorder t) \<Longrightarrow> lookup t x = map_of (inorder t) x"
by (induction t) (auto simp: map_of_simps split: option.split)


lemma inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update a b t) = upd_list a b (inorder t)"
by(induction t) (auto simp: upd_list_simps)


lemma del_minD:
  "del_min t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> sorted1(inorder t) \<Longrightarrow>
   x # inorder t' = inorder t"
by(induction t arbitrary: t' rule: del_min.induct)
  (auto simp: del_list_simps split: prod.splits)

lemma inorder_delete:
  "sorted1(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(induction t) (auto simp: del_list_simps del_minD split: prod.splits)


interpretation Map_by_Ordered
where empty = Leaf and lookup = lookup and update = update and delete = delete
and inorder = inorder and wf = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: lookup_eq)
next
  case 3 thus ?case by(simp add: inorder_update)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed (rule TrueI)+

end
