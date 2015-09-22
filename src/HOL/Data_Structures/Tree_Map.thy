(* Author: Tobias Nipkow *)

section {* Unbalanced Tree as Map *}

theory Tree_Map
imports
  "~~/src/HOL/Library/Tree"
  Map_by_Ordered
begin

fun lookup :: "('a::linorder*'b) tree \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup Leaf x = None" |
"lookup (Node l (a,b) r) x = (if x < a then lookup l x else
  if x > a then lookup r x else Some b)"

fun update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree" where
"update a b Leaf = Node Leaf (a,b) Leaf" |
"update a b (Node l (x,y) r) =
   (if a < x then Node (update a b l) (x,y) r
    else if a=x then Node l (a,b) r
    else Node l (x,y) (update a b r))"

fun del_min :: "'a tree \<Rightarrow> 'a * 'a tree" where
"del_min (Node Leaf a r) = (a, r)" |
"del_min (Node l a r) = (let (x,l') = del_min l in (x, Node l' a r))"

fun delete :: "'a::linorder \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree" where
"delete k Leaf = Leaf" |
"delete k (Node l (a,b) r) = (if k<a then Node (delete k l) (a,b) r else
  if k > a then Node l (a,b) (delete k r) else
  if r = Leaf then l else let (ab',r') = del_min r in Node l ab' r')"


subsection "Functional Correctness Proofs"

lemma lookup_eq:
  "sorted1(inorder t) \<Longrightarrow> lookup t x = map_of (inorder t) x"
apply (induction t)
apply (auto simp: sorted_lems map_of_append map_of_sorteds split: option.split)
done


lemma inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update a b t) = upd_list a b (inorder t)"
by(induction t) (auto simp: upd_list_simps)


lemma del_minD:
  "del_min t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> sorted1(inorder t) \<Longrightarrow>
   x # inorder t' = inorder t"
by(induction t arbitrary: t' rule: del_min.induct)
  (auto simp: sorted_lems split: prod.splits)

lemma inorder_delete:
  "sorted1(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_sorted sorted_lems dest!: del_minD split: prod.splits)


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
