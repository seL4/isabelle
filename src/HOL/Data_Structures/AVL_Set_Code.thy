(*
Author:     Tobias Nipkow, Daniel Stüwe
Based on the AFP entry AVL.
*)

section "AVL Tree Implementation of Sets"

theory AVL_Set_Code
imports
  Cmp
  Isin2
begin

subsection \<open>Code\<close>

type_synonym 'a tree_ht = "('a*nat) tree"

definition empty :: "'a tree_ht" where
"empty = Leaf"

fun ht :: "'a tree_ht \<Rightarrow> nat" where
"ht Leaf = 0" |
"ht (Node l (a,n) r) = n"

definition node :: "'a tree_ht \<Rightarrow> 'a \<Rightarrow> 'a tree_ht \<Rightarrow> 'a tree_ht" where
"node l a r = Node l (a, max (ht l) (ht r) + 1) r"

definition balL :: "'a tree_ht \<Rightarrow> 'a \<Rightarrow> 'a tree_ht \<Rightarrow> 'a tree_ht" where
"balL AB c C =
  (if ht AB = ht C + 2 then
     case AB of 
       Node A (a, _) B \<Rightarrow>
         if ht A \<ge> ht B then node A a (node B c C)
         else
           case B of
             Node B\<^sub>1 (b, _) B\<^sub>2 \<Rightarrow> node (node A a B\<^sub>1) b (node B\<^sub>2 c C)
   else node AB c C)"

definition balR :: "'a tree_ht \<Rightarrow> 'a \<Rightarrow> 'a tree_ht \<Rightarrow> 'a tree_ht" where
"balR A a BC =
   (if ht BC = ht A + 2 then
      case BC of
        Node B (c, _) C \<Rightarrow>
          if ht B \<le> ht C then node (node A a B) c C
          else
            case B of
              Node B\<^sub>1 (b, _) B\<^sub>2 \<Rightarrow> node (node A a B\<^sub>1) b (node B\<^sub>2 c C)
  else node A a BC)"

fun insert :: "'a::linorder \<Rightarrow> 'a tree_ht \<Rightarrow> 'a tree_ht" where
"insert x Leaf = Node Leaf (x, 1) Leaf" |
"insert x (Node l (a, n) r) = (case cmp x a of
   EQ \<Rightarrow> Node l (a, n) r |
   LT \<Rightarrow> balL (insert x l) a r |
   GT \<Rightarrow> balR l a (insert x r))"

fun split_max :: "'a tree_ht \<Rightarrow> 'a tree_ht * 'a" where
"split_max (Node l (a, _) r) =
  (if r = Leaf then (l,a) else let (r',a') = split_max r in (balL l a r', a'))"

lemmas split_max_induct = split_max.induct[case_names Node Leaf]

fun delete :: "'a::linorder \<Rightarrow> 'a tree_ht \<Rightarrow> 'a tree_ht" where
"delete _ Leaf = Leaf" |
"delete x (Node l (a, n) r) =
  (case cmp x a of
     EQ \<Rightarrow> if l = Leaf then r
           else let (l', a') = split_max l in balR l' a' r |
     LT \<Rightarrow> balR (delete x l) a r |
     GT \<Rightarrow> balL l a (delete x r))"


subsection \<open>Functional Correctness Proofs\<close>

text\<open>Very different from the AFP/AVL proofs\<close>


subsubsection "Proofs for insert"

lemma inorder_balL:
  "inorder (balL l a r) = inorder l @ a # inorder r"
by (auto simp: node_def balL_def split:tree.splits)

lemma inorder_balR:
  "inorder (balR l a r) = inorder l @ a # inorder r"
by (auto simp: node_def balR_def split:tree.splits)

theorem inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
by (induct t) 
   (auto simp: ins_list_simps inorder_balL inorder_balR)


subsubsection "Proofs for delete"

lemma inorder_split_maxD:
  "\<lbrakk> split_max t = (t',a); t \<noteq> Leaf \<rbrakk> \<Longrightarrow>
   inorder t' @ [a] = inorder t"
by(induction t arbitrary: t' rule: split_max.induct)
  (auto simp: inorder_balL split: if_splits prod.splits tree.split)

theorem inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder (delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_balL inorder_balR inorder_split_maxD split: prod.splits)

end
