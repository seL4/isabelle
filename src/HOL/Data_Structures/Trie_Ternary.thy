section "Ternary Tries"

theory Trie_Ternary
imports
  Tree_Map
  Trie_Fun
begin

text \<open>An implementation of tries for an arbitrary alphabet \<open>'a\<close> where the mapping
from an element of type \<open>'a\<close> to the sub-trie is implemented by an (unbalanced) binary search tree.
In principle, other search trees (e.g. red-black trees) work just as well,
with some small adjustments (Exercise!).

This is an implementation of the ``ternary search trees'' by Bentley and Sedgewick
[SODA 1997, Dr. Dobbs 1998]. The name derives from the fact that a node in the BST can now
be drawn to have 3 children, where the middle child is the sub-trie that the node maps
its key to. Hence the name \<open>trie3\<close>.

Example from @{url "https://en.wikipedia.org/wiki/Ternary_search_tree#Description"}:

          c
        / | \
       a  u  h
       |  |  | \
       t. t  e. u
     /  / |   / |
    s. p. e. i. s.

Characters with a dot are final.
Thus the tree represents the set of strings "cute","cup","at","as","he","us" and "i".
\<close>

datatype 'a trie3 = Nd3 bool "('a * 'a trie3) tree"

text \<open>The development below works almost verbatim for any search tree implementation, eg \<open>RBT_Map\<close>,
and not just \<open>Tree_Map\<close>, except for the termination lemma \<open>lookup_size\<close>.\<close>

term size_tree
lemma lookup_size[termination_simp]:
  fixes t :: "('a::linorder * 'a trie3) tree"
  shows "lookup t a = Some b \<Longrightarrow> size b < Suc (size_tree (\<lambda>ab. Suc (size (snd( ab)))) t)"
apply(induction t a rule: lookup.induct)
apply(auto split: if_splits)
done


definition empty3 :: "'a trie3" where
[simp]: "empty3 = Nd3 False Leaf"

fun isin3 :: "('a::linorder) trie3 \<Rightarrow> 'a list \<Rightarrow> bool" where
"isin3 (Nd3 b m) [] = b" |
"isin3 (Nd3 b m) (x # xs) = (case lookup m x of None \<Rightarrow> False | Some t \<Rightarrow> isin3 t xs)"

fun insert3 :: "('a::linorder) list \<Rightarrow> 'a trie3 \<Rightarrow> 'a trie3" where
"insert3 [] (Nd3 b m) = Nd3 True m" |
"insert3 (x#xs) (Nd3 b m) =
  Nd3 b (update x (insert3 xs (case lookup m x of None \<Rightarrow> empty3 | Some t \<Rightarrow> t)) m)"

fun delete3 :: "('a::linorder) list \<Rightarrow> 'a trie3 \<Rightarrow> 'a trie3" where
"delete3 [] (Nd3 b m) = Nd3 False m" |
"delete3 (x#xs) (Nd3 b m) = Nd3 b
   (case lookup m x of
      None \<Rightarrow> m |
      Some t \<Rightarrow> update x (delete3 xs t) m)"


subsection "Correctness"

text \<open>Proof by stepwise refinement. First abs3tract to type @{typ "'a trie"}.\<close>

fun abs3 :: "'a::linorder trie3 \<Rightarrow> 'a trie" where
"abs3 (Nd3 b t) = Nd b (\<lambda>a. map_option abs3 (lookup t a))"

fun invar3 :: "('a::linorder)trie3 \<Rightarrow> bool" where
"invar3 (Nd3 b m) = (M.invar m \<and> (\<forall>a t. lookup m a = Some t \<longrightarrow> invar3 t))"

lemma isin_abs3: "isin3 t xs = isin (abs3 t) xs"
apply(induction t xs rule: isin3.induct)
apply(auto split: option.split)
done

lemma abs3_insert3: "invar3 t \<Longrightarrow> abs3(insert3 xs t) = insert xs (abs3 t)"
apply(induction xs t rule: insert3.induct)
apply(auto simp: M.map_specs Tree_Set.empty_def[symmetric] split: option.split)
done

lemma abs3_delete3: "invar3 t \<Longrightarrow> abs3(delete3 xs t) = delete xs (abs3 t)"
apply(induction xs t rule: delete3.induct)
apply(auto simp: M.map_specs split: option.split)
done

lemma invar3_insert3: "invar3 t \<Longrightarrow> invar3 (insert3 xs t)"
apply(induction xs t rule: insert3.induct)
apply(auto simp: M.map_specs Tree_Set.empty_def[symmetric] split: option.split)
done

lemma invar3_delete3: "invar3 t \<Longrightarrow> invar3 (delete3 xs t)"
apply(induction xs t rule: delete3.induct)
apply(auto simp: M.map_specs split: option.split)
done

text \<open>Overall correctness w.r.t. the \<open>Set\<close> ADT:\<close>

interpretation S2: Set
where empty = empty3 and isin = isin3 and insert = insert3 and delete = delete3
and set = "set o abs3" and invar = invar3
proof (standard, goal_cases)
  case 1 show ?case by (simp add: isin_case split: list.split)
next
  case 2 thus ?case by (simp add: isin_abs3)
next
  case 3 thus ?case by (simp add: set_insert abs3_insert3 del: set_def)
next
  case 4 thus ?case by (simp add: set_delete abs3_delete3 del: set_def)
next
  case 5 thus ?case by (simp add: M.map_specs Tree_Set.empty_def[symmetric])
next
  case 6 thus ?case by (simp add: invar3_insert3)
next
  case 7 thus ?case by (simp add: invar3_delete3)
qed

end
