section "Tries via Search Trees"

theory Trie_Map
imports
  RBT_Map
  Trie_Fun
begin

text \<open>An implementation of tries based on maps implemented by red-black trees.
Works for any kind of search tree.\<close>

text \<open>Implementation of map:\<close>

type_synonym 'a mapi = "'a rbt"

datatype 'a trie_map = Nd bool "('a * 'a trie_map) mapi"

text \<open>In principle one should be able to given an implementation of tries
once and for all for any map implementation and not just for a specific one (RBT) as done here.
But because the map (@{typ "'a rbt"}) is used in a datatype, the HOL type system does not support this.

However, the development below works verbatim for any map implementation, eg \<open>Tree_Map\<close>,
and not just \<open>RBT_Map\<close>, except for the termination lemma \<open>lookup_size\<close>.\<close>
term size_tree
lemma lookup_size[termination_simp]:
  fixes t :: "('a::linorder * 'a trie_map) rbt"
  shows "lookup t a = Some b \<Longrightarrow> size b < Suc (size_tree (\<lambda>ab. Suc(Suc (size (snd(fst ab))))) t)"
apply(induction t a rule: lookup.induct)
apply(auto split: if_splits)
done


definition empty :: "'a trie_map" where
[simp]: "empty = Nd False Leaf"

fun isin :: "('a::linorder) trie_map \<Rightarrow> 'a list \<Rightarrow> bool" where
"isin (Nd b m) [] = b" |
"isin (Nd b m) (x # xs) = (case lookup m x of None \<Rightarrow> False | Some t \<Rightarrow> isin t xs)"

fun insert :: "('a::linorder) list \<Rightarrow> 'a trie_map \<Rightarrow> 'a trie_map" where
"insert [] (Nd b m) = Nd True m" |
"insert (x#xs) (Nd b m) =
  Nd b (update x (insert xs (case lookup m x of None \<Rightarrow> empty | Some t \<Rightarrow> t)) m)"

fun delete :: "('a::linorder) list \<Rightarrow> 'a trie_map \<Rightarrow> 'a trie_map" where
"delete [] (Nd b m) = Nd False m" |
"delete (x#xs) (Nd b m) = Nd b
   (case lookup m x of
      None \<Rightarrow> m |
      Some t \<Rightarrow> update x (delete xs t) m)"


subsection "Correctness"

text \<open>Proof by stepwise refinement. First abstract to type @{typ "'a trie"}.\<close>

fun abs :: "'a::linorder trie_map \<Rightarrow> 'a trie" where
"abs (Nd b t) = Trie_Fun.Nd b (\<lambda>a. map_option abs (lookup t a))"

fun invar :: "('a::linorder)trie_map \<Rightarrow> bool" where
"invar (Nd b m) = (M.invar m \<and> (\<forall>a t. lookup m a = Some t \<longrightarrow> invar t))"

lemma isin_abs: "isin t xs = Trie_Fun.isin (abs t) xs"
apply(induction t xs rule: isin.induct)
apply(auto split: option.split)
done

lemma abs_insert: "invar t \<Longrightarrow> abs(insert xs t) = Trie_Fun.insert xs (abs t)"
apply(induction xs t rule: insert.induct)
apply(auto simp: M.map_specs RBT_Set.empty_def[symmetric] split: option.split)
done

lemma abs_delete: "invar t \<Longrightarrow> abs(delete xs t) = Trie_Fun.delete xs (abs t)"
apply(induction xs t rule: delete.induct)
apply(auto simp: M.map_specs split: option.split)
done

lemma invar_insert: "invar t \<Longrightarrow> invar (insert xs t)"
apply(induction xs t rule: insert.induct)
apply(auto simp: M.map_specs RBT_Set.empty_def[symmetric] split: option.split)
done

lemma invar_delete: "invar t \<Longrightarrow> invar (delete xs t)"
apply(induction xs t rule: delete.induct)
apply(auto simp: M.map_specs split: option.split)
done

text \<open>Overall correctness w.r.t. the \<open>Set\<close> ADT:\<close>

interpretation S2: Set
where empty = empty and isin = isin and insert = insert and delete = delete
and set = "set o abs" and invar = invar
proof (standard, goal_cases)
  case 1 show ?case by (simp add: isin_case split: list.split)
next
  case 2 thus ?case by (simp add: isin_abs)
next
  case 3 thus ?case by (simp add: set_insert abs_insert del: set_def)
next
  case 4 thus ?case by (simp add: set_delete abs_delete del: set_def)
next
  case 5 thus ?case by (simp add: M.map_specs RBT_Set.empty_def[symmetric])
next
  case 6 thus ?case by (simp add: invar_insert)
next
  case 7 thus ?case by (simp add: invar_delete)
qed


end
