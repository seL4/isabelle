(* Author: Florian Haftmann, TU Muenchen *)

header {* Tables: finite mappings implemented by red-black trees *}

theory Table
imports Main RBT
begin

subsection {* Type definition *}

typedef (open) ('a, 'b) table = "{t :: ('a\<Colon>linorder, 'b) rbt. is_rbt t}"
  morphisms tree_of Table
proof -
  have "RBT.Empty \<in> ?table" by simp
  then show ?thesis ..
qed

lemma is_rbt_tree_of [simp, intro]:
  "is_rbt (tree_of t)"
  using tree_of [of t] by simp

lemma table_eq:
  "t1 = t2 \<longleftrightarrow> tree_of t1 = tree_of t2"
  by (simp add: tree_of_inject)

code_abstype Table tree_of
  by (simp add: tree_of_inverse)


subsection {* Primitive operations *}

definition lookup :: "('a\<Colon>linorder, 'b) table \<Rightarrow> 'a \<rightharpoonup> 'b" where
  [code]: "lookup t = RBT.lookup (tree_of t)"

definition empty :: "('a\<Colon>linorder, 'b) table" where
  "empty = Table RBT.Empty"

lemma tree_of_empty [code abstract]:
  "tree_of empty = RBT.Empty"
  by (simp add: empty_def Table_inverse)

definition update :: "'a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> ('a, 'b) table \<Rightarrow> ('a, 'b) table" where
  "update k v t = Table (RBT.insert k v (tree_of t))"

lemma tree_of_update [code abstract]:
  "tree_of (update k v t) = RBT.insert k v (tree_of t)"
  by (simp add: update_def Table_inverse)

definition delete :: "'a\<Colon>linorder \<Rightarrow> ('a, 'b) table \<Rightarrow> ('a, 'b) table" where
  "delete k t = Table (RBT.delete k (tree_of t))"

lemma tree_of_delete [code abstract]:
  "tree_of (delete k t) = RBT.delete k (tree_of t)"
  by (simp add: delete_def Table_inverse)

definition entries :: "('a\<Colon>linorder, 'b) table \<Rightarrow> ('a \<times> 'b) list" where
  [code]: "entries t = RBT.entries (tree_of t)"

definition bulkload :: "('a\<Colon>linorder \<times> 'b) list \<Rightarrow> ('a, 'b) table" where
  "bulkload xs = Table (RBT.bulkload xs)"

lemma tree_of_bulkload [code abstract]:
  "tree_of (bulkload xs) = RBT.bulkload xs"
  by (simp add: bulkload_def Table_inverse)

definition map_entry :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder, 'b) table \<Rightarrow> ('a, 'b) table" where
  "map_entry k f t = Table (RBT.map_entry k f (tree_of t))"

lemma tree_of_map_entry [code abstract]:
  "tree_of (map_entry k f t) = RBT.map_entry k f (tree_of t)"
  by (simp add: map_entry_def Table_inverse)

definition map :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder, 'b) table \<Rightarrow> ('a, 'b) table" where
  "map f t = Table (RBT.map f (tree_of t))"

lemma tree_of_map [code abstract]:
  "tree_of (map f t) = RBT.map f (tree_of t)"
  by (simp add: map_def Table_inverse)

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a\<Colon>linorder, 'b) table \<Rightarrow> 'c \<Rightarrow> 'c" where
  [code]: "fold f t = RBT.fold f (tree_of t)"


subsection {* Derived operations *}

definition is_empty :: "('a\<Colon>linorder, 'b) table \<Rightarrow> bool" where
  [code]: "is_empty t = (case tree_of t of RBT.Empty \<Rightarrow> True | _ \<Rightarrow> False)"


subsection {* Abstract lookup properties *}

lemma lookup_Table:
  "is_rbt t \<Longrightarrow> lookup (Table t) = RBT.lookup t"
  by (simp add: lookup_def Table_inverse)

lemma lookup_tree_of:
  "RBT.lookup (tree_of t) = lookup t"
  by (simp add: lookup_def)

lemma entries_tree_of:
  "RBT.entries (tree_of t) = entries t"
  by (simp add: entries_def)

lemma lookup_empty [simp]:
  "lookup empty = Map.empty"
  by (simp add: empty_def lookup_Table expand_fun_eq)

lemma lookup_update [simp]:
  "lookup (update k v t) = (lookup t)(k \<mapsto> v)"
  by (simp add: update_def lookup_Table lookup_insert lookup_tree_of)

lemma lookup_delete [simp]:
  "lookup (delete k t) = (lookup t)(k := None)"
  by (simp add: delete_def lookup_Table lookup_delete lookup_tree_of restrict_complement_singleton_eq)

lemma map_of_entries [simp]:
  "map_of (entries t) = lookup t"
  by (simp add: entries_def map_of_entries lookup_tree_of)

lemma lookup_bulkload [simp]:
  "lookup (bulkload xs) = map_of xs"
  by (simp add: bulkload_def lookup_Table lookup_bulkload)

lemma lookup_map_entry [simp]:
  "lookup (map_entry k f t) = (lookup t)(k := Option.map f (lookup t k))"
  by (simp add: map_entry_def lookup_Table lookup_map_entry lookup_tree_of)

lemma lookup_map [simp]:
  "lookup (map f t) k = Option.map (f k) (lookup t k)"
  by (simp add: map_def lookup_Table lookup_map lookup_tree_of)

lemma fold_fold:
  "fold f t = (\<lambda>s. foldl (\<lambda>s (k, v). f k v s) s (entries t))"
  by (simp add: fold_def expand_fun_eq RBT.fold_def entries_tree_of)

hide (open) const tree_of lookup empty update delete
  entries bulkload map_entry map fold

end
