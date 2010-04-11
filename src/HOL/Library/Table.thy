(* Author: Florian Haftmann, TU Muenchen *)

header {* Tables: finite mappings implemented by red-black trees *}

theory Table
imports Main RBT Mapping
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

lemma [code abstype]:
  "Table (tree_of t) = t"
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

definition keys :: "('a\<Colon>linorder, 'b) table \<Rightarrow> 'a list" where
  [code]: "keys t = RBT.keys (tree_of t)"

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

lemma keys_tree_of:
  "RBT.keys (tree_of t) = keys t"
  by (simp add: keys_def)

lemma lookup_empty [simp]:
  "lookup empty = Map.empty"
  by (simp add: empty_def lookup_Table expand_fun_eq)

lemma lookup_update [simp]:
  "lookup (update k v t) = (lookup t)(k \<mapsto> v)"
  by (simp add: update_def lookup_Table lookup_insert lookup_tree_of)

lemma lookup_delete [simp]:
  "lookup (delete k t) = (lookup t)(k := None)"
  by (simp add: delete_def lookup_Table RBT.lookup_delete lookup_tree_of restrict_complement_singleton_eq)

lemma map_of_entries [simp]:
  "map_of (entries t) = lookup t"
  by (simp add: entries_def map_of_entries lookup_tree_of)

lemma entries_lookup:
  "entries t1 = entries t2 \<longleftrightarrow> lookup t1 = lookup t2"
  by (simp add: entries_def lookup_def entries_lookup)

lemma lookup_bulkload [simp]:
  "lookup (bulkload xs) = map_of xs"
  by (simp add: bulkload_def lookup_Table RBT.lookup_bulkload)

lemma lookup_map_entry [simp]:
  "lookup (map_entry k f t) = (lookup t)(k := Option.map f (lookup t k))"
  by (simp add: map_entry_def lookup_Table lookup_map_entry lookup_tree_of)

lemma lookup_map [simp]:
  "lookup (map f t) k = Option.map (f k) (lookup t k)"
  by (simp add: map_def lookup_Table lookup_map lookup_tree_of)

lemma fold_fold:
  "fold f t = (\<lambda>s. foldl (\<lambda>s (k, v). f k v s) s (entries t))"
  by (simp add: fold_def expand_fun_eq RBT.fold_def entries_tree_of)

lemma is_empty_empty [simp]:
  "is_empty t \<longleftrightarrow> t = empty"
  by (simp add: table_eq is_empty_def tree_of_empty split: rbt.split)

lemma RBT_lookup_empty [simp]: (*FIXME*)
  "RBT.lookup t = Map.empty \<longleftrightarrow> t = RBT.Empty"
  by (cases t) (auto simp add: expand_fun_eq)

lemma lookup_empty_empty [simp]:
  "lookup t = Map.empty \<longleftrightarrow> t = empty"
  by (cases t) (simp add: empty_def lookup_def Table_inject Table_inverse)

lemma sorted_keys [iff]:
  "sorted (keys t)"
  by (simp add: keys_def RBT.keys_def sorted_entries)

lemma distinct_keys [iff]:
  "distinct (keys t)"
  by (simp add: keys_def RBT.keys_def distinct_entries)


subsection {* Implementation of mappings *}

definition Mapping :: "('a\<Colon>linorder, 'b) table \<Rightarrow> ('a, 'b) mapping" where
  "Mapping t = Mapping.Mapping (lookup t)"

code_datatype Mapping

lemma lookup_Mapping [simp, code]:
  "Mapping.lookup (Mapping t) = lookup t"
  by (simp add: Mapping_def)

lemma empty_Mapping [code]:
  "Mapping.empty = Mapping empty"
  by (rule mapping_eqI) simp

lemma is_empty_Mapping [code]:
  "Mapping.is_empty (Mapping t) \<longleftrightarrow> is_empty t"
  by (simp add: table_eq Mapping.is_empty_empty Mapping_def)

lemma update_Mapping [code]:
  "Mapping.update k v (Mapping t) = Mapping (update k v t)"
  by (rule mapping_eqI) simp

lemma delete_Mapping [code]:
  "Mapping.delete k (Mapping xs) = Mapping (delete k xs)"
  by (rule mapping_eqI) simp

lemma keys_Mapping [code]:
  "Mapping.keys (Mapping t) = set (keys t)"
  by (simp add: keys_def Mapping_def Mapping.keys_def lookup_def lookup_keys)

lemma ordered_keys_Mapping [code]:
  "Mapping.ordered_keys (Mapping t) = keys t"
  by (rule sorted_distinct_set_unique) (simp_all add: ordered_keys_def keys_Mapping)

lemma Mapping_size_card_keys: (*FIXME*)
  "Mapping.size m = card (Mapping.keys m)"
  by (simp add: Mapping.size_def Mapping.keys_def)

lemma size_Mapping [code]:
  "Mapping.size (Mapping t) = length (keys t)"
  by (simp add: Mapping_size_card_keys keys_Mapping distinct_card)

lemma tabulate_Mapping [code]:
  "Mapping.tabulate ks f = Mapping (bulkload (List.map (\<lambda>k. (k, f k)) ks))"
  by (rule mapping_eqI) (simp add: map_of_map_restrict)

lemma bulkload_Mapping [code]:
  "Mapping.bulkload vs = Mapping (bulkload (List.map (\<lambda>n. (n, vs ! n)) [0..<length vs]))"
  by (rule mapping_eqI) (simp add: map_of_map_restrict expand_fun_eq)

lemma [code, code del]: "HOL.eq (x :: (_, _) mapping) y \<longleftrightarrow> x = y" by (fact eq_equals) (*FIXME*)

lemma eq_Mapping [code]:
  "HOL.eq (Mapping t1) (Mapping t2) \<longleftrightarrow> entries t1 = entries t2"
  by (simp add: eq Mapping_def entries_lookup)

hide (open) const tree_of lookup empty update delete
  entries keys bulkload map_entry map fold

end
