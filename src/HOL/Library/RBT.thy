(* Author: Florian Haftmann, TU Muenchen *)

header {* Abstract type of Red-Black Trees *}

(*<*)
theory RBT
imports Main RBT_Impl Mapping
begin

subsection {* Type definition *}

typedef (open) ('a, 'b) rbt = "{t :: ('a\<Colon>linorder, 'b) RBT_Impl.rbt. is_rbt t}"
  morphisms impl_of RBT
proof -
  have "RBT_Impl.Empty \<in> ?rbt" by simp
  then show ?thesis ..
qed

lemma is_rbt_impl_of [simp, intro]:
  "is_rbt (impl_of t)"
  using impl_of [of t] by simp

lemma rbt_eq:
  "t1 = t2 \<longleftrightarrow> impl_of t1 = impl_of t2"
  by (simp add: impl_of_inject)

lemma [code abstype]:
  "RBT (impl_of t) = t"
  by (simp add: impl_of_inverse)


subsection {* Primitive operations *}

definition lookup :: "('a\<Colon>linorder, 'b) rbt \<Rightarrow> 'a \<rightharpoonup> 'b" where
  [code]: "lookup t = RBT_Impl.lookup (impl_of t)"

definition empty :: "('a\<Colon>linorder, 'b) rbt" where
  "empty = RBT RBT_Impl.Empty"

lemma impl_of_empty [code abstract]:
  "impl_of empty = RBT_Impl.Empty"
  by (simp add: empty_def RBT_inverse)

definition insert :: "'a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "insert k v t = RBT (RBT_Impl.insert k v (impl_of t))"

lemma impl_of_insert [code abstract]:
  "impl_of (insert k v t) = RBT_Impl.insert k v (impl_of t)"
  by (simp add: insert_def RBT_inverse)

definition delete :: "'a\<Colon>linorder \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "delete k t = RBT (RBT_Impl.delete k (impl_of t))"

lemma impl_of_delete [code abstract]:
  "impl_of (delete k t) = RBT_Impl.delete k (impl_of t)"
  by (simp add: delete_def RBT_inverse)

definition entries :: "('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a \<times> 'b) list" where
  [code]: "entries t = RBT_Impl.entries (impl_of t)"

definition keys :: "('a\<Colon>linorder, 'b) rbt \<Rightarrow> 'a list" where
  [code]: "keys t = RBT_Impl.keys (impl_of t)"

definition bulkload :: "('a\<Colon>linorder \<times> 'b) list \<Rightarrow> ('a, 'b) rbt" where
  "bulkload xs = RBT (RBT_Impl.bulkload xs)"

lemma impl_of_bulkload [code abstract]:
  "impl_of (bulkload xs) = RBT_Impl.bulkload xs"
  by (simp add: bulkload_def RBT_inverse)

definition map_entry :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "map_entry k f t = RBT (RBT_Impl.map_entry k f (impl_of t))"

lemma impl_of_map_entry [code abstract]:
  "impl_of (map_entry k f t) = RBT_Impl.map_entry k f (impl_of t)"
  by (simp add: map_entry_def RBT_inverse)

definition map :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "map f t = RBT (RBT_Impl.map f (impl_of t))"

lemma impl_of_map [code abstract]:
  "impl_of (map f t) = RBT_Impl.map f (impl_of t)"
  by (simp add: map_def RBT_inverse)

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a\<Colon>linorder, 'b) rbt \<Rightarrow> 'c \<Rightarrow> 'c" where
  [code]: "fold f t = RBT_Impl.fold f (impl_of t)"


subsection {* Derived operations *}

definition is_empty :: "('a\<Colon>linorder, 'b) rbt \<Rightarrow> bool" where
  [code]: "is_empty t = (case impl_of t of RBT_Impl.Empty \<Rightarrow> True | _ \<Rightarrow> False)"


subsection {* Abstract lookup properties *}

lemma lookup_RBT:
  "is_rbt t \<Longrightarrow> lookup (RBT t) = RBT_Impl.lookup t"
  by (simp add: lookup_def RBT_inverse)

lemma lookup_impl_of:
  "RBT_Impl.lookup (impl_of t) = lookup t"
  by (simp add: lookup_def)

lemma entries_impl_of:
  "RBT_Impl.entries (impl_of t) = entries t"
  by (simp add: entries_def)

lemma keys_impl_of:
  "RBT_Impl.keys (impl_of t) = keys t"
  by (simp add: keys_def)

lemma lookup_empty [simp]:
  "lookup empty = Map.empty"
  by (simp add: empty_def lookup_RBT ext_iff)

lemma lookup_insert [simp]:
  "lookup (insert k v t) = (lookup t)(k \<mapsto> v)"
  by (simp add: insert_def lookup_RBT lookup_insert lookup_impl_of)

lemma lookup_delete [simp]:
  "lookup (delete k t) = (lookup t)(k := None)"
  by (simp add: delete_def lookup_RBT RBT_Impl.lookup_delete lookup_impl_of restrict_complement_singleton_eq)

lemma map_of_entries [simp]:
  "map_of (entries t) = lookup t"
  by (simp add: entries_def map_of_entries lookup_impl_of)

lemma entries_lookup:
  "entries t1 = entries t2 \<longleftrightarrow> lookup t1 = lookup t2"
  by (simp add: entries_def lookup_def entries_lookup)

lemma lookup_bulkload [simp]:
  "lookup (bulkload xs) = map_of xs"
  by (simp add: bulkload_def lookup_RBT RBT_Impl.lookup_bulkload)

lemma lookup_map_entry [simp]:
  "lookup (map_entry k f t) = (lookup t)(k := Option.map f (lookup t k))"
  by (simp add: map_entry_def lookup_RBT RBT_Impl.lookup_map_entry lookup_impl_of)

lemma lookup_map [simp]:
  "lookup (map f t) k = Option.map (f k) (lookup t k)"
  by (simp add: map_def lookup_RBT lookup_map lookup_impl_of)

lemma fold_fold:
  "fold f t = More_List.fold (prod_case f) (entries t)"
  by (simp add: fold_def ext_iff RBT_Impl.fold_def entries_impl_of)

lemma is_empty_empty [simp]:
  "is_empty t \<longleftrightarrow> t = empty"
  by (simp add: rbt_eq is_empty_def impl_of_empty split: rbt.split)

lemma RBT_lookup_empty [simp]: (*FIXME*)
  "RBT_Impl.lookup t = Map.empty \<longleftrightarrow> t = RBT_Impl.Empty"
  by (cases t) (auto simp add: ext_iff)

lemma lookup_empty_empty [simp]:
  "lookup t = Map.empty \<longleftrightarrow> t = empty"
  by (cases t) (simp add: empty_def lookup_def RBT_inject RBT_inverse)

lemma sorted_keys [iff]:
  "sorted (keys t)"
  by (simp add: keys_def RBT_Impl.keys_def sorted_entries)

lemma distinct_keys [iff]:
  "distinct (keys t)"
  by (simp add: keys_def RBT_Impl.keys_def distinct_entries)


subsection {* Implementation of mappings *}

definition Mapping :: "('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a, 'b) mapping" where
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
  by (simp add: rbt_eq Mapping.is_empty_empty Mapping_def)

lemma insert_Mapping [code]:
  "Mapping.update k v (Mapping t) = Mapping (insert k v t)"
  by (rule mapping_eqI) simp

lemma delete_Mapping [code]:
  "Mapping.delete k (Mapping t) = Mapping (delete k t)"
  by (rule mapping_eqI) simp

lemma map_entry_Mapping [code]:
  "Mapping.map_entry k f (Mapping t) = Mapping (map_entry k f t)"
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
  by (rule mapping_eqI) (simp add: map_of_map_restrict ext_iff)

lemma equal_Mapping [code]:
  "HOL.equal (Mapping t1) (Mapping t2) \<longleftrightarrow> entries t1 = entries t2"
  by (simp add: equal Mapping_def entries_lookup)

lemma [code nbe]:
  "HOL.equal (x :: (_, _) mapping) x \<longleftrightarrow> True"
  by (fact equal_refl)


hide_const (open) impl_of lookup empty insert delete
  entries keys bulkload map_entry map fold
(*>*)

text {* 
  This theory defines abstract red-black trees as an efficient
  representation of finite maps, backed by the implementation
  in @{theory RBT_Impl}.
*}

subsection {* Data type and invariant *}

text {*
  The type @{typ "('k, 'v) RBT_Impl.rbt"} denotes red-black trees with
  keys of type @{typ "'k"} and values of type @{typ "'v"}. To function
  properly, the key type musorted belong to the @{text "linorder"}
  class.

  A value @{term t} of this type is a valid red-black tree if it
  satisfies the invariant @{text "is_rbt t"}.  The abstract type @{typ
  "('k, 'v) rbt"} always obeys this invariant, and for this reason you
  should only use this in our application.  Going back to @{typ "('k,
  'v) RBT_Impl.rbt"} may be necessary in proofs if not yet proven
  properties about the operations must be established.

  The interpretation function @{const "RBT.lookup"} returns the partial
  map represented by a red-black tree:
  @{term_type[display] "RBT.lookup"}

  This function should be used for reasoning about the semantics of the RBT
  operations. Furthermore, it implements the lookup functionality for
  the data structure: It is executable and the lookup is performed in
  $O(\log n)$.  
*}

subsection {* Operations *}

text {*
  Currently, the following operations are supported:

  @{term_type [display] "RBT.empty"}
  Returns the empty tree. $O(1)$

  @{term_type [display] "RBT.insert"}
  Updates the map at a given position. $O(\log n)$

  @{term_type [display] "RBT.delete"}
  Deletes a map entry at a given position. $O(\log n)$

  @{term_type [display] "RBT.entries"}
  Return a corresponding key-value list for a tree.

  @{term_type [display] "RBT.bulkload"}
  Builds a tree from a key-value list.

  @{term_type [display] "RBT.map_entry"}
  Maps a single entry in a tree.

  @{term_type [display] "RBT.map"}
  Maps all values in a tree. $O(n)$

  @{term_type [display] "RBT.fold"}
  Folds over all entries in a tree. $O(n)$
*}


subsection {* Invariant preservation *}

text {*
  \noindent
  @{thm Empty_is_rbt}\hfill(@{text "Empty_is_rbt"})

  \noindent
  @{thm insert_is_rbt}\hfill(@{text "insert_is_rbt"})

  \noindent
  @{thm delete_is_rbt}\hfill(@{text "delete_is_rbt"})

  \noindent
  @{thm bulkload_is_rbt}\hfill(@{text "bulkload_is_rbt"})

  \noindent
  @{thm map_entry_is_rbt}\hfill(@{text "map_entry_is_rbt"})

  \noindent
  @{thm map_is_rbt}\hfill(@{text "map_is_rbt"})

  \noindent
  @{thm union_is_rbt}\hfill(@{text "union_is_rbt"})
*}


subsection {* Map Semantics *}

text {*
  \noindent
  \underline{@{text "lookup_empty"}}
  @{thm [display] lookup_empty}
  \vspace{1ex}

  \noindent
  \underline{@{text "lookup_insert"}}
  @{thm [display] lookup_insert}
  \vspace{1ex}

  \noindent
  \underline{@{text "lookup_delete"}}
  @{thm [display] lookup_delete}
  \vspace{1ex}

  \noindent
  \underline{@{text "lookup_bulkload"}}
  @{thm [display] lookup_bulkload}
  \vspace{1ex}

  \noindent
  \underline{@{text "lookup_map"}}
  @{thm [display] lookup_map}
  \vspace{1ex}
*}

end
