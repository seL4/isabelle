(*  Title:      HOL/Library/RBT_Mapping.thy
    Author:     Florian Haftmann and Ondrej Kuncar
*)

header {* Implementation of mappings with Red-Black Trees *}

(*<*)
theory RBT_Mapping
imports RBT Mapping
begin

subsection {* Implementation of mappings *}

lift_definition Mapping :: "('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a, 'b) mapping" is lookup .

code_datatype Mapping

lemma lookup_Mapping [simp, code]:
  "Mapping.lookup (Mapping t) = lookup t"
   by (transfer fixing: t) rule

lemma empty_Mapping [code]: "Mapping.empty = Mapping empty"
proof -
  note RBT.empty.transfer[transfer_rule del]
  show ?thesis by transfer simp
qed

lemma is_empty_Mapping [code]:
  "Mapping.is_empty (Mapping t) \<longleftrightarrow> is_empty t"
  unfolding is_empty_def by (transfer fixing: t) simp

lemma insert_Mapping [code]:
  "Mapping.update k v (Mapping t) = Mapping (insert k v t)"
  by (transfer fixing: t) simp

lemma delete_Mapping [code]:
  "Mapping.delete k (Mapping t) = Mapping (delete k t)"
  by (transfer fixing: t) simp

lemma map_entry_Mapping [code]:
  "Mapping.map_entry k f (Mapping t) = Mapping (map_entry k f t)"
  apply (transfer fixing: t) by (case_tac "lookup t k") auto

lemma keys_Mapping [code]:
  "Mapping.keys (Mapping t) = set (keys t)"
by (transfer fixing: t) (simp add: lookup_keys)

lemma ordered_keys_Mapping [code]:
  "Mapping.ordered_keys (Mapping t) = keys t"
unfolding ordered_keys_def 
by (transfer fixing: t) (auto simp add: lookup_keys intro: sorted_distinct_set_unique)

lemma Mapping_size_card_keys: (*FIXME*)
  "Mapping.size m = card (Mapping.keys m)"
unfolding size_def by transfer simp

lemma size_Mapping [code]:
  "Mapping.size (Mapping t) = length (keys t)"
unfolding size_def
by (transfer fixing: t) (simp add: lookup_keys distinct_card)

context
  notes RBT.bulkload.transfer[transfer_rule del]
begin
  lemma tabulate_Mapping [code]:
    "Mapping.tabulate ks f = Mapping (bulkload (List.map (\<lambda>k. (k, f k)) ks))"
  by transfer (simp add: map_of_map_restrict)
  
  lemma bulkload_Mapping [code]:
    "Mapping.bulkload vs = Mapping (bulkload (List.map (\<lambda>n. (n, vs ! n)) [0..<length vs]))"
  by transfer (simp add: map_of_map_restrict fun_eq_iff)
end

lemma equal_Mapping [code]:
  "HOL.equal (Mapping t1) (Mapping t2) \<longleftrightarrow> entries t1 = entries t2"
by (transfer fixing: t1 t2) (simp add: entries_lookup)

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
  @{thm rbt_insert_is_rbt}\hfill(@{text "rbt_insert_is_rbt"})

  \noindent
  @{thm rbt_delete_is_rbt}\hfill(@{text "delete_is_rbt"})

  \noindent
  @{thm rbt_bulkload_is_rbt}\hfill(@{text "bulkload_is_rbt"})

  \noindent
  @{thm rbt_map_entry_is_rbt}\hfill(@{text "map_entry_is_rbt"})

  \noindent
  @{thm map_is_rbt}\hfill(@{text "map_is_rbt"})

  \noindent
  @{thm rbt_union_is_rbt}\hfill(@{text "union_is_rbt"})
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