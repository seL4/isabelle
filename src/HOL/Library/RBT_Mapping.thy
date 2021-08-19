(*  Title:      HOL/Library/RBT_Mapping.thy
    Author:     Florian Haftmann and Ondrej Kuncar
*)

section \<open>Implementation of mappings with Red-Black Trees\<close>

(*<*)
theory RBT_Mapping
imports RBT Mapping
begin

subsection \<open>Implementation of mappings\<close>

context includes rbt.lifting begin
lift_definition Mapping :: "('a::linorder, 'b) rbt \<Rightarrow> ('a, 'b) mapping" is RBT.lookup .
end

code_datatype Mapping

context includes rbt.lifting begin

lemma lookup_Mapping [simp, code]:
  "Mapping.lookup (Mapping t) = RBT.lookup t"
   by (transfer fixing: t) rule

lemma empty_Mapping [code]: "Mapping.empty = Mapping RBT.empty"
proof -
  note RBT.empty.transfer[transfer_rule del]
  show ?thesis by transfer simp
qed

lemma is_empty_Mapping [code]:
  "Mapping.is_empty (Mapping t) \<longleftrightarrow> RBT.is_empty t"
  unfolding is_empty_def by (transfer fixing: t) simp

lemma insert_Mapping [code]:
  "Mapping.update k v (Mapping t) = Mapping (RBT.insert k v t)"
  by (transfer fixing: t) simp

lemma delete_Mapping [code]:
  "Mapping.delete k (Mapping t) = Mapping (RBT.delete k t)"
  by (transfer fixing: t) simp

lemma map_entry_Mapping [code]:
  "Mapping.map_entry k f (Mapping t) = Mapping (RBT.map_entry k f t)"
  apply (transfer fixing: t)
  apply (case_tac "RBT.lookup t k")
   apply auto
  done

lemma keys_Mapping [code]:
  "Mapping.keys (Mapping t) = set (RBT.keys t)"
by (transfer fixing: t) (simp add: lookup_keys)

lemma ordered_keys_Mapping [code]:
  "Mapping.ordered_keys (Mapping t) = RBT.keys t"
unfolding ordered_keys_def 
by (transfer fixing: t) (auto simp add: lookup_keys intro: sorted_distinct_set_unique)

lemma Map_graph_lookup: "Map.graph (RBT.lookup t) = set (RBT.entries t)"
  by (metis RBT.distinct_entries RBT.map_of_entries graph_map_of_if_distinct_dom)

lemma entries_Mapping [code]: "Mapping.entries (Mapping t) = set (RBT.entries t)"
  by (transfer fixing: t) (fact Map_graph_lookup)

lemma ordered_entries_Mapping [code]: "Mapping.ordered_entries (Mapping t) = RBT.entries t"
proof -
  note folding_Map_graph.idem_if_sorted_distinct[
      where ?m="RBT.lookup t", OF _ _ folding_Map_graph.distinct_if_distinct_map]
  then show ?thesis
    unfolding ordered_entries_def
    by (transfer fixing: t) (auto simp: Map_graph_lookup distinct_entries sorted_entries)
qed

lemma fold_Mapping [code]: "Mapping.fold f (Mapping t) a = RBT.fold f t a"
  by (simp add: Mapping.fold_def fold_fold ordered_entries_Mapping)

lemma Mapping_size_card_keys: (*FIXME*)
  "Mapping.size m = card (Mapping.keys m)"
unfolding size_def by transfer simp

lemma size_Mapping [code]:
  "Mapping.size (Mapping t) = length (RBT.keys t)"
unfolding size_def
by (transfer fixing: t) (simp add: lookup_keys distinct_card)

context
  notes RBT.bulkload.transfer[transfer_rule del]
begin

lemma tabulate_Mapping [code]:
  "Mapping.tabulate ks f = Mapping (RBT.bulkload (List.map (\<lambda>k. (k, f k)) ks))"
by transfer (simp add: map_of_map_restrict)

lemma bulkload_Mapping [code]:
  "Mapping.bulkload vs = Mapping (RBT.bulkload (List.map (\<lambda>n. (n, vs ! n)) [0..<length vs]))"
by transfer (simp add: map_of_map_restrict fun_eq_iff)

end

lemma map_values_Mapping [code]: 
  "Mapping.map_values f (Mapping t) = Mapping (RBT.map f t)"
  by (transfer fixing: t) (auto simp: fun_eq_iff)

lemma filter_Mapping [code]: 
  "Mapping.filter P (Mapping t) = Mapping (RBT.filter P t)"
  by (transfer' fixing: P t) (simp add: RBT.lookup_filter fun_eq_iff)

lemma combine_with_key_Mapping [code]:
  "Mapping.combine_with_key f (Mapping t1) (Mapping t2) =
     Mapping (RBT.combine_with_key f t1 t2)"
  by (transfer fixing: f t1 t2) (simp_all add: fun_eq_iff)

lemma combine_Mapping [code]:
  "Mapping.combine f (Mapping t1) (Mapping t2) =
     Mapping (RBT.combine f t1 t2)"
  by (transfer fixing: f t1 t2) (simp_all add: fun_eq_iff)

lemma equal_Mapping [code]:
  "HOL.equal (Mapping t1) (Mapping t2) \<longleftrightarrow> RBT.entries t1 = RBT.entries t2"
  by (transfer fixing: t1 t2) (simp add: RBT.entries_lookup)

lemma [code nbe]:
  "HOL.equal (x :: (_, _) mapping) x \<longleftrightarrow> True"
  by (fact equal_refl)

end

(*>*)

text \<open>
  This theory defines abstract red-black trees as an efficient
  representation of finite maps, backed by the implementation
  in \<^theory>\<open>HOL-Library.RBT_Impl\<close>.
\<close>

subsection \<open>Data type and invariant\<close>

text \<open>
  The type \<^typ>\<open>('k, 'v) RBT_Impl.rbt\<close> denotes red-black trees with
  keys of type \<^typ>\<open>'k\<close> and values of type \<^typ>\<open>'v\<close>. To function
  properly, the key type musorted belong to the \<open>linorder\<close>
  class.

  A value \<^term>\<open>t\<close> of this type is a valid red-black tree if it
  satisfies the invariant \<open>is_rbt t\<close>.  The abstract type \<^typ>\<open>('k, 'v) rbt\<close> always obeys this invariant, and for this reason you
  should only use this in our application.  Going back to \<^typ>\<open>('k,
  'v) RBT_Impl.rbt\<close> may be necessary in proofs if not yet proven
  properties about the operations must be established.

  The interpretation function \<^const>\<open>RBT.lookup\<close> returns the partial
  map represented by a red-black tree:
  @{term_type[display] "RBT.lookup"}

  This function should be used for reasoning about the semantics of the RBT
  operations. Furthermore, it implements the lookup functionality for
  the data structure: It is executable and the lookup is performed in
  $O(\log n)$.  
\<close>

subsection \<open>Operations\<close>

text \<open>
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
\<close>


subsection \<open>Invariant preservation\<close>

text \<open>
  \noindent
  @{thm Empty_is_rbt}\hfill(\<open>Empty_is_rbt\<close>)

  \noindent
  @{thm rbt_insert_is_rbt}\hfill(\<open>rbt_insert_is_rbt\<close>)

  \noindent
  @{thm rbt_delete_is_rbt}\hfill(\<open>delete_is_rbt\<close>)

  \noindent
  @{thm rbt_bulkload_is_rbt}\hfill(\<open>bulkload_is_rbt\<close>)

  \noindent
  @{thm rbt_map_entry_is_rbt}\hfill(\<open>map_entry_is_rbt\<close>)

  \noindent
  @{thm map_is_rbt}\hfill(\<open>map_is_rbt\<close>)

  \noindent
  @{thm rbt_union_is_rbt}\hfill(\<open>union_is_rbt\<close>)
\<close>


subsection \<open>Map Semantics\<close>

text \<open>
  \noindent
  \underline{\<open>lookup_empty\<close>}
  @{thm [display] lookup_empty}
  \vspace{1ex}

  \noindent
  \underline{\<open>lookup_insert\<close>}
  @{thm [display] lookup_insert}
  \vspace{1ex}

  \noindent
  \underline{\<open>lookup_delete\<close>}
  @{thm [display] lookup_delete}
  \vspace{1ex}

  \noindent
  \underline{\<open>lookup_bulkload\<close>}
  @{thm [display] lookup_bulkload}
  \vspace{1ex}

  \noindent
  \underline{\<open>lookup_map\<close>}
  @{thm [display] lookup_map}
  \vspace{1ex}
\<close>

end
