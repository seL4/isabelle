(* Author: Florian Haftmann, TU Muenchen *)

header {* An abstract view on maps for code generation. *}

theory Mapping
imports Main
begin

lemma remove1_idem: (*FIXME move to List.thy*)
  assumes "x \<notin> set xs"
  shows "remove1 x xs = xs"
  using assms by (induct xs) simp_all

lemma remove1_insort [simp]:
  "remove1 x (insort x xs) = xs"
  by (induct xs) simp_all

lemma sorted_list_of_set_remove:
  assumes "finite A"
  shows "sorted_list_of_set (A - {x}) = remove1 x (sorted_list_of_set A)"
proof (cases "x \<in> A")
  case False with assms have "x \<notin> set (sorted_list_of_set A)" by simp
  with False show ?thesis by (simp add: remove1_idem)
next
  case True then obtain B where A: "A = insert x B" by (rule Set.set_insert)
  with assms show ?thesis by simp
qed

lemma sorted_list_of_set_range [simp]:
  "sorted_list_of_set {m..<n} = [m..<n]"
  by (rule sorted_distinct_set_unique) simp_all

subsection {* Type definition and primitive operations *}

datatype ('a, 'b) mapping = Mapping "'a \<rightharpoonup> 'b"

definition empty :: "('a, 'b) mapping" where
  "empty = Mapping (\<lambda>_. None)"

primrec lookup :: "('a, 'b) mapping \<Rightarrow> 'a \<rightharpoonup> 'b" where
  "lookup (Mapping f) = f"

primrec update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" where
  "update k v (Mapping f) = Mapping (f (k \<mapsto> v))"

primrec delete :: "'a \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" where
  "delete k (Mapping f) = Mapping (f (k := None))"


subsection {* Derived operations *}

definition keys :: "('a, 'b) mapping \<Rightarrow> 'a set" where
  "keys m = dom (lookup m)"

definition ordered_keys :: "('a\<Colon>linorder, 'b) mapping \<Rightarrow> 'a list" where
  "ordered_keys m = (if finite (keys m) then sorted_list_of_set (keys m) else [])"

definition is_empty :: "('a, 'b) mapping \<Rightarrow> bool" where
  "is_empty m \<longleftrightarrow> keys m = {}"

definition size :: "('a, 'b) mapping \<Rightarrow> nat" where
  "size m = (if finite (keys m) then card (keys m) else 0)"

definition replace :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" where
  "replace k v m = (if k \<in> keys m then update k v m else m)"

definition default :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" where
  "default k v m = (if k \<in> keys m then m else update k v m)"

definition map_entry :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" where
  "map_entry k f m = (case lookup m k of None \<Rightarrow> m
    | Some v \<Rightarrow> update k (f v) m)" 

definition map_default :: "'a \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" where
  "map_default k v f m = map_entry k f (default k v m)" 

definition tabulate :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping" where
  "tabulate ks f = Mapping (map_of (map (\<lambda>k. (k, f k)) ks))"

definition bulkload :: "'a list \<Rightarrow> (nat, 'a) mapping" where
  "bulkload xs = Mapping (\<lambda>k. if k < length xs then Some (xs ! k) else None)"


subsection {* Properties *}

lemma lookup_inject [simp]:
  "lookup m = lookup n \<longleftrightarrow> m = n"
  by (cases m, cases n) simp

lemma mapping_eqI:
  assumes "lookup m = lookup n"
  shows "m = n"
  using assms by simp

lemma keys_is_none_lookup [code_inline]:
  "k \<in> keys m \<longleftrightarrow> \<not> (Option.is_none (lookup m k))"
  by (auto simp add: keys_def is_none_def)

lemma lookup_empty [simp]:
  "lookup empty = Map.empty"
  by (simp add: empty_def)

lemma lookup_update [simp]:
  "lookup (update k v m) = (lookup m) (k \<mapsto> v)"
  by (cases m) simp

lemma lookup_delete [simp]:
  "lookup (delete k m) = (lookup m) (k := None)"
  by (cases m) simp

lemma lookup_map_entry [simp]:
  "lookup (map_entry k f m) = (lookup m) (k := Option.map f (lookup m k))"
  by (cases "lookup m k") (simp_all add: map_entry_def expand_fun_eq)

lemma lookup_tabulate [simp]:
  "lookup (tabulate ks f) = (Some o f) |` set ks"
  by (induct ks) (auto simp add: tabulate_def restrict_map_def expand_fun_eq)

lemma lookup_bulkload [simp]:
  "lookup (bulkload xs) = (\<lambda>k. if k < length xs then Some (xs ! k) else None)"
  by (simp add: bulkload_def)

lemma update_update:
  "update k v (update k w m) = update k v m"
  "k \<noteq> l \<Longrightarrow> update k v (update l w m) = update l w (update k v m)"
  by (rule mapping_eqI, simp add: fun_upd_twist)+

lemma update_delete [simp]:
  "update k v (delete k m) = update k v m"
  by (rule mapping_eqI) simp

lemma delete_update:
  "delete k (update k v m) = delete k m"
  "k \<noteq> l \<Longrightarrow> delete k (update l v m) = update l v (delete k m)"
  by (rule mapping_eqI, simp add: fun_upd_twist)+

lemma delete_empty [simp]:
  "delete k empty = empty"
  by (rule mapping_eqI) simp

lemma replace_update:
  "k \<notin> keys m \<Longrightarrow> replace k v m = m"
  "k \<in> keys m \<Longrightarrow> replace k v m = update k v m"
  by (rule mapping_eqI) (auto simp add: replace_def fun_upd_twist)+

lemma size_empty [simp]:
  "size empty = 0"
  by (simp add: size_def keys_def)

lemma size_update:
  "finite (keys m) \<Longrightarrow> size (update k v m) =
    (if k \<in> keys m then size m else Suc (size m))"
  by (auto simp add: size_def insert_dom keys_def)

lemma size_delete:
  "size (delete k m) = (if k \<in> keys m then size m - 1 else size m)"
  by (simp add: size_def keys_def)

lemma size_tabulate [simp]:
  "size (tabulate ks f) = length (remdups ks)"
  by (simp add: size_def distinct_card [of "remdups ks", symmetric] comp_def keys_def)

lemma bulkload_tabulate:
  "bulkload xs = tabulate [0..<length xs] (nth xs)"
  by (rule mapping_eqI) (simp add: expand_fun_eq)

lemma is_empty_empty: (*FIXME*)
  "is_empty m \<longleftrightarrow> m = Mapping Map.empty"
  by (cases m) (simp add: is_empty_def keys_def)

lemma is_empty_empty' [simp]:
  "is_empty empty"
  by (simp add: is_empty_empty empty_def) 

lemma is_empty_update [simp]:
  "\<not> is_empty (update k v m)"
  by (cases m) (simp add: is_empty_empty)

lemma is_empty_delete:
  "is_empty (delete k m) \<longleftrightarrow> is_empty m \<or> keys m = {k}"
  by (cases m) (auto simp add: is_empty_empty keys_def dom_eq_empty_conv [symmetric] simp del: dom_eq_empty_conv)

lemma is_empty_replace [simp]:
  "is_empty (replace k v m) \<longleftrightarrow> is_empty m"
  by (auto simp add: replace_def) (simp add: is_empty_def)

lemma is_empty_default [simp]:
  "\<not> is_empty (default k v m)"
  by (auto simp add: default_def) (simp add: is_empty_def)

lemma is_empty_map_entry [simp]:
  "is_empty (map_entry k f m) \<longleftrightarrow> is_empty m"
  by (cases "lookup m k")
    (auto simp add: map_entry_def, simp add: is_empty_empty)

lemma is_empty_map_default [simp]:
  "\<not> is_empty (map_default k v f m)"
  by (simp add: map_default_def)

lemma keys_empty [simp]:
  "keys empty = {}"
  by (simp add: keys_def)

lemma keys_update [simp]:
  "keys (update k v m) = insert k (keys m)"
  by (simp add: keys_def)

lemma keys_delete [simp]:
  "keys (delete k m) = keys m - {k}"
  by (simp add: keys_def)

lemma keys_replace [simp]:
  "keys (replace k v m) = keys m"
  by (auto simp add: keys_def replace_def)

lemma keys_default [simp]:
  "keys (default k v m) = insert k (keys m)"
  by (auto simp add: keys_def default_def)

lemma keys_map_entry [simp]:
  "keys (map_entry k f m) = keys m"
  by (auto simp add: keys_def)

lemma keys_map_default [simp]:
  "keys (map_default k v f m) = insert k (keys m)"
  by (simp add: map_default_def)

lemma keys_tabulate [simp]:
  "keys (tabulate ks f) = set ks"
  by (simp add: tabulate_def keys_def map_of_map_restrict o_def)

lemma keys_bulkload [simp]:
  "keys (bulkload xs) = {0..<length xs}"
  by (simp add: keys_tabulate bulkload_tabulate)

lemma distinct_ordered_keys [simp]:
  "distinct (ordered_keys m)"
  by (simp add: ordered_keys_def)

lemma ordered_keys_infinite [simp]:
  "\<not> finite (keys m) \<Longrightarrow> ordered_keys m = []"
  by (simp add: ordered_keys_def)

lemma ordered_keys_empty [simp]:
  "ordered_keys empty = []"
  by (simp add: ordered_keys_def)

lemma ordered_keys_update [simp]:
  "k \<in> keys m \<Longrightarrow> ordered_keys (update k v m) = ordered_keys m"
  "finite (keys m) \<Longrightarrow> k \<notin> keys m \<Longrightarrow> ordered_keys (update k v m) = insort k (ordered_keys m)"
  by (simp_all add: ordered_keys_def) (auto simp only: sorted_list_of_set_insert [symmetric] insert_absorb)

lemma ordered_keys_delete [simp]:
  "ordered_keys (delete k m) = remove1 k (ordered_keys m)"
proof (cases "finite (keys m)")
  case False then show ?thesis by simp
next
  case True note fin = True
  show ?thesis
  proof (cases "k \<in> keys m")
    case False with fin have "k \<notin> set (sorted_list_of_set (keys m))" by simp
    with False show ?thesis by (simp add: ordered_keys_def remove1_idem)
  next
    case True with fin show ?thesis by (simp add: ordered_keys_def sorted_list_of_set_remove)
  qed
qed

lemma ordered_keys_replace [simp]:
  "ordered_keys (replace k v m) = ordered_keys m"
  by (simp add: replace_def)

lemma ordered_keys_default [simp]:
  "k \<in> keys m \<Longrightarrow> ordered_keys (default k v m) = ordered_keys m"
  "finite (keys m) \<Longrightarrow> k \<notin> keys m \<Longrightarrow> ordered_keys (default k v m) = insort k (ordered_keys m)"
  by (simp_all add: default_def)

lemma ordered_keys_map_entry [simp]:
  "ordered_keys (map_entry k f m) = ordered_keys m"
  by (simp add: ordered_keys_def)

lemma ordered_keys_map_default [simp]:
  "k \<in> keys m \<Longrightarrow> ordered_keys (map_default k v f m) = ordered_keys m"
  "finite (keys m) \<Longrightarrow> k \<notin> keys m \<Longrightarrow> ordered_keys (map_default k v f m) = insort k (ordered_keys m)"
  by (simp_all add: map_default_def)

lemma ordered_keys_tabulate [simp]:
  "ordered_keys (tabulate ks f) = sort (remdups ks)"
  by (simp add: ordered_keys_def sorted_list_of_set_sort_remdups)

lemma ordered_keys_bulkload [simp]:
  "ordered_keys (bulkload ks) = [0..<length ks]"
  by (simp add: ordered_keys_def)


subsection {* Some technical code lemmas *}

lemma [code]:
  "mapping_case f m = f (Mapping.lookup m)"
  by (cases m) simp

lemma [code]:
  "mapping_rec f m = f (Mapping.lookup m)"
  by (cases m) simp

lemma [code]:
  "Nat.size (m :: (_, _) mapping) = 0"
  by (cases m) simp

lemma [code]:
  "mapping_size f g m = 0"
  by (cases m) simp


hide_const (open) empty is_empty lookup update delete ordered_keys keys size replace tabulate bulkload

end