(* Author: Florian Haftmann, TU Muenchen *)

header {* An abstract view on maps for code generation. *}

theory Mapping
imports Main
begin

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
  "ordered_keys m = sorted_list_of_set (keys m)"

definition is_empty :: "('a, 'b) mapping \<Rightarrow> bool" where
  "is_empty m \<longleftrightarrow> dom (lookup m) = {}"

definition size :: "('a, 'b) mapping \<Rightarrow> nat" where
  "size m = (if finite (dom (lookup m)) then card (dom (lookup m)) else 0)"

definition replace :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" where
  "replace k v m = (if lookup m k = None then m else update k v m)"

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

lemma lookup_empty [simp]:
  "lookup empty = Map.empty"
  by (simp add: empty_def)

lemma lookup_update [simp]:
  "lookup (update k v m) = (lookup m) (k \<mapsto> v)"
  by (cases m) simp

lemma lookup_delete [simp]:
  "lookup (delete k m) = (lookup m) (k := None)"
  by (cases m) simp

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
  "k \<notin> dom (lookup m) \<Longrightarrow> replace k v m = m"
  "k \<in> dom (lookup m) \<Longrightarrow> replace k v m = update k v m"
  by (rule mapping_eqI, auto simp add: replace_def fun_upd_twist)+

lemma size_empty [simp]:
  "size empty = 0"
  by (simp add: size_def)

lemma size_update:
  "finite (dom (lookup m)) \<Longrightarrow> size (update k v m) =
    (if k \<in> dom (lookup m) then size m else Suc (size m))"
  by (auto simp add: size_def insert_dom)

lemma size_delete:
  "size (delete k m) = (if k \<in> dom (lookup m) then size m - 1 else size m)"
  by (simp add: size_def)

lemma size_tabulate:
  "size (tabulate ks f) = length (remdups ks)"
  by (simp add: size_def distinct_card [of "remdups ks", symmetric] comp_def)

lemma bulkload_tabulate:
  "bulkload xs = tabulate [0..<length xs] (nth xs)"
  by (rule mapping_eqI) (simp add: expand_fun_eq)


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


hide (open) const empty is_empty lookup update delete ordered_keys keys size replace tabulate bulkload

end