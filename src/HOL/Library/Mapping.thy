(* Author: Florian Haftmann, TU Muenchen *)

header {* An abstract view on maps for code generation. *}

theory Mapping
imports Map Main
begin

subsection {* Type definition and primitive operations *}

datatype ('a, 'b) map = Map "'a \<rightharpoonup> 'b"

definition empty :: "('a, 'b) map" where
  "empty = Map (\<lambda>_. None)"

primrec lookup :: "('a, 'b) map \<Rightarrow> 'a \<rightharpoonup> 'b" where
  "lookup (Map f) = f"

primrec update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) map \<Rightarrow> ('a, 'b) map" where
  "update k v (Map f) = Map (f (k \<mapsto> v))"

primrec delete :: "'a \<Rightarrow> ('a, 'b) map \<Rightarrow> ('a, 'b) map" where
  "delete k (Map f) = Map (f (k := None))"

primrec keys :: "('a, 'b) map \<Rightarrow> 'a set" where
  "keys (Map f) = dom f"


subsection {* Derived operations *}

definition size :: "('a, 'b) map \<Rightarrow> nat" where
  "size m = (if finite (keys m) then card (keys m) else 0)"

definition replace :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) map \<Rightarrow> ('a, 'b) map" where
  "replace k v m = (if lookup m k = None then m else update k v m)"

definition tabulate :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) map" where
  "tabulate ks f = Map (map_of (map (\<lambda>k. (k, f k)) ks))"

definition bulkload :: "'a list \<Rightarrow> (nat, 'a) map" where
  "bulkload xs = Map (\<lambda>k. if k < length xs then Some (xs ! k) else None)"


subsection {* Properties *}

lemma lookup_inject:
  "lookup m = lookup n \<longleftrightarrow> m = n"
  by (cases m, cases n) simp

lemma lookup_empty [simp]:
  "lookup empty = Map.empty"
  by (simp add: empty_def)

lemma lookup_update [simp]:
  "lookup (update k v m) = (lookup m) (k \<mapsto> v)"
  by (cases m) simp

lemma lookup_delete:
  "lookup (delete k m) k = None"
  "k \<noteq> l \<Longrightarrow> lookup (delete k m) l = lookup m l"
  by (cases m, simp)+

lemma lookup_tabulate:
  "lookup (tabulate ks f) = (Some o f) |` set ks"
  by (induct ks) (auto simp add: tabulate_def restrict_map_def expand_fun_eq)

lemma lookup_bulkload:
  "lookup (bulkload xs) = (\<lambda>k. if k < length xs then Some (xs ! k) else None)"
  unfolding bulkload_def by simp

lemma update_update:
  "update k v (update k w m) = update k v m"
  "k \<noteq> l \<Longrightarrow> update k v (update l w m) = update l w (update k v m)"
  by (cases m, simp add: expand_fun_eq)+

lemma replace_update:
  "lookup m k = None \<Longrightarrow> replace k v m = m"
  "lookup m k \<noteq> None \<Longrightarrow> replace k v m = update k v m"
  by (auto simp add: replace_def)

lemma delete_empty [simp]:
  "delete k empty = empty"
  by (simp add: empty_def)

lemma delete_update:
  "delete k (update k v m) = delete k m"
  "k \<noteq> l \<Longrightarrow> delete k (update l v m) = update l v (delete k m)"
  by (cases m, simp add: expand_fun_eq)+

lemma update_delete [simp]:
  "update k v (delete k m) = update k v m"
  by (cases m) simp

lemma keys_empty [simp]:
  "keys empty = {}"
  unfolding empty_def by simp

lemma keys_update [simp]:
  "keys (update k v m) = insert k (keys m)"
  by (cases m) simp

lemma keys_delete [simp]:
  "keys (delete k m) = keys m - {k}"
  by (cases m) simp

lemma keys_tabulate [simp]:
  "keys (tabulate ks f) = set ks"
  by (auto simp add: tabulate_def dest: map_of_SomeD intro!: weak_map_of_SomeI)

lemma size_empty [simp]:
  "size empty = 0"
  by (simp add: size_def keys_empty)

lemma size_update:
  "finite (keys m) \<Longrightarrow> size (update k v m) =
    (if k \<in> keys m then size m else Suc (size m))"
  by (simp add: size_def keys_update)
    (auto simp only: card_insert card_Suc_Diff1)

lemma size_delete:
  "size (delete k m) = (if k \<in> keys m then size m - 1 else size m)"
  by (simp add: size_def keys_delete)

lemma size_tabulate:
  "size (tabulate ks f) = length (remdups ks)"
  by (simp add: size_def keys_tabulate distinct_card [of "remdups ks", symmetric])

lemma bulkload_tabulate:
  "bulkload xs = tabulate [0..<length xs] (nth xs)"
  by (rule sym)
    (auto simp add: bulkload_def tabulate_def expand_fun_eq map_of_eq_None_iff map_compose [symmetric] comp_def)


subsection {* Some technical code lemmas *}

lemma [code]:
  "map_case f m = f (Mapping.lookup m)"
  by (cases m) simp

lemma [code]:
  "map_rec f m = f (Mapping.lookup m)"
  by (cases m) simp

lemma [code]:
  "Nat.size (m :: (_, _) map) = 0"
  by (cases m) simp

lemma [code]:
  "map_size f g m = 0"
  by (cases m) simp

end