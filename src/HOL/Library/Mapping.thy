(*  Title:      HOL/Library/Mapping.thy
    Author:     Florian Haftmann and Ondrej Kuncar
*)

header {* An abstract view on maps for code generation. *}

theory Mapping
imports Main
begin

subsection {* Parametricity transfer rules *}

context
begin
interpretation lifting_syntax .

lemma empty_transfer: "(A ===> option_rel B) Map.empty Map.empty" by transfer_prover

lemma lookup_transfer: "((A ===> B) ===> A ===> B) (\<lambda>m k. m k) (\<lambda>m k. m k)" by transfer_prover

lemma update_transfer:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> B ===> (A ===> option_rel B) ===> A ===> option_rel B) 
          (\<lambda>k v m. m(k \<mapsto> v)) (\<lambda>k v m. m(k \<mapsto> v))"
by transfer_prover

lemma delete_transfer:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> (A ===> option_rel B) ===> A ===> option_rel B) 
          (\<lambda>k m. m(k := None)) (\<lambda>k m. m(k := None))"
by transfer_prover

definition equal_None :: "'a option \<Rightarrow> bool" where "equal_None x \<equiv> x = None"

lemma [transfer_rule]: "(option_rel A ===> op=) equal_None equal_None" 
unfolding fun_rel_def option_rel_def equal_None_def by (auto split: option.split)

lemma dom_transfer:
  assumes [transfer_rule]: "bi_total A"
  shows "((A ===> option_rel B) ===> set_rel A) dom dom" 
unfolding dom_def[abs_def] equal_None_def[symmetric] 
by transfer_prover

lemma map_of_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique R1"
  shows "(list_all2 (prod_rel R1 R2) ===> R1 ===> option_rel R2) map_of map_of"
unfolding map_of_def by transfer_prover

lemma tabulate_transfer: 
  assumes [transfer_rule]: "bi_unique A"
  shows "(list_all2 A ===> (A ===> B) ===> A ===> option_rel B) 
    (\<lambda>ks f. (map_of (List.map (\<lambda>k. (k, f k)) ks))) (\<lambda>ks f. (map_of (List.map (\<lambda>k. (k, f k)) ks)))"
by transfer_prover

lemma bulkload_transfer: 
  "(list_all2 A ===> op= ===> option_rel A) 
    (\<lambda>xs k. if k < length xs then Some (xs ! k) else None) (\<lambda>xs k. if k < length xs then Some (xs ! k) else None)"
unfolding fun_rel_def 
apply clarsimp 
apply (erule list_all2_induct) 
  apply simp 
apply (case_tac xa) 
  apply simp 
by (auto dest: list_all2_lengthD list_all2_nthD)

lemma map_transfer: 
  "((A ===> B) ===> (C ===> D) ===> (B ===> option_rel C) ===> A ===> option_rel D) 
    (\<lambda>f g m. (map_option g \<circ> m \<circ> f)) (\<lambda>f g m. (map_option g \<circ> m \<circ> f))"
by transfer_prover

lemma map_entry_transfer:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> (B ===> B) ===> (A ===> option_rel B) ===> A ===> option_rel B) 
    (\<lambda>k f m. (case m k of None \<Rightarrow> m
      | Some v \<Rightarrow> m (k \<mapsto> (f v)))) (\<lambda>k f m. (case m k of None \<Rightarrow> m
      | Some v \<Rightarrow> m (k \<mapsto> (f v))))"
by transfer_prover

end

subsection {* Type definition and primitive operations *}

typedef ('a, 'b) mapping = "UNIV :: ('a \<rightharpoonup> 'b) set"
  morphisms rep Mapping ..

setup_lifting(no_code) type_definition_mapping

lift_definition empty :: "('a, 'b) mapping" is Map.empty parametric empty_transfer .

lift_definition lookup :: "('a, 'b) mapping \<Rightarrow> 'a \<Rightarrow> 'b option" is "\<lambda>m k. m k" 
  parametric lookup_transfer .

lift_definition update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" is "\<lambda>k v m. m(k \<mapsto> v)" 
  parametric update_transfer .

lift_definition delete :: "'a \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" is "\<lambda>k m. m(k := None)" 
  parametric delete_transfer .

lift_definition keys :: "('a, 'b) mapping \<Rightarrow> 'a set" is dom parametric dom_transfer .

lift_definition tabulate :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>ks f. (map_of (List.map (\<lambda>k. (k, f k)) ks))" parametric tabulate_transfer .

lift_definition bulkload :: "'a list \<Rightarrow> (nat, 'a) mapping" is
  "\<lambda>xs k. if k < length xs then Some (xs ! k) else None" parametric bulkload_transfer .

lift_definition map :: "('c \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('c, 'd) mapping" is
  "\<lambda>f g m. (map_option g \<circ> m \<circ> f)" parametric map_transfer .


subsection {* Functorial structure *}

functor map: map
  by (transfer, auto simp add: fun_eq_iff option.map_comp option.map_id)+


subsection {* Derived operations *}

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

lift_definition map_entry :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>k f m. (case m k of None \<Rightarrow> m
    | Some v \<Rightarrow> m (k \<mapsto> (f v)))" parametric map_entry_transfer .

lemma map_entry_code [code]: "map_entry k f m = (case lookup m k of None \<Rightarrow> m
    | Some v \<Rightarrow> update k (f v) m)"
  by transfer rule

definition map_default :: "'a \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" where
  "map_default k v f m = map_entry k f (default k v m)" 

lift_definition of_alist :: "('k \<times> 'v) list \<Rightarrow> ('k, 'v) mapping"
is map_of parametric map_of_transfer .

lemma of_alist_code [code]:
  "of_alist xs = foldr (\<lambda>(k, v) m. update k v m) xs empty"
by transfer(simp add: map_add_map_of_foldr[symmetric])

instantiation mapping :: (type, type) equal
begin

definition
  "HOL.equal m1 m2 \<longleftrightarrow> (\<forall>k. lookup m1 k = lookup m2 k)"

instance proof
qed (unfold equal_mapping_def, transfer, auto)

end

context
begin
interpretation lifting_syntax .

lemma [transfer_rule]:
  assumes [transfer_rule]: "bi_total A"
  assumes [transfer_rule]: "bi_unique B"
  shows  "(pcr_mapping A B ===> pcr_mapping A B ===> op=) HOL.eq HOL.equal"
by (unfold equal) transfer_prover

end

subsection {* Properties *}

lemma lookup_update: "lookup (update k v m) k = Some v" 
  by transfer simp

lemma lookup_update_neq: "k \<noteq> k' \<Longrightarrow> lookup (update k v m) k' = lookup m k'" 
  by transfer simp

lemma lookup_empty: "lookup empty k = None" 
  by transfer simp

lemma keys_is_none_rep [code_unfold]:
  "k \<in> keys m \<longleftrightarrow> \<not> (Option.is_none (lookup m k))"
  by transfer (auto simp add: is_none_def)

lemma tabulate_alt_def:
  "map_of (List.map (\<lambda>k. (k, f k)) ks) = (Some o f) |` set ks"
  by (induct ks) (auto simp add: tabulate_def restrict_map_def)

lemma update_update:
  "update k v (update k w m) = update k v m"
  "k \<noteq> l \<Longrightarrow> update k v (update l w m) = update l w (update k v m)"
  by (transfer, simp add: fun_upd_twist)+

lemma update_delete [simp]:
  "update k v (delete k m) = update k v m"
  by transfer simp

lemma delete_update:
  "delete k (update k v m) = delete k m"
  "k \<noteq> l \<Longrightarrow> delete k (update l v m) = update l v (delete k m)"
  by (transfer, simp add: fun_upd_twist)+

lemma delete_empty [simp]:
  "delete k empty = empty"
  by transfer simp

lemma replace_update:
  "k \<notin> keys m \<Longrightarrow> replace k v m = m"
  "k \<in> keys m \<Longrightarrow> replace k v m = update k v m"
  by (transfer, auto simp add: replace_def fun_upd_twist)+

lemma size_empty [simp]:
  "size empty = 0"
  unfolding size_def by transfer simp

lemma size_update:
  "finite (keys m) \<Longrightarrow> size (update k v m) =
    (if k \<in> keys m then size m else Suc (size m))"
  unfolding size_def by transfer (auto simp add: insert_dom)

lemma size_delete:
  "size (delete k m) = (if k \<in> keys m then size m - 1 else size m)"
  unfolding size_def by transfer simp

lemma size_tabulate [simp]:
  "size (tabulate ks f) = length (remdups ks)"
  unfolding size_def by transfer (auto simp add: tabulate_alt_def card_set comp_def)

lemma bulkload_tabulate:
  "bulkload xs = tabulate [0..<length xs] (nth xs)"
  by transfer (auto simp add: tabulate_alt_def)

lemma is_empty_empty [simp]:
  "is_empty empty"
  unfolding is_empty_def by transfer simp 

lemma is_empty_update [simp]:
  "\<not> is_empty (update k v m)"
  unfolding is_empty_def by transfer simp

lemma is_empty_delete:
  "is_empty (delete k m) \<longleftrightarrow> is_empty m \<or> keys m = {k}"
  unfolding is_empty_def by transfer (auto simp del: dom_eq_empty_conv)

lemma is_empty_replace [simp]:
  "is_empty (replace k v m) \<longleftrightarrow> is_empty m"
  unfolding is_empty_def replace_def by transfer auto

lemma is_empty_default [simp]:
  "\<not> is_empty (default k v m)"
  unfolding is_empty_def default_def by transfer auto

lemma is_empty_map_entry [simp]:
  "is_empty (map_entry k f m) \<longleftrightarrow> is_empty m"
  unfolding is_empty_def 
  apply transfer by (case_tac "m k") auto

lemma is_empty_map_default [simp]:
  "\<not> is_empty (map_default k v f m)"
  by (simp add: map_default_def)

lemma keys_empty [simp]:
  "keys empty = {}"
  by transfer simp

lemma keys_update [simp]:
  "keys (update k v m) = insert k (keys m)"
  by transfer simp

lemma keys_delete [simp]:
  "keys (delete k m) = keys m - {k}"
  by transfer simp

lemma keys_replace [simp]:
  "keys (replace k v m) = keys m"
  unfolding replace_def by transfer (simp add: insert_absorb)

lemma keys_default [simp]:
  "keys (default k v m) = insert k (keys m)"
  unfolding default_def by transfer (simp add: insert_absorb)

lemma keys_map_entry [simp]:
  "keys (map_entry k f m) = keys m"
  apply transfer by (case_tac "m k") auto

lemma keys_map_default [simp]:
  "keys (map_default k v f m) = insert k (keys m)"
  by (simp add: map_default_def)

lemma keys_tabulate [simp]:
  "keys (tabulate ks f) = set ks"
  by transfer (simp add: map_of_map_restrict o_def)

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


subsection {* Code generator setup *}

code_datatype empty update

hide_const (open) empty is_empty rep lookup update delete ordered_keys keys size
  replace default map_entry map_default tabulate bulkload map of_alist

end
