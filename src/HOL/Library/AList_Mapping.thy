(* Title: HOL/Library/AList_Mapping.thy
   Author: Florian Haftmann, TU Muenchen
*)

header {* Implementation of mappings with Association Lists *}

theory AList_Mapping
imports AList Mapping
begin

lift_definition Mapping :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) mapping" is map_of .

code_datatype Mapping

lemma lookup_Mapping [simp, code]:
  "Mapping.lookup (Mapping xs) = map_of xs"
  by transfer rule

lemma keys_Mapping [simp, code]:
  "Mapping.keys (Mapping xs) = set (map fst xs)" 
  by transfer (simp add: dom_map_of_conv_image_fst)

lemma empty_Mapping [code]:
  "Mapping.empty = Mapping []"
  by transfer simp

lemma is_empty_Mapping [code]:
  "Mapping.is_empty (Mapping xs) \<longleftrightarrow> List.null xs"
  by (case_tac xs) (simp_all add: is_empty_def null_def)

lemma update_Mapping [code]:
  "Mapping.update k v (Mapping xs) = Mapping (AList.update k v xs)"
  by transfer (simp add: update_conv')

lemma delete_Mapping [code]:
  "Mapping.delete k (Mapping xs) = Mapping (AList.delete k xs)"
  by transfer (simp add: delete_conv')

lemma ordered_keys_Mapping [code]:
  "Mapping.ordered_keys (Mapping xs) = sort (remdups (map fst xs))"
  by (simp only: ordered_keys_def keys_Mapping sorted_list_of_set_sort_remdups) simp

lemma size_Mapping [code]:
  "Mapping.size (Mapping xs) = length (remdups (map fst xs))"
  by (simp add: size_def length_remdups_card_conv dom_map_of_conv_image_fst)

lemma tabulate_Mapping [code]:
  "Mapping.tabulate ks f = Mapping (map (\<lambda>k. (k, f k)) ks)"
  by transfer (simp add: map_of_map_restrict)

lemma bulkload_Mapping [code]:
  "Mapping.bulkload vs = Mapping (map (\<lambda>n. (n, vs ! n)) [0..<length vs])"
  by transfer (simp add: map_of_map_restrict fun_eq_iff)

lemma equal_Mapping [code]:
  "HOL.equal (Mapping xs) (Mapping ys) \<longleftrightarrow>
    (let ks = map fst xs; ls = map fst ys
    in (\<forall>l\<in>set ls. l \<in> set ks) \<and> (\<forall>k\<in>set ks. k \<in> set ls \<and> map_of xs k = map_of ys k))"
proof -
  have aux: "\<And>a b xs. (a, b) \<in> set xs \<Longrightarrow> a \<in> fst ` set xs"
    by (auto simp add: image_def intro!: bexI)
  show ?thesis apply transfer 
  by (auto intro!: map_of_eqI) (auto dest!: map_of_eq_dom intro: aux)
qed

lemma [code nbe]:
  "HOL.equal (x :: ('a, 'b) mapping) x \<longleftrightarrow> True"
  by (fact equal_refl)
  
end
