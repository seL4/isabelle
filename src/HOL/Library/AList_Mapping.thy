(*  Title:      HOL/Library/AList_Mapping.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Implementation of mappings with Association Lists\<close>

theory AList_Mapping
  imports AList Mapping
begin

lift_definition Mapping :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) mapping" is map_of .

code_datatype Mapping

lemma lookup_Mapping [simp, code]: "Mapping.lookup (Mapping xs) = map_of xs"
  by transfer rule

lemma keys_Mapping [simp, code]: "Mapping.keys (Mapping xs) = set (map fst xs)"
  by transfer (simp add: dom_map_of_conv_image_fst)

lemma empty_Mapping [code]: "Mapping.empty = Mapping []"
  by transfer simp

lemma is_empty_Mapping [code]: "Mapping.is_empty (Mapping xs) \<longleftrightarrow> List.null xs"
  by (cases xs) (simp_all add: is_empty_def null_def)

lemma update_Mapping [code]: "Mapping.update k v (Mapping xs) = Mapping (AList.update k v xs)"
  by transfer (simp add: update_conv')

lemma delete_Mapping [code]: "Mapping.delete k (Mapping xs) = Mapping (AList.delete k xs)"
  by transfer (simp add: delete_conv')

lemma ordered_keys_Mapping [code]:
  "Mapping.ordered_keys (Mapping xs) = sort (remdups (map fst xs))"
  by (simp only: ordered_keys_def keys_Mapping sorted_list_of_set_sort_remdups) simp

lemma entries_Mapping [code]:
  "Mapping.entries (Mapping xs) = set (AList.clearjunk xs)"
  by transfer (fact graph_map_of)

lemma ordered_entries_Mapping [code]:
  "Mapping.ordered_entries (Mapping xs) = sort_key fst (AList.clearjunk xs)"
proof -
  have distinct: "distinct (sort_key fst (AList.clearjunk xs))"
    using distinct_clearjunk distinct_map distinct_sort by blast
  note folding_Map_graph.idem_if_sorted_distinct[where ?m="map_of xs", OF _ sorted_sort_key distinct]
  then show ?thesis
    unfolding ordered_entries_def
    by (transfer fixing: xs) (auto simp: graph_map_of)
qed

lemma fold_Mapping [code]:
  "Mapping.fold f (Mapping xs) a = List.fold (case_prod f) (sort_key fst (AList.clearjunk xs)) a"
  by (simp add: Mapping.fold_def ordered_entries_Mapping)

lemma size_Mapping [code]: "Mapping.size (Mapping xs) = length (remdups (map fst xs))"
  by (simp add: size_def length_remdups_card_conv dom_map_of_conv_image_fst)

lemma tabulate_Mapping [code]: "Mapping.tabulate ks f = Mapping (map (\<lambda>k. (k, f k)) ks)"
  by transfer (simp add: map_of_map_restrict)

lemma bulkload_Mapping [code]:
  "Mapping.bulkload vs = Mapping (map (\<lambda>n. (n, vs ! n)) [0..<length vs])"
  by transfer (simp add: map_of_map_restrict fun_eq_iff)

lemma equal_Mapping [code]:
  "HOL.equal (Mapping xs) (Mapping ys) \<longleftrightarrow>
    (let ks = map fst xs; ls = map fst ys
     in (\<forall>l\<in>set ls. l \<in> set ks) \<and> (\<forall>k\<in>set ks. k \<in> set ls \<and> map_of xs k = map_of ys k))"
proof -
  have *: "(a, b) \<in> set xs \<Longrightarrow> a \<in> fst ` set xs" for a b xs
    by (auto simp add: image_def intro!: bexI)
  show ?thesis
    apply transfer
    apply (auto intro!: map_of_eqI)
     apply (auto dest!: map_of_eq_dom intro: *)
    done
qed

lemma map_values_Mapping [code]:
  "Mapping.map_values f (Mapping xs) = Mapping (map (\<lambda>(x,y). (x, f x y)) xs)"
  for f :: "'c \<Rightarrow> 'a \<Rightarrow> 'b" and xs :: "('c \<times> 'a) list"
  apply transfer
  apply (rule ext)
  subgoal for f xs x by (induct xs) auto
  done

lemma combine_with_key_code [code]:
  "Mapping.combine_with_key f (Mapping xs) (Mapping ys) =
     Mapping.tabulate (remdups (map fst xs @ map fst ys))
       (\<lambda>x. the (combine_options (f x) (map_of xs x) (map_of ys x)))"
  apply transfer
  apply (rule ext)
  apply (rule sym)
  subgoal for f xs ys x
    apply (cases "map_of xs x"; cases "map_of ys x"; simp)
       apply (force simp: map_of_eq_None_iff combine_options_def option.the_def o_def image_iff
        dest: map_of_SomeD split: option.splits)+
    done
  done

lemma combine_code [code]:
  "Mapping.combine f (Mapping xs) (Mapping ys) =
     Mapping.tabulate (remdups (map fst xs @ map fst ys))
       (\<lambda>x. the (combine_options f (map_of xs x) (map_of ys x)))"
  apply transfer
  apply (rule ext)
  apply (rule sym)
  subgoal for f xs ys x
    apply (cases "map_of xs x"; cases "map_of ys x"; simp)
       apply (force simp: map_of_eq_None_iff combine_options_def option.the_def o_def image_iff
        dest: map_of_SomeD split: option.splits)+
    done
  done

lemma map_of_filter_distinct:  (* TODO: move? *)
  assumes "distinct (map fst xs)"
  shows "map_of (filter P xs) x =
    (case map_of xs x of
      None \<Rightarrow> None
    | Some y \<Rightarrow> if P (x,y) then Some y else None)"
  using assms
  by (auto simp: map_of_eq_None_iff filter_map distinct_map_filter dest: map_of_SomeD
      simp del: map_of_eq_Some_iff intro!: map_of_is_SomeI split: option.splits)

lemma filter_Mapping [code]:
  "Mapping.filter P (Mapping xs) = Mapping (filter (\<lambda>(k,v). P k v) (AList.clearjunk xs))"
  apply transfer
  apply (rule ext)
  apply (subst map_of_filter_distinct)
   apply (simp_all add: map_of_clearjunk split: option.split)
  done

lemma [code nbe]: "HOL.equal (x :: ('a, 'b) mapping) x \<longleftrightarrow> True"
  by (fact equal_refl)

end
