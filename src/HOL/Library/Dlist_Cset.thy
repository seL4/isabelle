(* Author: Florian Haftmann, TU Muenchen *)

header {* Canonical implementation of sets by distinct lists *}

theory Dlist_Cset
imports Dlist Cset
begin

definition Set :: "'a dlist \<Rightarrow> 'a Cset.set" where
  "Set dxs = Cset.set (list_of_dlist dxs)"

definition Coset :: "'a dlist \<Rightarrow> 'a Cset.set" where
  "Coset dxs = Cset.coset (list_of_dlist dxs)"

code_datatype Set Coset

lemma Set_Dlist [simp]:
  "Set (Dlist xs) = Cset.set xs"
  by (rule Cset.set_eqI) (simp add: Set_def)

lemma Coset_Dlist [simp]:
  "Coset (Dlist xs) = Cset.coset xs"
  by (rule Cset.set_eqI) (simp add: Coset_def)

lemma member_Set [simp]:
  "Cset.member (Set dxs) = List.member (list_of_dlist dxs)"
  by (simp add: Set_def fun_eq_iff List.member_def)

lemma member_Coset [simp]:
  "Cset.member (Coset dxs) = Not \<circ> List.member (list_of_dlist dxs)"
  by (simp add: Coset_def fun_eq_iff List.member_def)

lemma Set_dlist_of_list [code]:
  "Cset.set xs = Set (dlist_of_list xs)"
  by (rule Cset.set_eqI) simp

lemma Coset_dlist_of_list [code]:
  "Cset.coset xs = Coset (dlist_of_list xs)"
  by (rule Cset.set_eqI) simp

lemma is_empty_Set [code]:
  "Cset.is_empty (Set dxs) \<longleftrightarrow> Dlist.null dxs"
  by (simp add: Dlist.null_def List.null_def Set_def)

lemma bot_code [code]:
  "bot = Set Dlist.empty"
  by (simp add: empty_def)

lemma top_code [code]:
  "top = Coset Dlist.empty"
  by (simp add: empty_def Cset.coset_def)

lemma insert_code [code]:
  "Cset.insert x (Set dxs) = Set (Dlist.insert x dxs)"
  "Cset.insert x (Coset dxs) = Coset (Dlist.remove x dxs)"
  by (simp_all add: Dlist.insert_def Dlist.remove_def Cset.set_def Cset.coset_def Set_def Coset_def)

lemma remove_code [code]:
  "Cset.remove x (Set dxs) = Set (Dlist.remove x dxs)"
  "Cset.remove x (Coset dxs) = Coset (Dlist.insert x dxs)"
  by (simp_all add: Dlist.insert_def Dlist.remove_def Cset.set_def Cset.coset_def Set_def Coset_def Compl_insert)

lemma member_code [code]:
  "Cset.member (Set dxs) = Dlist.member dxs"
  "Cset.member (Coset dxs) = Not \<circ> Dlist.member dxs"
  by (simp_all add: List.member_def member_def fun_eq_iff Dlist.member_def)

lemma compl_code [code]:
  "- Set dxs = Coset dxs"
  "- Coset dxs = Set dxs"
  by (rule Cset.set_eqI, simp add: fun_eq_iff List.member_def Set_def Coset_def)+

lemma map_code [code]:
  "Cset.map f (Set dxs) = Set (Dlist.map f dxs)"
  by (rule Cset.set_eqI) (simp add: fun_eq_iff List.member_def Set_def)
  
lemma filter_code [code]:
  "Cset.filter f (Set dxs) = Set (Dlist.filter f dxs)"
  by (rule Cset.set_eqI) (simp add: fun_eq_iff List.member_def Set_def)

lemma forall_Set [code]:
  "Cset.forall P (Set xs) \<longleftrightarrow> list_all P (list_of_dlist xs)"
  by (simp add: Set_def list_all_iff)

lemma exists_Set [code]:
  "Cset.exists P (Set xs) \<longleftrightarrow> list_ex P (list_of_dlist xs)"
  by (simp add: Set_def list_ex_iff)

lemma card_code [code]:
  "Cset.card (Set dxs) = Dlist.length dxs"
  by (simp add: length_def Set_def distinct_card)

lemma inter_code [code]:
  "inf A (Set xs) = Set (Dlist.filter (Cset.member A) xs)"
  "inf A (Coset xs) = Dlist.foldr Cset.remove xs A"
  by (simp_all only: Set_def Coset_def foldr_def inter_project list_of_dlist_filter)

lemma subtract_code [code]:
  "A - Set xs = Dlist.foldr Cset.remove xs A"
  "A - Coset xs = Set (Dlist.filter (Cset.member A) xs)"
  by (simp_all only: Set_def Coset_def foldr_def subtract_remove list_of_dlist_filter)

lemma union_code [code]:
  "sup (Set xs) A = Dlist.foldr Cset.insert xs A"
  "sup (Coset xs) A = Coset (Dlist.filter (Not \<circ> Cset.member A) xs)"
  by (simp_all only: Set_def Coset_def foldr_def union_insert list_of_dlist_filter)

context complete_lattice
begin

lemma Infimum_code [code]:
  "Infimum (Set As) = Dlist.foldr inf As top"
  by (simp only: Set_def Infimum_inf foldr_def inf.commute)

lemma Supremum_code [code]:
  "Supremum (Set As) = Dlist.foldr sup As bot"
  by (simp only: Set_def Supremum_sup foldr_def sup.commute)

end

declare Cset.single_code[code]

lemma bind_set [code]:
  "Cset.bind (Dlist_Cset.Set xs) f = fold (sup \<circ> f) (list_of_dlist xs) Cset.empty"
  by (simp add: Cset.bind_set Set_def)
hide_fact (open) bind_set

lemma pred_of_cset_set [code]:
  "pred_of_cset (Dlist_Cset.Set xs) = foldr sup (map Predicate.single (list_of_dlist xs)) bot"
  by (simp add: Cset.pred_of_cset_set Dlist_Cset.Set_def)
hide_fact (open) pred_of_cset_set

export_code "Cset._" in Haskell

end
