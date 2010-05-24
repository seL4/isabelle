(* Author: Florian Haftmann, TU Muenchen *)

header {* Lists with elements distinct as canonical example for datatype invariants *}

theory Dlist
imports Main More_List Fset
begin

section {* The type of distinct lists *}

typedef (open) 'a dlist = "{xs::'a list. distinct xs}"
  morphisms list_of_dlist Abs_dlist
proof
  show "[] \<in> ?dlist" by simp
qed

lemma dlist_ext:
  assumes "list_of_dlist xs = list_of_dlist ys"
  shows "xs = ys"
  using assms by (simp add: list_of_dlist_inject)


text {* Formal, totalized constructor for @{typ "'a dlist"}: *}

definition Dlist :: "'a list \<Rightarrow> 'a dlist" where
  [code del]: "Dlist xs = Abs_dlist (remdups xs)"

lemma distinct_list_of_dlist [simp]:
  "distinct (list_of_dlist dxs)"
  using list_of_dlist [of dxs] by simp

lemma list_of_dlist_Dlist [simp]:
  "list_of_dlist (Dlist xs) = remdups xs"
  by (simp add: Dlist_def Abs_dlist_inverse)

lemma Dlist_list_of_dlist [simp, code abstype]:
  "Dlist (list_of_dlist dxs) = dxs"
  by (simp add: Dlist_def list_of_dlist_inverse distinct_remdups_id)


text {* Fundamental operations: *}

definition empty :: "'a dlist" where
  "empty = Dlist []"

definition insert :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "insert x dxs = Dlist (List.insert x (list_of_dlist dxs))"

definition remove :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "remove x dxs = Dlist (remove1 x (list_of_dlist dxs))"

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b dlist" where
  "map f dxs = Dlist (remdups (List.map f (list_of_dlist dxs)))"

definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "filter P dxs = Dlist (List.filter P (list_of_dlist dxs))"


text {* Derived operations: *}

definition null :: "'a dlist \<Rightarrow> bool" where
  "null dxs = List.null (list_of_dlist dxs)"

definition member :: "'a dlist \<Rightarrow> 'a \<Rightarrow> bool" where
  "member dxs = List.member (list_of_dlist dxs)"

definition length :: "'a dlist \<Rightarrow> nat" where
  "length dxs = List.length (list_of_dlist dxs)"

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b" where
  "fold f dxs = More_List.fold f (list_of_dlist dxs)"

definition foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b" where
  "foldr f dxs = List.foldr f (list_of_dlist dxs)"


section {* Executable version obeying invariant *}

lemma list_of_dlist_empty [simp, code abstract]:
  "list_of_dlist empty = []"
  by (simp add: empty_def)

lemma list_of_dlist_insert [simp, code abstract]:
  "list_of_dlist (insert x dxs) = List.insert x (list_of_dlist dxs)"
  by (simp add: insert_def)

lemma list_of_dlist_remove [simp, code abstract]:
  "list_of_dlist (remove x dxs) = remove1 x (list_of_dlist dxs)"
  by (simp add: remove_def)

lemma list_of_dlist_map [simp, code abstract]:
  "list_of_dlist (map f dxs) = remdups (List.map f (list_of_dlist dxs))"
  by (simp add: map_def)

lemma list_of_dlist_filter [simp, code abstract]:
  "list_of_dlist (filter P dxs) = List.filter P (list_of_dlist dxs)"
  by (simp add: filter_def)


text {* Explicit executable conversion *}

definition dlist_of_list [simp]:
  "dlist_of_list = Dlist"

lemma [code abstract]:
  "list_of_dlist (dlist_of_list xs) = remdups xs"
  by simp


section {* Induction principle and case distinction *}

lemma dlist_induct [case_names empty insert, induct type: dlist]:
  assumes empty: "P empty"
  assumes insrt: "\<And>x dxs. \<not> member dxs x \<Longrightarrow> P dxs \<Longrightarrow> P (insert x dxs)"
  shows "P dxs"
proof (cases dxs)
  case (Abs_dlist xs)
  then have "distinct xs" and dxs: "dxs = Dlist xs" by (simp_all add: Dlist_def distinct_remdups_id)
  from `distinct xs` have "P (Dlist xs)"
  proof (induct xs rule: distinct_induct)
    case Nil from empty show ?case by (simp add: empty_def)
  next
    case (insert x xs)
    then have "\<not> member (Dlist xs) x" and "P (Dlist xs)"
      by (simp_all add: member_def mem_iff)
    with insrt have "P (insert x (Dlist xs))" .
    with insert show ?case by (simp add: insert_def distinct_remdups_id)
  qed
  with dxs show "P dxs" by simp
qed

lemma dlist_case [case_names empty insert, cases type: dlist]:
  assumes empty: "dxs = empty \<Longrightarrow> P"
  assumes insert: "\<And>x dys. \<not> member dys x \<Longrightarrow> dxs = insert x dys \<Longrightarrow> P"
  shows P
proof (cases dxs)
  case (Abs_dlist xs)
  then have dxs: "dxs = Dlist xs" and distinct: "distinct xs"
    by (simp_all add: Dlist_def distinct_remdups_id)
  show P proof (cases xs)
    case Nil with dxs have "dxs = empty" by (simp add: empty_def) 
    with empty show P .
  next
    case (Cons x xs)
    with dxs distinct have "\<not> member (Dlist xs) x"
      and "dxs = insert x (Dlist xs)"
      by (simp_all add: member_def mem_iff insert_def distinct_remdups_id)
    with insert show P .
  qed
qed


section {* Implementation of sets by distinct lists -- canonical! *}

definition Set :: "'a dlist \<Rightarrow> 'a fset" where
  "Set dxs = Fset.Set (list_of_dlist dxs)"

definition Coset :: "'a dlist \<Rightarrow> 'a fset" where
  "Coset dxs = Fset.Coset (list_of_dlist dxs)"

code_datatype Set Coset

declare member_code [code del]
declare is_empty_Set [code del]
declare empty_Set [code del]
declare UNIV_Set [code del]
declare insert_Set [code del]
declare remove_Set [code del]
declare compl_Set [code del]
declare compl_Coset [code del]
declare map_Set [code del]
declare filter_Set [code del]
declare forall_Set [code del]
declare exists_Set [code del]
declare card_Set [code del]
declare inter_project [code del]
declare subtract_remove [code del]
declare union_insert [code del]
declare Infimum_inf [code del]
declare Supremum_sup [code del]

lemma Set_Dlist [simp]:
  "Set (Dlist xs) = Fset (set xs)"
  by (simp add: Set_def Fset.Set_def)

lemma Coset_Dlist [simp]:
  "Coset (Dlist xs) = Fset (- set xs)"
  by (simp add: Coset_def Fset.Coset_def)

lemma member_Set [simp]:
  "Fset.member (Set dxs) = List.member (list_of_dlist dxs)"
  by (simp add: Set_def member_set)

lemma member_Coset [simp]:
  "Fset.member (Coset dxs) = Not \<circ> List.member (list_of_dlist dxs)"
  by (simp add: Coset_def member_set not_set_compl)

lemma Set_dlist_of_list [code]:
  "Fset.Set xs = Set (dlist_of_list xs)"
  by simp

lemma Coset_dlist_of_list [code]:
  "Fset.Coset xs = Coset (dlist_of_list xs)"
  by simp

lemma is_empty_Set [code]:
  "Fset.is_empty (Set dxs) \<longleftrightarrow> null dxs"
  by (simp add: null_def null_empty member_set)

lemma bot_code [code]:
  "bot = Set empty"
  by (simp add: empty_def)

lemma top_code [code]:
  "top = Coset empty"
  by (simp add: empty_def)

lemma insert_code [code]:
  "Fset.insert x (Set dxs) = Set (insert x dxs)"
  "Fset.insert x (Coset dxs) = Coset (remove x dxs)"
  by (simp_all add: insert_def remove_def member_set not_set_compl)

lemma remove_code [code]:
  "Fset.remove x (Set dxs) = Set (remove x dxs)"
  "Fset.remove x (Coset dxs) = Coset (insert x dxs)"
  by (auto simp add: insert_def remove_def member_set not_set_compl)

lemma member_code [code]:
  "Fset.member (Set dxs) = member dxs"
  "Fset.member (Coset dxs) = Not \<circ> member dxs"
  by (simp_all add: member_def)

lemma compl_code [code]:
  "- Set dxs = Coset dxs"
  "- Coset dxs = Set dxs"
  by (simp_all add: not_set_compl member_set)

lemma map_code [code]:
  "Fset.map f (Set dxs) = Set (map f dxs)"
  by (simp add: member_set)
  
lemma filter_code [code]:
  "Fset.filter f (Set dxs) = Set (filter f dxs)"
  by (simp add: member_set)

lemma forall_Set [code]:
  "Fset.forall P (Set xs) \<longleftrightarrow> list_all P (list_of_dlist xs)"
  by (simp add: member_set list_all_iff)

lemma exists_Set [code]:
  "Fset.exists P (Set xs) \<longleftrightarrow> list_ex P (list_of_dlist xs)"
  by (simp add: member_set list_ex_iff)

lemma card_code [code]:
  "Fset.card (Set dxs) = length dxs"
  by (simp add: length_def member_set distinct_card)

lemma inter_code [code]:
  "inf A (Set xs) = Set (filter (Fset.member A) xs)"
  "inf A (Coset xs) = foldr Fset.remove xs A"
  by (simp_all only: Set_def Coset_def foldr_def inter_project list_of_dlist_filter)

lemma subtract_code [code]:
  "A - Set xs = foldr Fset.remove xs A"
  "A - Coset xs = Set (filter (Fset.member A) xs)"
  by (simp_all only: Set_def Coset_def foldr_def subtract_remove list_of_dlist_filter)

lemma union_code [code]:
  "sup (Set xs) A = foldr Fset.insert xs A"
  "sup (Coset xs) A = Coset (filter (Not \<circ> Fset.member A) xs)"
  by (simp_all only: Set_def Coset_def foldr_def union_insert list_of_dlist_filter)

context complete_lattice
begin

lemma Infimum_code [code]:
  "Infimum (Set As) = foldr inf As top"
  by (simp only: Set_def Infimum_inf foldr_def inf.commute)

lemma Supremum_code [code]:
  "Supremum (Set As) = foldr sup As bot"
  by (simp only: Set_def Supremum_sup foldr_def sup.commute)

end

hide_const (open) member fold foldr empty insert remove map filter null member length fold

end
