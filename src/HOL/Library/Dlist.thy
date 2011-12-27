(* Author: Florian Haftmann, TU Muenchen *)

header {* Lists with elements distinct as canonical example for datatype invariants *}

theory Dlist
imports Main
begin

subsection {* The type of distinct lists *}

typedef (open) 'a dlist = "{xs::'a list. distinct xs}"
  morphisms list_of_dlist Abs_dlist
proof
  show "[] \<in> {xs. distinct xs}" by simp
qed

lemma dlist_eq_iff:
  "dxs = dys \<longleftrightarrow> list_of_dlist dxs = list_of_dlist dys"
  by (simp add: list_of_dlist_inject)

lemma dlist_eqI:
  "list_of_dlist dxs = list_of_dlist dys \<Longrightarrow> dxs = dys"
  by (simp add: dlist_eq_iff)

text {* Formal, totalized constructor for @{typ "'a dlist"}: *}

definition Dlist :: "'a list \<Rightarrow> 'a dlist" where
  "Dlist xs = Abs_dlist (remdups xs)"

lemma distinct_list_of_dlist [simp, intro]:
  "distinct (list_of_dlist dxs)"
  using list_of_dlist [of dxs] by simp

lemma list_of_dlist_Dlist [simp]:
  "list_of_dlist (Dlist xs) = remdups xs"
  by (simp add: Dlist_def Abs_dlist_inverse)

lemma remdups_list_of_dlist [simp]:
  "remdups (list_of_dlist dxs) = list_of_dlist dxs"
  by simp

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


subsection {* Executable version obeying invariant *}

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


text {* Equality *}

instantiation dlist :: (equal) equal
begin

definition "HOL.equal dxs dys \<longleftrightarrow> HOL.equal (list_of_dlist dxs) (list_of_dlist dys)"

instance proof
qed (simp add: equal_dlist_def equal list_of_dlist_inject)

end

declare equal_dlist_def [code]

lemma [code nbe]:
  "HOL.equal (dxs :: 'a::equal dlist) dxs \<longleftrightarrow> True"
  by (fact equal_refl)


subsection {* Induction principle and case distinction *}

lemma dlist_induct [case_names empty insert, induct type: dlist]:
  assumes empty: "P empty"
  assumes insrt: "\<And>x dxs. \<not> member dxs x \<Longrightarrow> P dxs \<Longrightarrow> P (insert x dxs)"
  shows "P dxs"
proof (cases dxs)
  case (Abs_dlist xs)
  then have "distinct xs" and dxs: "dxs = Dlist xs" by (simp_all add: Dlist_def distinct_remdups_id)
  from `distinct xs` have "P (Dlist xs)"
  proof (induct xs)
    case Nil from empty show ?case by (simp add: empty_def)
  next
    case (Cons x xs)
    then have "\<not> member (Dlist xs) x" and "P (Dlist xs)"
      by (simp_all add: member_def List.member_def)
    with insrt have "P (insert x (Dlist xs))" .
    with Cons show ?case by (simp add: insert_def distinct_remdups_id)
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
      by (simp_all add: member_def List.member_def insert_def distinct_remdups_id)
    with insert show P .
  qed
qed


subsection {* Functorial structure *}

enriched_type map: map
  by (simp_all add: List.map.id remdups_map_remdups fun_eq_iff dlist_eq_iff)

subsection {* Quickcheck generators *}

quickcheck_generator dlist constructors: empty, insert

hide_const (open) member fold foldr empty insert remove map filter null member length fold

end
