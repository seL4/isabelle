
(* Author: Florian Haftmann, TU Muenchen *)

header {* Executable finite sets *}

theory Fset
imports List_Set
begin

declare mem_def [simp]

subsection {* Lifting *}

datatype 'a fset = Fset "'a set"

primrec member :: "'a fset \<Rightarrow> 'a set" where
  "member (Fset A) = A"

lemma Fset_member [simp]:
  "Fset (member A) = A"
  by (cases A) simp

definition Set :: "'a list \<Rightarrow> 'a fset" where
  "Set xs = Fset (set xs)"

lemma member_Set [simp]:
  "member (Set xs) = set xs"
  by (simp add: Set_def)

definition Coset :: "'a list \<Rightarrow> 'a fset" where
  "Coset xs = Fset (- set xs)"

lemma member_Coset [simp]:
  "member (Coset xs) = - set xs"
  by (simp add: Coset_def)

code_datatype Set Coset

lemma member_code [code]:
  "member (Set xs) y \<longleftrightarrow> List.member y xs"
  "member (Coset xs) y \<longleftrightarrow> \<not> List.member y xs"
  by (simp_all add: mem_iff fun_Compl_def bool_Compl_def)

lemma member_image_UNIV [simp]:
  "member ` UNIV = UNIV"
proof -
  have "\<And>A \<Colon> 'a set. \<exists>B \<Colon> 'a fset. A = member B"
  proof
    fix A :: "'a set"
    show "A = member (Fset A)" by simp
  qed
  then show ?thesis by (simp add: image_def)
qed


subsection {* Basic operations *}

definition is_empty :: "'a fset \<Rightarrow> bool" where
  [simp]: "is_empty A \<longleftrightarrow> List_Set.is_empty (member A)"

lemma is_empty_Set [code]:
  "is_empty (Set xs) \<longleftrightarrow> null xs"
  by (simp add: is_empty_set)

definition empty :: "'a fset" where
  [simp]: "empty = Fset {}"

lemma empty_Set [code]:
  "empty = Set []"
  by (simp add: Set_def)

definition insert :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "insert x A = Fset (Set.insert x (member A))"

lemma insert_Set [code]:
  "insert x (Set xs) = Set (List_Set.insert x xs)"
  "insert x (Coset xs) = Coset (remove_all x xs)"
  by (simp_all add: Set_def Coset_def insert_set insert_set_compl)

definition remove :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "remove x A = Fset (List_Set.remove x (member A))"

lemma remove_Set [code]:
  "remove x (Set xs) = Set (remove_all x xs)"
  "remove x (Coset xs) = Coset (List_Set.insert x xs)"
  by (simp_all add: Set_def Coset_def remove_set remove_set_compl)

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset" where
  [simp]: "map f A = Fset (image f (member A))"

lemma map_Set [code]:
  "map f (Set xs) = Set (remdups (List.map f xs))"
  by (simp add: Set_def)

definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "filter P A = Fset (List_Set.project P (member A))"

lemma filter_Set [code]:
  "filter P (Set xs) = Set (List.filter P xs)"
  by (simp add: Set_def project_set)

definition forall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> bool" where
  [simp]: "forall P A \<longleftrightarrow> Ball (member A) P"

lemma forall_Set [code]:
  "forall P (Set xs) \<longleftrightarrow> list_all P xs"
  by (simp add: Set_def ball_set)

definition exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> bool" where
  [simp]: "exists P A \<longleftrightarrow> Bex (member A) P"

lemma exists_Set [code]:
  "exists P (Set xs) \<longleftrightarrow> list_ex P xs"
  by (simp add: Set_def bex_set)

definition card :: "'a fset \<Rightarrow> nat" where
  [simp]: "card A = Finite_Set.card (member A)"

lemma card_Set [code]:
  "card (Set xs) = length (remdups xs)"
proof -
  have "Finite_Set.card (set (remdups xs)) = length (remdups xs)"
    by (rule distinct_card) simp
  then show ?thesis by (simp add: Set_def card_def)
qed


subsection {* Derived operations *}

definition subfset_eq :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  [simp]: "subfset_eq A B \<longleftrightarrow> member A \<subseteq> member B"

lemma subfset_eq_forall [code]:
  "subfset_eq A B \<longleftrightarrow> forall (member B) A"
  by (simp add: subset_eq)

definition subfset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  [simp]: "subfset A B \<longleftrightarrow> member A \<subset> member B"

lemma subfset_subfset_eq [code]:
  "subfset A B \<longleftrightarrow> subfset_eq A B \<and> \<not> subfset_eq B A"
  by (simp add: subset)

lemma eq_fset_subfset_eq [code]:
  "eq_class.eq A B \<longleftrightarrow> subfset_eq A B \<and> subfset_eq B A"
  by (cases A, cases B) (simp add: eq set_eq)


subsection {* Functorial operations *}

definition inter :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "inter A B = Fset (member A \<inter> member B)"

lemma inter_project [code]:
  "inter A (Set xs) = Set (List.filter (member A) xs)"
  "inter A (Coset xs) = foldl (\<lambda>A x. remove x A) A xs"
proof -
  show "inter A (Set xs) = Set (List.filter (member A) xs)"
    by (simp add: inter project_def Set_def)
  have "foldl (\<lambda>A x. List_Set.remove x A) (member A) xs =
    member (foldl (\<lambda>A x. Fset (List_Set.remove x (member A))) A xs)"
    by (rule foldl_apply_inv) simp
  then show "inter A (Coset xs) = foldl (\<lambda>A x. remove x A) A xs"
    by (simp add: Diff_eq [symmetric] minus_set)
qed

definition subtract :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "subtract A B = Fset (member B - member A)"

lemma subtract_remove [code]:
  "subtract (Set xs) A = foldl (\<lambda>A x. remove x A) A xs"
  "subtract (Coset xs) A = Set (List.filter (member A) xs)"
proof -
  have "foldl (\<lambda>A x. List_Set.remove x A) (member A) xs =
    member (foldl (\<lambda>A x. Fset (List_Set.remove x (member A))) A xs)"
    by (rule foldl_apply_inv) simp
  then show "subtract (Set xs) A = foldl (\<lambda>A x. remove x A) A xs"
    by (simp add: minus_set)
  show "subtract (Coset xs) A = Set (List.filter (member A) xs)"
    by (auto simp add: Coset_def Set_def)
qed

definition union :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "union A B = Fset (member A \<union> member B)"

lemma union_insert [code]:
  "union (Set xs) A = foldl (\<lambda>A x. insert x A) A xs"
  "union (Coset xs) A = Coset (List.filter (Not \<circ> member A) xs)"
proof -
  have "foldl (\<lambda>A x. Set.insert x A) (member A) xs =
    member (foldl (\<lambda>A x. Fset (Set.insert x (member A))) A xs)"
    by (rule foldl_apply_inv) simp
  then show "union (Set xs) A = foldl (\<lambda>A x. insert x A) A xs"
    by (simp add: union_set)
  show "union (Coset xs) A = Coset (List.filter (Not \<circ> member A) xs)"
    by (auto simp add: Coset_def)
qed

definition Inter :: "'a fset fset \<Rightarrow> 'a fset" where
  [simp]: "Inter A = Fset (Complete_Lattice.Inter (member ` member A))"

lemma Inter_inter [code]:
  "Inter (Set As) = foldl inter (Coset []) As"
  "Inter (Coset []) = empty"
proof -
  have [simp]: "Coset [] = Fset UNIV"
    by (simp add: Coset_def)
  note Inter_image_eq [simp del] set_map [simp del] set.simps [simp del]
  have "foldl (op \<inter>) (member (Coset [])) (List.map member As) = 
    member (foldl (\<lambda>B A. Fset (member B \<inter> A)) (Coset []) (List.map member As))"
    by (rule foldl_apply_inv) simp
  then show "Inter (Set As) = foldl inter (Coset []) As"
    by (simp add: Inf_set_fold image_set inter inter_def_raw foldl_map)
  show "Inter (Coset []) = empty"
    by simp
qed

definition Union :: "'a fset fset \<Rightarrow> 'a fset" where
  [simp]: "Union A = Fset (Complete_Lattice.Union (member ` member A))"

lemma Union_union [code]:
  "Union (Set As) = foldl union empty As"
  "Union (Coset []) = Coset []"
proof -
  have [simp]: "Coset [] = Fset UNIV"
    by (simp add: Coset_def)
  note Union_image_eq [simp del] set_map [simp del]
  have "foldl (op \<union>) (member empty) (List.map member As) = 
    member (foldl (\<lambda>B A. Fset (member B \<union> A)) empty (List.map member As))"
    by (rule foldl_apply_inv) simp
  then show "Union (Set As) = foldl union empty As"
    by (simp add: Sup_set_fold image_set union_def_raw foldl_map)
  show "Union (Coset []) = Coset []"
    by simp
qed


subsection {* Misc operations *}

lemma size_fset [code]:
  "fset_size f A = 0"
  "size A = 0"
  by (cases A, simp) (cases A, simp)

lemma fset_case_code [code]:
  "fset_case f A = f (member A)"
  by (cases A) simp

lemma fset_rec_code [code]:
  "fset_rec f A = f (member A)"
  by (cases A) simp


subsection {* Simplified simprules *}

lemma is_empty_simp [simp]:
  "is_empty A \<longleftrightarrow> member A = {}"
  by (simp add: List_Set.is_empty_def)
declare is_empty_def [simp del]

lemma remove_simp [simp]:
  "remove x A = Fset (member A - {x})"
  by (simp add: List_Set.remove_def)
declare remove_def [simp del]

lemma filter_simp [simp]:
  "filter P A = Fset {x \<in> member A. P x}"
  by (simp add: List_Set.project_def)
declare filter_def [simp del]

declare mem_def [simp del]


hide (open) const is_empty empty insert remove map filter forall exists card
  subfset_eq subfset inter union subtract Inter Union

end
