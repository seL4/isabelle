
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

code_datatype Set


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
  by (simp add: Set_def insert_set)

definition remove :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "remove x A = Fset (List_Set.remove x (member A))"

lemma remove_Set [code]:
  "remove x (Set xs) = Set (remove_all x xs)"
  by (simp add: Set_def remove_set)

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

lemma member_exists [code]:
  "member A y \<longleftrightarrow> exists (\<lambda>x. y = x) A"
  by simp

definition subfset_eq :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  [simp]: "subfset_eq A B \<longleftrightarrow> member A \<subseteq> member B"

lemma subfset_eq_forall [code]:
  "subfset_eq A B \<longleftrightarrow> forall (\<lambda>x. member B x) A"
  by (simp add: subset_eq)

definition subfset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  [simp]: "subfset A B \<longleftrightarrow> member A \<subset> member B"

lemma subfset_subfset_eq [code]:
  "subfset A B \<longleftrightarrow> subfset_eq A B \<and> \<not> subfset_eq B A"
  by (simp add: subset)

lemma eq_fset_subfset_eq [code]:
  "eq_class.eq A B \<longleftrightarrow> subfset_eq A B \<and> subfset_eq B A"
  by (cases A, cases B) (simp add: eq set_eq)

definition inter :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "inter A B = Fset (project (member A) (member B))"

lemma inter_project [code]:
  "inter A B = filter (member A) B"
  by (simp add: inter)


subsection {* Functorial operations *}

definition union :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "union A B = Fset (member A \<union> member B)"

lemma union_insert [code]:
  "union (Set xs) A = foldl (\<lambda>A x. insert x A) A xs"
proof -
  have "foldl (\<lambda>A x. Set.insert x A) (member A) xs =
    member (foldl (\<lambda>A x. Fset (Set.insert x (member A))) A xs)"
    by (rule foldl_apply_inv) simp
  then show ?thesis by (simp add: union_set)
qed

definition subtract :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "subtract A B = Fset (member B - member A)"

lemma subtract_remove [code]:
  "subtract (Set xs) A = foldl (\<lambda>A x. remove x A) A xs"
proof -
  have "foldl (\<lambda>A x. List_Set.remove x A) (member A) xs =
    member (foldl (\<lambda>A x. Fset (List_Set.remove x (member A))) A xs)"
    by (rule foldl_apply_inv) simp
  then show ?thesis by (simp add: minus_set)
qed

definition Inter :: "'a fset fset \<Rightarrow> 'a fset" where
  [simp]: "Inter A = Fset (Complete_Lattice.Inter (member ` member A))"

lemma Inter_inter [code]:
  "Inter (Set (A # As)) = foldl inter A As"
proof -
  note Inter_image_eq [simp del] set_map [simp del] set.simps [simp del]
  have "foldl (op \<inter>) (member A) (List.map member As) = 
    member (foldl (\<lambda>B A. Fset (member B \<inter> A)) A (List.map member As))"
    by (rule foldl_apply_inv) simp
  then show ?thesis
    by (simp add: Inter_set image_set inter_def_raw inter foldl_map)
qed

definition Union :: "'a fset fset \<Rightarrow> 'a fset" where
  [simp]: "Union A = Fset (Complete_Lattice.Union (member ` member A))"

lemma Union_union [code]:
  "Union (Set As) = foldl union empty As"
proof -
  note Union_image_eq [simp del] set_map [simp del]
  have "foldl (op \<union>) (member empty) (List.map member As) = 
    member (foldl (\<lambda>B A. Fset (member B \<union> A)) empty (List.map member As))"
    by (rule foldl_apply_inv) simp
  then show ?thesis
    by (simp add: Union_set image_set union_def_raw foldl_map)
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

lemma inter_simp [simp]:
  "inter A B = Fset (member A \<inter> member B)"
  by (simp add: inter)
declare inter_def [simp del]

declare mem_def [simp del]


hide (open) const is_empty empty insert remove map filter forall exists card
  subfset_eq subfset inter union subtract Inter Union

end
