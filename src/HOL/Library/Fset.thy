
(* Author: Florian Haftmann, TU Muenchen *)

header {* Executable finite sets *}

theory Fset
imports List_Set More_List
begin

declare mem_def [simp]

subsection {* Lifting *}

datatype 'a fset = Fset "'a set"

primrec member :: "'a fset \<Rightarrow> 'a set" where
  "member (Fset A) = A"

lemma member_inject [simp]:
  "member A = member B \<Longrightarrow> A = B"
  by (cases A, cases B) simp

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
  "member (Set xs) = List.member xs"
  "member (Coset xs) = Not \<circ> List.member xs"
  by (simp_all add: expand_fun_eq mem_iff fun_Compl_def bool_Compl_def)

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


subsection {* Lattice instantiation *}

instantiation fset :: (type) boolean_algebra
begin

definition less_eq_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  [simp]: "A \<le> B \<longleftrightarrow> member A \<subseteq> member B"

definition less_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  [simp]: "A < B \<longleftrightarrow> member A \<subset> member B"

definition inf_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "inf A B = Fset (member A \<inter> member B)"

definition sup_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "sup A B = Fset (member A \<union> member B)"

definition bot_fset :: "'a fset" where
  [simp]: "bot = Fset {}"

definition top_fset :: "'a fset" where
  [simp]: "top = Fset UNIV"

definition uminus_fset :: "'a fset \<Rightarrow> 'a fset" where
  [simp]: "- A = Fset (- (member A))"

definition minus_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "A - B = Fset (member A - member B)"

instance proof
qed auto

end

instantiation fset :: (type) complete_lattice
begin

definition Inf_fset :: "'a fset set \<Rightarrow> 'a fset" where
  [simp, code del]: "Inf_fset As = Fset (Inf (image member As))"

definition Sup_fset :: "'a fset set \<Rightarrow> 'a fset" where
  [simp, code del]: "Sup_fset As = Fset (Sup (image member As))"

instance proof
qed (auto simp add: le_fun_def le_bool_def)

end


subsection {* Basic operations *}

definition is_empty :: "'a fset \<Rightarrow> bool" where
  [simp]: "is_empty A \<longleftrightarrow> List_Set.is_empty (member A)"

lemma is_empty_Set [code]:
  "is_empty (Set xs) \<longleftrightarrow> null xs"
  by (simp add: is_empty_set)

lemma empty_Set [code]:
  "bot = Set []"
  by simp

lemma UNIV_Set [code]:
  "top = Coset []"
  by simp

definition insert :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "insert x A = Fset (Set.insert x (member A))"

lemma insert_Set [code]:
  "insert x (Set xs) = Set (List.insert x xs)"
  "insert x (Coset xs) = Coset (removeAll x xs)"
  by (simp_all add: Set_def Coset_def)

definition remove :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  [simp]: "remove x A = Fset (List_Set.remove x (member A))"

lemma remove_Set [code]:
  "remove x (Set xs) = Set (removeAll x xs)"
  "remove x (Coset xs) = Coset (List.insert x xs)"
  by (simp_all add: Set_def Coset_def remove_set_compl)
    (simp add: List_Set.remove_def)

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
  then show ?thesis by (simp add: Set_def)
qed

lemma compl_Set [simp, code]:
  "- Set xs = Coset xs"
  by (simp add: Set_def Coset_def)

lemma compl_Coset [simp, code]:
  "- Coset xs = Set xs"
  by (simp add: Set_def Coset_def)


subsection {* Derived operations *}

lemma subfset_eq_forall [code]:
  "A \<le> B \<longleftrightarrow> forall (member B) A"
  by (simp add: subset_eq)

lemma subfset_subfset_eq [code]:
  "A < B \<longleftrightarrow> A \<le> B \<and> \<not> B \<le> (A :: 'a fset)"
  by (fact less_le_not_le)

lemma eq_fset_subfset_eq [code]:
  "eq_class.eq A B \<longleftrightarrow> A \<le> B \<and> B \<le> (A :: 'a fset)"
  by (cases A, cases B) (simp add: eq set_eq)


subsection {* Functorial operations *}

lemma inter_project [code]:
  "inf A (Set xs) = Set (List.filter (member A) xs)"
  "inf A (Coset xs) = foldr remove xs A"
proof -
  show "inf A (Set xs) = Set (List.filter (member A) xs)"
    by (simp add: inter project_def Set_def)
  have *: "\<And>x::'a. remove = (\<lambda>x. Fset \<circ> List_Set.remove x \<circ> member)"
    by (simp add: expand_fun_eq)
  have "member \<circ> fold (\<lambda>x. Fset \<circ> List_Set.remove x \<circ> member) xs =
    fold List_Set.remove xs \<circ> member"
    by (rule fold_apply) (simp add: expand_fun_eq)
  then have "fold List_Set.remove xs (member A) = 
    member (fold (\<lambda>x. Fset \<circ> List_Set.remove x \<circ> member) xs A)"
    by (simp add: expand_fun_eq)
  then have "inf A (Coset xs) = fold remove xs A"
    by (simp add: Diff_eq [symmetric] minus_set *)
  moreover have "\<And>x y :: 'a. Fset.remove y \<circ> Fset.remove x = Fset.remove x \<circ> Fset.remove y"
    by (auto simp add: List_Set.remove_def * intro: ext)
  ultimately show "inf A (Coset xs) = foldr remove xs A"
    by (simp add: foldr_fold)
qed

lemma subtract_remove [code]:
  "A - Set xs = foldr remove xs A"
  "A - Coset xs = Set (List.filter (member A) xs)"
  by (simp_all only: diff_eq compl_Set compl_Coset inter_project)

lemma union_insert [code]:
  "sup (Set xs) A = foldr insert xs A"
  "sup (Coset xs) A = Coset (List.filter (Not \<circ> member A) xs)"
proof -
  have *: "\<And>x::'a. insert = (\<lambda>x. Fset \<circ> Set.insert x \<circ> member)"
    by (simp add: expand_fun_eq)
  have "member \<circ> fold (\<lambda>x. Fset \<circ> Set.insert x \<circ> member) xs =
    fold Set.insert xs \<circ> member"
    by (rule fold_apply) (simp add: expand_fun_eq)
  then have "fold Set.insert xs (member A) =
    member (fold (\<lambda>x. Fset \<circ> Set.insert x \<circ> member) xs A)"
    by (simp add: expand_fun_eq)
  then have "sup (Set xs) A = fold insert xs A"
    by (simp add: union_set *)
  moreover have "\<And>x y :: 'a. Fset.insert y \<circ> Fset.insert x = Fset.insert x \<circ> Fset.insert y"
    by (auto simp add: * intro: ext)
  ultimately show "sup (Set xs) A = foldr insert xs A"
    by (simp add: foldr_fold)
  show "sup (Coset xs) A = Coset (List.filter (Not \<circ> member A) xs)"
    by (auto simp add: Coset_def)
qed

context complete_lattice
begin

definition Infimum :: "'a fset \<Rightarrow> 'a" where
  [simp]: "Infimum A = Inf (member A)"

lemma Infimum_inf [code]:
  "Infimum (Set As) = foldr inf As top"
  "Infimum (Coset []) = bot"
  by (simp_all add: Inf_set_foldr Inf_UNIV)

definition Supremum :: "'a fset \<Rightarrow> 'a" where
  [simp]: "Supremum A = Sup (member A)"

lemma Supremum_sup [code]:
  "Supremum (Set As) = foldr sup As bot"
  "Supremum (Coset []) = top"
  by (simp_all add: Sup_set_foldr Sup_UNIV)

end


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


hide_const (open) is_empty insert remove map filter forall exists card
  Inter Union

end
