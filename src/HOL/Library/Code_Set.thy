
(* Author: Florian Haftmann, TU Muenchen *)

header {* Executable finite sets *}

theory Code_Set
imports List_Set
begin

lemma foldl_apply_inv:
  assumes "\<And>x. g (h x) = x"
  shows "foldl f (g s) xs = g (foldl (\<lambda>s x. h (f (g s) x)) s xs)"
  by (rule sym, induct xs arbitrary: s) (simp_all add: assms)

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
  "is_empty A \<longleftrightarrow> List_Set.is_empty (member A)"

lemma is_empty_Set [code]:
  "is_empty (Set xs) \<longleftrightarrow> null xs"
  by (simp add: is_empty_def is_empty_set)

definition empty :: "'a fset" where
  "empty = Fset {}"

lemma empty_Set [code]:
  "empty = Set []"
  by (simp add: empty_def Set_def)

definition insert :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "insert x A = Fset (Set.insert x (member A))"

lemma insert_Set [code]:
  "insert x (Set xs) = Set (List_Set.insert x xs)"
  by (simp add: insert_def Set_def insert_set)

definition remove :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "remove x A = Fset (List_Set.remove x (member A))"

lemma remove_Set [code]:
  "remove x (Set xs) = Set (remove_all x xs)"
  by (simp add: remove_def Set_def remove_set)

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset" where
  "map f A = Fset (image f (member A))"

lemma map_Set [code]:
  "map f (Set xs) = Set (remdups (List.map f xs))"
  by (simp add: map_def Set_def)

definition project :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "project P A = Fset (List_Set.project P (member A))"

lemma project_Set [code]:
  "project P (Set xs) = Set (filter P xs)"
  by (simp add: project_def Set_def project_set)

definition forall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> bool" where
  "forall P A \<longleftrightarrow> Ball (member A) P"

lemma forall_Set [code]:
  "forall P (Set xs) \<longleftrightarrow> list_all P xs"
  by (simp add: forall_def Set_def ball_set)

definition exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> bool" where
  "exists P A \<longleftrightarrow> Bex (member A) P"

lemma exists_Set [code]:
  "exists P (Set xs) \<longleftrightarrow> list_ex P xs"
  by (simp add: exists_def Set_def bex_set)


subsection {* Functorial operations *}

definition union :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "union A B = Fset (member A \<union> member B)"

lemma union_insert [code]:
  "union (Set xs) A = foldl (\<lambda>A x. insert x A) A xs"
proof -
  have "foldl (\<lambda>A x. Set.insert x A) (member A) xs =
    member (foldl (\<lambda>A x. Fset (Set.insert x (member A))) A xs)"
    by (rule foldl_apply_inv) simp
  then show ?thesis by (simp add: union_def union_set insert_def)
qed

definition subtract :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "subtract A B = Fset (member B - member A)"

lemma subtract_remove [code]:
  "subtract (Set xs) A = foldl (\<lambda>A x. remove x A) A xs"
proof -
  have "foldl (\<lambda>A x. List_Set.remove x A) (member A) xs =
    member (foldl (\<lambda>A x. Fset (List_Set.remove x (member A))) A xs)"
    by (rule foldl_apply_inv) simp
  then show ?thesis by (simp add: subtract_def minus_set remove_def)
qed


subsection {* Derived operations *}

lemma member_exists [code]:
  "member A y \<longleftrightarrow> exists (\<lambda>x. y = x) A"
  by (simp add: exists_def mem_def)

definition subfset_eq :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  "subfset_eq A B \<longleftrightarrow> member A \<subseteq> member B"

lemma subfset_eq_forall [code]:
  "subfset_eq A B \<longleftrightarrow> forall (\<lambda>x. member B x) A"
  by (simp add: subfset_eq_def subset_eq forall_def mem_def)

definition subfset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  "subfset A B \<longleftrightarrow> member A \<subset> member B"

lemma subfset_subfset_eq [code]:
  "subfset A B \<longleftrightarrow> subfset_eq A B \<and> \<not> subfset_eq B A"
  by (simp add: subfset_def subfset_eq_def subset)

lemma eq_fset_subfset_eq [code]:
  "eq_class.eq A B \<longleftrightarrow> subfset_eq A B \<and> subfset_eq B A"
  by (cases A, cases B) (simp add: eq subfset_eq_def set_eq)

definition inter :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "inter A B = Fset (List_Set.project (member A) (member B))"

lemma inter_project [code]:
  "inter A B = project (member A) B"
  by (simp add: inter_def project_def inter)


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

end
