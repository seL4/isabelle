
(* Author: Florian Haftmann, TU Muenchen *)

header {* A dedicated set type which is executable on its finite part *}

theory Cset
imports More_Set More_List
begin

subsection {* Lifting *}

typedef (open) 'a set = "UNIV :: 'a set set"
  morphisms member Set by rule+
hide_type (open) set

lemma member_Set [simp]:
  "member (Set A) = A"
  by (rule Set_inverse) rule

lemma Set_member [simp]:
  "Set (member A) = A"
  by (fact member_inverse)

lemma Set_inject [simp]:
  "Set A = Set B \<longleftrightarrow> A = B"
  by (simp add: Set_inject)

lemma set_eq_iff:
  "A = B \<longleftrightarrow> member A = member B"
  by (simp add: member_inject)
hide_fact (open) set_eq_iff

lemma set_eqI:
  "member A = member B \<Longrightarrow> A = B"
  by (simp add: Cset.set_eq_iff)
hide_fact (open) set_eqI

declare mem_def [simp]

definition set :: "'a list \<Rightarrow> 'a Cset.set" where
  "set xs = Set (List.set xs)"
hide_const (open) set

lemma member_set [simp]:
  "member (Cset.set xs) = set xs"
  by (simp add: set_def)
hide_fact (open) member_set

definition coset :: "'a list \<Rightarrow> 'a Cset.set" where
  "coset xs = Set (- set xs)"
hide_const (open) coset

lemma member_coset [simp]:
  "member (Cset.coset xs) = - set xs"
  by (simp add: coset_def)
hide_fact (open) member_coset

code_datatype Cset.set Cset.coset

lemma member_code [code]:
  "member (Cset.set xs) = List.member xs"
  "member (Cset.coset xs) = Not \<circ> List.member xs"
  by (simp_all add: fun_eq_iff member_def fun_Compl_def bool_Compl_def)

lemma member_image_UNIV [simp]:
  "member ` UNIV = UNIV"
proof -
  have "\<And>A \<Colon> 'a set. \<exists>B \<Colon> 'a Cset.set. A = member B"
  proof
    fix A :: "'a set"
    show "A = member (Set A)" by simp
  qed
  then show ?thesis by (simp add: image_def)
qed

definition (in term_syntax)
  setify :: "'a\<Colon>typerep list \<times> (unit \<Rightarrow> Code_Evaluation.term)
    \<Rightarrow> 'a Cset.set \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  [code_unfold]: "setify xs = Code_Evaluation.valtermify Cset.set {\<cdot>} xs"

notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation Cset.set :: (random) random
begin

definition
  "Quickcheck.random i = Quickcheck.random i \<circ>\<rightarrow> (\<lambda>xs. Pair (setify xs))"

instance ..

end

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)


subsection {* Lattice instantiation *}

instantiation Cset.set :: (type) boolean_algebra
begin

definition less_eq_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "A \<le> B \<longleftrightarrow> member A \<subseteq> member B"

definition less_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "A < B \<longleftrightarrow> member A \<subset> member B"

definition inf_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "inf A B = Set (member A \<inter> member B)"

definition sup_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "sup A B = Set (member A \<union> member B)"

definition bot_set :: "'a Cset.set" where
  [simp]: "bot = Set {}"

definition top_set :: "'a Cset.set" where
  [simp]: "top = Set UNIV"

definition uminus_set :: "'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "- A = Set (- (member A))"

definition minus_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "A - B = Set (member A - member B)"

instance proof
qed (auto intro: Cset.set_eqI)

end

instantiation Cset.set :: (type) complete_lattice
begin

definition Inf_set :: "'a Cset.set set \<Rightarrow> 'a Cset.set" where
  [simp]: "Inf_set As = Set (Inf (image member As))"

definition Sup_set :: "'a Cset.set set \<Rightarrow> 'a Cset.set" where
  [simp]: "Sup_set As = Set (Sup (image member As))"

instance proof
qed (auto simp add: le_fun_def le_bool_def)

end


subsection {* Basic operations *}

definition is_empty :: "'a Cset.set \<Rightarrow> bool" where
  [simp]: "is_empty A \<longleftrightarrow> More_Set.is_empty (member A)"

lemma is_empty_set [code]:
  "is_empty (Cset.set xs) \<longleftrightarrow> List.null xs"
  by (simp add: is_empty_set)
hide_fact (open) is_empty_set

lemma empty_set [code]:
  "bot = Cset.set []"
  by (simp add: set_def)
hide_fact (open) empty_set

lemma UNIV_set [code]:
  "top = Cset.coset []"
  by (simp add: coset_def)
hide_fact (open) UNIV_set

definition insert :: "'a \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "insert x A = Set (Set.insert x (member A))"

lemma insert_set [code]:
  "insert x (Cset.set xs) = Cset.set (List.insert x xs)"
  "insert x (Cset.coset xs) = Cset.coset (removeAll x xs)"
  by (simp_all add: set_def coset_def)

definition remove :: "'a \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "remove x A = Set (More_Set.remove x (member A))"

lemma remove_set [code]:
  "remove x (Cset.set xs) = Cset.set (removeAll x xs)"
  "remove x (Cset.coset xs) = Cset.coset (List.insert x xs)"
  by (simp_all add: set_def coset_def remove_set_compl)
    (simp add: More_Set.remove_def)

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Cset.set \<Rightarrow> 'b Cset.set" where
  [simp]: "map f A = Set (image f (member A))"

lemma map_set [code]:
  "map f (Cset.set xs) = Cset.set (remdups (List.map f xs))"
  by (simp add: set_def)

type_mapper map
  by (simp_all add: image_image)

definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "filter P A = Set (More_Set.project P (member A))"

lemma filter_set [code]:
  "filter P (Cset.set xs) = Cset.set (List.filter P xs)"
  by (simp add: set_def project_set)

definition forall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "forall P A \<longleftrightarrow> Ball (member A) P"

lemma forall_set [code]:
  "forall P (Cset.set xs) \<longleftrightarrow> list_all P xs"
  by (simp add: set_def list_all_iff)

definition exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "exists P A \<longleftrightarrow> Bex (member A) P"

lemma exists_set [code]:
  "exists P (Cset.set xs) \<longleftrightarrow> list_ex P xs"
  by (simp add: set_def list_ex_iff)

definition card :: "'a Cset.set \<Rightarrow> nat" where
  [simp]: "card A = Finite_Set.card (member A)"

lemma card_set [code]:
  "card (Cset.set xs) = length (remdups xs)"
proof -
  have "Finite_Set.card (set (remdups xs)) = length (remdups xs)"
    by (rule distinct_card) simp
  then show ?thesis by (simp add: set_def)
qed

lemma compl_set [simp, code]:
  "- Cset.set xs = Cset.coset xs"
  by (simp add: set_def coset_def)

lemma compl_coset [simp, code]:
  "- Cset.coset xs = Cset.set xs"
  by (simp add: set_def coset_def)


subsection {* Derived operations *}

lemma subset_eq_forall [code]:
  "A \<le> B \<longleftrightarrow> forall (member B) A"
  by (simp add: subset_eq)

lemma subset_subset_eq [code]:
  "A < B \<longleftrightarrow> A \<le> B \<and> \<not> B \<le> (A :: 'a Cset.set)"
  by (fact less_le_not_le)

instantiation Cset.set :: (type) equal
begin

definition [code]:
  "HOL.equal A B \<longleftrightarrow> A \<le> B \<and> B \<le> (A :: 'a Cset.set)"

instance proof
qed (simp add: equal_set_def set_eq [symmetric] Cset.set_eq_iff)

end

lemma [code nbe]:
  "HOL.equal (A :: 'a Cset.set) A \<longleftrightarrow> True"
  by (fact equal_refl)


subsection {* Functorial operations *}

lemma inter_project [code]:
  "inf A (Cset.set xs) = Cset.set (List.filter (member A) xs)"
  "inf A (Cset.coset xs) = foldr remove xs A"
proof -
  show "inf A (Cset.set xs) = Cset.set (List.filter (member A) xs)"
    by (simp add: inter project_def set_def)
  have *: "\<And>x::'a. remove = (\<lambda>x. Set \<circ> More_Set.remove x \<circ> member)"
    by (simp add: fun_eq_iff)
  have "member \<circ> fold (\<lambda>x. Set \<circ> More_Set.remove x \<circ> member) xs =
    fold More_Set.remove xs \<circ> member"
    by (rule fold_commute) (simp add: fun_eq_iff)
  then have "fold More_Set.remove xs (member A) = 
    member (fold (\<lambda>x. Set \<circ> More_Set.remove x \<circ> member) xs A)"
    by (simp add: fun_eq_iff)
  then have "inf A (Cset.coset xs) = fold remove xs A"
    by (simp add: Diff_eq [symmetric] minus_set *)
  moreover have "\<And>x y :: 'a. Cset.remove y \<circ> Cset.remove x = Cset.remove x \<circ> Cset.remove y"
    by (auto simp add: More_Set.remove_def * intro: ext)
  ultimately show "inf A (Cset.coset xs) = foldr remove xs A"
    by (simp add: foldr_fold)
qed

lemma subtract_remove [code]:
  "A - Cset.set xs = foldr remove xs A"
  "A - Cset.coset xs = Cset.set (List.filter (member A) xs)"
  by (simp_all only: diff_eq compl_set compl_coset inter_project)

lemma union_insert [code]:
  "sup (Cset.set xs) A = foldr insert xs A"
  "sup (Cset.coset xs) A = Cset.coset (List.filter (Not \<circ> member A) xs)"
proof -
  have *: "\<And>x::'a. insert = (\<lambda>x. Set \<circ> Set.insert x \<circ> member)"
    by (simp add: fun_eq_iff)
  have "member \<circ> fold (\<lambda>x. Set \<circ> Set.insert x \<circ> member) xs =
    fold Set.insert xs \<circ> member"
    by (rule fold_commute) (simp add: fun_eq_iff)
  then have "fold Set.insert xs (member A) =
    member (fold (\<lambda>x. Set \<circ> Set.insert x \<circ> member) xs A)"
    by (simp add: fun_eq_iff)
  then have "sup (Cset.set xs) A = fold insert xs A"
    by (simp add: union_set *)
  moreover have "\<And>x y :: 'a. Cset.insert y \<circ> Cset.insert x = Cset.insert x \<circ> Cset.insert y"
    by (auto simp add: * intro: ext)
  ultimately show "sup (Cset.set xs) A = foldr insert xs A"
    by (simp add: foldr_fold)
  show "sup (Cset.coset xs) A = Cset.coset (List.filter (Not \<circ> member A) xs)"
    by (auto simp add: coset_def)
qed

context complete_lattice
begin

definition Infimum :: "'a Cset.set \<Rightarrow> 'a" where
  [simp]: "Infimum A = Inf (member A)"

lemma Infimum_inf [code]:
  "Infimum (Cset.set As) = foldr inf As top"
  "Infimum (Cset.coset []) = bot"
  by (simp_all add: Inf_set_foldr Inf_UNIV)

definition Supremum :: "'a Cset.set \<Rightarrow> 'a" where
  [simp]: "Supremum A = Sup (member A)"

lemma Supremum_sup [code]:
  "Supremum (Cset.set As) = foldr sup As bot"
  "Supremum (Cset.coset []) = top"
  by (simp_all add: Sup_set_foldr Sup_UNIV)

end


subsection {* Simplified simprules *}

lemma is_empty_simp [simp]:
  "is_empty A \<longleftrightarrow> member A = {}"
  by (simp add: More_Set.is_empty_def)
declare is_empty_def [simp del]

lemma remove_simp [simp]:
  "remove x A = Set (member A - {x})"
  by (simp add: More_Set.remove_def)
declare remove_def [simp del]

lemma filter_simp [simp]:
  "filter P A = Set {x \<in> member A. P x}"
  by (simp add: More_Set.project_def)
declare filter_def [simp del]

declare mem_def [simp del]


hide_const (open) setify is_empty insert remove map filter forall exists card
  Inter Union

end
