
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

definition insert :: "'a \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "insert x A = Set (Set.insert x (member A))"

definition remove :: "'a \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "remove x A = Set (More_Set.remove x (member A))"

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Cset.set \<Rightarrow> 'b Cset.set" where
  [simp]: "map f A = Set (image f (member A))"

enriched_type map: map
  by (simp_all add: fun_eq_iff image_compose)

definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "filter P A = Set (More_Set.project P (member A))"

definition forall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "forall P A \<longleftrightarrow> Ball (member A) P"

definition exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "exists P A \<longleftrightarrow> Bex (member A) P"

definition card :: "'a Cset.set \<Rightarrow> nat" where
  [simp]: "card A = Finite_Set.card (member A)"
  
context complete_lattice
begin

definition Infimum :: "'a Cset.set \<Rightarrow> 'a" where
  [simp]: "Infimum A = Inf (member A)"

definition Supremum :: "'a Cset.set \<Rightarrow> 'a" where
  [simp]: "Supremum A = Sup (member A)"

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


hide_const (open) is_empty insert remove map filter forall exists card
  Inter Union

end
