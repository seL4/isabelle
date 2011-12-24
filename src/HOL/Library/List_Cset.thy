
(* Author: Florian Haftmann, TU Muenchen *)

header {* implementation of Cset.sets based on lists *}

theory List_Cset
imports Cset
begin

code_datatype Cset.set Cset.coset

lemma member_code [code]:
  "member (Cset.set xs) = List.member xs"
  "member (Cset.coset xs) = Not \<circ> List.member xs"
  by (simp_all add: fun_eq_iff List.member_def)

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

subsection {* Basic operations *}

lemma is_empty_set [code]:
  "Cset.is_empty (Cset.set xs) \<longleftrightarrow> List.null xs"
  by (simp add: is_empty_set null_def)
hide_fact (open) is_empty_set

lemma empty_set [code]:
  "Cset.empty = Cset.set []"
  by simp
hide_fact (open) empty_set

lemma UNIV_set [code]:
  "top = Cset.coset []"
  by (simp add: Cset.coset_def)
hide_fact (open) UNIV_set

lemma remove_set [code]:
  "Cset.remove x (Cset.set xs) = Cset.set (removeAll x xs)"
  "Cset.remove x (Cset.coset xs) = Cset.coset (List.insert x xs)"
  by (simp_all add: Cset.set_def Cset.coset_def Compl_insert)

lemma insert_set [code]:
  "Cset.insert x (Cset.set xs) = Cset.set (List.insert x xs)"
  "Cset.insert x (Cset.coset xs) = Cset.coset (removeAll x xs)"
  by (simp_all add: Cset.set_def Cset.coset_def)

declare compl_set [code]
declare compl_coset [code]
declare subtract_remove [code]

lemma map_set [code]:
  "Cset.map f (Cset.set xs) = Cset.set (remdups (List.map f xs))"
  by (simp add: Cset.set_def)
  
lemma filter_set [code]:
  "Cset.filter P (Cset.set xs) = Cset.set (List.filter P xs)"
  by (simp add: Cset.set_def project_set)

lemma forall_set [code]:
  "Cset.forall P (Cset.set xs) \<longleftrightarrow> list_all P xs"
  by (simp add: Cset.set_def list_all_iff)

lemma exists_set [code]:
  "Cset.exists P (Cset.set xs) \<longleftrightarrow> list_ex P xs"
  by (simp add: Cset.set_def list_ex_iff)

lemma card_set [code]:
  "Cset.card (Cset.set xs) = length (remdups xs)"
proof -
  have "Finite_Set.card (set (remdups xs)) = length (remdups xs)"
    by (rule distinct_card) simp
  then show ?thesis by (simp add: Cset.set_def)
qed

context complete_lattice
begin

declare Infimum_inf [code]
declare Supremum_sup [code]

end

declare Cset.single_code [code del]
lemma single_set [code]:
  "Cset.single a = Cset.set [a]"
by(simp add: Cset.single_code)
hide_fact (open) single_set

declare Cset.bind_set [code]
declare Cset.pred_of_cset_set [code]


subsection {* Derived operations *}

lemma subset_eq_forall [code]:
  "A \<le> B \<longleftrightarrow> Cset.forall (member B) A"
  by (simp add: subset_eq member_def)

lemma subset_subset_eq [code]:
  "A < B \<longleftrightarrow> A \<le> B \<and> \<not> B \<le> (A :: 'a Cset.set)"
  by (fact less_le_not_le)

instantiation Cset.set :: (type) equal
begin

definition [code]:
  "HOL.equal A B \<longleftrightarrow> A \<le> B \<and> B \<le> (A :: 'a Cset.set)"

instance proof
qed (auto simp add: equal_set_def Cset.set_eq_iff Cset.member_def fun_eq_iff)

end

lemma [code nbe]:
  "HOL.equal (A :: 'a Cset.set) A \<longleftrightarrow> True"
  by (fact equal_refl)


subsection {* Functorial operations *}

declare inter_project [code]
declare union_insert [code]

end
