
(* Author: Florian Haftmann, TU Muenchen *)

header {* implementation of Cset.sets based on lists *}

theory List_Cset
imports Cset
begin

declare mem_def [simp]
declare Cset.set_code [code del]

definition coset :: "'a list \<Rightarrow> 'a Cset.set" where
  "coset xs = Set (- set xs)"
hide_const (open) coset

lemma member_coset [simp]:
  "member (List_Cset.coset xs) = - set xs"
  by (simp add: coset_def)
hide_fact (open) member_coset

code_datatype Cset.set List_Cset.coset

lemma member_code [code]:
  "member (Cset.set xs) = List.member xs"
  "member (List_Cset.coset xs) = Not \<circ> List.member xs"
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

subsection {* Basic operations *}

lemma is_empty_set [code]:
  "Cset.is_empty (Cset.set xs) \<longleftrightarrow> List.null xs"
  by (simp add: is_empty_set null_def)
hide_fact (open) is_empty_set

lemma empty_set [code]:
  "Cset.empty = Cset.set []"
  by (simp add: set_def)
hide_fact (open) empty_set

lemma UNIV_set [code]:
  "top = List_Cset.coset []"
  by (simp add: coset_def)
hide_fact (open) UNIV_set

lemma remove_set [code]:
  "Cset.remove x (Cset.set xs) = Cset.set (removeAll x xs)"
  "Cset.remove x (List_Cset.coset xs) = List_Cset.coset (List.insert x xs)"
by (simp_all add: Cset.set_def coset_def)
  (metis List.set_insert More_Set.remove_def remove_set_compl)

lemma insert_set [code]:
  "Cset.insert x (Cset.set xs) = Cset.set (List.insert x xs)"
  "Cset.insert x (List_Cset.coset xs) = List_Cset.coset (removeAll x xs)"
  by (simp_all add: Cset.set_def coset_def)

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

lemma compl_set [simp, code]:
  "- Cset.set xs = List_Cset.coset xs"
  by (simp add: Cset.set_def coset_def)

lemma compl_coset [simp, code]:
  "- List_Cset.coset xs = Cset.set xs"
  by (simp add: Cset.set_def coset_def)

context complete_lattice
begin

lemma Infimum_inf [code]:
  "Infimum (Cset.set As) = foldr inf As top"
  "Infimum (List_Cset.coset []) = bot"
  by (simp_all add: Inf_set_foldr Inf_UNIV)

lemma Supremum_sup [code]:
  "Supremum (Cset.set As) = foldr sup As bot"
  "Supremum (List_Cset.coset []) = top"
  by (simp_all add: Sup_set_foldr Sup_UNIV)

end

declare Cset.single_code [code del]
lemma single_set [code]:
  "Cset.single a = Cset.set [a]"
by(simp add: Cset.single_code)
hide_fact (open) single_set

lemma bind_set [code]:
  "Cset.bind (Cset.set xs) f = foldl (\<lambda>A x. sup A (f x)) (Cset.set []) xs"
proof(rule sym)
  show "foldl (\<lambda>A x. sup A (f x)) (Cset.set []) xs = Cset.bind (Cset.set xs) f"
    by(induct xs rule: rev_induct)(auto simp add: Cset.bind_def Cset.set_def)
qed
hide_fact (open) bind_set

lemma pred_of_cset_set [code]:
  "pred_of_cset (Cset.set xs) = foldr sup (map Predicate.single xs) bot"
proof -
  have "pred_of_cset (Cset.set xs) = Predicate.Pred (\<lambda>x. x \<in> set xs)"
    by(auto simp add: Cset.pred_of_cset_def mem_def)
  moreover have "foldr sup (map Predicate.single xs) bot = \<dots>"
    by(induct xs)(auto simp add: bot_pred_def simp del: mem_def intro: pred_eqI, simp)
  ultimately show ?thesis by(simp)
qed
hide_fact (open) pred_of_cset_set

subsection {* Derived operations *}

lemma subset_eq_forall [code]:
  "A \<le> B \<longleftrightarrow> Cset.forall (member B) A"
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
  "inf A (Cset.set xs) = Cset.set (List.filter (Cset.member A) xs)"
  "inf A (List_Cset.coset xs) = foldr Cset.remove xs A"
proof -
  show "inf A (Cset.set xs) = Cset.set (List.filter (member A) xs)"
    by (simp add: inter project_def Cset.set_def)
  have *: "\<And>x::'a. Cset.remove = (\<lambda>x. Set \<circ> More_Set.remove x \<circ> member)"
    by (simp add: fun_eq_iff More_Set.remove_def)
  have "member \<circ> fold (\<lambda>x. Set \<circ> More_Set.remove x \<circ> member) xs =
    fold More_Set.remove xs \<circ> member"
    by (rule fold_commute) (simp add: fun_eq_iff)
  then have "fold More_Set.remove xs (member A) = 
    member (fold (\<lambda>x. Set \<circ> More_Set.remove x \<circ> member) xs A)"
    by (simp add: fun_eq_iff)
  then have "inf A (List_Cset.coset xs) = fold Cset.remove xs A"
    by (simp add: Diff_eq [symmetric] minus_set *)
  moreover have "\<And>x y :: 'a. Cset.remove y \<circ> Cset.remove x = Cset.remove x \<circ> Cset.remove y"
    by (auto simp add: More_Set.remove_def * intro: ext)
  ultimately show "inf A (List_Cset.coset xs) = foldr Cset.remove xs A"
    by (simp add: foldr_fold)
qed

lemma subtract_remove [code]:
  "A - Cset.set xs = foldr Cset.remove xs A"
  "A - List_Cset.coset xs = Cset.set (List.filter (member A) xs)"
  by (simp_all only: diff_eq compl_set compl_coset inter_project)

lemma union_insert [code]:
  "sup (Cset.set xs) A = foldr Cset.insert xs A"
  "sup (List_Cset.coset xs) A = List_Cset.coset (List.filter (Not \<circ> member A) xs)"
proof -
  have *: "\<And>x::'a. Cset.insert = (\<lambda>x. Set \<circ> Set.insert x \<circ> member)"
    by (simp add: fun_eq_iff)
  have "member \<circ> fold (\<lambda>x. Set \<circ> Set.insert x \<circ> member) xs =
    fold Set.insert xs \<circ> member"
    by (rule fold_commute) (simp add: fun_eq_iff)
  then have "fold Set.insert xs (member A) =
    member (fold (\<lambda>x. Set \<circ> Set.insert x \<circ> member) xs A)"
    by (simp add: fun_eq_iff)
  then have "sup (Cset.set xs) A = fold Cset.insert xs A"
    by (simp add: union_set *)
  moreover have "\<And>x y :: 'a. Cset.insert y \<circ> Cset.insert x = Cset.insert x \<circ> Cset.insert y"
    by (auto simp add: * intro: ext)
  ultimately show "sup (Cset.set xs) A = foldr Cset.insert xs A"
    by (simp add: foldr_fold)
  show "sup (List_Cset.coset xs) A = List_Cset.coset (List.filter (Not \<circ> member A) xs)"
    by (auto simp add: coset_def)
qed

declare mem_def[simp del]

end