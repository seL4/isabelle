(*  Title:      HOL/Quotient_Examples/List_Quotient_Set.thy
    Author:     Florian Haftmann, Alexander Krauss, TU Muenchen
*)

header {* Implementation of type Quotient_Set.set based on lists. Code equations obtained via quotient lifting. *}

theory List_Quotient_Set
imports Quotient_Set
begin

lemma [quot_respect]: "((op = ===> set_eq ===> set_eq) ===> op = ===> set_eq ===> set_eq)
  foldr foldr"
by (simp add: fun_rel_eq)

lemma [quot_preserve]: "((id ---> abs_set ---> rep_set) ---> id ---> rep_set ---> abs_set) foldr = foldr"
apply (rule ext)+
by (induct_tac xa) (auto simp: Quotient_abs_rep[OF Quotient_set])


subsection {* Relationship to lists *}

(*FIXME: maybe define on sets first and then lift -> more canonical*)
definition coset :: "'a list \<Rightarrow> 'a Quotient_Set.set" where
  "coset xs = Quotient_Set.uminus (Quotient_Set.set xs)"

code_datatype Quotient_Set.set List_Quotient_Set.coset

lemma member_code [code]:
  "member x (Quotient_Set.set xs) \<longleftrightarrow> List.member xs x"
  "member x (coset xs) \<longleftrightarrow> \<not> List.member xs x"
unfolding coset_def
apply (lifting in_set_member)
by descending (simp add: in_set_member)

definition (in term_syntax)
  setify :: "'a\<Colon>typerep list \<times> (unit \<Rightarrow> Code_Evaluation.term)
    \<Rightarrow> 'a Quotient_Set.set \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  [code_unfold]: "setify xs = Code_Evaluation.valtermify Quotient_Set.set {\<cdot>} xs"

notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation Quotient_Set.set :: (random) random
begin

definition
  "Quickcheck.random i = Quickcheck.random i \<circ>\<rightarrow> (\<lambda>xs. Pair (setify xs))"

instance ..

end

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)

subsection {* Basic operations *}

lemma is_empty_set [code]:
  "Quotient_Set.is_empty (Quotient_Set.set xs) \<longleftrightarrow> List.null xs"
  by (lifting is_empty_set)
hide_fact (open) is_empty_set

lemma empty_set [code]:
  "Quotient_Set.empty = Quotient_Set.set []"
  by (lifting set.simps(1)[symmetric])
hide_fact (open) empty_set

lemma UNIV_set [code]:
  "Quotient_Set.UNIV = coset []"
  unfolding coset_def by descending simp
hide_fact (open) UNIV_set

lemma remove_set [code]:
  "Quotient_Set.remove x (Quotient_Set.set xs) = Quotient_Set.set (removeAll x xs)"
  "Quotient_Set.remove x (coset xs) = coset (List.insert x xs)"
unfolding coset_def
apply descending
apply (simp add: More_Set.remove_def)
apply descending
by (simp add: remove_set_compl)

lemma insert_set [code]:
  "Quotient_Set.insert x (Quotient_Set.set xs) = Quotient_Set.set (List.insert x xs)"
  "Quotient_Set.insert x (coset xs) = coset (removeAll x xs)"
unfolding coset_def
apply (lifting set_insert[symmetric])
by descending simp

lemma map_set [code]:
  "Quotient_Set.map f (Quotient_Set.set xs) = Quotient_Set.set (remdups (List.map f xs))"
by descending simp

lemma filter_set [code]:
  "Quotient_Set.filter P (Quotient_Set.set xs) = Quotient_Set.set (List.filter P xs)"
by descending (simp add: project_set)

lemma forall_set [code]:
  "Quotient_Set.forall (Quotient_Set.set xs) P \<longleftrightarrow> list_all P xs"
(* FIXME: why does (lifting Ball_set_list_all) fail? *)
by descending (fact Ball_set_list_all)

lemma exists_set [code]:
  "Quotient_Set.exists (Quotient_Set.set xs) P \<longleftrightarrow> list_ex P xs"
by descending (fact Bex_set_list_ex)

lemma card_set [code]:
  "Quotient_Set.card (Quotient_Set.set xs) = length (remdups xs)"
by (lifting length_remdups_card_conv[symmetric])

lemma compl_set [simp, code]:
  "Quotient_Set.uminus (Quotient_Set.set xs) = coset xs"
unfolding coset_def by descending simp

lemma compl_coset [simp, code]:
  "Quotient_Set.uminus (coset xs) = Quotient_Set.set xs"
unfolding coset_def by descending simp

lemma Inf_inf [code]:
  "Quotient_Set.Inf (Quotient_Set.set (xs\<Colon>'a\<Colon>complete_lattice list)) = foldr inf xs top"
  "Quotient_Set.Inf (coset ([]\<Colon>'a\<Colon>complete_lattice list)) = bot"
  unfolding List_Quotient_Set.UNIV_set[symmetric]
  by (lifting Inf_set_foldr Inf_UNIV)

lemma Sup_sup [code]:
  "Quotient_Set.Sup (Quotient_Set.set (xs\<Colon>'a\<Colon>complete_lattice list)) = foldr sup xs bot"
  "Quotient_Set.Sup (coset ([]\<Colon>'a\<Colon>complete_lattice list)) = top"
  unfolding List_Quotient_Set.UNIV_set[symmetric]
  by (lifting Sup_set_foldr Sup_UNIV)

subsection {* Derived operations *}

lemma subset_eq_forall [code]:
  "Quotient_Set.subset A B \<longleftrightarrow> Quotient_Set.forall A (\<lambda>x. member x B)"
by descending blast

lemma subset_subset_eq [code]:
  "Quotient_Set.psubset A B \<longleftrightarrow> Quotient_Set.subset A B \<and> \<not> Quotient_Set.subset B A"
by descending blast

instantiation Quotient_Set.set :: (type) equal
begin

definition [code]:
  "HOL.equal A B \<longleftrightarrow> Quotient_Set.subset A B \<and> Quotient_Set.subset B A"

instance
apply intro_classes
unfolding equal_set_def
by descending auto

end

lemma [code nbe]:
  "HOL.equal (A :: 'a Quotient_Set.set) A \<longleftrightarrow> True"
  by (fact equal_refl)


subsection {* Functorial operations *}

lemma inter_project [code]:
  "Quotient_Set.inter A (Quotient_Set.set xs) = Quotient_Set.set (List.filter (\<lambda>x. Quotient_Set.member x A) xs)"
  "Quotient_Set.inter A (coset xs) = foldr Quotient_Set.remove xs A"
apply descending
apply auto
unfolding coset_def
apply descending
apply simp
by (metis diff_eq minus_set_foldr)

lemma subtract_remove [code]:
  "Quotient_Set.minus A (Quotient_Set.set xs) = foldr Quotient_Set.remove xs A"
  "Quotient_Set.minus A (coset xs) = Quotient_Set.set (List.filter (\<lambda>x. member x A) xs)"
unfolding coset_def
apply (lifting minus_set_foldr)
by descending auto

lemma union_insert [code]:
  "Quotient_Set.union (Quotient_Set.set xs) A = foldr Quotient_Set.insert xs A"
  "Quotient_Set.union (coset xs) A = coset (List.filter (\<lambda>x. \<not> member x A) xs)"
unfolding coset_def
apply (lifting union_set_foldr)
by descending auto

lemma UNION_code [code]:
  "Quotient_Set.UNION (Quotient_Set.set []) f = Quotient_Set.set []"
  "Quotient_Set.UNION (Quotient_Set.set (x#xs)) f =
     Quotient_Set.union (f x) (Quotient_Set.UNION (Quotient_Set.set xs) f)"
  by (descending, simp)+


end
