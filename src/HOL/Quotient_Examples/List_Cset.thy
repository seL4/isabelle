(*  Title:      HOL/Quotient_Examples/List_Cset.thy
    Author:     Florian Haftmann, Alexander Krauss, TU Muenchen
*)

header {* Implementation of type Cset.set based on lists. Code equations obtained via quotient lifting. *}

theory List_Cset
imports Cset
begin

lemma [quot_respect]: "((op = ===> set_eq ===> set_eq) ===> op = ===> set_eq ===> set_eq)
  foldr foldr"
by (simp add: fun_rel_eq)

lemma [quot_preserve]: "((id ---> abs_set ---> rep_set) ---> id ---> rep_set ---> abs_set) foldr = foldr"
apply (rule ext)+
by (induct_tac xa) (auto simp: Quotient_abs_rep[OF Quotient_set])


subsection {* Relationship to lists *}

(*FIXME: maybe define on sets first and then lift -> more canonical*)
definition coset :: "'a list \<Rightarrow> 'a Cset.set" where
  "coset xs = Cset.uminus (Cset.set xs)"

code_datatype Cset.set List_Cset.coset

lemma member_code [code]:
  "member x (Cset.set xs) \<longleftrightarrow> List.member xs x"
  "member x (coset xs) \<longleftrightarrow> \<not> List.member xs x"
unfolding coset_def
apply (lifting in_set_member)
by descending (simp add: in_set_member)

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
  by (lifting is_empty_set)
hide_fact (open) is_empty_set

lemma empty_set [code]:
  "Cset.empty = Cset.set []"
  by (lifting set.simps(1)[symmetric])
hide_fact (open) empty_set

lemma UNIV_set [code]:
  "Cset.UNIV = coset []"
  unfolding coset_def by descending simp
hide_fact (open) UNIV_set

lemma remove_set [code]:
  "Cset.remove x (Cset.set xs) = Cset.set (removeAll x xs)"
  "Cset.remove x (coset xs) = coset (List.insert x xs)"
unfolding coset_def
apply descending
apply (simp add: More_Set.remove_def)
apply descending
by (simp add: remove_set_compl)

lemma insert_set [code]:
  "Cset.insert x (Cset.set xs) = Cset.set (List.insert x xs)"
  "Cset.insert x (coset xs) = coset (removeAll x xs)"
unfolding coset_def
apply (lifting set_insert[symmetric])
by descending simp

lemma map_set [code]:
  "Cset.map f (Cset.set xs) = Cset.set (remdups (List.map f xs))"
by descending simp

lemma filter_set [code]:
  "Cset.filter P (Cset.set xs) = Cset.set (List.filter P xs)"
by descending (simp add: project_set)

lemma forall_set [code]:
  "Cset.forall (Cset.set xs) P \<longleftrightarrow> list_all P xs"
(* FIXME: why does (lifting Ball_set_list_all) fail? *)
by descending (fact Ball_set_list_all)

lemma exists_set [code]:
  "Cset.exists (Cset.set xs) P \<longleftrightarrow> list_ex P xs"
by descending (fact Bex_set_list_ex)

lemma card_set [code]:
  "Cset.card (Cset.set xs) = length (remdups xs)"
by (lifting length_remdups_card_conv[symmetric])

lemma compl_set [simp, code]:
  "Cset.uminus (Cset.set xs) = coset xs"
unfolding coset_def by descending simp

lemma compl_coset [simp, code]:
  "Cset.uminus (coset xs) = Cset.set xs"
unfolding coset_def by descending simp

lemma Inf_inf [code]:
  "Cset.Inf (Cset.set (xs\<Colon>'a\<Colon>complete_lattice list)) = foldr inf xs top"
  "Cset.Inf (coset ([]\<Colon>'a\<Colon>complete_lattice list)) = bot"
  unfolding List_Cset.UNIV_set[symmetric]
  by (lifting Inf_set_foldr Inf_UNIV)

lemma Sup_sup [code]:
  "Cset.Sup (Cset.set (xs\<Colon>'a\<Colon>complete_lattice list)) = foldr sup xs bot"
  "Cset.Sup (coset ([]\<Colon>'a\<Colon>complete_lattice list)) = top"
  unfolding List_Cset.UNIV_set[symmetric]
  by (lifting Sup_set_foldr Sup_UNIV)

subsection {* Derived operations *}

lemma subset_eq_forall [code]:
  "Cset.subset A B \<longleftrightarrow> Cset.forall A (\<lambda>x. member x B)"
by descending blast

lemma subset_subset_eq [code]:
  "Cset.psubset A B \<longleftrightarrow> Cset.subset A B \<and> \<not> Cset.subset B A"
by descending blast

instantiation Cset.set :: (type) equal
begin

definition [code]:
  "HOL.equal A B \<longleftrightarrow> Cset.subset A B \<and> Cset.subset B A"

instance
apply intro_classes
unfolding equal_set_def
by descending auto

end

lemma [code nbe]:
  "HOL.equal (A :: 'a Cset.set) A \<longleftrightarrow> True"
  by (fact equal_refl)


subsection {* Functorial operations *}

lemma inter_project [code]:
  "Cset.inter A (Cset.set xs) = Cset.set (List.filter (\<lambda>x. Cset.member x A) xs)"
  "Cset.inter A (coset xs) = foldr Cset.remove xs A"
apply descending
apply auto
unfolding coset_def
apply descending
apply simp
by (metis diff_eq minus_set_foldr)

lemma subtract_remove [code]:
  "Cset.minus A (Cset.set xs) = foldr Cset.remove xs A"
  "Cset.minus A (coset xs) = Cset.set (List.filter (\<lambda>x. member x A) xs)"
unfolding coset_def
apply (lifting minus_set_foldr)
by descending auto

lemma union_insert [code]:
  "Cset.union (Cset.set xs) A = foldr Cset.insert xs A"
  "Cset.union (coset xs) A = coset (List.filter (\<lambda>x. \<not> member x A) xs)"
unfolding coset_def
apply (lifting union_set_foldr)
by descending auto

lemma UNION_code [code]:
  "Cset.UNION (Cset.set []) f = Cset.set []"
  "Cset.UNION (Cset.set (x#xs)) f =
     Cset.union (f x) (Cset.UNION (Cset.set xs) f)"
  by (descending, simp)+


end
