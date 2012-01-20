(*  Title:      HOL/Quotient_Examples/List_Quotient_Cset.thy
    Author:     Florian Haftmann, Alexander Krauss, TU Muenchen
*)

header {* Implementation of type Quotient_Cset.set based on lists. Code equations obtained via quotient lifting. *}

theory List_Quotient_Cset
imports Quotient_Cset
begin

lemma [quot_respect]: "((op = ===> set_eq ===> set_eq) ===> op = ===> set_eq ===> set_eq)
  foldr foldr"
by (simp add: fun_rel_eq)

lemma [quot_preserve]: "((id ---> abs_set ---> rep_set) ---> id ---> rep_set ---> abs_set) foldr = foldr"
apply (rule ext)+
by (induct_tac xa) (auto simp: Quotient_abs_rep[OF Quotient_set])


subsection {* Relationship to lists *}

(*FIXME: maybe define on sets first and then lift -> more canonical*)
definition coset :: "'a list \<Rightarrow> 'a Quotient_Cset.set" where
  "coset xs = Quotient_Cset.uminus (Quotient_Cset.set xs)"

code_datatype Quotient_Cset.set List_Quotient_Cset.coset

lemma member_code [code]:
  "member x (Quotient_Cset.set xs) \<longleftrightarrow> List.member xs x"
  "member x (coset xs) \<longleftrightarrow> \<not> List.member xs x"
unfolding coset_def
apply (lifting in_set_member)
by descending (simp add: in_set_member)

definition (in term_syntax)
  csetify :: "'a\<Colon>typerep list \<times> (unit \<Rightarrow> Code_Evaluation.term)
    \<Rightarrow> 'a Quotient_Cset.set \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  [code_unfold]: "csetify xs = Code_Evaluation.valtermify Quotient_Cset.set {\<cdot>} xs"

notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation Quotient_Cset.set :: (random) random
begin

definition
  "Quickcheck.random i = Quickcheck.random i \<circ>\<rightarrow> (\<lambda>xs. Pair (csetify xs))"

instance ..

end

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)

subsection {* Basic operations *}

lemma is_empty_set [code]:
  "Quotient_Cset.is_empty (Quotient_Cset.set xs) \<longleftrightarrow> List.null xs"
  by (lifting is_empty_set)
hide_fact (open) is_empty_set

lemma empty_set [code]:
  "Quotient_Cset.empty = Quotient_Cset.set []"
  by (lifting set.simps(1)[symmetric])
hide_fact (open) empty_set

lemma UNIV_set [code]:
  "Quotient_Cset.UNIV = coset []"
  unfolding coset_def by descending simp
hide_fact (open) UNIV_set

lemma remove_set [code]:
  "Quotient_Cset.remove x (Quotient_Cset.set xs) = Quotient_Cset.set (removeAll x xs)"
  "Quotient_Cset.remove x (coset xs) = coset (List.insert x xs)"
unfolding coset_def
apply descending
apply (simp add: Set.remove_def)
apply descending
by (auto simp add: set_eq_iff)

lemma insert_set [code]:
  "Quotient_Cset.insert x (Quotient_Cset.set xs) = Quotient_Cset.set (List.insert x xs)"
  "Quotient_Cset.insert x (coset xs) = coset (removeAll x xs)"
unfolding coset_def
apply (lifting set_insert[symmetric])
by descending simp

lemma map_set [code]:
  "Quotient_Cset.map f (Quotient_Cset.set xs) = Quotient_Cset.set (remdups (List.map f xs))"
by descending simp

lemma filter_set [code]:
  "Quotient_Cset.filter P (Quotient_Cset.set xs) = Quotient_Cset.set (List.filter P xs)"
by descending (simp add: set_eq_iff)

lemma forall_set [code]:
  "Quotient_Cset.forall (Quotient_Cset.set xs) P \<longleftrightarrow> list_all P xs"
(* FIXME: why does (lifting Ball_set_list_all) fail? *)
by descending (fact Ball_set_list_all)

lemma exists_set [code]:
  "Quotient_Cset.exists (Quotient_Cset.set xs) P \<longleftrightarrow> list_ex P xs"
by descending (fact Bex_set_list_ex)

lemma card_set [code]:
  "Quotient_Cset.card (Quotient_Cset.set xs) = length (remdups xs)"
by (lifting length_remdups_card_conv[symmetric])

lemma compl_set [simp, code]:
  "Quotient_Cset.uminus (Quotient_Cset.set xs) = coset xs"
unfolding coset_def by descending simp

lemma compl_coset [simp, code]:
  "Quotient_Cset.uminus (coset xs) = Quotient_Cset.set xs"
unfolding coset_def by descending simp

lemma Inf_inf [code]:
  "Quotient_Cset.Inf (Quotient_Cset.set (xs\<Colon>'a\<Colon>complete_lattice list)) = foldr inf xs top"
  "Quotient_Cset.Inf (coset ([]\<Colon>'a\<Colon>complete_lattice list)) = bot"
  unfolding List_Quotient_Cset.UNIV_set[symmetric]
  by (lifting Inf_set_foldr Inf_UNIV)

lemma Sup_sup [code]:
  "Quotient_Cset.Sup (Quotient_Cset.set (xs\<Colon>'a\<Colon>complete_lattice list)) = foldr sup xs bot"
  "Quotient_Cset.Sup (coset ([]\<Colon>'a\<Colon>complete_lattice list)) = top"
  unfolding List_Quotient_Cset.UNIV_set[symmetric]
  by (lifting Sup_set_foldr Sup_UNIV)

subsection {* Derived operations *}

lemma subset_eq_forall [code]:
  "Quotient_Cset.subset A B \<longleftrightarrow> Quotient_Cset.forall A (\<lambda>x. member x B)"
by descending blast

lemma subset_subset_eq [code]:
  "Quotient_Cset.psubset A B \<longleftrightarrow> Quotient_Cset.subset A B \<and> \<not> Quotient_Cset.subset B A"
by descending blast

instantiation Quotient_Cset.set :: (type) equal
begin

definition [code]:
  "HOL.equal A B \<longleftrightarrow> Quotient_Cset.subset A B \<and> Quotient_Cset.subset B A"

instance
apply intro_classes
unfolding equal_set_def
by descending auto

end

lemma [code nbe]:
  "HOL.equal (A :: 'a Quotient_Cset.set) A \<longleftrightarrow> True"
  by (fact equal_refl)


subsection {* Functorial operations *}

lemma inter_project [code]:
  "Quotient_Cset.inter A (Quotient_Cset.set xs) = Quotient_Cset.set (List.filter (\<lambda>x. Quotient_Cset.member x A) xs)"
  "Quotient_Cset.inter A (coset xs) = foldr Quotient_Cset.remove xs A"
apply descending
apply auto
unfolding coset_def
apply descending
apply simp
by (metis diff_eq minus_set_foldr)

lemma subtract_remove [code]:
  "Quotient_Cset.minus A (Quotient_Cset.set xs) = foldr Quotient_Cset.remove xs A"
  "Quotient_Cset.minus A (coset xs) = Quotient_Cset.set (List.filter (\<lambda>x. member x A) xs)"
unfolding coset_def
apply (lifting minus_set_foldr)
by descending auto

lemma union_insert [code]:
  "Quotient_Cset.union (Quotient_Cset.set xs) A = foldr Quotient_Cset.insert xs A"
  "Quotient_Cset.union (coset xs) A = coset (List.filter (\<lambda>x. \<not> member x A) xs)"
unfolding coset_def
apply (lifting union_set_foldr)
by descending auto

lemma UNION_code [code]:
  "Quotient_Cset.UNION (Quotient_Cset.set []) f = Quotient_Cset.set []"
  "Quotient_Cset.UNION (Quotient_Cset.set (x#xs)) f =
     Quotient_Cset.union (f x) (Quotient_Cset.UNION (Quotient_Cset.set xs) f)"
  by (descending, simp)+


end
