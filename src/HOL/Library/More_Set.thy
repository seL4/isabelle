
(* Author: Florian Haftmann, TU Muenchen *)

header {* Relating (finite) sets and lists *}

theory More_Set
imports Main More_List
begin

lemma comp_fun_idem_remove:
  "comp_fun_idem Set.remove"
proof -
  have rem: "Set.remove = (\<lambda>x A. A - {x})" by (simp add: fun_eq_iff remove_def)
  show ?thesis by (simp only: comp_fun_idem_remove rem)
qed

lemma minus_fold_remove:
  assumes "finite A"
  shows "B - A = Finite_Set.fold Set.remove B A"
proof -
  have rem: "Set.remove = (\<lambda>x A. A - {x})" by (simp add: fun_eq_iff remove_def)
  show ?thesis by (simp only: rem assms minus_fold_remove)
qed

lemma bounded_Collect_code [code_unfold_post]:
  "{x \<in> A. P x} = Set.project P A"
  by (simp add: project_def)


subsection {* Basic set operations *}

lemma is_empty_set:
  "Set.is_empty (set xs) \<longleftrightarrow> List.null xs"
  by (simp add: Set.is_empty_def null_def)

lemma empty_set:
  "{} = set []"
  by simp

lemma insert_set_compl:
  "insert x (- set xs) = - set (removeAll x xs)"
  by auto

lemma remove_set_compl:
  "Set.remove x (- set xs) = - set (List.insert x xs)"
  by (auto simp add: remove_def List.insert_def)

lemma image_set:
  "image f (set xs) = set (map f xs)"
  by simp

lemma project_set:
  "Set.project P (set xs) = set (filter P xs)"
  by (auto simp add: project_def)


subsection {* Functorial set operations *}

lemma union_set:
  "set xs \<union> A = fold Set.insert xs A"
proof -
  interpret comp_fun_idem Set.insert
    by (fact comp_fun_idem_insert)
  show ?thesis by (simp add: union_fold_insert fold_set)
qed

lemma union_set_foldr:
  "set xs \<union> A = foldr Set.insert xs A"
proof -
  have "\<And>x y :: 'a. insert y \<circ> insert x = insert x \<circ> insert y"
    by auto
  then show ?thesis by (simp add: union_set foldr_fold)
qed

lemma minus_set:
  "A - set xs = fold Set.remove xs A"
proof -
  interpret comp_fun_idem Set.remove
    by (fact comp_fun_idem_remove)
  show ?thesis
    by (simp add: minus_fold_remove [of _ A] fold_set)
qed

lemma minus_set_foldr:
  "A - set xs = foldr Set.remove xs A"
proof -
  have "\<And>x y :: 'a. Set.remove y \<circ> Set.remove x = Set.remove x \<circ> Set.remove y"
    by (auto simp add: remove_def)
  then show ?thesis by (simp add: minus_set foldr_fold)
qed


subsection {* Derived set operations *}

lemma member:
  "a \<in> A \<longleftrightarrow> (\<exists>x\<in>A. a = x)"
  by simp

lemma subset_eq:
  "A \<subseteq> B \<longleftrightarrow> (\<forall>x\<in>A. x \<in> B)"
  by (fact subset_eq)

lemma subset:
  "A \<subset> B \<longleftrightarrow> A \<subseteq> B \<and> \<not> B \<subseteq> A"
  by (fact less_le_not_le)

lemma set_eq:
  "A = B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A"
  by (fact eq_iff)

lemma inter:
  "A \<inter> B = Set.project (\<lambda>x. x \<in> A) B"
  by (auto simp add: project_def)


subsection {* Theorems on relations *}

lemma product_code:
  "Product_Type.product (set xs) (set ys) = set [(x, y). x \<leftarrow> xs, y \<leftarrow> ys]"
  by (auto simp add: Product_Type.product_def)

lemma Id_on_set:
  "Id_on (set xs) = set [(x, x). x \<leftarrow> xs]"
  by (auto simp add: Id_on_def)

lemma trancl_set_ntrancl: "trancl (set xs) = ntrancl (card (set xs) - 1) (set xs)"
  by (simp add: finite_trancl_ntranl)

lemma set_rel_comp:
  "set xys O set yzs = set ([(fst xy, snd yz). xy \<leftarrow> xys, yz \<leftarrow> yzs, snd xy = fst yz])"
  by (auto simp add: Bex_def)

lemma wf_set:
  "wf (set xs) = acyclic (set xs)"
  by (simp add: wf_iff_acyclic_if_finite)


subsection {* Code generator setup *}

definition coset :: "'a list \<Rightarrow> 'a set" where
  [simp]: "coset xs = - set xs"

code_datatype set coset


subsection {* Basic operations *}

lemma [code]:
  "x \<in> set xs \<longleftrightarrow> List.member xs x"
  "x \<in> coset xs \<longleftrightarrow> \<not> List.member xs x"
  by (simp_all add: member_def)

lemma [code_unfold]:
  "A = {} \<longleftrightarrow> Set.is_empty A"
  by (simp add: Set.is_empty_def)

declare empty_set [code]

declare is_empty_set [code]

lemma UNIV_coset [code]:
  "UNIV = coset []"
  by simp

lemma insert_code [code]:
  "insert x (set xs) = set (List.insert x xs)"
  "insert x (coset xs) = coset (removeAll x xs)"
  by simp_all

lemma remove_code [code]:
  "Set.remove x (set xs) = set (removeAll x xs)"
  "Set.remove x (coset xs) = coset (List.insert x xs)"
  by (simp_all add: remove_def Compl_insert)

declare image_set [code]

declare project_set [code]

lemma Ball_set [code]:
  "Ball (set xs) P \<longleftrightarrow> list_all P xs"
  by (simp add: list_all_iff)

lemma Bex_set [code]:
  "Bex (set xs) P \<longleftrightarrow> list_ex P xs"
  by (simp add: list_ex_iff)

lemma card_set [code]:
  "card (set xs) = length (remdups xs)"
proof -
  have "card (set (remdups xs)) = length (remdups xs)"
    by (rule distinct_card) simp
  then show ?thesis by simp
qed


subsection {* Derived operations *}

declare subset_eq [code]

declare subset [code]


subsection {* Functorial operations *}

lemma inter_code [code]:
  "A \<inter> set xs = set (List.filter (\<lambda>x. x \<in> A) xs)"
  "A \<inter> coset xs = foldr Set.remove xs A"
  by (simp add: inter project_def) (simp add: Diff_eq [symmetric] minus_set_foldr)

lemma subtract_code [code]:
  "A - set xs = foldr Set.remove xs A"
  "A - coset xs = set (List.filter (\<lambda>x. x \<in> A) xs)"
  by (auto simp add: minus_set_foldr)

lemma union_code [code]:
  "set xs \<union> A = foldr insert xs A"
  "coset xs \<union> A = coset (List.filter (\<lambda>x. x \<notin> A) xs)"
  by (auto simp add: union_set_foldr)

definition Inf :: "'a::complete_lattice set \<Rightarrow> 'a" where
  [simp]: "Inf = Complete_Lattices.Inf"

hide_const (open) Inf

lemma [code_unfold_post]:
  "Inf = More_Set.Inf"
  by simp

definition Sup :: "'a::complete_lattice set \<Rightarrow> 'a" where
  [simp]: "Sup = Complete_Lattices.Sup"

hide_const (open) Sup

lemma [code_unfold_post]:
  "Sup = More_Set.Sup"
  by simp

lemma Inf_code [code]:
  "More_Set.Inf (set xs) = foldr inf xs top"
  "More_Set.Inf (coset []) = bot"
  by (simp_all add: Inf_set_foldr)

lemma Sup_sup [code]:
  "More_Set.Sup (set xs) = foldr sup xs bot"
  "More_Set.Sup (coset []) = top"
  by (simp_all add: Sup_set_foldr)

lemma INF_code [code]:
  "INFI (set xs) f = foldr (inf \<circ> f) xs top"
  by (simp add: INF_def Inf_set_foldr image_set foldr_map del: set_map)

lemma SUP_sup [code]:
  "SUPR (set xs) f = foldr (sup \<circ> f) xs bot"
  by (simp add: SUP_def Sup_set_foldr image_set foldr_map del: set_map)

hide_const (open) coset


subsection {* Operations on relations *}

text {* Initially contributed by Tjark Weber. *}

declare Domain_fst [code]

declare Range_snd [code]

declare trans_join [code]

declare irrefl_distinct [code]

declare trancl_set_ntrancl [code]

declare acyclic_irrefl [code]

declare product_code [code]

declare Id_on_set [code]

declare set_rel_comp [code]

declare wf_set [code]

end

