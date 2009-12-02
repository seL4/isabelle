
(* Author: Florian Haftmann, TU Muenchen *)

header {* Relating (finite) sets and lists *}

theory List_Set
imports Main
begin

subsection {* Various additional list functions *}

definition insert :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert x xs = (if x \<in> set xs then xs else x # xs)"

definition remove_all :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_all x xs = filter (Not o op = x) xs"


subsection {* Various additional set functions *}

definition is_empty :: "'a set \<Rightarrow> bool" where
  "is_empty A \<longleftrightarrow> A = {}"

definition remove :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "remove x A = A - {x}"

lemma fun_left_comm_idem_remove:
  "fun_left_comm_idem remove"
proof -
  have rem: "remove = (\<lambda>x A. A - {x})" by (simp add: expand_fun_eq remove_def)
  show ?thesis by (simp only: fun_left_comm_idem_remove rem)
qed

lemma minus_fold_remove:
  assumes "finite A"
  shows "B - A = fold remove B A"
proof -
  have rem: "remove = (\<lambda>x A. A - {x})" by (simp add: expand_fun_eq remove_def)
  show ?thesis by (simp only: rem assms minus_fold_remove)
qed

definition project :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "project P A = {a\<in>A. P a}"


subsection {* Basic set operations *}

lemma is_empty_set:
  "is_empty (set xs) \<longleftrightarrow> null xs"
  by (simp add: is_empty_def null_empty)

lemma ball_set:
  "(\<forall>x\<in>set xs. P x) \<longleftrightarrow> list_all P xs"
  by (rule list_ball_code)

lemma bex_set:
  "(\<exists>x\<in>set xs. P x) \<longleftrightarrow> list_ex P xs"
  by (rule list_bex_code)

lemma empty_set:
  "{} = set []"
  by simp

lemma insert_set:
  "Set.insert x (set xs) = set (insert x xs)"
  by (auto simp add: insert_def)

lemma insert_set_compl:
  "Set.insert x (- set xs) = - set (List_Set.remove_all x xs)"
  by (auto simp del: mem_def simp add: remove_all_def)

lemma remove_set:
  "remove x (set xs) = set (remove_all x xs)"
  by (auto simp add: remove_def remove_all_def)

lemma remove_set_compl:
  "List_Set.remove x (- set xs) = - set (List_Set.insert x xs)"
  by (auto simp del: mem_def simp add: remove_def List_Set.insert_def)

lemma image_set:
  "image f (set xs) = set (map f xs)"
  by simp

lemma project_set:
  "project P (set xs) = set (filter P xs)"
  by (auto simp add: project_def)

text {* FIXME move the following to @{text Finite_Set.thy} *}

lemma fun_left_comm_idem_inf:
  "fun_left_comm_idem inf"
proof
qed (auto simp add: inf_left_commute)

lemma fun_left_comm_idem_sup:
  "fun_left_comm_idem sup"
proof
qed (auto simp add: sup_left_commute)

lemma inf_Inf_fold_inf:
  fixes A :: "'a::complete_lattice set"
  assumes "finite A"
  shows "inf B (Inf A) = fold inf B A"
proof -
  interpret fun_left_comm_idem inf by (fact fun_left_comm_idem_inf)
  from `finite A` show ?thesis by (induct A arbitrary: B)
    (simp_all add: top_def [symmetric] Inf_insert inf_commute fold_fun_comm)
qed

lemma sup_Sup_fold_sup:
  fixes A :: "'a::complete_lattice set"
  assumes "finite A"
  shows "sup B (Sup A) = fold sup B A"
proof -
  interpret fun_left_comm_idem sup by (fact fun_left_comm_idem_sup)
  from `finite A` show ?thesis by (induct A arbitrary: B)
    (simp_all add: bot_def [symmetric] Sup_insert sup_commute fold_fun_comm)
qed

lemma Inf_fold_inf:
  fixes A :: "'a::complete_lattice set"
  assumes "finite A"
  shows "Inf A = fold inf top A"
  using assms inf_Inf_fold_inf [of A top] by (simp add: inf_absorb2)

lemma Sup_fold_sup:
  fixes A :: "'a::complete_lattice set"
  assumes "finite A"
  shows "Sup A = fold sup bot A"
  using assms sup_Sup_fold_sup [of A bot] by (simp add: sup_absorb2)


subsection {* Functorial set operations *}

lemma union_set:
  "set xs \<union> A = foldl (\<lambda>A x. Set.insert x A) A xs"
proof -
  interpret fun_left_comm_idem Set.insert
    by (fact fun_left_comm_idem_insert)
  show ?thesis by (simp add: union_fold_insert fold_set)
qed

lemma minus_set:
  "A - set xs = foldl (\<lambda>A x. remove x A) A xs"
proof -
  interpret fun_left_comm_idem remove
    by (fact fun_left_comm_idem_remove)
  show ?thesis
    by (simp add: minus_fold_remove [of _ A] fold_set)
qed

lemma INFI_set_fold: -- "FIXME move to List.thy"
  "INFI (set xs) f = foldl (\<lambda>y x. inf (f x) y) top xs"
  unfolding INFI_def image_set Inf_set_fold foldl_map by (simp add: inf_commute)

lemma SUPR_set_fold: -- "FIXME move to List.thy"
  "SUPR (set xs) f = foldl (\<lambda>y x. sup (f x) y) bot xs"
  unfolding SUPR_def image_set Sup_set_fold foldl_map by (simp add: sup_commute)


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
  "A \<inter> B = project (\<lambda>x. x \<in> A) B"
  by (auto simp add: project_def)


hide (open) const insert

end