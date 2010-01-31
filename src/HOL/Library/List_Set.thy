
(* Author: Florian Haftmann, TU Muenchen *)

header {* Relating (finite) sets and lists *}

theory List_Set
imports Main
begin

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

lemma insert_set_compl:
  "insert x (- set xs) = - set (removeAll x xs)"
  by auto

lemma remove_set_compl:
  "remove x (- set xs) = - set (List.insert x xs)"
  by (auto simp del: mem_def simp add: remove_def List.insert_def)

lemma image_set:
  "image f (set xs) = set (map f xs)"
  by simp

lemma project_set:
  "project P (set xs) = set (filter P xs)"
  by (auto simp add: project_def)


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

end