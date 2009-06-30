
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

lemma remove_set:
  "remove x (set xs) = set (remove_all x xs)"
  by (auto simp add: remove_def remove_all_def)

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

lemma Inter_set:
  "Inter (set (A # As)) = foldl (op \<inter>) A As"
proof -
  have "finite (set (A # As))" by simp
  moreover have "fold (op \<inter>) UNIV (set (A # As)) = foldl (\<lambda>y x. x \<inter> y) UNIV (A # As)"
    by (rule fun_left_comm_idem.fold_set, unfold_locales, auto)
  ultimately have "Inter (set (A # As)) = foldl (op \<inter>) UNIV (A # As)"
    by (simp only: Inter_fold_inter Int_commute)
  then show ?thesis by simp
qed

lemma Union_set:
  "Union (set As) = foldl (op \<union>) {} As"
proof -
  have "fold (op \<union>) {} (set As) = foldl (\<lambda>y x. x \<union> y) {} As"
    by (rule fun_left_comm_idem.fold_set, unfold_locales, auto)
  then show ?thesis
    by (simp only: Union_fold_union finite_set Un_commute)
qed

lemma INTER_set:
  "INTER (set (A # As)) f = foldl (\<lambda>B A. f A \<inter> B) (f A) As"
proof -
  have "finite (set (A # As))" by simp
  moreover have "fold (\<lambda>A. op \<inter> (f A)) UNIV (set (A # As)) = foldl (\<lambda>B A. f A \<inter> B) UNIV (A # As)"
    by (rule fun_left_comm_idem.fold_set, unfold_locales, auto)
  ultimately have "INTER (set (A # As)) f = foldl (\<lambda>B A. f A \<inter> B) UNIV (A # As)"
    by (simp only: INTER_fold_inter) 
  then show ?thesis by simp
qed

lemma UNION_set:
  "UNION (set As) f = foldl (\<lambda>B A. f A \<union> B) {} As"
proof -
  have "fold (\<lambda>A. op \<union> (f A)) {} (set As) = foldl (\<lambda>B A. f A \<union> B) {} As"
    by (rule fun_left_comm_idem.fold_set, unfold_locales, auto)
  then show ?thesis
    by (simp only: UNION_fold_union finite_set)
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


hide (open) const insert

end