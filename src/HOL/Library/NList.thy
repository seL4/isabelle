(*  Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

section \<open>Fixed Length Lists\<close>

theory NList
imports Main
begin

definition nlists :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a list set"
  where "nlists n A = {xs. size xs = n \<and> set xs \<subseteq> A}"

lemma nlistsI: "\<lbrakk> size xs = n; set xs \<subseteq> A \<rbrakk> \<Longrightarrow> xs \<in> nlists n A"
  by (simp add: nlists_def)

text \<open>These [simp] attributes are double-edged.
 Many proofs in Jinja rely on it but they can degrade performance.\<close>

lemma nlistsE_length [simp]: "xs \<in> nlists n A \<Longrightarrow> size xs = n"
  by (simp add: nlists_def)

lemma in_nlists_UNIV: "xs \<in> nlists k UNIV \<longleftrightarrow> length xs = k"
unfolding nlists_def by(auto)

lemma less_lengthI: "\<lbrakk> xs \<in> nlists n A; p < n \<rbrakk> \<Longrightarrow> p < size xs"
by (simp)

lemma nlistsE_set[simp]: "xs \<in> nlists n A \<Longrightarrow> set xs \<subseteq> A"
unfolding nlists_def by (simp)

lemma nlists_mono:
assumes "A \<subseteq> B" shows "nlists n A \<subseteq> nlists n B"
proof
  fix xs assume "xs \<in> nlists n A"
  then obtain size: "size xs = n" and inA: "set xs \<subseteq> A" by (simp)
  with assms have "set xs \<subseteq> B" by simp
  with size show "xs \<in> nlists n B" by(clarsimp intro!: nlistsI)
qed

lemma nlists_singleton: "nlists n {a} = {replicate n a}"
unfolding nlists_def by(auto simp: replicate_length_same dest!: subset_singletonD)

lemma nlists_n_0 [simp]: "nlists 0 A = {[]}"
unfolding nlists_def by (auto)

lemma in_nlists_Suc_iff: "(xs \<in> nlists (Suc n) A) = (\<exists>y\<in>A. \<exists>ys \<in> nlists n A. xs = y#ys)"
unfolding nlists_def by (cases "xs") auto

lemma Cons_in_nlists_Suc [iff]: "(x#xs \<in> nlists (Suc n) A) \<longleftrightarrow> (x\<in>A \<and> xs \<in> nlists n A)"
unfolding nlists_def by (auto)

lemma nlists_Suc: "nlists (Suc n) A = (\<Union>a\<in>A. (#) a ` nlists n A)"
by(auto simp: set_eq_iff image_iff in_nlists_Suc_iff)

lemma nlists_not_empty: "A\<noteq>{} \<Longrightarrow> \<exists>xs. xs \<in> nlists n A"
by (induct "n") (auto simp: in_nlists_Suc_iff)

lemma nlistsE_nth_in: "\<lbrakk> xs \<in> nlists n A; i < n \<rbrakk> \<Longrightarrow> xs!i \<in> A"
unfolding nlists_def by (auto)

lemma nlists_Cons_Suc [elim!]:
  "l#xs \<in> nlists n A \<Longrightarrow> (\<And>n'. n = Suc n' \<Longrightarrow> l \<in> A \<Longrightarrow> xs \<in> nlists n' A \<Longrightarrow> P) \<Longrightarrow> P"
unfolding nlists_def by (auto)

lemma nlists_appendE [elim!]:
  "a@b \<in> nlists n A \<Longrightarrow> (\<And>n1 n2. n=n1+n2 \<Longrightarrow> a \<in> nlists n1 A \<Longrightarrow> b \<in> nlists n2 A \<Longrightarrow> P) \<Longrightarrow> P"
proof -
  have "\<And>n. a@b \<in> nlists n A \<Longrightarrow> \<exists>n1 n2. n=n1+n2 \<and> a \<in> nlists n1 A \<and> b \<in> nlists n2 A"
    (is "\<And>n. ?list a n \<Longrightarrow> \<exists>n1 n2. ?P a n n1 n2")
  proof (induct a)
    fix n assume "?list [] n"
    hence "?P [] n 0 n" by simp
    thus "\<exists>n1 n2. ?P [] n n1 n2" by fast
  next
    fix n l ls
    assume "?list (l#ls) n"
    then obtain n' where n: "n = Suc n'" "l \<in> A" and n': "ls@b \<in> nlists n' A" by fastforce
    assume "\<And>n. ls @ b \<in> nlists n A \<Longrightarrow> \<exists>n1 n2. n = n1 + n2 \<and> ls \<in> nlists n1 A \<and> b \<in> nlists n2 A"
    from this and n' have "\<exists>n1 n2. n' = n1 + n2 \<and> ls \<in> nlists n1 A \<and> b \<in> nlists n2 A" .
    then obtain n1 n2 where "n' = n1 + n2" "ls \<in> nlists n1 A" "b \<in> nlists n2 A" by fast
    with n have "?P (l#ls) n (n1+1) n2" by simp
    thus "\<exists>n1 n2. ?P (l#ls) n n1 n2" by fastforce
  qed
  moreover assume "a@b \<in> nlists n A" "\<And>n1 n2. n=n1+n2 \<Longrightarrow> a \<in> nlists n1 A \<Longrightarrow> b \<in> nlists n2 A \<Longrightarrow> P"
  ultimately show ?thesis by blast
qed


lemma nlists_update_in_list [simp, intro!]:
  "\<lbrakk> xs \<in> nlists n A; x\<in>A \<rbrakk> \<Longrightarrow> xs[i := x] \<in> nlists n A"
  by (metis length_list_update nlistsE_length nlistsE_set nlistsI set_update_subsetI)

lemma nlists_appendI [intro?]:
  "\<lbrakk> a \<in> nlists n A; b \<in> nlists m A \<rbrakk> \<Longrightarrow> a @ b \<in> nlists (n+m) A"
unfolding nlists_def by (auto)

lemma nlists_append:
  "xs @ ys \<in> nlists k A \<longleftrightarrow>
   k = length(xs @ ys) \<and> xs \<in> nlists (length xs) A \<and> ys \<in> nlists (length ys) A"
unfolding nlists_def by (auto)

lemma nlists_map [simp]: "(map f xs \<in> nlists (size xs) A) = (f ` set xs \<subseteq> A)"
unfolding nlists_def by (auto)

lemma nlists_replicateI [intro]: "x \<in> A \<Longrightarrow> replicate n x \<in> nlists n A"
 by (induct n) auto

text \<open>Link to an executable version on lists in List.\<close>
lemma nlists_set[code]: "nlists n (set xs) = set(List.n_lists n xs)"
by (metis nlists_def set_n_lists)

end
