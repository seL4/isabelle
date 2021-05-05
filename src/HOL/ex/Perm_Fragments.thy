(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Fragments on permuations\<close>

theory Perm_Fragments
imports "HOL-Library.Dlist" "HOL-Combinatorics.Perm"
begin

text \<open>On cycles\<close>

context
  includes permutation_syntax
begin

lemma cycle_prod_list:
  "\<langle>a # as\<rangle> = prod_list (map (\<lambda>b. \<langle>a \<leftrightarrow> b\<rangle>) (rev as))"
  by (induct as) simp_all

lemma cycle_append [simp]:
  "\<langle>a # as @ bs\<rangle> = \<langle>a # bs\<rangle> * \<langle>a # as\<rangle>"
proof (induct as rule: cycle.induct)
  case (3 b c as)
  then have "\<langle>a # (b # as) @ bs\<rangle> = \<langle>a # bs\<rangle> * \<langle>a # b # as\<rangle>"
    by simp
  then have "\<langle>a # as @ bs\<rangle> * \<langle>a \<leftrightarrow> b\<rangle> =
    \<langle>a # bs\<rangle> * \<langle>a # as\<rangle> * \<langle>a \<leftrightarrow> b\<rangle>"
    by (simp add: ac_simps)
  then have "\<langle>a # as @ bs\<rangle> * \<langle>a \<leftrightarrow> b\<rangle> * \<langle>a \<leftrightarrow> b\<rangle> =
    \<langle>a # bs\<rangle> * \<langle>a # as\<rangle> * \<langle>a \<leftrightarrow> b\<rangle> * \<langle>a \<leftrightarrow> b\<rangle>"
    by simp
  then have "\<langle>a # as @ bs\<rangle> = \<langle>a # bs\<rangle> * \<langle>a # as\<rangle>"
    by (simp add: ac_simps)
  then show "\<langle>a # (b # c # as) @ bs\<rangle> =
    \<langle>a # bs\<rangle> * \<langle>a # b # c # as\<rangle>"
    by (simp add: ac_simps)
qed simp_all

lemma affected_cycle:
  "affected \<langle>as\<rangle> \<subseteq> set as"
proof (induct as rule: cycle.induct)
  case (3 a b as)
  from affected_times
  have "affected (\<langle>a # as\<rangle> * \<langle>a \<leftrightarrow> b\<rangle>)
    \<subseteq> affected \<langle>a # as\<rangle> \<union> affected \<langle>a \<leftrightarrow> b\<rangle>" .
  moreover from 3
  have "affected (\<langle>a # as\<rangle>) \<subseteq> insert a (set as)"
    by simp
  moreover
  have "affected \<langle>a \<leftrightarrow> b\<rangle> \<subseteq> {a, b}"
    by (cases "a = b") (simp_all add: affected_swap)
  ultimately have "affected (\<langle>a # as\<rangle> * \<langle>a \<leftrightarrow> b\<rangle>)
    \<subseteq> insert a (insert b (set as))"
    by blast
  then show ?case by auto
qed simp_all

lemma orbit_cycle_non_elem:
  assumes "a \<notin> set as"
  shows "orbit \<langle>as\<rangle> a = {a}"
  unfolding not_in_affected_iff_orbit_eq_singleton [symmetric]
  using assms affected_cycle [of as] by blast

lemma inverse_cycle:
  assumes "distinct as"
  shows "inverse \<langle>as\<rangle> = \<langle>rev as\<rangle>"
using assms proof (induct as rule: cycle.induct)
  case (3 a b as)
  then have *: "inverse \<langle>a # as\<rangle> = \<langle>rev (a # as)\<rangle>"
    and distinct: "distinct (a # b # as)"
    by simp_all
  show " inverse \<langle>a # b # as\<rangle> = \<langle>rev (a # b # as)\<rangle>"
  proof (cases as rule: rev_cases)
    case Nil with * show ?thesis
      by (simp add: swap_sym)
  next
    case (snoc cs c)
    with distinct have "distinct (a # b # cs @ [c])"
      by simp
    then have **: "\<langle>a \<leftrightarrow> b\<rangle> * \<langle>c \<leftrightarrow> a\<rangle> = \<langle>c \<leftrightarrow> a\<rangle> * \<langle>c \<leftrightarrow> b\<rangle>"
      by transfer (auto simp add: comp_def Fun.swap_def)
    with snoc * show ?thesis
      by (simp add: mult.assoc [symmetric])
  qed
qed simp_all

lemma order_cycle_non_elem:
  assumes "a \<notin> set as"
  shows "order \<langle>as\<rangle> a = 1"
proof -
  from assms have "orbit \<langle>as\<rangle> a = {a}" 
    by (rule orbit_cycle_non_elem)
  then have "card (orbit \<langle>as\<rangle> a) = card {a}"
    by simp
  then show ?thesis
    by simp
qed

lemma orbit_cycle_elem:
  assumes "distinct as" and "a \<in> set as"
  shows "orbit \<langle>as\<rangle> a = set as"
  oops \<comment> \<open>(we need rotation here\<close>

lemma order_cycle_elem:
  assumes "distinct as" and "a \<in> set as"
  shows "order \<langle>as\<rangle> a = length as"
  oops


text \<open>Adding fixpoints\<close>

definition fixate :: "'a \<Rightarrow> 'a perm \<Rightarrow> 'a perm"
where
  "fixate a f = (if a \<in> affected f then f * \<langle>inverse f \<langle>$\<rangle> a \<leftrightarrow> a\<rangle> else f)"

lemma affected_fixate_trivial:
  assumes "a \<notin> affected f"
  shows "affected (fixate a f) = affected f"
  using assms by (simp add: fixate_def)

lemma affected_fixate_binary_circle:
  assumes "order f a = 2"
  shows "affected (fixate a f) = affected f - {a, apply f a}" (is "?A = ?B")
proof (rule set_eqI)
  interpret bijection "apply f"
    by standard simp
  fix b
  from assms order_greater_eq_two_iff [of f a] have "a \<in> affected f"
    by simp
  moreover have "apply (f ^ 2) a = a"
    by (simp add: assms [symmetric])
  ultimately show "b \<in> ?A \<longleftrightarrow> b \<in> ?B"
    by (cases "b \<in> {a, apply (inverse f) a}")
      (auto simp add: in_affected power2_eq_square apply_inverse apply_times fixate_def)
qed

lemma affected_fixate_no_binary_circle:
  assumes "order f a > 2"
  shows "affected (fixate a f) = affected f - {a}" (is "?A = ?B")
proof (rule set_eqI)
  interpret bijection "apply f"
    by standard simp
  fix b
  from assms order_greater_eq_two_iff [of f a]
  have "a \<in> affected f"
    by simp
  moreover from assms
  have "apply f (apply f a) \<noteq> a"
    using apply_power_eq_iff [of f 2 a 0]
    by (simp add: power2_eq_square apply_times)
  ultimately show "b \<in> ?A \<longleftrightarrow> b \<in> ?B"
    by (cases "b \<in> {a, apply (inverse f) a}")
      (auto simp add: in_affected apply_inverse apply_times fixate_def)
qed
  
lemma affected_fixate:
  "affected (fixate a f) \<subseteq> affected f - {a}"
proof -
  have "a \<notin> affected f \<or> order f a = 2 \<or> order f a > 2"
    by (auto simp add: not_less dest: affected_order_greater_eq_two)
  then consider "a \<notin> affected f" | "order f a = 2" | "order f a > 2"
    by blast
  then show ?thesis apply cases
  using affected_fixate_trivial [of a f]
    affected_fixate_binary_circle [of f a]
    affected_fixate_no_binary_circle [of f a]
    by auto
qed

lemma orbit_fixate_self [simp]:
  "orbit (fixate a f) a = {a}"
proof -
  have "apply (f * inverse f) a = a"
    by simp
  then have "apply f (apply (inverse f) a) = a"
    by (simp only: apply_times comp_apply)
  then show ?thesis
    by (simp add: fixate_def not_in_affected_iff_orbit_eq_singleton [symmetric] in_affected apply_times)
qed

lemma order_fixate_self [simp]:
  "order (fixate a f) a = 1"
proof -
  have "card (orbit (fixate a f) a) = card {a}"
    by simp
  then show ?thesis
    by (simp only: card_orbit_eq) simp
qed

lemma 
  assumes "b \<notin> orbit f a"
  shows "orbit (fixate b f) a = orbit f a"
  oops

lemma
  assumes "b \<in> orbit f a" and "b \<noteq> a"
  shows "orbit (fixate b f) a = orbit f a - {b}"
  oops
    

text \<open>Distilling cycles from permutations\<close>

inductive_set orbits :: "'a perm \<Rightarrow> 'a set set" for f
where
  in_orbitsI: "a \<in> affected f \<Longrightarrow> orbit f a \<in> orbits f"

lemma orbits_unfold:
  "orbits f = orbit f ` affected f"
  by (auto intro: in_orbitsI elim: orbits.cases)

lemma in_orbit_affected:
  assumes "b \<in> orbit f a"
  assumes "a \<in> affected f"
  shows "b \<in> affected f"
proof (cases "a = b")
  case True with assms show ?thesis by simp
next
  case False with assms have "{a, b} \<subseteq> orbit f a"
    by auto
  also from assms have "orbit f a \<subseteq> affected f"
    by (blast intro!: orbit_subset_eq_affected)
  finally show ?thesis by simp
qed

lemma Union_orbits [simp]:
  "\<Union>(orbits f) = affected f"
  by (auto simp add: orbits.simps intro: in_orbitsI in_orbit_affected)

lemma finite_orbits [simp]:
  "finite (orbits f)"
  by (simp add: orbits_unfold)

lemma card_in_orbits:
  assumes "A \<in> orbits f"
  shows "card A \<ge> 2"
  using assms by cases
    (auto dest: affected_order_greater_eq_two)

lemma disjoint_orbits:
  assumes "A \<in> orbits f" and "B \<in> orbits f" and "A \<noteq> B"
  shows "A \<inter> B = {}"
  using \<open>A \<in> orbits f\<close> apply cases
  using \<open>B \<in> orbits f\<close> apply cases
  using \<open>A \<noteq> B\<close> apply (simp_all add: orbit_disjoint)
  done

definition trace :: "'a \<Rightarrow> 'a perm \<Rightarrow> 'a list"
where
  "trace a f = map (\<lambda>n. apply (f ^ n) a) [0..<order f a]"

lemma set_trace_eq [simp]:
  "set (trace a f) = orbit f a"
  by (auto simp add: trace_def orbit_unfold_image)

definition seeds :: "'a perm \<Rightarrow> 'a::linorder list"
where
  "seeds f = sorted_list_of_set (Min ` orbits f)"

definition cycles :: "'a perm \<Rightarrow> 'a::linorder list list"
where
  "cycles f = map (\<lambda>a. trace a f) (seeds f)"

end


text \<open>Misc\<close>

lemma (in comm_monoid_list_set) sorted_list_of_set:
  assumes "finite A"
  shows "list.F (map h (sorted_list_of_set A)) = set.F h A"
proof -
  from distinct_sorted_list_of_set
  have "set.F h (set (sorted_list_of_set A)) = list.F (map h (sorted_list_of_set A))"
    by (rule distinct_set_conv_list)
  with \<open>finite A\<close> show ?thesis
    by (simp)
qed

primrec subtract :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "subtract [] ys = ys"
| "subtract (x # xs) ys = subtract xs (removeAll x ys)"

lemma length_subtract_less_eq [simp]:
  "length (subtract xs ys) \<le> length ys"
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then have "length (subtract xs (removeAll x ys)) \<le> length (removeAll x ys)" .
  also have "length (removeAll x ys) \<le> length ys"
    by simp
  finally show ?case
    by simp
qed

end
