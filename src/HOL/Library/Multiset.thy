(*  Title:      HOL/Library/Multiset.thy
    Author:     Tobias Nipkow, Markus Wenzel, Lawrence C Paulson, Norbert Voelker
    Author:     Andrei Popescu, TU Muenchen
*)

header {* (Finite) multisets *}

theory Multiset
imports Main
begin

subsection {* The type of multisets *}

definition "multiset = {f :: 'a => nat. finite {x. f x > 0}}"

typedef 'a multiset = "multiset :: ('a => nat) set"
  morphisms count Abs_multiset
  unfolding multiset_def
proof
  show "(\<lambda>x. 0::nat) \<in> {f. finite {x. f x > 0}}" by simp
qed

setup_lifting type_definition_multiset

abbreviation Melem :: "'a => 'a multiset => bool"  ("(_/ :# _)" [50, 51] 50) where
  "a :# M == 0 < count M a"

notation (xsymbols)
  Melem (infix "\<in>#" 50)

lemma multiset_eq_iff:
  "M = N \<longleftrightarrow> (\<forall>a. count M a = count N a)"
  by (simp only: count_inject [symmetric] fun_eq_iff)

lemma multiset_eqI:
  "(\<And>x. count A x = count B x) \<Longrightarrow> A = B"
  using multiset_eq_iff by auto

text {*
 \medskip Preservation of the representing set @{term multiset}.
*}

lemma const0_in_multiset:
  "(\<lambda>a. 0) \<in> multiset"
  by (simp add: multiset_def)

lemma only1_in_multiset:
  "(\<lambda>b. if b = a then n else 0) \<in> multiset"
  by (simp add: multiset_def)

lemma union_preserves_multiset:
  "M \<in> multiset \<Longrightarrow> N \<in> multiset \<Longrightarrow> (\<lambda>a. M a + N a) \<in> multiset"
  by (simp add: multiset_def)

lemma diff_preserves_multiset:
  assumes "M \<in> multiset"
  shows "(\<lambda>a. M a - N a) \<in> multiset"
proof -
  have "{x. N x < M x} \<subseteq> {x. 0 < M x}"
    by auto
  with assms show ?thesis
    by (auto simp add: multiset_def intro: finite_subset)
qed

lemma filter_preserves_multiset:
  assumes "M \<in> multiset"
  shows "(\<lambda>x. if P x then M x else 0) \<in> multiset"
proof -
  have "{x. (P x \<longrightarrow> 0 < M x) \<and> P x} \<subseteq> {x. 0 < M x}"
    by auto
  with assms show ?thesis
    by (auto simp add: multiset_def intro: finite_subset)
qed

lemmas in_multiset = const0_in_multiset only1_in_multiset
  union_preserves_multiset diff_preserves_multiset filter_preserves_multiset


subsection {* Representing multisets *}

text {* Multiset enumeration *}

instantiation multiset :: (type) cancel_comm_monoid_add
begin

lift_definition zero_multiset :: "'a multiset" is "\<lambda>a. 0"
by (rule const0_in_multiset)

abbreviation Mempty :: "'a multiset" ("{#}") where
  "Mempty \<equiv> 0"

lift_definition plus_multiset :: "'a multiset => 'a multiset => 'a multiset" is "\<lambda>M N. (\<lambda>a. M a + N a)"
by (rule union_preserves_multiset)

instance
by default (transfer, simp add: fun_eq_iff)+

end

lift_definition single :: "'a => 'a multiset" is "\<lambda>a b. if b = a then 1 else 0"
by (rule only1_in_multiset)

syntax
  "_multiset" :: "args => 'a multiset"    ("{#(_)#}")
translations
  "{#x, xs#}" == "{#x#} + {#xs#}"
  "{#x#}" == "CONST single x"

lemma count_empty [simp]: "count {#} a = 0"
  by (simp add: zero_multiset.rep_eq)

lemma count_single [simp]: "count {#b#} a = (if b = a then 1 else 0)"
  by (simp add: single.rep_eq)


subsection {* Basic operations *}

subsubsection {* Union *}

lemma count_union [simp]: "count (M + N) a = count M a + count N a"
  by (simp add: plus_multiset.rep_eq)


subsubsection {* Difference *}

instantiation multiset :: (type) comm_monoid_diff
begin

lift_definition minus_multiset :: "'a multiset => 'a multiset => 'a multiset" is "\<lambda> M N. \<lambda>a. M a - N a"
by (rule diff_preserves_multiset)

instance
by default (transfer, simp add: fun_eq_iff)+

end

lemma count_diff [simp]: "count (M - N) a = count M a - count N a"
  by (simp add: minus_multiset.rep_eq)

lemma diff_empty [simp]: "M - {#} = M \<and> {#} - M = {#}"
  by rule (fact Groups.diff_zero, fact Groups.zero_diff)

lemma diff_cancel[simp]: "A - A = {#}"
  by (fact Groups.diff_cancel)

lemma diff_union_cancelR [simp]: "M + N - N = (M::'a multiset)"
  by (fact add_diff_cancel_right')

lemma diff_union_cancelL [simp]: "N + M - N = (M::'a multiset)"
  by (fact add_diff_cancel_left')

lemma diff_right_commute:
  "(M::'a multiset) - N - Q = M - Q - N"
  by (fact diff_right_commute)

lemma diff_add:
  "(M::'a multiset) - (N + Q) = M - N - Q"
  by (rule sym) (fact diff_diff_add)

lemma insert_DiffM:
  "x \<in># M \<Longrightarrow> {#x#} + (M - {#x#}) = M"
  by (clarsimp simp: multiset_eq_iff)

lemma insert_DiffM2 [simp]:
  "x \<in># M \<Longrightarrow> M - {#x#} + {#x#} = M"
  by (clarsimp simp: multiset_eq_iff)

lemma diff_union_swap:
  "a \<noteq> b \<Longrightarrow> M - {#a#} + {#b#} = M + {#b#} - {#a#}"
  by (auto simp add: multiset_eq_iff)

lemma diff_union_single_conv:
  "a \<in># J \<Longrightarrow> I + J - {#a#} = I + (J - {#a#})"
  by (simp add: multiset_eq_iff)


subsubsection {* Equality of multisets *}

lemma single_not_empty [simp]: "{#a#} \<noteq> {#} \<and> {#} \<noteq> {#a#}"
  by (simp add: multiset_eq_iff)

lemma single_eq_single [simp]: "{#a#} = {#b#} \<longleftrightarrow> a = b"
  by (auto simp add: multiset_eq_iff)

lemma union_eq_empty [iff]: "M + N = {#} \<longleftrightarrow> M = {#} \<and> N = {#}"
  by (auto simp add: multiset_eq_iff)

lemma empty_eq_union [iff]: "{#} = M + N \<longleftrightarrow> M = {#} \<and> N = {#}"
  by (auto simp add: multiset_eq_iff)

lemma multi_self_add_other_not_self [simp]: "M = M + {#x#} \<longleftrightarrow> False"
  by (auto simp add: multiset_eq_iff)

lemma diff_single_trivial:
  "\<not> x \<in># M \<Longrightarrow> M - {#x#} = M"
  by (auto simp add: multiset_eq_iff)

lemma diff_single_eq_union:
  "x \<in># M \<Longrightarrow> M - {#x#} = N \<longleftrightarrow> M = N + {#x#}"
  by auto

lemma union_single_eq_diff:
  "M + {#x#} = N \<Longrightarrow> M = N - {#x#}"
  by (auto dest: sym)

lemma union_single_eq_member:
  "M + {#x#} = N \<Longrightarrow> x \<in># N"
  by auto

lemma union_is_single:
  "M + N = {#a#} \<longleftrightarrow> M = {#a#} \<and> N={#} \<or> M = {#} \<and> N = {#a#}" (is "?lhs = ?rhs")
proof
  assume ?rhs then show ?lhs by auto
next
  assume ?lhs then show ?rhs
    by (simp add: multiset_eq_iff split:if_splits) (metis add_is_1)
qed

lemma single_is_union:
  "{#a#} = M + N \<longleftrightarrow> {#a#} = M \<and> N = {#} \<or> M = {#} \<and> {#a#} = N"
  by (auto simp add: eq_commute [of "{#a#}" "M + N"] union_is_single)

lemma add_eq_conv_diff:
  "M + {#a#} = N + {#b#} \<longleftrightarrow> M = N \<and> a = b \<or> M = N - {#a#} + {#b#} \<and> N = M - {#b#} + {#a#}"  (is "?lhs = ?rhs")
(* shorter: by (simp add: multiset_eq_iff) fastforce *)
proof
  assume ?rhs then show ?lhs
  by (auto simp add: add.assoc add.commute [of "{#b#}"])
    (drule sym, simp add: add.assoc [symmetric])
next
  assume ?lhs
  show ?rhs
  proof (cases "a = b")
    case True with `?lhs` show ?thesis by simp
  next
    case False
    from `?lhs` have "a \<in># N + {#b#}" by (rule union_single_eq_member)
    with False have "a \<in># N" by auto
    moreover from `?lhs` have "M = N + {#b#} - {#a#}" by (rule union_single_eq_diff)
    moreover note False
    ultimately show ?thesis by (auto simp add: diff_right_commute [of _ "{#a#}"] diff_union_swap)
  qed
qed

lemma insert_noteq_member:
  assumes BC: "B + {#b#} = C + {#c#}"
   and bnotc: "b \<noteq> c"
  shows "c \<in># B"
proof -
  have "c \<in># C + {#c#}" by simp
  have nc: "\<not> c \<in># {#b#}" using bnotc by simp
  then have "c \<in># B + {#b#}" using BC by simp
  then show "c \<in># B" using nc by simp
qed

lemma add_eq_conv_ex:
  "(M + {#a#} = N + {#b#}) =
    (M = N \<and> a = b \<or> (\<exists>K. M = K + {#b#} \<and> N = K + {#a#}))"
  by (auto simp add: add_eq_conv_diff)

lemma multi_member_split:
  "x \<in># M \<Longrightarrow> \<exists>A. M = A + {#x#}"
  by (rule_tac x = "M - {#x#}" in exI, simp)

lemma multiset_add_sub_el_shuffle:
  assumes "c \<in># B" and "b \<noteq> c"
  shows "B - {#c#} + {#b#} = B + {#b#} - {#c#}"
proof -
  from `c \<in># B` obtain A where B: "B = A + {#c#}"
    by (blast dest: multi_member_split)
  have "A + {#b#} = A + {#b#} + {#c#} - {#c#}" by simp
  then have "A + {#b#} = A + {#c#} + {#b#} - {#c#}"
    by (simp add: ac_simps)
  then show ?thesis using B by simp
qed


subsubsection {* Pointwise ordering induced by count *}

instantiation multiset :: (type) ordered_ab_semigroup_add_imp_le
begin

lift_definition less_eq_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" is "\<lambda> A B. (\<forall>a. A a \<le> B a)" .

lemmas mset_le_def = less_eq_multiset_def

definition less_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  mset_less_def: "(A::'a multiset) < B \<longleftrightarrow> A \<le> B \<and> A \<noteq> B"

instance
  by default (auto simp add: mset_le_def mset_less_def multiset_eq_iff intro: order_trans antisym)

end

lemma mset_less_eqI:
  "(\<And>x. count A x \<le> count B x) \<Longrightarrow> A \<le> B"
  by (simp add: mset_le_def)

lemma mset_le_exists_conv:
  "(A::'a multiset) \<le> B \<longleftrightarrow> (\<exists>C. B = A + C)"
apply (unfold mset_le_def, rule iffI, rule_tac x = "B - A" in exI)
apply (auto intro: multiset_eq_iff [THEN iffD2])
done

instance multiset :: (type) ordered_cancel_comm_monoid_diff
  by default (simp, fact mset_le_exists_conv)

lemma mset_le_mono_add_right_cancel [simp]:
  "(A::'a multiset) + C \<le> B + C \<longleftrightarrow> A \<le> B"
  by (fact add_le_cancel_right)

lemma mset_le_mono_add_left_cancel [simp]:
  "C + (A::'a multiset) \<le> C + B \<longleftrightarrow> A \<le> B"
  by (fact add_le_cancel_left)

lemma mset_le_mono_add:
  "(A::'a multiset) \<le> B \<Longrightarrow> C \<le> D \<Longrightarrow> A + C \<le> B + D"
  by (fact add_mono)

lemma mset_le_add_left [simp]:
  "(A::'a multiset) \<le> A + B"
  unfolding mset_le_def by auto

lemma mset_le_add_right [simp]:
  "B \<le> (A::'a multiset) + B"
  unfolding mset_le_def by auto

lemma mset_le_single:
  "a :# B \<Longrightarrow> {#a#} \<le> B"
  by (simp add: mset_le_def)

lemma multiset_diff_union_assoc:
  "C \<le> B \<Longrightarrow> (A::'a multiset) + B - C = A + (B - C)"
  by (simp add: multiset_eq_iff mset_le_def)

lemma mset_le_multiset_union_diff_commute:
  "B \<le> A \<Longrightarrow> (A::'a multiset) - B + C = A + C - B"
by (simp add: multiset_eq_iff mset_le_def)

lemma diff_le_self[simp]: "(M::'a multiset) - N \<le> M"
by(simp add: mset_le_def)

lemma mset_lessD: "A < B \<Longrightarrow> x \<in># A \<Longrightarrow> x \<in># B"
apply (clarsimp simp: mset_le_def mset_less_def)
apply (erule_tac x=x in allE)
apply auto
done

lemma mset_leD: "A \<le> B \<Longrightarrow> x \<in># A \<Longrightarrow> x \<in># B"
apply (clarsimp simp: mset_le_def mset_less_def)
apply (erule_tac x = x in allE)
apply auto
done

lemma mset_less_insertD: "(A + {#x#} < B) \<Longrightarrow> (x \<in># B \<and> A < B)"
apply (rule conjI)
 apply (simp add: mset_lessD)
apply (clarsimp simp: mset_le_def mset_less_def)
apply safe
 apply (erule_tac x = a in allE)
 apply (auto split: split_if_asm)
done

lemma mset_le_insertD: "(A + {#x#} \<le> B) \<Longrightarrow> (x \<in># B \<and> A \<le> B)"
apply (rule conjI)
 apply (simp add: mset_leD)
apply (force simp: mset_le_def mset_less_def split: split_if_asm)
done

lemma mset_less_of_empty[simp]: "A < {#} \<longleftrightarrow> False"
  by (auto simp add: mset_less_def mset_le_def multiset_eq_iff)

lemma empty_le[simp]: "{#} \<le> A"
  unfolding mset_le_exists_conv by auto

lemma le_empty[simp]: "(M \<le> {#}) = (M = {#})"
  unfolding mset_le_exists_conv by auto

lemma multi_psub_of_add_self[simp]: "A < A + {#x#}"
  by (auto simp: mset_le_def mset_less_def)

lemma multi_psub_self[simp]: "(A::'a multiset) < A = False"
  by simp

lemma mset_less_add_bothsides:
  "T + {#x#} < S + {#x#} \<Longrightarrow> T < S"
  by (fact add_less_imp_less_right)

lemma mset_less_empty_nonempty:
  "{#} < S \<longleftrightarrow> S \<noteq> {#}"
  by (auto simp: mset_le_def mset_less_def)

lemma mset_less_diff_self:
  "c \<in># B \<Longrightarrow> B - {#c#} < B"
  by (auto simp: mset_le_def mset_less_def multiset_eq_iff)


subsubsection {* Intersection *}

instantiation multiset :: (type) semilattice_inf
begin

definition inf_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" where
  multiset_inter_def: "inf_multiset A B = A - (A - B)"

instance
proof -
  have aux: "\<And>m n q :: nat. m \<le> n \<Longrightarrow> m \<le> q \<Longrightarrow> m \<le> n - (n - q)" by arith
  show "OFCLASS('a multiset, semilattice_inf_class)"
    by default (auto simp add: multiset_inter_def mset_le_def aux)
qed

end

abbreviation multiset_inter :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" (infixl "#\<inter>" 70) where
  "multiset_inter \<equiv> inf"

lemma multiset_inter_count [simp]:
  "count (A #\<inter> B) x = min (count A x) (count B x)"
  by (simp add: multiset_inter_def)

lemma multiset_inter_single: "a \<noteq> b \<Longrightarrow> {#a#} #\<inter> {#b#} = {#}"
  by (rule multiset_eqI) auto

lemma multiset_union_diff_commute:
  assumes "B #\<inter> C = {#}"
  shows "A + B - C = A - C + B"
proof (rule multiset_eqI)
  fix x
  from assms have "min (count B x) (count C x) = 0"
    by (auto simp add: multiset_eq_iff)
  then have "count B x = 0 \<or> count C x = 0"
    by auto
  then show "count (A + B - C) x = count (A - C + B) x"
    by auto
qed

lemma empty_inter [simp]:
  "{#} #\<inter> M = {#}"
  by (simp add: multiset_eq_iff)

lemma inter_empty [simp]:
  "M #\<inter> {#} = {#}"
  by (simp add: multiset_eq_iff)

lemma inter_add_left1:
  "\<not> x \<in># N \<Longrightarrow> (M + {#x#}) #\<inter> N = M #\<inter> N"
  by (simp add: multiset_eq_iff)

lemma inter_add_left2:
  "x \<in># N \<Longrightarrow> (M + {#x#}) #\<inter> N = (M #\<inter> (N - {#x#})) + {#x#}"
  by (simp add: multiset_eq_iff)

lemma inter_add_right1:
  "\<not> x \<in># N \<Longrightarrow> N #\<inter> (M + {#x#}) = N #\<inter> M"
  by (simp add: multiset_eq_iff)

lemma inter_add_right2:
  "x \<in># N \<Longrightarrow> N #\<inter> (M + {#x#}) = ((N - {#x#}) #\<inter> M) + {#x#}"
  by (simp add: multiset_eq_iff)


subsubsection {* Bounded union *}

instantiation multiset :: (type) semilattice_sup
begin

definition sup_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" where
  "sup_multiset A B = A + (B - A)"

instance
proof -
  have aux: "\<And>m n q :: nat. m \<le> n \<Longrightarrow> q \<le> n \<Longrightarrow> m + (q - m) \<le> n" by arith
  show "OFCLASS('a multiset, semilattice_sup_class)"
    by default (auto simp add: sup_multiset_def mset_le_def aux)
qed

end

abbreviation sup_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" (infixl "#\<union>" 70) where
  "sup_multiset \<equiv> sup"

lemma sup_multiset_count [simp]:
  "count (A #\<union> B) x = max (count A x) (count B x)"
  by (simp add: sup_multiset_def)

lemma empty_sup [simp]:
  "{#} #\<union> M = M"
  by (simp add: multiset_eq_iff)

lemma sup_empty [simp]:
  "M #\<union> {#} = M"
  by (simp add: multiset_eq_iff)

lemma sup_add_left1:
  "\<not> x \<in># N \<Longrightarrow> (M + {#x#}) #\<union> N = (M #\<union> N) + {#x#}"
  by (simp add: multiset_eq_iff)

lemma sup_add_left2:
  "x \<in># N \<Longrightarrow> (M + {#x#}) #\<union> N = (M #\<union> (N - {#x#})) + {#x#}"
  by (simp add: multiset_eq_iff)

lemma sup_add_right1:
  "\<not> x \<in># N \<Longrightarrow> N #\<union> (M + {#x#}) = (N #\<union> M) + {#x#}"
  by (simp add: multiset_eq_iff)

lemma sup_add_right2:
  "x \<in># N \<Longrightarrow> N #\<union> (M + {#x#}) = ((N - {#x#}) #\<union> M) + {#x#}"
  by (simp add: multiset_eq_iff)


subsubsection {* Filter (with comprehension syntax) *}

text {* Multiset comprehension *}

lift_definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" is "\<lambda>P M. \<lambda>x. if P x then M x else 0"
by (rule filter_preserves_multiset)

hide_const (open) filter

lemma count_filter [simp]:
  "count (Multiset.filter P M) a = (if P a then count M a else 0)"
  by (simp add: filter.rep_eq)

lemma filter_empty [simp]:
  "Multiset.filter P {#} = {#}"
  by (rule multiset_eqI) simp

lemma filter_single [simp]:
  "Multiset.filter P {#x#} = (if P x then {#x#} else {#})"
  by (rule multiset_eqI) simp

lemma filter_union [simp]:
  "Multiset.filter P (M + N) = Multiset.filter P M + Multiset.filter P N"
  by (rule multiset_eqI) simp

lemma filter_diff [simp]:
  "Multiset.filter P (M - N) = Multiset.filter P M - Multiset.filter P N"
  by (rule multiset_eqI) simp

lemma filter_inter [simp]:
  "Multiset.filter P (M #\<inter> N) = Multiset.filter P M #\<inter> Multiset.filter P N"
  by (rule multiset_eqI) simp

lemma multiset_filter_subset[simp]: "Multiset.filter f M \<le> M"
  unfolding less_eq_multiset.rep_eq by auto

lemma multiset_filter_mono: assumes "A \<le> B"
  shows "Multiset.filter f A \<le> Multiset.filter f B"
proof -
  from assms[unfolded mset_le_exists_conv]
  obtain C where B: "B = A + C" by auto
  show ?thesis unfolding B by auto
qed

syntax
  "_MCollect" :: "pttrn \<Rightarrow> 'a multiset \<Rightarrow> bool \<Rightarrow> 'a multiset"    ("(1{# _ :# _./ _#})")
syntax (xsymbol)
  "_MCollect" :: "pttrn \<Rightarrow> 'a multiset \<Rightarrow> bool \<Rightarrow> 'a multiset"    ("(1{# _ \<in># _./ _#})")
translations
  "{#x \<in># M. P#}" == "CONST Multiset.filter (\<lambda>x. P) M"


subsubsection {* Set of elements *}

definition set_of :: "'a multiset => 'a set" where
  "set_of M = {x. x :# M}"

lemma set_of_empty [simp]: "set_of {#} = {}"
by (simp add: set_of_def)

lemma set_of_single [simp]: "set_of {#b#} = {b}"
by (simp add: set_of_def)

lemma set_of_union [simp]: "set_of (M + N) = set_of M \<union> set_of N"
by (auto simp add: set_of_def)

lemma set_of_eq_empty_iff [simp]: "(set_of M = {}) = (M = {#})"
by (auto simp add: set_of_def multiset_eq_iff)

lemma mem_set_of_iff [simp]: "(x \<in> set_of M) = (x :# M)"
by (auto simp add: set_of_def)

lemma set_of_filter [simp]: "set_of {# x:#M. P x #} = set_of M \<inter> {x. P x}"
by (auto simp add: set_of_def)

lemma finite_set_of [iff]: "finite (set_of M)"
  using count [of M] by (simp add: multiset_def set_of_def)

lemma finite_Collect_mem [iff]: "finite {x. x :# M}"
  unfolding set_of_def[symmetric] by simp

lemma set_of_mono: "A \<le> B \<Longrightarrow> set_of A \<subseteq> set_of B"
  by (metis mset_leD subsetI mem_set_of_iff)

subsubsection {* Size *}

definition wcount where "wcount f M = (\<lambda>x. count M x * Suc (f x))"

lemma wcount_union: "wcount f (M + N) a = wcount f M a + wcount f N a"
  by (auto simp: wcount_def add_mult_distrib)

definition size_multiset :: "('a \<Rightarrow> nat) \<Rightarrow> 'a multiset \<Rightarrow> nat" where
  "size_multiset f M = setsum (wcount f M) (set_of M)"

lemmas size_multiset_eq = size_multiset_def[unfolded wcount_def]

instantiation multiset :: (type) size begin
definition size_multiset where
  size_multiset_overloaded_def: "size_multiset = Multiset.size_multiset (\<lambda>_. 0)"
instance ..
end

lemmas size_multiset_overloaded_eq =
  size_multiset_overloaded_def[THEN fun_cong, unfolded size_multiset_eq, simplified]

lemma size_multiset_empty [simp]: "size_multiset f {#} = 0"
by (simp add: size_multiset_def)

lemma size_empty [simp]: "size {#} = 0"
by (simp add: size_multiset_overloaded_def)

lemma size_multiset_single [simp]: "size_multiset f {#b#} = Suc (f b)"
by (simp add: size_multiset_eq)

lemma size_single [simp]: "size {#b#} = 1"
by (simp add: size_multiset_overloaded_def)

lemma setsum_wcount_Int:
  "finite A \<Longrightarrow> setsum (wcount f N) (A \<inter> set_of N) = setsum (wcount f N) A"
apply (induct rule: finite_induct)
 apply simp
apply (simp add: Int_insert_left set_of_def wcount_def)
done

lemma size_multiset_union [simp]:
  "size_multiset f (M + N::'a multiset) = size_multiset f M + size_multiset f N"
apply (simp add: size_multiset_def setsum_Un_nat setsum.distrib setsum_wcount_Int wcount_union)
apply (subst Int_commute)
apply (simp add: setsum_wcount_Int)
done

lemma size_union [simp]: "size (M + N::'a multiset) = size M + size N"
by (auto simp add: size_multiset_overloaded_def)

lemma size_multiset_eq_0_iff_empty [iff]: "(size_multiset f M = 0) = (M = {#})"
by (auto simp add: size_multiset_eq multiset_eq_iff)

lemma size_eq_0_iff_empty [iff]: "(size M = 0) = (M = {#})"
by (auto simp add: size_multiset_overloaded_def)

lemma nonempty_has_size: "(S \<noteq> {#}) = (0 < size S)"
by (metis gr0I gr_implies_not0 size_empty size_eq_0_iff_empty)

lemma size_eq_Suc_imp_elem: "size M = Suc n ==> \<exists>a. a :# M"
apply (unfold size_multiset_overloaded_eq)
apply (drule setsum_SucD)
apply auto
done

lemma size_eq_Suc_imp_eq_union:
  assumes "size M = Suc n"
  shows "\<exists>a N. M = N + {#a#}"
proof -
  from assms obtain a where "a \<in># M"
    by (erule size_eq_Suc_imp_elem [THEN exE])
  then have "M = M - {#a#} + {#a#}" by simp
  then show ?thesis by blast
qed


subsection {* Induction and case splits *}

theorem multiset_induct [case_names empty add, induct type: multiset]:
  assumes empty: "P {#}"
  assumes add: "\<And>M x. P M \<Longrightarrow> P (M + {#x#})"
  shows "P M"
proof (induct n \<equiv> "size M" arbitrary: M)
  case 0 thus "P M" by (simp add: empty)
next
  case (Suc k)
  obtain N x where "M = N + {#x#}"
    using `Suc k = size M` [symmetric]
    using size_eq_Suc_imp_eq_union by fast
  with Suc add show "P M" by simp
qed

lemma multi_nonempty_split: "M \<noteq> {#} \<Longrightarrow> \<exists>A a. M = A + {#a#}"
by (induct M) auto

lemma multiset_cases [cases type]:
  obtains (empty) "M = {#}"
    | (add) N x where "M = N + {#x#}"
  using assms by (induct M) simp_all

lemma multi_drop_mem_not_eq: "c \<in># B \<Longrightarrow> B - {#c#} \<noteq> B"
by (cases "B = {#}") (auto dest: multi_member_split)

lemma multiset_partition: "M = {# x:#M. P x #} + {# x:#M. \<not> P x #}"
apply (subst multiset_eq_iff)
apply auto
done

lemma mset_less_size: "(A::'a multiset) < B \<Longrightarrow> size A < size B"
proof (induct A arbitrary: B)
  case (empty M)
  then have "M \<noteq> {#}" by (simp add: mset_less_empty_nonempty)
  then obtain M' x where "M = M' + {#x#}"
    by (blast dest: multi_nonempty_split)
  then show ?case by simp
next
  case (add S x T)
  have IH: "\<And>B. S < B \<Longrightarrow> size S < size B" by fact
  have SxsubT: "S + {#x#} < T" by fact
  then have "x \<in># T" and "S < T" by (auto dest: mset_less_insertD)
  then obtain T' where T: "T = T' + {#x#}"
    by (blast dest: multi_member_split)
  then have "S < T'" using SxsubT
    by (blast intro: mset_less_add_bothsides)
  then have "size S < size T'" using IH by simp
  then show ?case using T by simp
qed


subsubsection {* Strong induction and subset induction for multisets *}

text {* Well-foundedness of strict subset relation *}

lemma wf_less_mset_rel: "wf {(M, N :: 'a multiset). M < N}"
apply (rule wf_measure [THEN wf_subset, where f1=size])
apply (clarsimp simp: measure_def inv_image_def mset_less_size)
done

lemma full_multiset_induct [case_names less]:
assumes ih: "\<And>B. \<forall>(A::'a multiset). A < B \<longrightarrow> P A \<Longrightarrow> P B"
shows "P B"
apply (rule wf_less_mset_rel [THEN wf_induct])
apply (rule ih, auto)
done

lemma multi_subset_induct [consumes 2, case_names empty add]:
assumes "F \<le> A"
  and empty: "P {#}"
  and insert: "\<And>a F. a \<in># A \<Longrightarrow> P F \<Longrightarrow> P (F + {#a#})"
shows "P F"
proof -
  from `F \<le> A`
  show ?thesis
  proof (induct F)
    show "P {#}" by fact
  next
    fix x F
    assume P: "F \<le> A \<Longrightarrow> P F" and i: "F + {#x#} \<le> A"
    show "P (F + {#x#})"
    proof (rule insert)
      from i show "x \<in># A" by (auto dest: mset_le_insertD)
      from i have "F \<le> A" by (auto dest: mset_le_insertD)
      with P show "P F" .
    qed
  qed
qed


subsection {* The fold combinator *}

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a multiset \<Rightarrow> 'b"
where
  "fold f s M = Finite_Set.fold (\<lambda>x. f x ^^ count M x) s (set_of M)"

lemma fold_mset_empty [simp]:
  "fold f s {#} = s"
  by (simp add: fold_def)

context comp_fun_commute
begin

lemma fold_mset_insert:
  "fold f s (M + {#x#}) = f x (fold f s M)"
proof -
  interpret mset: comp_fun_commute "\<lambda>y. f y ^^ count M y"
    by (fact comp_fun_commute_funpow)
  interpret mset_union: comp_fun_commute "\<lambda>y. f y ^^ count (M + {#x#}) y"
    by (fact comp_fun_commute_funpow)
  show ?thesis
  proof (cases "x \<in> set_of M")
    case False
    then have *: "count (M + {#x#}) x = 1" by simp
    from False have "Finite_Set.fold (\<lambda>y. f y ^^ count (M + {#x#}) y) s (set_of M) =
      Finite_Set.fold (\<lambda>y. f y ^^ count M y) s (set_of M)"
      by (auto intro!: Finite_Set.fold_cong comp_fun_commute_funpow)
    with False * show ?thesis
      by (simp add: fold_def del: count_union)
  next
    case True
    def N \<equiv> "set_of M - {x}"
    from N_def True have *: "set_of M = insert x N" "x \<notin> N" "finite N" by auto
    then have "Finite_Set.fold (\<lambda>y. f y ^^ count (M + {#x#}) y) s N =
      Finite_Set.fold (\<lambda>y. f y ^^ count M y) s N"
      by (auto intro!: Finite_Set.fold_cong comp_fun_commute_funpow)
    with * show ?thesis by (simp add: fold_def del: count_union) simp
  qed
qed

corollary fold_mset_single [simp]:
  "fold f s {#x#} = f x s"
proof -
  have "fold f s ({#} + {#x#}) = f x s" by (simp only: fold_mset_insert) simp
  then show ?thesis by simp
qed

lemma fold_mset_fun_left_comm:
  "f x (fold f s M) = fold f (f x s) M"
  by (induct M) (simp_all add: fold_mset_insert fun_left_comm)

lemma fold_mset_union [simp]:
  "fold f s (M + N) = fold f (fold f s M) N"
proof (induct M)
  case empty then show ?case by simp
next
  case (add M x)
  have "M + {#x#} + N = (M + N) + {#x#}"
    by (simp add: ac_simps)
  with add show ?case by (simp add: fold_mset_insert fold_mset_fun_left_comm)
qed

lemma fold_mset_fusion:
  assumes "comp_fun_commute g"
  shows "(\<And>x y. h (g x y) = f x (h y)) \<Longrightarrow> h (fold g w A) = fold f (h w) A" (is "PROP ?P")
proof -
  interpret comp_fun_commute g by (fact assms)
  show "PROP ?P" by (induct A) auto
qed

end

text {*
  A note on code generation: When defining some function containing a
  subterm @{term "fold F"}, code generation is not automatic. When
  interpreting locale @{text left_commutative} with @{text F}, the
  would be code thms for @{const fold} become thms like
  @{term "fold F z {#} = z"} where @{text F} is not a pattern but
  contains defined symbols, i.e.\ is not a code thm. Hence a separate
  constant with its own code thms needs to be introduced for @{text
  F}. See the image operator below.
*}


subsection {* Image *}

definition image_mset :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a multiset \<Rightarrow> 'b multiset" where
  "image_mset f = fold (plus o single o f) {#}"

lemma comp_fun_commute_mset_image:
  "comp_fun_commute (plus o single o f)"
proof
qed (simp add: ac_simps fun_eq_iff)

lemma image_mset_empty [simp]: "image_mset f {#} = {#}"
  by (simp add: image_mset_def)

lemma image_mset_single [simp]: "image_mset f {#x#} = {#f x#}"
proof -
  interpret comp_fun_commute "plus o single o f"
    by (fact comp_fun_commute_mset_image)
  show ?thesis by (simp add: image_mset_def)
qed

lemma image_mset_union [simp]:
  "image_mset f (M + N) = image_mset f M + image_mset f N"
proof -
  interpret comp_fun_commute "plus o single o f"
    by (fact comp_fun_commute_mset_image)
  show ?thesis by (induct N) (simp_all add: image_mset_def ac_simps)
qed

corollary image_mset_insert:
  "image_mset f (M + {#a#}) = image_mset f M + {#f a#}"
  by simp

lemma set_of_image_mset [simp]:
  "set_of (image_mset f M) = image f (set_of M)"
  by (induct M) simp_all

lemma size_image_mset [simp]:
  "size (image_mset f M) = size M"
  by (induct M) simp_all

lemma image_mset_is_empty_iff [simp]:
  "image_mset f M = {#} \<longleftrightarrow> M = {#}"
  by (cases M) auto

syntax
  "_comprehension1_mset" :: "'a \<Rightarrow> 'b \<Rightarrow> 'b multiset \<Rightarrow> 'a multiset"
      ("({#_/. _ :# _#})")
translations
  "{#e. x:#M#}" == "CONST image_mset (%x. e) M"

syntax
  "_comprehension2_mset" :: "'a \<Rightarrow> 'b \<Rightarrow> 'b multiset \<Rightarrow> bool \<Rightarrow> 'a multiset"
      ("({#_/ | _ :# _./ _#})")
translations
  "{#e | x:#M. P#}" => "{#e. x :# {# x:#M. P#}#}"

text {*
  This allows to write not just filters like @{term "{#x:#M. x<c#}"}
  but also images like @{term "{#x+x. x:#M #}"} and @{term [source]
  "{#x+x|x:#M. x<c#}"}, where the latter is currently displayed as
  @{term "{#x+x|x:#M. x<c#}"}.
*}

functor image_mset: image_mset
proof -
  fix f g show "image_mset f \<circ> image_mset g = image_mset (f \<circ> g)"
  proof
    fix A
    show "(image_mset f \<circ> image_mset g) A = image_mset (f \<circ> g) A"
      by (induct A) simp_all
  qed
  show "image_mset id = id"
  proof
    fix A
    show "image_mset id A = id A"
      by (induct A) simp_all
  qed
qed

declare image_mset.identity [simp]


subsection {* Further conversions *}

primrec multiset_of :: "'a list \<Rightarrow> 'a multiset" where
  "multiset_of [] = {#}" |
  "multiset_of (a # x) = multiset_of x + {# a #}"

lemma in_multiset_in_set:
  "x \<in># multiset_of xs \<longleftrightarrow> x \<in> set xs"
  by (induct xs) simp_all

lemma count_multiset_of:
  "count (multiset_of xs) x = length (filter (\<lambda>y. x = y) xs)"
  by (induct xs) simp_all

lemma multiset_of_zero_iff[simp]: "(multiset_of x = {#}) = (x = [])"
by (induct x) auto

lemma multiset_of_zero_iff_right[simp]: "({#} = multiset_of x) = (x = [])"
by (induct x) auto

lemma set_of_multiset_of[simp]: "set_of (multiset_of x) = set x"
by (induct x) auto

lemma mem_set_multiset_eq: "x \<in> set xs = (x :# multiset_of xs)"
by (induct xs) auto

lemma size_multiset_of [simp]: "size (multiset_of xs) = length xs"
  by (induct xs) simp_all

lemma multiset_of_append [simp]:
  "multiset_of (xs @ ys) = multiset_of xs + multiset_of ys"
  by (induct xs arbitrary: ys) (auto simp: ac_simps)

lemma multiset_of_filter:
  "multiset_of (filter P xs) = {#x :# multiset_of xs. P x #}"
  by (induct xs) simp_all

lemma multiset_of_rev [simp]:
  "multiset_of (rev xs) = multiset_of xs"
  by (induct xs) simp_all

lemma surj_multiset_of: "surj multiset_of"
apply (unfold surj_def)
apply (rule allI)
apply (rule_tac M = y in multiset_induct)
 apply auto
apply (rule_tac x = "x # xa" in exI)
apply auto
done

lemma set_count_greater_0: "set x = {a. count (multiset_of x) a > 0}"
by (induct x) auto

lemma distinct_count_atmost_1:
  "distinct x = (! a. count (multiset_of x) a = (if a \<in> set x then 1 else 0))"
apply (induct x, simp, rule iffI, simp_all)
apply (rename_tac a b)
apply (rule conjI)
apply (simp_all add: set_of_multiset_of [THEN sym] del: set_of_multiset_of)
apply (erule_tac x = a in allE, simp, clarify)
apply (erule_tac x = aa in allE, simp)
done

lemma multiset_of_eq_setD:
  "multiset_of xs = multiset_of ys \<Longrightarrow> set xs = set ys"
by (rule) (auto simp add:multiset_eq_iff set_count_greater_0)

lemma set_eq_iff_multiset_of_eq_distinct:
  "distinct x \<Longrightarrow> distinct y \<Longrightarrow>
    (set x = set y) = (multiset_of x = multiset_of y)"
by (auto simp: multiset_eq_iff distinct_count_atmost_1)

lemma set_eq_iff_multiset_of_remdups_eq:
   "(set x = set y) = (multiset_of (remdups x) = multiset_of (remdups y))"
apply (rule iffI)
apply (simp add: set_eq_iff_multiset_of_eq_distinct[THEN iffD1])
apply (drule distinct_remdups [THEN distinct_remdups
      [THEN set_eq_iff_multiset_of_eq_distinct [THEN iffD2]]])
apply simp
done

lemma multiset_of_compl_union [simp]:
  "multiset_of [x\<leftarrow>xs. P x] + multiset_of [x\<leftarrow>xs. \<not>P x] = multiset_of xs"
  by (induct xs) (auto simp: ac_simps)

lemma count_multiset_of_length_filter:
  "count (multiset_of xs) x = length (filter (\<lambda>y. x = y) xs)"
  by (induct xs) auto

lemma nth_mem_multiset_of: "i < length ls \<Longrightarrow> (ls ! i) :# multiset_of ls"
apply (induct ls arbitrary: i)
 apply simp
apply (case_tac i)
 apply auto
done

lemma multiset_of_remove1[simp]:
  "multiset_of (remove1 a xs) = multiset_of xs - {#a#}"
by (induct xs) (auto simp add: multiset_eq_iff)

lemma multiset_of_eq_length:
  assumes "multiset_of xs = multiset_of ys"
  shows "length xs = length ys"
  using assms by (metis size_multiset_of)

lemma multiset_of_eq_length_filter:
  assumes "multiset_of xs = multiset_of ys"
  shows "length (filter (\<lambda>x. z = x) xs) = length (filter (\<lambda>y. z = y) ys)"
  using assms by (metis count_multiset_of)

lemma fold_multiset_equiv:
  assumes f: "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> f x \<circ> f y = f y \<circ> f x"
    and equiv: "multiset_of xs = multiset_of ys"
  shows "List.fold f xs = List.fold f ys"
using f equiv [symmetric]
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then have *: "set ys = set (x # xs)" by (blast dest: multiset_of_eq_setD)
  have "\<And>x y. x \<in> set ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x \<circ> f y = f y \<circ> f x"
    by (rule Cons.prems(1)) (simp_all add: *)
  moreover from * have "x \<in> set ys" by simp
  ultimately have "List.fold f ys = List.fold f (remove1 x ys) \<circ> f x" by (fact fold_remove1_split)
  moreover from Cons.prems have "List.fold f xs = List.fold f (remove1 x ys)" by (auto intro: Cons.hyps)
  ultimately show ?case by simp
qed

lemma multiset_of_insort [simp]:
  "multiset_of (insort x xs) = multiset_of xs + {#x#}"
  by (induct xs) (simp_all add: ac_simps)

lemma in_multiset_of:
  "x \<in># multiset_of xs \<longleftrightarrow> x \<in> set xs"
  by (induct xs) simp_all

lemma multiset_of_map:
  "multiset_of (map f xs) = image_mset f (multiset_of xs)"
  by (induct xs) simp_all

definition multiset_of_set :: "'a set \<Rightarrow> 'a multiset"
where
  "multiset_of_set = folding.F (\<lambda>x M. {#x#} + M) {#}"

interpretation multiset_of_set!: folding "\<lambda>x M. {#x#} + M" "{#}"
where
  "folding.F (\<lambda>x M. {#x#} + M) {#} = multiset_of_set"
proof -
  interpret comp_fun_commute "\<lambda>x M. {#x#} + M" by default (simp add: fun_eq_iff ac_simps)
  show "folding (\<lambda>x M. {#x#} + M)" by default (fact comp_fun_commute)
  from multiset_of_set_def show "folding.F (\<lambda>x M. {#x#} + M) {#} = multiset_of_set" ..
qed

lemma count_multiset_of_set [simp]:
  "finite A \<Longrightarrow> x \<in> A \<Longrightarrow> count (multiset_of_set A) x = 1" (is "PROP ?P")
  "\<not> finite A \<Longrightarrow> count (multiset_of_set A) x = 0" (is "PROP ?Q")
  "x \<notin> A \<Longrightarrow> count (multiset_of_set A) x = 0" (is "PROP ?R")
proof -
  { fix A
    assume "x \<notin> A"
    have "count (multiset_of_set A) x = 0"
    proof (cases "finite A")
      case False then show ?thesis by simp
    next
      case True from True `x \<notin> A` show ?thesis by (induct A) auto
    qed
  } note * = this
  then show "PROP ?P" "PROP ?Q" "PROP ?R"
  by (auto elim!: Set.set_insert)
qed -- {* TODO: maybe define @{const multiset_of_set} also in terms of @{const Abs_multiset} *}

context linorder
begin

definition sorted_list_of_multiset :: "'a multiset \<Rightarrow> 'a list"
where
  "sorted_list_of_multiset M = fold insort [] M"

lemma sorted_list_of_multiset_empty [simp]:
  "sorted_list_of_multiset {#} = []"
  by (simp add: sorted_list_of_multiset_def)

lemma sorted_list_of_multiset_singleton [simp]:
  "sorted_list_of_multiset {#x#} = [x]"
proof -
  interpret comp_fun_commute insort by (fact comp_fun_commute_insort)
  show ?thesis by (simp add: sorted_list_of_multiset_def)
qed

lemma sorted_list_of_multiset_insert [simp]:
  "sorted_list_of_multiset (M + {#x#}) = List.insort x (sorted_list_of_multiset M)"
proof -
  interpret comp_fun_commute insort by (fact comp_fun_commute_insort)
  show ?thesis by (simp add: sorted_list_of_multiset_def)
qed

end

lemma multiset_of_sorted_list_of_multiset [simp]:
  "multiset_of (sorted_list_of_multiset M) = M"
  by (induct M) simp_all

lemma sorted_list_of_multiset_multiset_of [simp]:
  "sorted_list_of_multiset (multiset_of xs) = sort xs"
  by (induct xs) simp_all

lemma finite_set_of_multiset_of_set:
  assumes "finite A"
  shows "set_of (multiset_of_set A) = A"
  using assms by (induct A) simp_all

lemma infinite_set_of_multiset_of_set:
  assumes "\<not> finite A"
  shows "set_of (multiset_of_set A) = {}"
  using assms by simp

lemma set_sorted_list_of_multiset [simp]:
  "set (sorted_list_of_multiset M) = set_of M"
  by (induct M) (simp_all add: set_insort)

lemma sorted_list_of_multiset_of_set [simp]:
  "sorted_list_of_multiset (multiset_of_set A) = sorted_list_of_set A"
  by (cases "finite A") (induct A rule: finite_induct, simp_all add: ac_simps)


subsection {* Big operators *}

no_notation times (infixl "*" 70)
no_notation Groups.one ("1")

locale comm_monoid_mset = comm_monoid
begin

definition F :: "'a multiset \<Rightarrow> 'a"
where
  eq_fold: "F M = Multiset.fold f 1 M"

lemma empty [simp]:
  "F {#} = 1"
  by (simp add: eq_fold)

lemma singleton [simp]:
  "F {#x#} = x"
proof -
  interpret comp_fun_commute
    by default (simp add: fun_eq_iff left_commute)
  show ?thesis by (simp add: eq_fold)
qed

lemma union [simp]:
  "F (M + N) = F M * F N"
proof -
  interpret comp_fun_commute f
    by default (simp add: fun_eq_iff left_commute)
  show ?thesis by (induct N) (simp_all add: left_commute eq_fold)
qed

end

notation times (infixl "*" 70)
notation Groups.one ("1")

context comm_monoid_add
begin

definition msetsum :: "'a multiset \<Rightarrow> 'a"
where
  "msetsum = comm_monoid_mset.F plus 0"

sublocale msetsum!: comm_monoid_mset plus 0
where
  "comm_monoid_mset.F plus 0 = msetsum"
proof -
  show "comm_monoid_mset plus 0" ..
  from msetsum_def show "comm_monoid_mset.F plus 0 = msetsum" ..
qed

lemma setsum_unfold_msetsum:
  "setsum f A = msetsum (image_mset f (multiset_of_set A))"
  by (cases "finite A") (induct A rule: finite_induct, simp_all)

end

syntax
  "_msetsum_image" :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add"
      ("(3SUM _:#_. _)" [0, 51, 10] 10)

syntax (xsymbols)
  "_msetsum_image" :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add"
      ("(3\<Sum>_\<in>#_. _)" [0, 51, 10] 10)

syntax (HTML output)
  "_msetsum_image" :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add"
      ("(3\<Sum>_\<in>#_. _)" [0, 51, 10] 10)

translations
  "SUM i :# A. b" == "CONST msetsum (CONST image_mset (\<lambda>i. b) A)"

context comm_monoid_mult
begin

definition msetprod :: "'a multiset \<Rightarrow> 'a"
where
  "msetprod = comm_monoid_mset.F times 1"

sublocale msetprod!: comm_monoid_mset times 1
where
  "comm_monoid_mset.F times 1 = msetprod"
proof -
  show "comm_monoid_mset times 1" ..
  from msetprod_def show "comm_monoid_mset.F times 1 = msetprod" ..
qed

lemma msetprod_empty:
  "msetprod {#} = 1"
  by (fact msetprod.empty)

lemma msetprod_singleton:
  "msetprod {#x#} = x"
  by (fact msetprod.singleton)

lemma msetprod_Un:
  "msetprod (A + B) = msetprod A * msetprod B"
  by (fact msetprod.union)

lemma setprod_unfold_msetprod:
  "setprod f A = msetprod (image_mset f (multiset_of_set A))"
  by (cases "finite A") (induct A rule: finite_induct, simp_all)

lemma msetprod_multiplicity:
  "msetprod M = setprod (\<lambda>x. x ^ count M x) (set_of M)"
  by (simp add: Multiset.fold_def setprod.eq_fold msetprod.eq_fold funpow_times_power comp_def)

end

syntax
  "_msetprod_image" :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_mult"
      ("(3PROD _:#_. _)" [0, 51, 10] 10)

syntax (xsymbols)
  "_msetprod_image" :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_mult"
      ("(3\<Prod>_\<in>#_. _)" [0, 51, 10] 10)

syntax (HTML output)
  "_msetprod_image" :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_mult"
      ("(3\<Prod>_\<in>#_. _)" [0, 51, 10] 10)

translations
  "PROD i :# A. b" == "CONST msetprod (CONST image_mset (\<lambda>i. b) A)"

lemma (in comm_semiring_1) dvd_msetprod:
  assumes "x \<in># A"
  shows "x dvd msetprod A"
proof -
  from assms have "A = (A - {#x#}) + {#x#}" by simp
  then obtain B where "A = B + {#x#}" ..
  then show ?thesis by simp
qed


subsection {* Cardinality *}

definition mcard :: "'a multiset \<Rightarrow> nat"
where
  "mcard = msetsum \<circ> image_mset (\<lambda>_. 1)"

lemma mcard_empty [simp]:
  "mcard {#} = 0"
  by (simp add: mcard_def)

lemma mcard_singleton [simp]:
  "mcard {#a#} = Suc 0"
  by (simp add: mcard_def)

lemma mcard_plus [simp]:
  "mcard (M + N) = mcard M + mcard N"
  by (simp add: mcard_def)

lemma mcard_empty_iff [simp]:
  "mcard M = 0 \<longleftrightarrow> M = {#}"
  by (induct M) simp_all

lemma mcard_unfold_setsum:
  "mcard M = setsum (count M) (set_of M)"
proof (induct M)
  case empty then show ?case by simp
next
  case (add M x) then show ?case
    by (cases "x \<in> set_of M")
      (simp_all del: mem_set_of_iff add: setsum.distrib setsum.delta' insert_absorb, simp)
qed

lemma size_eq_mcard:
  "size = mcard"
  by (simp add: fun_eq_iff size_multiset_overloaded_eq mcard_unfold_setsum)

lemma mcard_multiset_of:
  "mcard (multiset_of xs) = length xs"
  by (induct xs) simp_all

lemma mcard_mono: assumes "A \<le> B"
  shows "mcard A \<le> mcard B"
proof -
  from assms[unfolded mset_le_exists_conv]
  obtain C where B: "B = A + C" by auto
  show ?thesis unfolding B by (induct C, auto)
qed

lemma mcard_filter_lesseq[simp]: "mcard (Multiset.filter f M) \<le> mcard M"
  by (rule mcard_mono[OF multiset_filter_subset])


subsection {* Alternative representations *}

subsubsection {* Lists *}

context linorder
begin

lemma multiset_of_insort [simp]:
  "multiset_of (insort_key k x xs) = {#x#} + multiset_of xs"
  by (induct xs) (simp_all add: ac_simps)

lemma multiset_of_sort [simp]:
  "multiset_of (sort_key k xs) = multiset_of xs"
  by (induct xs) (simp_all add: ac_simps)

text {*
  This lemma shows which properties suffice to show that a function
  @{text "f"} with @{text "f xs = ys"} behaves like sort.
*}

lemma properties_for_sort_key:
  assumes "multiset_of ys = multiset_of xs"
  and "\<And>k. k \<in> set ys \<Longrightarrow> filter (\<lambda>x. f k = f x) ys = filter (\<lambda>x. f k = f x) xs"
  and "sorted (map f ys)"
  shows "sort_key f xs = ys"
using assms
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(2) have
    "\<forall>k \<in> set ys. filter (\<lambda>x. f k = f x) (remove1 x ys) = filter (\<lambda>x. f k = f x) xs"
    by (simp add: filter_remove1)
  with Cons.prems have "sort_key f xs = remove1 x ys"
    by (auto intro!: Cons.hyps simp add: sorted_map_remove1)
  moreover from Cons.prems have "x \<in> set ys"
    by (auto simp add: mem_set_multiset_eq intro!: ccontr)
  ultimately show ?case using Cons.prems by (simp add: insort_key_remove1)
qed

lemma properties_for_sort:
  assumes multiset: "multiset_of ys = multiset_of xs"
  and "sorted ys"
  shows "sort xs = ys"
proof (rule properties_for_sort_key)
  from multiset show "multiset_of ys = multiset_of xs" .
  from `sorted ys` show "sorted (map (\<lambda>x. x) ys)" by simp
  from multiset have "\<And>k. length (filter (\<lambda>y. k = y) ys) = length (filter (\<lambda>x. k = x) xs)"
    by (rule multiset_of_eq_length_filter)
  then have "\<And>k. replicate (length (filter (\<lambda>y. k = y) ys)) k = replicate (length (filter (\<lambda>x. k = x) xs)) k"
    by simp
  then show "\<And>k. k \<in> set ys \<Longrightarrow> filter (\<lambda>y. k = y) ys = filter (\<lambda>x. k = x) xs"
    by (simp add: replicate_length_filter)
qed

lemma sort_key_by_quicksort:
  "sort_key f xs = sort_key f [x\<leftarrow>xs. f x < f (xs ! (length xs div 2))]
    @ [x\<leftarrow>xs. f x = f (xs ! (length xs div 2))]
    @ sort_key f [x\<leftarrow>xs. f x > f (xs ! (length xs div 2))]" (is "sort_key f ?lhs = ?rhs")
proof (rule properties_for_sort_key)
  show "multiset_of ?rhs = multiset_of ?lhs"
    by (rule multiset_eqI) (auto simp add: multiset_of_filter)
next
  show "sorted (map f ?rhs)"
    by (auto simp add: sorted_append intro: sorted_map_same)
next
  fix l
  assume "l \<in> set ?rhs"
  let ?pivot = "f (xs ! (length xs div 2))"
  have *: "\<And>x. f l = f x \<longleftrightarrow> f x = f l" by auto
  have "[x \<leftarrow> sort_key f xs . f x = f l] = [x \<leftarrow> xs. f x = f l]"
    unfolding filter_sort by (rule properties_for_sort_key) (auto intro: sorted_map_same)
  with * have **: "[x \<leftarrow> sort_key f xs . f l = f x] = [x \<leftarrow> xs. f l = f x]" by simp
  have "\<And>x P. P (f x) ?pivot \<and> f l = f x \<longleftrightarrow> P (f l) ?pivot \<and> f l = f x" by auto
  then have "\<And>P. [x \<leftarrow> sort_key f xs . P (f x) ?pivot \<and> f l = f x] =
    [x \<leftarrow> sort_key f xs. P (f l) ?pivot \<and> f l = f x]" by simp
  note *** = this [of "op <"] this [of "op >"] this [of "op ="]
  show "[x \<leftarrow> ?rhs. f l = f x] = [x \<leftarrow> ?lhs. f l = f x]"
  proof (cases "f l" ?pivot rule: linorder_cases)
    case less
    then have "f l \<noteq> ?pivot" and "\<not> f l > ?pivot" by auto
    with less show ?thesis
      by (simp add: filter_sort [symmetric] ** ***)
  next
    case equal then show ?thesis
      by (simp add: * less_le)
  next
    case greater
    then have "f l \<noteq> ?pivot" and "\<not> f l < ?pivot" by auto
    with greater show ?thesis
      by (simp add: filter_sort [symmetric] ** ***)
  qed
qed

lemma sort_by_quicksort:
  "sort xs = sort [x\<leftarrow>xs. x < xs ! (length xs div 2)]
    @ [x\<leftarrow>xs. x = xs ! (length xs div 2)]
    @ sort [x\<leftarrow>xs. x > xs ! (length xs div 2)]" (is "sort ?lhs = ?rhs")
  using sort_key_by_quicksort [of "\<lambda>x. x", symmetric] by simp

text {* A stable parametrized quicksort *}

definition part :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'b list \<times> 'b list \<times> 'b list" where
  "part f pivot xs = ([x \<leftarrow> xs. f x < pivot], [x \<leftarrow> xs. f x = pivot], [x \<leftarrow> xs. pivot < f x])"

lemma part_code [code]:
  "part f pivot [] = ([], [], [])"
  "part f pivot (x # xs) = (let (lts, eqs, gts) = part f pivot xs; x' = f x in
     if x' < pivot then (x # lts, eqs, gts)
     else if x' > pivot then (lts, eqs, x # gts)
     else (lts, x # eqs, gts))"
  by (auto simp add: part_def Let_def split_def)

lemma sort_key_by_quicksort_code [code]:
  "sort_key f xs = (case xs of [] \<Rightarrow> []
    | [x] \<Rightarrow> xs
    | [x, y] \<Rightarrow> (if f x \<le> f y then xs else [y, x])
    | _ \<Rightarrow> (let (lts, eqs, gts) = part f (f (xs ! (length xs div 2))) xs
       in sort_key f lts @ eqs @ sort_key f gts))"
proof (cases xs)
  case Nil then show ?thesis by simp
next
  case (Cons _ ys) note hyps = Cons show ?thesis
  proof (cases ys)
    case Nil with hyps show ?thesis by simp
  next
    case (Cons _ zs) note hyps = hyps Cons show ?thesis
    proof (cases zs)
      case Nil with hyps show ?thesis by auto
    next
      case Cons
      from sort_key_by_quicksort [of f xs]
      have "sort_key f xs = (let (lts, eqs, gts) = part f (f (xs ! (length xs div 2))) xs
        in sort_key f lts @ eqs @ sort_key f gts)"
      by (simp only: split_def Let_def part_def fst_conv snd_conv)
      with hyps Cons show ?thesis by (simp only: list.cases)
    qed
  qed
qed

end

hide_const (open) part

lemma multiset_of_remdups_le: "multiset_of (remdups xs) \<le> multiset_of xs"
  by (induct xs) (auto intro: order_trans)

lemma multiset_of_update:
  "i < length ls \<Longrightarrow> multiset_of (ls[i := v]) = multiset_of ls - {#ls ! i#} + {#v#}"
proof (induct ls arbitrary: i)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case 0 then show ?thesis by simp
  next
    case (Suc i')
    with Cons show ?thesis
      apply simp
      apply (subst add.assoc)
      apply (subst add.commute [of "{#v#}" "{#x#}"])
      apply (subst add.assoc [symmetric])
      apply simp
      apply (rule mset_le_multiset_union_diff_commute)
      apply (simp add: mset_le_single nth_mem_multiset_of)
      done
  qed
qed

lemma multiset_of_swap:
  "i < length ls \<Longrightarrow> j < length ls \<Longrightarrow>
    multiset_of (ls[j := ls ! i, i := ls ! j]) = multiset_of ls"
  by (cases "i = j") (simp_all add: multiset_of_update nth_mem_multiset_of)


subsection {* The multiset order *}

subsubsection {* Well-foundedness *}

definition mult1 :: "('a \<times> 'a) set => ('a multiset \<times> 'a multiset) set" where
  "mult1 r = {(N, M). \<exists>a M0 K. M = M0 + {#a#} \<and> N = M0 + K \<and>
      (\<forall>b. b :# K --> (b, a) \<in> r)}"

definition mult :: "('a \<times> 'a) set => ('a multiset \<times> 'a multiset) set" where
  "mult r = (mult1 r)\<^sup>+"

lemma not_less_empty [iff]: "(M, {#}) \<notin> mult1 r"
by (simp add: mult1_def)

lemma less_add: "(N, M0 + {#a#}) \<in> mult1 r ==>
    (\<exists>M. (M, M0) \<in> mult1 r \<and> N = M + {#a#}) \<or>
    (\<exists>K. (\<forall>b. b :# K --> (b, a) \<in> r) \<and> N = M0 + K)"
  (is "_ \<Longrightarrow> ?case1 (mult1 r) \<or> ?case2")
proof (unfold mult1_def)
  let ?r = "\<lambda>K a. \<forall>b. b :# K --> (b, a) \<in> r"
  let ?R = "\<lambda>N M. \<exists>a M0 K. M = M0 + {#a#} \<and> N = M0 + K \<and> ?r K a"
  let ?case1 = "?case1 {(N, M). ?R N M}"

  assume "(N, M0 + {#a#}) \<in> {(N, M). ?R N M}"
  then have "\<exists>a' M0' K.
      M0 + {#a#} = M0' + {#a'#} \<and> N = M0' + K \<and> ?r K a'" by simp
  then show "?case1 \<or> ?case2"
  proof (elim exE conjE)
    fix a' M0' K
    assume N: "N = M0' + K" and r: "?r K a'"
    assume "M0 + {#a#} = M0' + {#a'#}"
    then have "M0 = M0' \<and> a = a' \<or>
        (\<exists>K'. M0 = K' + {#a'#} \<and> M0' = K' + {#a#})"
      by (simp only: add_eq_conv_ex)
    then show ?thesis
    proof (elim disjE conjE exE)
      assume "M0 = M0'" "a = a'"
      with N r have "?r K a \<and> N = M0 + K" by simp
      then have ?case2 .. then show ?thesis ..
    next
      fix K'
      assume "M0' = K' + {#a#}"
      with N have n: "N = K' + K + {#a#}" by (simp add: ac_simps)

      assume "M0 = K' + {#a'#}"
      with r have "?R (K' + K) M0" by blast
      with n have ?case1 by simp then show ?thesis ..
    qed
  qed
qed

lemma all_accessible: "wf r ==> \<forall>M. M \<in> Wellfounded.acc (mult1 r)"
proof
  let ?R = "mult1 r"
  let ?W = "Wellfounded.acc ?R"
  {
    fix M M0 a
    assume M0: "M0 \<in> ?W"
      and wf_hyp: "!!b. (b, a) \<in> r ==> (\<forall>M \<in> ?W. M + {#b#} \<in> ?W)"
      and acc_hyp: "\<forall>M. (M, M0) \<in> ?R --> M + {#a#} \<in> ?W"
    have "M0 + {#a#} \<in> ?W"
    proof (rule accI [of "M0 + {#a#}"])
      fix N
      assume "(N, M0 + {#a#}) \<in> ?R"
      then have "((\<exists>M. (M, M0) \<in> ?R \<and> N = M + {#a#}) \<or>
          (\<exists>K. (\<forall>b. b :# K --> (b, a) \<in> r) \<and> N = M0 + K))"
        by (rule less_add)
      then show "N \<in> ?W"
      proof (elim exE disjE conjE)
        fix M assume "(M, M0) \<in> ?R" and N: "N = M + {#a#}"
        from acc_hyp have "(M, M0) \<in> ?R --> M + {#a#} \<in> ?W" ..
        from this and `(M, M0) \<in> ?R` have "M + {#a#} \<in> ?W" ..
        then show "N \<in> ?W" by (simp only: N)
      next
        fix K
        assume N: "N = M0 + K"
        assume "\<forall>b. b :# K --> (b, a) \<in> r"
        then have "M0 + K \<in> ?W"
        proof (induct K)
          case empty
          from M0 show "M0 + {#} \<in> ?W" by simp
        next
          case (add K x)
          from add.prems have "(x, a) \<in> r" by simp
          with wf_hyp have "\<forall>M \<in> ?W. M + {#x#} \<in> ?W" by blast
          moreover from add have "M0 + K \<in> ?W" by simp
          ultimately have "(M0 + K) + {#x#} \<in> ?W" ..
          then show "M0 + (K + {#x#}) \<in> ?W" by (simp only: add.assoc)
        qed
        then show "N \<in> ?W" by (simp only: N)
      qed
    qed
  } note tedious_reasoning = this

  assume wf: "wf r"
  fix M
  show "M \<in> ?W"
  proof (induct M)
    show "{#} \<in> ?W"
    proof (rule accI)
      fix b assume "(b, {#}) \<in> ?R"
      with not_less_empty show "b \<in> ?W" by contradiction
    qed

    fix M a assume "M \<in> ?W"
    from wf have "\<forall>M \<in> ?W. M + {#a#} \<in> ?W"
    proof induct
      fix a
      assume r: "!!b. (b, a) \<in> r ==> (\<forall>M \<in> ?W. M + {#b#} \<in> ?W)"
      show "\<forall>M \<in> ?W. M + {#a#} \<in> ?W"
      proof
        fix M assume "M \<in> ?W"
        then show "M + {#a#} \<in> ?W"
          by (rule acc_induct) (rule tedious_reasoning [OF _ r])
      qed
    qed
    from this and `M \<in> ?W` show "M + {#a#} \<in> ?W" ..
  qed
qed

theorem wf_mult1: "wf r ==> wf (mult1 r)"
by (rule acc_wfI) (rule all_accessible)

theorem wf_mult: "wf r ==> wf (mult r)"
unfolding mult_def by (rule wf_trancl) (rule wf_mult1)


subsubsection {* Closure-free presentation *}

text {* One direction. *}

lemma mult_implies_one_step:
  "trans r ==> (M, N) \<in> mult r ==>
    \<exists>I J K. N = I + J \<and> M = I + K \<and> J \<noteq> {#} \<and>
    (\<forall>k \<in> set_of K. \<exists>j \<in> set_of J. (k, j) \<in> r)"
apply (unfold mult_def mult1_def set_of_def)
apply (erule converse_trancl_induct, clarify)
 apply (rule_tac x = M0 in exI, simp, clarify)
apply (case_tac "a :# K")
 apply (rule_tac x = I in exI)
 apply (simp (no_asm))
 apply (rule_tac x = "(K - {#a#}) + Ka" in exI)
 apply (simp (no_asm_simp) add: add.assoc [symmetric])
 apply (drule_tac f = "\<lambda>M. M - {#a#}" and x="?S + ?T" in arg_cong)
 apply (simp add: diff_union_single_conv)
 apply (simp (no_asm_use) add: trans_def)
 apply blast
apply (subgoal_tac "a :# I")
 apply (rule_tac x = "I - {#a#}" in exI)
 apply (rule_tac x = "J + {#a#}" in exI)
 apply (rule_tac x = "K + Ka" in exI)
 apply (rule conjI)
  apply (simp add: multiset_eq_iff split: nat_diff_split)
 apply (rule conjI)
  apply (drule_tac f = "\<lambda>M. M - {#a#}" and x="?S + ?T" in arg_cong, simp)
  apply (simp add: multiset_eq_iff split: nat_diff_split)
 apply (simp (no_asm_use) add: trans_def)
 apply blast
apply (subgoal_tac "a :# (M0 + {#a#})")
 apply simp
apply (simp (no_asm))
done

lemma one_step_implies_mult_aux:
  "trans r ==>
    \<forall>I J K. (size J = n \<and> J \<noteq> {#} \<and> (\<forall>k \<in> set_of K. \<exists>j \<in> set_of J. (k, j) \<in> r))
      --> (I + K, I + J) \<in> mult r"
apply (induct_tac n, auto)
apply (frule size_eq_Suc_imp_eq_union, clarify)
apply (rename_tac "J'", simp)
apply (erule notE, auto)
apply (case_tac "J' = {#}")
 apply (simp add: mult_def)
 apply (rule r_into_trancl)
 apply (simp add: mult1_def set_of_def, blast)
txt {* Now we know @{term "J' \<noteq> {#}"}. *}
apply (cut_tac M = K and P = "\<lambda>x. (x, a) \<in> r" in multiset_partition)
apply (erule_tac P = "\<forall>k \<in> set_of K. ?P k" in rev_mp)
apply (erule ssubst)
apply (simp add: Ball_def, auto)
apply (subgoal_tac
  "((I + {# x :# K. (x, a) \<in> r #}) + {# x :# K. (x, a) \<notin> r #},
    (I + {# x :# K. (x, a) \<in> r #}) + J') \<in> mult r")
 prefer 2
 apply force
apply (simp (no_asm_use) add: add.assoc [symmetric] mult_def)
apply (erule trancl_trans)
apply (rule r_into_trancl)
apply (simp add: mult1_def set_of_def)
apply (rule_tac x = a in exI)
apply (rule_tac x = "I + J'" in exI)
apply (simp add: ac_simps)
done

lemma one_step_implies_mult:
  "trans r ==> J \<noteq> {#} ==> \<forall>k \<in> set_of K. \<exists>j \<in> set_of J. (k, j) \<in> r
    ==> (I + K, I + J) \<in> mult r"
using one_step_implies_mult_aux by blast


subsubsection {* Partial-order properties *}

definition less_multiset :: "'a\<Colon>order multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" (infix "<#" 50) where
  "M' <# M \<longleftrightarrow> (M', M) \<in> mult {(x', x). x' < x}"

definition le_multiset :: "'a\<Colon>order multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" (infix "<=#" 50) where
  "M' <=# M \<longleftrightarrow> M' <# M \<or> M' = M"

notation (xsymbols) less_multiset (infix "\<subset>#" 50)
notation (xsymbols) le_multiset (infix "\<subseteq>#" 50)

interpretation multiset_order: order le_multiset less_multiset
proof -
  have irrefl: "\<And>M :: 'a multiset. \<not> M \<subset># M"
  proof
    fix M :: "'a multiset"
    assume "M \<subset># M"
    then have MM: "(M, M) \<in> mult {(x, y). x < y}" by (simp add: less_multiset_def)
    have "trans {(x'::'a, x). x' < x}"
      by (rule transI) simp
    moreover note MM
    ultimately have "\<exists>I J K. M = I + J \<and> M = I + K
      \<and> J \<noteq> {#} \<and> (\<forall>k\<in>set_of K. \<exists>j\<in>set_of J. (k, j) \<in> {(x, y). x < y})"
      by (rule mult_implies_one_step)
    then obtain I J K where "M = I + J" and "M = I + K"
      and "J \<noteq> {#}" and "(\<forall>k\<in>set_of K. \<exists>j\<in>set_of J. (k, j) \<in> {(x, y). x < y})" by blast
    then have aux1: "K \<noteq> {#}" and aux2: "\<forall>k\<in>set_of K. \<exists>j\<in>set_of K. k < j" by auto
    have "finite (set_of K)" by simp
    moreover note aux2
    ultimately have "set_of K = {}"
      by (induct rule: finite_induct) (auto intro: order_less_trans)
    with aux1 show False by simp
  qed
  have trans: "\<And>K M N :: 'a multiset. K \<subset># M \<Longrightarrow> M \<subset># N \<Longrightarrow> K \<subset># N"
    unfolding less_multiset_def mult_def by (blast intro: trancl_trans)
  show "class.order (le_multiset :: 'a multiset \<Rightarrow> _) less_multiset"
    by default (auto simp add: le_multiset_def irrefl dest: trans)
qed

lemma mult_less_irrefl [elim!]: "M \<subset># (M::'a::order multiset) ==> R"
  by simp


subsubsection {* Monotonicity of multiset union *}

lemma mult1_union: "(B, D) \<in> mult1 r ==> (C + B, C + D) \<in> mult1 r"
apply (unfold mult1_def)
apply auto
apply (rule_tac x = a in exI)
apply (rule_tac x = "C + M0" in exI)
apply (simp add: add.assoc)
done

lemma union_less_mono2: "B \<subset># D ==> C + B \<subset># C + (D::'a::order multiset)"
apply (unfold less_multiset_def mult_def)
apply (erule trancl_induct)
 apply (blast intro: mult1_union)
apply (blast intro: mult1_union trancl_trans)
done

lemma union_less_mono1: "B \<subset># D ==> B + C \<subset># D + (C::'a::order multiset)"
apply (subst add.commute [of B C])
apply (subst add.commute [of D C])
apply (erule union_less_mono2)
done

lemma union_less_mono:
  "A \<subset># C ==> B \<subset># D ==> A + B \<subset># C + (D::'a::order multiset)"
  by (blast intro!: union_less_mono1 union_less_mono2 multiset_order.less_trans)

interpretation multiset_order: ordered_ab_semigroup_add plus le_multiset less_multiset
proof
qed (auto simp add: le_multiset_def intro: union_less_mono2)


subsection {* Termination proofs with multiset orders *}

lemma multi_member_skip: "x \<in># XS \<Longrightarrow> x \<in># {# y #} + XS"
  and multi_member_this: "x \<in># {# x #} + XS"
  and multi_member_last: "x \<in># {# x #}"
  by auto

definition "ms_strict = mult pair_less"
definition "ms_weak = ms_strict \<union> Id"

lemma ms_reduction_pair: "reduction_pair (ms_strict, ms_weak)"
unfolding reduction_pair_def ms_strict_def ms_weak_def pair_less_def
by (auto intro: wf_mult1 wf_trancl simp: mult_def)

lemma smsI:
  "(set_of A, set_of B) \<in> max_strict \<Longrightarrow> (Z + A, Z + B) \<in> ms_strict"
  unfolding ms_strict_def
by (rule one_step_implies_mult) (auto simp add: max_strict_def pair_less_def elim!:max_ext.cases)

lemma wmsI:
  "(set_of A, set_of B) \<in> max_strict \<or> A = {#} \<and> B = {#}
  \<Longrightarrow> (Z + A, Z + B) \<in> ms_weak"
unfolding ms_weak_def ms_strict_def
by (auto simp add: pair_less_def max_strict_def elim!:max_ext.cases intro: one_step_implies_mult)

inductive pw_leq
where
  pw_leq_empty: "pw_leq {#} {#}"
| pw_leq_step:  "\<lbrakk>(x,y) \<in> pair_leq; pw_leq X Y \<rbrakk> \<Longrightarrow> pw_leq ({#x#} + X) ({#y#} + Y)"

lemma pw_leq_lstep:
  "(x, y) \<in> pair_leq \<Longrightarrow> pw_leq {#x#} {#y#}"
by (drule pw_leq_step) (rule pw_leq_empty, simp)

lemma pw_leq_split:
  assumes "pw_leq X Y"
  shows "\<exists>A B Z. X = A + Z \<and> Y = B + Z \<and> ((set_of A, set_of B) \<in> max_strict \<or> (B = {#} \<and> A = {#}))"
  using assms
proof (induct)
  case pw_leq_empty thus ?case by auto
next
  case (pw_leq_step x y X Y)
  then obtain A B Z where
    [simp]: "X = A + Z" "Y = B + Z"
      and 1[simp]: "(set_of A, set_of B) \<in> max_strict \<or> (B = {#} \<and> A = {#})"
    by auto
  from pw_leq_step have "x = y \<or> (x, y) \<in> pair_less"
    unfolding pair_leq_def by auto
  thus ?case
  proof
    assume [simp]: "x = y"
    have
      "{#x#} + X = A + ({#y#}+Z)
      \<and> {#y#} + Y = B + ({#y#}+Z)
      \<and> ((set_of A, set_of B) \<in> max_strict \<or> (B = {#} \<and> A = {#}))"
      by (auto simp: ac_simps)
    thus ?case by (intro exI)
  next
    assume A: "(x, y) \<in> pair_less"
    let ?A' = "{#x#} + A" and ?B' = "{#y#} + B"
    have "{#x#} + X = ?A' + Z"
      "{#y#} + Y = ?B' + Z"
      by (auto simp add: ac_simps)
    moreover have
      "(set_of ?A', set_of ?B') \<in> max_strict"
      using 1 A unfolding max_strict_def
      by (auto elim!: max_ext.cases)
    ultimately show ?thesis by blast
  qed
qed

lemma
  assumes pwleq: "pw_leq Z Z'"
  shows ms_strictI: "(set_of A, set_of B) \<in> max_strict \<Longrightarrow> (Z + A, Z' + B) \<in> ms_strict"
  and   ms_weakI1:  "(set_of A, set_of B) \<in> max_strict \<Longrightarrow> (Z + A, Z' + B) \<in> ms_weak"
  and   ms_weakI2:  "(Z + {#}, Z' + {#}) \<in> ms_weak"
proof -
  from pw_leq_split[OF pwleq]
  obtain A' B' Z''
    where [simp]: "Z = A' + Z''" "Z' = B' + Z''"
    and mx_or_empty: "(set_of A', set_of B') \<in> max_strict \<or> (A' = {#} \<and> B' = {#})"
    by blast
  {
    assume max: "(set_of A, set_of B) \<in> max_strict"
    from mx_or_empty
    have "(Z'' + (A + A'), Z'' + (B + B')) \<in> ms_strict"
    proof
      assume max': "(set_of A', set_of B') \<in> max_strict"
      with max have "(set_of (A + A'), set_of (B + B')) \<in> max_strict"
        by (auto simp: max_strict_def intro: max_ext_additive)
      thus ?thesis by (rule smsI)
    next
      assume [simp]: "A' = {#} \<and> B' = {#}"
      show ?thesis by (rule smsI) (auto intro: max)
    qed
    thus "(Z + A, Z' + B) \<in> ms_strict" by (simp add:ac_simps)
    thus "(Z + A, Z' + B) \<in> ms_weak" by (simp add: ms_weak_def)
  }
  from mx_or_empty
  have "(Z'' + A', Z'' + B') \<in> ms_weak" by (rule wmsI)
  thus "(Z + {#}, Z' + {#}) \<in> ms_weak" by (simp add:ac_simps)
qed

lemma empty_neutral: "{#} + x = x" "x + {#} = x"
and nonempty_plus: "{# x #} + rs \<noteq> {#}"
and nonempty_single: "{# x #} \<noteq> {#}"
by auto

setup {*
let
  fun msetT T = Type (@{type_name multiset}, [T]);

  fun mk_mset T [] = Const (@{const_abbrev Mempty}, msetT T)
    | mk_mset T [x] = Const (@{const_name single}, T --> msetT T) $ x
    | mk_mset T (x :: xs) =
          Const (@{const_name plus}, msetT T --> msetT T --> msetT T) $
                mk_mset T [x] $ mk_mset T xs

  fun mset_member_tac m i =
      (if m <= 0 then
           rtac @{thm multi_member_this} i ORELSE rtac @{thm multi_member_last} i
       else
           rtac @{thm multi_member_skip} i THEN mset_member_tac (m - 1) i)

  val mset_nonempty_tac =
      rtac @{thm nonempty_plus} ORELSE' rtac @{thm nonempty_single}

  val regroup_munion_conv =
      Function_Lib.regroup_conv @{const_abbrev Mempty} @{const_name plus}
        (map (fn t => t RS eq_reflection) (@{thms ac_simps} @ @{thms empty_neutral}))

  fun unfold_pwleq_tac i =
    (rtac @{thm pw_leq_step} i THEN (fn st => unfold_pwleq_tac (i + 1) st))
      ORELSE (rtac @{thm pw_leq_lstep} i)
      ORELSE (rtac @{thm pw_leq_empty} i)

  val set_of_simps = [@{thm set_of_empty}, @{thm set_of_single}, @{thm set_of_union},
                      @{thm Un_insert_left}, @{thm Un_empty_left}]
in
  ScnpReconstruct.multiset_setup (ScnpReconstruct.Multiset
  {
    msetT=msetT, mk_mset=mk_mset, mset_regroup_conv=regroup_munion_conv,
    mset_member_tac=mset_member_tac, mset_nonempty_tac=mset_nonempty_tac,
    mset_pwleq_tac=unfold_pwleq_tac, set_of_simps=set_of_simps,
    smsI'= @{thm ms_strictI}, wmsI2''= @{thm ms_weakI2}, wmsI1= @{thm ms_weakI1},
    reduction_pair= @{thm ms_reduction_pair}
  })
end
*}


subsection {* Legacy theorem bindings *}

lemmas multi_count_eq = multiset_eq_iff [symmetric]

lemma union_commute: "M + N = N + (M::'a multiset)"
  by (fact add.commute)

lemma union_assoc: "(M + N) + K = M + (N + (K::'a multiset))"
  by (fact add.assoc)

lemma union_lcomm: "M + (N + K) = N + (M + (K::'a multiset))"
  by (fact add.left_commute)

lemmas union_ac = union_assoc union_commute union_lcomm

lemma union_right_cancel: "M + K = N + K \<longleftrightarrow> M = (N::'a multiset)"
  by (fact add_right_cancel)

lemma union_left_cancel: "K + M = K + N \<longleftrightarrow> M = (N::'a multiset)"
  by (fact add_left_cancel)

lemma multi_union_self_other_eq: "(A::'a multiset) + X = A + Y \<Longrightarrow> X = Y"
  by (fact add_imp_eq)

lemma mset_less_trans: "(M::'a multiset) < K \<Longrightarrow> K < N \<Longrightarrow> M < N"
  by (fact order_less_trans)

lemma multiset_inter_commute: "A #\<inter> B = B #\<inter> A"
  by (fact inf.commute)

lemma multiset_inter_assoc: "A #\<inter> (B #\<inter> C) = A #\<inter> B #\<inter> C"
  by (fact inf.assoc [symmetric])

lemma multiset_inter_left_commute: "A #\<inter> (B #\<inter> C) = B #\<inter> (A #\<inter> C)"
  by (fact inf.left_commute)

lemmas multiset_inter_ac =
  multiset_inter_commute
  multiset_inter_assoc
  multiset_inter_left_commute

lemma mult_less_not_refl:
  "\<not> M \<subset># (M::'a::order multiset)"
  by (fact multiset_order.less_irrefl)

lemma mult_less_trans:
  "K \<subset># M ==> M \<subset># N ==> K \<subset># (N::'a::order multiset)"
  by (fact multiset_order.less_trans)

lemma mult_less_not_sym:
  "M \<subset># N ==> \<not> N \<subset># (M::'a::order multiset)"
  by (fact multiset_order.less_not_sym)

lemma mult_less_asym:
  "M \<subset># N ==> (\<not> P ==> N \<subset># (M::'a::order multiset)) ==> P"
  by (fact multiset_order.less_asym)

ML {*
fun multiset_postproc _ maybe_name all_values (T as Type (_, [elem_T]))
                      (Const _ $ t') =
    let
      val (maybe_opt, ps) =
        Nitpick_Model.dest_plain_fun t' ||> op ~~
        ||> map (apsnd (snd o HOLogic.dest_number))
      fun elems_for t =
        case AList.lookup (op =) ps t of
          SOME n => replicate n t
        | NONE => [Const (maybe_name, elem_T --> elem_T) $ t]
    in
      case maps elems_for (all_values elem_T) @
           (if maybe_opt then [Const (Nitpick_Model.unrep (), elem_T)]
            else []) of
        [] => Const (@{const_name zero_class.zero}, T)
      | ts => foldl1 (fn (t1, t2) =>
                         Const (@{const_name plus_class.plus}, T --> T --> T)
                         $ t1 $ t2)
                     (map (curry (op $) (Const (@{const_name single},
                                                elem_T --> T))) ts)
    end
  | multiset_postproc _ _ _ _ t = t
*}

declaration {*
Nitpick_Model.register_term_postprocessor @{typ "'a multiset"}
    multiset_postproc
*}

hide_const (open) fold


subsection {* Naive implementation using lists *}

code_datatype multiset_of

lemma [code]:
  "{#} = multiset_of []"
  by simp

lemma [code]:
  "{#x#} = multiset_of [x]"
  by simp

lemma union_code [code]:
  "multiset_of xs + multiset_of ys = multiset_of (xs @ ys)"
  by simp

lemma [code]:
  "image_mset f (multiset_of xs) = multiset_of (map f xs)"
  by (simp add: multiset_of_map)

lemma [code]:
  "Multiset.filter f (multiset_of xs) = multiset_of (filter f xs)"
  by (simp add: multiset_of_filter)

lemma [code]:
  "multiset_of xs - multiset_of ys = multiset_of (fold remove1 ys xs)"
  by (rule sym, induct ys arbitrary: xs) (simp_all add: diff_add diff_right_commute)

lemma [code]:
  "multiset_of xs #\<inter> multiset_of ys =
    multiset_of (snd (fold (\<lambda>x (ys, zs).
      if x \<in> set ys then (remove1 x ys, x # zs) else (ys, zs)) xs (ys, [])))"
proof -
  have "\<And>zs. multiset_of (snd (fold (\<lambda>x (ys, zs).
    if x \<in> set ys then (remove1 x ys, x # zs) else (ys, zs)) xs (ys, zs))) =
      (multiset_of xs #\<inter> multiset_of ys) + multiset_of zs"
    by (induct xs arbitrary: ys)
      (auto simp add: mem_set_multiset_eq inter_add_right1 inter_add_right2 ac_simps)
  then show ?thesis by simp
qed

lemma [code]:
  "multiset_of xs #\<union> multiset_of ys =
    multiset_of (split append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, [])))"
proof -
  have "\<And>zs. multiset_of (split append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, zs))) =
      (multiset_of xs #\<union> multiset_of ys) + multiset_of zs"
    by (induct xs arbitrary: ys) (simp_all add: multiset_eq_iff)
  then show ?thesis by simp
qed

lemma [code_unfold]:
  "x \<in># multiset_of xs \<longleftrightarrow> x \<in> set xs"
  by (simp add: in_multiset_of)

lemma [code]:
  "count (multiset_of xs) x = fold (\<lambda>y. if x = y then Suc else id) xs 0"
proof -
  have "\<And>n. fold (\<lambda>y. if x = y then Suc else id) xs n = count (multiset_of xs) x + n"
    by (induct xs) simp_all
  then show ?thesis by simp
qed

lemma [code]:
  "set_of (multiset_of xs) = set xs"
  by simp

lemma [code]:
  "sorted_list_of_multiset (multiset_of xs) = sort xs"
  by (induct xs) simp_all

lemma [code]: -- {* not very efficient, but representation-ignorant! *}
  "multiset_of_set A = multiset_of (sorted_list_of_set A)"
  apply (cases "finite A")
  apply simp_all
  apply (induct A rule: finite_induct)
  apply (simp_all add: union_commute)
  done

lemma [code]:
  "mcard (multiset_of xs) = length xs"
  by (simp add: mcard_multiset_of)

fun ms_lesseq_impl :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool option" where
  "ms_lesseq_impl [] ys = Some (ys \<noteq> [])"
| "ms_lesseq_impl (Cons x xs) ys = (case List.extract (op = x) ys of
     None \<Rightarrow> None
   | Some (ys1,_,ys2) \<Rightarrow> ms_lesseq_impl xs (ys1 @ ys2))"

lemma ms_lesseq_impl: "(ms_lesseq_impl xs ys = None \<longleftrightarrow> \<not> multiset_of xs \<le> multiset_of ys) \<and>
  (ms_lesseq_impl xs ys = Some True \<longleftrightarrow> multiset_of xs < multiset_of ys) \<and>
  (ms_lesseq_impl xs ys = Some False \<longrightarrow> multiset_of xs = multiset_of ys)"
proof (induct xs arbitrary: ys)
  case (Nil ys)
  show ?case by (auto simp: mset_less_empty_nonempty)
next
  case (Cons x xs ys)
  show ?case
  proof (cases "List.extract (op = x) ys")
    case None
    hence x: "x \<notin> set ys" by (simp add: extract_None_iff)
    {
      assume "multiset_of (x # xs) \<le> multiset_of ys"
      from set_of_mono[OF this] x have False by simp
    } note nle = this
    moreover
    {
      assume "multiset_of (x # xs) < multiset_of ys"
      hence "multiset_of (x # xs) \<le> multiset_of ys" by auto
      from nle[OF this] have False .
    }
    ultimately show ?thesis using None by auto
  next
    case (Some res)
    obtain ys1 y ys2 where res: "res = (ys1,y,ys2)" by (cases res, auto)
    note Some = Some[unfolded res]
    from extract_SomeE[OF Some] have "ys = ys1 @ x # ys2" by simp
    hence id: "multiset_of ys = multiset_of (ys1 @ ys2) + {#x#}"
      by (auto simp: ac_simps)
    show ?thesis unfolding ms_lesseq_impl.simps
      unfolding Some option.simps split
      unfolding id
      using Cons[of "ys1 @ ys2"]
      unfolding mset_le_def mset_less_def by auto
  qed
qed

lemma [code]: "multiset_of xs \<le> multiset_of ys \<longleftrightarrow> ms_lesseq_impl xs ys \<noteq> None"
  using ms_lesseq_impl[of xs ys] by (cases "ms_lesseq_impl xs ys", auto)

lemma [code]: "multiset_of xs < multiset_of ys \<longleftrightarrow> ms_lesseq_impl xs ys = Some True"
  using ms_lesseq_impl[of xs ys] by (cases "ms_lesseq_impl xs ys", auto)

instantiation multiset :: (equal) equal
begin

definition
  [code del]: "HOL.equal A (B :: 'a multiset) \<longleftrightarrow> A = B"
lemma [code]: "HOL.equal (multiset_of xs) (multiset_of ys) \<longleftrightarrow> ms_lesseq_impl xs ys = Some False"
  unfolding equal_multiset_def
  using ms_lesseq_impl[of xs ys] by (cases "ms_lesseq_impl xs ys", auto)

instance
  by default (simp add: equal_multiset_def)
end

lemma [code]:
  "msetsum (multiset_of xs) = listsum xs"
  by (induct xs) (simp_all add: add.commute)

lemma [code]:
  "msetprod (multiset_of xs) = fold times xs 1"
proof -
  have "\<And>x. fold times xs x = msetprod (multiset_of xs) * x"
    by (induct xs) (simp_all add: mult.assoc)
  then show ?thesis by simp
qed

lemma [code]:
  "size = mcard"
  by (fact size_eq_mcard)

text {*
  Exercise for the casual reader: add implementations for @{const le_multiset}
  and @{const less_multiset} (multiset order).
*}

text {* Quickcheck generators *}

definition (in term_syntax)
  msetify :: "'a\<Colon>typerep list \<times> (unit \<Rightarrow> Code_Evaluation.term)
    \<Rightarrow> 'a multiset \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  [code_unfold]: "msetify xs = Code_Evaluation.valtermify multiset_of {\<cdot>} xs"

notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation multiset :: (random) random
begin

definition
  "Quickcheck_Random.random i = Quickcheck_Random.random i \<circ>\<rightarrow> (\<lambda>xs. Pair (msetify xs))"

instance ..

end

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation multiset :: (full_exhaustive) full_exhaustive
begin

definition full_exhaustive_multiset :: "('a multiset \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "full_exhaustive_multiset f i = Quickcheck_Exhaustive.full_exhaustive (\<lambda>xs. f (msetify xs)) i"

instance ..

end

hide_const (open) msetify


subsection {* BNF setup *}

definition rel_mset where
  "rel_mset R X Y \<longleftrightarrow> (\<exists>xs ys. multiset_of xs = X \<and> multiset_of ys = Y \<and> list_all2 R xs ys)"

lemma multiset_of_zip_take_Cons_drop_twice:
  assumes "length xs = length ys" "j \<le> length xs"
  shows "multiset_of (zip (take j xs @ x # drop j xs) (take j ys @ y # drop j ys)) =
    multiset_of (zip xs ys) + {#(x, y)#}"
using assms
proof (induct xs ys arbitrary: x y j rule: list_induct2)
  case Nil
  thus ?case
    by simp
next
  case (Cons x xs y ys)
  thus ?case
  proof (cases "j = 0")
    case True
    thus ?thesis
      by simp
  next
    case False
    then obtain k where k: "j = Suc k"
      by (case_tac j) simp
    hence "k \<le> length xs"
      using Cons.prems by auto
    hence "multiset_of (zip (take k xs @ x # drop k xs) (take k ys @ y # drop k ys)) =
      multiset_of (zip xs ys) + {#(x, y)#}"
      by (rule Cons.hyps(2))
    thus ?thesis
      unfolding k by (auto simp: add.commute union_lcomm)
  qed
qed

lemma ex_multiset_of_zip_left:
  assumes "length xs = length ys" "multiset_of xs' = multiset_of xs"
  shows "\<exists>ys'. length ys' = length xs' \<and> multiset_of (zip xs' ys') = multiset_of (zip xs ys)"
using assms
proof (induct xs ys arbitrary: xs' rule: list_induct2)
  case Nil
  thus ?case
    by auto
next
  case (Cons x xs y ys xs')
  obtain j where j_len: "j < length xs'" and nth_j: "xs' ! j = x"
    by (metis Cons.prems in_set_conv_nth list.set_intros(1) multiset_of_eq_setD)

  def xsa \<equiv> "take j xs' @ drop (Suc j) xs'"
  have "multiset_of xs' = {#x#} + multiset_of xsa"
    unfolding xsa_def using j_len nth_j
    by (metis (no_types) ab_semigroup_add_class.add_ac(1) append_take_drop_id Cons_nth_drop_Suc
      multiset_of.simps(2) union_code union_commute)
  hence ms_x: "multiset_of xsa = multiset_of xs"
    by (metis Cons.prems add.commute add_right_imp_eq multiset_of.simps(2))
  then obtain ysa where
    len_a: "length ysa = length xsa" and ms_a: "multiset_of (zip xsa ysa) = multiset_of (zip xs ys)"
    using Cons.hyps(2) by blast

  def ys' \<equiv> "take j ysa @ y # drop j ysa"
  have xs': "xs' = take j xsa @ x # drop j xsa"
    using ms_x j_len nth_j Cons.prems xsa_def
    by (metis append_eq_append_conv append_take_drop_id diff_Suc_Suc Cons_nth_drop_Suc length_Cons
      length_drop mcard_multiset_of)
  have j_len': "j \<le> length xsa"
    using j_len xs' xsa_def
    by (metis add_Suc_right append_take_drop_id length_Cons length_append less_eq_Suc_le not_less)
  have "length ys' = length xs'"
    unfolding ys'_def using Cons.prems len_a ms_x
    by (metis add_Suc_right append_take_drop_id length_Cons length_append multiset_of_eq_length)
  moreover have "multiset_of (zip xs' ys') = multiset_of (zip (x # xs) (y # ys))"
    unfolding xs' ys'_def
    by (rule trans[OF multiset_of_zip_take_Cons_drop_twice])
      (auto simp: len_a ms_a j_len' add.commute)
  ultimately show ?case
    by blast
qed

lemma list_all2_reorder_left_invariance:
  assumes rel: "list_all2 R xs ys" and ms_x: "multiset_of xs' = multiset_of xs"
  shows "\<exists>ys'. list_all2 R xs' ys' \<and> multiset_of ys' = multiset_of ys"
proof -
  have len: "length xs = length ys"
    using rel list_all2_conv_all_nth by auto
  obtain ys' where
    len': "length xs' = length ys'" and ms_xy: "multiset_of (zip xs' ys') = multiset_of (zip xs ys)"
    using len ms_x by (metis ex_multiset_of_zip_left)
  have "list_all2 R xs' ys'"
    using assms(1) len' ms_xy unfolding list_all2_iff by (blast dest: multiset_of_eq_setD)
  moreover have "multiset_of ys' = multiset_of ys"
    using len len' ms_xy map_snd_zip multiset_of_map by metis
  ultimately show ?thesis
    by blast
qed

lemma ex_multiset_of: "\<exists>xs. multiset_of xs = X"
  by (induct X) (simp, metis multiset_of.simps(2))

bnf "'a multiset"
  map: image_mset
  sets: set_of
  bd: natLeq
  wits: "{#}"
  rel: rel_mset
proof -
  show "image_mset id = id"
    by (rule image_mset.id)
next
  show "\<And>f g. image_mset (g \<circ> f) = image_mset g \<circ> image_mset f"
    unfolding comp_def by (rule ext) (simp add: image_mset.compositionality comp_def)
next
  fix X :: "'a multiset"
  show "\<And>f g. (\<And>z. z \<in> set_of X \<Longrightarrow> f z = g z) \<Longrightarrow> image_mset f X = image_mset g X"
    by (induct X, (simp (no_asm))+,
      metis One_nat_def Un_iff count_single mem_set_of_iff set_of_union zero_less_Suc)
next
  show "\<And>f. set_of \<circ> image_mset f = op ` f \<circ> set_of"
    by auto
next
  show "card_order natLeq"
    by (rule natLeq_card_order)
next
  show "BNF_Cardinal_Arithmetic.cinfinite natLeq"
    by (rule natLeq_cinfinite)
next
  show "\<And>X. ordLeq3 (card_of (set_of X)) natLeq"
    by transfer
      (auto intro!: ordLess_imp_ordLeq simp: finite_iff_ordLess_natLeq[symmetric] multiset_def)
next
  show "\<And>R S. rel_mset R OO rel_mset S \<le> rel_mset (R OO S)"
    unfolding rel_mset_def[abs_def] OO_def
    apply clarify
    apply (rename_tac X Z Y xs ys' ys zs)
    apply (drule_tac xs = ys' and ys = zs and xs' = ys in list_all2_reorder_left_invariance)
    by (auto intro: list_all2_trans)
next
  show "\<And>R. rel_mset R =
    (BNF_Def.Grp {x. set_of x \<subseteq> {(x, y). R x y}} (image_mset fst))\<inverse>\<inverse> OO
    BNF_Def.Grp {x. set_of x \<subseteq> {(x, y). R x y}} (image_mset snd)"
    unfolding rel_mset_def[abs_def] BNF_Def.Grp_def OO_def
    apply (rule ext)+
    apply auto
     apply (rule_tac x = "multiset_of (zip xs ys)" in exI)
     apply auto[1]
        apply (metis list_all2_lengthD map_fst_zip multiset_of_map)
       apply (auto simp: list_all2_iff)[1]
      apply (metis list_all2_lengthD map_snd_zip multiset_of_map)
     apply (auto simp: list_all2_iff)[1]
    apply (rename_tac XY)
    apply (cut_tac X = XY in ex_multiset_of)
    apply (erule exE)
    apply (rename_tac xys)
    apply (rule_tac x = "map fst xys" in exI)
    apply (auto simp: multiset_of_map)
    apply (rule_tac x = "map snd xys" in exI)
    by (auto simp: multiset_of_map list_all2I subset_eq zip_map_fst_snd)
next
  show "\<And>z. z \<in> set_of {#} \<Longrightarrow> False"
    by auto
qed

inductive rel_mset' where
  Zero[intro]: "rel_mset' R {#} {#}"
| Plus[intro]: "\<lbrakk>R a b; rel_mset' R M N\<rbrakk> \<Longrightarrow> rel_mset' R (M + {#a#}) (N + {#b#})"

lemma rel_mset_Zero: "rel_mset R {#} {#}"
unfolding rel_mset_def Grp_def by auto

declare multiset.count[simp]
declare Abs_multiset_inverse[simp]
declare multiset.count_inverse[simp]
declare union_preserves_multiset[simp]

lemma rel_mset_Plus:
assumes ab: "R a b" and MN: "rel_mset R M N"
shows "rel_mset R (M + {#a#}) (N + {#b#})"
proof-
  {fix y assume "R a b" and "set_of y \<subseteq> {(x, y). R x y}"
   hence "\<exists>ya. image_mset fst y + {#a#} = image_mset fst ya \<and>
               image_mset snd y + {#b#} = image_mset snd ya \<and>
               set_of ya \<subseteq> {(x, y). R x y}"
   apply(intro exI[of _ "y + {#(a,b)#}"]) by auto
  }
  thus ?thesis
  using assms
  unfolding multiset.rel_compp_Grp Grp_def by blast
qed

lemma rel_mset'_imp_rel_mset:
"rel_mset' R M N \<Longrightarrow> rel_mset R M N"
apply(induct rule: rel_mset'.induct)
using rel_mset_Zero rel_mset_Plus by auto

lemma mcard_image_mset[simp]: "mcard (image_mset f M) = mcard M"
  unfolding size_eq_mcard[symmetric] by (rule size_image_mset)

lemma rel_mset_mcard:
  assumes "rel_mset R M N"
  shows "mcard M = mcard N"
using assms unfolding multiset.rel_compp_Grp Grp_def by auto

lemma multiset_induct2[case_names empty addL addR]:
assumes empty: "P {#} {#}"
and addL: "\<And>M N a. P M N \<Longrightarrow> P (M + {#a#}) N"
and addR: "\<And>M N a. P M N \<Longrightarrow> P M (N + {#a#})"
shows "P M N"
apply(induct N rule: multiset_induct)
  apply(induct M rule: multiset_induct, rule empty, erule addL)
  apply(induct M rule: multiset_induct, erule addR, erule addR)
done

lemma multiset_induct2_mcard[consumes 1, case_names empty add]:
assumes c: "mcard M = mcard N"
and empty: "P {#} {#}"
and add: "\<And>M N a b. P M N \<Longrightarrow> P (M + {#a#}) (N + {#b#})"
shows "P M N"
using c proof(induct M arbitrary: N rule: measure_induct_rule[of mcard])
  case (less M)  show ?case
  proof(cases "M = {#}")
    case True hence "N = {#}" using less.prems by auto
    thus ?thesis using True empty by auto
  next
    case False then obtain M1 a where M: "M = M1 + {#a#}" by (metis multi_nonempty_split)
    have "N \<noteq> {#}" using False less.prems by auto
    then obtain N1 b where N: "N = N1 + {#b#}" by (metis multi_nonempty_split)
    have "mcard M1 = mcard N1" using less.prems unfolding M N by auto
    thus ?thesis using M N less.hyps add by auto
  qed
qed

lemma msed_map_invL:
assumes "image_mset f (M + {#a#}) = N"
shows "\<exists>N1. N = N1 + {#f a#} \<and> image_mset f M = N1"
proof-
  have "f a \<in># N"
  using assms multiset.set_map[of f "M + {#a#}"] by auto
  then obtain N1 where N: "N = N1 + {#f a#}" using multi_member_split by metis
  have "image_mset f M = N1" using assms unfolding N by simp
  thus ?thesis using N by blast
qed

lemma msed_map_invR:
assumes "image_mset f M = N + {#b#}"
shows "\<exists>M1 a. M = M1 + {#a#} \<and> f a = b \<and> image_mset f M1 = N"
proof-
  obtain a where a: "a \<in># M" and fa: "f a = b"
  using multiset.set_map[of f M] unfolding assms
  by (metis image_iff mem_set_of_iff union_single_eq_member)
  then obtain M1 where M: "M = M1 + {#a#}" using multi_member_split by metis
  have "image_mset f M1 = N" using assms unfolding M fa[symmetric] by simp
  thus ?thesis using M fa by blast
qed

lemma msed_rel_invL:
assumes "rel_mset R (M + {#a#}) N"
shows "\<exists>N1 b. N = N1 + {#b#} \<and> R a b \<and> rel_mset R M N1"
proof-
  obtain K where KM: "image_mset fst K = M + {#a#}"
  and KN: "image_mset snd K = N" and sK: "set_of K \<subseteq> {(a, b). R a b}"
  using assms
  unfolding multiset.rel_compp_Grp Grp_def by auto
  obtain K1 ab where K: "K = K1 + {#ab#}" and a: "fst ab = a"
  and K1M: "image_mset fst K1 = M" using msed_map_invR[OF KM] by auto
  obtain N1 where N: "N = N1 + {#snd ab#}" and K1N1: "image_mset snd K1 = N1"
  using msed_map_invL[OF KN[unfolded K]] by auto
  have Rab: "R a (snd ab)" using sK a unfolding K by auto
  have "rel_mset R M N1" using sK K1M K1N1
  unfolding K multiset.rel_compp_Grp Grp_def by auto
  thus ?thesis using N Rab by auto
qed

lemma msed_rel_invR:
assumes "rel_mset R M (N + {#b#})"
shows "\<exists>M1 a. M = M1 + {#a#} \<and> R a b \<and> rel_mset R M1 N"
proof-
  obtain K where KN: "image_mset snd K = N + {#b#}"
  and KM: "image_mset fst K = M" and sK: "set_of K \<subseteq> {(a, b). R a b}"
  using assms
  unfolding multiset.rel_compp_Grp Grp_def by auto
  obtain K1 ab where K: "K = K1 + {#ab#}" and b: "snd ab = b"
  and K1N: "image_mset snd K1 = N" using msed_map_invR[OF KN] by auto
  obtain M1 where M: "M = M1 + {#fst ab#}" and K1M1: "image_mset fst K1 = M1"
  using msed_map_invL[OF KM[unfolded K]] by auto
  have Rab: "R (fst ab) b" using sK b unfolding K by auto
  have "rel_mset R M1 N" using sK K1N K1M1
  unfolding K multiset.rel_compp_Grp Grp_def by auto
  thus ?thesis using M Rab by auto
qed

lemma rel_mset_imp_rel_mset':
assumes "rel_mset R M N"
shows "rel_mset' R M N"
using assms proof(induct M arbitrary: N rule: measure_induct_rule[of mcard])
  case (less M)
  have c: "mcard M = mcard N" using rel_mset_mcard[OF less.prems] .
  show ?case
  proof(cases "M = {#}")
    case True hence "N = {#}" using c by simp
    thus ?thesis using True rel_mset'.Zero by auto
  next
    case False then obtain M1 a where M: "M = M1 + {#a#}" by (metis multi_nonempty_split)
    obtain N1 b where N: "N = N1 + {#b#}" and R: "R a b" and ms: "rel_mset R M1 N1"
    using msed_rel_invL[OF less.prems[unfolded M]] by auto
    have "rel_mset' R M1 N1" using less.hyps[of M1 N1] ms unfolding M by simp
    thus ?thesis using rel_mset'.Plus[of R a b, OF R] unfolding M N by simp
  qed
qed

lemma rel_mset_rel_mset':
"rel_mset R M N = rel_mset' R M N"
using rel_mset_imp_rel_mset' rel_mset'_imp_rel_mset by auto

(* The main end product for rel_mset: inductive characterization *)
theorems rel_mset_induct[case_names empty add, induct pred: rel_mset] =
         rel_mset'.induct[unfolded rel_mset_rel_mset'[symmetric]]


subsection {* Size setup *}

lemma multiset_size_o_map: "size_multiset g \<circ> image_mset f = size_multiset (g \<circ> f)"
  unfolding o_apply by (rule ext) (induct_tac, auto)

setup {*
BNF_LFP_Size.register_size_global @{type_name multiset} @{const_name size_multiset}
  @{thms size_multiset_empty size_multiset_single size_multiset_union size_empty size_single
    size_union}
  @{thms multiset_size_o_map}
*}

hide_const (open) wcount

end
