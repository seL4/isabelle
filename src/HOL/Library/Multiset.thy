(*  Title:      HOL/Library/Multiset.thy
    Author:     Tobias Nipkow, Markus Wenzel, Lawrence C Paulson, Norbert Voelker
*)

header {* (Finite) multisets *}

theory Multiset
imports Main DAList
begin

subsection {* The type of multisets *}

definition "multiset = {f :: 'a => nat. finite {x. f x > 0}}"

typedef (open) 'a multiset = "multiset :: ('a => nat) set"
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

instantiation multiset :: (type) minus
begin

lift_definition minus_multiset :: "'a multiset => 'a multiset => 'a multiset" is "\<lambda> M N. \<lambda>a. M a - N a"
by (rule diff_preserves_multiset)
 
instance ..

end

lemma count_diff [simp]: "count (M - N) a = count M a - count N a"
  by (simp add: minus_multiset.rep_eq)

lemma diff_empty [simp]: "M - {#} = M \<and> {#} - M = {#}"
by(simp add: multiset_eq_iff)

lemma diff_cancel[simp]: "A - A = {#}"
by (rule multiset_eqI) simp

lemma diff_union_cancelR [simp]: "M + N - N = (M::'a multiset)"
by(simp add: multiset_eq_iff)

lemma diff_union_cancelL [simp]: "N + M - N = (M::'a multiset)"
by(simp add: multiset_eq_iff)

lemma insert_DiffM:
  "x \<in># M \<Longrightarrow> {#x#} + (M - {#x#}) = M"
  by (clarsimp simp: multiset_eq_iff)

lemma insert_DiffM2 [simp]:
  "x \<in># M \<Longrightarrow> M - {#x#} + {#x#} = M"
  by (clarsimp simp: multiset_eq_iff)

lemma diff_right_commute:
  "(M::'a multiset) - N - Q = M - Q - N"
  by (auto simp add: multiset_eq_iff)

lemma diff_add:
  "(M::'a multiset) - (N + Q) = M - N - Q"
by (simp add: multiset_eq_iff)

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
  by (auto simp add: add_assoc add_commute [of "{#b#}"])
    (drule sym, simp add: add_assoc [symmetric])
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


subsubsection {* Pointwise ordering induced by count *}

instantiation multiset :: (type) ordered_ab_semigroup_add_imp_le
begin

lift_definition less_eq_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" is "\<lambda> A B. (\<forall>a. A a \<le> B a)"
by simp
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

subsubsection {* Size *}

instantiation multiset :: (type) size
begin

definition size_def:
  "size M = setsum (count M) (set_of M)"

instance ..

end

lemma size_empty [simp]: "size {#} = 0"
by (simp add: size_def)

lemma size_single [simp]: "size {#b#} = 1"
by (simp add: size_def)

lemma setsum_count_Int:
  "finite A ==> setsum (count N) (A \<inter> set_of N) = setsum (count N) A"
apply (induct rule: finite_induct)
 apply simp
apply (simp add: Int_insert_left set_of_def)
done

lemma size_union [simp]: "size (M + N::'a multiset) = size M + size N"
apply (unfold size_def)
apply (subgoal_tac "count (M + N) = (\<lambda>a. count M a + count N a)")
 prefer 2
 apply (rule ext, simp)
apply (simp (no_asm_simp) add: setsum_Un_nat setsum_addf setsum_count_Int)
apply (subst Int_commute)
apply (simp (no_asm_simp) add: setsum_count_Int)
done

lemma size_eq_0_iff_empty [iff]: "(size M = 0) = (M = {#})"
by (auto simp add: size_def multiset_eq_iff)

lemma nonempty_has_size: "(S \<noteq> {#}) = (0 < size S)"
by (metis gr0I gr_implies_not0 size_empty size_eq_0_iff_empty)

lemma size_eq_Suc_imp_elem: "size M = Suc n ==> \<exists>a. a :# M"
apply (unfold size_def)
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

lemma multiset_cases [cases type, case_names empty add]:
assumes em:  "M = {#} \<Longrightarrow> P"
assumes add: "\<And>N x. M = N + {#x#} \<Longrightarrow> P"
shows "P"
using assms by (induct M) simp_all

lemma multi_member_split: "x \<in># M \<Longrightarrow> \<exists>A. M = A + {#x#}"
by (rule_tac x="M - {#x#}" in exI, simp)

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

text {* Well-foundedness of proper subset operator: *}

text {* proper multiset subset *}

definition
  mset_less_rel :: "('a multiset * 'a multiset) set" where
  "mset_less_rel = {(A,B). A < B}"

lemma multiset_add_sub_el_shuffle: 
  assumes "c \<in># B" and "b \<noteq> c" 
  shows "B - {#c#} + {#b#} = B + {#b#} - {#c#}"
proof -
  from `c \<in># B` obtain A where B: "B = A + {#c#}" 
    by (blast dest: multi_member_split)
  have "A + {#b#} = A + {#b#} + {#c#} - {#c#}" by simp
  then have "A + {#b#} = A + {#c#} + {#b#} - {#c#}" 
    by (simp add: add_ac)
  then show ?thesis using B by simp
qed

lemma wf_mset_less_rel: "wf mset_less_rel"
apply (unfold mset_less_rel_def)
apply (rule wf_measure [THEN wf_subset, where f1=size])
apply (clarsimp simp: measure_def inv_image_def mset_less_size)
done

text {* The induction rules: *}

lemma full_multiset_induct [case_names less]:
assumes ih: "\<And>B. \<forall>(A::'a multiset). A < B \<longrightarrow> P A \<Longrightarrow> P B"
shows "P B"
apply (rule wf_mset_less_rel [THEN wf_induct])
apply (rule ih, auto simp: mset_less_rel_def)
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


subsection {* Alternative representations *}

subsubsection {* Lists *}

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

lemma multiset_of_append [simp]:
  "multiset_of (xs @ ys) = multiset_of xs + multiset_of ys"
  by (induct xs arbitrary: ys) (auto simp: add_ac)

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
  by (induct xs) (auto simp: add_ac)

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
using assms
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then have "x \<in># multiset_of ys" by (simp add: union_single_eq_member)
  then have "x \<in> set ys" by (simp add: in_multiset_in_set)
  from Cons.prems [symmetric] have "multiset_of xs = multiset_of (remove1 x ys)"
    by simp
  with Cons.hyps have "length xs = length (remove1 x ys)" .
  with `x \<in> set ys` show ?case
    by (auto simp add: length_remove1 dest: length_pos_if_in_set)
qed

lemma multiset_of_eq_length_filter:
  assumes "multiset_of xs = multiset_of ys"
  shows "length (filter (\<lambda>x. z = x) xs) = length (filter (\<lambda>y. z = y) ys)"
proof (cases "z \<in># multiset_of xs")
  case False
  moreover have "\<not> z \<in># multiset_of ys" using assms False by simp
  ultimately show ?thesis by (simp add: count_multiset_of_length_filter)
next
  case True
  moreover have "z \<in># multiset_of ys" using assms True by simp
  show ?thesis using assms
  proof (induct xs arbitrary: ys)
    case Nil then show ?case by simp
  next
    case (Cons x xs)
    from `multiset_of (x # xs) = multiset_of ys` [symmetric]
      have *: "multiset_of xs = multiset_of (remove1 x ys)"
      and "x \<in> set ys"
      by (auto simp add: mem_set_multiset_eq)
    from * have "length (filter (\<lambda>x. z = x) xs) = length (filter (\<lambda>y. z = y) (remove1 x ys))" by (rule Cons.hyps)
    moreover from `x \<in> set ys` have "length (filter (\<lambda>y. x = y) ys) > 0" by (simp add: filter_empty_conv)
    ultimately show ?case using `x \<in> set ys`
      by (simp add: filter_remove1) (auto simp add: length_remove1)
  qed
qed

lemma fold_multiset_equiv:
  assumes f: "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> f x \<circ> f y = f y \<circ> f x"
    and equiv: "multiset_of xs = multiset_of ys"
  shows "fold f xs = fold f ys"
using f equiv [symmetric]
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then have *: "set ys = set (x # xs)" by (blast dest: multiset_of_eq_setD)
  have "\<And>x y. x \<in> set ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x \<circ> f y = f y \<circ> f x" 
    by (rule Cons.prems(1)) (simp_all add: *)
  moreover from * have "x \<in> set ys" by simp
  ultimately have "fold f ys = fold f (remove1 x ys) \<circ> f x" by (fact fold_remove1_split)
  moreover from Cons.prems have "fold f xs = fold f (remove1 x ys)" by (auto intro: Cons.hyps)
  ultimately show ?case by simp
qed

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
      apply (subst add_assoc)
      apply (subst add_commute [of "{#v#}" "{#x#}"])
      apply (subst add_assoc [symmetric])
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


subsubsection {* Association lists -- including code generation *}

text {* Preliminaries *}

text {* Raw operations on lists *}

definition join_raw :: "('key \<Rightarrow> 'val \<times> 'val \<Rightarrow> 'val) \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
where
  "join_raw f xs ys = foldr (\<lambda>(k, v). map_default k v (%v'. f k (v', v))) ys xs"

lemma join_raw_Nil [simp]:
  "join_raw f xs [] = xs"
by (simp add: join_raw_def)

lemma join_raw_Cons [simp]:
  "join_raw f xs ((k, v) # ys) = map_default k v (%v'. f k (v', v)) (join_raw f xs ys)"
by (simp add: join_raw_def)

lemma map_of_join_raw:
  assumes "distinct (map fst ys)"
  shows "map_of (join_raw f xs ys) x = (case map_of xs x of None => map_of ys x | Some v =>
    (case map_of ys x of None => Some v | Some v' => Some (f x (v, v'))))"
using assms
apply (induct ys)
apply (auto simp add: map_of_map_default split: option.split)
apply (metis map_of_eq_None_iff option.simps(2) weak_map_of_SomeI)
by (metis Some_eq_map_of_iff map_of_eq_None_iff option.simps(2))

lemma distinct_join_raw:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (join_raw f xs ys))"
using assms
proof (induct ys)
  case (Cons y ys)
  thus ?case by (cases y) (simp add: distinct_map_default)
qed auto

definition
  "subtract_entries_raw xs ys = foldr (%(k, v). AList.map_entry k (%v'. v' - v)) ys xs"

lemma map_of_subtract_entries_raw:
  assumes "distinct (map fst ys)"
  shows "map_of (subtract_entries_raw xs ys) x = (case map_of xs x of None => None | Some v =>
    (case map_of ys x of None => Some v | Some v' => Some (v - v')))"
using assms unfolding subtract_entries_raw_def
apply (induct ys)
apply auto
apply (simp split: option.split)
apply (simp add: map_of_map_entry)
apply (auto split: option.split)
apply (metis map_of_eq_None_iff option.simps(3) option.simps(4))
by (metis map_of_eq_None_iff option.simps(4) option.simps(5))

lemma distinct_subtract_entries_raw:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (subtract_entries_raw xs ys))"
using assms
unfolding subtract_entries_raw_def by (induct ys) (auto simp add: distinct_map_entry)

text {* Operations on alists with distinct keys *}

lift_definition join :: "('a \<Rightarrow> 'b \<times> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) alist \<Rightarrow> ('a, 'b) alist \<Rightarrow> ('a, 'b) alist" 
is join_raw
by (simp add: distinct_join_raw)

lift_definition subtract_entries :: "('a, ('b :: minus)) alist \<Rightarrow> ('a, 'b) alist \<Rightarrow> ('a, 'b) alist"
is subtract_entries_raw 
by (simp add: distinct_subtract_entries_raw)

text {* Implementing multisets by means of association lists *}

definition count_of :: "('a \<times> nat) list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count_of xs x = (case map_of xs x of None \<Rightarrow> 0 | Some n \<Rightarrow> n)"

lemma count_of_multiset:
  "count_of xs \<in> multiset"
proof -
  let ?A = "{x::'a. 0 < (case map_of xs x of None \<Rightarrow> 0\<Colon>nat | Some (n\<Colon>nat) \<Rightarrow> n)}"
  have "?A \<subseteq> dom (map_of xs)"
  proof
    fix x
    assume "x \<in> ?A"
    then have "0 < (case map_of xs x of None \<Rightarrow> 0\<Colon>nat | Some (n\<Colon>nat) \<Rightarrow> n)" by simp
    then have "map_of xs x \<noteq> None" by (cases "map_of xs x") auto
    then show "x \<in> dom (map_of xs)" by auto
  qed
  with finite_dom_map_of [of xs] have "finite ?A"
    by (auto intro: finite_subset)
  then show ?thesis
    by (simp add: count_of_def fun_eq_iff multiset_def)
qed

lemma count_simps [simp]:
  "count_of [] = (\<lambda>_. 0)"
  "count_of ((x, n) # xs) = (\<lambda>y. if x = y then n else count_of xs y)"
  by (simp_all add: count_of_def fun_eq_iff)

lemma count_of_empty:
  "x \<notin> fst ` set xs \<Longrightarrow> count_of xs x = 0"
  by (induct xs) (simp_all add: count_of_def)

lemma count_of_filter:
  "count_of (List.filter (P \<circ> fst) xs) x = (if P x then count_of xs x else 0)"
  by (induct xs) auto

lemma count_of_map_default [simp]:
  "count_of (map_default x b (%x. x + b) xs) y = (if x = y then count_of xs x + b else count_of xs y)"
unfolding count_of_def by (simp add: map_of_map_default split: option.split)

lemma count_of_join_raw:
  "distinct (map fst ys) ==> count_of xs x + count_of ys x = count_of (join_raw (%x (x, y). x + y) xs ys) x"
unfolding count_of_def by (simp add: map_of_join_raw split: option.split)

lemma count_of_subtract_entries_raw:
  "distinct (map fst ys) ==> count_of xs x - count_of ys x = count_of (subtract_entries_raw xs ys) x"
unfolding count_of_def by (simp add: map_of_subtract_entries_raw split: option.split)

text {* Code equations for multiset operations *}

definition Bag :: "('a, nat) alist \<Rightarrow> 'a multiset" where
  "Bag xs = Abs_multiset (count_of (DAList.impl_of xs))"

code_datatype Bag

lemma count_Bag [simp, code]:
  "count (Bag xs) = count_of (DAList.impl_of xs)"
  by (simp add: Bag_def count_of_multiset Abs_multiset_inverse)

lemma Mempty_Bag [code]:
  "{#} = Bag (DAList.empty)"
  by (simp add: multiset_eq_iff alist.Alist_inverse DAList.empty_def)

lemma single_Bag [code]:
  "{#x#} = Bag (DAList.update x 1 DAList.empty)"
  by (simp add: multiset_eq_iff alist.Alist_inverse update.rep_eq empty.rep_eq)

lemma union_Bag [code]:
  "Bag xs + Bag ys = Bag (join (\<lambda>x (n1, n2). n1 + n2) xs ys)"
by (rule multiset_eqI) (simp add: count_of_join_raw alist.Alist_inverse distinct_join_raw join_def)

lemma minus_Bag [code]:
  "Bag xs - Bag ys = Bag (subtract_entries xs ys)"
by (rule multiset_eqI)
  (simp add: count_of_subtract_entries_raw alist.Alist_inverse distinct_subtract_entries_raw subtract_entries_def)

lemma filter_Bag [code]:
  "Multiset.filter P (Bag xs) = Bag (DAList.filter (P \<circ> fst) xs)"
by (rule multiset_eqI) (simp add: count_of_filter DAList.filter.rep_eq)

lemma mset_less_eq_Bag [code]:
  "Bag xs \<le> A \<longleftrightarrow> (\<forall>(x, n) \<in> set (DAList.impl_of xs). count_of (DAList.impl_of xs) x \<le> count A x)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs
    by (auto simp add: mset_le_def)
next
  assume ?rhs
  show ?lhs
  proof (rule mset_less_eqI)
    fix x
    from `?rhs` have "count_of (DAList.impl_of xs) x \<le> count A x"
      by (cases "x \<in> fst ` set (DAList.impl_of xs)") (auto simp add: count_of_empty)
    then show "count (Bag xs) x \<le> count A x"
      by (simp add: mset_le_def)
  qed
qed

instantiation multiset :: (equal) equal
begin

definition
  [code]: "HOL.equal A B \<longleftrightarrow> (A::'a multiset) \<le> B \<and> B \<le> A"

instance
  by default (simp add: equal_multiset_def eq_iff)

end

text {* Quickcheck generators *}

definition (in term_syntax)
  bagify :: "('a\<Colon>typerep, nat) alist \<times> (unit \<Rightarrow> Code_Evaluation.term)
    \<Rightarrow> 'a multiset \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  [code_unfold]: "bagify xs = Code_Evaluation.valtermify Bag {\<cdot>} xs"

notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation multiset :: (random) random
begin

definition
  "Quickcheck.random i = Quickcheck.random i \<circ>\<rightarrow> (\<lambda>xs. Pair (bagify xs))"

instance ..

end

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation multiset :: (exhaustive) exhaustive
begin

definition exhaustive_multiset :: "('a multiset => (bool * term list) option) => code_numeral => (bool * term list) option"
where
  "exhaustive_multiset f i = Quickcheck_Exhaustive.exhaustive (%xs. f (Bag xs)) i"

instance ..

end

instantiation multiset :: (full_exhaustive) full_exhaustive
begin

definition full_exhaustive_multiset :: "('a multiset * (unit => term) => (bool * term list) option) => code_numeral => (bool * term list) option"
where
  "full_exhaustive_multiset f i = Quickcheck_Exhaustive.full_exhaustive (%xs. f (bagify xs)) i"

instance ..

end

hide_const (open) bagify


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
      with N have n: "N = K' + K + {#a#}" by (simp add: add_ac)

      assume "M0 = K' + {#a'#}"
      with r have "?R (K' + K) M0" by blast
      with n have ?case1 by simp then show ?thesis ..
    qed
  qed
qed

lemma all_accessible: "wf r ==> \<forall>M. M \<in> acc (mult1 r)"
proof
  let ?R = "mult1 r"
  let ?W = "acc ?R"
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
          then show "M0 + (K + {#x#}) \<in> ?W" by (simp only: add_assoc)
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
 apply (simp (no_asm_simp) add: add_assoc [symmetric])
 apply (drule_tac f = "\<lambda>M. M - {#a#}" in arg_cong)
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
  apply (drule_tac f = "\<lambda>M. M - {#a#}" in arg_cong, simp)
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
apply (simp (no_asm_use) add: add_assoc [symmetric] mult_def)
apply (erule trancl_trans)
apply (rule r_into_trancl)
apply (simp add: mult1_def set_of_def)
apply (rule_tac x = a in exI)
apply (rule_tac x = "I + J'" in exI)
apply (simp add: add_ac)
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
apply (simp add: add_assoc)
done

lemma union_less_mono2: "B \<subset># D ==> C + B \<subset># C + (D::'a::order multiset)"
apply (unfold less_multiset_def mult_def)
apply (erule trancl_induct)
 apply (blast intro: mult1_union)
apply (blast intro: mult1_union trancl_trans)
done

lemma union_less_mono1: "B \<subset># D ==> B + C \<subset># D + (C::'a::order multiset)"
apply (subst add_commute [of B C])
apply (subst add_commute [of D C])
apply (erule union_less_mono2)
done

lemma union_less_mono:
  "A \<subset># C ==> B \<subset># D ==> A + B \<subset># C + (D::'a::order multiset)"
  by (blast intro!: union_less_mono1 union_less_mono2 multiset_order.less_trans)

interpretation multiset_order: ordered_ab_semigroup_add plus le_multiset less_multiset
proof
qed (auto simp add: le_multiset_def intro: union_less_mono2)


subsection {* The fold combinator *}

text {*
  The intended behaviour is
  @{text "fold_mset f z {#x\<^isub>1, ..., x\<^isub>n#} = f x\<^isub>1 (\<dots> (f x\<^isub>n z)\<dots>)"}
  if @{text f} is associative-commutative. 
*}

text {*
  The graph of @{text "fold_mset"}, @{text "z"}: the start element,
  @{text "f"}: folding function, @{text "A"}: the multiset, @{text
  "y"}: the result.
*}
inductive 
  fold_msetG :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a multiset \<Rightarrow> 'b \<Rightarrow> bool" 
  for f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" 
  and z :: 'b
where
  emptyI [intro]:  "fold_msetG f z {#} z"
| insertI [intro]: "fold_msetG f z A y \<Longrightarrow> fold_msetG f z (A + {#x#}) (f x y)"

inductive_cases empty_fold_msetGE [elim!]: "fold_msetG f z {#} x"
inductive_cases insert_fold_msetGE: "fold_msetG f z (A + {#}) y" 

definition
  fold_mset :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a multiset \<Rightarrow> 'b" where
  "fold_mset f z A = (THE x. fold_msetG f z A x)"

lemma Diff1_fold_msetG:
  "fold_msetG f z (A - {#x#}) y \<Longrightarrow> x \<in># A \<Longrightarrow> fold_msetG f z A (f x y)"
apply (frule_tac x = x in fold_msetG.insertI)
apply auto
done

lemma fold_msetG_nonempty: "\<exists>x. fold_msetG f z A x"
apply (induct A)
 apply blast
apply clarsimp
apply (drule_tac x = x in fold_msetG.insertI)
apply auto
done

lemma fold_mset_empty[simp]: "fold_mset f z {#} = z"
unfolding fold_mset_def by blast

context comp_fun_commute
begin

lemma fold_msetG_insertE_aux:
  "fold_msetG f z A y \<Longrightarrow> a \<in># A \<Longrightarrow> \<exists>y'. y = f a y' \<and> fold_msetG f z (A - {#a#}) y'"
proof (induct set: fold_msetG)
  case (insertI A y x) show ?case
  proof (cases "x = a")
    assume "x = a" with insertI show ?case by auto
  next
    assume "x \<noteq> a"
    then obtain y' where y: "y = f a y'" and y': "fold_msetG f z (A - {#a#}) y'"
      using insertI by auto
    have "f x y = f a (f x y')"
      unfolding y by (rule fun_left_comm)
    moreover have "fold_msetG f z (A + {#x#} - {#a#}) (f x y')"
      using y' and `x \<noteq> a`
      by (simp add: diff_union_swap [symmetric] fold_msetG.insertI)
    ultimately show ?case by fast
  qed
qed simp

lemma fold_msetG_insertE:
  assumes "fold_msetG f z (A + {#x#}) v"
  obtains y where "v = f x y" and "fold_msetG f z A y"
using assms by (auto dest: fold_msetG_insertE_aux [where a=x])

lemma fold_msetG_determ:
  "fold_msetG f z A x \<Longrightarrow> fold_msetG f z A y \<Longrightarrow> y = x"
proof (induct arbitrary: y set: fold_msetG)
  case (insertI A y x v)
  from `fold_msetG f z (A + {#x#}) v`
  obtain y' where "v = f x y'" and "fold_msetG f z A y'"
    by (rule fold_msetG_insertE)
  from `fold_msetG f z A y'` have "y' = y" by (rule insertI)
  with `v = f x y'` show "v = f x y" by simp
qed fast

lemma fold_mset_equality: "fold_msetG f z A y \<Longrightarrow> fold_mset f z A = y"
unfolding fold_mset_def by (blast intro: fold_msetG_determ)

lemma fold_msetG_fold_mset: "fold_msetG f z A (fold_mset f z A)"
proof -
  from fold_msetG_nonempty fold_msetG_determ
  have "\<exists>!x. fold_msetG f z A x" by (rule ex_ex1I)
  then show ?thesis unfolding fold_mset_def by (rule theI')
qed

lemma fold_mset_insert:
  "fold_mset f z (A + {#x#}) = f x (fold_mset f z A)"
by (intro fold_mset_equality fold_msetG.insertI fold_msetG_fold_mset)

lemma fold_mset_commute: "f x (fold_mset f z A) = fold_mset f (f x z) A"
by (induct A) (auto simp: fold_mset_insert fun_left_comm [of x])

lemma fold_mset_single [simp]: "fold_mset f z {#x#} = f x z"
using fold_mset_insert [of z "{#}"] by simp

lemma fold_mset_union [simp]:
  "fold_mset f z (A+B) = fold_mset f (fold_mset f z A) B"
proof (induct A)
  case empty then show ?case by simp
next
  case (add A x)
  have "A + {#x#} + B = (A+B) + {#x#}" by (simp add: add_ac)
  then have "fold_mset f z (A + {#x#} + B) = f x (fold_mset f z (A + B))" 
    by (simp add: fold_mset_insert)
  also have "\<dots> = fold_mset f (fold_mset f z (A + {#x#})) B"
    by (simp add: fold_mset_commute[of x,symmetric] add fold_mset_insert)
  finally show ?case .
qed

lemma fold_mset_fusion:
  assumes "comp_fun_commute g"
  shows "(\<And>x y. h (g x y) = f x (h y)) \<Longrightarrow> h (fold_mset g w A) = fold_mset f (h w) A" (is "PROP ?P")
proof -
  interpret comp_fun_commute g by (fact assms)
  show "PROP ?P" by (induct A) auto
qed

lemma fold_mset_rec:
  assumes "a \<in># A" 
  shows "fold_mset f z A = f a (fold_mset f z (A - {#a#}))"
proof -
  from assms obtain A' where "A = A' + {#a#}"
    by (blast dest: multi_member_split)
  then show ?thesis by simp
qed

end

text {*
  A note on code generation: When defining some function containing a
  subterm @{term"fold_mset F"}, code generation is not automatic. When
  interpreting locale @{text left_commutative} with @{text F}, the
  would be code thms for @{const fold_mset} become thms like
  @{term"fold_mset F z {#} = z"} where @{text F} is not a pattern but
  contains defined symbols, i.e.\ is not a code thm. Hence a separate
  constant with its own code thms needs to be introduced for @{text
  F}. See the image operator below.
*}


subsection {* Image *}

definition image_mset :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a multiset \<Rightarrow> 'b multiset" where
  "image_mset f = fold_mset (op + o single o f) {#}"

interpretation image_fun_commute: comp_fun_commute "op + o single o f" for f
proof qed (simp add: add_ac fun_eq_iff)

lemma image_mset_empty [simp]: "image_mset f {#} = {#}"
by (simp add: image_mset_def)

lemma image_mset_single [simp]: "image_mset f {#x#} = {#f x#}"
by (simp add: image_mset_def)

lemma image_mset_insert:
  "image_mset f (M + {#a#}) = image_mset f M + {#f a#}"
by (simp add: image_mset_def add_ac)

lemma image_mset_union [simp]:
  "image_mset f (M+N) = image_mset f M + image_mset f N"
apply (induct N)
 apply simp
apply (simp add: add_assoc [symmetric] image_mset_insert)
done

lemma size_image_mset [simp]: "size (image_mset f M) = size M"
by (induct M) simp_all

lemma image_mset_is_empty_iff [simp]: "image_mset f M = {#} \<longleftrightarrow> M = {#}"
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

enriched_type image_mset: image_mset
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
      by (auto simp: add_ac)
    thus ?case by (intro exI)
  next
    assume A: "(x, y) \<in> pair_less"
    let ?A' = "{#x#} + A" and ?B' = "{#y#} + B"
    have "{#x#} + X = ?A' + Z"
      "{#y#} + Y = ?B' + Z"
      by (auto simp add: add_ac)
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
    thus "(Z + A, Z' + B) \<in> ms_strict" by (simp add:add_ac)
    thus "(Z + A, Z' + B) \<in> ms_weak" by (simp add: ms_weak_def)
  }
  from mx_or_empty
  have "(Z'' + A', Z'' + B') \<in> ms_weak" by (rule wmsI)
  thus "(Z + {#}, Z' + {#}) \<in> ms_weak" by (simp add:add_ac)
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
        (map (fn t => t RS eq_reflection) (@{thms add_ac} @ @{thms empty_neutral}))

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
  by (fact add_commute)

lemma union_assoc: "(M + N) + K = M + (N + (K::'a multiset))"
  by (fact add_assoc)

lemma union_lcomm: "M + (N + K) = N + (M + (K::'a multiset))"
  by (fact add_left_commute)

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

end
