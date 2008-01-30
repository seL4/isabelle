(*  Title:      HOL/Library/Multiset.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Markus Wenzel, Lawrence C Paulson, Norbert Voelker
*)

header {* Multisets *}

theory Multiset
imports List
begin

subsection {* The type of multisets *}

typedef 'a multiset = "{f::'a => nat. finite {x . f x > 0}}"
proof
  show "(\<lambda>x. 0::nat) \<in> ?multiset" by simp
qed

lemmas multiset_typedef [simp] =
    Abs_multiset_inverse Rep_multiset_inverse Rep_multiset
  and [simp] = Rep_multiset_inject [symmetric]

definition
  Mempty :: "'a multiset"  ("{#}") where
  "{#} = Abs_multiset (\<lambda>a. 0)"

definition
  single :: "'a => 'a multiset" where
  "single a = Abs_multiset (\<lambda>b. if b = a then 1 else 0)"

declare
  Mempty_def[code func del] single_def[code func del]

definition
  count :: "'a multiset => 'a => nat" where
  "count = Rep_multiset"

definition
  MCollect :: "'a multiset => ('a => bool) => 'a multiset" where
  "MCollect M P = Abs_multiset (\<lambda>x. if P x then Rep_multiset M x else 0)"

abbreviation
  Melem :: "'a => 'a multiset => bool"  ("(_/ :# _)" [50, 51] 50) where
  "a :# M == 0 < count M a"

notation (xsymbols) Melem (infix "\<in>#" 50)

syntax
  "_MCollect" :: "pttrn => 'a multiset => bool => 'a multiset"    ("(1{# _ : _./ _#})")
translations
  "{#x:M. P#}" == "CONST MCollect M (\<lambda>x. P)"

definition
  set_of :: "'a multiset => 'a set" where
  "set_of M = {x. x :# M}"

instantiation multiset :: (type) "{plus, minus, zero, size}" 
begin

definition
  union_def[code func del]:
  "M + N == Abs_multiset (\<lambda>a. Rep_multiset M a + Rep_multiset N a)"

definition
  diff_def: "M - N == Abs_multiset (\<lambda>a. Rep_multiset M a - Rep_multiset N a)"

definition
  Zero_multiset_def [simp]: "0 == {#}"

definition
  size_def[code func del]: "size M == setsum (count M) (set_of M)"

instance ..

end

definition
  multiset_inter :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset"  (infixl "#\<inter>" 70) where
  "multiset_inter A B = A - (A - B)"

syntax -- "Multiset Enumeration"
  "@multiset" :: "args => 'a multiset"    ("{#(_)#}")

translations
  "{#x, xs#}" == "{#x#} + {#xs#}"
  "{#x#}" == "CONST single x"


text {*
 \medskip Preservation of the representing set @{term multiset}.
*}

lemma const0_in_multiset: "(\<lambda>a. 0) \<in> multiset"
  by (simp add: multiset_def)

lemma only1_in_multiset: "(\<lambda>b. if b = a then 1 else 0) \<in> multiset"
  by (simp add: multiset_def)

lemma union_preserves_multiset:
    "M \<in> multiset ==> N \<in> multiset ==> (\<lambda>a. M a + N a) \<in> multiset"
  apply (simp add: multiset_def)
  apply (drule (1) finite_UnI)
  apply (simp del: finite_Un add: Un_def)
  done

lemma diff_preserves_multiset:
    "M \<in> multiset ==> (\<lambda>a. M a - N a) \<in> multiset"
  apply (simp add: multiset_def)
  apply (rule finite_subset)
   apply auto
  done

lemma MCollect_preserves_multiset:
    "M \<in> multiset ==> (\<lambda>x. if P x then M x else 0) \<in> multiset"
  apply (simp add: multiset_def)
  apply (rule finite_subset, auto)
  done

lemmas in_multiset = const0_in_multiset only1_in_multiset
  union_preserves_multiset diff_preserves_multiset MCollect_preserves_multiset

subsection {* Algebraic properties *}

subsubsection {* Union *}

lemma union_empty [simp]: "M + {#} = M \<and> {#} + M = M"
by (simp add: union_def Mempty_def in_multiset)

lemma union_commute: "M + N = N + (M::'a multiset)"
by (simp add: union_def add_ac in_multiset)

lemma union_assoc: "(M + N) + K = M + (N + (K::'a multiset))"
by (simp add: union_def add_ac in_multiset)

lemma union_lcomm: "M + (N + K) = N + (M + (K::'a multiset))"
proof -
  have "M + (N + K) = (N + K) + M"
    by (rule union_commute)
  also have "\<dots> = N + (K + M)"
    by (rule union_assoc)
  also have "K + M = M + K"
    by (rule union_commute)
  finally show ?thesis .
qed

lemmas union_ac = union_assoc union_commute union_lcomm

instance multiset :: (type) comm_monoid_add
proof
  fix a b c :: "'a multiset"
  show "(a + b) + c = a + (b + c)" by (rule union_assoc)
  show "a + b = b + a" by (rule union_commute)
  show "0 + a = a" by simp
qed


subsubsection {* Difference *}

lemma diff_empty [simp]: "M - {#} = M \<and> {#} - M = {#}"
by (simp add: Mempty_def diff_def in_multiset)

lemma diff_union_inverse2 [simp]: "M + {#a#} - {#a#} = M"
by (simp add: union_def diff_def in_multiset)


subsubsection {* Count of elements *}

lemma count_empty [simp]: "count {#} a = 0"
by (simp add: count_def Mempty_def in_multiset)

lemma count_single [simp]: "count {#b#} a = (if b = a then 1 else 0)"
by (simp add: count_def single_def in_multiset)

lemma count_union [simp]: "count (M + N) a = count M a + count N a"
by (simp add: count_def union_def in_multiset)

lemma count_diff [simp]: "count (M - N) a = count M a - count N a"
by (simp add: count_def diff_def in_multiset)

lemma count_MCollect [simp]:
  "count {# x:M. P x #} a = (if P a then count M a else 0)"
by (simp add: count_def MCollect_def in_multiset)


subsubsection {* Set of elements *}

lemma set_of_empty [simp]: "set_of {#} = {}"
by (simp add: set_of_def)

lemma set_of_single [simp]: "set_of {#b#} = {b}"
by (simp add: set_of_def)

lemma set_of_union [simp]: "set_of (M + N) = set_of M \<union> set_of N"
by (auto simp add: set_of_def)

lemma set_of_eq_empty_iff [simp]: "(set_of M = {}) = (M = {#})"
by(auto simp: set_of_def Mempty_def in_multiset count_def expand_fun_eq)

lemma mem_set_of_iff [simp]: "(x \<in> set_of M) = (x :# M)"
by (auto simp add: set_of_def)

lemma set_of_MCollect [simp]: "set_of {# x:M. P x #} = set_of M \<inter> {x. P x}"
by (auto simp add: set_of_def)


subsubsection {* Size *}

lemma size_empty [simp,code func]: "size {#} = 0"
by (simp add: size_def)

lemma size_single [simp,code func]: "size {#b#} = 1"
by (simp add: size_def)

lemma finite_set_of [iff]: "finite (set_of M)"
  using Rep_multiset [of M]
  by (simp add: multiset_def set_of_def count_def)

lemma setsum_count_Int:
    "finite A ==> setsum (count N) (A \<inter> set_of N) = setsum (count N) A"
  apply (induct rule: finite_induct)
   apply simp
  apply (simp add: Int_insert_left set_of_def)
  done

lemma size_union[simp,code func]: "size (M + N::'a multiset) = size M + size N"
  apply (unfold size_def)
  apply (subgoal_tac "count (M + N) = (\<lambda>a. count M a + count N a)")
   prefer 2
   apply (rule ext, simp)
  apply (simp (no_asm_simp) add: setsum_Un_nat setsum_addf setsum_count_Int)
  apply (subst Int_commute)
  apply (simp (no_asm_simp) add: setsum_count_Int)
  done

lemma size_eq_0_iff_empty [iff]: "(size M = 0) = (M = {#})"
apply (unfold size_def Mempty_def count_def, auto simp: in_multiset)
apply (simp add: set_of_def count_def in_multiset expand_fun_eq)
done

lemma nonempty_has_size: "(S \<noteq> {#}) = (0 < size S)"
by(metis gr0I gr_implies_not0 size_empty size_eq_0_iff_empty)

lemma size_eq_Suc_imp_elem: "size M = Suc n ==> \<exists>a. a :# M"
  apply (unfold size_def)
  apply (drule setsum_SucD, auto)
  done

subsubsection {* Equality of multisets *}

lemma multiset_eq_conv_count_eq: "(M = N) = (\<forall>a. count M a = count N a)"
  by (simp add: count_def expand_fun_eq)

lemma single_not_empty [simp]: "{#a#} \<noteq> {#} \<and> {#} \<noteq> {#a#}"
by (simp add: single_def Mempty_def in_multiset expand_fun_eq)

lemma single_eq_single [simp]: "({#a#} = {#b#}) = (a = b)"
by (auto simp add: single_def in_multiset expand_fun_eq)

lemma union_eq_empty [iff]: "(M + N = {#}) = (M = {#} \<and> N = {#})"
by (auto simp add: union_def Mempty_def in_multiset expand_fun_eq)

lemma empty_eq_union [iff]: "({#} = M + N) = (M = {#} \<and> N = {#})"
by (auto simp add: union_def Mempty_def in_multiset expand_fun_eq)

lemma union_right_cancel [simp]: "(M + K = N + K) = (M = (N::'a multiset))"
by (simp add: union_def in_multiset expand_fun_eq)

lemma union_left_cancel [simp]: "(K + M = K + N) = (M = (N::'a multiset))"
by (simp add: union_def in_multiset expand_fun_eq)

lemma union_is_single:
  "(M + N = {#a#}) = (M = {#a#} \<and> N={#} \<or> M = {#} \<and> N = {#a#})"
apply (simp add: Mempty_def single_def union_def in_multiset add_is_1 expand_fun_eq)
apply blast
done

lemma single_is_union:
     "({#a#} = M + N) = ({#a#} = M \<and> N = {#} \<or> M = {#} \<and> {#a#} = N)"
apply (unfold Mempty_def single_def union_def)
apply (simp add: add_is_1 one_is_add in_multiset expand_fun_eq)
apply (blast dest: sym)
done

lemma add_eq_conv_diff:
  "(M + {#a#} = N + {#b#}) =
   (M = N \<and> a = b \<or> M = N - {#a#} + {#b#} \<and> N = M - {#b#} + {#a#})"
  using [[simproc del: neq]]
  apply (unfold single_def union_def diff_def)
  apply (simp (no_asm) add: in_multiset expand_fun_eq)
  apply (rule conjI, force, safe, simp_all)
  apply (simp add: eq_sym_conv)
  done

declare Rep_multiset_inject [symmetric, simp del]

instance multiset :: (type) cancel_ab_semigroup_add
proof
  fix a b c :: "'a multiset"
  show "a + b = a + c \<Longrightarrow> b = c" by simp
qed

lemma insert_DiffM:
  "x \<in># M \<Longrightarrow> {#x#} + (M - {#x#}) = M"
  by (clarsimp simp: multiset_eq_conv_count_eq)

lemma insert_DiffM2[simp]:
  "x \<in># M \<Longrightarrow> M - {#x#} + {#x#} = M"
  by (clarsimp simp: multiset_eq_conv_count_eq)

lemma multi_union_self_other_eq: 
  "(A::'a multiset) + X = A + Y \<Longrightarrow> X = Y"
  by (induct A arbitrary: X Y, auto)

lemma multi_self_add_other_not_self[simp]: "(A = A + {#x#}) = False"
by (metis single_not_empty union_empty union_left_cancel)

lemma insert_noteq_member: 
  assumes BC: "B + {#b#} = C + {#c#}"
   and bnotc: "b \<noteq> c"
  shows "c \<in># B"
proof -
  have "c \<in># C + {#c#}" by simp
  have nc: "\<not> c \<in># {#b#}" using bnotc by simp
  hence "c \<in># B + {#b#}" using BC by simp
  thus "c \<in># B" using nc by simp
qed


lemma add_eq_conv_ex:
  "(M + {#a#} = N + {#b#}) =
    (M = N \<and> a = b \<or> (\<exists>K. M = K + {#b#} \<and> N = K + {#a#}))"
by (auto simp add: add_eq_conv_diff)


lemma empty_multiset_count:
  "(\<forall>x. count A x = 0) = (A = {#})"
by(metis count_empty multiset_eq_conv_count_eq)


subsubsection {* Intersection *}

lemma multiset_inter_count:
  "count (A #\<inter> B) x = min (count A x) (count B x)"
by (simp add: multiset_inter_def min_def)

lemma multiset_inter_commute: "A #\<inter> B = B #\<inter> A"
by (simp add: multiset_eq_conv_count_eq multiset_inter_count
    min_max.inf_commute)

lemma multiset_inter_assoc: "A #\<inter> (B #\<inter> C) = A #\<inter> B #\<inter> C"
by (simp add: multiset_eq_conv_count_eq multiset_inter_count
    min_max.inf_assoc)

lemma multiset_inter_left_commute: "A #\<inter> (B #\<inter> C) = B #\<inter> (A #\<inter> C)"
by (simp add: multiset_eq_conv_count_eq multiset_inter_count min_def)

lemmas multiset_inter_ac =
  multiset_inter_commute
  multiset_inter_assoc
  multiset_inter_left_commute

lemma multiset_union_diff_commute: "B #\<inter> C = {#} \<Longrightarrow> A + B - C = A - C + B"
  apply (simp add: multiset_eq_conv_count_eq multiset_inter_count min_def
    split: split_if_asm)
  apply clarsimp
  apply (erule_tac x = a in allE)
  apply auto
  done


subsubsection {* Comprehension (filter) *}

lemma MCollect_empty[simp, code func]: "MCollect {#} P = {#}"
by(simp add:MCollect_def Mempty_def Abs_multiset_inject in_multiset expand_fun_eq)

lemma MCollect_single[simp, code func]:
  "MCollect {#x#} P = (if P x then {#x#} else {#})"
by(simp add:MCollect_def Mempty_def single_def Abs_multiset_inject in_multiset expand_fun_eq)

lemma MCollect_union[simp, code func]:
  "MCollect (M+N) f = MCollect M f + MCollect N f"
by(simp add:MCollect_def union_def Abs_multiset_inject in_multiset expand_fun_eq)


subsection {* Induction and case splits *}

lemma setsum_decr:
  "finite F ==> (0::nat) < f a ==>
    setsum (f (a := f a - 1)) F = (if a\<in>F then setsum f F - 1 else setsum f F)"
  apply (induct rule: finite_induct)
   apply auto
  apply (drule_tac a = a in mk_disjoint_insert, auto)
  done

lemma rep_multiset_induct_aux:
  assumes 1: "P (\<lambda>a. (0::nat))"
    and 2: "!!f b. f \<in> multiset ==> P f ==> P (f (b := f b + 1))"
  shows "\<forall>f. f \<in> multiset --> setsum f {x. f x \<noteq> 0} = n --> P f"
  apply (unfold multiset_def)
  apply (induct_tac n, simp, clarify)
   apply (subgoal_tac "f = (\<lambda>a.0)")
    apply simp
    apply (rule 1)
   apply (rule ext, force, clarify)
  apply (frule setsum_SucD, clarify)
  apply (rename_tac a)
  apply (subgoal_tac "finite {x. (f (a := f a - 1)) x > 0}")
   prefer 2
   apply (rule finite_subset)
    prefer 2
    apply assumption
   apply simp
   apply blast
  apply (subgoal_tac "f = (f (a := f a - 1))(a := (f (a := f a - 1)) a + 1)")
   prefer 2
   apply (rule ext)
   apply (simp (no_asm_simp))
   apply (erule ssubst, rule 2 [unfolded multiset_def], blast)
  apply (erule allE, erule impE, erule_tac [2] mp, blast)
  apply (simp (no_asm_simp) add: setsum_decr del: fun_upd_apply One_nat_def)
  apply (subgoal_tac "{x. x \<noteq> a --> f x \<noteq> 0} = {x. f x \<noteq> 0}")
   prefer 2
   apply blast
  apply (subgoal_tac "{x. x \<noteq> a \<and> f x \<noteq> 0} = {x. f x \<noteq> 0} - {a}")
   prefer 2
   apply blast
  apply (simp add: le_imp_diff_is_add setsum_diff1_nat cong: conj_cong)
  done

theorem rep_multiset_induct:
  "f \<in> multiset ==> P (\<lambda>a. 0) ==>
    (!!f b. f \<in> multiset ==> P f ==> P (f (b := f b + 1))) ==> P f"
  using rep_multiset_induct_aux by blast

theorem multiset_induct [case_names empty add, induct type: multiset]:
  assumes empty: "P {#}"
    and add: "!!M x. P M ==> P (M + {#x#})"
  shows "P M"
proof -
  note defns = union_def single_def Mempty_def
  show ?thesis
    apply (rule Rep_multiset_inverse [THEN subst])
    apply (rule Rep_multiset [THEN rep_multiset_induct])
     apply (rule empty [unfolded defns])
    apply (subgoal_tac "f(b := f b + 1) = (\<lambda>a. f a + (if a=b then 1 else 0))")
     prefer 2
     apply (simp add: expand_fun_eq)
    apply (erule ssubst)
    apply (erule Abs_multiset_inverse [THEN subst])
    apply (drule add [unfolded defns, simplified])
    apply(simp add:in_multiset)
    done
qed

lemma multi_nonempty_split: "M \<noteq> {#} \<Longrightarrow> \<exists>A a. M = A + {#a#}"
  by (induct M, auto)

lemma multiset_cases [cases type, case_names empty add]:
  assumes em:  "M = {#} \<Longrightarrow> P"
  assumes add: "\<And>N x. M = N + {#x#} \<Longrightarrow> P"
  shows "P"
proof (cases "M = {#}")
  assume "M = {#}" thus ?thesis using em by simp
next
  assume "M \<noteq> {#}"
  then obtain M' m where "M = M' + {#m#}" 
    by (blast dest: multi_nonempty_split)
  thus ?thesis using add by simp
qed

lemma multi_member_split: "x \<in># M \<Longrightarrow> \<exists>A. M = A + {#x#}"
  apply (cases M, simp)
  apply (rule_tac x="M - {#x#}" in exI, simp)
  done

lemma multiset_partition: "M = {# x:M. P x #} + {# x:M. \<not> P x #}"
  by (subst multiset_eq_conv_count_eq, auto)

declare multiset_typedef [simp del]

lemma multi_drop_mem_not_eq: "c \<in># B \<Longrightarrow> B - {#c#} \<noteq> B"
  by (cases "B={#}", auto dest: multi_member_split)

subsection {* Orderings *}

subsubsection {* Well-foundedness *}

definition
  mult1 :: "('a \<times> 'a) set => ('a multiset \<times> 'a multiset) set" where
  "mult1 r =
    {(N, M). \<exists>a M0 K. M = M0 + {#a#} \<and> N = M0 + K \<and>
      (\<forall>b. b :# K --> (b, a) \<in> r)}"

definition
  mult :: "('a \<times> 'a) set => ('a multiset \<times> 'a multiset) set" where
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
      with N have n: "N = K' + K + {#a#}" by (simp add: union_ac)

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
          then show "M0 + (K + {#x#}) \<in> ?W" by (simp only: union_assoc)
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

(*Badly needed: a linear arithmetic procedure for multisets*)

lemma diff_union_single_conv: "a :# J ==> I + J - {#a#} = I + (J - {#a#})"
  by (simp add: multiset_eq_conv_count_eq)

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
   apply (simp (no_asm_simp) add: union_assoc [symmetric])
   apply (drule_tac f = "\<lambda>M. M - {#a#}" in arg_cong)
   apply (simp add: diff_union_single_conv)
   apply (simp (no_asm_use) add: trans_def)
   apply blast
  apply (subgoal_tac "a :# I")
   apply (rule_tac x = "I - {#a#}" in exI)
   apply (rule_tac x = "J + {#a#}" in exI)
   apply (rule_tac x = "K + Ka" in exI)
   apply (rule conjI)
    apply (simp add: multiset_eq_conv_count_eq split: nat_diff_split)
   apply (rule conjI)
    apply (drule_tac f = "\<lambda>M. M - {#a#}" in arg_cong, simp)
    apply (simp add: multiset_eq_conv_count_eq split: nat_diff_split)
   apply (simp (no_asm_use) add: trans_def)
   apply blast
  apply (subgoal_tac "a :# (M0 + {#a#})")
   apply simp
  apply (simp (no_asm))
  done

lemma elem_imp_eq_diff_union: "a :# M ==> M = M - {#a#} + {#a#}"
  by (simp add: multiset_eq_conv_count_eq)

lemma size_eq_Suc_imp_eq_union: "size M = Suc n ==> \<exists>a N. M = N + {#a#}"
  apply (erule size_eq_Suc_imp_elem [THEN exE])
  apply (drule elem_imp_eq_diff_union, auto)
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
    "((I + {# x : K. (x, a) \<in> r #}) + {# x : K. (x, a) \<notin> r #},
      (I + {# x : K. (x, a) \<in> r #}) + J') \<in> mult r")
   prefer 2
   apply force
  apply (simp (no_asm_use) add: union_assoc [symmetric] mult_def)
  apply (erule trancl_trans)
  apply (rule r_into_trancl)
  apply (simp add: mult1_def set_of_def)
  apply (rule_tac x = a in exI)
  apply (rule_tac x = "I + J'" in exI)
  apply (simp add: union_ac)
  done

lemma one_step_implies_mult:
  "trans r ==> J \<noteq> {#} ==> \<forall>k \<in> set_of K. \<exists>j \<in> set_of J. (k, j) \<in> r
    ==> (I + K, I + J) \<in> mult r"
  using one_step_implies_mult_aux by blast


subsubsection {* Partial-order properties *}

instance multiset :: (type) ord ..

defs (overloaded)
  less_multiset_def: "M' < M == (M', M) \<in> mult {(x', x). x' < x}"
  le_multiset_def: "M' <= M == M' = M \<or> M' < (M::'a multiset)"

lemma trans_base_order: "trans {(x', x). x' < (x::'a::order)}"
  unfolding trans_def by (blast intro: order_less_trans)

text {*
 \medskip Irreflexivity.
*}

lemma mult_irrefl_aux:
    "finite A ==> (\<forall>x \<in> A. \<exists>y \<in> A. x < (y::'a::order)) \<Longrightarrow> A = {}"
  by (induct rule: finite_induct) (auto intro: order_less_trans)

lemma mult_less_not_refl: "\<not> M < (M::'a::order multiset)"
  apply (unfold less_multiset_def, auto)
  apply (drule trans_base_order [THEN mult_implies_one_step], auto)
  apply (drule finite_set_of [THEN mult_irrefl_aux [rule_format (no_asm)]])
  apply (simp add: set_of_eq_empty_iff)
  done

lemma mult_less_irrefl [elim!]: "M < (M::'a::order multiset) ==> R"
  using insert mult_less_not_refl by fast


text {* Transitivity. *}

theorem mult_less_trans: "K < M ==> M < N ==> K < (N::'a::order multiset)"
  unfolding less_multiset_def mult_def by (blast intro: trancl_trans)

text {* Asymmetry. *}

theorem mult_less_not_sym: "M < N ==> \<not> N < (M::'a::order multiset)"
  apply auto
  apply (rule mult_less_not_refl [THEN notE])
  apply (erule mult_less_trans, assumption)
  done

theorem mult_less_asym:
    "M < N ==> (\<not> P ==> N < (M::'a::order multiset)) ==> P"
  by (insert mult_less_not_sym, blast)

theorem mult_le_refl [iff]: "M <= (M::'a::order multiset)"
  unfolding le_multiset_def by auto

text {* Anti-symmetry. *}

theorem mult_le_antisym:
    "M <= N ==> N <= M ==> M = (N::'a::order multiset)"
  unfolding le_multiset_def by (blast dest: mult_less_not_sym)

text {* Transitivity. *}

theorem mult_le_trans:
    "K <= M ==> M <= N ==> K <= (N::'a::order multiset)"
  unfolding le_multiset_def by (blast intro: mult_less_trans)

theorem mult_less_le: "(M < N) = (M <= N \<and> M \<noteq> (N::'a::order multiset))"
  unfolding le_multiset_def by auto

text {* Partial order. *}

instance multiset :: (order) order
  apply intro_classes
  apply (rule mult_less_le)
  apply (rule mult_le_refl)
  apply (erule mult_le_trans, assumption)
  apply (erule mult_le_antisym, assumption)
  done


subsubsection {* Monotonicity of multiset union *}

lemma mult1_union:
    "(B, D) \<in> mult1 r ==> trans r ==> (C + B, C + D) \<in> mult1 r"
  apply (unfold mult1_def, auto)
  apply (rule_tac x = a in exI)
  apply (rule_tac x = "C + M0" in exI)
  apply (simp add: union_assoc)
  done

lemma union_less_mono2: "B < D ==> C + B < C + (D::'a::order multiset)"
  apply (unfold less_multiset_def mult_def)
  apply (erule trancl_induct)
   apply (blast intro: mult1_union transI order_less_trans r_into_trancl)
  apply (blast intro: mult1_union transI order_less_trans r_into_trancl trancl_trans)
  done

lemma union_less_mono1: "B < D ==> B + C < D + (C::'a::order multiset)"
  apply (subst union_commute [of B C])
  apply (subst union_commute [of D C])
  apply (erule union_less_mono2)
  done

lemma union_less_mono:
    "A < C ==> B < D ==> A + B < C + (D::'a::order multiset)"
  apply (blast intro!: union_less_mono1 union_less_mono2 mult_less_trans)
  done

lemma union_le_mono:
    "A <= C ==> B <= D ==> A + B <= C + (D::'a::order multiset)"
  unfolding le_multiset_def
  by (blast intro: union_less_mono union_less_mono1 union_less_mono2)

lemma empty_leI [iff]: "{#} <= (M::'a::order multiset)"
  apply (unfold le_multiset_def less_multiset_def)
  apply (case_tac "M = {#}")
   prefer 2
   apply (subgoal_tac "({#} + {#}, {#} + M) \<in> mult (Collect (split op <))")
    prefer 2
    apply (rule one_step_implies_mult)
      apply (simp only: trans_def, auto)
  done

lemma union_upper1: "A <= A + (B::'a::order multiset)"
proof -
  have "A + {#} <= A + B" by (blast intro: union_le_mono)
  then show ?thesis by simp
qed

lemma union_upper2: "B <= A + (B::'a::order multiset)"
  by (subst union_commute) (rule union_upper1)

instance multiset :: (order) pordered_ab_semigroup_add
apply intro_classes
apply(erule union_le_mono[OF mult_le_refl])
done

subsection {* Link with lists *}

primrec multiset_of :: "'a list \<Rightarrow> 'a multiset" where
"multiset_of [] = {#}" |
"multiset_of (a # x) = multiset_of x + {# a #}"

lemma multiset_of_zero_iff[simp]: "(multiset_of x = {#}) = (x = [])"
  by (induct x) auto

lemma multiset_of_zero_iff_right[simp]: "({#} = multiset_of x) = (x = [])"
  by (induct x) auto

lemma set_of_multiset_of[simp]: "set_of(multiset_of x) = set x"
  by (induct x) auto

lemma mem_set_multiset_eq: "x \<in> set xs = (x :# multiset_of xs)"
  by (induct xs) auto

lemma multiset_of_append [simp]:
    "multiset_of (xs @ ys) = multiset_of xs + multiset_of ys"
  by (induct xs arbitrary: ys) (auto simp: union_ac)

lemma surj_multiset_of: "surj multiset_of"
  apply (unfold surj_def, rule allI)
  apply (rule_tac M=y in multiset_induct, auto)
  apply (rule_tac x = "x # xa" in exI, auto)
  done

lemma set_count_greater_0: "set x = {a. count (multiset_of x) a > 0}"
  by (induct x) auto

lemma distinct_count_atmost_1:
   "distinct x = (! a. count (multiset_of x) a = (if a \<in> set x then 1 else 0))"
   apply (induct x, simp, rule iffI, simp_all)
   apply (rule conjI)
   apply (simp_all add: set_of_multiset_of [THEN sym] del: set_of_multiset_of)
   apply (erule_tac x=a in allE, simp, clarify)
   apply (erule_tac x=aa in allE, simp)
   done

lemma multiset_of_eq_setD:
  "multiset_of xs = multiset_of ys \<Longrightarrow> set xs = set ys"
  by (rule) (auto simp add:multiset_eq_conv_count_eq set_count_greater_0)

lemma set_eq_iff_multiset_of_eq_distinct:
  "\<lbrakk>distinct x; distinct y\<rbrakk>
   \<Longrightarrow> (set x = set y) = (multiset_of x = multiset_of y)"
  by (auto simp: multiset_eq_conv_count_eq distinct_count_atmost_1)

lemma set_eq_iff_multiset_of_remdups_eq:
   "(set x = set y) = (multiset_of (remdups x) = multiset_of (remdups y))"
  apply (rule iffI)
  apply (simp add: set_eq_iff_multiset_of_eq_distinct[THEN iffD1])
  apply (drule distinct_remdups[THEN distinct_remdups
                      [THEN set_eq_iff_multiset_of_eq_distinct[THEN iffD2]]])
  apply simp
  done

lemma multiset_of_compl_union [simp]:
    "multiset_of [x\<leftarrow>xs. P x] + multiset_of [x\<leftarrow>xs. \<not>P x] = multiset_of xs"
  by (induct xs) (auto simp: union_ac)

lemma count_filter:
    "count (multiset_of xs) x = length [y \<leftarrow> xs. y = x]"
  by (induct xs) auto


subsection {* Pointwise ordering induced by count *}

definition
  mset_le :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool"  (infix "\<le>#" 50) where
  "(A \<le># B) = (\<forall>a. count A a \<le> count B a)"
definition
  mset_less :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool"  (infix "<#" 50) where
  "(A <# B) = (A \<le># B \<and> A \<noteq> B)"

notation mset_le (infix "\<subseteq>#" 50)
notation mset_less (infix "\<subset>#" 50)

lemma mset_le_refl[simp]: "A \<le># A"
  unfolding mset_le_def by auto

lemma mset_le_trans: "\<lbrakk> A \<le># B; B \<le># C \<rbrakk> \<Longrightarrow> A \<le># C"
  unfolding mset_le_def by (fast intro: order_trans)

lemma mset_le_antisym: "\<lbrakk> A \<le># B; B \<le># A \<rbrakk> \<Longrightarrow> A = B"
  apply (unfold mset_le_def)
  apply (rule multiset_eq_conv_count_eq[THEN iffD2])
  apply (blast intro: order_antisym)
  done

lemma mset_le_exists_conv:
  "(A \<le># B) = (\<exists>C. B = A + C)"
  apply (unfold mset_le_def, rule iffI, rule_tac x = "B - A" in exI)
  apply (auto intro: multiset_eq_conv_count_eq [THEN iffD2])
  done

lemma mset_le_mono_add_right_cancel[simp]: "(A + C \<le># B + C) = (A \<le># B)"
  unfolding mset_le_def by auto

lemma mset_le_mono_add_left_cancel[simp]: "(C + A \<le># C + B) = (A \<le># B)"
  unfolding mset_le_def by auto

lemma mset_le_mono_add: "\<lbrakk> A \<le># B; C \<le># D \<rbrakk> \<Longrightarrow> A + C \<le># B + D"
  apply (unfold mset_le_def)
  apply auto
  apply (erule_tac x=a in allE)+
  apply auto
  done

lemma mset_le_add_left[simp]: "A \<le># A + B"
  unfolding mset_le_def by auto

lemma mset_le_add_right[simp]: "B \<le># A + B"
  unfolding mset_le_def by auto

lemma multiset_of_remdups_le: "multiset_of (remdups xs) \<le># multiset_of xs"
apply (induct xs)
 apply auto
apply (rule mset_le_trans)
 apply auto
done

interpretation mset_order:
  order ["op \<le>#" "op <#"]
  by (auto intro: order.intro mset_le_refl mset_le_antisym
    mset_le_trans simp: mset_less_def)

interpretation mset_order_cancel_semigroup:
  pordered_cancel_ab_semigroup_add ["op +" "op \<le>#" "op <#"]
  by unfold_locales (erule mset_le_mono_add [OF mset_le_refl])

interpretation mset_order_semigroup_cancel:
  pordered_ab_semigroup_add_imp_le ["op +" "op \<le>#" "op <#"]
  by (unfold_locales) simp


lemma mset_lessD:
  "\<lbrakk> A \<subset># B ; x \<in># A \<rbrakk> \<Longrightarrow> x \<in># B"
  apply (clarsimp simp: mset_le_def mset_less_def)
  apply (erule_tac x=x in allE)
  apply auto
  done

lemma mset_leD:
  "\<lbrakk> A \<subseteq># B ; x \<in># A \<rbrakk> \<Longrightarrow> x \<in># B"
  apply (clarsimp simp: mset_le_def mset_less_def)
  apply (erule_tac x=x in allE)
  apply auto
  done
  
lemma mset_less_insertD:
  "(A + {#x#} \<subset># B) \<Longrightarrow> (x \<in># B \<and> A \<subset># B)"
  apply (rule conjI)
   apply (simp add: mset_lessD)
  apply (clarsimp simp: mset_le_def mset_less_def)
  apply safe
   apply (erule_tac x=a in allE)
   apply (auto split: split_if_asm)
  done

lemma mset_le_insertD:
  "(A + {#x#} \<subseteq># B) \<Longrightarrow> (x \<in># B \<and> A \<subseteq># B)"
  apply (rule conjI)
   apply (simp add: mset_leD)
  apply (force simp: mset_le_def mset_less_def split: split_if_asm)
  done

lemma mset_less_of_empty[simp]: "A \<subset># {#} = False" 
  by (induct A, auto simp: mset_le_def mset_less_def)

lemma multi_psub_of_add_self[simp]: "A \<subset># A + {#x#}"
  by (clarsimp simp: mset_le_def mset_less_def)

lemma multi_psub_self[simp]: "A \<subset># A = False"
  by (clarsimp simp: mset_le_def mset_less_def)

lemma mset_less_add_bothsides:
  "T + {#x#} \<subset># S + {#x#} \<Longrightarrow> T \<subset># S"
  by (clarsimp simp: mset_le_def mset_less_def)

lemma mset_less_empty_nonempty: "({#} \<subset># S) = (S \<noteq> {#})"
  by (auto simp: mset_le_def mset_less_def)

lemma mset_less_size: "A \<subset># B \<Longrightarrow> size A < size B"
proof (induct A arbitrary: B)
  case (empty M)
  hence "M \<noteq> {#}" by (simp add: mset_less_empty_nonempty)
  then obtain M' x where "M = M' + {#x#}" 
    by (blast dest: multi_nonempty_split)
  thus ?case by simp
next
  case (add S x T)
  have IH: "\<And>B. S \<subset># B \<Longrightarrow> size S < size B" by fact
  have SxsubT: "S + {#x#} \<subset># T" by fact
  hence "x \<in># T" and "S \<subset># T" by (auto dest: mset_less_insertD)
  then obtain T' where T: "T = T' + {#x#}" 
    by (blast dest: multi_member_split)
  hence "S \<subset># T'" using SxsubT 
    by (blast intro: mset_less_add_bothsides)
  hence "size S < size T'" using IH by simp
  thus ?case using T by simp
qed

lemmas mset_less_trans = mset_order.less_eq_less.less_trans

lemma mset_less_diff_self: "c \<in># B \<Longrightarrow> B - {#c#} \<subset># B"
  by (auto simp: mset_le_def mset_less_def multi_drop_mem_not_eq)

subsection {* Strong induction and subset induction for multisets *}

text {* Well-foundedness of proper subset operator: *}

definition
  mset_less_rel  :: "('a multiset * 'a multiset) set" 
  where
  --{* proper multiset subset *}
  "mset_less_rel \<equiv> {(A,B). A \<subset># B}"

lemma multiset_add_sub_el_shuffle: 
  assumes cinB: "c \<in># B" and bnotc: "b \<noteq> c" 
  shows "B - {#c#} + {#b#} = B + {#b#} - {#c#}"
proof -
  from cinB obtain A where B: "B = A + {#c#}" 
    by (blast dest: multi_member_split)
  have "A + {#b#} = A + {#b#} + {#c#} - {#c#}" by simp
  hence "A + {#b#} = A + {#c#} + {#b#} - {#c#}" 
    by (simp add: union_ac)
  thus ?thesis using B by simp
qed

lemma wf_mset_less_rel: "wf mset_less_rel"
  apply (unfold mset_less_rel_def)
  apply (rule wf_measure [THEN wf_subset, where f1=size])
  apply (clarsimp simp: measure_def inv_image_def mset_less_size)
  done

text {* The induction rules: *}

lemma full_multiset_induct [case_names less]:
  assumes ih: "\<And>B. \<forall>A. A \<subset># B \<longrightarrow> P A \<Longrightarrow> P B"
  shows "P B"
  apply (rule wf_mset_less_rel [THEN wf_induct])
  apply (rule ih, auto simp: mset_less_rel_def)
  done

lemma multi_subset_induct [consumes 2, case_names empty add]:
  assumes "F \<subseteq># A"
    and empty: "P {#}"
    and insert: "\<And>a F. a \<in># A \<Longrightarrow> P F \<Longrightarrow> P (F + {#a#})"
  shows "P F"
proof -
  from `F \<subseteq># A`
  show ?thesis
  proof (induct F)
    show "P {#}" by fact
  next
    fix x F
    assume P: "F \<subseteq># A \<Longrightarrow> P F" and i: "F + {#x#} \<subseteq># A"
    show "P (F + {#x#})"
    proof (rule insert)
      from i show "x \<in># A" by (auto dest: mset_le_insertD)
      from i have "F \<subseteq># A" by (auto simp: mset_le_insertD)
      with P show "P F" .
    qed
  qed
qed 

text{* A consequence: Extensionality. *}

lemma multi_count_eq: 
  "(\<forall>x. count A x = count B x) = (A = B)"
  apply (rule iffI)
   prefer 2
   apply clarsimp 
  apply (induct A arbitrary: B rule: full_multiset_induct)
  apply (rename_tac C)
  apply (case_tac B rule: multiset_cases)
   apply (simp add: empty_multiset_count)
  apply simp
  apply (case_tac "x \<in># C")
   apply (force dest: multi_member_split)
  apply (erule_tac x=x in allE)
  apply simp
  done

lemmas multi_count_ext = multi_count_eq [THEN iffD1, rule_format]

subsection {* The fold combinator *}

text {* The intended behaviour is
@{text "fold_mset f z {#x\<^isub>1, ..., x\<^isub>n#} = f x\<^isub>1 (\<dots> (f x\<^isub>n z)\<dots>)"}
if @{text f} is associative-commutative. 
*}

(* the graph of fold_mset, z = the start element, f = folding function, 
   A the multiset, y the result *)
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
  fold_mset :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a multiset \<Rightarrow> 'b"
where
  "fold_mset f z A \<equiv> THE x. fold_msetG f z A x"

lemma Diff1_fold_msetG:
  "\<lbrakk> fold_msetG f z (A - {#x#}) y; x \<in># A \<rbrakk> \<Longrightarrow> fold_msetG f z A (f x y)"
  by (frule_tac x=x in fold_msetG.insertI, auto)

lemma fold_msetG_nonempty: "\<exists>x. fold_msetG f z A x"
  apply (induct A)
   apply blast
  apply clarsimp
  apply (drule_tac x=x in fold_msetG.insertI)
  apply auto
  done

lemma fold_mset_empty[simp]: "fold_mset f z {#} = z"
  by (unfold fold_mset_def, blast)

locale left_commutative = 
  fixes f :: "'a => 'b => 'b"
  assumes left_commute: "f x (f y z) = f y (f x z)"

lemma (in left_commutative) fold_msetG_determ:
  "\<lbrakk>fold_msetG f z A x; fold_msetG f z A y\<rbrakk> \<Longrightarrow> y = x"
proof (induct arbitrary: x y z rule: full_multiset_induct)
  case (less M x\<^isub>1 x\<^isub>2 Z)
  have IH: "\<forall>A. A \<subset># M \<longrightarrow> 
    (\<forall>x x' x''. fold_msetG f x'' A x \<longrightarrow> fold_msetG f x'' A x'
               \<longrightarrow> x' = x)" by fact
  have Mfoldx\<^isub>1: "fold_msetG f Z M x\<^isub>1" and Mfoldx\<^isub>2: "fold_msetG f Z M x\<^isub>2" by fact+
  show ?case
  proof (rule fold_msetG.cases [OF Mfoldx\<^isub>1])
    assume "M = {#}" and "x\<^isub>1 = Z"
    thus ?case using Mfoldx\<^isub>2 by auto 
  next
    fix B b u
    assume "M = B + {#b#}" and "x\<^isub>1 = f b u" and Bu: "fold_msetG f Z B u"
    hence MBb: "M = B + {#b#}" and x\<^isub>1: "x\<^isub>1 = f b u" by auto
    show ?case
    proof (rule fold_msetG.cases [OF Mfoldx\<^isub>2])
      assume "M = {#}" "x\<^isub>2 = Z"
      thus ?case using Mfoldx\<^isub>1 by auto
    next
      fix C c v
      assume "M = C + {#c#}" and "x\<^isub>2 = f c v" and Cv: "fold_msetG f Z C v"
      hence MCc: "M = C + {#c#}" and x\<^isub>2: "x\<^isub>2 = f c v" by auto
      hence CsubM: "C \<subset># M" by simp
      from MBb have BsubM: "B \<subset># M" by simp
      show ?case
      proof cases
        assume "b=c"
        then moreover have "B = C" using MBb MCc by auto
        ultimately show ?thesis using Bu Cv x\<^isub>1 x\<^isub>2 CsubM IH by auto
      next
        assume diff: "b \<noteq> c"
        let ?D = "B - {#c#}"
        have cinB: "c \<in># B" and binC: "b \<in># C" using MBb MCc diff
          by (auto intro: insert_noteq_member dest: sym)
        have "B - {#c#} \<subset># B" using cinB by (rule mset_less_diff_self)
        hence DsubM: "?D \<subset># M" using BsubM by (blast intro: mset_less_trans)
        from MBb MCc have "B + {#b#} = C + {#c#}" by blast
        hence [simp]: "B + {#b#} - {#c#} = C"
          using MBb MCc binC cinB by auto
        have B: "B = ?D + {#c#}" and C: "C = ?D + {#b#}"
          using MBb MCc diff binC cinB
          by (auto simp: multiset_add_sub_el_shuffle)
        then obtain d where Dfoldd: "fold_msetG f Z ?D d"
          using fold_msetG_nonempty by iprover
        hence "fold_msetG f Z B (f c d)" using cinB
          by (rule Diff1_fold_msetG)
        hence "f c d = u" using IH BsubM Bu by blast
        moreover 
        have "fold_msetG f Z C (f b d)" using binC cinB diff Dfoldd
          by (auto simp: multiset_add_sub_el_shuffle 
            dest: fold_msetG.insertI [where x=b])
        hence "f b d = v" using IH CsubM Cv by blast
        ultimately show ?thesis using x\<^isub>1 x\<^isub>2
          by (auto simp: left_commute)
      qed
    qed
  qed
qed
        
lemma (in left_commutative) fold_mset_insert_aux: "
    (fold_msetG f z (A + {#x#}) v) =
    (\<exists>y. fold_msetG f z A y \<and> v = f x y)"
  apply (rule iffI)
   prefer 2
   apply blast
  apply (rule_tac A=A and f=f in fold_msetG_nonempty [THEN exE, standard])
  apply (blast intro: fold_msetG_determ)
  done

lemma (in left_commutative) fold_mset_equality: "fold_msetG f z A y \<Longrightarrow> fold_mset f z A = y"
  by (unfold fold_mset_def) (blast intro: fold_msetG_determ)

lemma (in left_commutative) fold_mset_insert:
  "fold_mset f z (A + {#x#}) = f x (fold_mset f z A)"
  apply (simp add: fold_mset_def fold_mset_insert_aux union_commute)  
  apply (rule the_equality)
  apply (auto cong add: conj_cong 
              simp add: fold_mset_def [symmetric] fold_mset_equality fold_msetG_nonempty)
  done

lemma (in left_commutative) fold_mset_insert_idem:
  shows "fold_mset f z (A + {#a#}) = f a (fold_mset f z A)"
  apply (simp add: fold_mset_def fold_mset_insert_aux)
  apply (rule the_equality)
  apply (auto cong add: conj_cong 
              simp add: fold_mset_def [symmetric] fold_mset_equality fold_msetG_nonempty)
  done

lemma (in left_commutative) fold_mset_commute:
  "f x (fold_mset f z A) = fold_mset f (f x z) A"
  by (induct A, auto simp: fold_mset_insert left_commute [of x])
  
lemma (in left_commutative) fold_mset_single [simp]:
   "fold_mset f z {#x#} = f x z"
using fold_mset_insert[of z "{#}"] by simp

lemma (in left_commutative) fold_mset_union [simp]:
   "fold_mset f z (A+B) = fold_mset f (fold_mset f z A) B"
proof (induct A)
   case empty thus ?case by simp
next
   case (add A x)
   have "A + {#x#} + B = (A+B) + {#x#}" by(simp add:union_ac)
   hence "fold_mset f z (A + {#x#} + B) = f x (fold_mset f z (A + B))" 
     by (simp add: fold_mset_insert)
   also have "\<dots> = fold_mset f (fold_mset f z (A + {#x#})) B"
     by (simp add: fold_mset_commute[of x,symmetric] add fold_mset_insert)
   finally show ?case .
qed

lemma (in left_commutative) fold_mset_fusion:
  includes left_commutative g
  shows "\<lbrakk>\<And>x y. h (g x y) = f x (h y) \<rbrakk> \<Longrightarrow> h (fold_mset g w A) = fold_mset f (h w) A"
  by (induct A, auto)

lemma (in left_commutative) fold_mset_rec:
  assumes a: "a \<in># A" 
  shows "fold_mset f z A = f a (fold_mset f z (A - {#a#}))"
proof -
  from a obtain A' where "A = A' + {#a#}" by (blast dest: multi_member_split)
  thus ?thesis by simp
qed

text{* A note on code generation: When defining some
function containing a subterm @{term"fold_mset F"}, code generation is
not automatic. When interpreting locale @{text left_commutative} with
@{text F}, the would be code thms for @{const fold_mset} become thms like
@{term"fold_mset F z {#} = z"} where @{text F} is not a pattern but contains
defined symbols, i.e.\ is not a code thm. Hence a separate constant with its
own code thms needs to be introduced for @{text F}. See the image operator
below. *}

subsection {* Image *}

definition [code func del]: "image_mset f == fold_mset (op + o single o f) {#}"

interpretation image_left_comm: left_commutative["op + o single o f"]
by(unfold_locales)(simp add:union_ac)

lemma image_mset_empty[simp,code func]: "image_mset f {#} = {#}"
by(simp add:image_mset_def)

lemma image_mset_single[simp,code func]: "image_mset f {#x#} = {#f x#}"
by(simp add:image_mset_def)

lemma image_mset_insert:
  "image_mset f (M + {#a#}) = image_mset f M + {#f a#}"
by(simp add:image_mset_def add_ac)

lemma image_mset_union[simp, code func]:
  "image_mset f (M+N) = image_mset f M + image_mset f N"
apply(induct N)
 apply simp
apply(simp add:union_assoc[symmetric] image_mset_insert)
done

lemma size_image_mset[simp]: "size(image_mset f M) = size M"
by(induct M) simp_all

lemma image_mset_is_empty_iff[simp]: "image_mset f M = {#} \<longleftrightarrow> M={#}"
by (cases M) auto


syntax comprehension1_mset :: "'a \<Rightarrow> 'b \<Rightarrow> 'b multiset \<Rightarrow> 'a multiset"
       ("({#_/. _ :# _#})")
translations "{#e. x:#M#}" == "CONST image_mset (%x. e) M"

syntax comprehension2_mset :: "'a \<Rightarrow> 'b \<Rightarrow> 'b multiset \<Rightarrow> bool \<Rightarrow> 'a multiset"
       ("({#_/ | _ :# _./ _#})")
translations
  "{#e | x:#M. P#}" => "{#e. x :# {# x:M. P#}#}"

text{* This allows to write not just filters like @{term"{#x:M. x<c#}"}
but also images like @{term"{#x+x. x:#M #}"}
and @{term[source]"{#x+x|x:#M. x<c#}"}, where the latter is currently
displayed as @{term"{#x+x|x:#M. x<c#}"}. *}

end
