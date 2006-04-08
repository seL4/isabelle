(*  Title:      HOL/Library/Multiset.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Markus Wenzel, Lawrence C Paulson, Norbert Voelker
*)

header {* Multisets *}

theory Multiset
imports Accessible_Part
begin

subsection {* The type of multisets *}

typedef 'a multiset = "{f::'a => nat. finite {x . 0 < f x}}"
proof
  show "(\<lambda>x. 0::nat) \<in> ?multiset" by simp
qed

lemmas multiset_typedef [simp] =
    Abs_multiset_inverse Rep_multiset_inverse Rep_multiset
  and [simp] = Rep_multiset_inject [symmetric]

definition
  Mempty :: "'a multiset"    ("{#}")
  "{#} = Abs_multiset (\<lambda>a. 0)"

  single :: "'a => 'a multiset"    ("{#_#}")
  "{#a#} = Abs_multiset (\<lambda>b. if b = a then 1 else 0)"

  count :: "'a multiset => 'a => nat"
  "count = Rep_multiset"

  MCollect :: "'a multiset => ('a => bool) => 'a multiset"
  "MCollect M P = Abs_multiset (\<lambda>x. if P x then Rep_multiset M x else 0)"

abbreviation
  Melem :: "'a => 'a multiset => bool"    ("(_/ :# _)" [50, 51] 50)
  "a :# M == 0 < count M a"

syntax
  "_MCollect" :: "pttrn => 'a multiset => bool => 'a multiset"    ("(1{# _ : _./ _#})")
translations
  "{#x:M. P#}" == "MCollect M (\<lambda>x. P)"

definition
  set_of :: "'a multiset => 'a set"
  "set_of M = {x. x :# M}"

instance multiset :: (type) "{plus, minus, zero}" ..

defs (overloaded)
  union_def: "M + N == Abs_multiset (\<lambda>a. Rep_multiset M a + Rep_multiset N a)"
  diff_def: "M - N == Abs_multiset (\<lambda>a. Rep_multiset M a - Rep_multiset N a)"
  Zero_multiset_def [simp]: "0 == {#}"
  size_def: "size M == setsum (count M) (set_of M)"

definition
  multiset_inter :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" (infixl "#\<inter>" 70)
  "multiset_inter A B = A - (A - B)"


text {*
 \medskip Preservation of the representing set @{term multiset}.
*}

lemma const0_in_multiset [simp]: "(\<lambda>a. 0) \<in> multiset"
  by (simp add: multiset_def)

lemma only1_in_multiset [simp]: "(\<lambda>b. if b = a then 1 else 0) \<in> multiset"
  by (simp add: multiset_def)

lemma union_preserves_multiset [simp]:
    "M \<in> multiset ==> N \<in> multiset ==> (\<lambda>a. M a + N a) \<in> multiset"
  apply (simp add: multiset_def)
  apply (drule (1) finite_UnI)
  apply (simp del: finite_Un add: Un_def)
  done

lemma diff_preserves_multiset [simp]:
    "M \<in> multiset ==> (\<lambda>a. M a - N a) \<in> multiset"
  apply (simp add: multiset_def)
  apply (rule finite_subset)
   apply auto
  done


subsection {* Algebraic properties of multisets *}

subsubsection {* Union *}

lemma union_empty [simp]: "M + {#} = M \<and> {#} + M = M"
  by (simp add: union_def Mempty_def)

lemma union_commute: "M + N = N + (M::'a multiset)"
  by (simp add: union_def add_ac)

lemma union_assoc: "(M + N) + K = M + (N + (K::'a multiset))"
  by (simp add: union_def add_ac)

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
  by (simp add: Mempty_def diff_def)

lemma diff_union_inverse2 [simp]: "M + {#a#} - {#a#} = M"
  by (simp add: union_def diff_def)


subsubsection {* Count of elements *}

lemma count_empty [simp]: "count {#} a = 0"
  by (simp add: count_def Mempty_def)

lemma count_single [simp]: "count {#b#} a = (if b = a then 1 else 0)"
  by (simp add: count_def single_def)

lemma count_union [simp]: "count (M + N) a = count M a + count N a"
  by (simp add: count_def union_def)

lemma count_diff [simp]: "count (M - N) a = count M a - count N a"
  by (simp add: count_def diff_def)


subsubsection {* Set of elements *}

lemma set_of_empty [simp]: "set_of {#} = {}"
  by (simp add: set_of_def)

lemma set_of_single [simp]: "set_of {#b#} = {b}"
  by (simp add: set_of_def)

lemma set_of_union [simp]: "set_of (M + N) = set_of M \<union> set_of N"
  by (auto simp add: set_of_def)

lemma set_of_eq_empty_iff [simp]: "(set_of M = {}) = (M = {#})"
  by (auto simp add: set_of_def Mempty_def count_def expand_fun_eq)

lemma mem_set_of_iff [simp]: "(x \<in> set_of M) = (x :# M)"
  by (auto simp add: set_of_def)


subsubsection {* Size *}

lemma size_empty [simp]: "size {#} = 0"
  by (simp add: size_def)

lemma size_single [simp]: "size {#b#} = 1"
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
  apply (unfold size_def Mempty_def count_def, auto)
  apply (simp add: set_of_def count_def expand_fun_eq)
  done

lemma size_eq_Suc_imp_elem: "size M = Suc n ==> \<exists>a. a :# M"
  apply (unfold size_def)
  apply (drule setsum_SucD, auto)
  done


subsubsection {* Equality of multisets *}

lemma multiset_eq_conv_count_eq: "(M = N) = (\<forall>a. count M a = count N a)"
  by (simp add: count_def expand_fun_eq)

lemma single_not_empty [simp]: "{#a#} \<noteq> {#} \<and> {#} \<noteq> {#a#}"
  by (simp add: single_def Mempty_def expand_fun_eq)

lemma single_eq_single [simp]: "({#a#} = {#b#}) = (a = b)"
  by (auto simp add: single_def expand_fun_eq)

lemma union_eq_empty [iff]: "(M + N = {#}) = (M = {#} \<and> N = {#})"
  by (auto simp add: union_def Mempty_def expand_fun_eq)

lemma empty_eq_union [iff]: "({#} = M + N) = (M = {#} \<and> N = {#})"
  by (auto simp add: union_def Mempty_def expand_fun_eq)

lemma union_right_cancel [simp]: "(M + K = N + K) = (M = (N::'a multiset))"
  by (simp add: union_def expand_fun_eq)

lemma union_left_cancel [simp]: "(K + M = K + N) = (M = (N::'a multiset))"
  by (simp add: union_def expand_fun_eq)

lemma union_is_single:
    "(M + N = {#a#}) = (M = {#a#} \<and> N={#} \<or> M = {#} \<and> N = {#a#})"
  apply (simp add: Mempty_def single_def union_def add_is_1 expand_fun_eq)
  apply blast
  done

lemma single_is_union:
     "({#a#} = M + N) = ({#a#} = M \<and> N = {#} \<or> M = {#} \<and> {#a#} = N)"
  apply (unfold Mempty_def single_def union_def)
  apply (simp add: add_is_1 one_is_add expand_fun_eq)
  apply (blast dest: sym)
  done

ML"reset use_neq_simproc"
lemma add_eq_conv_diff:
  "(M + {#a#} = N + {#b#}) =
   (M = N \<and> a = b \<or> M = N - {#a#} + {#b#} \<and> N = M - {#b#} + {#a#})"
  apply (unfold single_def union_def diff_def)
  apply (simp (no_asm) add: expand_fun_eq)
  apply (rule conjI, force, safe, simp_all)
  apply (simp add: eq_sym_conv)
  done
ML"set use_neq_simproc"

declare Rep_multiset_inject [symmetric, simp del]


subsubsection {* Intersection *}

lemma multiset_inter_count:
    "count (A #\<inter> B) x = min (count A x) (count B x)"
  by (simp add: multiset_inter_def min_def)

lemma multiset_inter_commute: "A #\<inter> B = B #\<inter> A"
  by (simp add: multiset_eq_conv_count_eq multiset_inter_count
    min_max.below_inf.inf_commute)

lemma multiset_inter_assoc: "A #\<inter> (B #\<inter> C) = A #\<inter> B #\<inter> C"
  by (simp add: multiset_eq_conv_count_eq multiset_inter_count
    min_max.below_inf.inf_assoc)

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


subsection {* Induction over multisets *}

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
  shows "\<forall>f. f \<in> multiset --> setsum f {x. 0 < f x} = n --> P f"
  apply (unfold multiset_def)
  apply (induct_tac n, simp, clarify)
   apply (subgoal_tac "f = (\<lambda>a.0)")
    apply simp
    apply (rule 1)
   apply (rule ext, force, clarify)
  apply (frule setsum_SucD, clarify)
  apply (rename_tac a)
  apply (subgoal_tac "finite {x. 0 < (f (a := f a - 1)) x}")
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
  apply (subgoal_tac "{x. x \<noteq> a --> 0 < f x} = {x. 0 < f x}")
   prefer 2
   apply blast
  apply (subgoal_tac "{x. x \<noteq> a \<and> 0 < f x} = {x. 0 < f x} - {a}")
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
    apply (erule add [unfolded defns, simplified])
    done
qed

lemma MCollect_preserves_multiset:
    "M \<in> multiset ==> (\<lambda>x. if P x then M x else 0) \<in> multiset"
  apply (simp add: multiset_def)
  apply (rule finite_subset, auto)
  done

lemma count_MCollect [simp]:
    "count {# x:M. P x #} a = (if P a then count M a else 0)"
  by (simp add: count_def MCollect_def MCollect_preserves_multiset)

lemma set_of_MCollect [simp]: "set_of {# x:M. P x #} = set_of M \<inter> {x. P x}"
  by (auto simp add: set_of_def)

lemma multiset_partition: "M = {# x:M. P x #} + {# x:M. \<not> P x #}"
  by (subst multiset_eq_conv_count_eq, auto)

lemma add_eq_conv_ex:
  "(M + {#a#} = N + {#b#}) =
    (M = N \<and> a = b \<or> (\<exists>K. M = K + {#b#} \<and> N = K + {#a#}))"
  by (auto simp add: add_eq_conv_diff)

declare multiset_typedef [simp del]


subsection {* Multiset orderings *}

subsubsection {* Well-foundedness *}

definition
  mult1 :: "('a \<times> 'a) set => ('a multiset \<times> 'a multiset) set"
  "mult1 r =
    {(N, M). \<exists>a M0 K. M = M0 + {#a#} \<and> N = M0 + K \<and>
      (\<forall>b. b :# K --> (b, a) \<in> r)}"

  mult :: "('a \<times> 'a) set => ('a multiset \<times> 'a multiset) set"
  "mult r = (mult1 r)\<^sup>+"

lemma not_less_empty [iff]: "(M, {#}) \<notin> mult1 r"
  by (simp add: mult1_def)

lemma less_add: "(N, M0 + {#a#}) \<in> mult1 r ==>
    (\<exists>M. (M, M0) \<in> mult1 r \<and> N = M + {#a#}) \<or>
    (\<exists>K. (\<forall>b. b :# K --> (b, a) \<in> r) \<and> N = M0 + K)"
  (concl is "?case1 (mult1 r) \<or> ?case2")
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
        then have "M + {#a#} \<in> ?W" ..
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
      assume "!!b. (b, a) \<in> r ==> (\<forall>M \<in> ?W. M + {#b#} \<in> ?W)"
      show "\<forall>M \<in> ?W. M + {#a#} \<in> ?W"
      proof
        fix M assume "M \<in> ?W"
        then show "M + {#a#} \<in> ?W"
          by (rule acc_induct) (rule tedious_reasoning)
      qed
    qed
    then show "M + {#a#} \<in> ?W" ..
  qed
qed

theorem wf_mult1: "wf r ==> wf (mult1 r)"
  by (rule acc_wfI, rule all_accessible)

theorem wf_mult: "wf r ==> wf (mult r)"
  by (unfold mult_def, rule wf_trancl, rule wf_mult1)


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
  apply (insert one_step_implies_mult_aux, blast)
  done


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
  apply (induct rule: finite_induct)
   apply (auto intro: order_less_trans)
  done

lemma mult_less_not_refl: "\<not> M < (M::'a::order multiset)"
  apply (unfold less_multiset_def, auto)
  apply (drule trans_base_order [THEN mult_implies_one_step], auto)
  apply (drule finite_set_of [THEN mult_irrefl_aux [rule_format (no_asm)]])
  apply (simp add: set_of_eq_empty_iff)
  done

lemma mult_less_irrefl [elim!]: "M < (M::'a::order multiset) ==> R"
by (insert mult_less_not_refl, fast)


text {* Transitivity. *}

theorem mult_less_trans: "K < M ==> M < N ==> K < (N::'a::order multiset)"
  apply (unfold less_multiset_def mult_def)
  apply (blast intro: trancl_trans)
  done

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
     apply (rule mult_le_refl)
    apply (erule mult_le_trans, assumption)
   apply (erule mult_le_antisym, assumption)
  apply (rule mult_less_le)
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


subsection {* Link with lists *}

consts
  multiset_of :: "'a list \<Rightarrow> 'a multiset"
primrec
  "multiset_of [] = {#}"
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
  by (induct xs fixing: ys) (auto simp: union_ac)

lemma surj_multiset_of: "surj multiset_of"
  apply (unfold surj_def, rule allI)
  apply (rule_tac M=y in multiset_induct, auto)
  apply (rule_tac x = "x # xa" in exI, auto)
  done

lemma set_count_greater_0: "set x = {a. 0 < count (multiset_of x) a}"
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
    "multiset_of [x\<in>xs. P x] + multiset_of [x\<in>xs. \<not>P x] = multiset_of xs"
  by (induct xs) (auto simp: union_ac)

lemma count_filter:
    "count (multiset_of xs) x = length [y \<in> xs. y = x]"
  by (induct xs) auto


subsection {* Pointwise ordering induced by count *}

definition
  mset_le :: "['a multiset, 'a multiset] \<Rightarrow> bool"   ("_ \<le># _"  [50,51] 50)
  "(xs \<le># ys) = (\<forall>a. count xs a \<le> count ys a)"

lemma mset_le_refl[simp]: "xs \<le># xs"
  unfolding mset_le_def by auto

lemma mset_le_trans: "\<lbrakk> xs \<le># ys; ys \<le># zs \<rbrakk> \<Longrightarrow> xs \<le># zs"
  unfolding mset_le_def by (fast intro: order_trans)

lemma mset_le_antisym: "\<lbrakk> xs\<le># ys; ys \<le># xs\<rbrakk> \<Longrightarrow> xs = ys"
  apply (unfold mset_le_def)
  apply (rule multiset_eq_conv_count_eq[THEN iffD2])
  apply (blast intro: order_antisym)
  done

lemma mset_le_exists_conv:
  "(xs \<le># ys) = (\<exists>zs. ys = xs + zs)"
  apply (unfold mset_le_def, rule iffI, rule_tac x = "ys - xs" in exI)
  apply (auto intro: multiset_eq_conv_count_eq [THEN iffD2])
  done

lemma mset_le_mono_add_right_cancel[simp]: "(xs + zs \<le># ys + zs) = (xs \<le># ys)"
  unfolding mset_le_def by auto

lemma mset_le_mono_add_left_cancel[simp]: "(zs + xs \<le># zs + ys) = (xs \<le># ys)"
  unfolding mset_le_def by auto

lemma mset_le_mono_add: "\<lbrakk> xs \<le># ys; vs \<le># ws \<rbrakk> \<Longrightarrow> xs + vs \<le># ys + ws"
  apply (unfold mset_le_def)
  apply auto
  apply (erule_tac x=a in allE)+
  apply auto
  done

lemma mset_le_add_left[simp]: "xs \<le># xs + ys"
  unfolding mset_le_def by auto

lemma mset_le_add_right[simp]: "ys \<le># xs + ys"
  unfolding mset_le_def by auto

lemma multiset_of_remdups_le: "multiset_of (remdups x) \<le># multiset_of x"
  apply (induct x)
   apply auto
  apply (rule mset_le_trans)
   apply auto
  done

end
