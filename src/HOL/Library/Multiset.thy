(*  Title:      HOL/Library/Multiset.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Markus Wenzel, and Lawrence C Paulson
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Multisets *}

theory Multiset = Accessible_Part:

subsection {* The type of multisets *}

typedef 'a multiset = "{f::'a => nat. finite {x . 0 < f x}}"
proof
  show "(\<lambda>x. 0::nat) \<in> ?multiset" by simp
qed

lemmas multiset_typedef [simp] =
    Abs_multiset_inverse Rep_multiset_inverse Rep_multiset
  and [simp] = Rep_multiset_inject [symmetric]

constdefs
  Mempty :: "'a multiset"    ("{#}")
  "{#} == Abs_multiset (\<lambda>a. 0)"

  single :: "'a => 'a multiset"    ("{#_#}")
  "{#a#} == Abs_multiset (\<lambda>b. if b = a then 1 else 0)"

  count :: "'a multiset => 'a => nat"
  "count == Rep_multiset"

  MCollect :: "'a multiset => ('a => bool) => 'a multiset"
  "MCollect M P == Abs_multiset (\<lambda>x. if P x then Rep_multiset M x else 0)"

syntax
  "_Melem" :: "'a => 'a multiset => bool"    ("(_/ :# _)" [50, 51] 50)
  "_MCollect" :: "pttrn => 'a multiset => bool => 'a multiset"    ("(1{# _ : _./ _#})")
translations
  "a :# M" == "0 < count M a"
  "{#x:M. P#}" == "MCollect M (\<lambda>x. P)"

constdefs
  set_of :: "'a multiset => 'a set"
  "set_of M == {x. x :# M}"

instance multiset :: (type) "{plus, minus, zero}" ..

defs (overloaded)
  union_def: "M + N == Abs_multiset (\<lambda>a. Rep_multiset M a + Rep_multiset N a)"
  diff_def: "M - N == Abs_multiset (\<lambda>a. Rep_multiset M a - Rep_multiset N a)"
  Zero_multiset_def [simp]: "0 == {#}"
  size_def: "size M == setsum (count M) (set_of M)"


text {*
 \medskip Preservation of the representing set @{term multiset}.
*}

lemma const0_in_multiset [simp]: "(\<lambda>a. 0) \<in> multiset"
  apply (simp add: multiset_def)
  done

lemma only1_in_multiset [simp]: "(\<lambda>b. if b = a then 1 else 0) \<in> multiset"
  apply (simp add: multiset_def)
  done

lemma union_preserves_multiset [simp]:
    "M \<in> multiset ==> N \<in> multiset ==> (\<lambda>a. M a + N a) \<in> multiset"
  apply (unfold multiset_def)
  apply simp
  apply (drule finite_UnI)
   apply assumption
  apply (simp del: finite_Un add: Un_def)
  done

lemma diff_preserves_multiset [simp]:
    "M \<in> multiset ==> (\<lambda>a. M a - N a) \<in> multiset"
  apply (unfold multiset_def)
  apply simp
  apply (rule finite_subset)
   prefer 2
   apply assumption
  apply auto
  done


subsection {* Algebraic properties of multisets *}

subsubsection {* Union *}

theorem union_empty [simp]: "M + {#} = M \<and> {#} + M = M"
  apply (simp add: union_def Mempty_def)
  done

theorem union_commute: "M + N = N + (M::'a multiset)"
  apply (simp add: union_def add_ac)
  done

theorem union_assoc: "(M + N) + K = M + (N + (K::'a multiset))"
  apply (simp add: union_def add_ac)
  done

theorem union_lcomm: "M + (N + K) = N + (M + (K::'a multiset))"
  apply (rule union_commute [THEN trans])
  apply (rule union_assoc [THEN trans])
  apply (rule union_commute [THEN arg_cong])
  done

theorems union_ac = union_assoc union_commute union_lcomm

instance multiset :: (type) plus_ac0
proof 
  fix a b c :: "'a multiset"
  show "(a + b) + c = a + (b + c)" by (rule union_assoc)
  show "a + b = b + a" by (rule union_commute)
  show "0 + a = a" by simp
qed


subsubsection {* Difference *}

theorem diff_empty [simp]: "M - {#} = M \<and> {#} - M = {#}"
  apply (simp add: Mempty_def diff_def)
  done

theorem diff_union_inverse2 [simp]: "M + {#a#} - {#a#} = M"
  apply (simp add: union_def diff_def)
  done


subsubsection {* Count of elements *}

theorem count_empty [simp]: "count {#} a = 0"
  apply (simp add: count_def Mempty_def)
  done

theorem count_single [simp]: "count {#b#} a = (if b = a then 1 else 0)"
  apply (simp add: count_def single_def)
  done

theorem count_union [simp]: "count (M + N) a = count M a + count N a"
  apply (simp add: count_def union_def)
  done

theorem count_diff [simp]: "count (M - N) a = count M a - count N a"
  apply (simp add: count_def diff_def)
  done


subsubsection {* Set of elements *}

theorem set_of_empty [simp]: "set_of {#} = {}"
  apply (simp add: set_of_def)
  done

theorem set_of_single [simp]: "set_of {#b#} = {b}"
  apply (simp add: set_of_def)
  done

theorem set_of_union [simp]: "set_of (M + N) = set_of M \<union> set_of N"
  apply (auto simp add: set_of_def)
  done

theorem set_of_eq_empty_iff [simp]: "(set_of M = {}) = (M = {#})"
  apply (auto simp add: set_of_def Mempty_def count_def expand_fun_eq)
  done

theorem mem_set_of_iff [simp]: "(x \<in> set_of M) = (x :# M)"
  apply (auto simp add: set_of_def)
  done


subsubsection {* Size *}

theorem size_empty [simp]: "size {#} = 0"
  apply (simp add: size_def)
  done

theorem size_single [simp]: "size {#b#} = 1"
  apply (simp add: size_def)
  done

theorem finite_set_of [iff]: "finite (set_of M)"
  apply (cut_tac x = M in Rep_multiset)
  apply (simp add: multiset_def set_of_def count_def)
  done

theorem setsum_count_Int:
    "finite A ==> setsum (count N) (A \<inter> set_of N) = setsum (count N) A"
  apply (erule finite_induct)
   apply simp
  apply (simp add: Int_insert_left set_of_def)
  done

theorem size_union [simp]: "size (M + N::'a multiset) = size M + size N"
  apply (unfold size_def)
  apply (subgoal_tac "count (M + N) = (\<lambda>a. count M a + count N a)")
   prefer 2
   apply (rule ext)
   apply simp
  apply (simp (no_asm_simp) add: setsum_Un setsum_addf setsum_count_Int)
  apply (subst Int_commute)
  apply (simp (no_asm_simp) add: setsum_count_Int)
  done

theorem size_eq_0_iff_empty [iff]: "(size M = 0) = (M = {#})"
  apply (unfold size_def Mempty_def count_def)
  apply auto
  apply (simp add: set_of_def count_def expand_fun_eq)
  done

theorem size_eq_Suc_imp_elem: "size M = Suc n ==> \<exists>a. a :# M"
  apply (unfold size_def)
  apply (drule setsum_SucD)
  apply auto
  done


subsubsection {* Equality of multisets *}

theorem multiset_eq_conv_count_eq: "(M = N) = (\<forall>a. count M a = count N a)"
  apply (simp add: count_def expand_fun_eq)
  done

theorem single_not_empty [simp]: "{#a#} \<noteq> {#} \<and> {#} \<noteq> {#a#}"
  apply (simp add: single_def Mempty_def expand_fun_eq)
  done

theorem single_eq_single [simp]: "({#a#} = {#b#}) = (a = b)"
  apply (auto simp add: single_def expand_fun_eq)
  done

theorem union_eq_empty [iff]: "(M + N = {#}) = (M = {#} \<and> N = {#})"
  apply (auto simp add: union_def Mempty_def expand_fun_eq)
  done

theorem empty_eq_union [iff]: "({#} = M + N) = (M = {#} \<and> N = {#})"
  apply (auto simp add: union_def Mempty_def expand_fun_eq)
  done

theorem union_right_cancel [simp]: "(M + K = N + K) = (M = (N::'a multiset))"
  apply (simp add: union_def expand_fun_eq)
  done

theorem union_left_cancel [simp]: "(K + M = K + N) = (M = (N::'a multiset))"
  apply (simp add: union_def expand_fun_eq)
  done

theorem union_is_single:
    "(M + N = {#a#}) = (M = {#a#} \<and> N={#} \<or> M = {#} \<and> N = {#a#})"
  apply (unfold Mempty_def single_def union_def)
  apply (simp add: add_is_1 expand_fun_eq)
  apply blast
  done

theorem single_is_union:
  "({#a#} = M + N) =
    ({#a#} = M \<and> N = {#} \<or> M = {#} \<and> {#a#} = N)"
  apply (unfold Mempty_def single_def union_def)
  apply (simp add: add_is_1 one_is_add expand_fun_eq)
  apply (blast dest: sym)
  done

theorem add_eq_conv_diff:
  "(M + {#a#} = N + {#b#}) =
    (M = N \<and> a = b \<or>
      M = N - {#a#} + {#b#} \<and> N = M - {#b#} + {#a#})"
  apply (unfold single_def union_def diff_def)
  apply (simp (no_asm) add: expand_fun_eq)
  apply (rule conjI)
   apply force
  apply safe
  apply simp_all
  apply (simp add: eq_sym_conv)
  done

(*
val prems = Goal
 "[| !!F. [| finite F; !G. G < F --> P G |] ==> P F |] ==> finite F --> P F";
by (res_inst_tac [("a","F"),("f","\<lambda>A. if finite A then card A else 0")]
     measure_induct 1);
by (Clarify_tac 1);
by (resolve_tac prems 1);
 by (assume_tac 1);
by (Clarify_tac 1);
by (subgoal_tac "finite G" 1);
 by (fast_tac (claset() addDs [finite_subset,order_less_le RS iffD1]) 2);
by (etac allE 1);
by (etac impE 1);
 by (Blast_tac 2);
by (asm_simp_tac (simpset() addsimps [psubset_card]) 1);
no_qed();
val lemma = result();

val prems = Goal
 "[| finite F; !!F. [| finite F; !G. G < F --> P G |] ==> P F |] ==> P F";
by (rtac (lemma RS mp) 1);
by (REPEAT(ares_tac prems 1));
qed "finite_psubset_induct";

Better: use wf_finite_psubset in WF_Rel
*)


subsection {* Induction over multisets *}

lemma setsum_decr:
  "finite F ==> (0::nat) < f a ==>
    setsum (f (a := f a - 1)) F = (if a \<in> F then setsum f F - 1 else setsum f F)"
  apply (erule finite_induct)
   apply auto
  apply (drule_tac a = a in mk_disjoint_insert)
  apply auto
  done

lemma rep_multiset_induct_aux:
  "P (\<lambda>a. (0::nat)) ==> (!!f b. f \<in> multiset ==> P f ==> P (f (b := f b + 1)))
    ==> \<forall>f. f \<in> multiset --> setsum f {x. 0 < f x} = n --> P f"
proof -
  case rule_context
  note premises = this [unfolded multiset_def]
  show ?thesis
    apply (unfold multiset_def)
    apply (induct_tac n)
     apply simp
     apply clarify
     apply (subgoal_tac "f = (\<lambda>a.0)")
      apply simp
      apply (rule premises)
     apply (rule ext)
     apply force
    apply clarify
    apply (frule setsum_SucD)
    apply clarify
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
     apply (erule ssubst, rule premises)
     apply blast
    apply (erule allE, erule impE, erule_tac [2] mp)
     apply blast
    apply (simp (no_asm_simp) add: setsum_decr del: fun_upd_apply One_nat_def)
    apply (subgoal_tac "{x. x \<noteq> a --> 0 < f x} = {x. 0 < f x}")
     prefer 2
     apply blast
    apply (subgoal_tac "{x. x \<noteq> a \<and> 0 < f x} = {x. 0 < f x} - {a}")
     prefer 2
     apply blast
    apply (simp add: le_imp_diff_is_add setsum_diff1 cong: conj_cong)
    done
qed

theorem rep_multiset_induct:
  "f \<in> multiset ==> P (\<lambda>a. 0) ==>
    (!!f b. f \<in> multiset ==> P f ==> P (f (b := f b + 1))) ==> P f"
  apply (insert rep_multiset_induct_aux)
  apply blast
  done

theorem multiset_induct [induct type: multiset]:
  "P {#} ==> (!!M x. P M ==> P (M + {#x#})) ==> P M"
proof -
  note defns = union_def single_def Mempty_def
  assume prem1 [unfolded defns]: "P {#}"
  assume prem2 [unfolded defns]: "!!M x. P M ==> P (M + {#x#})"
  show ?thesis
    apply (rule Rep_multiset_inverse [THEN subst])
    apply (rule Rep_multiset [THEN rep_multiset_induct])
     apply (rule prem1)
    apply (subgoal_tac "f (b := f b + 1) = (\<lambda>a. f a + (if a = b then 1 else 0))")
     prefer 2
     apply (simp add: expand_fun_eq)
    apply (erule ssubst)
    apply (erule Abs_multiset_inverse [THEN subst])
    apply (erule prem2 [simplified])
    done
qed


lemma MCollect_preserves_multiset:
    "M \<in> multiset ==> (\<lambda>x. if P x then M x else 0) \<in> multiset"
  apply (simp add: multiset_def)
  apply (rule finite_subset)
   apply auto
  done

theorem count_MCollect [simp]:
    "count {# x:M. P x #} a = (if P a then count M a else 0)"
  apply (unfold count_def MCollect_def)
  apply (simp add: MCollect_preserves_multiset)
  done

theorem set_of_MCollect [simp]: "set_of {# x:M. P x #} = set_of M \<inter> {x. P x}"
  apply (auto simp add: set_of_def)
  done

theorem multiset_partition: "M = {# x:M. P x #} + {# x:M. \<not> P x #}"
  apply (subst multiset_eq_conv_count_eq)
  apply auto
  done

declare Rep_multiset_inject [symmetric, simp del]
declare multiset_typedef [simp del]

theorem add_eq_conv_ex:
  "(M + {#a#} = N + {#b#}) =
    (M = N \<and> a = b \<or> (\<exists>K. M = K + {#b#} \<and> N = K + {#a#}))"
  apply (auto simp add: add_eq_conv_diff)
  done


subsection {* Multiset orderings *}

subsubsection {* Well-foundedness *}

constdefs
  mult1 :: "('a \<times> 'a) set => ('a multiset \<times> 'a multiset) set"
  "mult1 r ==
    {(N, M). \<exists>a M0 K. M = M0 + {#a#} \<and> N = M0 + K \<and>
      (\<forall>b. b :# K --> (b, a) \<in> r)}"

  mult :: "('a \<times> 'a) set => ('a multiset \<times> 'a multiset) set"
  "mult r == (mult1 r)\<^sup>+"

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
  hence "\<exists>a' M0' K.
      M0 + {#a#} = M0' + {#a'#} \<and> N = M0' + K \<and> ?r K a'" by simp
  thus "?case1 \<or> ?case2"
  proof (elim exE conjE)
    fix a' M0' K
    assume N: "N = M0' + K" and r: "?r K a'"
    assume "M0 + {#a#} = M0' + {#a'#}"
    hence "M0 = M0' \<and> a = a' \<or>
        (\<exists>K'. M0 = K' + {#a'#} \<and> M0' = K' + {#a#})"
      by (simp only: add_eq_conv_ex)
    thus ?thesis
    proof (elim disjE conjE exE)
      assume "M0 = M0'" "a = a'"
      with N r have "?r K a \<and> N = M0 + K" by simp
      hence ?case2 .. thus ?thesis ..
    next
      fix K'
      assume "M0' = K' + {#a#}"
      with N have n: "N = K' + K + {#a#}" by (simp add: union_ac)

      assume "M0 = K' + {#a'#}"
      with r have "?R (K' + K) M0" by blast
      with n have ?case1 by simp thus ?thesis ..
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
      hence "((\<exists>M. (M, M0) \<in> ?R \<and> N = M + {#a#}) \<or>
          (\<exists>K. (\<forall>b. b :# K --> (b, a) \<in> r) \<and> N = M0 + K))"
        by (rule less_add)
      thus "N \<in> ?W"
      proof (elim exE disjE conjE)
        fix M assume "(M, M0) \<in> ?R" and N: "N = M + {#a#}"
        from acc_hyp have "(M, M0) \<in> ?R --> M + {#a#} \<in> ?W" ..
        hence "M + {#a#} \<in> ?W" ..
        thus "N \<in> ?W" by (simp only: N)
      next
        fix K
        assume N: "N = M0 + K"
        assume "\<forall>b. b :# K --> (b, a) \<in> r"
        have "?this --> M0 + K \<in> ?W" (is "?P K")
        proof (induct K)
          from M0 have "M0 + {#} \<in> ?W" by simp
          thus "?P {#}" ..

          fix K x assume hyp: "?P K"
          show "?P (K + {#x#})"
          proof
            assume a: "\<forall>b. b :# (K + {#x#}) --> (b, a) \<in> r"
            hence "(x, a) \<in> r" by simp
            with wf_hyp have b: "\<forall>M \<in> ?W. M + {#x#} \<in> ?W" by blast

            from a hyp have "M0 + K \<in> ?W" by simp
            with b have "(M0 + K) + {#x#} \<in> ?W" ..
            thus "M0 + (K + {#x#}) \<in> ?W" by (simp only: union_assoc)
          qed
        qed
        hence "M0 + K \<in> ?W" ..
        thus "N \<in> ?W" by (simp only: N)
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
        thus "M + {#a#} \<in> ?W"
          by (rule acc_induct) (rule tedious_reasoning)
      qed
    qed
    thus "M + {#a#} \<in> ?W" ..
  qed
qed

theorem wf_mult1: "wf r ==> wf (mult1 r)"
  by (rule acc_wfI, rule all_accessible)

theorem wf_mult: "wf r ==> wf (mult r)"
  by (unfold mult_def, rule wf_trancl, rule wf_mult1)


subsubsection {* Closure-free presentation *}

(*Badly needed: a linear arithmetic procedure for multisets*)

lemma diff_union_single_conv: "a :# J ==> I + J - {#a#} = I + (J - {#a#})"
  apply (simp add: multiset_eq_conv_count_eq)
  done

text {* One direction. *}

lemma mult_implies_one_step:
  "trans r ==> (M, N) \<in> mult r ==>
    \<exists>I J K. N = I + J \<and> M = I + K \<and> J \<noteq> {#} \<and>
    (\<forall>k \<in> set_of K. \<exists>j \<in> set_of J. (k, j) \<in> r)"
  apply (unfold mult_def mult1_def set_of_def)
  apply (erule converse_trancl_induct)
  apply clarify
   apply (rule_tac x = M0 in exI)
   apply simp
  apply clarify
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
    apply (drule_tac f = "\<lambda>M. M - {#a#}" in arg_cong)
    apply simp
    apply (simp add: multiset_eq_conv_count_eq split: nat_diff_split)
   apply (simp (no_asm_use) add: trans_def)
   apply blast
  apply (subgoal_tac "a :# (M0 + {#a#})")
   apply simp
  apply (simp (no_asm))
  done

lemma elem_imp_eq_diff_union: "a :# M ==> M = M - {#a#} + {#a#}"
  apply (simp add: multiset_eq_conv_count_eq)
  done

lemma size_eq_Suc_imp_eq_union: "size M = Suc n ==> \<exists>a N. M = N + {#a#}"
  apply (erule size_eq_Suc_imp_elem [THEN exE])
  apply (drule elem_imp_eq_diff_union)
  apply auto
  done

lemma one_step_implies_mult_aux:
  "trans r ==>
    \<forall>I J K. (size J = n \<and> J \<noteq> {#} \<and> (\<forall>k \<in> set_of K. \<exists>j \<in> set_of J. (k, j) \<in> r))
      --> (I + K, I + J) \<in> mult r"
  apply (induct_tac n)
   apply auto
  apply (frule size_eq_Suc_imp_eq_union)
  apply clarify
  apply (rename_tac "J'")
  apply simp
  apply (erule notE)
   apply auto
  apply (case_tac "J' = {#}")
   apply (simp add: mult_def)
   apply (rule r_into_trancl)
   apply (simp add: mult1_def set_of_def)
   apply blast
  txt {* Now we know @{term "J' \<noteq> {#}"}. *}
  apply (cut_tac M = K and P = "\<lambda>x. (x, a) \<in> r" in multiset_partition)
  apply (erule_tac P = "\<forall>k \<in> set_of K. ?P k" in rev_mp)
  apply (erule ssubst)
  apply (simp add: Ball_def)
  apply auto
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

theorem one_step_implies_mult:
  "trans r ==> J \<noteq> {#} ==> \<forall>k \<in> set_of K. \<exists>j \<in> set_of J. (k, j) \<in> r
    ==> (I + K, I + J) \<in> mult r"
  apply (insert one_step_implies_mult_aux)
  apply blast
  done


subsubsection {* Partial-order properties *}

instance multiset :: (type) ord ..

defs (overloaded)
  less_multiset_def: "M' < M == (M', M) \<in> mult {(x', x). x' < x}"
  le_multiset_def: "M' <= M == M' = M \<or> M' < (M::'a multiset)"

lemma trans_base_order: "trans {(x', x). x' < (x::'a::order)}"
  apply (unfold trans_def)
  apply (blast intro: order_less_trans)
  done

text {*
 \medskip Irreflexivity.
*}

lemma mult_irrefl_aux:
    "finite A ==> (\<forall>x \<in> A. \<exists>y \<in> A. x < (y::'a::order)) --> A = {}"
  apply (erule finite_induct)
   apply (auto intro: order_less_trans)
  done

theorem mult_less_not_refl: "\<not> M < (M::'a::order multiset)"
  apply (unfold less_multiset_def)
  apply auto
  apply (drule trans_base_order [THEN mult_implies_one_step])
  apply auto
  apply (drule finite_set_of [THEN mult_irrefl_aux [rule_format (no_asm)]])
  apply (simp add: set_of_eq_empty_iff)
  done

lemma mult_less_irrefl [elim!]: "M < (M::'a::order multiset) ==> R"
  apply (insert mult_less_not_refl)
  apply fast
  done


text {* Transitivity. *}

theorem mult_less_trans: "K < M ==> M < N ==> K < (N::'a::order multiset)"
  apply (unfold less_multiset_def mult_def)
  apply (blast intro: trancl_trans)
  done

text {* Asymmetry. *}

theorem mult_less_not_sym: "M < N ==> \<not> N < (M::'a::order multiset)"
  apply auto
  apply (rule mult_less_not_refl [THEN notE])
  apply (erule mult_less_trans)
  apply assumption
  done

theorem mult_less_asym:
    "M < N ==> (\<not> P ==> N < (M::'a::order multiset)) ==> P"
  apply (insert mult_less_not_sym)
  apply blast
  done

theorem mult_le_refl [iff]: "M <= (M::'a::order multiset)"
  apply (unfold le_multiset_def)
  apply auto
  done

text {* Anti-symmetry. *}

theorem mult_le_antisym:
    "M <= N ==> N <= M ==> M = (N::'a::order multiset)"
  apply (unfold le_multiset_def)
  apply (blast dest: mult_less_not_sym)
  done

text {* Transitivity. *}

theorem mult_le_trans:
    "K <= M ==> M <= N ==> K <= (N::'a::order multiset)"
  apply (unfold le_multiset_def)
  apply (blast intro: mult_less_trans)
  done

theorem mult_less_le: "(M < N) = (M <= N \<and> M \<noteq> (N::'a::order multiset))"
  apply (unfold le_multiset_def)
  apply auto
  done

text {* Partial order. *}

instance multiset :: (order) order
  apply intro_classes
     apply (rule mult_le_refl)
    apply (erule mult_le_trans)
    apply assumption
   apply (erule mult_le_antisym)
   apply assumption
  apply (rule mult_less_le)
  done


subsubsection {* Monotonicity of multiset union *}

theorem mult1_union:
    "(B, D) \<in> mult1 r ==> trans r ==> (C + B, C + D) \<in> mult1 r"
  apply (unfold mult1_def)
  apply auto
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

theorem union_less_mono:
    "A < C ==> B < D ==> A + B < C + (D::'a::order multiset)"
  apply (blast intro!: union_less_mono1 union_less_mono2 mult_less_trans)
  done

theorem union_le_mono:
    "A <= C ==> B <= D ==> A + B <= C + (D::'a::order multiset)"
  apply (unfold le_multiset_def)
  apply (blast intro: union_less_mono union_less_mono1 union_less_mono2)
  done

theorem empty_leI [iff]: "{#} <= (M::'a::order multiset)"
  apply (unfold le_multiset_def less_multiset_def)
  apply (case_tac "M = {#}")
   prefer 2
   apply (subgoal_tac "({#} + {#}, {#} + M) \<in> mult (Collect (split op <))")
    prefer 2
    apply (rule one_step_implies_mult)
      apply (simp only: trans_def)
      apply auto
  done

theorem union_upper1: "A <= A + (B::'a::order multiset)"
  apply (subgoal_tac "A + {#} <= A + B")
   prefer 2
   apply (rule union_le_mono)
    apply auto
  done

theorem union_upper2: "B <= A + (B::'a::order multiset)"
  apply (subst union_commute, rule union_upper1)
  done

end
