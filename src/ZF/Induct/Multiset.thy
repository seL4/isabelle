(*  Title:      ZF/Induct/Multiset.thy
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory

A definitional theory of multisets,
including a wellfoundedness proof for the multiset order.

The theory features ordinal multisets and the usual ordering.
*)

theory Multiset
imports FoldSet Acc
begin

abbreviation (input)
  -- {* Short cut for multiset space *}
  Mult :: "i=>i" where
  "Mult(A) == A -||> nat-{0}"

definition
  (* This is the original "restrict" from ZF.thy.
     Restricts the function f to the domain A
     FIXME: adapt Multiset to the new "restrict". *)
  funrestrict :: "[i,i] => i"  where
  "funrestrict(f,A) == \<lambda>x \<in> A. f`x"

definition
  (* M is a multiset *)
  multiset :: "i => o"  where
  "multiset(M) == \<exists>A. M \<in> A -> nat-{0} & Finite(A)"

definition
  mset_of :: "i=>i"  where
  "mset_of(M) == domain(M)"

definition
  munion    :: "[i, i] => i" (infixl "+#" 65)  where
  "M +# N == \<lambda>x \<in> mset_of(M) Un mset_of(N).
     if x \<in> mset_of(M) Int mset_of(N) then  (M`x) #+ (N`x)
     else (if x \<in> mset_of(M) then M`x else N`x)"

definition
  (*convert a function to a multiset by eliminating 0*)
  normalize :: "i => i"  where
  "normalize(f) ==
       if (\<exists>A. f \<in> A -> nat & Finite(A)) then
            funrestrict(f, {x \<in> mset_of(f). 0 < f`x})
       else 0"

definition
  mdiff  :: "[i, i] => i" (infixl "-#" 65)  where
  "M -# N ==  normalize(\<lambda>x \<in> mset_of(M).
                        if x \<in> mset_of(N) then M`x #- N`x else M`x)"

definition
  (* set of elements of a multiset *)
  msingle :: "i => i"    ("{#_#}")  where
  "{#a#} == {<a, 1>}"

definition
  MCollect :: "[i, i=>o] => i"  (*comprehension*)  where
  "MCollect(M, P) == funrestrict(M, {x \<in> mset_of(M). P(x)})"

definition
  (* Counts the number of occurences of an element in a multiset *)
  mcount :: "[i, i] => i"  where
  "mcount(M, a) == if a \<in> mset_of(M) then  M`a else 0"

definition
  msize :: "i => i"  where
  "msize(M) == setsum(%a. $# mcount(M,a), mset_of(M))"

abbreviation
  melem :: "[i,i] => o"    ("(_/ :# _)" [50, 51] 50)  where
  "a :# M == a \<in> mset_of(M)"

syntax
  "_MColl" :: "[pttrn, i, o] => i" ("(1{# _ : _./ _#})")
syntax (xsymbols)
  "_MColl" :: "[pttrn, i, o] => i" ("(1{# _ \<in> _./ _#})")
translations
  "{#x \<in> M. P#}" == "CONST MCollect(M, %x. P)"

  (* multiset orderings *)

definition
   (* multirel1 has to be a set (not a predicate) so that we can form
      its transitive closure and reason about wf(.) and acc(.) *)
  multirel1 :: "[i,i]=>i"  where
  "multirel1(A, r) ==
     {<M, N> \<in> Mult(A)*Mult(A).
      \<exists>a \<in> A. \<exists>M0 \<in> Mult(A). \<exists>K \<in> Mult(A).
      N=M0 +# {#a#} & M=M0 +# K & (\<forall>b \<in> mset_of(K). <b,a> \<in> r)}"

definition
  multirel :: "[i, i] => i"  where
  "multirel(A, r) == multirel1(A, r)^+"                 

  (* ordinal multiset orderings *)

definition
  omultiset :: "i => o"  where
  "omultiset(M) == \<exists>i. Ord(i) & M \<in> Mult(field(Memrel(i)))"

definition
  mless :: "[i, i] => o" (infixl "<#" 50)  where
  "M <# N ==  \<exists>i. Ord(i) & <M, N> \<in> multirel(field(Memrel(i)), Memrel(i))"

definition
  mle  :: "[i, i] => o"  (infixl "<#=" 50)  where
  "M <#= N == (omultiset(M) & M = N) | M <# N"


subsection{*Properties of the original "restrict" from ZF.thy*}

lemma funrestrict_subset: "[| f \<in> Pi(C,B);  A\<subseteq>C |] ==> funrestrict(f,A) \<subseteq> f"
by (auto simp add: funrestrict_def lam_def intro: apply_Pair)

lemma funrestrict_type:
    "[| !!x. x \<in> A ==> f`x \<in> B(x) |] ==> funrestrict(f,A) \<in> Pi(A,B)"
by (simp add: funrestrict_def lam_type)

lemma funrestrict_type2: "[| f \<in> Pi(C,B);  A\<subseteq>C |] ==> funrestrict(f,A) \<in> Pi(A,B)"
by (blast intro: apply_type funrestrict_type)

lemma funrestrict [simp]: "a \<in> A ==> funrestrict(f,A) ` a = f`a"
by (simp add: funrestrict_def)

lemma funrestrict_empty [simp]: "funrestrict(f,0) = 0"
by (simp add: funrestrict_def)

lemma domain_funrestrict [simp]: "domain(funrestrict(f,C)) = C"
by (auto simp add: funrestrict_def lam_def)

lemma fun_cons_funrestrict_eq:
     "f \<in> cons(a, b) -> B ==> f = cons(<a, f ` a>, funrestrict(f, b))"
apply (rule equalityI)
prefer 2 apply (blast intro: apply_Pair funrestrict_subset [THEN subsetD])
apply (auto dest!: Pi_memberD simp add: funrestrict_def lam_def)
done

declare domain_of_fun [simp]
declare domainE [rule del]


text{* A useful simplification rule *}
lemma multiset_fun_iff:
     "(f \<in> A -> nat-{0}) <-> f \<in> A->nat&(\<forall>a \<in> A. f`a \<in> nat & 0 < f`a)"
apply safe
apply (rule_tac [4] B1 = "range (f) " in Pi_mono [THEN subsetD])
apply (auto intro!: Ord_0_lt
            dest: apply_type Diff_subset [THEN Pi_mono, THEN subsetD]
            simp add: range_of_fun apply_iff)
done

(** The multiset space  **)
lemma multiset_into_Mult: "[| multiset(M); mset_of(M)\<subseteq>A |] ==> M \<in> Mult(A)"
apply (simp add: multiset_def)
apply (auto simp add: multiset_fun_iff mset_of_def)
apply (rule_tac B1 = "nat-{0}" in FiniteFun_mono [THEN subsetD], simp_all)
apply (rule Finite_into_Fin [THEN [2] Fin_mono [THEN subsetD], THEN fun_FiniteFunI])
apply (simp_all (no_asm_simp) add: multiset_fun_iff)
done

lemma Mult_into_multiset: "M \<in> Mult(A) ==> multiset(M) & mset_of(M)\<subseteq>A"
apply (simp add: multiset_def mset_of_def)
apply (frule FiniteFun_is_fun)
apply (drule FiniteFun_domain_Fin)
apply (frule FinD, clarify)
apply (rule_tac x = "domain (M) " in exI)
apply (blast intro: Fin_into_Finite)
done

lemma Mult_iff_multiset: "M \<in> Mult(A) <-> multiset(M) & mset_of(M)\<subseteq>A"
by (blast dest: Mult_into_multiset intro: multiset_into_Mult)

lemma multiset_iff_Mult_mset_of: "multiset(M) <-> M \<in> Mult(mset_of(M))"
by (auto simp add: Mult_iff_multiset)


text{*The @{term multiset} operator*}

(* the empty multiset is 0 *)

lemma multiset_0 [simp]: "multiset(0)"
by (auto intro: FiniteFun.intros simp add: multiset_iff_Mult_mset_of)


text{*The @{term mset_of} operator*}

lemma multiset_set_of_Finite [simp]: "multiset(M) ==> Finite(mset_of(M))"
by (simp add: multiset_def mset_of_def, auto)

lemma mset_of_0 [iff]: "mset_of(0) = 0"
by (simp add: mset_of_def)

lemma mset_is_0_iff: "multiset(M) ==> mset_of(M)=0 <-> M=0"
by (auto simp add: multiset_def mset_of_def)

lemma mset_of_single [iff]: "mset_of({#a#}) = {a}"
by (simp add: msingle_def mset_of_def)

lemma mset_of_union [iff]: "mset_of(M +# N) = mset_of(M) Un mset_of(N)"
by (simp add: mset_of_def munion_def)

lemma mset_of_diff [simp]: "mset_of(M)\<subseteq>A ==> mset_of(M -# N) \<subseteq> A"
by (auto simp add: mdiff_def multiset_def normalize_def mset_of_def)

(* msingle *)

lemma msingle_not_0 [iff]: "{#a#} \<noteq> 0 & 0 \<noteq> {#a#}"
by (simp add: msingle_def)

lemma msingle_eq_iff [iff]: "({#a#} = {#b#}) <->  (a = b)"
by (simp add: msingle_def)

lemma msingle_multiset [iff,TC]: "multiset({#a#})"
apply (simp add: multiset_def msingle_def)
apply (rule_tac x = "{a}" in exI)
apply (auto intro: Finite_cons Finite_0 fun_extend3)
done

(** normalize **)

lemmas Collect_Finite = Collect_subset [THEN subset_Finite]

lemma normalize_idem [simp]: "normalize(normalize(f)) = normalize(f)"
apply (simp add: normalize_def funrestrict_def mset_of_def)
apply (case_tac "\<exists>A. f \<in> A -> nat & Finite (A) ")
apply clarify
apply (drule_tac x = "{x \<in> domain (f) . 0 < f ` x}" in spec)
apply auto
apply (auto  intro!: lam_type simp add: Collect_Finite)
done

lemma normalize_multiset [simp]: "multiset(M) ==> normalize(M) = M"
by (auto simp add: multiset_def normalize_def mset_of_def funrestrict_def multiset_fun_iff)

lemma multiset_normalize [simp]: "multiset(normalize(f))"
apply (simp add: normalize_def)
apply (simp add: normalize_def mset_of_def multiset_def, auto)
apply (rule_tac x = "{x \<in> A . 0<f`x}" in exI)
apply (auto intro: Collect_subset [THEN subset_Finite] funrestrict_type)
done

(** Typechecking rules for union and difference of multisets **)

(* union *)

lemma munion_multiset [simp]: "[| multiset(M); multiset(N) |] ==> multiset(M +# N)"
apply (unfold multiset_def munion_def mset_of_def, auto)
apply (rule_tac x = "A Un Aa" in exI)
apply (auto intro!: lam_type intro: Finite_Un simp add: multiset_fun_iff zero_less_add)
done

(* difference *)

lemma mdiff_multiset [simp]: "multiset(M -# N)"
by (simp add: mdiff_def)

(** Algebraic properties of multisets **)

(* Union *)

lemma munion_0 [simp]: "multiset(M) ==> M +# 0 = M & 0 +# M = M"
apply (simp add: multiset_def)
apply (auto simp add: munion_def mset_of_def)
done

lemma munion_commute: "M +# N = N +# M"
by (auto intro!: lam_cong simp add: munion_def)

lemma munion_assoc: "(M +# N) +# K = M +# (N +# K)"
apply (unfold munion_def mset_of_def)
apply (rule lam_cong, auto)
done

lemma munion_lcommute: "M +# (N +# K) = N +# (M +# K)"
apply (unfold munion_def mset_of_def)
apply (rule lam_cong, auto)
done

lemmas munion_ac = munion_commute munion_assoc munion_lcommute

(* Difference *)

lemma mdiff_self_eq_0 [simp]: "M -# M = 0"
by (simp add: mdiff_def normalize_def mset_of_def)

lemma mdiff_0 [simp]: "0 -# M = 0"
by (simp add: mdiff_def normalize_def)

lemma mdiff_0_right [simp]: "multiset(M) ==> M -# 0 = M"
by (auto simp add: multiset_def mdiff_def normalize_def multiset_fun_iff mset_of_def funrestrict_def)

lemma mdiff_union_inverse2 [simp]: "multiset(M) ==> M +# {#a#} -# {#a#} = M"
apply (unfold multiset_def munion_def mdiff_def msingle_def normalize_def mset_of_def)
apply (auto cong add: if_cong simp add: ltD multiset_fun_iff funrestrict_def subset_Un_iff2 [THEN iffD1])
prefer 2 apply (force intro!: lam_type)
apply (subgoal_tac [2] "{x \<in> A \<union> {a} . x \<noteq> a \<and> x \<in> A} = A")
apply (rule fun_extension, auto)
apply (drule_tac x = "A Un {a}" in spec)
apply (simp add: Finite_Un)
apply (force intro!: lam_type)
done

(** Count of elements **)

lemma mcount_type [simp,TC]: "multiset(M) ==> mcount(M, a) \<in> nat"
by (auto simp add: multiset_def mcount_def mset_of_def multiset_fun_iff)

lemma mcount_0 [simp]: "mcount(0, a) = 0"
by (simp add: mcount_def)

lemma mcount_single [simp]: "mcount({#b#}, a) = (if a=b then 1 else 0)"
by (simp add: mcount_def mset_of_def msingle_def)

lemma mcount_union [simp]: "[| multiset(M); multiset(N) |]
                     ==>  mcount(M +# N, a) = mcount(M, a) #+ mcount (N, a)"
apply (auto simp add: multiset_def multiset_fun_iff mcount_def munion_def mset_of_def)
done

lemma mcount_diff [simp]:
     "multiset(M) ==> mcount(M -# N, a) = mcount(M, a) #- mcount(N, a)"
apply (simp add: multiset_def)
apply (auto dest!: not_lt_imp_le
     simp add: mdiff_def multiset_fun_iff mcount_def normalize_def mset_of_def)
apply (force intro!: lam_type)
apply (force intro!: lam_type)
done

lemma mcount_elem: "[| multiset(M); a \<in> mset_of(M) |] ==> 0 < mcount(M, a)"
apply (simp add: multiset_def, clarify)
apply (simp add: mcount_def mset_of_def)
apply (simp add: multiset_fun_iff)
done

(** msize **)

lemma msize_0 [simp]: "msize(0) = #0"
by (simp add: msize_def)

lemma msize_single [simp]: "msize({#a#}) = #1"
by (simp add: msize_def)

lemma msize_type [simp,TC]: "msize(M) \<in> int"
by (simp add: msize_def)

lemma msize_zpositive: "multiset(M)==> #0 $\<le> msize(M)"
by (auto simp add: msize_def intro: g_zpos_imp_setsum_zpos)

lemma msize_int_of_nat: "multiset(M) ==> \<exists>n \<in> nat. msize(M)= $# n"
apply (rule not_zneg_int_of)
apply (simp_all (no_asm_simp) add: msize_type [THEN znegative_iff_zless_0] not_zless_iff_zle msize_zpositive)
done

lemma not_empty_multiset_imp_exist:
     "[| M\<noteq>0; multiset(M) |] ==> \<exists>a \<in> mset_of(M). 0 < mcount(M, a)"
apply (simp add: multiset_def)
apply (erule not_emptyE)
apply (auto simp add: mset_of_def mcount_def multiset_fun_iff)
apply (blast dest!: fun_is_rel)
done

lemma msize_eq_0_iff: "multiset(M) ==> msize(M)=#0 <-> M=0"
apply (simp add: msize_def, auto)
apply (rule_tac P = "setsum (?u,?v) \<noteq> #0" in swap)
apply blast
apply (drule not_empty_multiset_imp_exist, assumption, clarify)
apply (subgoal_tac "Finite (mset_of (M) - {a}) ")
 prefer 2 apply (simp add: Finite_Diff)
apply (subgoal_tac "setsum (%x. $# mcount (M, x), cons (a, mset_of (M) -{a}))=#0")
 prefer 2 apply (simp add: cons_Diff, simp)
apply (subgoal_tac "#0 $\<le> setsum (%x. $# mcount (M, x), mset_of (M) - {a}) ")
apply (rule_tac [2] g_zpos_imp_setsum_zpos)
apply (auto simp add: Finite_Diff not_zless_iff_zle [THEN iff_sym] znegative_iff_zless_0 [THEN iff_sym])
apply (rule not_zneg_int_of [THEN bexE])
apply (auto simp del: int_of_0 simp add: int_of_add [symmetric] int_of_0 [symmetric])
done

lemma setsum_mcount_Int:
     "Finite(A) ==> setsum(%a. $# mcount(N, a), A Int mset_of(N))
                  = setsum(%a. $# mcount(N, a), A)"
apply (induct rule: Finite_induct)
 apply auto
apply (subgoal_tac "Finite (B Int mset_of (N))")
prefer 2 apply (blast intro: subset_Finite)
apply (auto simp add: mcount_def Int_cons_left)
done

lemma msize_union [simp]:
     "[| multiset(M); multiset(N) |] ==> msize(M +# N) = msize(M) $+ msize(N)"
apply (simp add: msize_def setsum_Un setsum_addf int_of_add setsum_mcount_Int)
apply (subst Int_commute)
apply (simp add: setsum_mcount_Int)
done

lemma msize_eq_succ_imp_elem: "[|msize(M)= $# succ(n); n \<in> nat|] ==> \<exists>a. a \<in> mset_of(M)"
apply (unfold msize_def)
apply (blast dest: setsum_succD)
done

(** Equality of multisets **)

lemma equality_lemma:
     "[| multiset(M); multiset(N); \<forall>a. mcount(M, a)=mcount(N, a) |]
      ==> mset_of(M)=mset_of(N)"
apply (simp add: multiset_def)
apply (rule sym, rule equalityI)
apply (auto simp add: multiset_fun_iff mcount_def mset_of_def)
apply (drule_tac [!] x=x in spec)
apply (case_tac [2] "x \<in> Aa", case_tac "x \<in> A", auto)
done

lemma multiset_equality:
  "[| multiset(M); multiset(N) |]==> M=N<->(\<forall>a. mcount(M, a)=mcount(N, a))"
apply auto
apply (subgoal_tac "mset_of (M) = mset_of (N) ")
prefer 2 apply (blast intro: equality_lemma)
apply (simp add: multiset_def mset_of_def)
apply (auto simp add: multiset_fun_iff)
apply (rule fun_extension)
apply (blast, blast)
apply (drule_tac x = x in spec)
apply (auto simp add: mcount_def mset_of_def)
done

(** More algebraic properties of multisets **)

lemma munion_eq_0_iff [simp]: "[|multiset(M); multiset(N)|]==>(M +# N =0) <-> (M=0 & N=0)"
by (auto simp add: multiset_equality)

lemma empty_eq_munion_iff [simp]: "[|multiset(M); multiset(N)|]==>(0=M +# N) <-> (M=0 & N=0)"
apply (rule iffI, drule sym)
apply (simp_all add: multiset_equality)
done

lemma munion_right_cancel [simp]:
     "[| multiset(M); multiset(N); multiset(K) |]==>(M +# K = N +# K)<->(M=N)"
by (auto simp add: multiset_equality)

lemma munion_left_cancel [simp]:
  "[|multiset(K); multiset(M); multiset(N)|] ==>(K +# M = K +# N) <-> (M = N)"
by (auto simp add: multiset_equality)

lemma nat_add_eq_1_cases: "[| m \<in> nat; n \<in> nat |] ==> (m #+ n = 1) <-> (m=1 & n=0) | (m=0 & n=1)"
by (induct_tac n) auto

lemma munion_is_single:
     "[|multiset(M); multiset(N)|] 
      ==> (M +# N = {#a#}) <->  (M={#a#} & N=0) | (M = 0 & N = {#a#})"
apply (simp (no_asm_simp) add: multiset_equality)
apply safe
apply simp_all
apply (case_tac "aa=a")
apply (drule_tac [2] x = aa in spec)
apply (drule_tac x = a in spec)
apply (simp add: nat_add_eq_1_cases, simp)
apply (case_tac "aaa=aa", simp)
apply (drule_tac x = aa in spec)
apply (simp add: nat_add_eq_1_cases)
apply (case_tac "aaa=a")
apply (drule_tac [4] x = aa in spec)
apply (drule_tac [3] x = a in spec)
apply (drule_tac [2] x = aaa in spec)
apply (drule_tac x = aa in spec)
apply (simp_all add: nat_add_eq_1_cases)
done

lemma msingle_is_union: "[| multiset(M); multiset(N) |]
  ==> ({#a#} = M +# N) <-> ({#a#} = M  & N=0 | M = 0 & {#a#} = N)"
apply (subgoal_tac " ({#a#} = M +# N) <-> (M +# N = {#a#}) ")
apply (simp (no_asm_simp) add: munion_is_single)
apply blast
apply (blast dest: sym)
done

(** Towards induction over multisets **)

lemma setsum_decr:
"Finite(A)
  ==>  (\<forall>M. multiset(M) -->
  (\<forall>a \<in> mset_of(M). setsum(%z. $# mcount(M(a:=M`a #- 1), z), A) =
  (if a \<in> A then setsum(%z. $# mcount(M, z), A) $- #1
           else setsum(%z. $# mcount(M, z), A))))"
apply (unfold multiset_def)
apply (erule Finite_induct)
apply (auto simp add: multiset_fun_iff)
apply (unfold mset_of_def mcount_def)
apply (case_tac "x \<in> A", auto)
apply (subgoal_tac "$# M ` x $+ #-1 = $# M ` x $- $# 1")
apply (erule ssubst)
apply (rule int_of_diff, auto)
done

lemma setsum_decr2:
     "Finite(A)
      ==> \<forall>M. multiset(M) --> (\<forall>a \<in> mset_of(M).
           setsum(%x. $# mcount(funrestrict(M, mset_of(M)-{a}), x), A) =
           (if a \<in> A then setsum(%x. $# mcount(M, x), A) $- $# M`a
            else setsum(%x. $# mcount(M, x), A)))"
apply (simp add: multiset_def)
apply (erule Finite_induct)
apply (auto simp add: multiset_fun_iff mcount_def mset_of_def)
done

lemma setsum_decr3: "[| Finite(A); multiset(M); a \<in> mset_of(M) |]
      ==> setsum(%x. $# mcount(funrestrict(M, mset_of(M)-{a}), x), A - {a}) =
          (if a \<in> A then setsum(%x. $# mcount(M, x), A) $- $# M`a
           else setsum(%x. $# mcount(M, x), A))"
apply (subgoal_tac "setsum (%x. $# mcount (funrestrict (M, mset_of (M) -{a}),x),A-{a}) = setsum (%x. $# mcount (funrestrict (M, mset_of (M) -{a}),x),A) ")
apply (rule_tac [2] setsum_Diff [symmetric])
apply (rule sym, rule ssubst, blast)
apply (rule sym, drule setsum_decr2, auto)
apply (simp add: mcount_def mset_of_def)
done

lemma nat_le_1_cases: "n \<in> nat ==> n le 1 <-> (n=0 | n=1)"
by (auto elim: natE)

lemma succ_pred_eq_self: "[| 0<n; n \<in> nat |] ==> succ(n #- 1) = n"
apply (subgoal_tac "1 le n")
apply (drule add_diff_inverse2, auto)
done

text{*Specialized for use in the proof below.*}
lemma multiset_funrestict:
     "\<lbrakk>\<forall>a\<in>A. M ` a \<in> nat \<and> 0 < M ` a; Finite(A)\<rbrakk>
      \<Longrightarrow> multiset(funrestrict(M, A - {a}))"
apply (simp add: multiset_def multiset_fun_iff)
apply (rule_tac x="A-{a}" in exI)
apply (auto intro: Finite_Diff funrestrict_type)
done

lemma multiset_induct_aux:
  assumes prem1: "!!M a. [| multiset(M); a\<notin>mset_of(M); P(M) |] ==> P(cons(<a, 1>, M))"
      and prem2: "!!M b. [| multiset(M); b \<in> mset_of(M); P(M) |] ==> P(M(b:= M`b #+ 1))"
  shows
  "[| n \<in> nat; P(0) |]
     ==> (\<forall>M. multiset(M)-->
  (setsum(%x. $# mcount(M, x), {x \<in> mset_of(M). 0 < M`x}) = $# n) --> P(M))"
apply (erule nat_induct, clarify)
apply (frule msize_eq_0_iff)
apply (auto simp add: mset_of_def multiset_def multiset_fun_iff msize_def)
apply (subgoal_tac "setsum (%x. $# mcount (M, x), A) =$# succ (x) ")
apply (drule setsum_succD, auto)
apply (case_tac "1 <M`a")
apply (drule_tac [2] not_lt_imp_le)
apply (simp_all add: nat_le_1_cases)
apply (subgoal_tac "M= (M (a:=M`a #- 1)) (a:= (M (a:=M`a #- 1))`a #+ 1) ")
apply (rule_tac [2] A = A and B = "%x. nat" and D = "%x. nat" in fun_extension)
apply (rule_tac [3] update_type)+
apply (simp_all (no_asm_simp))
 apply (rule_tac [2] impI)
 apply (rule_tac [2] succ_pred_eq_self [symmetric])
apply (simp_all (no_asm_simp))
apply (rule subst, rule sym, blast, rule prem2)
apply (simp (no_asm) add: multiset_def multiset_fun_iff)
apply (rule_tac x = A in exI)
apply (force intro: update_type)
apply (simp (no_asm_simp) add: mset_of_def mcount_def)
apply (drule_tac x = "M (a := M ` a #- 1) " in spec)
apply (drule mp, drule_tac [2] mp, simp_all)
apply (rule_tac x = A in exI)
apply (auto intro: update_type)
apply (subgoal_tac "Finite ({x \<in> cons (a, A) . x\<noteq>a-->0<M`x}) ")
prefer 2 apply (blast intro: Collect_subset [THEN subset_Finite] Finite_cons)
apply (drule_tac A = "{x \<in> cons (a, A) . x\<noteq>a-->0<M`x}" in setsum_decr)
apply (drule_tac x = M in spec)
apply (subgoal_tac "multiset (M) ")
 prefer 2
 apply (simp add: multiset_def multiset_fun_iff)
 apply (rule_tac x = A in exI, force)
apply (simp_all add: mset_of_def)
apply (drule_tac psi = "\<forall>x \<in> A. ?u (x) " in asm_rl)
apply (drule_tac x = a in bspec)
apply (simp (no_asm_simp))
apply (subgoal_tac "cons (a, A) = A")
prefer 2 apply blast
apply simp
apply (subgoal_tac "M=cons (<a, M`a>, funrestrict (M, A-{a}))")
 prefer 2
 apply (rule fun_cons_funrestrict_eq)
 apply (subgoal_tac "cons (a, A-{a}) = A")
  apply force
  apply force
apply (rule_tac a = "cons (<a, 1>, funrestrict (M, A - {a}))" in ssubst)
apply simp
apply (frule multiset_funrestict, assumption)
apply (rule prem1, assumption)
apply (simp add: mset_of_def)
apply (drule_tac x = "funrestrict (M, A-{a}) " in spec)
apply (drule mp)
apply (rule_tac x = "A-{a}" in exI)
apply (auto intro: Finite_Diff funrestrict_type simp add: funrestrict)
apply (frule_tac A = A and M = M and a = a in setsum_decr3)
apply (simp (no_asm_simp) add: multiset_def multiset_fun_iff)
apply blast
apply (simp (no_asm_simp) add: mset_of_def)
apply (drule_tac b = "if ?u then ?v else ?w" in sym, simp_all)
apply (subgoal_tac "{x \<in> A - {a} . 0 < funrestrict (M, A - {x}) ` x} = A - {a}")
apply (auto intro!: setsum_cong simp add: zdiff_eq_iff zadd_commute multiset_def multiset_fun_iff mset_of_def)
done

lemma multiset_induct2:
  "[| multiset(M); P(0);
    (!!M a. [| multiset(M); a\<notin>mset_of(M); P(M) |] ==> P(cons(<a, 1>, M)));
    (!!M b. [| multiset(M); b \<in> mset_of(M);  P(M) |] ==> P(M(b:= M`b #+ 1))) |]
     ==> P(M)"
apply (subgoal_tac "\<exists>n \<in> nat. setsum (\<lambda>x. $# mcount (M, x), {x \<in> mset_of (M) . 0 < M ` x}) = $# n")
apply (rule_tac [2] not_zneg_int_of)
apply (simp_all (no_asm_simp) add: znegative_iff_zless_0 not_zless_iff_zle)
apply (rule_tac [2] g_zpos_imp_setsum_zpos)
prefer 2 apply (blast intro:  multiset_set_of_Finite Collect_subset [THEN subset_Finite])
 prefer 2 apply (simp add: multiset_def multiset_fun_iff, clarify)
apply (rule multiset_induct_aux [rule_format], auto)
done

lemma munion_single_case1:
     "[| multiset(M); a \<notin>mset_of(M) |] ==> M +# {#a#} = cons(<a, 1>, M)"
apply (simp add: multiset_def msingle_def)
apply (auto simp add: munion_def)
apply (unfold mset_of_def, simp)
apply (rule fun_extension, rule lam_type, simp_all)
apply (auto simp add: multiset_fun_iff fun_extend_apply)
apply (drule_tac c = a and b = 1 in fun_extend3)
apply (auto simp add: cons_eq Un_commute [of _ "{a}"])
done

lemma munion_single_case2:
     "[| multiset(M); a \<in> mset_of(M) |] ==> M +# {#a#} = M(a:=M`a #+ 1)"
apply (simp add: multiset_def)
apply (auto simp add: munion_def multiset_fun_iff msingle_def)
apply (unfold mset_of_def, simp)
apply (subgoal_tac "A Un {a} = A")
apply (rule fun_extension)
apply (auto dest: domain_type intro: lam_type update_type)
done

(* Induction principle for multisets *)

lemma multiset_induct:
  assumes M: "multiset(M)"
      and P0: "P(0)"
      and step: "!!M a. [| multiset(M); P(M) |] ==> P(M +# {#a#})"
  shows "P(M)"
apply (rule multiset_induct2 [OF M])
apply (simp_all add: P0)
apply (frule_tac [2] a = b in munion_single_case2 [symmetric])
apply (frule_tac a = a in munion_single_case1 [symmetric])
apply (auto intro: step)
done

(** MCollect **)

lemma MCollect_multiset [simp]:
     "multiset(M) ==> multiset({# x \<in> M. P(x)#})"
apply (simp add: MCollect_def multiset_def mset_of_def, clarify)
apply (rule_tac x = "{x \<in> A. P (x) }" in exI)
apply (auto dest: CollectD1 [THEN [2] apply_type]
            intro: Collect_subset [THEN subset_Finite] funrestrict_type)
done

lemma mset_of_MCollect [simp]:
     "multiset(M) ==> mset_of({# x \<in> M. P(x) #}) \<subseteq> mset_of(M)"
by (auto simp add: mset_of_def MCollect_def multiset_def funrestrict_def)

lemma MCollect_mem_iff [iff]:
     "x \<in> mset_of({#x \<in> M. P(x)#}) <->  x \<in> mset_of(M) & P(x)"
by (simp add: MCollect_def mset_of_def)

lemma mcount_MCollect [simp]:
     "mcount({# x \<in> M. P(x) #}, a) = (if P(a) then mcount(M,a) else 0)"
by (simp add: mcount_def MCollect_def mset_of_def)

lemma multiset_partition: "multiset(M) ==> M = {# x \<in> M. P(x) #} +# {# x \<in> M. ~ P(x) #}"
by (simp add: multiset_equality)

lemma natify_elem_is_self [simp]:
     "[| multiset(M); a \<in> mset_of(M) |] ==> natify(M`a) = M`a"
by (auto simp add: multiset_def mset_of_def multiset_fun_iff)

(* and more algebraic laws on multisets *)

lemma munion_eq_conv_diff: "[| multiset(M); multiset(N) |]
  ==>  (M +# {#a#} = N +# {#b#}) <->  (M = N & a = b |
       M = N -# {#a#} +# {#b#} & N = M -# {#b#} +# {#a#})"
apply (simp del: mcount_single add: multiset_equality)
apply (rule iffI, erule_tac [2] disjE, erule_tac [3] conjE)
apply (case_tac "a=b", auto)
apply (drule_tac x = a in spec)
apply (drule_tac [2] x = b in spec)
apply (drule_tac [3] x = aa in spec)
apply (drule_tac [4] x = a in spec, auto)
apply (subgoal_tac [!] "mcount (N,a) :nat")
apply (erule_tac [3] natE, erule natE, auto)
done

lemma melem_diff_single:
"multiset(M) ==>
  k \<in> mset_of(M -# {#a#}) <-> (k=a & 1 < mcount(M,a)) | (k\<noteq> a & k \<in> mset_of(M))"
apply (simp add: multiset_def)
apply (simp add: normalize_def mset_of_def msingle_def mdiff_def mcount_def)
apply (auto dest: domain_type intro: zero_less_diff [THEN iffD1]
            simp add: multiset_fun_iff apply_iff)
apply (force intro!: lam_type)
apply (force intro!: lam_type)
apply (force intro!: lam_type)
done

lemma munion_eq_conv_exist:
"[| M \<in> Mult(A); N \<in> Mult(A) |]
  ==> (M +# {#a#} = N +# {#b#}) <->
      (M=N & a=b | (\<exists>K \<in> Mult(A). M= K +# {#b#} & N=K +# {#a#}))"
by (auto simp add: Mult_iff_multiset melem_diff_single munion_eq_conv_diff)


subsection{*Multiset Orderings*}

(* multiset on a domain A are finite functions from A to nat-{0} *)


(* multirel1 type *)

lemma multirel1_type: "multirel1(A, r) \<subseteq> Mult(A)*Mult(A)"
by (auto simp add: multirel1_def)

lemma multirel1_0 [simp]: "multirel1(0, r) =0"
by (auto simp add: multirel1_def)

lemma multirel1_iff:
" <N, M> \<in> multirel1(A, r) <->
  (\<exists>a. a \<in> A &
  (\<exists>M0. M0 \<in> Mult(A) & (\<exists>K. K \<in> Mult(A) &
   M=M0 +# {#a#} & N=M0 +# K & (\<forall>b \<in> mset_of(K). <b,a> \<in> r))))"
by (auto simp add: multirel1_def Mult_iff_multiset Bex_def)


text{*Monotonicity of @{term multirel1}*}

lemma multirel1_mono1: "A\<subseteq>B ==> multirel1(A, r)\<subseteq>multirel1(B, r)"
apply (auto simp add: multirel1_def)
apply (auto simp add: Un_subset_iff Mult_iff_multiset)
apply (rule_tac x = a in bexI)
apply (rule_tac x = M0 in bexI, simp)
apply (rule_tac x = K in bexI)
apply (auto simp add: Mult_iff_multiset)
done

lemma multirel1_mono2: "r\<subseteq>s ==> multirel1(A,r)\<subseteq>multirel1(A, s)"
apply (simp add: multirel1_def, auto) 
apply (rule_tac x = a in bexI)
apply (rule_tac x = M0 in bexI)
apply (simp_all add: Mult_iff_multiset)
apply (rule_tac x = K in bexI)
apply (simp_all add: Mult_iff_multiset, auto)
done

lemma multirel1_mono:
     "[| A\<subseteq>B; r\<subseteq>s |] ==> multirel1(A, r) \<subseteq> multirel1(B, s)"
apply (rule subset_trans)
apply (rule multirel1_mono1)
apply (rule_tac [2] multirel1_mono2, auto)
done

subsection{* Toward the proof of well-foundedness of multirel1 *}

lemma not_less_0 [iff]: "<M,0> \<notin> multirel1(A, r)"
by (auto simp add: multirel1_def Mult_iff_multiset)

lemma less_munion: "[| <N, M0 +# {#a#}> \<in> multirel1(A, r); M0 \<in> Mult(A) |] ==>
  (\<exists>M. <M, M0> \<in> multirel1(A, r) & N = M +# {#a#}) |
  (\<exists>K. K \<in> Mult(A) & (\<forall>b \<in> mset_of(K). <b, a> \<in> r) & N = M0 +# K)"
apply (frule multirel1_type [THEN subsetD])
apply (simp add: multirel1_iff)
apply (auto simp add: munion_eq_conv_exist)
apply (rule_tac x="Ka +# K" in exI, auto, simp add: Mult_iff_multiset)
apply (simp (no_asm_simp) add: munion_left_cancel munion_assoc)
apply (auto simp add: munion_commute)
done

lemma multirel1_base: "[| M \<in> Mult(A); a \<in> A |] ==> <M, M +# {#a#}> \<in> multirel1(A, r)"
apply (auto simp add: multirel1_iff)
apply (simp add: Mult_iff_multiset)
apply (rule_tac x = a in exI, clarify)
apply (rule_tac x = M in exI, simp)
apply (rule_tac x = 0 in exI, auto)
done

lemma acc_0: "acc(0)=0"
by (auto intro!: equalityI dest: acc.dom_subset [THEN subsetD])

lemma lemma1: "[| \<forall>b \<in> A. <b,a> \<in> r -->
    (\<forall>M \<in> acc(multirel1(A, r)). M +# {#b#}:acc(multirel1(A, r)));
    M0 \<in> acc(multirel1(A, r)); a \<in> A;
    \<forall>M. <M,M0> \<in> multirel1(A, r) --> M +# {#a#} \<in> acc(multirel1(A, r)) |]
  ==> M0 +# {#a#} \<in> acc(multirel1(A, r))"
apply (subgoal_tac "M0 \<in> Mult(A) ")
 prefer 2
 apply (erule acc.cases)
 apply (erule fieldE)
 apply (auto dest: multirel1_type [THEN subsetD])
apply (rule accI)
apply (rename_tac "N")
apply (drule less_munion, blast)
apply (auto simp add: Mult_iff_multiset)
apply (erule_tac P = "\<forall>x \<in> mset_of (K) . <x, a> \<in> r" in rev_mp)
apply (erule_tac P = "mset_of (K) \<subseteq>A" in rev_mp)
apply (erule_tac M = K in multiset_induct)
(* three subgoals *)
(* subgoal 1: the induction base case *)
apply (simp (no_asm_simp))
(* subgoal 2: the induction general case *)
apply (simp add: Ball_def Un_subset_iff, clarify)
apply (drule_tac x = aa in spec, simp)
apply (subgoal_tac "aa \<in> A")
prefer 2 apply blast
apply (drule_tac x = "M0 +# M" and P =
       "%x. x \<in> acc(multirel1(A, r)) \<longrightarrow> ?Q(x)" in spec)
apply (simp add: munion_assoc [symmetric])
(* subgoal 3: additional conditions *)
apply (auto intro!: multirel1_base [THEN fieldI2] simp add: Mult_iff_multiset)
done

lemma lemma2: "[| \<forall>b \<in> A. <b,a> \<in> r
   --> (\<forall>M \<in> acc(multirel1(A, r)). M +# {#b#} :acc(multirel1(A, r)));
        M \<in> acc(multirel1(A, r)); a \<in> A|] ==> M +# {#a#} \<in> acc(multirel1(A, r))"
apply (erule acc_induct)
apply (blast intro: lemma1)
done

lemma lemma3: "[| wf[A](r); a \<in> A |]
      ==> \<forall>M \<in> acc(multirel1(A, r)). M +# {#a#} \<in> acc(multirel1(A, r))"
apply (erule_tac a = a in wf_on_induct, blast)
apply (blast intro: lemma2)
done

lemma lemma4: "multiset(M) ==> mset_of(M)\<subseteq>A -->
   wf[A](r) --> M \<in> field(multirel1(A, r)) --> M \<in> acc(multirel1(A, r))"
apply (erule multiset_induct)
(* proving the base case *)
apply clarify
apply (rule accI, force)
apply (simp add: multirel1_def)
(* Proving the general case *)
apply clarify
apply simp
apply (subgoal_tac "mset_of (M) \<subseteq>A")
prefer 2 apply blast
apply clarify
apply (drule_tac a = a in lemma3, blast)
apply (subgoal_tac "M \<in> field (multirel1 (A,r))")
apply blast
apply (rule multirel1_base [THEN fieldI1])
apply (auto simp add: Mult_iff_multiset)
done

lemma all_accessible: "[| wf[A](r); M \<in> Mult(A); A \<noteq> 0|] ==> M \<in> acc(multirel1(A, r))"
apply (erule not_emptyE)
apply  (rule lemma4 [THEN mp, THEN mp, THEN mp])
apply (rule_tac [4] multirel1_base [THEN fieldI1])
apply  (auto simp add: Mult_iff_multiset)
done

lemma wf_on_multirel1: "wf[A](r) ==> wf[A-||>nat-{0}](multirel1(A, r))"
apply (case_tac "A=0")
apply (simp (no_asm_simp))
apply (rule wf_imp_wf_on)
apply (rule wf_on_field_imp_wf)
apply (simp (no_asm_simp) add: wf_on_0)
apply (rule_tac A = "acc (multirel1 (A,r))" in wf_on_subset_A)
apply (rule wf_on_acc)
apply (blast intro: all_accessible)
done

lemma wf_multirel1: "wf(r) ==>wf(multirel1(field(r), r))"
apply (simp (no_asm_use) add: wf_iff_wf_on_field)
apply (drule wf_on_multirel1)
apply (rule_tac A = "field (r) -||> nat - {0}" in wf_on_subset_A)
apply (simp (no_asm_simp))
apply (rule field_rel_subset)
apply (rule multirel1_type)
done

(** multirel **)

lemma multirel_type: "multirel(A, r) \<subseteq> Mult(A)*Mult(A)"
apply (simp add: multirel_def)
apply (rule trancl_type [THEN subset_trans])
apply (auto dest: multirel1_type [THEN subsetD])
done

(* Monotonicity of multirel *)
lemma multirel_mono:
     "[| A\<subseteq>B; r\<subseteq>s |] ==> multirel(A, r)\<subseteq>multirel(B,s)"
apply (simp add: multirel_def)
apply (rule trancl_mono)
apply (rule multirel1_mono, auto)
done

(* Equivalence of multirel with the usual (closure-free) def *)

lemma add_diff_eq: "k \<in> nat ==> 0 < k --> n #+ k #- 1 = n #+ (k #- 1)"
by (erule nat_induct, auto)

lemma mdiff_union_single_conv: "[|a \<in> mset_of(J); multiset(I); multiset(J) |]
   ==> I +# J -# {#a#} = I +# (J-# {#a#})"
apply (simp (no_asm_simp) add: multiset_equality)
apply (case_tac "a \<notin> mset_of (I) ")
apply (auto simp add: mcount_def mset_of_def multiset_def multiset_fun_iff)
apply (auto dest: domain_type simp add: add_diff_eq)
done

lemma diff_add_commute: "[| n le m;  m \<in> nat; n \<in> nat; k \<in> nat |] ==> m #- n #+ k = m #+ k #- n"
by (auto simp add: le_iff less_iff_succ_add)

(* One direction *)

lemma multirel_implies_one_step:
"<M,N> \<in> multirel(A, r) ==>
     trans[A](r) -->
     (\<exists>I J K.
         I \<in> Mult(A) & J \<in> Mult(A) &  K \<in> Mult(A) &
         N = I +# J & M = I +# K & J \<noteq> 0 &
        (\<forall>k \<in> mset_of(K). \<exists>j \<in> mset_of(J). <k,j> \<in> r))"
apply (simp add: multirel_def Ball_def Bex_def)
apply (erule converse_trancl_induct)
apply (simp_all add: multirel1_iff Mult_iff_multiset)
(* Two subgoals remain *)
(* Subgoal 1 *)
apply clarify
apply (rule_tac x = M0 in exI, force)
(* Subgoal 2 *)
apply clarify
apply (case_tac "a \<in> mset_of (Ka) ")
apply (rule_tac x = I in exI, simp (no_asm_simp))
apply (rule_tac x = J in exI, simp (no_asm_simp))
apply (rule_tac x = " (Ka -# {#a#}) +# K" in exI, simp (no_asm_simp))
apply (simp_all add: Un_subset_iff)
apply (simp (no_asm_simp) add: munion_assoc [symmetric])
apply (drule_tac t = "%M. M-#{#a#}" in subst_context)
apply (simp add: mdiff_union_single_conv melem_diff_single, clarify)
apply (erule disjE, simp)
apply (erule disjE, simp)
apply (drule_tac x = a and P = "%x. x :# Ka \<longrightarrow> ?Q(x)" in spec)
apply clarify
apply (rule_tac x = xa in exI)
apply (simp (no_asm_simp))
apply (blast dest: trans_onD)
(* new we know that  a\<notin>mset_of(Ka) *)
apply (subgoal_tac "a :# I")
apply (rule_tac x = "I-#{#a#}" in exI, simp (no_asm_simp))
apply (rule_tac x = "J+#{#a#}" in exI)
apply (simp (no_asm_simp) add: Un_subset_iff)
apply (rule_tac x = "Ka +# K" in exI)
apply (simp (no_asm_simp) add: Un_subset_iff)
apply (rule conjI)
apply (simp (no_asm_simp) add: multiset_equality mcount_elem [THEN succ_pred_eq_self])
apply (rule conjI)
apply (drule_tac t = "%M. M-#{#a#}" in subst_context)
apply (simp add: mdiff_union_inverse2)
apply (simp_all (no_asm_simp) add: multiset_equality)
apply (rule diff_add_commute [symmetric])
apply (auto intro: mcount_elem)
apply (subgoal_tac "a \<in> mset_of (I +# Ka) ")
apply (drule_tac [2] sym, auto)
done

lemma melem_imp_eq_diff_union [simp]: "[| a \<in> mset_of(M); multiset(M) |] ==> M -# {#a#} +# {#a#} = M"
by (simp add: multiset_equality mcount_elem [THEN succ_pred_eq_self])

lemma msize_eq_succ_imp_eq_union:
     "[| msize(M)=$# succ(n); M \<in> Mult(A); n \<in> nat |]
      ==> \<exists>a N. M = N +# {#a#} & N \<in> Mult(A) & a \<in> A"
apply (drule msize_eq_succ_imp_elem, auto)
apply (rule_tac x = a in exI)
apply (rule_tac x = "M -# {#a#}" in exI)
apply (frule Mult_into_multiset)
apply (simp (no_asm_simp))
apply (auto simp add: Mult_iff_multiset)
done

(* The second direction *)

lemma one_step_implies_multirel_lemma [rule_format (no_asm)]:
"n \<in> nat ==>
   (\<forall>I J K.
    I \<in> Mult(A) & J \<in> Mult(A) & K \<in> Mult(A) &
   (msize(J) = $# n & J \<noteq>0 &  (\<forall>k \<in> mset_of(K).  \<exists>j \<in> mset_of(J). <k, j> \<in> r))
    --> <I +# K, I +# J> \<in> multirel(A, r))"
apply (simp add: Mult_iff_multiset)
apply (erule nat_induct, clarify)
apply (drule_tac M = J in msize_eq_0_iff, auto)
(* one subgoal remains *)
apply (subgoal_tac "msize (J) =$# succ (x) ")
 prefer 2 apply simp
apply (frule_tac A = A in msize_eq_succ_imp_eq_union)
apply (simp_all add: Mult_iff_multiset, clarify)
apply (rename_tac "J'", simp)
apply (case_tac "J' = 0")
apply (simp add: multirel_def)
apply (rule r_into_trancl, clarify)
apply (simp add: multirel1_iff Mult_iff_multiset, force)
(*Now we know J' \<noteq>  0*)
apply (drule sym, rotate_tac -1, simp)
apply (erule_tac V = "$# x = msize (J') " in thin_rl)
apply (frule_tac M = K and P = "%x. <x,a> \<in> r" in multiset_partition)
apply (erule_tac P = "\<forall>k \<in> mset_of (K) . ?P (k) " in rev_mp)
apply (erule ssubst)
apply (simp add: Ball_def, auto)
apply (subgoal_tac "< (I +# {# x \<in> K. <x, a> \<in> r#}) +# {# x \<in> K. <x, a> \<notin> r#}, (I +# {# x \<in> K. <x, a> \<in> r#}) +# J'> \<in> multirel(A, r) ")
 prefer 2
 apply (drule_tac x = "I +# {# x \<in> K. <x, a> \<in> r#}" in spec)
 apply (rotate_tac -1)
 apply (drule_tac x = "J'" in spec)
 apply (rotate_tac -1)
 apply (drule_tac x = "{# x \<in> K. <x, a> \<notin> r#}" in spec, simp) apply blast
apply (simp add: munion_assoc [symmetric] multirel_def)
apply (rule_tac b = "I +# {# x \<in> K. <x, a> \<in> r#} +# J'" in trancl_trans, blast)
apply (rule r_into_trancl)
apply (simp add: multirel1_iff Mult_iff_multiset)
apply (rule_tac x = a in exI)
apply (simp (no_asm_simp))
apply (rule_tac x = "I +# J'" in exI)
apply (auto simp add: munion_ac Un_subset_iff)
done

lemma one_step_implies_multirel:
     "[| J \<noteq> 0;  \<forall>k \<in> mset_of(K). \<exists>j \<in> mset_of(J). <k,j> \<in> r;
         I \<in> Mult(A); J \<in> Mult(A); K \<in> Mult(A) |]
      ==> <I+#K, I+#J> \<in> multirel(A, r)"
apply (subgoal_tac "multiset (J) ")
 prefer 2 apply (simp add: Mult_iff_multiset)
apply (frule_tac M = J in msize_int_of_nat)
apply (auto intro: one_step_implies_multirel_lemma)
done

(** Proving that multisets are partially ordered **)

(*irreflexivity*)

lemma multirel_irrefl_lemma:
     "Finite(A) ==> part_ord(A, r) --> (\<forall>x \<in> A. \<exists>y \<in> A. <x,y> \<in> r) -->A=0"
apply (erule Finite_induct)
apply (auto dest: subset_consI [THEN [2] part_ord_subset])
apply (auto simp add: part_ord_def irrefl_def)
apply (drule_tac x = xa in bspec)
apply (drule_tac [2] a = xa and b = x in trans_onD, auto)
done

lemma irrefl_on_multirel:
     "part_ord(A, r) ==> irrefl(Mult(A), multirel(A, r))"
apply (simp add: irrefl_def)
apply (subgoal_tac "trans[A](r) ")
 prefer 2 apply (simp add: part_ord_def, clarify)
apply (drule multirel_implies_one_step, clarify)
apply (simp add: Mult_iff_multiset, clarify)
apply (subgoal_tac "Finite (mset_of (K))")
apply (frule_tac r = r in multirel_irrefl_lemma)
apply (frule_tac B = "mset_of (K) " in part_ord_subset)
apply simp_all
apply (auto simp add: multiset_def mset_of_def)
done

lemma trans_on_multirel: "trans[Mult(A)](multirel(A, r))"
apply (simp add: multirel_def trans_on_def)
apply (blast intro: trancl_trans)
done

lemma multirel_trans:
 "[| <M, N> \<in> multirel(A, r); <N, K> \<in> multirel(A, r) |] ==>  <M, K> \<in> multirel(A,r)"
apply (simp add: multirel_def)
apply (blast intro: trancl_trans)
done

lemma trans_multirel: "trans(multirel(A,r))"
apply (simp add: multirel_def)
apply (rule trans_trancl)
done

lemma part_ord_multirel: "part_ord(A,r) ==> part_ord(Mult(A), multirel(A, r))"
apply (simp (no_asm) add: part_ord_def)
apply (blast intro: irrefl_on_multirel trans_on_multirel)
done

(** Monotonicity of multiset union **)

lemma munion_multirel1_mono:
"[|<M,N> \<in> multirel1(A, r); K \<in> Mult(A) |] ==> <K +# M, K +# N> \<in> multirel1(A, r)"
apply (frule multirel1_type [THEN subsetD])
apply (auto simp add: multirel1_iff Mult_iff_multiset)
apply (rule_tac x = a in exI)
apply (simp (no_asm_simp))
apply (rule_tac x = "K+#M0" in exI)
apply (simp (no_asm_simp) add: Un_subset_iff)
apply (rule_tac x = Ka in exI)
apply (simp (no_asm_simp) add: munion_assoc)
done

lemma munion_multirel_mono2:
 "[| <M, N> \<in> multirel(A, r); K \<in> Mult(A) |]==><K +# M, K +# N> \<in> multirel(A, r)"
apply (frule multirel_type [THEN subsetD])
apply (simp (no_asm_use) add: multirel_def)
apply clarify
apply (drule_tac psi = "<M,N> \<in> multirel1 (A, r) ^+" in asm_rl)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule trancl_induct, clarify)
apply (blast intro: munion_multirel1_mono r_into_trancl, clarify)
apply (subgoal_tac "y \<in> Mult(A) ")
 prefer 2
 apply (blast dest: multirel_type [unfolded multirel_def, THEN subsetD])
apply (subgoal_tac "<K +# y, K +# z> \<in> multirel1 (A, r) ")
prefer 2 apply (blast intro: munion_multirel1_mono)
apply (blast intro: r_into_trancl trancl_trans)
done

lemma munion_multirel_mono1:
     "[|<M, N> \<in> multirel(A, r); K \<in> Mult(A)|] ==> <M +# K, N +# K> \<in> multirel(A, r)"
apply (frule multirel_type [THEN subsetD])
apply (rule_tac P = "%x. <x,?u> \<in> multirel(A, r) " in munion_commute [THEN subst])
apply (subst munion_commute [of N])
apply (rule munion_multirel_mono2)
apply (auto simp add: Mult_iff_multiset)
done

lemma munion_multirel_mono:
     "[|<M,K> \<in> multirel(A, r); <N,L> \<in> multirel(A, r)|]
      ==> <M +# N, K +# L> \<in> multirel(A, r)"
apply (subgoal_tac "M \<in> Mult(A) & N \<in> Mult(A) & K \<in> Mult(A) & L \<in> Mult(A) ")
prefer 2 apply (blast dest: multirel_type [THEN subsetD])
apply (blast intro: munion_multirel_mono1 multirel_trans munion_multirel_mono2)
done


subsection{*Ordinal Multisets*}

(* A \<subseteq> B ==>  field(Memrel(A)) \<subseteq> field(Memrel(B)) *)
lemmas field_Memrel_mono = Memrel_mono [THEN field_mono]

(*
[| Aa \<subseteq> Ba; A \<subseteq> B |] ==>
multirel(field(Memrel(Aa)), Memrel(A))\<subseteq> multirel(field(Memrel(Ba)), Memrel(B))
*)

lemmas multirel_Memrel_mono = multirel_mono [OF field_Memrel_mono Memrel_mono]

lemma omultiset_is_multiset [simp]: "omultiset(M) ==> multiset(M)"
apply (simp add: omultiset_def)
apply (auto simp add: Mult_iff_multiset)
done

lemma munion_omultiset [simp]: "[| omultiset(M); omultiset(N) |] ==> omultiset(M +# N)"
apply (simp add: omultiset_def, clarify)
apply (rule_tac x = "i Un ia" in exI)
apply (simp add: Mult_iff_multiset Ord_Un Un_subset_iff)
apply (blast intro: field_Memrel_mono)
done

lemma mdiff_omultiset [simp]: "omultiset(M) ==> omultiset(M -# N)"
apply (simp add: omultiset_def, clarify)
apply (simp add: Mult_iff_multiset)
apply (rule_tac x = i in exI)
apply (simp (no_asm_simp))
done

(** Proving that Memrel is a partial order **)

lemma irrefl_Memrel: "Ord(i) ==> irrefl(field(Memrel(i)), Memrel(i))"
apply (rule irreflI, clarify)
apply (subgoal_tac "Ord (x) ")
prefer 2 apply (blast intro: Ord_in_Ord)
apply (drule_tac i = x in ltI [THEN lt_irrefl], auto)
done

lemma trans_iff_trans_on: "trans(r) <-> trans[field(r)](r)"
by (simp add: trans_on_def trans_def, auto)

lemma part_ord_Memrel: "Ord(i) ==>part_ord(field(Memrel(i)), Memrel(i))"
apply (simp add: part_ord_def)
apply (simp (no_asm) add: trans_iff_trans_on [THEN iff_sym])
apply (blast intro: trans_Memrel irrefl_Memrel)
done

(*
  Ord(i) ==>
  part_ord(field(Memrel(i))-||>nat-{0}, multirel(field(Memrel(i)), Memrel(i)))
*)

lemmas part_ord_mless = part_ord_Memrel [THEN part_ord_multirel]

(*irreflexivity*)

lemma mless_not_refl: "~(M <# M)"
apply (simp add: mless_def, clarify)
apply (frule multirel_type [THEN subsetD])
apply (drule part_ord_mless)
apply (simp add: part_ord_def irrefl_def)
done

(* N<N ==> R *)
lemmas mless_irrefl = mless_not_refl [THEN notE, elim!]

(*transitivity*)
lemma mless_trans: "[| K <# M; M <# N |] ==> K <# N"
apply (simp add: mless_def, clarify)
apply (rule_tac x = "i Un ia" in exI)
apply (blast dest: multirel_Memrel_mono [OF Un_upper1 Un_upper1, THEN subsetD]
                   multirel_Memrel_mono [OF Un_upper2 Un_upper2, THEN subsetD]
        intro: multirel_trans Ord_Un)
done

(*asymmetry*)
lemma mless_not_sym: "M <# N ==> ~ N <# M"
apply clarify
apply (rule mless_not_refl [THEN notE])
apply (erule mless_trans, assumption)
done

lemma mless_asym: "[| M <# N; ~P ==> N <# M |] ==> P"
by (blast dest: mless_not_sym)

lemma mle_refl [simp]: "omultiset(M) ==> M <#= M"
by (simp add: mle_def)

(*anti-symmetry*)
lemma mle_antisym:
     "[| M <#= N;  N <#= M |] ==> M = N"
apply (simp add: mle_def)
apply (blast dest: mless_not_sym)
done

(*transitivity*)
lemma mle_trans: "[| K <#= M; M <#= N |] ==> K <#= N"
apply (simp add: mle_def)
apply (blast intro: mless_trans)
done

lemma mless_le_iff: "M <# N <-> (M <#= N & M \<noteq> N)"
by (simp add: mle_def, auto)

(** Monotonicity of mless **)

lemma munion_less_mono2: "[| M <# N; omultiset(K) |] ==> K +# M <# K +# N"
apply (simp add: mless_def omultiset_def, clarify)
apply (rule_tac x = "i Un ia" in exI)
apply (simp add: Mult_iff_multiset Ord_Un Un_subset_iff)
apply (rule munion_multirel_mono2)
 apply (blast intro: multirel_Memrel_mono [THEN subsetD])
apply (simp add: Mult_iff_multiset)
apply (blast intro: field_Memrel_mono [THEN subsetD])
done

lemma munion_less_mono1: "[| M <# N; omultiset(K) |] ==> M +# K <# N +# K"
by (force dest: munion_less_mono2 simp add: munion_commute)

lemma mless_imp_omultiset: "M <# N ==> omultiset(M) & omultiset(N)"
by (auto simp add: mless_def omultiset_def dest: multirel_type [THEN subsetD])

lemma munion_less_mono: "[| M <# K; N <# L |] ==> M +# N <# K +# L"
apply (frule_tac M = M in mless_imp_omultiset)
apply (frule_tac M = N in mless_imp_omultiset)
apply (blast intro: munion_less_mono1 munion_less_mono2 mless_trans)
done

(* <#= *)

lemma mle_imp_omultiset: "M <#= N ==> omultiset(M) & omultiset(N)"
by (auto simp add: mle_def mless_imp_omultiset)

lemma mle_mono: "[| M <#= K;  N <#= L |] ==> M +# N <#= K +# L"
apply (frule_tac M = M in mle_imp_omultiset)
apply (frule_tac M = N in mle_imp_omultiset)
apply (auto simp add: mle_def intro: munion_less_mono1 munion_less_mono2 munion_less_mono)
done

lemma omultiset_0 [iff]: "omultiset(0)"
by (auto simp add: omultiset_def Mult_iff_multiset)

lemma empty_leI [simp]: "omultiset(M) ==> 0 <#= M"
apply (simp add: mle_def mless_def)
apply (subgoal_tac "\<exists>i. Ord (i) & M \<in> Mult(field(Memrel(i))) ")
 prefer 2 apply (simp add: omultiset_def)
apply (case_tac "M=0", simp_all, clarify)
apply (subgoal_tac "<0 +# 0, 0 +# M> \<in> multirel(field (Memrel(i)), Memrel(i))")
apply (rule_tac [2] one_step_implies_multirel)
apply (auto simp add: Mult_iff_multiset)
done

lemma munion_upper1: "[| omultiset(M); omultiset(N) |] ==> M <#= M +# N"
apply (subgoal_tac "M +# 0 <#= M +# N")
apply (rule_tac [2] mle_mono, auto)
done

end
