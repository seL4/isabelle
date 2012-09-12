(*  Title:      HOL/Codatatype/Countable_Set.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

(At most) countable sets.
*)

header {* (At Most) Countable Sets *}

theory Countable_Set
imports "../Cardinals/Cardinal_Arithmetic" "~~/src/HOL/Library/Countable"
begin


subsection{* Basics  *}

definition "countable A \<equiv> |A| \<le>o natLeq"

lemma countable_card_of_nat:
"countable A \<longleftrightarrow> |A| \<le>o |UNIV::nat set|"
unfolding countable_def using card_of_nat
using ordLeq_ordIso_trans ordIso_symmetric by blast

lemma countable_ex_to_nat:
fixes A :: "'a set"
shows "countable A \<longleftrightarrow> (\<exists> f::'a\<Rightarrow>nat. inj_on f A)"
unfolding countable_card_of_nat card_of_ordLeq[symmetric] by auto

lemma countable_or_card_of:
assumes "countable A"
shows "(finite A \<and> |A| <o |UNIV::nat set| ) \<or>
       (infinite A  \<and> |A| =o |UNIV::nat set| )"
apply (cases "finite A")
  apply(metis finite_iff_cardOf_nat)
  by (metis assms countable_card_of_nat infinite_iff_card_of_nat ordIso_iff_ordLeq)

lemma countable_or:
assumes "countable A"
shows "(\<exists> f::'a\<Rightarrow>nat. finite A \<and> inj_on f A) \<or>
       (\<exists> f::'a\<Rightarrow>nat. infinite A \<and> bij_betw f A UNIV)"
using countable_or_card_of[OF assms]
by (metis assms card_of_ordIso countable_ex_to_nat)

lemma countable_cases_card_of[elim, consumes 1, case_names Fin Inf]:
assumes "countable A"
and "\<lbrakk>finite A; |A| <o |UNIV::nat set|\<rbrakk> \<Longrightarrow> phi"
and "\<lbrakk>infinite A; |A| =o |UNIV::nat set|\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms countable_or_card_of by blast

lemma countable_cases[elim, consumes 1, case_names Fin Inf]:
assumes "countable A"
and "\<And> f::'a\<Rightarrow>nat. \<lbrakk>finite A; inj_on f A\<rbrakk> \<Longrightarrow> phi"
and "\<And> f::'a\<Rightarrow>nat. \<lbrakk>infinite A; bij_betw f A UNIV\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms countable_or by metis

definition toNat_pred :: "'a set \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool"
where
"toNat_pred (A::'a set) f \<equiv>
 (finite A \<and> inj_on f A) \<or> (infinite A \<and> bij_betw f A UNIV)"
definition toNat where "toNat A \<equiv> SOME f. toNat_pred A f"

lemma toNat_pred:
assumes "countable A"
shows "\<exists> f. toNat_pred A f"
using assms countable_ex_to_nat toNat_pred_def by (cases rule: countable_cases) auto

lemma toNat_pred_toNat:
assumes "countable A"
shows "toNat_pred A (toNat A)"
unfolding toNat_def apply(rule someI_ex[of "toNat_pred A"])
using toNat_pred[OF assms] .

lemma bij_betw_toNat:
assumes c: "countable A" and i: "infinite A"
shows "bij_betw (toNat A) A (UNIV::nat set)"
using toNat_pred_toNat[OF c] unfolding toNat_pred_def using i by auto

lemma inj_on_toNat:
assumes c: "countable A"
shows "inj_on (toNat A) A"
using c apply(cases rule: countable_cases)
using bij_betw_toNat[OF c] toNat_pred_toNat[OF c]
unfolding toNat_pred_def unfolding bij_betw_def by auto

lemma toNat_inj[simp]:
assumes c: "countable A" and a: "a \<in> A" and b: "b \<in> A"
shows "toNat A a = toNat A b \<longleftrightarrow> a = b"
using inj_on_toNat[OF c] using a b unfolding inj_on_def by auto

lemma image_toNat:
assumes c: "countable A" and i: "infinite A"
shows "toNat A ` A = UNIV"
using bij_betw_toNat[OF assms] unfolding bij_betw_def by simp

lemma toNat_surj:
assumes "countable A" and i: "infinite A"
shows "\<exists> a. a \<in> A \<and> toNat A a = n"
using image_toNat[OF assms]
by (metis (no_types) image_iff iso_tuple_UNIV_I)

definition
"fromNat A n \<equiv>
 if n \<in> toNat A ` A then inv_into A (toNat A) n
 else (SOME a. a \<in> A)"

lemma fromNat:
assumes "A \<noteq> {}"
shows "fromNat A n \<in> A"
unfolding fromNat_def by (metis assms equals0I inv_into_into someI_ex)

lemma toNat_fromNat[simp]:
assumes "n \<in> toNat A ` A"
shows "toNat A (fromNat A n) = n"
by (metis assms f_inv_into_f fromNat_def)

lemma infinite_toNat_fromNat[simp]:
assumes c: "countable A" and i: "infinite A"
shows "toNat A (fromNat A n) = n"
apply(rule toNat_fromNat) using toNat_surj[OF assms]
by (metis image_iff)

lemma fromNat_toNat[simp]:
assumes c: "countable A" and a: "a \<in> A"
shows "fromNat A (toNat A a) = a"
by (metis a c equals0D fromNat imageI toNat_fromNat toNat_inj)

lemma fromNat_inj:
assumes c: "countable A" and i: "infinite A"
shows "fromNat A m = fromNat A n \<longleftrightarrow> m = n" (is "?L = ?R \<longleftrightarrow> ?K")
proof-
  have "?L = ?R \<longleftrightarrow> toNat A ?L = toNat A ?R"
  unfolding toNat_inj[OF c fromNat[OF infinite_imp_nonempty[OF i]]
                           fromNat[OF infinite_imp_nonempty[OF i]]] ..
  also have "... \<longleftrightarrow> ?K" using c i by simp
  finally show ?thesis .
qed

lemma fromNat_surj:
assumes c: "countable A" and a: "a \<in> A"
shows "\<exists> n. fromNat A n = a"
apply(rule exI[of _ "toNat A a"]) using assms by simp

lemma fromNat_image_incl:
assumes "A \<noteq> {}"
shows "fromNat A ` UNIV \<subseteq> A"
using fromNat[OF assms] by auto

lemma incl_fromNat_image:
assumes "countable A"
shows "A \<subseteq> fromNat A ` UNIV"
unfolding image_def using fromNat_surj[OF assms] by auto

lemma fromNat_image[simp]:
assumes "A \<noteq> {}" and "countable A"
shows "fromNat A ` UNIV = A"
by (metis assms equalityI fromNat_image_incl incl_fromNat_image)

lemma fromNat_inject[simp]:
assumes A: "A \<noteq> {}" "countable A" and B: "B \<noteq> {}" "countable B"
shows "fromNat A = fromNat B \<longleftrightarrow> A = B"
by (metis assms fromNat_image)

lemma inj_on_fromNat:
"inj_on fromNat ({A. A \<noteq> {} \<and> countable A})"
unfolding inj_on_def by auto


subsection {* Preservation under the set theoretic operations *}

lemma contable_empty[simp,intro]:
"countable {}"
by (metis countable_ex_to_nat inj_on_empty)

lemma incl_countable:
assumes "A \<subseteq> B" and "countable B"
shows "countable A"
by (metis assms countable_ex_to_nat subset_inj_on)

lemma countable_diff:
assumes "countable A"
shows "countable (A - B)"
by (metis Diff_subset assms incl_countable)

lemma finite_countable[simp]:
assumes "finite A"
shows "countable A"
by (metis assms countable_ex_to_nat finite_imp_inj_to_nat_seg)

lemma countable_singl[simp]:
"countable {a}"
by simp

lemma countable_insert[simp]:
"countable (insert a A) \<longleftrightarrow> countable A"
proof
  assume c: "countable A"
  thus "countable (insert a A)"
  apply (cases rule: countable_cases_card_of)
    apply (metis finite_countable finite_insert)
    unfolding countable_card_of_nat
    by (metis infinite_card_of_insert ordIso_imp_ordLeq ordIso_transitive)
qed(insert incl_countable, metis incl_countable subset_insertI)

lemma contable_IntL[simp]:
assumes "countable A"
shows "countable (A \<inter> B)"
by (metis Int_lower1 assms incl_countable)

lemma contable_IntR[simp]:
assumes "countable B"
shows "countable (A \<inter> B)"
by (metis assms contable_IntL inf.commute)

lemma countable_UN[simp]:
assumes cI: "countable I" and cA: "\<And> i. i \<in> I \<Longrightarrow> countable (A i)"
shows "countable (\<Union> i \<in> I. A i)"
using assms unfolding countable_card_of_nat
apply(intro card_of_UNION_ordLeq_infinite) by auto

lemma contable_Un[simp]:
"countable (A \<union> B) \<longleftrightarrow> countable A \<and> countable B"
proof safe
  assume cA: "countable A" and cB: "countable B"
  let ?I = "{0,Suc 0}"  let ?As = "\<lambda> i. case i of 0 \<Rightarrow> A|Suc 0 \<Rightarrow> B"
  have AB: "A \<union> B = (\<Union> i \<in> ?I. ?As i)" by simp
  show "countable (A \<union> B)" unfolding AB apply(rule countable_UN)
  using cA cB by auto
qed (metis Un_upper1 incl_countable, metis Un_upper2 incl_countable)

lemma countable_INT[simp]:
assumes "i \<in> I" and "countable (A i)"
shows "countable (\<Inter> i \<in> I. A i)"
by (metis INF_insert assms contable_IntL insert_absorb)

lemma countable_class[simp]:
fixes A :: "('a::countable) set"
shows "countable A"
proof-
  have "inj_on to_nat A" by (metis inj_on_to_nat)
  thus ?thesis by (metis countable_ex_to_nat)
qed

lemma countable_image[simp]:
assumes "countable A"
shows "countable (f ` A)"
using assms unfolding countable_card_of_nat
by (metis card_of_image ordLeq_transitive)

lemma countable_ordLeq:
assumes "|A| \<le>o |B|" and "countable B"
shows "countable A"
using assms unfolding countable_card_of_nat by(rule ordLeq_transitive)

lemma countable_ordLess:
assumes AB: "|A| <o |B|" and B: "countable B"
shows "countable A"
using countable_ordLeq[OF ordLess_imp_ordLeq[OF AB] B] .

lemma countable_vimage:
assumes "B \<subseteq> range f" and "countable (f -` B)"
shows "countable B"
by (metis Int_absorb2 assms countable_image image_vimage_eq)

lemma surj_countable_vimage:
assumes s: "surj f" and c: "countable (f -` B)"
shows "countable B"
apply(rule countable_vimage[OF _ c]) using s by auto

lemma countable_Collect[simp]:
assumes "countable A"
shows "countable {a \<in> A. \<phi> a}"
by (metis Collect_conj_eq Int_absorb Int_commute Int_def assms contable_IntR)


subsection{*  The type of countable sets *}

typedef (open) 'a cset = "{A :: 'a set. countable A}"
apply(rule exI[of _ "{}"]) by simp

abbreviation rcset where "rcset \<equiv> Rep_cset"
abbreviation acset where "acset \<equiv> Abs_cset"

lemmas acset_rcset = Rep_cset_inverse
declare acset_rcset[simp]

lemma acset_surj:
"\<exists> A. countable A \<and> acset A = C"
apply(cases rule: Abs_cset_cases[of C]) by auto

lemma rcset_acset[simp]:
assumes "countable A"
shows "rcset (acset A) = A"
using Abs_cset_inverse assms by auto

lemma acset_inj[simp]:
assumes "countable A" and "countable B"
shows "acset A = acset B \<longleftrightarrow> A = B"
using assms Abs_cset_inject by auto

lemma rcset[simp]:
"countable (rcset C)"
using Rep_cset by simp

lemma rcset_inj[simp]:
"rcset C = rcset D \<longleftrightarrow> C = D"
by (metis acset_rcset)

lemma rcset_surj:
assumes "countable A"
shows "\<exists> C. rcset C = A"
apply(cases rule: Rep_cset_cases[of A])
using assms by auto

definition "cIn a C \<equiv> (a \<in> rcset C)"
definition "cEmp \<equiv> acset {}"
definition "cIns a C \<equiv> acset (insert a (rcset C))"
abbreviation cSingl where "cSingl a \<equiv> cIns a cEmp"
definition "cUn C D \<equiv> acset (rcset C \<union> rcset D)"
definition "cInt C D \<equiv> acset (rcset C \<inter> rcset D)"
definition "cDif C D \<equiv> acset (rcset C - rcset D)"
definition "cIm f C \<equiv> acset (f ` rcset C)"
definition "cVim f D \<equiv> acset (f -` rcset D)"
(* TODO eventually: nice setup for these operations, copied from the set setup *)

end
