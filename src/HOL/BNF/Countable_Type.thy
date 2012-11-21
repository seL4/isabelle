(*  Title:      HOL/BNF/Countable_Type.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

(At most) countable sets.
*)

header {* (At Most) Countable Sets *}

theory Countable_Type
imports "../Cardinals/Cardinals" "~~/src/HOL/Library/Countable_Set"
begin

subsection{* Cardinal stuff *}

lemma countable_card_of_nat: "countable A \<longleftrightarrow> |A| \<le>o |UNIV::nat set|"
  unfolding countable_def card_of_ordLeq[symmetric] by auto

lemma countable_card_le_natLeq: "countable A \<longleftrightarrow> |A| \<le>o natLeq"
  unfolding countable_card_of_nat using card_of_nat ordLeq_ordIso_trans ordIso_symmetric by blast

lemma countable_or_card_of:
assumes "countable A"
shows "(finite A \<and> |A| <o |UNIV::nat set| ) \<or>
       (infinite A  \<and> |A| =o |UNIV::nat set| )"
apply (cases "finite A")
  apply(metis finite_iff_cardOf_nat)
  by (metis assms countable_card_of_nat infinite_iff_card_of_nat ordIso_iff_ordLeq)

lemma countable_cases_card_of[elim]:
  assumes "countable A"
  obtains (Fin) "finite A" "|A| <o |UNIV::nat set|"
        | (Inf) "infinite A" "|A| =o |UNIV::nat set|"
  using assms countable_or_card_of by blast

lemma countable_or:
  "countable A \<Longrightarrow> (\<exists> f::'a\<Rightarrow>nat. finite A \<and> inj_on f A) \<or> (\<exists> f::'a\<Rightarrow>nat. infinite A \<and> bij_betw f A UNIV)"
  by (auto elim: countable_enum_cases)

lemma countable_cases[elim]:
  assumes "countable A"
  obtains (Fin) f :: "'a\<Rightarrow>nat" where "finite A" "inj_on f A"
        | (Inf) f :: "'a\<Rightarrow>nat" where "infinite A" "bij_betw f A UNIV"
  using assms countable_or by metis

lemma countable_ordLeq:
assumes "|A| \<le>o |B|" and "countable B"
shows "countable A"
using assms unfolding countable_card_of_nat by(rule ordLeq_transitive)

lemma countable_ordLess:
assumes AB: "|A| <o |B|" and B: "countable B"
shows "countable A"
using countable_ordLeq[OF ordLess_imp_ordLeq[OF AB] B] .

lemma ordLeq_countable:
assumes "|A| \<le>o |B|" and "countable B"
shows "countable A"
using assms unfolding countable_card_of_nat by(rule ordLeq_transitive)

lemma ordLess_countable:
assumes A: "|A| <o |B|" and B: "countable B"
shows "countable A"
by (rule ordLeq_countable[OF ordLess_imp_ordLeq[OF A] B])

subsection{*  The type of countable sets *}

typedef 'a cset = "{A :: 'a set. countable A}"
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
