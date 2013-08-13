(*  Title:      HOL/BNF/Countable_Type.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

(At most) countable sets.
*)

header {* (At Most) Countable Sets *}

theory Countable_Type
imports
  "~~/src/HOL/Cardinals/Cardinals"
  "~~/src/HOL/Library/Countable_Set"
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
proof (cases "finite A")
  case True thus ?thesis by (metis finite_iff_cardOf_nat)
next
  case False with assms show ?thesis
    by (metis countable_card_of_nat infinite_iff_card_of_nat ordIso_iff_ordLeq)
qed

lemma countable_cases_card_of[elim]:
  assumes "countable A"
  obtains (Fin) "finite A" "|A| <o |UNIV::nat set|"
        | (Inf) "infinite A" "|A| =o |UNIV::nat set|"
  using assms countable_or_card_of by blast

lemma countable_or:
  "countable A \<Longrightarrow> (\<exists> f::'a\<Rightarrow>nat. finite A \<and> inj_on f A) \<or> (\<exists> f::'a\<Rightarrow>nat. infinite A \<and> bij_betw f A UNIV)"
  by (elim countable_enum_cases) fastforce+

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

subsection{*  The type of countable sets *}

typedef 'a cset = "{A :: 'a set. countable A}" morphisms rcset acset
  by (rule exI[of _ "{}"]) simp

setup_lifting type_definition_cset

declare
  rcset_inverse[simp]
  acset_inverse[Transfer.transferred, unfolded mem_Collect_eq, simp]
  acset_inject[Transfer.transferred, unfolded mem_Collect_eq, simp]
  rcset[Transfer.transferred, unfolded mem_Collect_eq, simp]

lift_definition cin :: "'a \<Rightarrow> 'a cset \<Rightarrow> bool" is "op \<in>" parametric member_transfer
  ..
lift_definition cempty :: "'a cset" is "{}" parametric empty_transfer
  by (rule countable_empty)
lift_definition cinsert :: "'a \<Rightarrow> 'a cset \<Rightarrow> 'a cset" is insert parametric Lifting_Set.insert_transfer
  by (rule countable_insert)
lift_definition csingle :: "'a \<Rightarrow> 'a cset" is "\<lambda>x. {x}"
  by (rule countable_insert[OF countable_empty])
lift_definition cUn :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> 'a cset" is "op \<union>" parametric union_transfer
  by (rule countable_Un)
lift_definition cInt :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> 'a cset" is "op \<inter>" parametric inter_transfer
  by (rule countable_Int1)
lift_definition cDiff :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> 'a cset" is "op -" parametric Diff_transfer
  by (rule countable_Diff)
lift_definition cimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a cset \<Rightarrow> 'b cset" is "op `" parametric image_transfer
  by (rule countable_image)

end
