(*  Title:      HOL/Library/Countable_Set_Type.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Type of (at most) countable sets.
*)

section {* Type of (at Most) Countable Sets *}

theory Countable_Set_Type
imports Countable_Set Cardinal_Notations
begin

abbreviation "Grp \<equiv> BNF_Def.Grp"


subsection{* Cardinal stuff *}

lemma countable_card_of_nat: "countable A \<longleftrightarrow> |A| \<le>o |UNIV::nat set|"
  unfolding countable_def card_of_ordLeq[symmetric] by auto

lemma countable_card_le_natLeq: "countable A \<longleftrightarrow> |A| \<le>o natLeq"
  unfolding countable_card_of_nat using card_of_nat ordLeq_ordIso_trans ordIso_symmetric by blast

lemma countable_or_card_of:
assumes "countable A"
shows "(finite A \<and> |A| <o |UNIV::nat set| ) \<or>
       (infinite A  \<and> |A| =o |UNIV::nat set| )"
by (metis assms countable_card_of_nat infinite_iff_card_of_nat ordIso_iff_ordLeq
      ordLeq_iff_ordLess_or_ordIso)

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

subsection {* The type of countable sets *}

typedef 'a cset = "{A :: 'a set. countable A}" morphisms rcset acset
  by (rule exI[of _ "{}"]) simp

setup_lifting type_definition_cset

declare
  rcset_inverse[simp]
  acset_inverse[Transfer.transferred, unfolded mem_Collect_eq, simp]
  acset_inject[Transfer.transferred, unfolded mem_Collect_eq, simp]
  rcset[Transfer.transferred, unfolded mem_Collect_eq, simp]

lift_definition cin :: "'a \<Rightarrow> 'a cset \<Rightarrow> bool" is "op \<in>" parametric member_transfer
  .
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

subsection {* Registration as BNF *}

lemma card_of_countable_sets_range:
fixes A :: "'a set"
shows "|{X. X \<subseteq> A \<and> countable X \<and> X \<noteq> {}}| \<le>o |{f::nat \<Rightarrow> 'a. range f \<subseteq> A}|"
apply(rule card_of_ordLeqI[of from_nat_into]) using inj_on_from_nat_into
unfolding inj_on_def by auto

lemma card_of_countable_sets_Func:
"|{X. X \<subseteq> A \<and> countable X \<and> X \<noteq> {}}| \<le>o |A| ^c natLeq"
using card_of_countable_sets_range card_of_Func_UNIV[THEN ordIso_symmetric]
unfolding cexp_def Field_natLeq Field_card_of
by (rule ordLeq_ordIso_trans)

lemma ordLeq_countable_subsets:
"|A| \<le>o |{X. X \<subseteq> A \<and> countable X}|"
apply (rule card_of_ordLeqI[of "\<lambda> a. {a}"]) unfolding inj_on_def by auto

lemma finite_countable_subset:
"finite {X. X \<subseteq> A \<and> countable X} \<longleftrightarrow> finite A"
apply default
 apply (erule contrapos_pp)
 apply (rule card_of_ordLeq_infinite)
 apply (rule ordLeq_countable_subsets)
 apply assumption
apply (rule finite_Collect_conjI)
apply (rule disjI1)
by (erule finite_Collect_subsets)

lemma rcset_to_rcset: "countable A \<Longrightarrow> rcset (the_inv rcset A) = A"
  apply (rule f_the_inv_into_f[unfolded inj_on_def image_iff])
   apply transfer' apply simp
  apply transfer' apply simp
  done

lemma Collect_Int_Times:
"{(x, y). R x y} \<inter> A \<times> B = {(x, y). R x y \<and> x \<in> A \<and> y \<in> B}"
by auto

definition rel_cset :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a cset \<Rightarrow> 'b cset \<Rightarrow> bool" where
"rel_cset R a b \<longleftrightarrow>
 (\<forall>t \<in> rcset a. \<exists>u \<in> rcset b. R t u) \<and>
 (\<forall>t \<in> rcset b. \<exists>u \<in> rcset a. R u t)"

lemma rel_cset_aux:
"(\<forall>t \<in> rcset a. \<exists>u \<in> rcset b. R t u) \<and> (\<forall>t \<in> rcset b. \<exists>u \<in> rcset a. R u t) \<longleftrightarrow>
 ((Grp {x. rcset x \<subseteq> {(a, b). R a b}} (cimage fst))\<inverse>\<inverse> OO
          Grp {x. rcset x \<subseteq> {(a, b). R a b}} (cimage snd)) a b" (is "?L = ?R")
proof
  assume ?L
  def R' \<equiv> "the_inv rcset (Collect (split R) \<inter> (rcset a \<times> rcset b))"
  (is "the_inv rcset ?L'")
  have L: "countable ?L'" by auto
  hence *: "rcset R' = ?L'" unfolding R'_def by (intro rcset_to_rcset)
  thus ?R unfolding Grp_def relcompp.simps conversep.simps
  proof (intro CollectI case_prodI exI[of _ a] exI[of _ b] exI[of _ R'] conjI refl)
    from * `?L` show "a = cimage fst R'" by transfer (auto simp: image_def Collect_Int_Times)
  next
    from * `?L` show "b = cimage snd R'" by transfer (auto simp: image_def Collect_Int_Times)
  qed simp_all
next
  assume ?R thus ?L unfolding Grp_def relcompp.simps conversep.simps
    by transfer force
qed

bnf "'a cset"
  map: cimage
  sets: rcset
  bd: natLeq
  wits: "cempty"
  rel: rel_cset
proof -
  show "cimage id = id" by transfer' simp
next
  fix f g show "cimage (g \<circ> f) = cimage g \<circ> cimage f" by transfer' fastforce
next
  fix C f g assume eq: "\<And>a. a \<in> rcset C \<Longrightarrow> f a = g a"
  thus "cimage f C = cimage g C" by transfer force
next
  fix f show "rcset \<circ> cimage f = op ` f \<circ> rcset" by transfer' fastforce
next
  show "card_order natLeq" by (rule natLeq_card_order)
next
  show "cinfinite natLeq" by (rule natLeq_cinfinite)
next
  fix C show "|rcset C| \<le>o natLeq" by transfer (unfold countable_card_le_natLeq)
next
  fix R S
  show "rel_cset R OO rel_cset S \<le> rel_cset (R OO S)"
    unfolding rel_cset_def[abs_def] by fast
next
  fix R
  show "rel_cset R =
        (Grp {x. rcset x \<subseteq> Collect (split R)} (cimage fst))\<inverse>\<inverse> OO
         Grp {x. rcset x \<subseteq> Collect (split R)} (cimage snd)"
  unfolding rel_cset_def[abs_def] rel_cset_aux by simp
qed (transfer, simp)

end
