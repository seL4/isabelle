(*  Title:      HOL/Algebra/Module
    ID:         $Id$
    Author:     Clemens Ballarin, started 15 April 2003
    Copyright:  Clemens Ballarin
*)

header {* Modules over an Abelian Group *}

theory Module = CRing:

record ('a, 'b) module = "'b ring" +
  smult :: "['a, 'b] => 'b" (infixl "\<odot>\<index>" 70)

locale module = cring R + abelian_group M +
  assumes smult_closed [simp, intro]:
      "[| a \<in> carrier R; x \<in> carrier M |] ==> a \<odot>\<^sub>2 x \<in> carrier M"
    and smult_l_distr:
      "[| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      (a \<oplus> b) \<odot>\<^sub>2 x = a \<odot>\<^sub>2 x \<oplus>\<^sub>2 b \<odot>\<^sub>2 x"
    and smult_r_distr:
      "[| a \<in> carrier R; x \<in> carrier M; y \<in> carrier M |] ==>
      a \<odot>\<^sub>2 (x \<oplus>\<^sub>2 y) = a \<odot>\<^sub>2 x \<oplus>\<^sub>2 a \<odot>\<^sub>2 y"
    and smult_assoc1:
      "[| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      (a \<otimes> b) \<odot>\<^sub>2 x = a \<odot>\<^sub>2 (b \<odot>\<^sub>2 x)"
    and smult_one [simp]:
      "x \<in> carrier M ==> \<one> \<odot>\<^sub>2 x = x"

locale algebra = module R M + cring M +
  assumes smult_assoc2:
      "[| a \<in> carrier R; x \<in> carrier M; y \<in> carrier M |] ==>
      (a \<odot>\<^sub>2 x) \<otimes>\<^sub>2 y = a \<odot>\<^sub>2 (x \<otimes>\<^sub>2 y)"

lemma moduleI:
  assumes cring: "cring R"
    and abelian_group: "abelian_group M"
    and smult_closed:
      "!!a x. [| a \<in> carrier R; x \<in> carrier M |] ==> smult M a x \<in> carrier M"
    and smult_l_distr:
      "!!a b x. [| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      smult M (add R a b) x = add M (smult M a x) (smult M b x)"
    and smult_r_distr:
      "!!a x y. [| a \<in> carrier R; x \<in> carrier M; y \<in> carrier M |] ==>
      smult M a (add M x y) = add M (smult M a x) (smult M a y)"
    and smult_assoc1:
      "!!a b x. [| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      smult M (mult R a b) x = smult M a (smult M b x)"
    and smult_one:
      "!!x. x \<in> carrier M ==> smult M (one R) x = x"
  shows "module R M"
  by (auto intro: module.intro cring.axioms abelian_group.axioms
    module_axioms.intro prems)

lemma algebraI:
  assumes R_cring: "cring R"
    and M_cring: "cring M"
    and smult_closed:
      "!!a x. [| a \<in> carrier R; x \<in> carrier M |] ==> smult M a x \<in> carrier M"
    and smult_l_distr:
      "!!a b x. [| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      smult M (add R a b) x = add M (smult M a x) (smult M b x)"
    and smult_r_distr:
      "!!a x y. [| a \<in> carrier R; x \<in> carrier M; y \<in> carrier M |] ==>
      smult M a (add M x y) = add M (smult M a x) (smult M a y)"
    and smult_assoc1:
      "!!a b x. [| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      smult M (mult R a b) x = smult M a (smult M b x)"
    and smult_one:
      "!!x. x \<in> carrier M ==> smult M (one R) x = x"
    and smult_assoc2:
      "!!a x y. [| a \<in> carrier R; x \<in> carrier M; y \<in> carrier M |] ==>
      mult M (smult M a x) y = smult M a (mult M x y)"
  shows "algebra R M"
  by (auto intro!: algebra.intro algebra_axioms.intro cring.axioms 
    module_axioms.intro prems)

lemma (in algebra) R_cring:
  "cring R"
  by (rule cring.intro) assumption+

lemma (in algebra) M_cring:
  "cring M"
  by (rule cring.intro) assumption+

lemma (in algebra) module:
  "module R M"
  by (auto intro: moduleI R_cring is_abelian_group
    smult_l_distr smult_r_distr smult_assoc1)

subsection {* Basic Properties of Algebras *}

lemma (in algebra) smult_l_null [simp]:
  "x \<in> carrier M ==> \<zero> \<odot>\<^sub>2 x = \<zero>\<^sub>2"
proof -
  assume M: "x \<in> carrier M"
  note facts = M smult_closed
  from facts have "\<zero> \<odot>\<^sub>2 x = (\<zero> \<odot>\<^sub>2 x \<oplus>\<^sub>2 \<zero> \<odot>\<^sub>2 x) \<oplus>\<^sub>2 \<ominus>\<^sub>2 (\<zero> \<odot>\<^sub>2 x)" by algebra
  also from M have "... = (\<zero> \<oplus> \<zero>) \<odot>\<^sub>2 x \<oplus>\<^sub>2 \<ominus>\<^sub>2 (\<zero> \<odot>\<^sub>2 x)"
    by (simp add: smult_l_distr del: R.l_zero R.r_zero)
  also from facts have "... = \<zero>\<^sub>2" by algebra
  finally show ?thesis .
qed

lemma (in algebra) smult_r_null [simp]:
  "a \<in> carrier R ==> a \<odot>\<^sub>2 \<zero>\<^sub>2 = \<zero>\<^sub>2";
proof -
  assume R: "a \<in> carrier R"
  note facts = R smult_closed
  from facts have "a \<odot>\<^sub>2 \<zero>\<^sub>2 = (a \<odot>\<^sub>2 \<zero>\<^sub>2 \<oplus>\<^sub>2 a \<odot>\<^sub>2 \<zero>\<^sub>2) \<oplus>\<^sub>2 \<ominus>\<^sub>2 (a \<odot>\<^sub>2 \<zero>\<^sub>2)"
    by algebra
  also from R have "... = a \<odot>\<^sub>2 (\<zero>\<^sub>2 \<oplus>\<^sub>2 \<zero>\<^sub>2) \<oplus>\<^sub>2 \<ominus>\<^sub>2 (a \<odot>\<^sub>2 \<zero>\<^sub>2)"
    by (simp add: smult_r_distr del: M.l_zero M.r_zero)
  also from facts have "... = \<zero>\<^sub>2" by algebra
  finally show ?thesis .
qed

lemma (in algebra) smult_l_minus:
  "[| a \<in> carrier R; x \<in> carrier M |] ==> (\<ominus>a) \<odot>\<^sub>2 x = \<ominus>\<^sub>2 (a \<odot>\<^sub>2 x)"
proof -
  assume RM: "a \<in> carrier R" "x \<in> carrier M"
  note facts = RM smult_closed
  from facts have "(\<ominus>a) \<odot>\<^sub>2 x = (\<ominus>a \<odot>\<^sub>2 x \<oplus>\<^sub>2 a \<odot>\<^sub>2 x) \<oplus>\<^sub>2 \<ominus>\<^sub>2(a \<odot>\<^sub>2 x)" by algebra
  also from RM have "... = (\<ominus>a \<oplus> a) \<odot>\<^sub>2 x \<oplus>\<^sub>2 \<ominus>\<^sub>2(a \<odot>\<^sub>2 x)"
    by (simp add: smult_l_distr)
  also from facts smult_l_null have "... = \<ominus>\<^sub>2(a \<odot>\<^sub>2 x)" by algebra
  finally show ?thesis .
qed

lemma (in algebra) smult_r_minus:
  "[| a \<in> carrier R; x \<in> carrier M |] ==> a \<odot>\<^sub>2 (\<ominus>\<^sub>2x) = \<ominus>\<^sub>2 (a \<odot>\<^sub>2 x)"
proof -
  assume RM: "a \<in> carrier R" "x \<in> carrier M"
  note facts = RM smult_closed
  from facts have "a \<odot>\<^sub>2 (\<ominus>\<^sub>2x) = (a \<odot>\<^sub>2 \<ominus>\<^sub>2x \<oplus>\<^sub>2 a \<odot>\<^sub>2 x) \<oplus>\<^sub>2 \<ominus>\<^sub>2(a \<odot>\<^sub>2 x)"
    by algebra
  also from RM have "... = a \<odot>\<^sub>2 (\<ominus>\<^sub>2x \<oplus>\<^sub>2 x) \<oplus>\<^sub>2 \<ominus>\<^sub>2(a \<odot>\<^sub>2 x)"
    by (simp add: smult_r_distr)
  also from facts smult_r_null have "... = \<ominus>\<^sub>2(a \<odot>\<^sub>2 x)" by algebra
  finally show ?thesis .
qed

end
