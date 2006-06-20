(*  Title:      HOL/Algebra/Module.thy
    ID:         $Id$
    Author:     Clemens Ballarin, started 15 April 2003
    Copyright:  Clemens Ballarin
*)

header {* Modules over an Abelian Group *}

theory Module imports CRing begin

record ('a, 'b) module = "'b ring" +
  smult :: "['a, 'b] => 'b" (infixl "\<odot>\<index>" 70)

locale module = cring R + abelian_group M +
  assumes smult_closed [simp, intro]:
      "[| a \<in> carrier R; x \<in> carrier M |] ==> a \<odot>\<^bsub>M\<^esub> x \<in> carrier M"
    and smult_l_distr:
      "[| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      (a \<oplus> b) \<odot>\<^bsub>M\<^esub> x = a \<odot>\<^bsub>M\<^esub> x \<oplus>\<^bsub>M\<^esub> b \<odot>\<^bsub>M\<^esub> x"
    and smult_r_distr:
      "[| a \<in> carrier R; x \<in> carrier M; y \<in> carrier M |] ==>
      a \<odot>\<^bsub>M\<^esub> (x \<oplus>\<^bsub>M\<^esub> y) = a \<odot>\<^bsub>M\<^esub> x \<oplus>\<^bsub>M\<^esub> a \<odot>\<^bsub>M\<^esub> y"
    and smult_assoc1:
      "[| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      (a \<otimes> b) \<odot>\<^bsub>M\<^esub> x = a \<odot>\<^bsub>M\<^esub> (b \<odot>\<^bsub>M\<^esub> x)"
    and smult_one [simp]:
      "x \<in> carrier M ==> \<one> \<odot>\<^bsub>M\<^esub> x = x"

locale algebra = module R M + cring M +
  assumes smult_assoc2:
      "[| a \<in> carrier R; x \<in> carrier M; y \<in> carrier M |] ==>
      (a \<odot>\<^bsub>M\<^esub> x) \<otimes>\<^bsub>M\<^esub> y = a \<odot>\<^bsub>M\<^esub> (x \<otimes>\<^bsub>M\<^esub> y)"

lemma moduleI:
  fixes R (structure) and M (structure)
  assumes cring: "cring R"
    and abelian_group: "abelian_group M"
    and smult_closed:
      "!!a x. [| a \<in> carrier R; x \<in> carrier M |] ==> a \<odot>\<^bsub>M\<^esub> x \<in> carrier M"
    and smult_l_distr:
      "!!a b x. [| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      (a \<oplus> b) \<odot>\<^bsub>M\<^esub> x = (a \<odot>\<^bsub>M\<^esub> x) \<oplus>\<^bsub>M\<^esub> (b \<odot>\<^bsub>M\<^esub> x)"
    and smult_r_distr:
      "!!a x y. [| a \<in> carrier R; x \<in> carrier M; y \<in> carrier M |] ==>
      a \<odot>\<^bsub>M\<^esub> (x \<oplus>\<^bsub>M\<^esub> y) = (a \<odot>\<^bsub>M\<^esub> x) \<oplus>\<^bsub>M\<^esub> (a \<odot>\<^bsub>M\<^esub> y)"
    and smult_assoc1:
      "!!a b x. [| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      (a \<otimes> b) \<odot>\<^bsub>M\<^esub> x = a \<odot>\<^bsub>M\<^esub> (b \<odot>\<^bsub>M\<^esub> x)"
    and smult_one:
      "!!x. x \<in> carrier M ==> \<one> \<odot>\<^bsub>M\<^esub> x = x"
  shows "module R M"
  by (auto intro: module.intro cring.axioms abelian_group.axioms
    module_axioms.intro prems)

lemma algebraI:
  fixes R (structure) and M (structure)
  assumes R_cring: "cring R"
    and M_cring: "cring M"
    and smult_closed:
      "!!a x. [| a \<in> carrier R; x \<in> carrier M |] ==> a \<odot>\<^bsub>M\<^esub> x \<in> carrier M"
    and smult_l_distr:
      "!!a b x. [| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      (a \<oplus> b) \<odot>\<^bsub>M\<^esub> x = (a \<odot>\<^bsub>M\<^esub> x) \<oplus>\<^bsub>M\<^esub> (b \<odot>\<^bsub>M\<^esub> x)"
    and smult_r_distr:
      "!!a x y. [| a \<in> carrier R; x \<in> carrier M; y \<in> carrier M |] ==>
      a \<odot>\<^bsub>M\<^esub> (x \<oplus>\<^bsub>M\<^esub> y) = (a \<odot>\<^bsub>M\<^esub> x) \<oplus>\<^bsub>M\<^esub> (a \<odot>\<^bsub>M\<^esub> y)"
    and smult_assoc1:
      "!!a b x. [| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      (a \<otimes> b) \<odot>\<^bsub>M\<^esub> x = a \<odot>\<^bsub>M\<^esub> (b \<odot>\<^bsub>M\<^esub> x)"
    and smult_one:
      "!!x. x \<in> carrier M ==> (one R) \<odot>\<^bsub>M\<^esub> x = x"
    and smult_assoc2:
      "!!a x y. [| a \<in> carrier R; x \<in> carrier M; y \<in> carrier M |] ==>
      (a \<odot>\<^bsub>M\<^esub> x) \<otimes>\<^bsub>M\<^esub> y = a \<odot>\<^bsub>M\<^esub> (x \<otimes>\<^bsub>M\<^esub> y)"
  shows "algebra R M"
apply (intro_locales!)
apply (rule cring.axioms ring.axioms abelian_group.axioms comm_monoid.axioms prems)+
apply (rule module_axioms.intro)
 apply (simp add: smult_closed)
 apply (simp add: smult_l_distr)
 apply (simp add: smult_r_distr)
 apply (simp add: smult_assoc1)
 apply (simp add: smult_one)
apply (rule cring.axioms ring.axioms abelian_group.axioms comm_monoid.axioms prems)+
apply (rule algebra_axioms.intro)
 apply (simp add: smult_assoc2)
done

lemma (in algebra) R_cring:
  "cring R"
  by intro_locales

lemma (in algebra) M_cring:
  "cring M"
  by intro_locales

lemma (in algebra) module:
  "module R M"
  by (auto intro: moduleI R_cring is_abelian_group
    smult_l_distr smult_r_distr smult_assoc1)


subsection {* Basic Properties of Algebras *}

lemma (in algebra) smult_l_null [simp]:
  "x \<in> carrier M ==> \<zero> \<odot>\<^bsub>M\<^esub> x = \<zero>\<^bsub>M\<^esub>"
proof -
  assume M: "x \<in> carrier M"
  note facts = M smult_closed
  from facts have "\<zero> \<odot>\<^bsub>M\<^esub> x = (\<zero> \<odot>\<^bsub>M\<^esub> x \<oplus>\<^bsub>M\<^esub> \<zero> \<odot>\<^bsub>M\<^esub> x) \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub> (\<zero> \<odot>\<^bsub>M\<^esub> x)" by algebra
  also from M have "... = (\<zero> \<oplus> \<zero>) \<odot>\<^bsub>M\<^esub> x \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub> (\<zero> \<odot>\<^bsub>M\<^esub> x)"
    by (simp add: smult_l_distr del: R.l_zero R.r_zero)
  also from facts have "... = \<zero>\<^bsub>M\<^esub>" by algebra
  finally show ?thesis .
qed

lemma (in algebra) smult_r_null [simp]:
  "a \<in> carrier R ==> a \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub> = \<zero>\<^bsub>M\<^esub>";
proof -
  assume R: "a \<in> carrier R"
  note facts = R smult_closed
  from facts have "a \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub> = (a \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub> \<oplus>\<^bsub>M\<^esub> a \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub>) \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub> (a \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub>)"
    by algebra
  also from R have "... = a \<odot>\<^bsub>M\<^esub> (\<zero>\<^bsub>M\<^esub> \<oplus>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub>) \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub> (a \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub>)"
    by (simp add: smult_r_distr del: M.l_zero M.r_zero)
  also from facts have "... = \<zero>\<^bsub>M\<^esub>" by algebra
  finally show ?thesis .
qed

lemma (in algebra) smult_l_minus:
  "[| a \<in> carrier R; x \<in> carrier M |] ==> (\<ominus>a) \<odot>\<^bsub>M\<^esub> x = \<ominus>\<^bsub>M\<^esub> (a \<odot>\<^bsub>M\<^esub> x)"
proof -
  assume RM: "a \<in> carrier R" "x \<in> carrier M"
  note facts = RM smult_closed
  from facts have "(\<ominus>a) \<odot>\<^bsub>M\<^esub> x = (\<ominus>a \<odot>\<^bsub>M\<^esub> x \<oplus>\<^bsub>M\<^esub> a \<odot>\<^bsub>M\<^esub> x) \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub>(a \<odot>\<^bsub>M\<^esub> x)"
    by algebra
  also from RM have "... = (\<ominus>a \<oplus> a) \<odot>\<^bsub>M\<^esub> x \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub>(a \<odot>\<^bsub>M\<^esub> x)"
    by (simp add: smult_l_distr)
  also from facts smult_l_null have "... = \<ominus>\<^bsub>M\<^esub>(a \<odot>\<^bsub>M\<^esub> x)" by algebra
  finally show ?thesis .
qed

lemma (in algebra) smult_r_minus:
  "[| a \<in> carrier R; x \<in> carrier M |] ==> a \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub>x) = \<ominus>\<^bsub>M\<^esub> (a \<odot>\<^bsub>M\<^esub> x)"
proof -
  assume RM: "a \<in> carrier R" "x \<in> carrier M"
  note facts = RM smult_closed
  from facts have "a \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub>x) = (a \<odot>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub>x \<oplus>\<^bsub>M\<^esub> a \<odot>\<^bsub>M\<^esub> x) \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub>(a \<odot>\<^bsub>M\<^esub> x)"
    by algebra
  also from RM have "... = a \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub>x \<oplus>\<^bsub>M\<^esub> x) \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub>(a \<odot>\<^bsub>M\<^esub> x)"
    by (simp add: smult_r_distr)
  also from facts smult_r_null have "... = \<ominus>\<^bsub>M\<^esub>(a \<odot>\<^bsub>M\<^esub> x)" by algebra
  finally show ?thesis .
qed

end
