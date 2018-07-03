(*  Title:      HOL/Algebra/Module.thy
    Author:     Clemens Ballarin, started 15 April 2003
                with contributions by Martin Baillon
*)

theory Module
imports Ring
begin

section \<open>Modules over an Abelian Group\<close>

subsection \<open>Definitions\<close>

record ('a, 'b) module = "'b ring" +
  smult :: "['a, 'b] => 'b" (infixl "\<odot>\<index>" 70)

locale module = R?: cring + M?: abelian_group M for M (structure) +
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

locale algebra = module + cring M +
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
    module_axioms.intro assms)

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
  apply intro_locales
             apply (rule cring.axioms ring.axioms abelian_group.axioms comm_monoid.axioms assms)+
      apply (rule module_axioms.intro)
          apply (simp add: smult_closed)
         apply (simp add: smult_l_distr)
        apply (simp add: smult_r_distr)
       apply (simp add: smult_assoc1)
      apply (simp add: smult_one)
     apply (rule cring.axioms ring.axioms abelian_group.axioms comm_monoid.axioms assms)+
  apply (rule algebra_axioms.intro)
  apply (simp add: smult_assoc2)
  done

lemma (in algebra) R_cring: "cring R" ..

lemma (in algebra) M_cring: "cring M" ..

lemma (in algebra) module: "module R M"
  by (auto intro: moduleI R_cring is_abelian_group smult_l_distr smult_r_distr smult_assoc1)


subsection \<open>Basic Properties of Modules\<close>

lemma (in module) smult_l_null [simp]:
 "x \<in> carrier M ==> \<zero> \<odot>\<^bsub>M\<^esub> x = \<zero>\<^bsub>M\<^esub>"
proof-
  assume M : "x \<in> carrier M"
  note facts = M smult_closed [OF R.zero_closed]
  from facts have "\<zero> \<odot>\<^bsub>M\<^esub> x = (\<zero> \<oplus> \<zero>) \<odot>\<^bsub>M\<^esub> x "
    using smult_l_distr by auto
  also have "... = \<zero> \<odot>\<^bsub>M\<^esub> x \<oplus>\<^bsub>M\<^esub> \<zero> \<odot>\<^bsub>M\<^esub> x"
    using smult_l_distr[of \<zero> \<zero> x] facts by auto
  finally show "\<zero> \<odot>\<^bsub>M\<^esub> x = \<zero>\<^bsub>M\<^esub>" using facts
    by (metis M.add.r_cancel_one')
qed

lemma (in module) smult_r_null [simp]:
  "a \<in> carrier R ==> a \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub> = \<zero>\<^bsub>M\<^esub>"
proof -
  assume R: "a \<in> carrier R"
  note facts = R smult_closed
  from facts have "a \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub> = (a \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub> \<oplus>\<^bsub>M\<^esub> a \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub>) \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub> (a \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub>)"
    by (simp add: M.add.inv_solve_right)
  also from R have "... = a \<odot>\<^bsub>M\<^esub> (\<zero>\<^bsub>M\<^esub> \<oplus>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub>) \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub> (a \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub>)"
    by (simp add: smult_r_distr del: M.l_zero M.r_zero)
  also from facts have "... = \<zero>\<^bsub>M\<^esub>"
    by (simp add: M.r_neg)
  finally show ?thesis .
qed

lemma (in module) smult_l_minus:
"\<lbrakk> a \<in> carrier R; x \<in> carrier M \<rbrakk> \<Longrightarrow> (\<ominus>a) \<odot>\<^bsub>M\<^esub> x = \<ominus>\<^bsub>M\<^esub> (a \<odot>\<^bsub>M\<^esub> x)"
proof-
  assume RM: "a \<in> carrier R" "x \<in> carrier M"
  from RM have a_smult: "a \<odot>\<^bsub>M\<^esub> x \<in> carrier M" by simp
  from RM have ma_smult: "\<ominus>a \<odot>\<^bsub>M\<^esub> x \<in> carrier M" by simp
  note facts = RM a_smult ma_smult
  from facts have "(\<ominus>a) \<odot>\<^bsub>M\<^esub> x = (\<ominus>a \<odot>\<^bsub>M\<^esub> x \<oplus>\<^bsub>M\<^esub> a \<odot>\<^bsub>M\<^esub> x) \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub>(a \<odot>\<^bsub>M\<^esub> x)"
    by (simp add: M.add.inv_solve_right)
  also from RM have "... = (\<ominus>a \<oplus> a) \<odot>\<^bsub>M\<^esub> x \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub>(a \<odot>\<^bsub>M\<^esub> x)"
    by (simp add: smult_l_distr)
  also from facts smult_l_null have "... = \<ominus>\<^bsub>M\<^esub>(a \<odot>\<^bsub>M\<^esub> x)"
    by (simp add: R.l_neg)
  finally show ?thesis .
qed

lemma (in module) smult_r_minus:
  "[| a \<in> carrier R; x \<in> carrier M |] ==> a \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub>x) = \<ominus>\<^bsub>M\<^esub> (a \<odot>\<^bsub>M\<^esub> x)"
proof -
  assume RM: "a \<in> carrier R" "x \<in> carrier M"
  note facts = RM smult_closed
  from facts have "a \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub>x) = (a \<odot>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub>x \<oplus>\<^bsub>M\<^esub> a \<odot>\<^bsub>M\<^esub> x) \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub>(a \<odot>\<^bsub>M\<^esub> x)"
    by (simp add: M.add.inv_solve_right)
  also from RM have "... = a \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub>x \<oplus>\<^bsub>M\<^esub> x) \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub>(a \<odot>\<^bsub>M\<^esub> x)"
    by (simp add: smult_r_distr)
  also from facts smult_l_null have "... = \<ominus>\<^bsub>M\<^esub>(a \<odot>\<^bsub>M\<^esub> x)"
    by (metis M.add.inv_closed M.add.inv_solve_right M.l_neg R.zero_closed r_null smult_assoc1)
  finally show ?thesis .
qed

lemma (in module) finsum_smult_ldistr:
  "\<lbrakk> finite A; a \<in> carrier R; f: A \<rightarrow> carrier M \<rbrakk> \<Longrightarrow>
     a \<odot>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub> i \<in> A. (f i)) = (\<Oplus>\<^bsub>M\<^esub> i \<in> A. ( a \<odot>\<^bsub>M\<^esub> (f i)))"
proof (induct set: finite)
  case empty then show ?case
    by (metis M.finsum_empty M.zero_closed R.zero_closed r_null smult_assoc1 smult_l_null)
next
  case (insert x F) then show ?case
    by (simp add: Pi_def smult_r_distr)
qed

end
