(*  Title:      HOL/Real/HahnBanach/Bounds.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Bounds *}

theory Bounds = Main + Real:

locale lub =
  fixes A and x
  assumes least [intro?]: "(\<And>a. a \<in> A \<Longrightarrow> a \<le> b) \<Longrightarrow> x \<le> b"
    and upper [intro?]: "a \<in> A \<Longrightarrow> a \<le> x"

lemmas [elim?] = lub.least lub.upper

syntax (xsymbols)
  the_lub :: "'a::order set \<Rightarrow> 'a"    ("\<Squnion>_" [90] 90)

constdefs
  the_lub :: "'a::order set \<Rightarrow> 'a"
  "\<Squnion>A \<equiv> The (lub A)"

lemma the_lub_equality [elim?]:
  includes lub
  shows "\<Squnion>A = (x::'a::order)"
proof (unfold the_lub_def)
  from lub_axioms show "The (lub A) = x"
  proof
    fix x' assume lub': "lub A x'"
    show "x' = x"
    proof (rule order_antisym)
      from lub' show "x' \<le> x"
      proof
        fix a assume "a \<in> A"
        then show "a \<le> x" ..
      qed
      show "x \<le> x'"
      proof
        fix a assume "a \<in> A"
        with lub' show "a \<le> x'" ..
      qed
    qed
  qed
qed

lemma the_lubI_ex:
  assumes ex: "\<exists>x. lub A x"
  shows "lub A (\<Squnion>A)"
proof -
  from ex obtain x where x: "lub A x" ..
  also from x have [symmetric]: "\<Squnion>A = x" ..
  finally show ?thesis .
qed

lemma lub_compat: "lub A x = isLub UNIV A x"
proof -
  have "isUb UNIV A = (\<lambda>x. A *<= x \<and> x \<in> UNIV)"
    by (rule ext) (simp only: isUb_def)
  then show ?thesis
    by (simp only: lub_def isLub_def leastP_def setge_def setle_def) blast
qed

lemma real_complete:
  fixes A :: "real set"
  assumes nonempty: "\<exists>a. a \<in> A"
    and ex_upper: "\<exists>y. \<forall>a \<in> A. a \<le> y"
  shows "\<exists>x. lub A x"
proof -
  from ex_upper have "\<exists>y. isUb UNIV A y"
    by (unfold isUb_def setle_def) blast
  with nonempty have "\<exists>x. isLub UNIV A x"
    by (rule reals_complete)
  then show ?thesis by (simp only: lub_compat)
qed

end
