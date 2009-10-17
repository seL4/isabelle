(*  Title:      HOL/Hahn_Banach/Bounds.thy
    Author:     Gertrud Bauer, TU Munich
*)

header {* Bounds *}

theory Bounds
imports Main ContNotDenum
begin

locale lub =
  fixes A and x
  assumes least [intro?]: "(\<And>a. a \<in> A \<Longrightarrow> a \<le> b) \<Longrightarrow> x \<le> b"
    and upper [intro?]: "a \<in> A \<Longrightarrow> a \<le> x"

lemmas [elim?] = lub.least lub.upper

definition
  the_lub :: "'a::order set \<Rightarrow> 'a" where
  "the_lub A = The (lub A)"

notation (xsymbols)
  the_lub  ("\<Squnion>_" [90] 90)

lemma the_lub_equality [elim?]:
  assumes "lub A x"
  shows "\<Squnion>A = (x::'a::order)"
proof -
  interpret lub A x by fact
  show ?thesis
  proof (unfold the_lub_def)
    from `lub A x` show "The (lub A) = x"
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
    unfolding isUb_def setle_def by blast
  with nonempty have "\<exists>x. isLub UNIV A x"
    by (rule reals_complete)
  then show ?thesis by (simp only: lub_compat)
qed

end
