(*  Title:      HOL/Hahn_Banach/Bounds.thy
    Author:     Gertrud Bauer, TU Munich
*)

section \<open>Bounds\<close>

theory Bounds
imports Main "HOL-Analysis.Continuum_Not_Denumerable"
begin

locale lub =
  fixes A and x
  assumes least [intro?]: "(\<And>a. a \<in> A \<Longrightarrow> a \<le> b) \<Longrightarrow> x \<le> b"
    and upper [intro?]: "a \<in> A \<Longrightarrow> a \<le> x"

lemmas [elim?] = lub.least lub.upper

definition the_lub :: "'a::order set \<Rightarrow> 'a"  (\<open>\<Squnion>_\<close> [90] 90)
  where "the_lub A = The (lub A)"

lemma the_lub_equality [elim?]:
  assumes "lub A x"
  shows "\<Squnion>A = (x::'a::order)"
proof -
  interpret lub A x by fact
  show ?thesis
  proof (unfold the_lub_def)
    from \<open>lub A x\<close> show "The (lub A) = x"
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

lemma real_complete: "\<exists>a::real. a \<in> A \<Longrightarrow> \<exists>y. \<forall>a \<in> A. a \<le> y \<Longrightarrow> \<exists>x. lub A x"
  by (intro exI[of _ "Sup A"]) (auto intro!: cSup_upper cSup_least simp: lub_def)

end
