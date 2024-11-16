(*  Title:      HOL/Hahn_Banach/Zorn_Lemma.thy
    Author:     Gertrud Bauer, TU Munich
*)

section \<open>Zorn's Lemma\<close>

theory Zorn_Lemma
imports Main
begin

text \<open>
  Zorn's Lemmas states: if every linear ordered subset of an ordered set \<open>S\<close>
  has an upper bound in \<open>S\<close>, then there exists a maximal element in \<open>S\<close>. In
  our application, \<open>S\<close> is a set of sets ordered by set inclusion. Since the
  union of a chain of sets is an upper bound for all elements of the chain,
  the conditions of Zorn's lemma can be modified: if \<open>S\<close> is non-empty, it
  suffices to show that for every non-empty chain \<open>c\<close> in \<open>S\<close> the union of \<open>c\<close>
  also lies in \<open>S\<close>.
\<close>

theorem Zorn's_Lemma:
  assumes r: "\<And>c. c \<in> chains S \<Longrightarrow> \<exists>x. x \<in> c \<Longrightarrow> \<Union>c \<in> S"
    and aS: "a \<in> S"
  shows "\<exists>y \<in> S. \<forall>z \<in> S. y \<subseteq> z \<longrightarrow> z = y"
proof (rule Zorn_Lemma2)
  show "\<forall>c \<in> chains S. \<exists>y \<in> S. \<forall>z \<in> c. z \<subseteq> y"
  proof
    fix c assume "c \<in> chains S"
    show "\<exists>y \<in> S. \<forall>z \<in> c. z \<subseteq> y"
    proof (cases "c = {}")
      txt \<open>If \<open>c\<close> is an empty chain, then every element in \<open>S\<close> is an upper
        bound of \<open>c\<close>.\<close>
      case True
      with aS show ?thesis by fast
    next
      txt \<open>If \<open>c\<close> is non-empty, then \<open>\<Union>c\<close> is an upper bound of \<open>c\<close>, lying in
        \<open>S\<close>.\<close>
      case False
      show ?thesis
      proof
        show "\<forall>z \<in> c. z \<subseteq> \<Union>c" by fast
        show "\<Union>c \<in> S"
        proof (rule r)
          from \<open>c \<noteq> {}\<close> show "\<exists>x. x \<in> c" by fast
          show "c \<in> chains S" by fact
        qed
      qed
    qed
  qed
qed

end
