(*  Title:      HOL/Isar_examples/Drinker.thy
    ID:         $Id$
    Author:     Makarius
*)

header {* The Drinker's Principle *}

theory Drinker imports Main begin

text {*
 Two parts of de-Morgan's law -- one intuitionistic and one classical:
*}

lemma deMorgan1: "\<not> (\<exists>x. P x) \<Longrightarrow> \<forall>x. \<not> P x"
proof -
  assume a: "\<not> (\<exists>x. P x)"
  show ?thesis
  proof
    fix x
    show "\<not> P x"
    proof
      assume "P x"
      then have "\<exists>x. P x" ..
      with a show False by contradiction
    qed
  qed
qed

lemma deMorgan2: "\<not> (\<forall>x. P x) \<Longrightarrow> \<exists>x. \<not> P x"
proof (rule classical)
  assume a: "\<not> (\<forall>x. P x)"
  assume b: "\<not> (\<exists>x. \<not> P x)"
  have "\<forall>x. P x"
  proof
    fix x
    show "P x"
    proof (rule classical)
      assume c: "\<not> P x"
      from b have "\<forall>x. \<not> \<not> P x" by (rule deMorgan1)
      then have "\<not> \<not> P x" ..
      with c show ?thesis by contradiction
    qed
  qed
  with a show ?thesis by contradiction
qed

text {*
 Here is another example of classical reasoning: the Drinker's
 Principle says that for some person, if he is drunk, everybody else
 is drunk!
*}

theorem Drinker's_Principle: "\<exists>x. drunk x \<longrightarrow> (\<forall>x. drunk x)"
proof cases
  fix a assume "\<forall>x. drunk x"
  then have "drunk a \<longrightarrow> (\<forall>x. drunk x)" ..
  then show ?thesis ..
next
  assume "\<not> (\<forall>x. drunk x)"
  then have "\<exists>x. \<not> drunk x" by (rule deMorgan2)
  then obtain a where a: "\<not> drunk a" ..
  have "drunk a \<longrightarrow> (\<forall>x. drunk x)"
  proof
    assume "drunk a"
    with a show "\<forall>x. drunk x" by (contradiction)
  qed
  then show ?thesis ..
qed

end
