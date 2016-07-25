(*  Title:      HOL/HOLCF/ex/Fix2.thy
    Author:     Franz Regensburger

Show that fix is the unique least fixed-point operator.
From axioms gix1_def,gix2_def it follows that fix = gix
*)

theory Fix2
imports HOLCF
begin

axiomatization
  gix :: "('a \<rightarrow> 'a) \<rightarrow>'a" where
  gix1_def: "F\<cdot>(gix\<cdot>F) = gix\<cdot>F" and
  gix2_def: "F\<cdot>y = y \<Longrightarrow> gix\<cdot>F << y"


lemma lemma1: "fix = gix"
apply (rule cfun_eqI)
apply (rule below_antisym)
apply (rule fix_least)
apply (rule gix1_def)
apply (rule gix2_def)
apply (rule fix_eq [symmetric])
done

lemma lemma2: "gix\<cdot>F = lub (range (\<lambda>i. iterate i\<cdot>F\<cdot>UU))"
apply (rule lemma1 [THEN subst])
apply (rule fix_def2)
done

end
