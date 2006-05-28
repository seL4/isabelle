(*  Title:      HOLCF/ex/Fix2.thy
    ID:         $Id$
    Author:     Franz Regensburger

Show that fix is the unique least fixed-point operator.
From axioms gix1_def,gix2_def it follows that fix = gix
*)

theory Fix2
imports HOLCF
begin

consts
  gix     :: "('a->'a)->'a"

axioms
  gix1_def: "F$(gix$F) = gix$F"
  gix2_def: "F$y=y ==> gix$F << y"


lemma lemma1: "fix = gix"
apply (rule ext_cfun)
apply (rule antisym_less)
apply (rule fix_least)
apply (rule gix1_def)
apply (rule gix2_def)
apply (rule fix_eq [symmetric])
done

lemma lemma2: "gix$F=lub(range(%i. iterate i$F$UU))"
apply (rule lemma1 [THEN subst])
apply (rule fix_def2)
done

end
