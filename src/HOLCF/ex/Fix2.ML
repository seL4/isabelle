(*  Title:      HOLCF/ex/Fix2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1995 Technische Universitaet Muenchen
*)

open Fix2;

val lemma1 = prove_goal Fix2.thy "fix = gix"
 (fn prems =>
        [
        (rtac ext_cfun 1),
        (rtac antisym_less 1),
        (rtac fix_least 1),
        (rtac gix1_def 1),
        (rtac gix2_def 1),
        (rtac (fix_eq RS sym) 1)
        ]);


val lemma2 = prove_goal Fix2.thy "gix`F=lub(range(%i. iterate i F UU))"
 (fn prems =>
        [
        (rtac (lemma1 RS subst) 1),
        (rtac fix_def2 1)
        ]);


