(*  Title:      HOLCF/ex/Fix2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1995 Technische Universitaet Muenchen
*)

Goal "fix = gix";
by (rtac ext_cfun 1);
by (rtac antisym_less 1);
by (rtac fix_least 1);
by (rtac gix1_def 1);
by (rtac gix2_def 1);
by (rtac (fix_eq RS sym) 1);
qed "lemma1";


Goal "gix$F=lub(range(%i. iterate i F UU))";
by (rtac (lemma1 RS subst) 1);
by (rtac fix_def2 1);
qed "lemma2";


