(*  Title:      HOL/IMP/Examples.ML
    ID:         $Id$
    Author:     David von Oheimb, TUM
    Copyright   2000 TUM
*)

Addsimps[update_def];

section "An example due to Tony Hoare";

Goal "[| !x. P x --> Q x; <w,s> -c-> t |] ==> \
\ !c. w = While P c --> <While Q c,t> -c-> u --> <While Q c,s> -c-> u";
by (etac evalc.induct 1);
by (Auto_tac);
val lemma1 = result() RS spec RS mp RS mp;

Goal "[| !x. P x --> Q x; <w,s> -c-> u |] ==> \
\ !c. w = While Q c --> <While P c; While Q c,s> -c-> u";
by (etac evalc.induct 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
by (case_tac "P s" 1);
by (Auto_tac);
val lemma2 = result() RS spec RS mp;

Goal "!x. P x --> Q x ==> \
\ (<While P c; While Q c, s> -c-> t) = (<While Q c, s> -c-> t)";
by (blast_tac (claset() addIs [lemma1,lemma2]) 1);
qed "Hoare_example";


section "Factorial";

val step = resolve_tac evalc.intrs 1;
val simp = Asm_simp_tac 1;
Goalw [factorial_def] "a~=b ==> \
\ <factorial a b, Mem(a:=#3)>  -c-> Mem(b:=#6,a:=#0)";
by (ftac not_sym 1);
by step;
by  step;
by simp;
by step;
by   simp;
by  step;
by   step;
by  simp;
by  step;
by simp;
by step;
by   simp;
by  step;
by   step;
by  simp;
by  step;
by simp;
by step;
by   simp;
by  step;
by   step;
by  simp;
by  step;
by simp;
by step;
by simp;
qed "factorial_3";
