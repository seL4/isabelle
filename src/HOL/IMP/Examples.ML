(*  Title:      HOL/IMP/Examples.ML
    ID:         $Id$
    Author:     David von Oheimb, TUM
    Copyright   2000 TUM
*)

(*###should go to Fun.ML*)
Goal "f(x:=y,a:=b,x:=z) = f(a:=b,x:=z)";
by (rtac ext 1);
by (Simp_tac 1);
qed "fun_upd_upd2";
Addsimps [fun_upd_upd2];

Addsimps[update_def];

section "Examples";

val step = resolve_tac evalc.intrs 1;
val simp = Asm_simp_tac 1;
Goalw [factorial_def] "a~=b ==> \
\ <factorial a b, Mem(a:=#3)>  -c-> Mem(b:=#6,a:=#0)";
by (ftac not_sym 1);
by step;
by  step;
by step;
by   simp;
by  step;
by   step;
by  step;
by simp;
by step;
by   simp;
by  step;
by   step;
by  step;
by simp;
by step;
by   simp;
by  step;
by   step;
by  step;
by simp;
by step;
by simp;
qed "factorial_3";
