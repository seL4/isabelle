(* Title:     HOL/W0/Maybe.ML
   ID:        $Id$
   Author:    Dieter Nazareth and Tobias Nipkow
   Copyright  1995 TU Muenchen
*)


(* constructor laws for bind *)
Goalw [bind_def] "(Ok s) bind f = (f s)";
by (Simp_tac 1);
qed "bind_Ok";

Goalw [bind_def] "Fail bind f = Fail";
by (Simp_tac 1);
qed "bind_Fail";

Addsimps [bind_Ok,bind_Fail];

(* case splitting of bind *)
Goal
  "P(res bind f) = ((res = Fail --> P Fail) & (!s. res = Ok s --> P(f s)))";
by (induct_tac "res" 1);
by (fast_tac (HOL_cs addss simpset()) 1);
by (Asm_simp_tac 1);
qed "split_bind";

Goal
  "P(res bind f) = (~ (res = Fail & ~ P Fail | (? s. res = Ok s & ~ P(f s))))";
 by (simp_tac (simpset() addsplits [split_bind]) 1);
qed "split_bind_asm";

bind_thms ("bind_splits", [split_bind, split_bind_asm]);

Goal
  "((m bind f) = Fail) = ((m=Fail) | (? p. m = Ok p & f p = Fail))";
by (simp_tac (simpset() addsplits [split_bind]) 1);
qed "bind_eq_Fail";

Addsimps [bind_eq_Fail];
