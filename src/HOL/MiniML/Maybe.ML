open Maybe;

(* constructor laws for bind *)
goalw thy [bind_def] "(Ok s) bind f = (f s)";
by (Simp_tac 1);
qed "bind_Ok";

goalw thy [bind_def] "Fail bind f = Fail";
by (Simp_tac 1);
qed "bind_Fail";

Addsimps [bind_Ok,bind_Fail];

(* expansion of bind *)
goal thy
  "P(res bind f) = ((res = Fail --> P Fail) & (!s. res = Ok s --> P(f s)))";
by (maybe.induct_tac "res" 1);
by (fast_tac (HOL_cs addss !simpset) 1);
by (Asm_simp_tac 1);
qed "expand_bind";

goal Maybe.thy
  "((m bind f) = Fail) = ((m=Fail) | (? p. m = Ok p & f p = Fail))";
by (simp_tac (!simpset setloop (split_tac [expand_bind])) 1);
by (fast_tac HOL_cs 1);
qed "bind_eq_Fail";

Addsimps [bind_eq_Fail];
