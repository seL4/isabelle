(*  Title:      HOL/RelPow.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen
*)

open RelPow;

val [rel_pow_0, rel_pow_Suc] = nat_recs rel_pow_def;
Addsimps [rel_pow_0, rel_pow_Suc];

goal RelPow.thy "(x,x) : R^0";
by(Simp_tac 1);
qed "rel_pow_0_I";

goal RelPow.thy "!!R. [| (x,y) : R^n; (y,z):R |] ==> (x,z):R^(Suc n)";
by(Simp_tac 1);
by(fast_tac comp_cs 1);
qed "rel_pow_Suc_I";

goal RelPow.thy "!z. (x,y) : R --> (y,z):R^n -->  (x,z):R^(Suc n)";
by(nat_ind_tac "n" 1);
by(Simp_tac 1);
by(fast_tac comp_cs 1);
by(Asm_full_simp_tac 1);
by(fast_tac comp_cs 1);
qed_spec_mp "rel_pow_Suc_I2";

goal RelPow.thy "!x z. (x,z):R^(Suc n) --> (? y. (x,y):R & (y,z):R^n)";
by(nat_ind_tac "n" 1);
by(Simp_tac 1);
by(fast_tac comp_cs 1);
by(Asm_full_simp_tac 1);
by(fast_tac comp_cs 1);
val lemma = result() RS spec RS spec RS mp;

goal RelPow.thy
  "(x,z) : R^n --> (n=0 --> x=z --> P) --> \
\     (!y m. n = Suc m --> (x,y):R --> (y,z):R^m --> P) --> P";
by(res_inst_tac [("n","n")] natE 1);
by(Asm_simp_tac 1);
by(hyp_subst_tac 1);
by(fast_tac (HOL_cs addDs [lemma]) 1);
val lemma = result() RS mp RS mp RS mp;

val [p1,p2,p3] = goal RelPow.thy
    "[| (x,z) : R^n;  [| n=0; x = z |] ==> P;        \
\       !!y m. [| n = Suc m; (x,y) : R; (y,z) : R^m |] ==> P  \
\    |] ==> P";
br (p1 RS lemma) 1;
by(REPEAT(ares_tac [impI,p2] 1));
by(REPEAT(ares_tac [allI,impI,p3] 1));
qed "UN_rel_powE2";

goal RelPow.thy "!!p. p:R^* ==> p : (UN n. R^n)";
by(split_all_tac 1);
be rtrancl_induct 1;
by(ALLGOALS (fast_tac (rel_cs addIs [rel_pow_0_I,rel_pow_Suc_I])));
qed "rtrancl_imp_UN_rel_pow";

goal RelPow.thy "!y. (x,y):R^n --> (x,y):R^*";
by(nat_ind_tac "n" 1);
by(Simp_tac 1);
by(fast_tac (HOL_cs addIs [rtrancl_refl]) 1);
by(Simp_tac 1);
by(fast_tac (trancl_cs addEs [rtrancl_into_rtrancl]) 1);
val lemma = result() RS spec RS mp;

goal RelPow.thy "!!p. p:R^n ==> p:R^*";
by(split_all_tac 1);
be lemma 1;
qed "UN_rel_pow_imp_rtrancl";

goal RelPow.thy "R^* = (UN n. R^n)";
by(fast_tac (eq_cs addIs [rtrancl_imp_UN_rel_pow,UN_rel_pow_imp_rtrancl]) 1);
qed "rtrancl_is_UN_rel_pow";
