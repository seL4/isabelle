(*  Title:      HOL/RelPow.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen
*)

open RelPow;

val [rel_pow_0, rel_pow_Suc] = nat_recs rel_pow_def;
Addsimps [rel_pow_0];

goal RelPow.thy "R^1 = R";
by (simp_tac (!simpset addsimps [rel_pow_Suc]) 1);
qed "rel_pow_1";
Addsimps [rel_pow_1];

goal RelPow.thy "(x,x) : R^0";
by (Simp_tac 1);
qed "rel_pow_0_I";

goal RelPow.thy "!!R. [| (x,y) : R^n; (y,z):R |] ==> (x,z):R^(Suc n)";
by (simp_tac (!simpset addsimps [rel_pow_Suc]) 1);
by (Fast_tac 1);
qed "rel_pow_Suc_I";

goal RelPow.thy "!z. (x,y) : R --> (y,z):R^n -->  (x,z):R^(Suc n)";
by (nat_ind_tac "n" 1);
by (simp_tac (!simpset addsimps [rel_pow_Suc]) 1);
by (Fast_tac 1);
by (asm_full_simp_tac (!simpset addsimps [rel_pow_Suc]) 1);
by (Fast_tac 1);
qed_spec_mp "rel_pow_Suc_I2";

goal RelPow.thy "!!R. [| (x,y) : R^0; x=y ==> P |] ==> P";
by (Asm_full_simp_tac 1);
qed "rel_pow_0_E";

val [major,minor] = goal RelPow.thy
  "[| (x,z) : R^(Suc n);  !!y. [| (x,y) : R^n; (y,z) : R |] ==> P |] ==> P";
by (cut_facts_tac [major] 1);
by (asm_full_simp_tac (!simpset addsimps [rel_pow_Suc]) 1);
by (fast_tac (!claset addIs [minor]) 1);
qed "rel_pow_Suc_E";

val [p1,p2,p3] = goal RelPow.thy
    "[| (x,z) : R^n;  [| n=0; x = z |] ==> P;        \
\       !!y m. [| n = Suc m; (x,y) : R^m; (y,z) : R |] ==> P  \
\    |] ==> P";
by (res_inst_tac [("n","n")] natE 1);
by (cut_facts_tac [p1] 1);
by (asm_full_simp_tac (!simpset addsimps [p2]) 1);
by (cut_facts_tac [p1] 1);
by (Asm_full_simp_tac 1);
by (etac rel_pow_Suc_E 1);
by (REPEAT(ares_tac [p3] 1));
qed "rel_pow_E";

goal RelPow.thy "!x z. (x,z):R^(Suc n) --> (? y. (x,y):R & (y,z):R^n)";
by (nat_ind_tac "n" 1);
by (fast_tac (!claset addIs [rel_pow_0_I] addEs [rel_pow_0_E,rel_pow_Suc_E]) 1);
by (fast_tac (!claset addIs [rel_pow_Suc_I] addEs[rel_pow_0_E,rel_pow_Suc_E]) 1);
qed_spec_mp "rel_pow_Suc_D2";

val [p1,p2,p3] = goal RelPow.thy
    "[| (x,z) : R^n;  [| n=0; x = z |] ==> P;        \
\       !!y m. [| n = Suc m; (x,y) : R; (y,z) : R^m |] ==> P  \
\    |] ==> P";
by (res_inst_tac [("n","n")] natE 1);
by (cut_facts_tac [p1] 1);
by (asm_full_simp_tac (!simpset addsimps [p2]) 1);
by (cut_facts_tac [p1] 1);
by (Asm_full_simp_tac 1);
by (dtac rel_pow_Suc_D2 1);
by (etac exE 1);
by (etac p3 1);
by (etac conjunct1 1);
by (etac conjunct2 1);
qed "rel_pow_E2";

goal RelPow.thy "!!p. p:R^* ==> p : (UN n. R^n)";
by (split_all_tac 1);
by (etac rtrancl_induct 1);
by (ALLGOALS (fast_tac (!claset addIs [rel_pow_0_I,rel_pow_Suc_I])));
qed "rtrancl_imp_UN_rel_pow";

goal RelPow.thy "!y. (x,y):R^n --> (x,y):R^*";
by (nat_ind_tac "n" 1);
by (fast_tac (!claset addIs [rtrancl_refl] addEs [rel_pow_0_E]) 1);
by (fast_tac (!claset addEs [rel_pow_Suc_E,rtrancl_into_rtrancl]) 1);
val lemma = result() RS spec RS mp;

goal RelPow.thy "!!p. p:R^n ==> p:R^*";
by (split_all_tac 1);
by (etac lemma 1);
qed "rel_pow_imp_rtrancl";

goal RelPow.thy "R^* = (UN n. R^n)";
by (fast_tac (!claset addIs [rtrancl_imp_UN_rel_pow,rel_pow_imp_rtrancl]) 1);
qed "rtrancl_is_UN_rel_pow";
