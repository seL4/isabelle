(*  Title:      HOL/RelPow.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen
*)

open RelPow;

Goal "!!R:: ('a*'a)set. R^1 = R";
by (Simp_tac 1);
qed "rel_pow_1";
Addsimps [rel_pow_1];

Goal "(x,x) : R^0";
by (Simp_tac 1);
qed "rel_pow_0_I";

Goal "[| (x,y) : R^n; (y,z):R |] ==> (x,z):R^(Suc n)";
by (Simp_tac  1);
by (Blast_tac 1);
qed "rel_pow_Suc_I";

Goal "!z. (x,y) : R --> (y,z):R^n -->  (x,z):R^(Suc n)";
by (nat_ind_tac "n" 1);
by (Simp_tac  1);
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "rel_pow_Suc_I2";

Goal "!!R. [| (x,y) : R^0; x=y ==> P |] ==> P";
by (Asm_full_simp_tac 1);
qed "rel_pow_0_E";

val [major,minor] = Goal
  "[| (x,z) : R^(Suc n);  !!y. [| (x,y) : R^n; (y,z) : R |] ==> P |] ==> P";
by (cut_facts_tac [major] 1);
by (Asm_full_simp_tac  1);
by (blast_tac (claset() addIs [minor]) 1);
qed "rel_pow_Suc_E";

val [p1,p2,p3] = Goal
    "[| (x,z) : R^n;  [| n=0; x = z |] ==> P;        \
\       !!y m. [| n = Suc m; (x,y) : R^m; (y,z) : R |] ==> P  \
\    |] ==> P";
by (cut_facts_tac [p1] 1);
by (exhaust_tac "n" 1);
by (asm_full_simp_tac (simpset() addsimps [p2]) 1);
by (Asm_full_simp_tac 1);
by (etac compEpair 1);
by (REPEAT(ares_tac [p3] 1));
qed "rel_pow_E";

Goal "!x z. (x,z):R^(Suc n) --> (? y. (x,y):R & (y,z):R^n)";
by (nat_ind_tac "n" 1);
by (blast_tac (claset() addIs [rel_pow_0_I] 
	                addEs [rel_pow_0_E,rel_pow_Suc_E]) 1);
by (blast_tac (claset() addIs [rel_pow_Suc_I]  
	                addEs [rel_pow_0_E,rel_pow_Suc_E]) 1);
qed_spec_mp "rel_pow_Suc_D2";


Goal "!x y z. (x,y) : R^n & (y,z) : R --> (? w. (x,w) : R & (w,z) : R^n)";
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed_spec_mp "rel_pow_Suc_D2'";

val [p1,p2,p3] = Goal
    "[| (x,z) : R^n;  [| n=0; x = z |] ==> P;        \
\       !!y m. [| n = Suc m; (x,y) : R; (y,z) : R^m |] ==> P  \
\    |] ==> P";
by (cut_facts_tac [p1] 1);
by (exhaust_tac "n" 1);
by (asm_full_simp_tac (simpset() addsimps [p2]) 1);
by (Asm_full_simp_tac 1);
by (etac compEpair 1);
by (dtac (conjI RS rel_pow_Suc_D2') 1);
by (assume_tac 1);
by (etac exE 1);
by (etac p3 1);
by (etac conjunct1 1);
by (etac conjunct2 1);
qed "rel_pow_E2";

Goal "!!p. p:R^* ==> p : (UN n. R^n)";
by (split_all_tac 1);
by (etac rtrancl_induct 1);
by (ALLGOALS (blast_tac (claset() addIs [rel_pow_0_I,rel_pow_Suc_I])));
qed "rtrancl_imp_UN_rel_pow";

Goal "!y. (x,y):R^n --> (x,y):R^*";
by (nat_ind_tac "n" 1);
by (blast_tac (claset() addIs [rtrancl_refl] addEs [rel_pow_0_E]) 1);
by (blast_tac (claset() addEs [rel_pow_Suc_E]
                       addIs [rtrancl_into_rtrancl]) 1);
val lemma = result() RS spec RS mp;

Goal "!!p. p:R^n ==> p:R^*";
by (split_all_tac 1);
by (etac lemma 1);
qed "rel_pow_imp_rtrancl";

Goal "R^* = (UN n. R^n)";
by (blast_tac (claset() addIs [rtrancl_imp_UN_rel_pow, rel_pow_imp_rtrancl]) 1);
qed "rtrancl_is_UN_rel_pow";


Goal "!!r::('a * 'a)set. univalent r ==> univalent (r^n)";
by (rtac univalentI 1);
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (fast_tac (claset() addDs [univalentD] addEs [rel_pow_Suc_E]) 1);
qed_spec_mp "univalent_rel_pow";




