(*  Title:      HOL/BCV/Semilat.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

Goalw [order_def] "order r ==> x <=_r x";
by (Asm_simp_tac 1);
qed "order_refl";
Addsimps [order_refl];
AddIs [order_refl];

Goalw [order_def] "[| order r; x <=_r y; y <=_r x |] ==> x = y";
by (Asm_simp_tac 1);
qed "order_antisym";

Goalw [order_def] "[| order r; x <=_r y; y <=_r z |] ==> x <=_r z";
by (Blast_tac 1);
qed "order_trans";

Goalw [order_def,lesssub_def] "order r ==> ~ x <_r x";
by (Blast_tac 1);
qed "order_less_irrefl";
AddIs [order_less_irrefl];
Addsimps [order_less_irrefl];

Goalw [order_def,lesssub_def] "[| order r; x <_r y; y <_r z |] ==> x <_r z";
by (Blast_tac 1);
qed "order_less_trans";

Goalw [top_def] "top r T ==> x <=_r T";
by (Asm_simp_tac 1);
qed "topD";
Addsimps [topD];
AddIs [topD];

Goal "[| order r; top r T |] ==> (T <=_r x) = (x = T)";
by (blast_tac (claset() addIs [order_antisym]) 1);
qed "top_le_conv";
Addsimps [top_le_conv];

Goalw [semilat_def, split_conv RS eq_reflection]
"semilat(A,r,f) == order r & closed A f & \
\                (!x:A. !y:A. x <=_r x +_f y)  & \
\                (!x:A. !y:A. y <=_r x +_f y)  & \
\                (!x:A. !y:A. !z:A. x <=_r z & y <=_r z --> x +_f y <=_r z)";
by (rtac (refl RS eq_reflection) 1);
qed "semilat_Def";

Goalw [semilat_Def] "semilat(A,r,f) ==> order r";
by (Asm_simp_tac 1);
qed "semilatDorderI";
Addsimps [semilatDorderI];
AddIs [semilatDorderI];

Goalw [semilat_Def] "semilat(A,r,f) ==> closed A f";
by (Asm_simp_tac 1);
qed "semilatDclosedI";
Addsimps [semilatDclosedI];
AddIs [semilatDclosedI];

Goalw [semilat_Def] "[| semilat(A,r,f); x:A; y:A |] ==> x <=_r x +_f y";
by (Asm_simp_tac 1);
qed "semilat_ub1";

Goalw [semilat_Def] "[| semilat(A,r,f); x:A; y:A |] ==> y <=_r x +_f y";
by (Asm_simp_tac 1);
qed "semilat_ub2";

Goalw [semilat_Def]
 "[| x <=_r z; y <=_r z; semilat(A,r,f); x:A; y:A; z:A |] ==> x +_f y <=_r z";
by (Asm_simp_tac 1);
qed "semilat_lub";

Addsimps [semilat_ub1,semilat_ub2,semilat_lub];

Goalw [semilat_Def]
 "[| x:A; y:A; z:A; semilat(A,r,f) |] ==> \
\ (x +_f y <=_r z) = (x <=_r z & y <=_r z)";
by (blast_tac (claset() addIs [semilat_ub1,semilat_ub2,semilat_lub,order_trans]) 1);
qed "plus_le_conv";
Addsimps [plus_le_conv];

Goal "[| x:A; y:A; semilat(A,r,f) |] ==> (x <=_r y) = (x +_f y = y)";
by (rtac iffI 1);
 by (REPEAT(ares_tac [semilatDorderI,order_antisym,semilat_lub,order_refl,semilat_ub2] 1));
by (etac subst 1);
by (Asm_simp_tac 1);
qed "le_iff_plus_unchanged";

Goal "[| x:A; y:A; semilat(A,r,f) |] ==> (x <=_r y) = (y +_f x = y)";
by (rtac iffI 1);
 by (REPEAT(ares_tac [semilatDorderI,order_antisym,semilat_lub,order_refl,semilat_ub1] 1));
by (etac subst 1);
by (Asm_simp_tac 1);
qed "le_iff_plus_unchanged2";

(*** closed ***)

Goalw [closed_def] "[| closed A f; x:A; y:A |] ==> x +_f y : A";
by (Blast_tac 1);
qed "closedD";

Goalw [closed_def] "closed UNIV f";
by (Simp_tac 1);
qed "closed_UNIV";
AddIffs [closed_UNIV];

(*** lub ***)

Goalw [is_lub_def]
 "is_lub r x y u ==> is_ub r x y u & (!z. is_ub r x y z --> (u,z):r)";
by (assume_tac 1);
qed "is_lubD";

Goalw [is_ub_def]
 "[| (x,u) : r; (y,u) : r |] ==> is_ub r x y u";
by (Asm_simp_tac 1);
qed "is_ubI";

Goalw [is_ub_def]
 "is_ub r x y u ==> (x,u) : r & (y,u) : r";
by (assume_tac 1);
qed "is_ubD";


Goalw [is_lub_def,is_ub_def] "is_lub (r^*) x y y = ((x,y):r^*)";
by (Blast_tac 1);
qed "is_lub_bigger1";
AddIffs [is_lub_bigger1];

Goalw [is_lub_def,is_ub_def] "is_lub (r^*) x y x = ((y,x):r^*)";
by (Blast_tac 1);
qed "is_lub_bigger2";
AddIffs [is_lub_bigger2];


Goalw [is_lub_def,is_ub_def]
 "[| single_valued r; is_lub (r^*) x y u; (x',x) : r |] ==> \
\    EX v. is_lub (r^*) x' y v";
by (case_tac "(y,x) : r^*" 1);
 by (case_tac "(y,x') : r^*" 1);
  by (Blast_tac 1);
 by (blast_tac (claset() addIs [r_into_rtrancl] addEs [converse_rtranclE]
                        addDs [single_valuedD]) 1);
by (rtac exI 1);
by (rtac conjI 1);
 by (blast_tac (claset() addIs [rtrancl_into_rtrancl2]addDs [single_valuedD]) 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl,rtrancl_into_rtrancl2]
                       addEs [converse_rtranclE] addDs [single_valuedD]) 1);
qed "extend_lub";

Goal "[| single_valued r; (x,u) : r^* |] ==> (!y. (y,u) : r^* --> \
\     (EX z. is_lub (r^*) x y z))";
by (etac converse_rtrancl_induct 1);
 by (Clarify_tac 1);
 by (etac converse_rtrancl_induct 1);
  by (Blast_tac 1);
 by (blast_tac (claset() addIs [rtrancl_into_rtrancl2]) 1);
by (blast_tac (claset() addIs [extend_lub]) 1);
qed_spec_mp "single_valued_has_lubs";

Goalw [some_lub_def,is_lub_def]
 "[| acyclic r; is_lub (r^*) x y u |] ==> some_lub (r^*) x y = u";
by (rtac someI2 1);
 by (assume_tac 1);
by (blast_tac (claset() addIs [antisymD]
                       addSDs [acyclic_impl_antisym_rtrancl]) 1);
qed "some_lub_conv";

Goal
 "[| single_valued r; acyclic r; (x,u):r^*; (y,u):r^* |] ==> \
\ is_lub (r^*) x y (some_lub (r^*) x y)";
by (fast_tac
    (claset() addDs [single_valued_has_lubs]
     addss (simpset() addsimps [some_lub_conv])) 1);
qed "is_lub_some_lub";
