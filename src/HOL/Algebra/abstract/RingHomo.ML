(*
    Ring homomorphism
    $Id$
    Author: Clemens Ballarin, started 15 April 1997
*)

(* Ring homomorphism *)

Goalw [homo_def]
  "!! f. [| !! a b. f (a + b) = f a + f b; !! a b. f (a * b) = f a * f b; \
\           f 1 = 1 |] ==> homo f";
by Auto_tac;
qed "homoI";

Goalw [homo_def] "!! f. homo f ==> f (a + b) = f a + f b";
by (Fast_tac 1);
qed "homo_add";

Goalw [homo_def] "!! f. homo f ==> f (a * b) = f a * f b";
by (Fast_tac 1);
qed "homo_mult";

Goalw [homo_def] "!! f. homo f ==> f 1 = 1";
by (Fast_tac 1);
qed "homo_one";

Goal "!! f::('a::ring=>'b::ring). homo f ==> f 0 = 0";
by (res_inst_tac [("a", "f 0")] a_lcancel 1);
by (asm_simp_tac (simpset() addsimps [homo_add RS sym]) 1);
qed "homo_zero";

Goal
  "!! f::('a::ring=>'b::ring). homo f ==> f (-a) = - f a";
by (res_inst_tac [("a", "f a")] a_lcancel 1);
by (ftac homo_zero 1);
by (asm_simp_tac (simpset() addsimps [homo_add RS sym]) 1);
qed "homo_uminus";

Goal "!! f::('a::ring=>'b::ring). homo f ==> f (a ^ n) = f a ^ n";
by (induct_tac "n" 1);
by (dtac homo_one 1);
by (Asm_simp_tac 1);
by (dres_inst_tac [("a", "a^n"), ("b", "a")] homo_mult 1);
by (Asm_full_simp_tac 1);
qed "homo_power";

Goal
  "!! f::('a::ring=>'b::ring). \
\  homo f ==> f (setsum g {..n::nat}) = setsum (f o g) {..n}";
by (induct_tac "n" 1);
by (Asm_simp_tac 1);
by (Simp_tac 1);
by (dres_inst_tac [("a", "g (Suc n)"), ("b", "setsum g {..n}")] homo_add 1);
by (Asm_full_simp_tac 1);
qed "homo_SUM";

Addsimps [homo_add, homo_mult, homo_one, homo_zero, 
  homo_uminus, homo_power, homo_SUM];

Goal "homo (%x. x)";
by (fast_tac (claset() addSIs [homoI]) 1);
qed "id_homo";

Addsimps [id_homo];
