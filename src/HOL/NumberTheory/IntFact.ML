(*  Title:	IntPowerFact.ML
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge

Factorial on integers.
Product of finite set.
Recursively defined set including all Integers from 2 up to a. 
*)


(*----  setprod  ----*)

Goalw [setprod_def] "setprod {} = #1";
by (Simp_tac 1);
qed "setprod_empty";
Addsimps [setprod_empty];

Goalw [setprod_def] 
      "[| finite A; a ~: A |] ==> setprod (insert a A) = a * setprod A";
by (asm_simp_tac (simpset() addsimps [zmult_left_commute,
                                      export fold_insert]) 1);
qed "setprod_insert";
Addsimps [setprod_insert];

(*---- IntFact ----*)

val [d22set_eq] = d22set.simps;
Delsimps d22set.simps;

val [prem1,prem2] =
Goal "[| !!a. P {} a; \
\        !!a. [| #1<(a::int); P (d22set (a-#1)) (a-#1) |] \
\             ==> P (d22set a) a |] \
\    ==> P (d22set u) u";
by (rtac d22set.induct 1);
by Safe_tac;
by (case_tac "#1<a" 2);
by (rtac prem2 2);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [d22set_eq,prem1])));
qed "d22set_induct";

Goal "b:(d22set a) --> #1<b";
by (res_inst_tac [("u","a")] d22set_induct 1);
by (stac d22set_eq 2);
by Auto_tac;
qed_spec_mp "d22set_g_1";

Goal "b:(d22set a) --> b<=a";
by (res_inst_tac [("u","a")] d22set_induct 1);
by (stac d22set_eq 2);
by Auto_tac;
qed_spec_mp "d22set_le";

Goal "a<b ==> b~:(d22set a)";
by (res_inst_tac [("Pa","b<=a")] swap 1);
by (rtac d22set_le 2); 
by Auto_tac;
qed "d22set_le_swap";

Goal "#1<b --> b<=a --> b:(d22set a)";
by (res_inst_tac [("x","a")] d22set.induct 1);
by Auto_tac;
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [d22set_eq])));
qed_spec_mp "d22set_mem";

Goal "finite (d22set a)";
by (res_inst_tac [("u","a")] d22set_induct 1);
by (stac d22set_eq 2);
by Auto_tac;
qed "d22set_fin";

val [zfact_eq] = zfact.simps;
Delsimps zfact.simps; 

Goal "setprod(d22set a) = zfact a";
by (res_inst_tac [("x","a")] d22set.induct 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [d22set_eq,zfact_eq]) 1);
by (stac d22set_eq 1);
by (stac zfact_eq 1);
by (case_tac "#1<a" 1);
by (asm_full_simp_tac (simpset() addsimps [d22set_eq,zfact_eq]) 2);
by (asm_full_simp_tac (simpset() addsimps [d22set_fin,d22set_le_swap]) 1);
qed "d22set_prod_zfact";

