(*  Title:      HOL/Hoare/Examples.thy
    ID:         $Id$
    Author:     Norbert Galm
    Copyright   1995 TUM

Various arithmetic examples.
*)

open Examples;

(*** multiplication by successive addition ***)

goal thy
 "{m=0 & s=0} \
\ WHILE m ~= a DO {s = m*b} s := s+b; m := Suc(m) END\
\ {s = a*b}";
by(hoare_tac 1);
by(ALLGOALS (asm_full_simp_tac (!simpset addsimps add_ac)));
qed "multiply_by_add";


(*** Euclid's algorithm for GCD ***)

goal thy
" {0<A & 0<B & a=A & b=B}   \
\ WHILE a ~= b  \
\ DO  {0<a & 0<b & gcd A B = gcd a b} \
\      IF a<b   \
\      THEN   \
\           b:=b-a   \
\      ELSE   \
\           a:=a-b   \
\      END   \
\ END   \
\ {a = gcd A B}";

by (hoare_tac 1);

by (safe_tac HOL_cs);

by (etac less_imp_diff_positive 1);
by (etac gcd_diff_r 1);

by (cut_facts_tac [less_linear] 1);
by (cut_facts_tac [less_linear] 2);
by (rtac less_imp_diff_positive 1);
by (rtac gcd_diff_l 2);

by (dtac gcd_nnn 3);

by (ALLGOALS (fast_tac HOL_cs));

qed "Euclid_GCD";


(*** Power by interated squaring and multiplication ***)

goal thy
" {a=A & b=B}   \
\ c:=1;   \
\ WHILE b~=0   \
\ DO {A pow B = c * a pow b}   \
\      WHILE b mod 2=0   \
\      DO  {A pow B = c * a pow b}  \
\           a:=a*a;   \
\           b:=b div 2   \
\      END;   \
\      c:=c*a;   \
\      b:=b-1   \
\ END   \
\ {c = A pow B}";

by (hoare_tac 1);

by (simp_tac ((simpset_of "Arith") addsimps [pow_0]) 3);

by (safe_tac HOL_cs);

by (subgoal_tac "a*a=a pow 2" 1);
by (Asm_simp_tac 1);
by (rtac (pow_pow_reduce RS ssubst) 1);

by (subgoal_tac "(b div 2)*2=b" 1);
by (subgoal_tac "0<2" 2);
by (dres_inst_tac [("m","b")] mod_div_equality 2);

by (ALLGOALS (asm_full_simp_tac ((simpset_of "Arith") addsimps [pow_0,pow_Suc,mult_assoc])));

by (subgoal_tac "b~=0" 1);
by (res_inst_tac [("n","b")] natE 1);
by (res_inst_tac [("Q","b mod 2 ~= 0")] not_imp_swap 3);
by (assume_tac 4);

by (ALLGOALS (asm_full_simp_tac ((simpset_of "Arith") addsimps [pow_0,pow_Suc,mult_assoc])));
by (rtac mod_less 1);
by (Simp_tac 1);

qed "power_by_mult";

(*** factorial ***)

goal thy
" {a=A}   \
\ b:=1;   \
\ WHILE a~=0    \
\ DO  {fac A = b*fac a} \
\      b:=b*a;   \
\      a:=a-1   \
\ END   \
\ {b = fac A}";

by (hoare_tac 1);

by (safe_tac HOL_cs);

by (res_inst_tac [("n","a")] natE 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [mult_assoc])));
by (fast_tac HOL_cs 1);

qed"factorial";
