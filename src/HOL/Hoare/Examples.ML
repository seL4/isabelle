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
by (hoare_tac 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps add_ac)));
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
(*Now prove the verification conditions*)
by Safe_tac;
by (etac less_imp_diff_positive 1);
by (asm_simp_tac (simpset() addsimps [less_imp_le, gcd_diff_r]) 1);
by (asm_full_simp_tac (simpset() addsimps [not_less_iff_le, gcd_diff_l]) 2);
by (etac gcd_nnn 2);
by (full_simp_tac (simpset() addsimps [not_less_iff_le, le_eq_less_or_eq]) 1);
by (blast_tac (claset() addIs [less_imp_diff_positive]) 1);
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

by (simp_tac ((simpset_of Arith.thy) addsimps [pow_0]) 3);

by (subgoal_tac "a*a=a pow 2" 1);
by (Asm_simp_tac 1);
by (stac pow_pow_reduce 1);

by (subgoal_tac "(b div 2)*2=b" 1);
by (subgoal_tac "0<2" 2);
by (dres_inst_tac [("m","b")] mod_div_equality 2);

by (ALLGOALS(asm_full_simp_tac(simpset() addsimps[pow_0,pow_Suc,mult_assoc])));

by (res_inst_tac [("n","b")] natE 1);
by (hyp_subst_tac 1);
by (asm_full_simp_tac (simpset() addsimps [mod_less]) 1);
by (asm_simp_tac (simpset() addsimps [pow_Suc]) 1);

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
by Safe_tac;
by (res_inst_tac [("n","a")] natE 1);
by (ALLGOALS
    (asm_simp_tac
     (simpset() addsimps [add_mult_distrib,add_mult_distrib2,mult_assoc])));
by (Fast_tac 1);

qed"factorial";
