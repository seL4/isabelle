(*  Title:      ZF/Update.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Function updates: like theory Map, but for ordinary functions
*)

open Update;

Goal "f(x:=y) ` z = if(z=x, y, f`z)";
by (simp_tac (simpset() addsimps [update_def]) 1);
by (case_tac "z : domain(f)" 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [apply_0]) 1);
qed "update_apply";
Addsimps [update_apply];

Goalw [update_def] "[| f`x = y;  f: Pi(A,B);  x: A |] ==> f(x:=y) = f";
by (asm_simp_tac (simpset() addsimps [domain_of_fun, cons_absorb]) 1);
by (rtac fun_extension 1);
by (best_tac (claset() addIs [apply_type, if_type, lam_type]) 1);
by (assume_tac 1);
by (Asm_simp_tac 1);
qed "update_idem";


(* [| f: Pi(A, B); x:A |] ==> f(x := f`x) = f *)
Addsimps [refl RS update_idem];

Goalw [update_def] "domain(f(x:=y)) = cons(x, domain(f))";
by (Asm_simp_tac 1);
qed "domain_update";
Addsimps [domain_update];

