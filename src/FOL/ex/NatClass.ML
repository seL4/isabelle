(*  Title: 	FOL/ex/NatClass.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

This is Nat.ML trivially modified to make it work with NatClass.thy.
*)

open NatClass;

goal NatClass.thy "Suc(k) ~= (k::'a::nat)";
by (res_inst_tac [("n","k")] induct 1);
by (resolve_tac [notI] 1);
by (eresolve_tac [Suc_neq_0] 1);
by (resolve_tac [notI] 1);
by (eresolve_tac [notE] 1);
by (eresolve_tac [Suc_inject] 1);
qed "Suc_n_not_n";


goal NatClass.thy "(k+m)+n = k+(m+n)";
prths ([induct] RL [topthm()]);  (*prints all 14 next states!*)
by (resolve_tac [induct] 1);
back();
back();
back();
back();
back();
back();

goalw NatClass.thy [add_def] "0+n = n";
by (resolve_tac [rec_0] 1);
qed "add_0";

goalw NatClass.thy [add_def] "Suc(m)+n = Suc(m+n)";
by (resolve_tac [rec_Suc] 1);
qed "add_Suc";

val add_ss = FOL_ss addsimps [add_0, add_Suc];

goal NatClass.thy "(k+m)+n = k+(m+n)";
by (res_inst_tac [("n","k")] induct 1);
by (simp_tac add_ss 1);
by (asm_simp_tac add_ss 1);
qed "add_assoc";

goal NatClass.thy "m+0 = m";
by (res_inst_tac [("n","m")] induct 1);
by (simp_tac add_ss 1);
by (asm_simp_tac add_ss 1);
qed "add_0_right";

goal NatClass.thy "m+Suc(n) = Suc(m+n)";
by (res_inst_tac [("n","m")] induct 1);
by (ALLGOALS (asm_simp_tac add_ss));
qed "add_Suc_right";

val [prem] = goal NatClass.thy "(!!n. f(Suc(n)) = Suc(f(n))) ==> f(i+j) = i+f(j)";
by (res_inst_tac [("n","i")] induct 1);
by (simp_tac add_ss 1);
by (asm_simp_tac (add_ss addsimps [prem]) 1);
result();
