(*  Title: 	FOL/ex/nat.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Examples for the manual "Introduction to Isabelle"

Proofs about the natural numbers

INCOMPATIBLE with nat2.ML, Nipkow's examples

To generate similar output to manual, execute these commands:
    Pretty.setmargin 72; print_depth 0;
*)

open Nat;

goal Nat.thy "Suc(k) ~= k";
by (res_inst_tac [("n","k")] induct 1);
by (resolve_tac [notI] 1);
by (eresolve_tac [Suc_neq_0] 1);
by (resolve_tac [notI] 1);
by (eresolve_tac [notE] 1);
by (eresolve_tac [Suc_inject] 1);
val Suc_n_not_n = result();


goal Nat.thy "(k+m)+n = k+(m+n)";
prths ([induct] RL [topthm()]);  (*prints all 14 next states!*)
by (resolve_tac [induct] 1);
back();
back();
back();
back();
back();
back();

goalw Nat.thy [add_def] "0+n = n";
by (resolve_tac [rec_0] 1);
val add_0 = result();

goalw Nat.thy [add_def] "Suc(m)+n = Suc(m+n)";
by (resolve_tac [rec_Suc] 1);
val add_Suc = result();

val add_ss = FOL_ss addsimps [add_0, add_Suc];

goal Nat.thy "(k+m)+n = k+(m+n)";
by (res_inst_tac [("n","k")] induct 1);
by (simp_tac add_ss 1);
by (asm_simp_tac add_ss 1);
val add_assoc = result();

goal Nat.thy "m+0 = m";
by (res_inst_tac [("n","m")] induct 1);
by (simp_tac add_ss 1);
by (asm_simp_tac add_ss 1);
val add_0_right = result();

goal Nat.thy "m+Suc(n) = Suc(m+n)";
by (res_inst_tac [("n","m")] induct 1);
by (ALLGOALS (asm_simp_tac add_ss));
val add_Suc_right = result();

val [prem] = goal Nat.thy "(!!n. f(Suc(n)) = Suc(f(n))) ==> f(i+j) = i+f(j)";
by (res_inst_tac [("n","i")] induct 1);
by (simp_tac add_ss 1);
by (asm_simp_tac (add_ss addsimps [prem]) 1);
result();
