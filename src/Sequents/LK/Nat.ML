(*  Title:      FOL/ex/Nat.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Proofs about the natural numbers.
*)

Addsimps [Suc_neq_0];

Add_safes [Suc_inject RS L_of_imp];

Goal "|- Suc(k) ~= k";
by (res_inst_tac [("n","k")] induct 1);
by (Simp_tac 1);
by (Fast_tac 1);
qed "Suc_n_not_n";

Goalw [add_def] "|- 0+n = n";
by (rtac rec_0 1);
qed "add_0";

Goalw [add_def] "|- Suc(m)+n = Suc(m+n)";
by (rtac rec_Suc 1);
qed "add_Suc";

Addsimps [add_0, add_Suc];

Goal "|- (k+m)+n = k+(m+n)";
by (res_inst_tac [("n","k")] induct 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_assoc";

Goal "|- m+0 = m";
by (res_inst_tac [("n","m")] induct 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_0_right";

Goal "|- m+Suc(n) = Suc(m+n)";
by (res_inst_tac [("n","m")] induct 1);
by (ALLGOALS (Asm_simp_tac));
qed "add_Suc_right";

(*Example used in Reference Manual, Doc/Ref/simplifier.tex*)
val [prem] = Goal "(!!n. |- f(Suc(n)) = Suc(f(n))) ==> |- f(i+j) = i+f(j)";
by (res_inst_tac [("n","i")] induct 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsimps [prem]) 1);
result();
