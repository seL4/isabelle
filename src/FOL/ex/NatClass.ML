(*  Title:      FOL/ex/NatClass.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

This is Nat.ML trivially modified to make it work with NatClass.thy.
*)

Goal "Suc(k) ~= (k::'a::nat)";
by (res_inst_tac [("n","k")] nat.induct 1);
by (rtac notI 1);
by (etac Suc_neq_0 1);
by (rtac notI 1);
by (etac notE 1);
by (etac Suc_inject 1);
qed "Suc_n_not_n";


Goal "(k+m)+n = k+(m+n)";
prths ([nat.induct] RL [topthm()]);  (*prints all 14 next states!*)
by (rtac nat.induct 1);
back();
back();
back();
back();
back();
back();

Goalw [add_def] "0+n = n";
by (rtac rec_0 1);
qed "add_0";

Goalw [add_def] "Suc(m)+n = Suc(m+n)";
by (rtac rec_Suc 1);
qed "add_Suc";

Addsimps [add_0, add_Suc];

Goal "(k+m)+n = k+(m+n)";
by (res_inst_tac [("n","k")] nat.induct 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_assoc";

Goal "m+0 = m";
by (res_inst_tac [("n","m")] nat.induct 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_0_right";

Goal "m+Suc(n) = Suc(m+n)";
by (res_inst_tac [("n","m")] nat.induct 1);
by (ALLGOALS (Asm_simp_tac));
qed "add_Suc_right";

val [prem] = goal (the_context ()) "(!!n. f(Suc(n)) = Suc(f(n))) ==> f(i+j) = i+f(j)";
by (res_inst_tac [("n","i")] nat.induct 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [prem]) 1);
result();
