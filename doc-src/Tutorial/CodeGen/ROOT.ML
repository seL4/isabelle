use_thy"CodeGen";

use"goal1.ML";
by(induct_tac "xs" 1);
by(Simp_tac 1);
use"simpsplit.ML";
qed "exec_append";
Addsimps [exec_append];

use"goal2.ML";
by(induct_tac "e" 1);
by(ALLGOALS Asm_simp_tac);
qed "exec_comp";
