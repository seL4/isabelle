(*  Title:      HOL/Lex/Auto.ML
    ID:         $Id$
    Author:     Richard Mayr & Tobias Nipkow
    Copyright   1995 TUM
*)

open Auto;

goalw Auto.thy [nexts_def] "nexts A st [] = st";
by(Simp_tac 1);
qed"nexts_Nil";

goalw Auto.thy [nexts_def] "nexts A st (x#xs) = nexts A (next A st x) xs";
by(Simp_tac 1);
qed"nexts_Cons";

Addsimps [nexts_Nil,nexts_Cons];

goalw Auto.thy [acc_prefix_def] "~acc_prefix A st []";
by(Simp_tac 1);
qed"acc_prefix_Nil";
Addsimps [acc_prefix_Nil];

goalw Auto.thy [acc_prefix_def]
 "acc_prefix A s (x#xs) = (fin A (next A s x) | acc_prefix A (next A s x) xs)";
by(simp_tac (!simpset addsimps [prefix_Cons]) 1);
by(safe_tac (!claset));
  by(Asm_full_simp_tac 1);
  by (case_tac "zs=[]" 1);
   by(hyp_subst_tac 1);
   by(Asm_full_simp_tac 1);
  by(fast_tac (!claset addSEs [Cons_neq_Nil]) 1);
 by(res_inst_tac [("x","[x]")] exI 1);
 by(asm_simp_tac (!simpset addsimps [eq_sym_conv]) 1);
by(res_inst_tac [("x","x#us")] exI 1);
by(Asm_simp_tac 1);
by (Fast_tac 1);
qed"acc_prefix_Cons";
Addsimps [acc_prefix_Cons];
