Goal "!xs. linInfixList t xs = infixList t @ xs";
by(induct_tac "t" 1);
by(Simp_tac 1);
by(Asm_simp_tac 1);
