Goal "sum n + sum n = n*(Suc n)";
by(induct_tac "n" 1);
by(Auto_tac);
