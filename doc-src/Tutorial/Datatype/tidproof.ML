Goal "subst  Var t  = (t ::('a,'b)term)  & \
\     substs Var ts = (ts::('a,'b)term list)";
by(induct_tac "t ts" 1);
by(Auto_tac);
