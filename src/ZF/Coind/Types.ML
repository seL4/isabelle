(*  Title:      ZF/Coind/Types.ML
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

val te_owrE = TyEnv.mk_cases "te_owr(te,f,t):TyEnv";

Goal "te_app(te_owr(te,x,t),x) = t";
by (Simp_tac 1);
qed "te_app_owr1";

Goal "x \\<noteq> y ==> te_app(te_owr(te,x,t),y) = te_app(te,y)";
by Auto_tac;
qed "te_app_owr2";

Goal "[| te \\<in> TyEnv; x \\<in> ExVar; x \\<in> te_dom(te) |] ==> te_app(te,x):Ty";
by (res_inst_tac [("P","x \\<in> te_dom(te)")] impE 1);
by (assume_tac 2);
by (assume_tac 2);
by (etac TyEnv.induct 1);
by (Simp_tac 1);
by (case_tac "xa = x" 1);
by Auto_tac;
qed "te_appI";


















