(*  Title:      ZF/Coind/Types.ML
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

open Types;

val te_owrE = 
  TyEnv.mk_cases TyEnv.con_defs "te_owr(te,f,t):TyEnv";

goalw Types.thy TyEnv.con_defs "rank(te) < rank(te_owr(te,x,t))";
by (simp_tac rank_ss 1);
qed "rank_te_owr1";

goal Types.thy "te_rec(te_emp,c_te_emp,f_te_owr) = c_te_emp";
by (rtac (te_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (!simpset addsimps (rank_te_owr1::TyEnv.case_eqns)) 1);
qed "te_rec_emp";

goal Types.thy 
  " te_rec(te_owr(te,x,t),c_te_emp,f_te_owr) = \
\   f_te_owr(te,x,t,te_rec(te,c_te_emp,f_te_owr))";
by (rtac (te_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (rank_ss addsimps (rank_te_owr1::TyEnv.case_eqns)) 1);
qed "te_rec_owr";

goalw Types.thy [te_dom_def] "te_dom(te_emp) = 0";
by (simp_tac (!simpset addsimps [te_rec_emp]) 1);
qed "te_dom_emp";

goalw Types.thy [te_dom_def] "te_dom(te_owr(te,x,v)) = te_dom(te) Un {x}";
by (simp_tac (!simpset addsimps [te_rec_owr]) 1);
qed "te_dom_owr";

goalw Types.thy [te_app_def] "te_app(te_owr(te,x,t),x) = t";
by (simp_tac (!simpset addsimps [te_rec_owr]) 1);
qed "te_app_owr1";

goalw Types.thy [te_app_def]
  "!!x y. x ~= y ==> te_app(te_owr(te,x,t),y) = te_app(te,y)";
by (asm_simp_tac (!simpset addsimps [te_rec_owr,(not_sym RS if_not_P)]) 1);
qed "te_app_owr2";

goal Types.thy
    "!!te. [| te:TyEnv; x:ExVar; x:te_dom(te) |] ==> te_app(te,x):Ty";
by (res_inst_tac [("P","x:te_dom(te)")] impE 1);
by (assume_tac 2);
by (assume_tac 2);
by (etac TyEnv.induct 1);
by (simp_tac (!simpset addsimps [te_dom_emp]) 1);
by (rtac impI 1);
by (rtac (excluded_middle RS disjE) 1);
by (stac te_app_owr2 1);
by (assume_tac 1);
by (asm_full_simp_tac (!simpset addsimps [te_dom_owr]) 1);
by (Fast_tac 1);
by (asm_simp_tac (!simpset addsimps [te_app_owr1]) 1);
qed "te_appI";


















