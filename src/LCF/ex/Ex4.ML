
val asms = goal thy "[| f(p) << p; !!q. f(q) << q ==> p << q |] ==> FIX(f)=p";
by (rewtac eq_def);
by (rtac conjI 1);
by (induct_tac "f" 1);
by (rtac minimal 1);
by (strip_tac 1);
by (rtac less_trans 1);
by (resolve_tac asms 2);
by (etac less_ap_term 1);
by (resolve_tac asms 1);
by (rtac (FIX_eq RS eq_imp_less1) 1);
qed "example";
