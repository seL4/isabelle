open I;

Unify.trace_bound := 45;
Unify.search_bound := 50;

goal thy
  "! a m s s' t n.  \
\    (new_tv m a & new_tv m s) --> I e a m s = Ok(s',t,n) -->   \
\    ( ? r. W e ($ s a) m = Ok(r, $ s' t, n) & s' = ($ r o s) )";
by (expr.induct_tac "e" 1);

(* case Var n *)
by (simp_tac (!simpset addsimps [app_subst_list]
    setloop (split_tac [expand_if])) 1);
by (fast_tac (HOL_cs addss !simpset) 1);

(* case Abs e *)
by (asm_full_simp_tac (!simpset setloop (split_tac [expand_bind])) 1);
by (strip_tac 1);
by (rtac conjI 1);

by (strip_tac 1);
by (REPEAT (etac allE 1));
by (etac impE 1);
by (fast_tac (HOL_cs addss (!simpset addsimps [new_tv_subst])) 2);
by (fast_tac (HOL_cs addIs [new_tv_Suc_list RS mp,new_tv_subst_le,
    less_imp_le,lessI]) 1); 

by (strip_tac 1);
by (REPEAT (etac allE 1));
by (etac impE 1);
by (fast_tac (HOL_cs addss (!simpset addsimps [new_tv_subst])) 2);
by (fast_tac (HOL_cs addIs [new_tv_Suc_list RS mp,new_tv_subst_le,
    less_imp_le,lessI]) 1); 

(* case App e1 e2 *)
by (simp_tac (!simpset setloop (split_tac [expand_bind])) 1);
by (strip_tac 1);
by (rename_tac "s1' t1 n1 s2' t2 n2 sa" 1);
by (rtac conjI 1);
by (fast_tac (HOL_cs addss !simpset) 1);

by (strip_tac 1);
by (rename_tac "s1 t1' n1'" 1);
by (eres_inst_tac [("x","a")] allE 1);
by (eres_inst_tac [("x","m")] allE 1);
by (eres_inst_tac [("x","s")] allE 1);
by (eres_inst_tac [("x","s1'")] allE 1);
by (eres_inst_tac [("x","t1")] allE 1);
by (eres_inst_tac [("x","n1")] allE 1);
by (eres_inst_tac [("x","a")] allE 1);
by (eres_inst_tac [("x","n1")] allE 1);
by (eres_inst_tac [("x","s1'")] allE 1);
by (eres_inst_tac [("x","s2'")] allE 1);
by (eres_inst_tac [("x","t2")] allE 1);
by (eres_inst_tac [("x","n2")] allE 1);

by (rtac conjI 1);
by (strip_tac 1);
by (mp_tac 1);
by (mp_tac 1);
by (etac exE 1);
by (etac conjE 1);
by (etac impE 1);
by ((forward_tac [new_tv_subst_tel] 1) THEN (atac 1)); 
by ((dres_inst_tac [("xc","$ s a")] new_tv_W 1) THEN (atac 1));
by (fast_tac (HOL_cs addDs [sym RS W_var_geD,new_tv_subst_le,new_tv_list_le] 
    addss !simpset) 1);
by (fast_tac (HOL_cs addss (!simpset addsimps [subst_comp_tel])) 1);

by (strip_tac 1);
by (rename_tac "s2 t2' n2'" 1);
by (rtac conjI 1);
by (strip_tac 1);
by (mp_tac 1);
by (mp_tac 1);
by (etac exE 1);
by (etac conjE 1);
by (etac impE 1);
by ((forward_tac [new_tv_subst_tel] 1) THEN (atac 1)); 
by ((dres_inst_tac [("xc","$ s a")] new_tv_W 1) THEN (atac 1));
by (fast_tac (HOL_cs addDs [sym RS W_var_geD,new_tv_subst_le,new_tv_list_le] 
    addss !simpset) 1);
by (fast_tac (HOL_cs addss (!simpset addsimps [subst_comp_tel,subst_comp_te])) 1);

by (strip_tac 1);
by (mp_tac 1);
by (mp_tac 1);
by (etac exE 1);
by (etac conjE 1);
by (etac impE 1);
by ((forward_tac [new_tv_subst_tel] 1) THEN (atac 1)); 
by ((dres_inst_tac [("xc","$ s a")] new_tv_W 1) THEN (atac 1));
by (fast_tac (HOL_cs addDs [sym RS W_var_geD,new_tv_subst_le,new_tv_list_le] 
    addss !simpset) 1);

by (mp_tac 1);
by (REPEAT (eresolve_tac [exE,conjE] 1));
by (REPEAT 
    ((asm_full_simp_tac (!simpset addsimps [subst_comp_tel,subst_comp_te]) 1) THEN
     (REPEAT (etac conjE 1)) THEN (hyp_subst_tac 1) ));
by (rtac exI 1);
by (safe_tac HOL_cs);
by (fast_tac HOL_cs 1);
by (Simp_tac 2);

by (subgoal_tac "new_tv n2 s & new_tv n2 r & new_tv n2 ra" 1);
by (asm_full_simp_tac (!simpset addsimps [new_tv_subst]) 1);
by ((forward_tac [new_tv_subst_tel] 1) THEN (atac 1));
by ((dres_inst_tac [("xc","$ s a")] new_tv_W 1) THEN (atac 1));
by (safe_tac HOL_cs);
by (fast_tac (HOL_cs addDs [sym RS W_var_geD,new_tv_subst_le,new_tv_list_le] 
    addss !simpset) 1);
by (fast_tac (HOL_cs addDs [sym RS W_var_geD,new_tv_subst_le,new_tv_list_le] 
    addss !simpset) 1);
by (dres_inst_tac [("e","expr1")] (sym RS W_var_geD) 1);
by ((dtac new_tv_subst_tel 1) THEN (atac 1));
by ((dres_inst_tac [("ts","$ s a")] new_tv_list_le 1) THEN (atac 1));
by ((dtac new_tv_subst_tel 1) THEN (atac 1));
by (fast_tac (HOL_cs addDs [new_tv_W] addss 
    (!simpset addsimps [subst_comp_tel])) 1);

qed "I_correct_wrt_W";
