(*  Title: 	ZF/Coind/Values.ML
    ID:         $Id$
    Author: 	Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

open Values;

(* Elimination rules *)

val prems = goalw Values.thy (Part_def::(tl (tl Val_ValEnv.defs)))
  "[| ve:ValEnv; !!m.[| ve=ve_mk(m); m:PMap(ExVar,Val) |] ==> Q |] ==> Q";
by (cut_facts_tac prems 1);
by (etac CollectE 1);
by (etac exE 1);
by (etac Val_ValEnv.elim 1);
by (eresolve_tac prems 3);
by (rewrite_tac Val_ValEnv.con_defs);
by (ALLGOALS (fast_tac qsum_cs));
qed "ValEnvE";

val prems = goalw Values.thy (Part_def::[hd (tl Val_ValEnv.defs)])
  "[| v:Val; \
\     !!c. [| v = v_const(c); c:Const |] ==> Q;\
\     !!e ve x. \
\       [| v = v_clos(x,e,ve); x:ExVar; e:Exp; ve:ValEnv |] ==> Q \
\  |] ==> \
\  Q";
by (cut_facts_tac prems 1);
by (etac CollectE 1);
by (etac exE 1);
by (etac Val_ValEnv.elim 1);
by (eresolve_tac prems 1);
by (assume_tac 1);
by (eresolve_tac prems 1);
by (assume_tac 1);
by (assume_tac 1);
by (assume_tac 1);
by (rewrite_tac Val_ValEnv.con_defs);
by (fast_tac qsum_cs 1);
qed "ValE";

(* Nonempty sets *)

val prems = goal Values.thy "A ~= 0 ==> EX a.a:A";
by (cut_facts_tac prems 1);
by (rtac (foundation RS disjE) 1);
by (fast_tac ZF_cs 1);
by (fast_tac ZF_cs 1);
qed "set_notemptyE";

goalw Values.thy (sum_def::QPair_def::QInl_def::QInr_def::Val_ValEnv.con_defs)
  "v_clos(x,e,ve) ~= 0";
by (rtac not_emptyI 1);
by (rtac UnI2 1);
by (rtac SigmaI 1);
by (rtac singletonI 1);
by (rtac UnI1 1);
by (fast_tac ZF_cs 1);
qed "v_closNE";

goalw Values.thy (sum_def::QPair_def::QInl_def::QInr_def::Val_ValEnv.con_defs)
  "!!c.c:Const ==> v_const(c) ~= 0";
by (dtac constNEE 1);
by (etac not_emptyE 1);
by (rtac not_emptyI 1);
by (rtac UnI2 1);
by (rtac SigmaI 1);
by (rtac singletonI 1);
by (rtac UnI2 1);
by (rtac SigmaI 1);
by (rtac singletonI 1);
by (assume_tac 1);
qed "v_constNE";

(* Proving that the empty set is not a value *)

goal Values.thy "!!v.v:Val ==> v ~= 0";
by (etac ValE 1);
by (ALLGOALS hyp_subst_tac);
by (etac v_constNE 1);
by (rtac v_closNE 1);
qed "ValNEE";

(* Equalities for value environments *)

val prems = goalw Values.thy [ve_dom_def,ve_owr_def]
  "[| ve:ValEnv; v ~=0 |] ==> ve_dom(ve_owr(ve,x,v)) = ve_dom(ve) Un {x}";
by (cut_facts_tac prems 1);
by (etac ValEnvE 1);
by (asm_full_simp_tac (ZF_ss addsimps Val_ValEnv.case_eqns) 1);
by (rtac (map_domain_owr RS ssubst) 1);
by (assume_tac 1);
by (rtac Un_commute 1);
qed "ve_dom_owr";

goalw Values.thy [ve_app_def,ve_owr_def]
"!!ve. ve:ValEnv ==> ve_app(ve_owr(ve,x,v),x) = v"; 
by (etac ValEnvE 1);
by (asm_full_simp_tac (ZF_ss addsimps Val_ValEnv.case_eqns) 1);
by (rtac map_app_owr1 1);
qed "ve_app_owr1";

goalw Values.thy [ve_app_def,ve_owr_def]
 "!!ve.ve:ValEnv ==> x ~= y ==> ve_app(ve_owr(ve,x,v),y) = ve_app(ve,y)";
by (etac ValEnvE 1);
by (asm_full_simp_tac (ZF_ss addsimps Val_ValEnv.case_eqns) 1);
by (rtac map_app_owr2 1);
by (fast_tac ZF_cs 1);
qed "ve_app_owr2";

(* Introduction rules for operators on value environments *)

goalw Values.thy [ve_app_def,ve_owr_def,ve_dom_def]
  "!!ve.[| ve:ValEnv; x:ve_dom(ve) |] ==> ve_app(ve,x):Val";
by (etac ValEnvE 1);
by (hyp_subst_tac 1);
by (asm_full_simp_tac (ZF_ss addsimps Val_ValEnv.case_eqns) 1);
by (rtac pmap_appI 1);
by (assume_tac 1);
by (assume_tac 1);
qed "ve_appI";

goalw Values.thy [ve_dom_def]
  "!!ve.[| ve:ValEnv; x:ve_dom(ve) |] ==> x:ExVar";
by (etac ValEnvE 1);
by (hyp_subst_tac 1);
by (asm_full_simp_tac (ZF_ss addsimps Val_ValEnv.case_eqns) 1);
by (rtac pmap_domainD 1);
by (assume_tac 1);
by (assume_tac 1);
qed "ve_domI";

goalw Values.thy [ve_emp_def] "ve_emp:ValEnv";
by (rtac Val_ValEnv.ve_mk_I 1);
by (rtac pmap_empI 1);
qed "ve_empI";

goalw Values.thy [ve_owr_def] 
  "!!ve.[|ve:ValEnv; x:ExVar; v:Val |] ==> ve_owr(ve,x,v):ValEnv";
by (etac ValEnvE 1);
by (hyp_subst_tac 1);
by (asm_full_simp_tac (ZF_ss addsimps Val_ValEnv.case_eqns) 1);
by (rtac Val_ValEnv.ve_mk_I 1);
by (etac pmap_owrI 1);
by (assume_tac 1);
by (assume_tac 1);
qed "ve_owrI";



