(*  Title:      ZF/Coind/Values.ML
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
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
by (ALLGOALS Fast_tac);
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
by (Fast_tac 1);
qed "ValE";

(* Nonempty sets *)

Goalw (QPair_def::QInl_def::QInr_def::Val_ValEnv.con_defs)
  "v_clos(x,e,ve) ~= 0";
by (Blast_tac 1);
qed "v_closNE";

Addsimps [v_closNE];
AddSEs [v_closNE RS notE];

Goalw (QPair_def::QInl_def::QInr_def::Val_ValEnv.con_defs)
  "c:Const ==> v_const(c) ~= 0";
by (dtac constNEE 1);
by Auto_tac;
qed "v_constNE";

Addsimps [v_constNE];

(* Proving that the empty set is not a value *)

Goal "v:Val ==> v ~= 0";
by (etac ValE 1);
by Auto_tac;
qed "ValNEE";

(* Equalities for value environments *)

Goal "[| ve:ValEnv; v ~=0 |] ==> ve_dom(ve_owr(ve,x,v)) = ve_dom(ve) Un {x}";
by (etac ValEnvE 1);
by (auto_tac (claset(),
	      simpset() addsimps [map_domain_owr]));
qed "ve_dom_owr";

Goal "ve:ValEnv \
\     ==> ve_app(ve_owr(ve,y,v),x) = (if x=y then v else ve_app(ve,x))"; 
by (etac ValEnvE 1);
by (asm_simp_tac (simpset() addsimps [map_app_owr]) 1);
qed "ve_app_owr";

Goal "ve:ValEnv ==> ve_app(ve_owr(ve,x,v),x) = v"; 
by (etac ValEnvE 1);
by (Asm_full_simp_tac 1);
by (rtac map_app_owr1 1);
qed "ve_app_owr1";

Goal "ve:ValEnv ==> x ~= y ==> ve_app(ve_owr(ve,x,v),y) = ve_app(ve,y)";
by (etac ValEnvE 1);
by (Asm_full_simp_tac 1);
by (rtac map_app_owr2 1);
by (Fast_tac 1);
qed "ve_app_owr2";

(* Introduction rules for operators on value environments *)

Goal "[| ve:ValEnv; x:ve_dom(ve) |] ==> ve_app(ve,x):Val";
by (etac ValEnvE 1);
by (hyp_subst_tac 1);
by (Asm_full_simp_tac 1);
by (rtac pmap_appI 1);
by (assume_tac 1);
by (assume_tac 1);
qed "ve_appI";

Goal "[| ve:ValEnv; x:ve_dom(ve) |] ==> x:ExVar";
by (etac ValEnvE 1);
by (hyp_subst_tac 1);
by (Asm_full_simp_tac 1);
by (rtac pmap_domainD 1);
by (assume_tac 1);
by (assume_tac 1);
qed "ve_domI";

Goalw [ve_emp_def] "ve_emp:ValEnv";
by (rtac Val_ValEnv.ve_mk_I 1);
by (rtac pmap_empI 1);
qed "ve_empI";

Goal "[|ve:ValEnv; x:ExVar; v:Val |] ==> ve_owr(ve,x,v):ValEnv";
by (etac ValEnvE 1);
by (hyp_subst_tac 1);
by (Asm_full_simp_tac 1);
by (rtac Val_ValEnv.ve_mk_I 1);
by (etac pmap_owrI 1);
by (assume_tac 1);
by (assume_tac 1);
qed "ve_owrI";



