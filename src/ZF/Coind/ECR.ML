(*  Title:      ZF/Coind/ECR.ML
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

open Dynamic ECR;

(* Specialised co-induction rule *)

goal ECR.thy
 "!!x.[| x:ExVar; e:Exp; t:Ty; ve:ValEnv; te:TyEnv; \
\    <te, e_fn(x, e), t>:ElabRel; ve_dom(ve) = te_dom(te); \
\    {<ve_app(ve,y),te_app(te,y)>.y:ve_dom(ve)}: \
\    Pow({<v_clos(x,e,ve),t>} Un HasTyRel) |] ==>  \
\ <v_clos(x, e, ve),t>:HasTyRel";
by (rtac HasTyRel.coinduct 1);
by (rtac singletonI 1);
by (fast_tac (ZF_cs addIs Val_ValEnv.intrs) 1);
by (rtac disjI2 1);
by (etac singletonE 1); 
by (REPEAT_FIRST (resolve_tac [conjI,exI]));
by (REPEAT (atac 1));
qed "htr_closCI";

(* Specialised elimination rules *)

val htr_constE = 
  (HasTyRel.mk_cases Val_ValEnv.con_defs "<v_const(c),t>:HasTyRel");

val htr_closE =
  (HasTyRel.mk_cases Val_ValEnv.con_defs "<v_clos(x,e,ve),t>:HasTyRel");

(* Classical reasoning sets *)

fun mk_htr_cs cs =
  let open HasTyRel in 
    ( cs 
      addSIs [htr_constI] 
      addSEs [htr_constE]
      addIs [htr_closI,htr_closCI]
      addEs [htr_closE])
  end;

val htr_cs = mk_htr_cs(static_cs);

(* Properties of the pointwise extension to environments *)

goalw ECR.thy [hastyenv_def]
  "!!ve.[| ve:ValEnv; te:TyEnv; hastyenv(ve,te); <v,t>:HasTyRel |] ==> \
\   hastyenv(ve_owr(ve,x,v),te_owr(te,x,t))";
by (safe_tac ZF_cs);
by (rtac (ve_dom_owr RS ssubst) 1);
by (assume_tac 1);
by (etac (HasTyRel.dom_subset RS subsetD RS SigmaD1 RS ValNEE) 1);
by (rtac (te_dom_owr RS ssubst) 1);
by (asm_simp_tac ZF_ss 1);
by (rtac (excluded_middle RS disjE) 1);
by (rtac (ve_app_owr2 RS ssubst) 1);
by (assume_tac 1);
by (assume_tac 1);
by (rtac (te_app_owr2 RS ssubst) 1);
by (assume_tac 1);
by (dtac (ve_dom_owr RS subst) 1);
by (etac (HasTyRel.dom_subset RS subsetD RS SigmaD1 RS ValNEE) 1);
by ((fast_tac ZF_cs 1) THEN (fast_tac ZF_cs 1));
by (asm_simp_tac (ZF_ss addsimps [ve_app_owr1,te_app_owr1]) 1);
qed "hastyenv_owr";

goalw ECR.thy  [isofenv_def,hastyenv_def]
  "!!ve.[| ve:ValEnv; te:TyEnv; isofenv(ve,te) |] ==> hastyenv(ve,te)";
by (safe_tac ZF_cs);
by (dtac bspec 1);
by (assume_tac 1);
by (safe_tac ZF_cs);
by (dtac HasTyRel.htr_constI 1);
by (assume_tac 2);
by (etac te_appI 1);
by (etac ve_domI 1);
by (ALLGOALS (asm_full_simp_tac ZF_ss));
qed "basic_consistency_lem";



