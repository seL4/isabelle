(*  Title:      ZF/Coind/MT.ML
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

open MT;

       
(* ############################################################ *)
(* The Consistency theorem                                      *)
(* ############################################################ *)

goal MT.thy 
  "!!t. [| c:Const; hastyenv(ve,te);<te,e_const(c),t>:ElabRel |] ==>         \
\       <v_const(c), t> : HasTyRel";
by (Fast_tac 1);
qed "consistency_const";


goalw  MT.thy [hastyenv_def]
  "!!t. [| x:ve_dom(ve); hastyenv(ve,te); <te,e_var(x),t>:ElabRel |] ==>     \
\  <ve_app(ve,x),t>:HasTyRel";
by (Fast_tac 1);
qed "consistency_var";


goalw MT.thy [hastyenv_def]
  "!!t. [| ve:ValEnv; x:ExVar; e:Exp; hastyenv(ve,te);       \
\          <te,e_fn(x,e),t>:ElabRel  \
\       |] ==> <v_clos(x, e, ve), t> : HasTyRel";
by (Best_tac 1);
qed "consistency_fn";

AddIs (Ty.intrs@TyEnv.intrs@Val_ValEnv.intrs);
AddDs [te_owrE,(ElabRel.dom_subset RS subsetD)];

Addsimps [ve_dom_owr, te_dom_owr, ve_app_owr1, ve_app_owr2, 
          te_app_owr1, te_app_owr2];

val clean_tac = 
  REPEAT_FIRST (fn i => 
    (eq_assume_tac i) ORELSE 
    (match_tac (Ty.intrs@TyEnv.intrs@Val_ValEnv.intrs) i) ORELSE
    (ematch_tac [te_owrE] i));

val prems = goalw MT.thy [hastyenv_def]
  "[| ve:ValEnv; x:ExVar; e:Exp; f:ExVar; cl:Val;               \
\     v_clos(x,e,ve_owr(ve,f,cl)) = cl;                         \ 
\     hastyenv(ve,te); <te,e_fix(f,x,e),t>:ElabRel |] ==>       \
\  <cl,t>:HasTyRel";
by (cut_facts_tac prems 1);
by (etac elab_fixE 1);
by Safe_tac;
by (EVERY [forward_tac [subst] 1,atac 2,rtac htr_closCI 1]);
by clean_tac;
by (rtac ve_owrI 1);
by clean_tac;
by (dtac (ElabRel.dom_subset RS subsetD) 1);
by (eres_inst_tac [("Q","te_owr(te,f,t_fun(t1,t2)):TyEnv")] 
    (SigmaD1 RS te_owrE) 1);
by (assume_tac 1);
by (rtac ElabRel.elab_fnI 1);
by clean_tac;
by (Asm_simp_tac 1);
by (stac ve_dom_owr 1);
by (assume_tac 1);
by (etac subst 1);
by (rtac v_closNE 1);
by (Asm_simp_tac 1);

by (rtac PowI 1);
by (stac ve_dom_owr 1);
by (assume_tac 1);
by (etac subst 1);
by (rtac v_closNE 1);
by (rtac subsetI 1);
by (etac RepFunE 1);
by (excluded_middle_tac "f=y" 1);
by (rtac UnI1 2);
by (rtac UnI2 1);
by Auto_tac;
qed "consistency_fix";


val prems = goal MT.thy
  " [| ve:ValEnv; e1:Exp; e2:Exp; c1:Const; c2:Const;   \
\     <ve,e1,v_const(c1)>:EvalRel;                      \
\     ALL t te.                                         \
\       hastyenv(ve,te) --> <te,e1,t>:ElabRel --> <v_const(c1),t>:HasTyRel; \
\     <ve, e2, v_const(c2)> : EvalRel;                  \
\     ALL t te.                                         \
\       hastyenv(ve,te) --> <te,e2,t>:ElabRel --> <v_const(c2),t>:HasTyRel; \
\     hastyenv(ve, te);                                 \
\     <te,e_app(e1,e2),t>:ElabRel |] ==>                \
\   <v_const(c_app(c1, c2)),t>:HasTyRel";
by (cut_facts_tac prems 1);
by (etac elab_appE 1);
by (fast_tac ((mk_htr_cs ZF_cs) addSIs [c_appI] addIs [isof_app]) 1);
qed "consistency_app1";

val prems = goal MT.thy
  " [| ve:ValEnv; vem:ValEnv; e1:Exp; e2:Exp; em:Exp; xm:ExVar; v:Val;  \
\      <ve,e1,v_clos(xm,em,vem)>:EvalRel;       \
\      ALL t te.                                \
\        hastyenv(ve,te) -->                    \
\        <te,e1,t>:ElabRel -->                  \
\        <v_clos(xm,em,vem),t>:HasTyRel;        \
\      <ve,e2,v2>:EvalRel;                      \
\      ALL t te.                                \
\        hastyenv(ve,te) -->                    \
\        <te,e2,t>:ElabRel -->                  \
\        <v2,t>:HasTyRel;                       \
\      <ve_owr(vem,xm,v2),em,v>:EvalRel;        \
\      ALL t te.                                \
\        hastyenv(ve_owr(vem,xm,v2),te) -->     \
\        <te,em,t>:ElabRel -->                  \
\        <v,t>:HasTyRel;                        \
\      hastyenv(ve,te); <te,e_app(e1,e2),t>:ElabRel |] ==>      \
\   <v,t>:HasTyRel ";
by (cut_facts_tac prems 1);
by (etac elab_appE 1);
by (dtac (spec RS spec RS mp RS mp) 1);
by (assume_tac 1);
by (assume_tac 1);
by (dtac (spec RS spec RS mp RS mp) 1);
by (assume_tac 1);
by (assume_tac 1);
by (etac htr_closE 1);
by (etac elab_fnE 1);
by (rewrite_tac Ty.con_defs);
by Safe_tac;
by (dtac (spec RS spec RS mp RS mp) 1);
by (assume_tac 3);
by (assume_tac 2);
by (rtac hastyenv_owr 1);
by (assume_tac 1);
by (assume_tac 1);
by (assume_tac 2);
by (rewrite_tac [hastyenv_def]);
by (Fast_tac 1);
qed "consistency_app2";

fun mt_cases_tac t = ((rtac t 1) THEN (TRYALL assume_tac)); 

goal MT.thy 
  "!!e. <ve,e,v>:EvalRel ==>         \
\       (ALL t te. hastyenv(ve,te) --> <te,e,t>:ElabRel --> <v,t>:HasTyRel)";
by (etac EvalRel.induct 1);
by (safe_tac ZF_cs);
by (mt_cases_tac consistency_const);
by (mt_cases_tac consistency_var);
by (mt_cases_tac consistency_fn);
by (mt_cases_tac consistency_fix);
by (mt_cases_tac consistency_app1);
by (mt_cases_tac consistency_app2);
qed "consistency";


val prems = goal MT.thy
  "[| ve:ValEnv; te:TyEnv;              \
\     isofenv(ve,te);                   \
\     <ve,e,v_const(c)>:EvalRel;        \
\     <te,e,t>:ElabRel                  \
\  |] ==>                               \
\  isof(c,t)";
by (cut_facts_tac prems 1);
by (rtac (htr_constE) 1);
by (dtac consistency 1);
by (fast_tac (claset() addSIs [basic_consistency_lem]) 1);
by (assume_tac 1);
qed "basic_consistency";




