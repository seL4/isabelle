(*  Title:      ZF/Coind/MT.ML
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

(* ############################################################ *)
(* The Consistency theorem                                      *)
(* ############################################################ *)

Goal "[| c \\<in> Const; hastyenv(ve,te);<te,e_const(c),t>:ElabRel |] ==>         \
\       <v_const(c), t> \\<in> HasTyRel";
by (Fast_tac 1);
qed "consistency_const";


Goalw [hastyenv_def]
  "[| x \\<in> ve_dom(ve); hastyenv(ve,te); <te,e_var(x),t>:ElabRel |] ==>     \
\  <ve_app(ve,x),t>:HasTyRel";
by (Fast_tac 1);
qed "consistency_var";


Goalw [hastyenv_def]
  "[| ve \\<in> ValEnv; x \\<in> ExVar; e \\<in> Exp; hastyenv(ve,te);       \
\          <te,e_fn(x,e),t>:ElabRel  \
\       |] ==> <v_clos(x, e, ve), t> \\<in> HasTyRel";
by (Blast_tac 1);
qed "consistency_fn";

AddDs [te_owrE, ElabRel.dom_subset RS subsetD];

Addsimps [ve_dom_owr, ve_app_owr1, ve_app_owr2, 
          te_app_owr1, te_app_owr2];

val clean_tac = 
  REPEAT_FIRST (fn i => 
    (eq_assume_tac i) ORELSE 
    (match_tac (Ty.intrs@TyEnv.intrs@Val_ValEnv.intrs) i) ORELSE
    (ematch_tac [te_owrE] i));

Goalw [hastyenv_def]
  "[| ve \\<in> ValEnv; x \\<in> ExVar; e \\<in> Exp; f \\<in> ExVar; cl \\<in> Val;               \
\     v_clos(x,e,ve_owr(ve,f,cl)) = cl;                         \ 
\     hastyenv(ve,te); <te,e_fix(f,x,e),t>:ElabRel |] ==>       \
\  <cl,t>:HasTyRel";
by (etac elab_fixE 1);
by Safe_tac;
by (EVERY [ftac subst 1,atac 2,rtac htr_closCI 1]);
by clean_tac;
by (rtac ve_owrI 1);
by clean_tac;
by (dtac (ElabRel.dom_subset RS subsetD) 1);
by (eres_inst_tac [("Q","te_owr(te,f,t_fun(t1,t2)):TyEnv")] 
    (SigmaD1 RS te_owrE) 1);
by (assume_tac 1);
by (rtac ElabRel.fnI 1);
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
by (case_tac "f=y" 1);
by Auto_tac;
qed "consistency_fix";


Goal "[| ve \\<in> ValEnv; e1 \\<in> Exp; e2 \\<in> Exp; c1 \\<in> Const; c2 \\<in> Const;   \
\     <ve,e1,v_const(c1)>:EvalRel;                      \
\     \\<forall>t te.                                         \
\       hastyenv(ve,te) --> <te,e1,t>:ElabRel --> <v_const(c1),t>:HasTyRel; \
\     <ve, e2, v_const(c2)> \\<in> EvalRel;                  \
\     \\<forall>t te.                                         \
\       hastyenv(ve,te) --> <te,e2,t>:ElabRel --> <v_const(c2),t>:HasTyRel; \
\     hastyenv(ve, te);                                 \
\     <te,e_app(e1,e2),t>:ElabRel |] ==>                \
\   <v_const(c_app(c1, c2)),t>:HasTyRel";
by (etac elab_appE 1);
by (fast_tac ((mk_htr_cs ZF_cs) addSIs [c_appI] addIs [isof_app]) 1);
qed "consistency_app1";

Goal "[| ve \\<in> ValEnv; vem \\<in> ValEnv; e1 \\<in> Exp; e2 \\<in> Exp; em \\<in> Exp; xm \\<in> ExVar; v \\<in> Val;  \
\        <ve,e1,v_clos(xm,em,vem)>:EvalRel;       \
\        \\<forall>t te.                                \
\          hastyenv(ve,te) -->                    \
\          <te,e1,t>:ElabRel -->                  \
\          <v_clos(xm,em,vem),t>:HasTyRel;        \
\        <ve,e2,v2>:EvalRel;                      \
\        \\<forall>t te.                                \
\          hastyenv(ve,te) -->                    \
\          <te,e2,t>:ElabRel -->                  \
\          <v2,t>:HasTyRel;                       \
\        <ve_owr(vem,xm,v2),em,v>:EvalRel;        \
\        \\<forall>t te.                                \
\          hastyenv(ve_owr(vem,xm,v2),te) -->     \
\          <te,em,t>:ElabRel -->                  \
\          <v,t>:HasTyRel;                        \
\        hastyenv(ve,te); <te,e_app(e1,e2),t>:ElabRel |] ==>      \
\     <v,t>:HasTyRel ";
by (etac elab_appE 1);
by (dtac (spec RS spec RS mp RS mp) 1);
by (assume_tac 1);
by (assume_tac 1);
by (dtac (spec RS spec RS mp RS mp) 1);
by (assume_tac 1);
by (assume_tac 1);
by (etac htr_closE 1);
by (etac elab_fnE 1);
by (Full_simp_tac 1);
by (Clarify_tac 1);
by (dtac (spec RS spec RS mp RS mp) 1);
by (assume_tac 3);
by (assume_tac 2);
by (rtac hastyenv_owr 1);
by (assume_tac 1);
by (assume_tac 1);
by (assume_tac 2);
by (asm_simp_tac (simpset() addsimps [hastyenv_def]) 1);
by (Fast_tac 1);
qed "consistency_app2";

Goal "<ve,e,v>:EvalRel ==>         \
\       (\\<forall>t te. hastyenv(ve,te) --> <te,e,t>:ElabRel --> <v,t>:HasTyRel)";
by (etac EvalRel.induct 1);
by (blast_tac (claset() addIs [consistency_app2]) 6);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [consistency_const, consistency_var, consistency_fn, consistency_fix, consistency_app1])));
qed "consistency";


Goal "[| ve \\<in> ValEnv; te \\<in> TyEnv;              \
\        isofenv(ve,te);                   \
\        <ve,e,v_const(c)>:EvalRel;        \
\        <te,e,t>:ElabRel                  \
\     |] ==> isof(c,t)";
by (rtac htr_constE 1);
by (dtac consistency 1);
by (blast_tac (claset() addSIs [basic_consistency_lem]) 1);
by (assume_tac 1);
qed "basic_consistency";
