(*  Title: 	HOL/ex/MT.ML
    ID:         $Id$
    Author: 	Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Based upon the article
    Robin Milner and Mads Tofte,
    Co-induction in Relational Semantics,
    Theoretical Computer Science 87 (1991), pages 209-220.

Written up as
    Jacob Frost, A Case Study of Co-induction in Isabelle/HOL
    Report 308, Computer Lab, University of Cambridge (1993).

NEEDS TO USE INDUCTIVE DEFS PACKAGE
*)

open MT;

val prems = goal MT.thy "~a:{b} ==> ~a=b";
by (cut_facts_tac prems 1);
by (rtac notI 1);
by (dtac notE 1);
by (hyp_subst_tac 1);
by (rtac singletonI 1);
by (assume_tac 1);
qed "notsingletonI";

(* ############################################################ *)
(* Inference systems                                            *)
(* ############################################################ *)

val infsys_mono_tac =
  (rewtac subset_def) THEN (safe_tac HOL_cs) THEN (rtac ballI 1) THEN
  (rtac CollectI 1) THEN (dtac CollectD 1) THEN
  REPEAT 
    ( (TRY ((etac disjE 1) THEN (rtac disjI2 2) THEN (rtac disjI1 1))) THEN
      (REPEAT (etac exE 1)) THEN (REPEAT (rtac exI 1)) THEN (fast_tac set_cs 1)
    );

val prems = goal MT.thy "P a b ==> P (fst (a,b)) (snd (a,b))";
by (simp_tac (!simpset addsimps prems) 1);
qed "infsys_p1";

val prems = goal MT.thy "!!a b. P (fst (a,b)) (snd (a,b)) ==> P a b";
by (Asm_full_simp_tac 1);
qed "infsys_p2";

val prems = goal MT.thy 
 "!!a. P a b c ==> P (fst(fst((a,b),c))) (snd(fst ((a,b),c))) (snd ((a,b),c))";
by (Asm_full_simp_tac 1);
qed "infsys_pp1";

val prems = goal MT.thy 
 "!!a. P (fst(fst((a,b),c))) (snd(fst((a,b),c))) (snd((a,b),c)) ==> P a b c";
by (Asm_full_simp_tac 1);
qed "infsys_pp2";

(* ############################################################ *)
(* Fixpoints                                                    *)
(* ############################################################ *)

(* Least fixpoints *)

val prems = goal MT.thy "[| mono(f); x:f(lfp(f)) |] ==> x:lfp(f)";
by (rtac subsetD 1);
by (rtac lfp_lemma2 1);
by (resolve_tac prems 1);
by (resolve_tac prems 1);
qed "lfp_intro2";

val prems = goal MT.thy
  " [| x:lfp(f); mono(f); !!y. y:f(lfp(f)) ==> P(y) |] ==> \
\   P(x)";
by (cut_facts_tac prems 1);
by (resolve_tac prems 1);
by (rtac subsetD 1);
by (rtac lfp_lemma3 1);
by (assume_tac 1);
by (assume_tac 1);
qed "lfp_elim2";

val prems = goal MT.thy
  " [| x:lfp(f); mono(f); !!y. y:f(lfp(f) Int {x.P(x)}) ==> P(y) |] ==> \
\   P(x)";
by (cut_facts_tac prems 1);
by (etac induct 1);
by (assume_tac 1);
by (eresolve_tac prems 1);
qed "lfp_ind2";

(* Greatest fixpoints *)

(* Note : "[| x:S; S <= f(S Un gfp(f)); mono(f) |] ==> x:gfp(f)" *)

val [cih,monoh] = goal MT.thy "[| x:f({x} Un gfp(f)); mono(f) |] ==> x:gfp(f)";
by (rtac (cih RSN (2,gfp_upperbound RS subsetD)) 1);
by (rtac (monoh RS monoD) 1);
by (rtac (UnE RS subsetI) 1);
by (assume_tac 1);
by (fast_tac (set_cs addSIs [cih]) 1);
by (rtac (monoh RS monoD RS subsetD) 1);
by (rtac Un_upper2 1);
by (etac (monoh RS gfp_lemma2 RS subsetD) 1);
qed "gfp_coind2";

val [gfph,monoh,caseh] = goal MT.thy 
  "[| x:gfp(f); mono(f); !! y. y:f(gfp(f)) ==> P(y) |] ==> P(x)";
by (rtac caseh 1);
by (rtac subsetD 1);
by (rtac gfp_lemma2 1);
by (rtac monoh 1);
by (rtac gfph 1);
qed "gfp_elim2";

(* ############################################################ *)
(* Expressions                                                  *)
(* ############################################################ *)

val e_injs = [e_const_inj, e_var_inj, e_fn_inj, e_fix_inj, e_app_inj];

val e_disjs = 
  [ e_disj_const_var, 
    e_disj_const_fn, 
    e_disj_const_fix, 
    e_disj_const_app,
    e_disj_var_fn, 
    e_disj_var_fix, 
    e_disj_var_app, 
    e_disj_fn_fix, 
    e_disj_fn_app, 
    e_disj_fix_app
  ];

val e_disj_si = e_disjs @ (e_disjs RL [not_sym]);
val e_disj_se = (e_disj_si RL [notE]);

fun e_ext_cs cs = cs addSIs e_disj_si addSEs e_disj_se addSDs e_injs;

(* ############################################################ *)
(* Values                                                      *)
(* ############################################################ *)

val v_disjs = [v_disj_const_clos];
val v_disj_si = v_disjs @ (v_disjs RL [not_sym]);
val v_disj_se = (v_disj_si RL [notE]);

val v_injs = [v_const_inj, v_clos_inj];

fun v_ext_cs cs  = cs addSIs v_disj_si addSEs v_disj_se addSDs v_injs;

(* ############################################################ *)
(* Evaluations                                                  *)
(* ############################################################ *)

(* Monotonicity of eval_fun *)

goalw MT.thy [mono_def, eval_fun_def] "mono(eval_fun)";
by infsys_mono_tac;
qed "eval_fun_mono";

(* Introduction rules *)

goalw MT.thy [eval_def, eval_rel_def] "ve |- e_const(c) ---> v_const(c)";
by (rtac lfp_intro2 1);
by (rtac eval_fun_mono 1);
by (rewtac eval_fun_def);
by (fast_tac set_cs 1);
qed "eval_const";

val prems = goalw MT.thy [eval_def, eval_rel_def] 
  "ev:ve_dom(ve) ==> ve |- e_var(ev) ---> ve_app ve ev";
by (cut_facts_tac prems 1);
by (rtac lfp_intro2 1);
by (rtac eval_fun_mono 1);
by (rewtac eval_fun_def);
by (fast_tac set_cs 1);
qed "eval_var2";

val prems = goalw MT.thy [eval_def, eval_rel_def] 
  "ve |- fn ev => e ---> v_clos(<|ev,e,ve|>)";
by (cut_facts_tac prems 1);
by (rtac lfp_intro2 1);
by (rtac eval_fun_mono 1);
by (rewtac eval_fun_def);
by (fast_tac set_cs 1);
qed "eval_fn";

val prems = goalw MT.thy [eval_def, eval_rel_def] 
  " cl = <| ev1, e, ve + {ev2 |-> v_clos(cl)} |> ==> \
\   ve |- fix ev2(ev1) = e ---> v_clos(cl)";
by (cut_facts_tac prems 1);
by (rtac lfp_intro2 1);
by (rtac eval_fun_mono 1);
by (rewtac eval_fun_def);
by (fast_tac set_cs 1);
qed "eval_fix";

val prems = goalw MT.thy [eval_def, eval_rel_def]
  " [| ve |- e1 ---> v_const(c1); ve |- e2 ---> v_const(c2) |] ==> \
\   ve |- e1 @ e2 ---> v_const(c_app c1 c2)";
by (cut_facts_tac prems 1);
by (rtac lfp_intro2 1);
by (rtac eval_fun_mono 1);
by (rewtac eval_fun_def);
by (fast_tac set_cs 1);
qed "eval_app1";

val prems = goalw MT.thy [eval_def, eval_rel_def] 
  " [|  ve |- e1 ---> v_clos(<|xm,em,vem|>); \
\       ve |- e2 ---> v2; \
\       vem + {xm |-> v2} |- em ---> v \
\   |] ==> \
\   ve |- e1 @ e2 ---> v";
by (cut_facts_tac prems 1);
by (rtac lfp_intro2 1);
by (rtac eval_fun_mono 1);
by (rewtac eval_fun_def);
by (fast_tac (set_cs addSIs [disjI2]) 1);
qed "eval_app2";

(* Strong elimination, induction on evaluations *)

val prems = goalw MT.thy [eval_def, eval_rel_def]
  " [| ve |- e ---> v; \
\      !!ve c. P(((ve,e_const(c)),v_const(c))); \
\      !!ev ve. ev:ve_dom(ve) ==> P(((ve,e_var(ev)),ve_app ve ev)); \
\      !!ev ve e. P(((ve,fn ev => e),v_clos(<|ev,e,ve|>))); \
\      !!ev1 ev2 ve cl e. \
\        cl = <| ev1, e, ve + {ev2 |-> v_clos(cl)} |> ==> \
\        P(((ve,fix ev2(ev1) = e),v_clos(cl))); \
\      !!ve c1 c2 e1 e2. \
\        [| P(((ve,e1),v_const(c1))); P(((ve,e2),v_const(c2))) |] ==> \
\        P(((ve,e1 @ e2),v_const(c_app c1 c2))); \
\      !!ve vem xm e1 e2 em v v2. \
\        [|  P(((ve,e1),v_clos(<|xm,em,vem|>))); \
\            P(((ve,e2),v2)); \
\            P(((vem + {xm |-> v2},em),v)) \
\        |] ==> \
\        P(((ve,e1 @ e2),v)) \
\   |] ==> \
\   P(((ve,e),v))";
by (resolve_tac (prems RL [lfp_ind2]) 1);
by (rtac eval_fun_mono 1);
by (rewtac eval_fun_def);
by (dtac CollectD 1);
by (safe_tac HOL_cs);
by (ALLGOALS (resolve_tac prems));
by (ALLGOALS (fast_tac set_cs));
qed "eval_ind0";

val prems = goal MT.thy 
  " [| ve |- e ---> v; \
\      !!ve c. P ve (e_const c) (v_const c); \
\      !!ev ve. ev:ve_dom(ve) ==> P ve (e_var ev) (ve_app ve ev); \
\      !!ev ve e. P ve (fn ev => e) (v_clos <|ev,e,ve|>); \
\      !!ev1 ev2 ve cl e. \
\        cl = <| ev1, e, ve + {ev2 |-> v_clos(cl)} |> ==> \
\        P ve (fix ev2(ev1) = e) (v_clos cl); \
\      !!ve c1 c2 e1 e2. \
\        [| P ve e1 (v_const c1); P ve e2 (v_const c2) |] ==> \
\        P ve (e1 @ e2) (v_const(c_app c1 c2)); \
\      !!ve vem evm e1 e2 em v v2. \
\        [|  P ve e1 (v_clos <|evm,em,vem|>); \
\            P ve e2 v2; \
\            P (vem + {evm |-> v2}) em v \
\        |] ==> P ve (e1 @ e2) v \
\   |] ==> P ve e v";
by (res_inst_tac [("P","P")] infsys_pp2 1);
by (rtac eval_ind0 1);
by (ALLGOALS (rtac infsys_pp1));
by (ALLGOALS (resolve_tac prems));
by (REPEAT ((assume_tac 1) ORELSE (dtac infsys_pp2 1)));
qed "eval_ind";

(* ############################################################ *)
(* Elaborations                                                 *)
(* ############################################################ *)

goalw MT.thy [mono_def, elab_fun_def] "mono(elab_fun)";
by infsys_mono_tac;
qed "elab_fun_mono";

(* Introduction rules *)

val prems = goalw MT.thy [elab_def, elab_rel_def] 
  "c isof ty ==> te |- e_const(c) ===> ty";
by (cut_facts_tac prems 1);
by (rtac lfp_intro2 1);
by (rtac elab_fun_mono 1);
by (rewtac elab_fun_def);
by (fast_tac set_cs 1);
qed "elab_const";

val prems = goalw MT.thy [elab_def, elab_rel_def] 
  "x:te_dom(te) ==> te |- e_var(x) ===> te_app te x";
by (cut_facts_tac prems 1);
by (rtac lfp_intro2 1);
by (rtac elab_fun_mono 1);
by (rewtac elab_fun_def);
by (fast_tac set_cs 1);
qed "elab_var";

val prems = goalw MT.thy [elab_def, elab_rel_def] 
  "te + {x |=> ty1} |- e ===> ty2 ==> te |- fn x => e ===> ty1->ty2";
by (cut_facts_tac prems 1);
by (rtac lfp_intro2 1);
by (rtac elab_fun_mono 1);
by (rewtac elab_fun_def);
by (fast_tac set_cs 1);
qed "elab_fn";

val prems = goalw MT.thy [elab_def, elab_rel_def]
  " te + {f |=> ty1->ty2} + {x |=> ty1} |- e ===> ty2 ==> \
\   te |- fix f(x) = e ===> ty1->ty2";
by (cut_facts_tac prems 1);
by (rtac lfp_intro2 1);
by (rtac elab_fun_mono 1);
by (rewtac elab_fun_def);
by (fast_tac set_cs 1);
qed "elab_fix";

val prems = goalw MT.thy [elab_def, elab_rel_def] 
  " [| te |- e1 ===> ty1->ty2; te |- e2 ===> ty1 |] ==> \
\   te |- e1 @ e2 ===> ty2";
by (cut_facts_tac prems 1);
by (rtac lfp_intro2 1);
by (rtac elab_fun_mono 1);
by (rewtac elab_fun_def);
by (fast_tac (set_cs addSIs [disjI2]) 1);
qed "elab_app";

(* Strong elimination, induction on elaborations *)

val prems = goalw MT.thy [elab_def, elab_rel_def]
  " [| te |- e ===> t; \
\      !!te c t. c isof t ==> P(((te,e_const(c)),t)); \
\      !!te x. x:te_dom(te) ==> P(((te,e_var(x)),te_app te x)); \
\      !!te x e t1 t2. \
\        [| te + {x |=> t1} |- e ===> t2; P(((te + {x |=> t1},e),t2)) |] ==> \
\        P(((te,fn x => e),t1->t2)); \
\      !!te f x e t1 t2. \
\        [| te + {f |=> t1->t2} + {x |=> t1} |- e ===> t2; \
\           P(((te + {f |=> t1->t2} + {x |=> t1},e),t2)) \
\        |] ==> \
\        P(((te,fix f(x) = e),t1->t2)); \
\      !!te e1 e2 t1 t2. \
\        [| te |- e1 ===> t1->t2; P(((te,e1),t1->t2)); \
\           te |- e2 ===> t1; P(((te,e2),t1)) \
\        |] ==> \
\        P(((te,e1 @ e2),t2)) \
\   |] ==> \
\   P(((te,e),t))";
by (resolve_tac (prems RL [lfp_ind2]) 1);
by (rtac elab_fun_mono 1);
by (rewtac elab_fun_def);
by (dtac CollectD 1);
by (safe_tac HOL_cs);
by (ALLGOALS (resolve_tac prems));
by (ALLGOALS (fast_tac set_cs));
qed "elab_ind0";

val prems = goal MT.thy
  " [| te |- e ===> t; \
\       !!te c t. c isof t ==> P te (e_const c) t; \
\      !!te x. x:te_dom(te) ==> P te (e_var x) (te_app te x); \
\      !!te x e t1 t2. \
\        [| te + {x |=> t1} |- e ===> t2; P (te + {x |=> t1}) e t2 |] ==> \
\        P te (fn x => e) (t1->t2); \
\      !!te f x e t1 t2. \
\        [| te + {f |=> t1->t2} + {x |=> t1} |- e ===> t2; \
\           P (te + {f |=> t1->t2} + {x |=> t1}) e t2 \
\        |] ==> \
\        P te (fix f(x) = e) (t1->t2); \
\      !!te e1 e2 t1 t2. \
\        [| te |- e1 ===> t1->t2; P te e1 (t1->t2); \
\           te |- e2 ===> t1; P te e2 t1 \
\        |] ==> \
\        P te (e1 @ e2) t2 \ 
\   |] ==> \
\   P te e t";
by (res_inst_tac [("P","P")] infsys_pp2 1);
by (rtac elab_ind0 1);
by (ALLGOALS (rtac infsys_pp1));
by (ALLGOALS (resolve_tac prems));
by (REPEAT ((assume_tac 1) ORELSE (dtac infsys_pp2 1)));
qed "elab_ind";

(* Weak elimination, case analysis on elaborations *)

val prems = goalw MT.thy [elab_def, elab_rel_def]
  " [| te |- e ===> t; \
\      !!te c t. c isof t ==> P(((te,e_const(c)),t)); \
\      !!te x. x:te_dom(te) ==> P(((te,e_var(x)),te_app te x)); \
\      !!te x e t1 t2. \
\        te + {x |=> t1} |- e ===> t2 ==> P(((te,fn x => e),t1->t2)); \
\      !!te f x e t1 t2. \
\        te + {f |=> t1->t2} + {x |=> t1} |- e ===> t2 ==> \
\        P(((te,fix f(x) = e),t1->t2)); \
\      !!te e1 e2 t1 t2. \
\        [| te |- e1 ===> t1->t2; te |- e2 ===> t1 |] ==> \
\        P(((te,e1 @ e2),t2)) \
\   |] ==> \
\   P(((te,e),t))";
by (resolve_tac (prems RL [lfp_elim2]) 1);
by (rtac elab_fun_mono 1);
by (rewtac elab_fun_def);
by (dtac CollectD 1);
by (safe_tac HOL_cs);
by (ALLGOALS (resolve_tac prems));
by (ALLGOALS (fast_tac set_cs));
qed "elab_elim0";

val prems = goal MT.thy
  " [| te |- e ===> t; \
\       !!te c t. c isof t ==> P te (e_const c) t; \
\      !!te x. x:te_dom(te) ==> P te (e_var x) (te_app te x); \
\      !!te x e t1 t2. \
\        te + {x |=> t1} |- e ===> t2 ==> P te (fn x => e) (t1->t2); \
\      !!te f x e t1 t2. \
\        te + {f |=> t1->t2} + {x |=> t1} |- e ===> t2 ==> \
\        P te (fix f(x) = e) (t1->t2); \
\      !!te e1 e2 t1 t2. \
\        [| te |- e1 ===> t1->t2; te |- e2 ===> t1 |] ==> \
\        P te (e1 @ e2) t2 \ 
\   |] ==> \
\   P te e t";
by (res_inst_tac [("P","P")] infsys_pp2 1);
by (rtac elab_elim0 1);
by (ALLGOALS (rtac infsys_pp1));
by (ALLGOALS (resolve_tac prems));
by (REPEAT ((assume_tac 1) ORELSE (dtac infsys_pp2 1)));
qed "elab_elim";

(* Elimination rules for each expression *)

fun elab_e_elim_tac p = 
  ( (rtac elab_elim 1) THEN 
    (resolve_tac p 1) THEN 
    (REPEAT (fast_tac (e_ext_cs HOL_cs) 1))
  );

val prems = goal MT.thy "te |- e ===> t ==> (e = e_const(c) --> c isof t)";
by (elab_e_elim_tac prems);
qed "elab_const_elim_lem";

val prems = goal MT.thy "te |- e_const(c) ===> t ==> c isof t";
by (cut_facts_tac prems 1);
by (dtac elab_const_elim_lem 1);
by (fast_tac prop_cs 1);
qed "elab_const_elim";

val prems = goal MT.thy 
  "te |- e ===> t ==> (e = e_var(x) --> t=te_app te x & x:te_dom(te))";
by (elab_e_elim_tac prems);
qed "elab_var_elim_lem";

val prems = goal MT.thy 
  "te |- e_var(ev) ===> t ==> t=te_app te ev & ev : te_dom(te)";
by (cut_facts_tac prems 1);
by (dtac elab_var_elim_lem 1);
by (fast_tac prop_cs 1);
qed "elab_var_elim";

val prems = goal MT.thy 
  " te |- e ===> t ==> \
\   ( e = fn x1 => e1 --> \
\     (? t1 t2.t=t_fun t1 t2 & te + {x1 |=> t1} |- e1 ===> t2) \
\   )";
by (elab_e_elim_tac prems);
qed "elab_fn_elim_lem";

val prems = goal MT.thy 
  " te |- fn x1 => e1 ===> t ==> \
\   (? t1 t2. t=t1->t2 & te + {x1 |=> t1} |- e1 ===> t2)";
by (cut_facts_tac prems 1);
by (dtac elab_fn_elim_lem 1);
by (fast_tac prop_cs 1);
qed "elab_fn_elim";

val prems = goal MT.thy 
  " te |- e ===> t ==> \
\   (e = fix f(x) = e1 --> \
\   (? t1 t2. t=t1->t2 & te + {f |=> t1->t2} + {x |=> t1} |- e1 ===> t2))"; 
by (elab_e_elim_tac prems);
qed "elab_fix_elim_lem";

val prems = goal MT.thy 
  " te |- fix ev1(ev2) = e1 ===> t ==> \
\   (? t1 t2. t=t1->t2 & te + {ev1 |=> t1->t2} + {ev2 |=> t1} |- e1 ===> t2)";
by (cut_facts_tac prems 1);
by (dtac elab_fix_elim_lem 1);
by (fast_tac prop_cs 1);
qed "elab_fix_elim";

val prems = goal MT.thy 
  " te |- e ===> t2 ==> \
\   (e = e1 @ e2 --> (? t1 . te |- e1 ===> t1->t2 & te |- e2 ===> t1))"; 
by (elab_e_elim_tac prems);
qed "elab_app_elim_lem";

val prems = goal MT.thy
 "te |- e1 @ e2 ===> t2 ==> (? t1 . te |- e1 ===> t1->t2 & te |- e2 ===> t1)"; 
by (cut_facts_tac prems 1);
by (dtac elab_app_elim_lem 1);
by (fast_tac prop_cs 1);
qed "elab_app_elim";

(* ############################################################ *)
(* The extended correspondence relation                       *)
(* ############################################################ *)

(* Monotonicity of hasty_fun *)

goalw MT.thy [mono_def,MT.hasty_fun_def] "mono(hasty_fun)";
by infsys_mono_tac;
bind_thm("mono_hasty_fun",  result());

(* 
  Because hasty_rel has been defined as the greatest fixpoint of hasty_fun it 
  enjoys two strong indtroduction (co-induction) rules and an elimination rule.
*)

(* First strong indtroduction (co-induction) rule for hasty_rel *)

val prems =
  goalw MT.thy [hasty_rel_def] "c isof t ==> (v_const(c),t) : hasty_rel";
by (cut_facts_tac prems 1);
by (rtac gfp_coind2 1);
by (rewtac MT.hasty_fun_def);
by (rtac CollectI 1);
by (rtac disjI1 1);
by (fast_tac HOL_cs 1);
by (rtac mono_hasty_fun 1);
qed "hasty_rel_const_coind";

(* Second strong introduction (co-induction) rule for hasty_rel *)

val prems = goalw MT.thy [hasty_rel_def]
  " [|  te |- fn ev => e ===> t; \
\       ve_dom(ve) = te_dom(te); \
\       ! ev1. \
\         ev1:ve_dom(ve) --> \
\         (ve_app ve ev1,te_app te ev1) : {(v_clos(<|ev,e,ve|>),t)} Un hasty_rel \
\   |] ==> \
\   (v_clos(<|ev,e,ve|>),t) : hasty_rel";
by (cut_facts_tac prems 1);
by (rtac gfp_coind2 1);
by (rewtac hasty_fun_def);
by (rtac CollectI 1);
by (rtac disjI2 1);
by (fast_tac HOL_cs 1);
by (rtac mono_hasty_fun 1);
qed "hasty_rel_clos_coind";

(* Elimination rule for hasty_rel *)

val prems = goalw MT.thy [hasty_rel_def]
  " [| !! c t.c isof t ==> P((v_const(c),t)); \
\      !! te ev e t ve. \
\        [| te |- fn ev => e ===> t; \
\           ve_dom(ve) = te_dom(te); \
\           !ev1.ev1:ve_dom(ve) --> (ve_app ve ev1,te_app te ev1) : hasty_rel \
\        |] ==> P((v_clos(<|ev,e,ve|>),t)); \
\      (v,t) : hasty_rel \
\   |] ==> P((v,t))";
by (cut_facts_tac prems 1);
by (etac gfp_elim2 1);
by (rtac mono_hasty_fun 1);
by (rewtac hasty_fun_def);
by (dtac CollectD 1);
by (fold_goals_tac [hasty_fun_def]);
by (safe_tac HOL_cs);
by (ALLGOALS (resolve_tac prems));
by (ALLGOALS (fast_tac set_cs));
qed "hasty_rel_elim0";

val prems = goal MT.thy 
  " [| (v,t) : hasty_rel; \
\      !! c t.c isof t ==> P (v_const c) t; \
\      !! te ev e t ve. \
\        [| te |- fn ev => e ===> t; \
\           ve_dom(ve) = te_dom(te); \
\           !ev1.ev1:ve_dom(ve) --> (ve_app ve ev1,te_app te ev1) : hasty_rel \
\        |] ==> P (v_clos <|ev,e,ve|>) t \
\   |] ==> P v t";
by (res_inst_tac [("P","P")] infsys_p2 1);
by (rtac hasty_rel_elim0 1);
by (ALLGOALS (rtac infsys_p1));
by (ALLGOALS (resolve_tac prems));
by (REPEAT ((assume_tac 1) ORELSE (dtac infsys_p2 1)));
qed "hasty_rel_elim";

(* Introduction rules for hasty *)

val prems = goalw MT.thy [hasty_def] "c isof t ==> v_const(c) hasty t";
by (resolve_tac (prems RL [hasty_rel_const_coind]) 1);
qed "hasty_const";

val prems = goalw MT.thy [hasty_def,hasty_env_def] 
  "te |- fn ev => e ===> t & ve hastyenv te ==> v_clos(<|ev,e,ve|>) hasty t";
by (cut_facts_tac prems 1);
by (rtac hasty_rel_clos_coind 1);
by (ALLGOALS (fast_tac set_cs));
qed "hasty_clos";

(* Elimination on constants for hasty *)

val prems = goalw MT.thy [hasty_def] 
  "v hasty t ==> (!c.(v = v_const(c) --> c isof t))";  
by (cut_facts_tac prems 1);
by (rtac hasty_rel_elim 1);
by (ALLGOALS (fast_tac (v_ext_cs HOL_cs)));
qed "hasty_elim_const_lem";

val prems = goal MT.thy "v_const(c) hasty t ==> c isof t";
by (cut_facts_tac (prems RL [hasty_elim_const_lem]) 1);
by (fast_tac HOL_cs 1);
qed "hasty_elim_const";

(* Elimination on closures for hasty *)

val prems = goalw MT.thy [hasty_env_def,hasty_def] 
  " v hasty t ==> \
\   ! x e ve. \
\     v=v_clos(<|x,e,ve|>) --> (? te.te |- fn x => e ===> t & ve hastyenv te)";
by (cut_facts_tac prems 1);
by (rtac hasty_rel_elim 1);
by (ALLGOALS (fast_tac (v_ext_cs HOL_cs)));
qed "hasty_elim_clos_lem";

val prems = goal MT.thy 
  "v_clos(<|ev,e,ve|>) hasty t ==> ? te.te |- fn ev => e ===>\
  \t & ve hastyenv te ";
by (cut_facts_tac (prems RL [hasty_elim_clos_lem]) 1);
by (fast_tac HOL_cs 1);
qed "hasty_elim_clos";

(* ############################################################ *)
(* The pointwise extension of hasty to environments             *)
(* ############################################################ *)

goal MT.thy
  "!!ve. [| ve hastyenv te; v hasty t |] ==> \
\        ve + {ev |-> v} hastyenv te + {ev |=> t}";
by (rewtac hasty_env_def);
by (asm_full_simp_tac (!simpset delsimps mem_simps
                                addsimps [ve_dom_owr, te_dom_owr]) 1);
by (safe_tac HOL_cs);
by (excluded_middle_tac "ev=x" 1);
by (asm_full_simp_tac (!simpset addsimps [ve_app_owr2, te_app_owr2]) 1);
by (fast_tac set_cs 1);
by (asm_simp_tac (!simpset addsimps [ve_app_owr1, te_app_owr1]) 1);
qed "hasty_env1";

(* ############################################################ *)
(* The Consistency theorem                                      *)
(* ############################################################ *)

val prems = goal MT.thy 
  "[| ve hastyenv te ; te |- e_const(c) ===> t |] ==> v_const(c) hasty t";
by (cut_facts_tac prems 1);
by (dtac elab_const_elim 1);
by (etac hasty_const 1);
qed "consistency_const";

val prems = goalw MT.thy [hasty_env_def]
  " [| ev : ve_dom(ve); ve hastyenv te ; te |- e_var(ev) ===> t |] ==> \
\   ve_app ve ev hasty t";
by (cut_facts_tac prems 1);
by (dtac elab_var_elim 1);
by (fast_tac HOL_cs 1);
qed "consistency_var";

val prems = goal MT.thy
  " [| ve hastyenv te ; te |- fn ev => e ===> t |] ==> \
\   v_clos(<| ev, e, ve |>) hasty t";
by (cut_facts_tac prems 1);
by (rtac hasty_clos 1);
by (fast_tac prop_cs 1);
qed "consistency_fn";

val prems = goalw MT.thy [hasty_env_def,hasty_def]
  " [| cl = <| ev1, e, ve + { ev2 |-> v_clos(cl) } |>; \
\      ve hastyenv te ; \
\      te |- fix ev2  ev1  = e ===> t \
\   |] ==> \
\   v_clos(cl) hasty t";
by (cut_facts_tac prems 1);
by (dtac elab_fix_elim 1);
by (safe_tac HOL_cs);
(*Do a single unfolding of cl*)
by ((forward_tac [ssubst] 1) THEN (assume_tac 2));
by (rtac hasty_rel_clos_coind 1);
by (etac elab_fn 1);
by (asm_simp_tac (!simpset addsimps [ve_dom_owr, te_dom_owr]) 1);

by (asm_simp_tac (!simpset delsimps mem_simps addsimps [ve_dom_owr]) 1);
by (safe_tac HOL_cs);
by (excluded_middle_tac "ev2=ev1a" 1);
by (asm_full_simp_tac (!simpset addsimps [ve_app_owr2, te_app_owr2]) 1);
by (fast_tac set_cs 1);

by (asm_simp_tac (!simpset delsimps mem_simps
                           addsimps [ve_app_owr1, te_app_owr1]) 1);
by (hyp_subst_tac 1);
by (etac subst 1);
by (fast_tac set_cs 1);
qed "consistency_fix";

val prems = goal MT.thy 
  " [| ! t te. ve hastyenv te  --> te |- e1 ===> t --> v_const(c1) hasty t; \
\      ! t te. ve hastyenv te  --> te |- e2 ===> t --> v_const(c2) hasty t; \
\      ve hastyenv te ; te |- e1 @ e2 ===> t \
\   |] ==> \
\   v_const(c_app c1 c2) hasty t";
by (cut_facts_tac prems 1);
by (dtac elab_app_elim 1);
by (safe_tac HOL_cs);
by (rtac hasty_const 1);
by (rtac isof_app 1);
by (rtac hasty_elim_const 1);
by (fast_tac HOL_cs 1);
by (rtac hasty_elim_const 1);
by (fast_tac HOL_cs 1);
qed "consistency_app1";

val prems = goal MT.thy 
  " [| ! t te. \
\        ve hastyenv te  --> \
\        te |- e1 ===> t --> v_clos(<|evm, em, vem|>) hasty t; \
\      ! t te. ve hastyenv te  --> te |- e2 ===> t --> v2 hasty t; \
\      ! t te. \
\        vem + { evm |-> v2 } hastyenv te  --> te |- em ===> t --> v hasty t; \
\      ve hastyenv te ; \
\      te |- e1 @ e2 ===> t \
\   |] ==> \
\   v hasty t";
by (cut_facts_tac prems 1);
by (dtac elab_app_elim 1);
by (safe_tac HOL_cs);
by ((etac allE 1) THEN (etac allE 1) THEN (etac impE 1));
by (assume_tac 1);
by (etac impE 1);
by (assume_tac 1);
by ((etac allE 1) THEN (etac allE 1) THEN (etac impE 1));
by (assume_tac 1);
by (etac impE 1);
by (assume_tac 1);
by (dtac hasty_elim_clos 1);
by (safe_tac HOL_cs);
by (dtac elab_fn_elim 1);
by (safe_tac HOL_cs);
by (dtac t_fun_inj 1);
by (safe_tac prop_cs);
by ((dtac hasty_env1 1) THEN (assume_tac 1) THEN (fast_tac HOL_cs 1));
qed "consistency_app2";

val [major] = goal MT.thy 
  "ve |- e ---> v ==> \
\  (! t te. ve hastyenv te --> te |- e ===> t --> v hasty t)";

(* Proof by induction on the structure of evaluations *)

by (rtac (major RS eval_ind) 1);
by (safe_tac HOL_cs);
by (DEPTH_SOLVE 
    (ares_tac [consistency_const, consistency_var, consistency_fn,
	       consistency_fix, consistency_app1, consistency_app2] 1));
qed "consistency";

(* ############################################################ *)
(* The Basic Consistency theorem                                *)
(* ############################################################ *)

val prems = goalw MT.thy [isof_env_def,hasty_env_def] 
  "ve isofenv te ==> ve hastyenv te";
by (cut_facts_tac prems 1);
by (safe_tac HOL_cs);
by (etac allE 1);
by (etac impE 1);
by (assume_tac 1);
by (etac exE 1);
by (etac conjE 1);
by (dtac hasty_const 1);
by (Asm_simp_tac 1);
qed "basic_consistency_lem";

val prems = goal MT.thy
  "[| ve isofenv te; ve |- e ---> v_const(c); te |- e ===> t |] ==> c isof t";
by (cut_facts_tac prems 1);
by (rtac hasty_elim_const 1);
by (dtac consistency 1);
by (fast_tac (HOL_cs addSIs [basic_consistency_lem]) 1);
qed "basic_consistency";
