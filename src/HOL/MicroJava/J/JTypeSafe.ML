(*  Title:      HOL/MicroJava/J/JTypeSafe.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

Type safety proof
*)

Goalw [conf_def] "G,s\\<turnstile>Unit\\<Colon>\\<preceq>PrimT Void";
by( Simp_tac 1);
qed "conf_VoidI";

Goalw [conf_def] "G,s\\<turnstile>Bool b\\<Colon>\\<preceq>PrimT Boolean";
by( Simp_tac 1);
qed "conf_BooleanI";

Goalw [conf_def] "G,s\\<turnstile>Intg i\\<Colon>\\<preceq>PrimT Integer";
by( Simp_tac 1);
qed "conf_IntegerI";

Addsimps [conf_VoidI, conf_BooleanI, conf_IntegerI];

Addsimps [split_beta];

Goal "\\<lbrakk>h a = None; (h, l)\\<Colon>\\<preceq>(G, lT); wf_prog wf_mb G; is_class G C\\<rbrakk> \\<Longrightarrow> \
\ (h(a\\<mapsto>(C,(init_vars (fields (G,C))))), l)\\<Colon>\\<preceq>(G, lT)";
by( etac conforms_upd_obj 1);
by(  rewtac oconf_def);
by(  auto_tac (claset() addSDs [is_type_fields, map_of_SomeD], simpset()));
qed "NewC_conforms";

Goalw [cast_ok_def]
 "\\<lbrakk> wf_prog wf_mb G; G,h\\<turnstile>v\\<Colon>\\<preceq>Tb; G\\<turnstile>Tb\\<Rightarrow>? T'; cast_ok G T' h v\\<rbrakk> \
\ \\<Longrightarrow> G,h\\<turnstile>v\\<Colon>\\<preceq>T'";
by( case_tac1 "v = Null" 1);
by(  Asm_full_simp_tac 1);
by(  dtac widen_RefT 1);
by(  Clarify_tac 1);
by(  forward_tac [cast_RefT] 1);
by(  Clarify_tac 1);
by(  rtac widen.null 1);
by( case_tac1 "\\<exists>pt. T' = PrimT pt" 1);
by(  strip_tac1 1);
by(  dtac cast_PrimT2 1);
by(  etac conf_widen 1);
by(   atac 1);
by(  atac 1);
by( Asm_full_simp_tac 1);
by( dtac (non_PrimT RS iffD1) 1);
by( strip_tac1 1);
by( forward_tac [cast_RefT2] 1);
by( strip_tac1 1);
by( dtac non_npD 1);
by(  atac 1);
by( rewrite_goals_tac [obj_ty_def]);
by Auto_tac ;
by(  ALLGOALS (rtac conf_AddrI));
by     Auto_tac;
qed "Cast_conf";

Goal "\\<lbrakk> wf_prog wf_mb G; field (G,C) fn = Some (fd, ft); (h,l)\\<Colon>\\<preceq>(G,lT); \
\    x' = None \\<longrightarrow> G,h\\<turnstile>a'\\<Colon>\\<preceq> Class C; np a' x' = None \\<rbrakk> \\<Longrightarrow> \
\ G,h\\<turnstile>the (snd (the (h (the_Addr a'))) (fn, fd))\\<Colon>\\<preceq>ft";
by( dtac np_NoneD 1);
by( etac conjE 1);
by( mp_tac 1);
by( dtac non_np_objD 1);
by   Auto_tac;
by( dtac (conforms_heapD RS hconfD) 1);
by(  atac 1);
by( dtac widen_cfs_fields 1);
by(   atac 1);
by(  atac 1);
by( dtac oconf_objD 1);
by(  atac 1);
by Auto_tac;
qed "FAcc_type_sound";

Goal
 "\\<lbrakk> wf_prog wf_mb G; a = the_Addr a'; (c, fs) = the (h a); \
\   (G, lT)\\<turnstile>v\\<Colon>T'; G\\<turnstile>T'\\<preceq>ft; \
\   (G, lT)\\<turnstile>aa\\<Colon>Class C; \
\   field (G,C) fn = Some (fd, ft); h''\\<le>|h'; \
\   x' = None \\<longrightarrow> G,h'\\<turnstile>a'\\<Colon>\\<preceq> Class C; h'\\<le>|h; \
\   (h, l)\\<Colon>\\<preceq>(G, lT); G,h\\<turnstile>x\\<Colon>\\<preceq>T'; np a' x' = None\\<rbrakk> \\<Longrightarrow> \
\ h''\\<le>|h(a\\<mapsto>(c,(fs((fn,fd)\\<mapsto>x)))) \\<and>  \
\ (h(a\\<mapsto>(c,(fs((fn,fd)\\<mapsto>x)))), l)\\<Colon>\\<preceq>(G, lT) \\<and>  \
\ G,h(a\\<mapsto>(c,(fs((fn,fd)\\<mapsto>x))))\\<turnstile>x\\<Colon>\\<preceq>T'";
by( dtac np_NoneD 1);
by( etac conjE 1);
by( Asm_full_simp_tac 1);
by( dtac non_np_objD 1);
by(   atac 1);
by(  SELECT_GOAL Auto_tac 1);
by( strip_tac1 1);
by( Full_simp_tac 1);
by( EVERY [forward_tac [hext_objD] 1, atac 1]);
by( etac exE 1);
by( Asm_full_simp_tac 1);
by( strip_tac1 1);
by( rtac conjI 1);
by(  fast_tac (HOL_cs addEs [hext_trans, hext_upd_obj]) 1);
by( rtac conjI 1);
by(  fast_tac (HOL_cs addEs [conf_upd_obj RS iffD2]) 2);

by( rtac conforms_upd_obj 1);
by   Auto_tac;
by(  rtac hextI 2);
by(  Force_tac 2);
by( rtac oconf_hext 1);
by(  etac hext_upd_obj 2);
by( dtac widen_cfs_fields 1);
by(   atac 1);
by(  atac 1);
by( rtac (oconf_obj RS iffD2) 1);
by( Simp_tac 1);
by( strip_tac 1);
by( case_tac1 "(aaa, b) = (fn, fd)" 1);
by(  Asm_full_simp_tac 1);
by(  fast_tac (HOL_cs addIs [conf_widen]) 1);
by( fast_tac (HOL_cs addDs [conforms_heapD RS hconfD, oconf_objD]) 1);
qed "FAss_type_sound";

Goalw [wf_mhead_def] "\\<lbrakk> wf_prog wf_mb G; list_all2 (conf G h) pvs pTs; \
 \ list_all2 (\\<lambda>T T'. G\\<turnstile>T\\<preceq>T') pTs pTs'; wf_mhead G (mn,pTs') rT; \
\ length pTs' = length pns; nodups pns; \
\ Ball (set lvars) (split (\\<lambda>vn. is_type G)) \
\ \\<rbrakk> \\<Longrightarrow> G,h\\<turnstile>init_vars lvars(pns[\\<mapsto>]pvs)[\\<Colon>\\<preceq>]map_of lvars(pns[\\<mapsto>]pTs')";
by( Clarsimp_tac 1);
by( rtac lconf_ext_list 1);
by(    rtac (Ball_set_table RS lconf_init_vars) 1);
by(    Force_tac 1);
by(   atac 1);
by(  atac 1);
by( (etac conf_list_gext_widen THEN_ALL_NEW atac) 1);
qed "Call_lemma2";

Goalw [wf_java_prog_def]
 "\\<lbrakk> wf_java_prog G; a' \\<noteq> Null; (h, l)\\<Colon>\\<preceq>(G, lT); \
\    max_spec G C (mn,pTsa) = {((mda,rTa),pTs')}; xc\\<le>|xh; xh\\<le>|h; \
\    list_all2 (conf G h) pvs pTsa;\
\    (md, rT, pns, lvars, blk, res) = \
\              the (method (G,fst (the (h (the_Addr a')))) (mn, pTs'));\
\ \\<forall>lT. (h, init_vars lvars(pns[\\<mapsto>]pvs)(This\\<mapsto>a'))\\<Colon>\\<preceq>(G, lT) \\<longrightarrow> \
\ (G, lT)\\<turnstile>blk\\<surd> \\<longrightarrow>  h\\<le>|xi \\<and>  (xi, xl)\\<Colon>\\<preceq>(G, lT); \
\ \\<forall>lT. (xi, xl)\\<Colon>\\<preceq>(G, lT) \\<longrightarrow> (\\<forall>T. (G, lT)\\<turnstile>res\\<Colon>T \\<longrightarrow> \
\         xi\\<le>|h' \\<and> (h', xj)\\<Colon>\\<preceq>(G, lT) \\<and> (x' = None \\<longrightarrow> G,h'\\<turnstile>v\\<Colon>\\<preceq>T)); \
\ G,xh\\<turnstile>a'\\<Colon>\\<preceq> Class C \\<rbrakk> \\<Longrightarrow> \
\ xc\\<le>|h' \\<and> (h', l)\\<Colon>\\<preceq>(G, lT) \\<and>  (x' = None \\<longrightarrow> G,h'\\<turnstile>v\\<Colon>\\<preceq>rTa)";
by( dtac (insertI1 RSN (2,(equalityD2 RS subsetD))) 1);
by( dtac (max_spec2appl_meths RS appl_methsD) 1);
by( Clarify_tac 1);
by( datac non_np_objD' 2 1);
by(  strip_tac1 1);
by(  Asm_full_simp_tac 1);
by( Clarsimp_tac 1);
by( EVERY'[forward_tac [hext_objD], atac] 1);
by( Clarsimp_tac 1);
by( EVERY'[dtac Call_lemma, atac, atac] 1);
by( clarsimp_tac (claset(),simpset() addsimps [wf_java_mdecl_def])1);
by( thin_tac "method ?sig ?x = ?y" 1);
by( EVERY'[dtac spec, etac impE] 1);
by(  mp_tac 2);
by(  rtac conformsI 1);
by(   etac conforms_heapD 1);
by(  rtac lconf_ext 1);
by(   force_tac (claset() addSEs [Call_lemma2],simpset()) 1);
by(  EVERY'[etac conf_hext, etac conf_obj_AddrI, atac] 1);
by( thin_tac "?E\\<turnstile>?blk\\<surd>" 1);
by( etac conjE 1);
by( EVERY'[dtac spec, mp_tac] 1);
(*by( thin_tac "?E\\<Colon>\\<preceq>(G, pT')" 1);*)
by( EVERY'[dtac spec, mp_tac] 1);
by( thin_tac "?E\\<turnstile>res\\<Colon>?rT" 1);
by( strip_tac1 1);
by( rtac conjI 1);
by(  fast_tac (HOL_cs addIs [hext_trans]) 1);
by( rtac conjI 1);
by(  rtac impI 2);
by(  mp_tac 2);
by(  forward_tac [conf_widen] 2);
by(    atac 4);
by(   atac 2);
by(  fast_tac (HOL_cs addSEs [widen_trans]) 2);
by( etac conforms_hext 1);
by(  etac hext_trans 1);
by(  atac 1);
by( etac conforms_heapD 1);
qed "Call_type_sound";



Unify.search_bound := 40;
Unify.trace_bound  := 40;
Delsplits[split_if];
Delsimps[fun_upd_apply];(*###*)
val forward_hyp_tac = ALLGOALS (TRY o (EVERY' [dtac spec, mp_tac,
	(mp_tac ORELSE' (dtac spec THEN' mp_tac)), REPEAT o (etac conjE)]));
Goal
"wf_java_prog G \\<Longrightarrow> \
\ (G\\<turnstile>(x,(h,l)) -e  \\<succ>v  \\<rightarrow> (x', (h',l')) \\<longrightarrow> \
\     (\\<forall>lT.    (h ,l )\\<Colon>\\<preceq>(G,lT) \\<longrightarrow> (\\<forall>T . (G,lT)\\<turnstile>e  \\<Colon> T \\<longrightarrow> \
\     h\\<le>|h' \\<and> (h',l')\\<Colon>\\<preceq>(G,lT) \\<and> (x'=None \\<longrightarrow> G,h'\\<turnstile>v  \\<Colon>\\<preceq> T )))) \\<and> \
\ (G\\<turnstile>(x,(h,l)) -es[\\<succ>]vs\\<rightarrow> (x', (h',l')) \\<longrightarrow> \
\     (\\<forall>lT.    (h ,l )\\<Colon>\\<preceq>(G,lT) \\<longrightarrow> (\\<forall>Ts. (G,lT)\\<turnstile>es[\\<Colon>]Ts \\<longrightarrow> \
\     h\\<le>|h' \\<and> (h',l')\\<Colon>\\<preceq>(G,lT) \\<and> (x'=None \\<longrightarrow> list_all2 (\\<lambda>v T. G,h'\\<turnstile>v\\<Colon>\\<preceq>T) vs Ts)))) \\<and> \
\ (G\\<turnstile>(x,(h,l)) -c       \\<rightarrow> (x', (h',l')) \\<longrightarrow> \
\     (\\<forall>lT.    (h ,l )\\<Colon>\\<preceq>(G,lT) \\<longrightarrow>       (G,lT)\\<turnstile>c  \\<surd> \\<longrightarrow> \
\     h\\<le>|h' \\<and> (h',l')\\<Colon>\\<preceq>(G,lT)))";
by( rtac eval_evals_exec.induct 1);
by( rewtac c_hupd_def);

(* several simplifications, XcptE, XcptEs, XcptS, Skip *)
by( ALLGOALS Asm_full_simp_tac);
by( ALLGOALS strip_tac);
by( ALLGOALS (eresolve_tac ty_expr_ty_exprs_wt_stmt.elims 
		THEN_ALL_NEW Full_simp_tac));
by( ALLGOALS (EVERY' [REPEAT o (etac conjE), REPEAT o hyp_subst_tac]));
by( rewtac wf_java_prog_def);

(* Level 7 *)

(* 14 NewC *)
by( dtac new_AddrD 1);
by( etac disjE 1);
by(  Asm_simp_tac 2);
by( etac conjE 1);
by( Asm_simp_tac 1);
by( rtac conjI 1);
by(  fast_tac (HOL_cs addSEs [NewC_conforms]) 1);
by( rtac conf_obj_AddrI 1);
by(  rtac rtrancl_refl 2);
by( Simp_tac 1);

(* for Cast *)
by( defer_tac 1);

(* 13 Lit *)
by( etac conf_litval 1);

(* 12 BinOp *)
by forward_hyp_tac;
by forward_hyp_tac;
by( EVERY'[rtac conjI, eatac hext_trans 1] 1);
by( etac conjI 1);
by( Clarsimp_tac 1);
by( dtac eval_no_xcpt 1);
by( asm_full_simp_tac (simpset() addsplits [binop.split]) 1);

(* 11 LAcc *)
by( fast_tac (claset() addEs [conforms_localD RS lconfD]) 1);

(* 10 Nil *)
by( Simp_tac 5);

(* for FAss *)
by( EVERY'[eresolve_tac ty_expr_ty_exprs_wt_stmt.elims THEN_ALL_NEW Full_simp_tac, 
			REPEAT o (etac conjE), hyp_subst_tac] 3);

(* for if *)
by( (case_tac1 "the_Bool v" THEN_ALL_NEW Asm_full_simp_tac) 8);

by forward_hyp_tac;

(* 10+1 if *)
by(  fast_tac (HOL_cs addIs [hext_trans]) 8);
by( fast_tac (HOL_cs addIs [hext_trans]) 8);

(* 9 Expr *)
by( Fast_tac 6);

by( ALLGOALS Asm_full_simp_tac);

(* 8 Cast *)
by( EVERY'[rtac impI, dtac raise_if_NoneD, Clarsimp_tac, 
           fast_tac (claset() addEs [Cast_conf])] 8);

(* 7 LAss *)
by( asm_simp_tac (simpset() addsplits [expand_if]) 1);
by( EVERY'[eresolve_tac ty_expr_ty_exprs_wt_stmt.elims THEN_ALL_NEW Full_simp_tac] 1);
by( blast_tac (claset() addIs [conforms_upd_local, conf_widen]) 1);

(* 6 FAcc *)
by( fast_tac (claset() addSEs [FAcc_type_sound]) 1);

(* 5 While *)
by( fast_tac (claset() addIs [ty_expr_ty_exprs_wt_stmt.Cond, ty_expr_ty_exprs_wt_stmt.Comp, ty_expr_ty_exprs_wt_stmt.Skip]
		       addEs [ty_expr_ty_exprs_wt_stmt.Loop]) 5);

by forward_hyp_tac;

(* 4 Cons *)
by( fast_tac (claset() addDs [evals_no_xcpt] addIs [conf_hext,hext_trans]) 3);

(* 3 ;; *)
by( fast_tac (claset() addIs [hext_trans]) 3);

(* 2 FAss *)
by( case_tac1 "x2 = None" 1);
by(  Asm_simp_tac 2);
by(  fast_tac (claset() addIs [hext_trans]) 2);
by( Asm_full_simp_tac 1);
by( dtac eval_no_xcpt 1);
by( SELECT_GOAL (etac FAss_type_sound 1 THEN rtac refl 1 THEN ALLGOALS atac) 1);

by prune_params_tac;
(* Level 45 *)

(* 1 Call *)
by( case_tac "x" 1);
by(  Clarsimp_tac 2);
by(  dtac exec_xcpt 2);
by(  Asm_full_simp_tac 2);
by(  dtac eval_xcpt 2);
by(  Asm_full_simp_tac 2);
by(  fast_tac (HOL_cs addEs [hext_trans]) 2);
by( Clarify_tac 1);
by( dtac evals_no_xcpt 1);
by( Asm_full_simp_tac 1);
by( case_tac1 "a' = Null" 1);
by(  Asm_full_simp_tac 1);
by(  dtac exec_xcpt 1);
by(  Asm_full_simp_tac 1);
by(  dtac eval_xcpt 1);
by(  Asm_full_simp_tac 1);
by(  fast_tac (HOL_cs addEs [hext_trans]) 1);
by( (rtac (rewrite_rule[wf_java_prog_def]Call_type_sound) THEN_ALL_NEW Asm_simp_tac) 1);
qed "eval_evals_exec_type_sound";

Goal "\\<And>E s s'. \
\ \\<lbrakk> G=prg E; wf_java_prog G; G\\<turnstile>(x,s) -e\\<succ>v \\<rightarrow> (x',s'); s\\<Colon>\\<preceq>E; E\\<turnstile>e\\<Colon>T \\<rbrakk> \
\ \\<Longrightarrow> s'\\<Colon>\\<preceq>E \\<and> (x'=None \\<longrightarrow> G,heap s'\\<turnstile>v\\<Colon>\\<preceq>T)";
by( split_all_tac 1);
bd (eval_evals_exec_type_sound RS conjunct1 RS mp RS spec RS mp) 1;
by Auto_tac;
qed "eval_type_sound";

Goal "\\<And>E s s'. \
\ \\<lbrakk> G=prg E; wf_java_prog G; G\\<turnstile>(x,s) -s0\\<rightarrow> (x',s'); s\\<Colon>\\<preceq>E; E\\<turnstile>s0\\<surd> \\<rbrakk> \
\ \\<Longrightarrow> s'\\<Colon>\\<preceq>E";
by( split_all_tac 1);
bd (eval_evals_exec_type_sound RS conjunct2 RS conjunct2 RS mp RS spec RS mp) 1;
by   Auto_tac;
qed "exec_type_sound";

Goal "\\<lbrakk>G=prg E; wf_java_prog G; G\\<turnstile>(x,s) -e\\<succ>a'\\<rightarrow> Norm s'; a' \\<noteq> Null;\
\         s\\<Colon>\\<preceq>E; E\\<turnstile>e\\<Colon>Class C; method (G,C) sig \\<noteq> None\\<rbrakk> \\<Longrightarrow> \
\ method (G,fst (the (heap s' (the_Addr a')))) sig \\<noteq> None";
by( datac eval_type_sound 4 1);
by( not_None_tac 1);
by( split_all_tac 1);
by(rewtac wf_java_prog_def);
by( forward_tac [widen_methd] 1);
by(   atac 1);
by(  rtac (not_None_eq RS iffD1) 2);
by(  Fast_tac 2);
by( etac conjE 1);
by( dtac non_npD 1);
by Auto_tac;
qed "all_methods_understood";

Delsimps [split_beta];
Addsimps[fun_upd_apply];(*###*)

