(* Title:     HOL/MiniML/W.ML
   ID:        $Id$
   Author:    Dieter Nazareth and Tobias Nipkow
   Copyright  1995 TU Muenchen

Correctness and completeness of type inference algorithm W
*)

open W;

Addsimps [Suc_le_lessD];
Delsimps (ex_simps @ all_simps);

(* correctness of W with respect to has_type *)
goal W.thy
        "!a s t m n . Ok (s,t,m) = W e a n --> $s a |- e :: t";
by (expr.induct_tac "e" 1);
(* case Var n *)
by (asm_simp_tac (!simpset setloop (split_tac [expand_if])) 1);
(* case Abs e *)
by (asm_full_simp_tac (!simpset addsimps [app_subst_list]
                        setloop (split_tac [expand_bind])) 1);
by (strip_tac 1);
by (eres_inst_tac [("x","TVar(n) # a")] allE 1);
by ( fast_tac (HOL_cs addss (!simpset addsimps [eq_sym_conv])) 1);
(* case App e1 e2 *)
by (simp_tac (!simpset setloop (split_tac [expand_bind])) 1);
by (strip_tac 1);
by ( rename_tac "sa ta na sb tb nb sc" 1);
by (res_inst_tac [("t2.0","$ sc tb")] has_type.AppI 1);
by (res_inst_tac [("s1","sc")] (app_subst_TVar RS subst) 1);
by (rtac (app_subst_Fun RS subst) 1);
by (res_inst_tac [("t","$sc(tb -> (TVar nb))"),("s","$sc($sb ta)")] subst 1);
by (Asm_full_simp_tac 1);
by (simp_tac (HOL_ss addsimps [subst_comp_tel RS sym]) 1);
by ( (rtac has_type_cl_sub 1) THEN (rtac has_type_cl_sub 1));
by (asm_full_simp_tac (!simpset addsimps [eq_sym_conv]) 1);
by (asm_full_simp_tac (!simpset addsimps [subst_comp_tel RS sym,o_def,has_type_cl_sub,eq_sym_conv]) 1);
qed_spec_mp "W_correct";

val has_type_casesE = map(has_type.mk_cases expr.simps)
        [" s |- Var n :: t"," s |- Abs e :: t","s |- App e1 e2 ::t"];


(* the resulting type variable is always greater or equal than the given one *)
goal thy
        "!a n s t m. W e a n  = Ok (s,t,m) --> n<=m";
by (expr.induct_tac "e" 1);
(* case Var(n) *)
by (fast_tac (HOL_cs addss (!simpset setloop (split_tac [expand_if]))) 1);
(* case Abs e *)
by (simp_tac (!simpset setloop (split_tac [expand_bind])) 1);
by (fast_tac (HOL_cs addDs [Suc_leD]) 1);
(* case App e1 e2 *)
by (simp_tac (!simpset setloop (split_tac [expand_bind])) 1);
by (strip_tac 1);
by (rename_tac "s t na sa ta nb sb sc tb m" 1);
by (eres_inst_tac [("x","a")] allE 1);
by (eres_inst_tac [("x","n")] allE 1);
by (eres_inst_tac [("x","$ s a")] allE 1);
by (eres_inst_tac [("x","s")] allE 1);
by (eres_inst_tac [("x","t")] allE 1);
by (eres_inst_tac [("x","na")] allE 1);
by (eres_inst_tac [("x","na")] allE 1);
by (asm_full_simp_tac (!simpset addsimps [eq_sym_conv]) 1);
by (etac conjE 1);
by (eres_inst_tac [("x","sa")] allE 1);
by (eres_inst_tac [("x","ta")] allE 1);
by (eres_inst_tac [("x","nb")] allE 1);
by (etac conjE 1);
by (res_inst_tac [("j","na")] le_trans 1); 
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
qed_spec_mp "W_var_ge";

Addsimps [W_var_ge];

goal thy
        "!! s. Ok (s,t,m) = W e a n ==> n<=m";
by (asm_full_simp_tac (!simpset addsimps [eq_sym_conv]) 1);
qed "W_var_geD";


(* auxiliary lemma *)
goal Maybe.thy "(y = Ok x) = (Ok x = y)";
by ( simp_tac (!simpset addsimps [eq_sym_conv]) 1);
qed "rotate_Ok";


(* resulting type variable is new *)
goal thy
     "!n a s t m. new_tv n a --> W e a n = Ok (s,t,m) -->    \
\                 new_tv m s & new_tv m t";
by (expr.induct_tac "e" 1);
(* case Var n *)
by (fast_tac (HOL_cs addss (!simpset 
        addsimps [id_subst_def,list_all_nth,new_tv_list,new_tv_subst] 
        setloop (split_tac [expand_if]))) 1);

(* case Abs e *)
by (simp_tac (!simpset addsimps [new_tv_subst,new_tv_Suc_list] 
    setloop (split_tac [expand_bind])) 1);
by (strip_tac 1);
by (eres_inst_tac [("x","Suc n")] allE 1);
by (eres_inst_tac [("x","(TVar n)#a")] allE 1);
by (fast_tac (HOL_cs addss (!simpset
              addsimps [new_tv_subst,new_tv_Suc_list])) 1);

(* case App e1 e2 *)
by (simp_tac (!simpset setloop (split_tac [expand_bind])) 1);
by (strip_tac 1);
by (rename_tac "s t na sa ta nb sb sc tb m" 1);
by (eres_inst_tac [("x","n")] allE 1);
by (eres_inst_tac [("x","a")] allE 1);
by (eres_inst_tac [("x","s")] allE 1);
by (eres_inst_tac [("x","t")] allE 1);
by (eres_inst_tac [("x","na")] allE 1);
by (eres_inst_tac [("x","na")] allE 1);
by (asm_full_simp_tac (!simpset addsimps [eq_sym_conv]) 1);
by (eres_inst_tac [("x","$ s a")] allE 1);
by (eres_inst_tac [("x","sa")] allE 1);
by (eres_inst_tac [("x","ta")] allE 1);
by (eres_inst_tac [("x","nb")] allE 1);
by ( asm_full_simp_tac (!simpset addsimps [o_def,rotate_Ok]) 1);
by (rtac conjI 1);
by (rtac new_tv_subst_comp_2 1);
by (rtac new_tv_subst_comp_2 1);
by (rtac (lessI RS less_imp_le RS new_tv_subst_le) 1);
by (res_inst_tac [("n","na")] new_tv_subst_le 1); 
by (asm_full_simp_tac (!simpset addsimps [rotate_Ok]) 1);
by (Asm_simp_tac 1);
by (fast_tac (HOL_cs addDs [W_var_geD] addIs
     [new_tv_list_le,new_tv_subst_tel,lessI RS less_imp_le RS new_tv_subst_le])
    1);
by (etac (sym RS mgu_new) 1);
by (best_tac (HOL_cs addDs [W_var_geD] 
                     addIs [new_tv_subst_te,new_tv_list_le,
                            new_tv_subst_tel,
                            lessI RS less_imp_le RS new_tv_le,
                            lessI RS less_imp_le RS new_tv_subst_le,
                            new_tv_le]) 1);
by (fast_tac (HOL_cs addDs [W_var_geD] 
                     addIs [new_tv_list_le,new_tv_subst_tel,new_tv_le] 
                     addss (!simpset)) 1);
by (rtac (lessI RS new_tv_subst_var) 1);
by (etac (sym RS mgu_new) 1);
by (best_tac (HOL_cs addSIs [lessI RS less_imp_le RS new_tv_le,new_tv_subst_te]
                     addDs [W_var_geD]
                     addIs [new_tv_list_le,
                            new_tv_subst_tel,
                            lessI RS less_imp_le RS new_tv_subst_le,
                            new_tv_le] 
                     addss !simpset) 1);
by (fast_tac (HOL_cs addDs [W_var_geD] 
                     addIs [new_tv_list_le,new_tv_subst_tel,new_tv_le]
                     addss (!simpset)) 1);
qed_spec_mp "new_tv_W";


goal thy
     "!n a s t m v. W e a n = Ok (s,t,m) -->            \
\         (v:free_tv s | v:free_tv t) --> v<n --> v:free_tv a";
by (expr.induct_tac "e" 1);
(* case Var n *)
by (fast_tac (HOL_cs addIs [nth_mem,subsetD,ftv_mem_sub_ftv_list] 
    addss (!simpset setloop (split_tac [expand_if]))) 1);

(* case Abs e *)
by (asm_full_simp_tac (!simpset addsimps
    [free_tv_subst] setloop (split_tac [expand_bind])) 1);
by (strip_tac 1);
by (rename_tac "s t na sa ta m v" 1);
by (eres_inst_tac [("x","Suc n")] allE 1);
by (eres_inst_tac [("x","TVar n # a")] allE 1);
by (eres_inst_tac [("x","s")] allE 1);
by (eres_inst_tac [("x","t")] allE 1);
by (eres_inst_tac [("x","na")] allE 1);
by (eres_inst_tac [("x","v")] allE 1);
by (fast_tac (HOL_cs addIs [cod_app_subst]
                     addss (!simpset addsimps [less_Suc_eq])) 1);

(* case App e1 e2 *)
by (simp_tac (!simpset setloop (split_tac [expand_bind])) 1);
by (strip_tac 1); 
by (rename_tac "s t na sa ta nb sb sc tb m v" 1);
by (eres_inst_tac [("x","n")] allE 1);
by (eres_inst_tac [("x","a")] allE 1);
by (eres_inst_tac [("x","s")] allE 1);
by (eres_inst_tac [("x","t")] allE 1);
by (eres_inst_tac [("x","na")] allE 1);
by (eres_inst_tac [("x","na")] allE 1);
by (eres_inst_tac [("x","v")] allE 1);
(* second case *)
by (eres_inst_tac [("x","$ s a")] allE 1);
by (eres_inst_tac [("x","sa")] allE 1);
by (eres_inst_tac [("x","ta")] allE 1);
by (eres_inst_tac [("x","nb")] allE 1);
by (eres_inst_tac [("x","v")] allE 1);
by (safe_tac (empty_cs addSIs [conjI,impI] addSEs [conjE]) ); 
by (asm_full_simp_tac (!simpset addsimps [rotate_Ok,o_def]) 1);
by (dtac W_var_geD 1);
by (dtac W_var_geD 1);
by ( (forward_tac [less_le_trans] 1) THEN (assume_tac 1) );
by (fast_tac (HOL_cs addDs [free_tv_comp_subst RS subsetD,sym RS mgu_free, 
    codD,free_tv_app_subst_te RS subsetD,free_tv_app_subst_tel RS subsetD,
    less_le_trans,less_not_refl2,subsetD]
  addEs [UnE] 
  addss !simpset) 1);
by (Asm_full_simp_tac 1); 
by (dtac (sym RS W_var_geD) 1);
by (dtac (sym RS W_var_geD) 1);
by ( (forward_tac [less_le_trans] 1) THEN (assume_tac 1) );
by (fast_tac (HOL_cs addDs [mgu_free, codD,free_tv_subst_var RS subsetD,
    free_tv_app_subst_te RS subsetD,free_tv_app_subst_tel RS subsetD,
    less_le_trans,subsetD]
  addEs [UnE]
  addss !simpset) 1); 
qed_spec_mp "free_tv_W"; 


(* Completeness of W w.r.t. has_type *)
goal thy
 "!s' a t' n. $s' a |- e :: t' --> new_tv n a -->     \
\             (? s t. (? m. W e a n = Ok (s,t,m)) &  \
\                     (? r. $s' a = $r ($s a) & t' = $r t))";
by (expr.induct_tac "e" 1);
(* case Var n *)
by (strip_tac 1);
by (simp_tac (!simpset addcongs [conj_cong] 
              setloop (split_tac [expand_if])) 1);
by (eresolve_tac has_type_casesE 1); 
by (asm_full_simp_tac (!simpset addsimps [eq_sym_conv,app_subst_list]) 1);
by (res_inst_tac [("x","id_subst")] exI 1);
by (res_inst_tac [("x","nth nat a")] exI 1);
by (Simp_tac 1);
by (res_inst_tac [("x","s'")] exI 1);
by (Asm_simp_tac 1);

(** LEVEL 10 **)
(* case Abs e *)
by (strip_tac 1);
by (eresolve_tac has_type_casesE 1);
by (eres_inst_tac [("x","%x.if x=n then t1 else (s' x)")] allE 1);
by (eres_inst_tac [("x","(TVar n)#a")] allE 1);
by (eres_inst_tac [("x","t2")] allE 1);
by (eres_inst_tac [("x","Suc n")] allE 1);
by (fast_tac (HOL_cs addss (!simpset addcongs [conj_cong]
                            setloop (split_tac [expand_bind]))) 1);

(** LEVEL 17 **)
(* case App e1 e2 *)
by (strip_tac 1);
by (eresolve_tac has_type_casesE 1);
by (eres_inst_tac [("x","s'")] allE 1);
by (eres_inst_tac [("x","a")] allE 1);
by (eres_inst_tac [("x","t2 -> t'")] allE 1);
by (eres_inst_tac [("x","n")] allE 1);
by (safe_tac HOL_cs);
by (eres_inst_tac [("x","r")] allE 1);
by (eres_inst_tac [("x","$ s a")] allE 1);
by (eres_inst_tac [("x","t2")] allE 1);
by (eres_inst_tac [("x","m")] allE 1);
by (dtac asm_rl 1);
by (dtac asm_rl 1);
by (dtac asm_rl 1);
by (Asm_full_simp_tac 1);
by (safe_tac HOL_cs);
by (fast_tac HOL_cs 1);
by (fast_tac (HOL_cs addIs [sym RS W_var_geD,new_tv_W RS
                            conjunct1,new_tv_list_le,new_tv_subst_tel]) 1);

(** LEVEL 35 **)
by (subgoal_tac
  "$ (%x.if x=ma then t' else (if x:(free_tv t - free_tv sa) then r x \
\        else ra x)) ($ sa t) = \
\  $ (%x.if x=ma then t' else (if x:(free_tv t - free_tv sa) then r x \
\        else ra x)) (ta -> (TVar ma))" 1);
by (res_inst_tac [("t","$ (%x. if x = ma then t' else \
\   (if x:(free_tv t - free_tv sa) then r x else ra x)) ($ sa t)"),
    ("s","($ ra ta) -> t'")] ssubst 2);
by (asm_simp_tac (!simpset addsimps [subst_comp_te]) 2);
by (rtac eq_free_eq_subst_te 2);  
by (strip_tac 2);
by (subgoal_tac "na ~=ma" 2);
by (fast_tac (HOL_cs addDs [new_tv_W,sym RS W_var_geD,
                            new_tv_not_free_tv,new_tv_le]) 3);
(** LEVEL 42 **)
by (case_tac "na:free_tv sa" 2);
(* na ~: free_tv sa *)
by (asm_simp_tac (!simpset addsimps [not_free_impl_id]
                  setloop (split_tac [expand_if])) 3);
(* na : free_tv sa *)
by (dres_inst_tac [("ts1","$ s a")] (subst_comp_tel RSN (2,trans)) 2);
by (dtac eq_subst_tel_eq_free 2);
by (fast_tac (HOL_cs addIs [free_tv_W,free_tv_le_new_tv] addDs [new_tv_W]) 2);
by (Asm_simp_tac 2); 
by (case_tac "na:dom sa" 2);
(* na ~: dom sa *)
by (asm_full_simp_tac (!simpset addsimps [dom_def] 
                       setloop (split_tac [expand_if])) 3);
(** LEVEL 50 **)
(* na : dom sa *)
by (rtac eq_free_eq_subst_te 2);
by (strip_tac 2);
by (subgoal_tac "nb ~= ma" 2);
by ((forward_tac [new_tv_W] 3) THEN (atac 3));
by (etac conjE 3);
by (dtac new_tv_subst_tel 3);
by (fast_tac (HOL_cs addIs [new_tv_list_le] addDs [sym RS W_var_geD]) 3);
by (fast_tac (set_cs addDs [new_tv_W,new_tv_not_free_tv] addss 
              (!simpset addsimps [cod_def,free_tv_subst])) 3);
by (fast_tac (set_cs addss (!simpset addsimps [cod_def,free_tv_subst] 
                            setloop (split_tac [expand_if]))) 2);

by (Simp_tac 2);  
(** LEVEL 60 **)
by (rtac eq_free_eq_subst_te 2);
by (strip_tac 2 );
by (subgoal_tac "na ~= ma" 2);
by ((forward_tac [new_tv_W] 3) THEN (atac 3));
by (etac conjE 3);
by (dtac (sym RS W_var_geD) 3);
by (fast_tac (HOL_cs addDs [new_tv_list_le,new_tv_subst_tel,new_tv_W,new_tv_not_free_tv]) 3);
by (case_tac "na: free_tv t - free_tv sa" 2);
(** LEVEL 68 **)
(* case na ~: free_tv t - free_tv sa *)
by ( asm_full_simp_tac (!simpset setloop (split_tac [expand_if])) 3);
(* case na : free_tv t - free_tv sa *)
by ( asm_full_simp_tac (!simpset setloop (split_tac [expand_if])) 2);
by (dres_inst_tac [("ts1","$ s a")] (subst_comp_tel RSN (2,trans)) 2);
by (dtac eq_subst_tel_eq_free 2);
by (fast_tac (HOL_cs addIs [free_tv_W,free_tv_le_new_tv] addDs [new_tv_W]) 2);
by (asm_full_simp_tac (!simpset addsimps [free_tv_subst,dom_def,de_Morgan_disj]) 2);
(** LEVEL 74 **)
by (asm_simp_tac (!simpset setloop (split_tac [expand_bind])) 1); 
by (safe_tac HOL_cs );
by (dtac mgu_Ok 1);
by ( fast_tac (HOL_cs addss !simpset) 1);
by (REPEAT (resolve_tac [exI,conjI] 1));
by (fast_tac HOL_cs 1);
by (fast_tac HOL_cs 1);
by ((dtac mgu_mg 1) THEN (atac 1));
by (etac exE 1);
by (res_inst_tac [("x","rb")] exI 1);
by (rtac conjI 1);
by (dres_inst_tac [("x","ma")] fun_cong 2);
by ( asm_full_simp_tac (!simpset addsimps [eq_sym_conv]) 2);
by (simp_tac (!simpset addsimps [subst_comp_tel RS sym]) 1);
by (res_inst_tac [("ts2","($ sa ($ s a))")] ((subst_comp_tel RS sym) RSN 
    (2,trans)) 1);
by ( asm_full_simp_tac (!simpset addsimps [o_def,eq_sym_conv]) 1);
(** LEVEL 90 **)
by (rtac eq_free_eq_subst_tel 1);
by ( safe_tac HOL_cs );
by (subgoal_tac "ma ~= na" 1);
by ((forward_tac [new_tv_W] 2) THEN (atac 2));
by (etac conjE 2);
by (dtac new_tv_subst_tel 2);
by (fast_tac (HOL_cs addIs [new_tv_list_le] addDs [sym RS W_var_geD]) 2);
by (( forw_inst_tac [("n","m")] (sym RSN (2,new_tv_W)) 2) THEN (atac 2));
by (etac conjE 2);
by (dtac (free_tv_app_subst_tel RS subsetD) 2);
(** LEVEL 100 **)
by (fast_tac (set_cs addDs [W_var_geD,new_tv_list_le,codD,
    new_tv_not_free_tv]) 2);
by (case_tac "na: free_tv t - free_tv sa" 1);
(* case na ~: free_tv t - free_tv sa *)
by (asm_full_simp_tac (!simpset setloop (split_tac [expand_if])) 2);
(* case na : free_tv t - free_tv sa *)
by (asm_full_simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (dtac (free_tv_app_subst_tel RS subsetD) 1);
by (fast_tac (set_cs addDs [codD,subst_comp_tel RSN (2,trans),
			    eq_subst_tel_eq_free] 
       addss ((!simpset addsimps [de_Morgan_disj,free_tv_subst,dom_def]))) 1);
(** LEVEL 106 **)
by (Fast_tac 1);
qed_spec_mp "W_complete_lemma";

goal W.thy
 "!!e. [] |- e :: t' ==>  (? s t. (? m. W e [] n = Ok(s,t,m)) &  \
\                                 (? r. t' = $r t))";
by (cut_inst_tac [("a","[]"),("s'","id_subst"),("e","e"),("t'","t'")]
                W_complete_lemma 1);
by (ALLGOALS Asm_full_simp_tac);
qed "W_complete";
