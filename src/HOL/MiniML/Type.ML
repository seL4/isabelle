open Type;

Addsimps [app_subst_TVar,app_subst_Fun];
Addsimps [mgu_eq,mgu_mg,mgu_free];
Addsimps [free_tv_TVar,free_tv_Fun,free_tv_Nil,free_tv_Cons];

(* mgu does not introduce new type variables *)
goalw thy [new_tv_def] 
      "!! n. [|mgu t1 t2 = Ok u; new_tv n t1; new_tv n t2|] ==> \
\            new_tv n u";
by( fast_tac (set_cs addDs [mgu_free]) 1);
qed "mgu_new";

(* application of id_subst does not change type expression *)
goalw thy [id_subst_def]
  "$ id_subst = (%t::typ.t)";
by (rtac ext 1);
by (typ.induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "app_subst_id_te";
Addsimps [app_subst_id_te];

(* application of id_subst does not change list of type expressions *)
goalw thy [app_subst_list]
  "$ id_subst = (%ts::typ list.ts)";
by (rtac ext 1); 
by (list.induct_tac "ts" 1);
by (ALLGOALS Asm_simp_tac);
qed "app_subst_id_tel";
Addsimps [app_subst_id_tel];

goalw thy [dom_def,id_subst_def,empty_def]
  "dom id_subst = {}";
by (Simp_tac 1);
qed "dom_id_subst";
Addsimps [dom_id_subst];

goalw thy [cod_def]
  "cod id_subst = {}";
by (Simp_tac 1);
qed "cod_id_subst";
Addsimps [cod_id_subst];

goalw thy [free_tv_subst]
  "free_tv id_subst = {}";
by (Simp_tac 1);
qed "free_tv_id_subst";
Addsimps [free_tv_id_subst];

goalw thy [dom_def,cod_def,UNION_def,Bex_def]
  "!!v. [| v : free_tv(s n); v~=n |] ==> v : cod s";
by (Simp_tac 1);
by (safe_tac (empty_cs addSIs [exI,conjI,notI]));
by (assume_tac 2);
by (rotate_tac 1 1);
by (Asm_full_simp_tac 1);
qed "cod_app_subst";
Addsimps [cod_app_subst];


(* composition of substitutions *)
goal thy
  "$ g ($ f t::typ) = $ (%x. $ g (f x) ) t";
by (typ.induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "subst_comp_te";

goalw thy [app_subst_list]
  "$ g ($ f ts::typ list) = $ (%x. $ g (f x)) ts";
by (list.induct_tac "ts" 1);
(* case [] *)
by (Simp_tac 1);
(* case x#xl *)
by (asm_full_simp_tac (!simpset addsimps [subst_comp_te]) 1);
qed "subst_comp_tel";


(* constructor laws for app_subst *)
goalw thy [app_subst_list]
  "$ s [] = []";
by (Simp_tac 1);
qed "app_subst_Nil";

goalw thy [app_subst_list]
  "$ s (t#ts) = ($ s t)#($ s ts)";
by (Simp_tac 1);
qed "app_subst_Cons";

Addsimps [app_subst_Nil,app_subst_Cons];

(* constructor laws for new_tv *)
goalw thy [new_tv_def]
  "new_tv n (TVar m) = (m<n)";
by (fast_tac (HOL_cs addss !simpset) 1);
qed "new_tv_TVar";

goalw thy [new_tv_def]
  "new_tv n (t1 -> t2) = (new_tv n t1 & new_tv n t2)";
by (fast_tac (HOL_cs addss !simpset) 1);
qed "new_tv_Fun";

goalw thy [new_tv_def]
  "new_tv n []";
by (Simp_tac 1);
qed "new_tv_Nil";

goalw thy [new_tv_def]
  "new_tv n (t#ts) = (new_tv n t & new_tv n ts)";
by (fast_tac (HOL_cs addss !simpset) 1);
qed "new_tv_Cons";

Addsimps [new_tv_TVar,new_tv_Fun,new_tv_Nil,new_tv_Cons];


goalw thy [new_tv_def]
  "new_tv n s = ((!m. n <= m --> (s m = TVar m)) & \
\                (! l. l < n --> new_tv n (s l) ))";
by( safe_tac HOL_cs );
(* ==> *)
by( fast_tac (HOL_cs addDs [leD] addss (!simpset addsimps [free_tv_subst,dom_def])) 1);
by( subgoal_tac "m:cod s | s l = TVar l" 1);
by( safe_tac HOL_cs );
by(fast_tac (HOL_cs addDs [UnI2] addss (!simpset addsimps [free_tv_subst])) 1);
by(dres_inst_tac [("P","%x. m:free_tv x")] subst 1 THEN atac 1);
by(Asm_full_simp_tac 1);
by(fast_tac (set_cs addss (!simpset addsimps [free_tv_subst,cod_def,dom_def])) 1);
(* <== *)
by( rewrite_goals_tac [free_tv_subst,cod_def,dom_def] );
by( safe_tac set_cs );
by( cut_inst_tac [("m","m"),("n","n")] less_linear 1);
by( fast_tac (HOL_cs addSIs [less_or_eq_imp_le]) 1);
by( cut_inst_tac [("m","ma"),("n","n")] less_linear 1);
by( fast_tac (HOL_cs addSIs [less_or_eq_imp_le]) 1);
qed "new_tv_subst";

goal thy 
  "new_tv n  = list_all (new_tv n)";
by (rtac ext 1);
by(list.induct_tac "x" 1);
by(ALLGOALS Asm_simp_tac);
qed "new_tv_list";

(* substitution affects only variables occurring freely *)
goal thy
  "new_tv n (t::typ) --> $(%x. if x=n then t' else s x) t = $s t";
by (typ.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
qed "subst_te_new_tv";
Addsimps [subst_te_new_tv];

goal thy
  "new_tv n (ts::typ list) --> $(%x. if x=n then t else s x) ts = $s ts";
by (list.induct_tac "ts" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "subst_tel_new_tv";
Addsimps [subst_tel_new_tv];

(* all greater variables are also new *)
goal thy
  "n<=m --> new_tv n (t::typ) --> new_tv m t";
by (typ.induct_tac "t" 1);
(* case TVar n *)
by( fast_tac (HOL_cs addIs [less_le_trans] addss !simpset) 1);
(* case Fun t1 t2 *)
by (Asm_simp_tac 1);
qed_spec_mp "new_tv_le";
Addsimps [lessI RS less_imp_le RS new_tv_le];

goal thy 
  "n<=m --> new_tv n (ts::typ list) --> new_tv m ts";
by( list.induct_tac "ts" 1);
(* case [] *)
by(Simp_tac 1);
(* case a#al *)
by (fast_tac (HOL_cs addIs [new_tv_le] addss !simpset) 1);
qed_spec_mp "new_tv_list_le";
Addsimps [lessI RS less_imp_le RS new_tv_list_le];

goal thy
  "!! n. [| n<=m; new_tv n (s::subst) |] ==> new_tv m s";
by (asm_full_simp_tac (!simpset addsimps [new_tv_subst]) 1);
by (rtac conjI 1);
by (slow_tac (HOL_cs addIs [le_trans]) 1);
by (safe_tac HOL_cs );
by (res_inst_tac [("P","l < n"),("Q","n <= l")] disjE 1);
by (fast_tac (HOL_cs addss (HOL_ss addsimps [le_def])) 1);
by (ALLGOALS (asm_full_simp_tac (!simpset addsimps [new_tv_le])) );
qed "new_tv_subst_le";
Addsimps [lessI RS less_imp_le RS new_tv_subst_le];

(* new_tv property remains if a substitution is applied *)
goal thy
  "!!n. [| n<m; new_tv m (s::subst) |] ==> new_tv m (s n)";
by (asm_full_simp_tac (!simpset addsimps [new_tv_subst]) 1);
qed "new_tv_subst_var";

goal thy
  "new_tv n s --> new_tv n (t::typ) --> new_tv n ($ s t)";
by (typ.induct_tac "t" 1);
by (ALLGOALS(fast_tac (HOL_cs addss (!simpset addsimps [new_tv_subst]))));
qed_spec_mp "new_tv_subst_te";
Addsimps [new_tv_subst_te];

goal thy
  "new_tv n s --> new_tv n (ts::typ list) --> new_tv n ($ s ts)";
by( simp_tac (!simpset addsimps [new_tv_list]) 1);
by (list.induct_tac "ts" 1);
by (ALLGOALS(fast_tac (HOL_cs addss (!simpset addsimps [new_tv_subst]))));
qed_spec_mp "new_tv_subst_tel";
Addsimps [new_tv_subst_tel];

(* auxilliary lemma *)
goal thy
  "new_tv n ts --> new_tv (Suc n) ((TVar n)#ts)";
by( simp_tac (!simpset addsimps [new_tv_list]) 1);
by (list.induct_tac "ts" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "new_tv_Suc_list";


(* composition of substitutions preserves new_tv proposition *)
goal thy 
     "!! n. [| new_tv n (s::subst); new_tv n r |] ==> \
\           new_tv n (($ r) o s)";
by (asm_full_simp_tac (!simpset addsimps [new_tv_subst]) 1);
qed "new_tv_subst_comp_1";

goal thy
     "!! n. [| new_tv n (s::subst); new_tv n r |] ==>  \ 
\     new_tv n (%v.$ r (s v))";
by (asm_full_simp_tac (!simpset addsimps [new_tv_subst]) 1);
qed "new_tv_subst_comp_2";

Addsimps [new_tv_subst_comp_1,new_tv_subst_comp_2];

(* new type variables do not occur freely in a type structure *)
goalw thy [new_tv_def] 
      "!!n. new_tv n ts ==> n~:(free_tv ts)";
by (fast_tac (HOL_cs addEs [less_irrefl]) 1);
qed "new_tv_not_free_tv";
Addsimps [new_tv_not_free_tv];

goal thy
  "(t::typ) mem ts --> free_tv t <= free_tv ts";
by (list.induct_tac "ts" 1);
(* case [] *)
by (Simp_tac 1);
(* case x#xl *)
by (fast_tac (set_cs addss (!simpset setloop (split_tac [expand_if]))) 1);
qed_spec_mp "ftv_mem_sub_ftv_list";
Addsimps [ftv_mem_sub_ftv_list];


(* if two substitutions yield the same result if applied to a type
   structure the substitutions coincide on the free type variables
   occurring in the type structure *)
goal thy
  "$ s1 (t::typ) = $ s2 t --> n:(free_tv t) --> s1 n = s2 n";
by (typ.induct_tac "t" 1);
(* case TVar n *)
by (fast_tac (HOL_cs addss !simpset) 1);
(* case Fun t1 t2 *)
by (fast_tac (HOL_cs addss !simpset) 1);
qed_spec_mp "eq_subst_te_eq_free";

goal thy
  "(!n. n:(free_tv t) --> s1 n = s2 n) --> $ s1 (t::typ) = $ s2 t";
by (typ.induct_tac "t" 1);
(* case TVar n *)
by (fast_tac (HOL_cs addss !simpset) 1);
(* case Fun t1 t2 *)
by (fast_tac (HOL_cs addss !simpset) 1);
qed_spec_mp "eq_free_eq_subst_te";

goal thy
  "$s1 (ts::typ list) = $s2 ts --> n:(free_tv ts) --> s1 n = s2 n";
by (list.induct_tac "ts" 1);
(* case [] *)
by (fast_tac (HOL_cs addss !simpset) 1);
(* case x#xl *)
by (fast_tac (HOL_cs addIs [eq_subst_te_eq_free] addss (!simpset)) 1);
qed_spec_mp "eq_subst_tel_eq_free";

goal thy
  "(!n. n:(free_tv ts) --> s1 n = s2 n) --> $s1 (ts::typ list) = $s2 ts";
by (list.induct_tac "ts" 1); 
(* case [] *)
by (fast_tac (HOL_cs addss !simpset) 1);
(* case x#xl *)
by (fast_tac (HOL_cs addIs [eq_free_eq_subst_te] addss (!simpset)) 1);
qed_spec_mp "eq_free_eq_subst_tel";

(* some useful theorems *)
goalw thy [free_tv_subst] 
      "!!v. v : cod s ==> v : free_tv s";
by( fast_tac set_cs 1);
qed "codD";
 
goalw thy [free_tv_subst,dom_def] 
      "!! x. x ~: free_tv s ==> s x = TVar x";
by( fast_tac set_cs 1);
qed "not_free_impl_id";

goalw thy [new_tv_def] 
      "!! n. [| new_tv n t; m:free_tv t |] ==> m<n";
by( fast_tac HOL_cs 1 );
qed "free_tv_le_new_tv";

goal thy 
     "free_tv (s (v::nat)) <= cod s Un {v}";
by( cut_inst_tac [("P","v:dom s")] excluded_middle 1);
by( safe_tac (HOL_cs addSIs [subsetI]) );
by (fast_tac (set_cs addss (!simpset addsimps [dom_def])) 1);
by (fast_tac (set_cs addss (!simpset addsimps [cod_def])) 1);
qed "free_tv_subst_var";

goal thy 
     "free_tv ($ s (t::typ)) <= cod s Un free_tv t";
by( typ.induct_tac "t" 1);
(* case TVar n *)
by( simp_tac (!simpset addsimps [free_tv_subst_var]) 1);
(* case Fun t1 t2 *)
by( fast_tac (set_cs addss !simpset) 1);
qed "free_tv_app_subst_te";     

goal thy 
     "free_tv ($ s (ts::typ list)) <= cod s Un free_tv ts";
by( list.induct_tac "ts" 1);
(* case [] *)
by (Simp_tac 1);
(* case a#al *)
by( cut_facts_tac [free_tv_app_subst_te] 1);
by( fast_tac (set_cs addss !simpset) 1);
qed "free_tv_app_subst_tel";

goalw thy [free_tv_subst,dom_def]
     "free_tv (%u::nat. $ s1 (s2 u) :: typ) <=   \
\     free_tv s1 Un free_tv s2";
by( fast_tac (set_cs addSDs [free_tv_app_subst_te RS
subsetD,free_tv_subst_var RS subsetD] addss (
!simpset addsimps [cod_def,dom_def])) 1);
qed "free_tv_comp_subst";

