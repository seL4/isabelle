(* Title:     HOL/MiniML/W.ML
   ID:        $Id$
   Author:    Dieter Nazareth and Tobias Nipkow
   Copyright  1995 TU Muenchen

Correctness and completeness of type inference algorithm W
*)

Addsimps [Suc_le_lessD];  Delsimps [less_imp_le];  (*the combination loops*)

val has_type_casesE = 
    map has_type.mk_cases
	[" A |- Var n :: t",
	 " A |- Abs e :: t",
	 "A |- App e1 e2 ::t",
	 "A |- LET e1 e2 ::t" ];

(* the resulting type variable is always greater or equal than the given one *)
Goal "!A n S t m. W e A n  = Some (S,t,m) --> n<=m";
by (induct_tac "e" 1);
(* case Var(n) *)
by (simp_tac (simpset() addsplits [split_option_bind]) 1);
(* case Abs e *)
by (simp_tac (simpset() addsplits [split_option_bind]) 1);
by (fast_tac (HOL_cs addDs [Suc_leD]) 1);
(* case App e1 e2 *)
by (simp_tac (simpset() addsplits [split_option_bind]) 1);
by (blast_tac (claset() addIs [le_SucI,le_trans]) 1);
(* case LET e1 e2 *)
by (simp_tac (simpset() addsplits [split_option_bind]) 1);
by (blast_tac (claset() addIs [le_trans]) 1);
qed_spec_mp "W_var_ge";

Addsimps [W_var_ge];

Goal "Some (S,t,m) = W e A n ==> n<=m";
by (asm_full_simp_tac (simpset() addsimps [eq_sym_conv]) 1);
qed "W_var_geD";

Goal "new_tv n A ==> Some (S,t,m) = W e A n ==> new_tv m A";
by (dtac W_var_geD 1);
by (rtac new_scheme_list_le 1);
by (assume_tac 1);
by (assume_tac 1);
qed "new_tv_compatible_W";

Goal "new_tv n sch --> new_tv (n + (min_new_bound_tv sch)) (bound_typ_inst (%b. TVar (b + n)) sch)";
by (induct_tac "sch" 1);
  by (Asm_full_simp_tac 1);
 by (asm_full_simp_tac (simpset() addsimps [add_commute]) 1);
by (strip_tac 1);
by (Asm_full_simp_tac 1);
by (etac conjE 1);
by (rtac conjI 1);
 by (rtac new_tv_le 1);
  by (assume_tac 2);
 by (rtac add_le_mono 1);
  by (Simp_tac 1);
 by (simp_tac (simpset() addsimps [max_def]) 1);
by (rtac new_tv_le 1);
 by (assume_tac 2);
by (rtac add_le_mono 1);
 by (Simp_tac 1);
by (simp_tac (simpset() addsimps [max_def]) 1);
qed_spec_mp "new_tv_bound_typ_inst_sch";

Addsimps [new_tv_bound_typ_inst_sch];

(* resulting type variable is new *)
Goal "!n A S t m. new_tv n A --> W e A n = Some (S,t,m) -->    \
\                 new_tv m S & new_tv m t";
by (induct_tac "e" 1);
(* case Var n *)
by (simp_tac (simpset() addsplits [split_option_bind]) 1);
by (strip_tac 1);
by (dtac new_tv_nth_nat_A 1);
by (assume_tac 1);
by (Asm_simp_tac 1);
(* case Abs e *)
by (simp_tac (simpset() addsimps [new_tv_subst,new_tv_Suc_list] 
    addsplits [split_option_bind]) 1);
by (strip_tac 1);
by (eres_inst_tac [("x","Suc n")] allE 1);
by (eres_inst_tac [("x","(FVar n)#A")] allE 1);
by (fast_tac (HOL_cs addss (simpset()
              addsimps [new_tv_subst,new_tv_Suc_list])) 1);
(* case App e1 e2 *)
by (simp_tac (simpset() addsplits [split_option_bind]) 1);
by (strip_tac 1);
by (rename_tac "S1 t1 n1 S2 t2 n2 S3" 1);
by (eres_inst_tac [("x","n")] allE 1);
by (eres_inst_tac [("x","A")] allE 1);
by (eres_inst_tac [("x","S1")] allE 1);
by (eres_inst_tac [("x","t1")] allE 1);
by (eres_inst_tac [("x","n1")] allE 1);
by (eres_inst_tac [("x","n1")] allE 1);
by (asm_full_simp_tac (simpset() addsimps [eq_sym_conv] delsimps all_simps) 1);
by (eres_inst_tac [("x","$S1 A")] allE 1);
by (eres_inst_tac [("x","S2")] allE 1);
by (eres_inst_tac [("x","t2")] allE 1);
by (eres_inst_tac [("x","n2")] allE 1);
by ( asm_full_simp_tac (simpset() addsimps [o_def,rotate_Some]) 1);
by (rtac conjI 1);
by (rtac new_tv_subst_comp_2 1);
by (rtac new_tv_subst_comp_2 1);
by (rtac (lessI RS less_imp_le RS new_tv_le) 1); 
by (res_inst_tac [("n","n1")] new_tv_subst_le 1); 
by (asm_full_simp_tac (simpset() addsimps [rotate_Some]) 1);
by (Asm_simp_tac 1);
by (fast_tac (HOL_cs addDs [W_var_geD] addIs
     [new_scheme_list_le,new_tv_subst_scheme_list,lessI RS less_imp_le RS new_tv_subst_le])
    1);
by (etac (sym RS mgu_new) 1);
by (best_tac (HOL_cs addDs [W_var_geD] addIs [new_tv_subst_te,new_scheme_list_le,
   new_tv_subst_scheme_list,lessI RS less_imp_le RS new_tv_le,lessI RS less_imp_le RS 
   new_tv_subst_le,new_tv_le]) 1);
by (fast_tac (HOL_cs addDs [W_var_geD] addIs
     [new_scheme_list_le,new_tv_subst_scheme_list,new_tv_le] 
        addss (simpset())) 1);
by (rtac (lessI RS new_tv_subst_var) 1);
by (etac (sym RS mgu_new) 1);
by (best_tac (HOL_cs addSIs [lessI RS less_imp_le RS new_tv_le,new_tv_subst_te]
   addDs [W_var_geD] addIs
   [new_scheme_list_le,new_tv_subst_scheme_list,lessI RS less_imp_le RS
   new_tv_subst_le,new_tv_le] addss simpset()) 1);
by (fast_tac (HOL_cs addDs [W_var_geD] addIs
     [new_scheme_list_le,new_tv_subst_scheme_list,new_tv_le]
     addss (simpset())) 1);
(* 41: case LET e1 e2 *)
by (simp_tac (simpset() addsplits [split_option_bind]) 1);
by (strip_tac 1);
by (EVERY1[etac allE,etac allE,etac allE,etac allE,etac allE,mp_tac,mp_tac]);
by (etac conjE 1);
by (EVERY[etac allE 1,etac allE 1,etac allE 1,etac allE 1,etac allE 1,
         etac impE 1, mp_tac 2]);
by (SELECT_GOAL(rewtac new_tv_def)1);
by (Asm_simp_tac 1);
by (REPEAT(dtac W_var_ge 1));
by (rtac allI 1);
by (strip_tac 1);
by (SELECT_GOAL(rewtac free_tv_subst) 1);
by (dtac (free_tv_app_subst_scheme_list RS subsetD) 1);
by (best_tac (claset() addEs [less_le_trans]) 1);
by (etac conjE 1);
by (rtac conjI 1);
by (SELECT_GOAL(rewtac o_def)1);
by (rtac new_tv_subst_comp_2 1);
by (etac (W_var_ge RS new_tv_subst_le) 1);
by (assume_tac 1);
by (assume_tac 1);
by (assume_tac 1);
qed_spec_mp "new_tv_W";

Goal "(v ~: free_tv sch) --> (v : free_tv (bound_typ_inst (TVar o S) sch)) --> (? x. v = S x)";
by (induct_tac "sch" 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (strip_tac 1);
by (rtac exI 1);
by (rtac refl 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "free_tv_bound_typ_inst1";

Addsimps [free_tv_bound_typ_inst1];

Goal "!n A S t m v. W e A n = Some (S,t,m) -->            \
\         (v:free_tv S | v:free_tv t) --> v<n --> v:free_tv A";
by (induct_tac "e" 1);
(* case Var n *)
by (simp_tac (simpset() addsimps
    [free_tv_subst] addsplits [split_option_bind]) 1);
by (strip_tac 1);
by (case_tac "v : free_tv (A!nat)" 1);
by (Asm_full_simp_tac 1);
by (dtac free_tv_bound_typ_inst1 1);
by (simp_tac (simpset() addsimps [o_def]) 1);
by (etac exE 1);
by (rotate_tac 3 1);
by (Asm_full_simp_tac 1);
(* case Abs e *)
by (asm_full_simp_tac (simpset() addsimps
    [free_tv_subst] addsplits [split_option_bind] delsimps all_simps) 1);
by (strip_tac 1);
by (rename_tac "S t n1 S1 t1 m v" 1);
by (eres_inst_tac [("x","Suc n")] allE 1);
by (eres_inst_tac [("x","FVar n # A")] allE 1);
by (eres_inst_tac [("x","S")] allE 1);
by (eres_inst_tac [("x","t")] allE 1);
by (eres_inst_tac [("x","n1")] allE 1);
by (eres_inst_tac [("x","v")] allE 1);
by (best_tac (HOL_cs addIs [cod_app_subst]
                     addss (simpset() addsimps [less_Suc_eq])) 1);
(* case App e1 e2 *)
by (simp_tac (simpset() addsplits [split_option_bind] delsimps all_simps) 1);
by (strip_tac 1); 
by (rename_tac "S t n1 S1 t1 n2 S2 S3 t2 m v" 1);
by (eres_inst_tac [("x","n")] allE 1);
by (eres_inst_tac [("x","A")] allE 1);
by (eres_inst_tac [("x","S")] allE 1);
by (eres_inst_tac [("x","t")] allE 1);
by (eres_inst_tac [("x","n1")] allE 1);
by (eres_inst_tac [("x","n1")] allE 1);
by (eres_inst_tac [("x","v")] allE 1);
(* second case *)
by (eres_inst_tac [("x","$ S A")] allE 1);
by (eres_inst_tac [("x","S1")] allE 1);
by (eres_inst_tac [("x","t1")] allE 1);
by (eres_inst_tac [("x","n2")] allE 1);
by (eres_inst_tac [("x","v")] allE 1);
by (safe_tac (empty_cs addSIs [conjI,impI] addSEs [conjE]) ); 
by (asm_full_simp_tac (simpset() addsimps [rotate_Some,o_def]) 1);
by (dtac W_var_geD 1);
by (dtac W_var_geD 1);
by ( (forward_tac [less_le_trans] 1) THEN (assume_tac 1) );
by (fast_tac (HOL_cs addDs [free_tv_comp_subst RS subsetD,sym RS mgu_free, 
    codD,free_tv_app_subst_te RS subsetD,free_tv_app_subst_scheme_list RS subsetD,
    less_le_trans,less_not_refl2,subsetD]
  addEs [UnE] 
  addss simpset()) 1);
by (Asm_full_simp_tac 1); 
by (dtac (sym RS W_var_geD) 1);
by (dtac (sym RS W_var_geD) 1);
by ( (forward_tac [less_le_trans] 1) THEN (assume_tac 1) );
by (fast_tac (HOL_cs addDs [mgu_free, codD,free_tv_subst_var RS subsetD,
    free_tv_app_subst_te RS subsetD,free_tv_app_subst_scheme_list RS subsetD,
    less_le_trans,subsetD]
  addEs [UnE]
  addss (simpset() setSolver unsafe_solver)) 1);
(* LET e1 e2 *)
by (simp_tac (simpset() addsplits [split_option_bind] delsimps all_simps) 1);
by (strip_tac 1); 
by (rename_tac "nat A S1 t1 n2 S2 t2 m2 S t m v" 1);
by (eres_inst_tac [("x","nat")] allE 1);
by (eres_inst_tac [("x","A")] allE 1);
by (eres_inst_tac [("x","S1")] allE 1);
by (eres_inst_tac [("x","t1")] allE 1);
by (rotate_tac 1 1);
by (eres_inst_tac [("x","n2")] allE 1);
by (rotate_tac 4 1);
by (eres_inst_tac [("x","v")] allE 1);
by (mp_tac 1);
by (EVERY1 [etac allE,etac allE,etac allE,etac allE,etac allE,eres_inst_tac [("x","v")] allE]);
by (mp_tac 1);
by (Asm_full_simp_tac 1);
by (rtac conjI 1);
by (fast_tac (claset() addSDs [codD,free_tv_app_subst_scheme_list RS subsetD,free_tv_o_subst RS subsetD,W_var_ge] 
              addDs [less_le_trans]) 1);
by (fast_tac (claset() addSDs [codD,free_tv_app_subst_scheme_list RS subsetD,W_var_ge] 
              addDs [less_le_trans]) 1);
qed_spec_mp "free_tv_W"; 

Goal "(!x. x : A --> x ~: B) ==> A Int B = {}";
by (Fast_tac 1);
val weaken_A_Int_B_eq_empty = result();

Goal "x ~: A | x : B ==> x ~: A - B";
by (Fast_tac 1);
val weaken_not_elem_A_minus_B = result();

(* correctness of W with respect to has_type *)
Goal "!A S t m n . new_tv n A --> Some (S,t,m) = W e A n --> $S A |- e :: t";
by (induct_tac "e" 1);
(* case Var n *)
by (Asm_full_simp_tac 1);
by (strip_tac 1);
by (rtac has_type.VarI 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsimps [is_bound_typ_instance]) 1);
by (rtac exI 1);
by (rtac refl 1);
(* case Abs e *)
by (asm_full_simp_tac (simpset() addsimps [app_subst_list]
                        addsplits [split_option_bind]) 1);
by (strip_tac 1);
by (eres_inst_tac [("x","(mk_scheme (TVar n)) # A")] allE 1);
by (Asm_full_simp_tac 1);
by (rtac has_type.AbsI 1);
by (dtac (le_refl RS le_SucI RS new_scheme_list_le) 1);
by (dtac sym 1);
by (REPEAT (etac allE 1));
by (etac impE 1);
by (mp_tac 2);
by (Asm_simp_tac 1);
by (assume_tac 1);
(* case App e1 e2 *)
by (simp_tac (simpset() addsplits [split_option_bind]) 1);
by (strip_tac 1);
by (rename_tac "S1 t1 n1 S2 t2 n2 S3" 1);
by (res_inst_tac [("t2.0","$ S3 t2")] has_type.AppI 1);
by (res_inst_tac [("S1","S3")] (app_subst_TVar RS subst) 1);
by (rtac (app_subst_Fun RS subst) 1);
by (res_inst_tac [("t","$S3 (t2 -> (TVar n2))"),("s","$S3 ($S2 t1)")] subst 1);
by (Asm_full_simp_tac 1);
by (simp_tac (HOL_ss addsimps [subst_comp_scheme_list RS sym,o_def]) 1);
by ((rtac (has_type_cl_sub RS spec) 1) THEN (rtac (has_type_cl_sub RS spec) 1));
by (asm_full_simp_tac (simpset() addsimps [eq_sym_conv]) 1);
by (asm_full_simp_tac (simpset() addsimps [subst_comp_scheme_list RS sym,o_def,has_type_cl_sub,eq_sym_conv]) 1);
by (rtac (has_type_cl_sub RS spec) 1);
by (forward_tac [new_tv_W] 1);
by (assume_tac 1);
by (dtac conjunct1 1);
by (dtac conjunct1 1);
by (forward_tac [new_tv_subst_scheme_list] 1);
by (rtac new_scheme_list_le 1);
by (rtac W_var_ge 1);
by (assume_tac 1);
by (assume_tac 1);
by (etac thin_rl 1);
by (REPEAT (etac allE 1));
by (dtac sym 1);
by (dtac sym 1);
by (etac thin_rl 1);
by (etac thin_rl 1);
by (mp_tac 1);
by (mp_tac 1);
by (assume_tac 1);
(* case Let e1 e2 *)
by (simp_tac (simpset() addsplits [split_option_bind]) 1);
by (strip_tac 1);
by (rename_tac "w q m1 S1 t1 m2 S2 t n2" 1); 
by (res_inst_tac [("t1.0","$ S2 t1")] has_type.LETI 1);
by (simp_tac (simpset() addsimps [o_def]) 1);
by (simp_tac (HOL_ss addsimps [subst_comp_scheme_list RS sym]) 1);
by (rtac (has_type_cl_sub RS spec) 1);
by (dres_inst_tac [("x","A")] spec 1);
by (dres_inst_tac [("x","S1")] spec 1);
by (dres_inst_tac [("x","t1")] spec 1);
by (dres_inst_tac [("x","m2")] spec 1);
by (rotate_tac 4 1);
by (dres_inst_tac [("x","m1")] spec 1);
by (mp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [eq_sym_conv]) 1);
by (simp_tac (simpset() addsimps [o_def]) 1);
by (simp_tac (HOL_ss addsimps [subst_comp_scheme_list RS sym]) 1);
by (rtac (gen_subst_commutes RS sym RS subst) 1);
by (rtac (app_subst_Cons RS subst) 2);
by (etac thin_rl 2);
by (dres_inst_tac [("x","gen ($S1 A) t1 # $ S1 A")] spec 2);
by (dres_inst_tac [("x","S2")] spec 2);
by (dres_inst_tac [("x","t")] spec 2);
by (dres_inst_tac [("x","n2")] spec 2);
by (dres_inst_tac [("x","m2")] spec 2);
by (forward_tac [new_tv_W] 2);
by (assume_tac 2);
by (dtac conjunct1 2);
by (dtac conjunct1 2);
by (forward_tac [new_tv_subst_scheme_list] 2);
by (rtac new_scheme_list_le 2);
by (rtac W_var_ge 2);
by (assume_tac 2);
by (assume_tac 2);
by (etac impE 2);
by (res_inst_tac [("A","$ S1 A")] new_tv_only_depends_on_free_tv_scheme_list 2);
by (Simp_tac 2);
by (Fast_tac 2);
by (assume_tac 2);
by (Asm_full_simp_tac 2);
by (rtac weaken_A_Int_B_eq_empty 1);
by (rtac allI 1);
by (strip_tac 1);
by (rtac weaken_not_elem_A_minus_B 1);
by (case_tac "x < m2" 1);
by (rtac disjI2 1);
by (rtac (free_tv_gen_cons RS subst) 1);
by (rtac free_tv_W 1);
by (assume_tac 1);
by (Asm_full_simp_tac 1);
by (assume_tac 1);
by (rtac disjI1 1);
by (dtac new_tv_W 1);
by (assume_tac 1);
by (dtac conjunct2 1);
by (dtac conjunct2 1);
by (rtac new_tv_not_free_tv 1);
by (rtac new_tv_le 1);
by (assume_tac 2);
by (asm_full_simp_tac (simpset() addsimps [not_less_iff_le]) 1);
qed_spec_mp "W_correct_lemma";

(* Completeness of W w.r.t. has_type *)
Goal "!S' A t' n. $S' A |- e :: t' --> new_tv n A -->     \
\             (? S t. (? m. W e A n = Some (S,t,m)) &  \
\                     (? R. $S' A = $R ($S A) & t' = $R t))";
by (induct_tac "e" 1);
(* case Var n *)
by (strip_tac 1);
by (simp_tac (simpset() addcongs [conj_cong]) 1);
by (eresolve_tac has_type_casesE 1); 
by (asm_full_simp_tac (simpset() addsimps [is_bound_typ_instance]) 1);
by (etac exE 1);
by (hyp_subst_tac 1);
by (rename_tac "S" 1);
by (res_inst_tac [("x","%x. (if x < n then S' x else S (x - n))")] exI 1);
by (rtac conjI 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [(bound_typ_inst_composed_subst RS sym),new_tv_nth_nat_A,o_def,nth_subst] 
                           delsimps [bound_typ_inst_composed_subst]) 1);
(** LEVEL 12 **)
(* case Abs e *)
by (strip_tac 1);
by (eresolve_tac has_type_casesE 1);
by (eres_inst_tac [("x","%x. if x=n then t1 else (S' x)")] allE 1);
by (eres_inst_tac [("x","(FVar n)#A")] allE 1);
by (eres_inst_tac [("x","t2")] allE 1);
by (eres_inst_tac [("x","Suc n")] allE 1);
by (best_tac (HOL_cs addSDs [mk_scheme_injective] 
                  addss (simpset() addcongs [conj_cong] 
                                addsplits [split_option_bind])) 1);
(** LEVEL 19 **)

(* case App e1 e2 *)
by (strip_tac 1);
by (eresolve_tac has_type_casesE 1);
by (eres_inst_tac [("x","S'")] allE 1);
by (eres_inst_tac [("x","A")] allE 1);
by (eres_inst_tac [("x","t2 -> t'")] allE 1);
by (eres_inst_tac [("x","n")] allE 1);
by (safe_tac HOL_cs);
(** LEVEL 26 **)
by (eres_inst_tac [("x","R")] allE 1);
by (eres_inst_tac [("x","$ S A")] allE 1);
by (eres_inst_tac [("x","t2")] allE 1);
by (eres_inst_tac [("x","m")] allE 1);
by (Asm_full_simp_tac 1);
by (safe_tac HOL_cs);
by (fast_tac (HOL_cs addIs [sym RS W_var_geD,new_tv_W RS
        conjunct1,new_scheme_list_le,new_tv_subst_scheme_list]) 1);
(** LEVEL 33 **)
by (subgoal_tac
  "$ (%x. if x=ma then t' else (if x:(free_tv t - free_tv Sa) then R x \
\        else Ra x)) ($ Sa t) = \
\  $ (%x. if x=ma then t' else (if x:(free_tv t - free_tv Sa) then R x \
\        else Ra x)) (ta -> (TVar ma))" 1);
by (res_inst_tac [("t","$ (%x. if x = ma then t' else \
\   (if x:(free_tv t - free_tv Sa) then R x else Ra x)) ($ Sa t)"),
    ("s","($ Ra ta) -> t'")] ssubst 2);
by (asm_simp_tac (simpset() addsimps [subst_comp_te]) 2);
by (rtac eq_free_eq_subst_te 2);  
by (strip_tac 2);
by (subgoal_tac "na ~=ma" 2);
by (best_tac (HOL_cs addDs [new_tv_W,sym RS W_var_geD,
    new_tv_not_free_tv,new_tv_le]) 3);
by (case_tac "na:free_tv Sa" 2);
(* n1 ~: free_tv S1 *)
by (forward_tac [not_free_impl_id] 3);
by (Asm_simp_tac 3);
(* na : free_tv Sa *)
by (dres_inst_tac [("A1","$ S A")] (subst_comp_scheme_list RSN (2,trans)) 2);
by (dtac eq_subst_scheme_list_eq_free 2);
by (fast_tac (HOL_cs addIs [free_tv_W,free_tv_le_new_tv] addDs [new_tv_W]) 2);
by (Asm_simp_tac 2); 
by (case_tac "na:dom Sa" 2);
(* na ~: dom Sa *)
by (asm_full_simp_tac (simpset() addsimps [dom_def]) 3);
(* na : dom Sa *)
by (rtac eq_free_eq_subst_te 2);
by (strip_tac 2);
by (subgoal_tac "nb ~= ma" 2);
by ((forward_tac [new_tv_W] 3) THEN (atac 3));
by (etac conjE 3);
by (dtac new_tv_subst_scheme_list 3);
by (fast_tac (HOL_cs addIs [new_scheme_list_le] addDs [sym RS W_var_geD]) 3);
by (fast_tac (set_cs addDs [new_tv_W,new_tv_not_free_tv] addss 
    (simpset() addsimps [cod_def,free_tv_subst])) 3);
by (fast_tac (set_cs addss (simpset() addsimps [cod_def,free_tv_subst])) 2);
by (Simp_tac 2);  
by (rtac eq_free_eq_subst_te 2);
by (strip_tac 2 );
by (subgoal_tac "na ~= ma" 2);
by ((forward_tac [new_tv_W] 3) THEN (atac 3));
by (etac conjE 3);
by (dtac (sym RS W_var_geD) 3);
by (fast_tac (HOL_cs addDs [new_scheme_list_le,new_tv_subst_scheme_list,new_tv_W,new_tv_not_free_tv]) 3);
by (case_tac "na: free_tv t - free_tv Sa" 2);
(* case na ~: free_tv t - free_tv Sa *)
by (Asm_full_simp_tac 3);
by (Fast_tac 3);
(* case na : free_tv t - free_tv Sa *)
by (Asm_full_simp_tac 2);
by (dres_inst_tac [("A1","$ S A")] (subst_comp_scheme_list RSN (2,trans)) 2);
by (dtac eq_subst_scheme_list_eq_free 2);
by (fast_tac (HOL_cs addIs [free_tv_W,free_tv_le_new_tv] addDs [new_tv_W]) 2);
(** LEVEL 73 **)
by (asm_full_simp_tac (simpset() addsimps [free_tv_subst,dom_def]) 2);
by (asm_simp_tac (simpset() addsplits [split_option_bind]) 1); 
by (safe_tac HOL_cs );
by (dtac mgu_Some 1);
by ( fast_tac (HOL_cs addss simpset()) 1);
(** LEVEL 78 *)
by ((dtac mgu_mg 1) THEN (atac 1));
by (etac exE 1);
by (res_inst_tac [("x","Rb")] exI 1);
by (rtac conjI 1);
by (dres_inst_tac [("x","ma")] fun_cong 2);
by ( asm_full_simp_tac (simpset() addsimps [eq_sym_conv]) 2);
by (simp_tac (simpset() addsimps [subst_comp_scheme_list]) 1);
by (simp_tac (simpset() addsimps [subst_comp_scheme_list RS sym]) 1);
by (res_inst_tac [("A2","($ Sa ($ S A))")]
       ((subst_comp_scheme_list RS sym) RSN (2,trans)) 1);
by ( asm_full_simp_tac (simpset() addsimps [o_def,eq_sym_conv]) 1);
by (dres_inst_tac [("s","Some ?X")] sym 1);
by (rtac eq_free_eq_subst_scheme_list 1);
by ( safe_tac HOL_cs );
by (subgoal_tac "ma ~= na" 1);
by ((forward_tac [new_tv_W] 2) THEN (atac 2));
by (etac conjE 2);
by (dtac new_tv_subst_scheme_list 2);
by (fast_tac (HOL_cs addIs [new_scheme_list_le] addDs [sym RS W_var_geD]) 2);
by (forw_inst_tac [("n","m")] new_tv_W 2  THEN  atac 2);
by (etac conjE 2);
by (dtac (free_tv_app_subst_scheme_list RS subsetD) 2);
by (fast_tac (set_cs addDs [sym RS W_var_geD,new_scheme_list_le,codD,
    new_tv_not_free_tv]) 2);
by (case_tac "na: free_tv t - free_tv Sa" 1);
(* case na ~: free_tv t - free_tv Sa *)
by (Asm_full_simp_tac 2);
(* case na : free_tv t - free_tv Sa *)
by (Asm_full_simp_tac 1);
by (dtac (free_tv_app_subst_scheme_list RS subsetD) 1);
by (fast_tac (set_cs addDs [codD,subst_comp_scheme_list RSN (2,trans),
    eq_subst_scheme_list_eq_free] addss ((simpset() addsimps 
    [free_tv_subst,dom_def]))) 1);
by (Fast_tac 1);
(* case Let e1 e2 *)
by (eresolve_tac has_type_casesE 1);
by (eres_inst_tac [("x","S'")] allE 1);
by (eres_inst_tac [("x","A")] allE 1);
by (eres_inst_tac [("x","t1")] allE 1);
by (eres_inst_tac [("x","n")] allE 1);
by (mp_tac 1);
by (mp_tac 1);
by (safe_tac HOL_cs);
by (Asm_simp_tac 1); 
by (eres_inst_tac [("x","R")] allE 1);
by (eres_inst_tac [("x","gen ($ S A) t # $ S A")] allE 1);
by (eres_inst_tac [("x","t'")] allE 1);
by (eres_inst_tac [("x","m")] allE 1);
by (Asm_full_simp_tac 1);
by (dtac mp 1);
by (rtac has_type_le_env 1);
by (assume_tac 1);
by (Simp_tac 1);
by (rtac gen_bound_typ_instance 1);
by (dtac mp 1);
by (forward_tac [new_tv_compatible_W] 1);
by (rtac sym 1);
by (assume_tac 1);
by (fast_tac (claset() addDs [new_tv_compatible_gen,new_tv_subst_scheme_list,new_tv_W]) 1);
by (safe_tac HOL_cs);
by (Asm_full_simp_tac 1);
by (res_inst_tac [("x","Ra")] exI 1);
by (simp_tac (simpset() addsimps [o_def,subst_comp_scheme_list RS sym]) 1);
qed_spec_mp "W_complete_lemma";

Goal "[] |- e :: t' ==>  (? S t. (? m. W e [] n = Some(S,t,m)) &  \
\                                 (? R. t' = $ R t))";
by (cut_inst_tac [("A","[]"),("S'","id_subst"),("e","e"),("t'","t'")]
                W_complete_lemma 1);
by (ALLGOALS Asm_full_simp_tac);
qed "W_complete";
