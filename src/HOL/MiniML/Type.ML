(* Title:     HOL/MiniML/Type.thy
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

Addsimps [mgu_eq,mgu_mg,mgu_free];


(* lemmata for make scheme *)

goal thy "mk_scheme t = sch1 =-> sch2 --> (? t1 t2. sch1 = mk_scheme t1 & sch2 = mk_scheme t2)";
by (typ.induct_tac "t" 1);
by (Simp_tac 1);
by (Asm_full_simp_tac 1);
by (Fast_tac 1);
qed_spec_mp "mk_scheme_Fun";

goal thy "!t'. mk_scheme t = mk_scheme t' --> t=t'";
by (typ.induct_tac "t" 1);
 by (rtac allI 1);
 by (typ.induct_tac "t'" 1);
  by (Simp_tac 1);
 by (Asm_full_simp_tac 1);
by (rtac allI 1);
by (typ.induct_tac "t'" 1);
 by (Simp_tac 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "mk_scheme_injective";

goal thy "!!t. free_tv (mk_scheme t) = free_tv t";
by (typ.induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "free_tv_mk_scheme";

Addsimps [free_tv_mk_scheme];

goal thy "!!t. $ S (mk_scheme t) = mk_scheme ($ S t)";
by (typ.induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "subst_mk_scheme";

Addsimps [subst_mk_scheme];


(* constructor laws for app_subst *)

goalw thy [app_subst_list]
  "$ S [] = []";
by (Simp_tac 1);
qed "app_subst_Nil";

goalw thy [app_subst_list]
  "$ S (x#l) = ($ S x)#($ S l)";
by (Simp_tac 1);
qed "app_subst_Cons";

Addsimps [app_subst_Nil,app_subst_Cons];


(* constructor laws for new_tv *)

goalw thy [new_tv_def]
  "new_tv n (TVar m) = (m<n)";
by (fast_tac (HOL_cs addss !simpset) 1);
qed "new_tv_TVar";

goalw thy [new_tv_def]
  "new_tv n (FVar m) = (m<n)";
by (fast_tac (HOL_cs addss !simpset) 1);
qed "new_tv_FVar";

goalw thy [new_tv_def]
  "new_tv n (BVar m) = True";
by (Simp_tac 1);
qed "new_tv_BVar";

goalw thy [new_tv_def]
  "new_tv n (t1 -> t2) = (new_tv n t1 & new_tv n t2)";
by (fast_tac (HOL_cs addss !simpset) 1);
qed "new_tv_Fun";

goalw thy [new_tv_def]
  "new_tv n (t1 =-> t2) = (new_tv n t1 & new_tv n t2)";
by (fast_tac (HOL_cs addss !simpset) 1);
qed "new_tv_Fun2";

goalw thy [new_tv_def]
  "new_tv n []";
by (Simp_tac 1);
qed "new_tv_Nil";

goalw thy [new_tv_def]
  "new_tv n (x#l) = (new_tv n x & new_tv n l)";
by (fast_tac (HOL_cs addss !simpset) 1);
qed "new_tv_Cons";

goalw thy [new_tv_def] "!!n. new_tv n TVar";
by (strip_tac 1);
by (asm_full_simp_tac (!simpset addsimps [free_tv_subst,dom_def,cod_def]) 1);
qed "new_tv_TVar_subst";

Addsimps [new_tv_TVar,new_tv_FVar,new_tv_BVar,new_tv_Fun,new_tv_Fun2,new_tv_Nil,new_tv_Cons,new_tv_TVar_subst];

goalw thy [id_subst_def,new_tv_def,free_tv_subst,dom_def,cod_def]
  "new_tv n id_subst";
by (Simp_tac 1);
qed "new_tv_id_subst";
Addsimps[new_tv_id_subst];

goal thy "new_tv n (sch::type_scheme) --> \
\              $(%k. if k<n then S k else S' k) sch = $S sch";
by (type_scheme.induct_tac "sch" 1);
by (ALLGOALS Asm_simp_tac);
qed "new_if_subst_type_scheme";
Addsimps [new_if_subst_type_scheme];

goal thy "new_tv n (A::type_scheme list) --> \
\              $(%k. if k<n then S k else S' k) A = $S A";
by (list.induct_tac "A" 1);
by (ALLGOALS Asm_simp_tac);
qed "new_if_subst_type_scheme_list";
Addsimps [new_if_subst_type_scheme_list];


(* constructor laws for dom and cod *)

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


(* lemmata for free_tv *)

goalw thy [free_tv_subst]
  "free_tv id_subst = {}";
by (Simp_tac 1);
qed "free_tv_id_subst";
Addsimps [free_tv_id_subst];

goal thy "!!A. !n. n < length A --> x : free_tv (nth n A) --> x : free_tv A";
by (list.induct_tac "A" 1);
by (Asm_full_simp_tac 1);
by (rtac allI 1);
by (res_inst_tac [("n","n")] nat_induct 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "free_tv_nth_A_impl_free_tv_A";

Addsimps [free_tv_nth_A_impl_free_tv_A];

goal thy "!!A. !nat. nat < length A --> x : free_tv (nth nat A) --> x : free_tv A";
by (list.induct_tac "A" 1);
by (Asm_full_simp_tac 1);
by (rtac allI 1);
by (res_inst_tac [("n","nat")] nat_induct 1);
by (strip_tac 1);
by (Asm_full_simp_tac 1);
by (Simp_tac 1);
qed_spec_mp "free_tv_nth_nat_A";


(* if two substitutions yield the same result if applied to a type
   structure the substitutions coincide on the free type variables
   occurring in the type structure *)

goal thy "!!S S'. (!x:free_tv t. (S x) = (S' x)) --> $ S (t::typ) = $ S' t";
by (typ.induct_tac "t" 1);
by (Simp_tac 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "typ_substitutions_only_on_free_variables";

goal thy
  "!!t. (!n. n:(free_tv t) --> S1 n = S2 n) ==> $ S1 (t::typ) = $ S2 t";
by (rtac typ_substitutions_only_on_free_variables 1);
by (simp_tac (!simpset addsimps [Ball_def]) 1);
qed "eq_free_eq_subst_te";

goal thy "!!S S'. (!x:free_tv sch. (S x) = (S' x)) --> $ S (sch::type_scheme) = $ S' sch";
by (type_scheme.induct_tac "sch" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "scheme_substitutions_only_on_free_variables";

goal thy
  "!!sch. (!n. n:(free_tv sch) --> S1 n = S2 n) ==> $ S1 (sch::type_scheme) = $ S2 sch";
by (rtac scheme_substitutions_only_on_free_variables 1);
by (simp_tac (!simpset addsimps [Ball_def]) 1);
qed "eq_free_eq_subst_type_scheme";

goal thy
  "(!n. n:(free_tv A) --> S1 n = S2 n) --> $S1 (A::type_scheme list) = $S2 A";
by (list.induct_tac "A" 1); 
(* case [] *)
by (fast_tac (HOL_cs addss !simpset) 1);
(* case x#xl *)
by (fast_tac (HOL_cs addIs [eq_free_eq_subst_type_scheme] addss (!simpset)) 1);
qed_spec_mp "eq_free_eq_subst_scheme_list";

goal thy "!!P Q. ((!x:A. (P x)) --> Q) ==> ((!x:A Un B. (P x)) --> Q)";
by (Fast_tac 1);
val weaken_asm_Un = result ();

goal thy "!!S S'. (!x:free_tv A. (S x) = (S' x)) --> $ S (A::type_scheme list) = $ S' A";
by (list.induct_tac "A" 1);
by (Simp_tac 1);
by (Asm_full_simp_tac 1);
by (rtac weaken_asm_Un 1);
by (strip_tac 1);
by (etac scheme_substitutions_only_on_free_variables 1);
qed_spec_mp "scheme_list_substitutions_only_on_free_variables";

goal thy
  "$ S1 (t::typ) = $ S2 t --> n:(free_tv t) --> S1 n = S2 n";
by (typ.induct_tac "t" 1);
(* case TVar n *)
by (fast_tac (HOL_cs addss !simpset) 1);
(* case Fun t1 t2 *)
by (fast_tac (HOL_cs addss !simpset) 1);
qed_spec_mp "eq_subst_te_eq_free";

goal thy
  "$ S1 (sch::type_scheme) = $ S2 sch --> n:(free_tv sch) --> S1 n = S2 n";
by (type_scheme.induct_tac "sch" 1);
(* case TVar n *)
by (Asm_simp_tac 1);
(* case BVar n *)
by (strip_tac 1);
by (etac mk_scheme_injective 1);
by (Asm_simp_tac 1);
(* case Fun t1 t2 *)
by (Asm_full_simp_tac 1);
qed_spec_mp "eq_subst_type_scheme_eq_free";

goal thy
  "$S1 (A::type_scheme list) = $S2 A --> n:(free_tv A) --> S1 n = S2 n";
by (list.induct_tac "A" 1);
(* case [] *)
by (fast_tac (HOL_cs addss !simpset) 1);
(* case x#xl *)
by (fast_tac (HOL_cs addIs [eq_subst_type_scheme_eq_free] addss (!simpset)) 1);
qed_spec_mp "eq_subst_scheme_list_eq_free";

goalw thy [free_tv_subst] 
      "!!v. v : cod S ==> v : free_tv S";
by (fast_tac set_cs 1);
qed "codD";
 
goalw thy [free_tv_subst,dom_def] 
      "!! x. x ~: free_tv S ==> S x = TVar x";
by (fast_tac set_cs 1);
qed "not_free_impl_id";

goalw thy [new_tv_def] 
      "!! n. [| new_tv n t; m:free_tv t |] ==> m<n";
by (fast_tac HOL_cs 1 );
qed "free_tv_le_new_tv";

goalw thy [dom_def,cod_def,UNION_def,Bex_def]
  "!!v. [| v : free_tv(S n); v~=n |] ==> v : cod S";
by (Simp_tac 1);
by (safe_tac (empty_cs addSIs [exI,conjI,notI]));
by (assume_tac 2);
by (rotate_tac 1 1);
by (Asm_full_simp_tac 1);
qed "cod_app_subst";
Addsimps [cod_app_subst];

goal thy 
     "free_tv (S (v::nat)) <= insert v (cod S)";
by (expand_case_tac "v:dom S" 1);
by (fast_tac (set_cs addss (!simpset addsimps [cod_def])) 1);
by (fast_tac (set_cs addss (!simpset addsimps [dom_def])) 1);
qed "free_tv_subst_var";

goal thy 
     "free_tv ($ S (t::typ)) <= cod S Un free_tv t";
by (typ.induct_tac "t" 1);
(* case TVar n *)
by (simp_tac (!simpset addsimps [free_tv_subst_var]) 1);
(* case Fun t1 t2 *)
by (fast_tac (set_cs addss !simpset) 1);
qed "free_tv_app_subst_te";     

goal thy 
     "free_tv ($ S (sch::type_scheme)) <= cod S Un free_tv sch";
by (type_scheme.induct_tac "sch" 1);
(* case FVar n *)
by (simp_tac (!simpset addsimps [free_tv_subst_var]) 1);
(* case BVar n *)
by (Simp_tac 1);
(* case Fun t1 t2 *)
by (fast_tac (set_cs addss !simpset) 1);
qed "free_tv_app_subst_type_scheme";  

goal thy 
     "free_tv ($ S (A::type_scheme list)) <= cod S Un free_tv A";
by (list.induct_tac "A" 1);
(* case [] *)
by (Simp_tac 1);
(* case a#al *)
by (cut_facts_tac [free_tv_app_subst_type_scheme] 1);
by (fast_tac (set_cs addss !simpset) 1);
qed "free_tv_app_subst_scheme_list";

goalw thy [free_tv_subst,dom_def]
     "free_tv (%u::nat. $ s1 (s2 u) :: typ) <=   \
\     free_tv s1 Un free_tv s2";
by (fast_tac (set_cs addSDs [free_tv_app_subst_te RS subsetD,
                             free_tv_subst_var RS subsetD] 
                     addss (!simpset delsimps bex_simps
                                     addsimps [cod_def,dom_def])) 1);
qed "free_tv_comp_subst";

goalw thy [o_def] 
     "free_tv ($ S1 o S2) <= free_tv S1 Un free_tv (S2 :: nat => typ)";
by (rtac free_tv_comp_subst 1);
qed "free_tv_o_subst";

goal thy "!!n. n : free_tv t --> free_tv (S n) <= free_tv ($ S t::typ)";
by (typ.induct_tac "t" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Fast_tac 1);
qed_spec_mp "free_tv_of_substitutions_extend_to_types";

goal thy "!!n. n : free_tv sch --> free_tv (S n) <= free_tv ($ S sch::type_scheme)";
by (type_scheme.induct_tac "sch" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Fast_tac 1);
qed_spec_mp "free_tv_of_substitutions_extend_to_schemes";

goal thy "!!n. n : free_tv A --> free_tv (S n) <= free_tv ($ S A::type_scheme list)";
by (list.induct_tac "A" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (fast_tac (!claset addDs [free_tv_of_substitutions_extend_to_schemes]) 1);
qed_spec_mp "free_tv_of_substitutions_extend_to_scheme_lists";

Addsimps [free_tv_of_substitutions_extend_to_scheme_lists];

goal thy "!!sch::type_scheme. (n : free_tv sch) = (n mem free_tv_ML sch)";
by (type_scheme.induct_tac "sch" 1);
by (ALLGOALS (asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
by (strip_tac 1);
by (Fast_tac 1);
qed "free_tv_ML_scheme";

goal thy "!!A::type_scheme list. (n : free_tv A) = (n mem free_tv_ML A)";
by (list.induct_tac "A" 1);
by (Simp_tac 1);
by (asm_simp_tac (!simpset addsimps [free_tv_ML_scheme]) 1);
qed "free_tv_ML_scheme_list";


(* lemmata for bound_tv *)

goal thy "!!t. bound_tv (mk_scheme t) = {}";
by (typ.induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "bound_tv_mk_scheme";

Addsimps [bound_tv_mk_scheme];

goal thy "!!sch::type_scheme. bound_tv ($ S sch) = bound_tv sch";
by (type_scheme.induct_tac "sch" 1);
by (ALLGOALS Asm_simp_tac);
qed "bound_tv_subst_scheme";

Addsimps [bound_tv_subst_scheme];

goal thy "!!A::type_scheme list. bound_tv ($ S A) = bound_tv A";
by (rtac list.induct 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "bound_tv_subst_scheme_list";

Addsimps [bound_tv_subst_scheme_list];


(* lemmata for new_tv *)

goalw thy [new_tv_def]
  "new_tv n S = ((!m. n <= m --> (S m = TVar m)) & \
\                (! l. l < n --> new_tv n (S l) ))";
by (safe_tac HOL_cs );
(* ==> *)
by (fast_tac (HOL_cs addDs [leD] addss (!simpset addsimps [free_tv_subst,dom_def])) 1);
by (subgoal_tac "m:cod S | S l = TVar l" 1);
by (safe_tac HOL_cs );
by (fast_tac (HOL_cs addDs [UnI2] addss (!simpset addsimps [free_tv_subst])) 1);
by (dres_inst_tac [("P","%x. m:free_tv x")] subst 1 THEN atac 1);
by (Asm_full_simp_tac 1);
by (fast_tac (set_cs addss (!simpset addsimps [free_tv_subst,cod_def,dom_def])) 1);
(* <== *)
by (rewrite_goals_tac [free_tv_subst,cod_def,dom_def] );
by (safe_tac set_cs );
by (cut_inst_tac [("m","m"),("n","n")] less_linear 1);
by (fast_tac (HOL_cs addSIs [less_or_eq_imp_le]) 1);
by (cut_inst_tac [("m","ma"),("n","n")] less_linear 1);
by (fast_tac (HOL_cs addSIs [less_or_eq_imp_le]) 1);
qed "new_tv_subst";

goal thy 
  "new_tv n  = list_all (new_tv n)";
by (rtac ext 1);
by (list.induct_tac "x" 1);
by (ALLGOALS Asm_simp_tac);
qed "new_tv_list";

(* substitution affects only variables occurring freely *)
goal thy
  "new_tv n (t::typ) --> $(%x. if x=n then t' else S x) t = $S t";
by (typ.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
qed "subst_te_new_tv";
Addsimps [subst_te_new_tv];

goal thy
  "new_tv n (sch::type_scheme) --> $(%x. if x=n then sch' else S x) sch = $S sch";
by (type_scheme.induct_tac "sch" 1);
by (ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
qed_spec_mp "subst_te_new_type_scheme";
Addsimps [subst_te_new_type_scheme];

goal thy
  "new_tv n (A::type_scheme list) --> $(%x. if x=n then t else S x) A = $S A";
by (list.induct_tac "A" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "subst_tel_new_scheme_list";
Addsimps [subst_tel_new_scheme_list];

(* all greater variables are also new *)
goalw thy [new_tv_def] 
  "!!n m. n<=m ==> new_tv n t ==> new_tv m t";
by (safe_tac (!claset));
by (dtac spec 1);
by (mp_tac 1);
by (trans_tac 1);
qed "new_tv_le";
Addsimps [lessI RS less_imp_le RS new_tv_le];

goal thy "!!n m. n<=m ==> new_tv n (t::typ) ==> new_tv m t";
by (asm_simp_tac (!simpset addsimps [new_tv_le]) 1);
qed "new_tv_typ_le";

goal thy "!!n m. n<=m ==> new_tv n (A::type_scheme list) ==> new_tv m A";
by (asm_simp_tac (!simpset addsimps [new_tv_le]) 1);
qed "new_scheme_list_le";

goal thy "!!n m. n<=m ==> new_tv n (S::subst) ==> new_tv m S";
by (asm_simp_tac (!simpset addsimps [new_tv_le]) 1);
qed "new_tv_subst_le";

(* new_tv property remains if a substitution is applied *)
goal thy
  "!!n. [| n<m; new_tv m (S::subst) |] ==> new_tv m (S n)";
by (asm_full_simp_tac (!simpset addsimps [new_tv_subst]) 1);
qed "new_tv_subst_var";

goal thy
  "new_tv n S --> new_tv n (t::typ) --> new_tv n ($ S t)";
by (typ.induct_tac "t" 1);
by (ALLGOALS(fast_tac (HOL_cs addss (!simpset addsimps [new_tv_subst]))));
qed_spec_mp "new_tv_subst_te";
Addsimps [new_tv_subst_te];

goal thy "new_tv n S --> new_tv n (sch::type_scheme) --> new_tv n ($ S sch)";
by (type_scheme.induct_tac "sch" 1);
by (ALLGOALS (Asm_full_simp_tac));
by (rewtac new_tv_def);
by (simp_tac (!simpset addsimps [free_tv_subst,dom_def,cod_def]) 1);
by (strip_tac 1);
by (case_tac "S nat = TVar nat" 1);
by (rotate_tac 3 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("x","m")] spec 1);
by (Fast_tac 1);
qed_spec_mp "new_tv_subst_type_scheme";
Addsimps [new_tv_subst_type_scheme];

goal thy
  "new_tv n S --> new_tv n (A::type_scheme list) --> new_tv n ($ S A)";
by (list.induct_tac "A" 1);
by (ALLGOALS(fast_tac (HOL_cs addss (!simpset))));
qed_spec_mp "new_tv_subst_scheme_list";
Addsimps [new_tv_subst_scheme_list];

goal thy
  "new_tv n A --> new_tv (Suc n) ((TVar n)#A)";
by (simp_tac (!simpset addsimps [new_tv_list]) 1);
by (list.induct_tac "A" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "new_tv_Suc_list";

goalw thy [new_tv_def] "!!sch::type_scheme. (free_tv sch) = (free_tv sch') --> (new_tv n sch --> new_tv n sch')";
by (Asm_simp_tac 1);
qed_spec_mp "new_tv_only_depends_on_free_tv_type_scheme";

goalw thy [new_tv_def] "!!A::type_scheme list. (free_tv A) = (free_tv A') --> (new_tv n A --> new_tv n A')";
by (Asm_simp_tac 1);
qed_spec_mp "new_tv_only_depends_on_free_tv_scheme_list";

goalw thy [new_tv_def] "!!A. !nat. nat < length A --> new_tv n A --> (new_tv n (nth nat A))";
by (list.induct_tac "A" 1);
by (Asm_full_simp_tac 1);
by (rtac allI 1);
by (res_inst_tac [("n","nat")] nat_induct 1);
by (strip_tac 1);
by (Asm_full_simp_tac 1);
by (Simp_tac 1);
qed_spec_mp "new_tv_nth_nat_A";


(* composition of substitutions preserves new_tv proposition *)
goal thy 
     "!! n. [| new_tv n (S::subst); new_tv n R |] ==> \
\           new_tv n (($ R) o S)";
by (asm_full_simp_tac (!simpset addsimps [new_tv_subst]) 1);
qed "new_tv_subst_comp_1";

goal thy
     "!! n. [| new_tv n (S::subst); new_tv n R |] ==>  \ 
\     new_tv n (%v.$ R (S v))";
by (asm_full_simp_tac (!simpset addsimps [new_tv_subst]) 1);
qed "new_tv_subst_comp_2";

Addsimps [new_tv_subst_comp_1,new_tv_subst_comp_2];

(* new type variables do not occur freely in a type structure *)
goalw thy [new_tv_def] 
      "!!n. new_tv n A ==> n~:(free_tv A)";
by (fast_tac (HOL_cs addEs [less_irrefl]) 1);
qed "new_tv_not_free_tv";
Addsimps [new_tv_not_free_tv];

goalw thy [max_def] "!!n::nat. m < n ==> m < max n n'";
by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (safe_tac (!claset));
by (trans_tac 1);
qed "less_maxL";

goalw thy [max_def] "!!n::nat. m < n' ==> m < max n n'";
by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (fast_tac (!claset addDs [not_leE] addIs [less_trans]) 1);
val less_maxR = result();

goalw thy [new_tv_def] "!!t::typ. ? n. (new_tv n t)";
by (typ.induct_tac "t" 1);
by (res_inst_tac [("x","Suc nat")] exI 1);
by (Asm_simp_tac 1);
by (REPEAT (etac exE 1));
by (rename_tac "n'" 1);
by (res_inst_tac [("x","max n n'")] exI 1);
by (Simp_tac 1);
by (fast_tac (!claset addIs [less_maxR,less_maxL]) 1);
qed "fresh_variable_types";

Addsimps [fresh_variable_types];

goalw thy [new_tv_def] "!!sch::type_scheme. ? n. (new_tv n sch)";
by (type_scheme.induct_tac "sch" 1);
by (res_inst_tac [("x","Suc nat")] exI 1);
by (Simp_tac 1);
by (res_inst_tac [("x","Suc nat")] exI 1);
by (Simp_tac 1);
by (REPEAT (etac exE 1));
by (rename_tac "n'" 1);
by (res_inst_tac [("x","max n n'")] exI 1);
by (Simp_tac 1);
by (fast_tac (!claset addIs [less_maxR,less_maxL]) 1);
qed "fresh_variable_type_schemes";

Addsimps [fresh_variable_type_schemes];

goalw thy [max_def] "!!n::nat. n <= (max n n')";
by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
val le_maxL = result();

goalw thy [max_def] "!!n'::nat. n' <= (max n n')";
by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (fast_tac (!claset addDs [not_leE] addIs [less_or_eq_imp_le]) 1);
val le_maxR = result();

goal thy "!!A::type_scheme list. ? n. (new_tv n A)";
by (list.induct_tac "A" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (etac exE 1);
by (cut_inst_tac [("sch","a")] fresh_variable_type_schemes 1);
by (etac exE 1);
by (rename_tac "n'" 1);
by (res_inst_tac [("x","(max n n')")] exI 1);
by (subgoal_tac "n <= (max n n')" 1);
by (subgoal_tac "n' <= (max n n')" 1);
by (fast_tac (!claset addDs [new_tv_le]) 1);
by (ALLGOALS (simp_tac (!simpset addsimps [le_maxR,le_maxL])));
qed "fresh_variable_type_scheme_lists";

Addsimps [fresh_variable_type_scheme_lists];

goal thy "!!x y. [| ? n1. (new_tv n1 x); ? n2. (new_tv n2 y)|] ==> ? n. (new_tv n x) & (new_tv n y)";
by (REPEAT (etac exE 1));
by (rename_tac "n1 n2" 1);
by (res_inst_tac [("x","(max n1 n2)")] exI 1);
by (subgoal_tac "n1 <= max n1 n2" 1);
by (subgoal_tac "n2 <= max n1 n2" 1);
by (fast_tac (!claset addDs [new_tv_le]) 1);
by (ALLGOALS (simp_tac (!simpset addsimps [le_maxL,le_maxR])));
qed "make_one_new_out_of_two";

goal thy "!!(A::type_scheme list) (A'::type_scheme list) (t::typ) (t'::typ). \
\         ? n. (new_tv n A) & (new_tv n A') & (new_tv n t) & (new_tv n t')" ;
by (cut_inst_tac [("t","t")] fresh_variable_types 1);
by (cut_inst_tac [("t","t'")] fresh_variable_types 1);
by (dtac make_one_new_out_of_two 1);
by (assume_tac 1);
by (thin_tac "? n. new_tv n t'" 1);
by (cut_inst_tac [("A","A")] fresh_variable_type_scheme_lists 1);
by (cut_inst_tac [("A","A'")] fresh_variable_type_scheme_lists 1);
by (rotate_tac 1 1);
by (dtac make_one_new_out_of_two 1);
by (assume_tac 1);
by (thin_tac "? n. new_tv n A'" 1);
by (REPEAT (etac exE 1));
by (rename_tac "n2 n1" 1);
by (res_inst_tac [("x","(max n1 n2)")] exI 1);
by (rewtac new_tv_def);
by (fast_tac (!claset addIs [less_maxL,less_maxR]) 1);
qed "ex_fresh_variable";

(* mgu does not introduce new type variables *)
goalw thy [new_tv_def] 
      "!! n. [|mgu t1 t2 = Some u; new_tv n t1; new_tv n t2|] ==> \
\            new_tv n u";
by (fast_tac (set_cs addDs [mgu_free]) 1);
qed "mgu_new";


(* lemmata for substitutions *)

goalw Type.thy [app_subst_list] 
   "!!A:: ('a::type_struct) list. length ($ S A) = length A";
by (Simp_tac 1);
qed "length_app_subst_list";
Addsimps [length_app_subst_list];

goal thy "!!sch::type_scheme. $ TVar sch = sch";
by (type_scheme.induct_tac "sch" 1);
by (ALLGOALS Asm_simp_tac);
qed "subst_TVar_scheme";

Addsimps [subst_TVar_scheme];

goal thy "!!A::type_scheme list. $ TVar A = A";
by (rtac list.induct 1);
by (ALLGOALS (asm_full_simp_tac (!simpset addsimps [app_subst_list])));
qed "subst_TVar_scheme_list";

Addsimps [subst_TVar_scheme_list];

(* application of id_subst does not change type expression *)
goalw thy [id_subst_def]
  "$ id_subst = (%t::typ. t)";
by (rtac ext 1);
by (typ.induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "app_subst_id_te";
Addsimps [app_subst_id_te];

goalw thy [id_subst_def]
  "$ id_subst = (%sch::type_scheme. sch)";
by (rtac ext 1);
by (type_scheme.induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "app_subst_id_type_scheme";
Addsimps [app_subst_id_type_scheme];

(* application of id_subst does not change list of type expressions *)
goalw thy [app_subst_list]
  "$ id_subst = (%A::type_scheme list. A)";
by (rtac ext 1); 
by (list.induct_tac "A" 1);
by (ALLGOALS Asm_simp_tac);
qed "app_subst_id_tel";
Addsimps [app_subst_id_tel];

goal thy "!!sch::type_scheme. $ id_subst sch = sch";
by (type_scheme.induct_tac "sch" 1);
by (ALLGOALS (asm_full_simp_tac (!simpset addsimps [id_subst_def])));
qed "id_subst_sch";

Addsimps [id_subst_sch];

goal thy "!!A::type_scheme list. $ id_subst A = A";
by (list.induct_tac "A" 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
qed "id_subst_A";

Addsimps [id_subst_A];

(* composition of substitutions *)
goalw Type.thy [id_subst_def,o_def] "$S o id_subst = S";
by (rtac ext 1);
by (Simp_tac 1);
qed "o_id_subst";
Addsimps[o_id_subst];

goal thy
  "$ R ($ S t::typ) = $ (%x. $ R (S x) ) t";
by (typ.induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "subst_comp_te";

goal thy
  "$ R ($ S sch::type_scheme) = $ (%x. $ R (S x) ) sch";
by (type_scheme.induct_tac "sch" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "subst_comp_type_scheme";

goalw thy [app_subst_list]
  "$ R ($ S A::type_scheme list) = $ (%x. $ R (S x)) A";
by (list.induct_tac "A" 1);
(* case [] *)
by (Simp_tac 1);
(* case x#xl *)
by (asm_full_simp_tac (!simpset addsimps [subst_comp_type_scheme]) 1);
qed "subst_comp_scheme_list";

goal thy "!!A::type_scheme list. !x : free_tv A. S x = (TVar x) ==> $ S A = $ id_subst A";
by (rtac scheme_list_substitutions_only_on_free_variables 1);
by (asm_full_simp_tac (!simpset addsimps [id_subst_def]) 1);
qed "subst_id_on_type_scheme_list'";

goal thy "!!A::type_scheme list. !x : free_tv A. S x = (TVar x) ==> $ S A = A";
by (stac subst_id_on_type_scheme_list' 1);
by (assume_tac 1);
by (Simp_tac 1);
qed "subst_id_on_type_scheme_list";

goal thy "!!n. !n. n < length A --> nth n ($ S A) = $S (nth n A)";
by (list.induct_tac "A" 1);
by (Asm_full_simp_tac 1);
by (rtac allI 1);
by (rename_tac "n1" 1);
by (res_inst_tac[("n","n1")] nat_induct 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "nth_subst";
