(* Title:     HOL/MiniML/MiniML.ML
   ID:        $Id$
   Author:    Dieter Nazareth and Tobias Nipkow
   Copyright  1995 TU Muenchen
*)

Addsimps has_type.intrs;
Addsimps [Un_upper1,Un_upper2];

Addsimps [is_bound_typ_instance_closed_subst];


goal thy "!!t::typ. $(%n. if n : (free_tv A) Un (free_tv t) then (S n) else (TVar n)) t = $S t";
by (rtac typ_substitutions_only_on_free_variables 1);
by (asm_full_simp_tac (simpset() addsimps [Ball_def]) 1);
qed "s'_t_equals_s_t";

Addsimps [s'_t_equals_s_t];

goal thy "!!A::type_scheme list. $(%n. if n : (free_tv A) Un (free_tv t) then (S n) else (TVar n)) A = $S A";
by (rtac scheme_list_substitutions_only_on_free_variables 1);
by (asm_full_simp_tac (simpset() addsimps [Ball_def]) 1);
qed "s'_a_equals_s_a";

Addsimps [s'_a_equals_s_a];

goal thy "!!S.($ (%n. if n : (free_tv A) Un (free_tv t) then (S n) else (TVar n)) A |- e :: \ 
\              $ (%n. if n : (free_tv A) Un (free_tv t) then (S n) else (TVar n)) t) ==> \
\             $S A |- e :: $S t";

by (res_inst_tac [("P","%A. A |- e :: $S t")] ssubst 1);
by (rtac (s'_a_equals_s_a RS sym) 1);
by (res_inst_tac [("P","%t. $ (%n. if n : free_tv A Un free_tv (?t1 S) then S n else TVar n) A |- e :: t")] ssubst 1);
by (rtac (s'_t_equals_s_t RS sym) 1);
by (Asm_full_simp_tac 1);
qed "replace_s_by_s'";

goal thy "!!A::type_scheme list. $ (%x. TVar (if x : free_tv A then x else n + x)) A = $ id_subst A";
by (rtac scheme_list_substitutions_only_on_free_variables 1);
by (asm_full_simp_tac (simpset() addsimps [id_subst_def]) 1);
qed "alpha_A'";

goal thy "!!A::type_scheme list. $ (%x. TVar (if x : free_tv A then x else n + x)) A = A";
by (rtac (alpha_A' RS ssubst) 1);
by (Asm_full_simp_tac 1);
qed "alpha_A";

goal thy "!!alpha. $ (S o alpha) (t::typ) = $ S ($ (%x. TVar (alpha x)) t)";
by (typ.induct_tac "t" 1);
by (ALLGOALS (Asm_full_simp_tac));
qed "S_o_alpha_typ";

goal thy "!!alpha. $ (%u. (S o alpha) u) (t::typ) = $ S ($ (%x. TVar (alpha x)) t)";
by (typ.induct_tac "t" 1);
by (ALLGOALS (Asm_full_simp_tac));
val S_o_alpha_typ' = result ();

goal thy "!!alpha. $ (S o alpha) (sch::type_scheme) = $ S ($ (%x. TVar (alpha x)) sch)";
by (type_scheme.induct_tac "sch" 1);
by (ALLGOALS (Asm_full_simp_tac));
qed "S_o_alpha_type_scheme";

goal thy "!!alpha. $ (S o alpha) (A::type_scheme list) = $ S ($ (%x. TVar (alpha x)) A)";
by (list.induct_tac "A" 1);
by (ALLGOALS (Asm_full_simp_tac));
by (rtac (rewrite_rule [o_def] S_o_alpha_type_scheme) 1);
qed "S_o_alpha_type_scheme_list";

goal thy "!!A::type_scheme list. \
\              ($ (%n. if n : free_tv A Un free_tv t \
\                      then S n else TVar n) \
\                 A) = \
\              ($ ((%x. if x : free_tv A Un free_tv t then S x \
\                       else TVar x) o \
\                  (%x. if x : free_tv A \
\                       then x else n + x)) A)";
by (stac S_o_alpha_type_scheme_list 1);
by (stac alpha_A 1);
by (rtac refl 1);
qed "S'_A_eq_S'_alpha_A";

goalw thy [free_tv_subst,dom_def]
          "!!A. dom (%n. if n : free_tv A Un free_tv t then S n else TVar n) <= \
\               free_tv A Un free_tv t";
by (Simp_tac 1);
by (Fast_tac 1);
qed "dom_S'";

goalw thy [free_tv_subst,cod_def,subset_def]
          "!!(A::type_scheme list) (t::typ). \ 
\              cod (%n. if n : free_tv A Un free_tv t then S n else TVar n) <= \
\              free_tv ($ S A) Un free_tv ($ S t)";
by (rtac ballI 1);
by (etac UN_E 1);
by (dtac (dom_S' RS subsetD) 1);
by (rotate_tac 1 1);
by (Asm_full_simp_tac 1);
by (fast_tac (claset() addDs [free_tv_of_substitutions_extend_to_scheme_lists] 
                      addIs [free_tv_of_substitutions_extend_to_types RS subsetD]) 1);
qed "cod_S'";

goalw thy [free_tv_subst]
          "!!(A::type_scheme list) (t::typ). \
\               free_tv (%n. if n : free_tv A Un free_tv t then S n else TVar n) <= \
\               free_tv A Un free_tv ($ S A) Un free_tv t Un free_tv ($ S t)";
by (fast_tac (claset() addDs [dom_S' RS subsetD,cod_S' RS subsetD]) 1);
qed "free_tv_S'";

goal thy "!!t1::typ. \
\         (free_tv ($ (%x. TVar (if x : free_tv A then x else n + x)) t1) - free_tv A) <= \
\         {x. ? y. x = n + y}";
by (typ.induct_tac "t1" 1);
by (Simp_tac 1);
by (Fast_tac 1);
by (Simp_tac 1);
by (Fast_tac 1);
qed "free_tv_alpha";

goal thy "!!(k::nat). n <= n + k";
by (res_inst_tac [("n","k")] nat_induct 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
val aux_plus = result();

Addsimps [aux_plus];

goal thy "!!t::typ. new_tv n t ==> {x. ? y. x = n + y} Int free_tv t = {}";
by Safe_tac;
by (cut_facts_tac [aux_plus] 1);
by (dtac new_tv_le 1);
by (assume_tac 1);
by (rotate_tac 1 1);
by (dtac new_tv_not_free_tv 1);
by (Fast_tac 1);
val new_tv_Int_free_tv_empty_type = result ();

goal thy "!!sch::type_scheme. new_tv n sch ==> {x. ? y. x = n + y} Int free_tv sch = {}";
by Safe_tac;
by (cut_facts_tac [aux_plus] 1);
by (dtac new_tv_le 1);
by (assume_tac 1);
by (rotate_tac 1 1);
by (dtac new_tv_not_free_tv 1);
by (Fast_tac 1);
val new_tv_Int_free_tv_empty_scheme = result ();

goal thy "!!n. !A::type_scheme list. new_tv n A --> {x. ? y. x = n + y} Int free_tv A = {}";
by (rtac allI 1);
by (list.induct_tac "A" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (fast_tac (claset() addDs [new_tv_Int_free_tv_empty_scheme ]) 1);
val new_tv_Int_free_tv_empty_scheme_list = result ();

goalw thy [le_type_scheme_def,is_bound_typ_instance] 
      "!!A. new_tv n A --> gen A t <= gen A ($ (%x. TVar (if x : free_tv A then x else n + x)) t)";
by (strip_tac 1);
by (etac exE 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("x","(%x. S (if n <= x then x - n else x))")] exI 1);
by (typ.induct_tac "t" 1);
by (Simp_tac 1);
by (case_tac "nat : free_tv A" 1);
by (Asm_simp_tac 1);
by (subgoal_tac "n <= n + nat" 1);
by (dtac new_tv_le 1);
by (assume_tac 1);
by (dtac new_tv_not_free_tv 1);
by (dtac new_tv_not_free_tv 1);
by (asm_simp_tac (simpset() addsimps [diff_add_inverse ]) 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed_spec_mp "gen_t_le_gen_alpha_t";

AddSIs has_type.intrs;

goal thy "!!e. A |- e::t ==> !B. A <= B -->  B |- e::t";
by (etac has_type.induct 1);
   by (simp_tac (simpset() addsimps [le_env_def]) 1);
   by (fast_tac (claset() addEs [bound_typ_instance_trans] addss simpset()) 1);
  by (Asm_full_simp_tac 1);
 by (Fast_tac 1);
by (slow_tac (claset() addEs [le_env_free_tv RS free_tv_subset_gen_le]) 1);
qed_spec_mp "has_type_le_env";

(* has_type is closed w.r.t. substitution *)
goal thy "!!a. A |- e :: t ==> !S. $S A |- e :: $S t";
by (etac has_type.induct 1);
(* case VarI *)
   by (rtac allI 1);
   by (rtac has_type.VarI 1);
    by (asm_full_simp_tac (simpset() addsimps [app_subst_list]) 1);
   by (asm_simp_tac (simpset() addsimps [app_subst_list]) 1);
  (* case AbsI *)
  by (rtac allI 1);
  by (Simp_tac 1);  
  by (rtac has_type.AbsI 1);
  by (Asm_full_simp_tac 1);
 (* case AppI *)
 by (rtac allI 1);
 by (rtac has_type.AppI 1);
  by (Asm_full_simp_tac 1);
  by (etac spec 1);
 by (etac spec 1);
(* case LetI *)
by (rtac allI 1);
by (rtac replace_s_by_s' 1);
by (cut_inst_tac [("A","$ S A"), 
                  ("A'","A"),
                  ("t","t"),
                  ("t'","$ S t")] 
                 ex_fresh_variable 1);
by (etac exE 1);
by (REPEAT (etac conjE 1));
by (res_inst_tac [("t1.0","$((%x. if x : free_tv A Un free_tv t then S x else TVar x) o \
\                            (%x. if x : free_tv A then x else n + x)) t1")] 
                 has_type.LETI 1);
 by (dres_inst_tac [("x","(%x. if x : free_tv A Un free_tv t then S x else TVar x) o \
\                         (%x. if x : free_tv A then x else n + x)")] spec 1);
 val o_apply = prove_goalw HOL.thy [o_def] "(f o g) x = f (g x)"
 (fn _ => [rtac refl 1]);
 by (stac (S'_A_eq_S'_alpha_A) 1);
 by (assume_tac 1);
by (stac S_o_alpha_typ 1);
by (stac gen_subst_commutes 1);
 by (rtac subset_antisym 1);
  by (rtac subsetI 1);
  by (etac IntE 1);
  by (dtac (free_tv_S' RS subsetD) 1);
  by (dtac (free_tv_alpha RS subsetD) 1);
  by (Asm_full_simp_tac 1);
  by (etac exE 1);
  by (hyp_subst_tac 1);
  by (subgoal_tac "new_tv (n + y) ($ S A)" 1);
   by (subgoal_tac "new_tv (n + y) ($ S t)" 1);
    by (subgoal_tac "new_tv (n + y) A" 1);
     by (subgoal_tac "new_tv (n + y) t" 1);
      by (REPEAT (dtac new_tv_not_free_tv 1));
      by (Fast_tac 1);
     by (REPEAT ((rtac new_tv_le 1) THEN (assume_tac 2) THEN (Simp_tac 1)));
 by (Fast_tac 1);
by (rtac has_type_le_env 1);
 by (dtac spec 1);
 by (dtac spec 1);
 by (assume_tac 1);
by (rtac (app_subst_Cons RS subst) 1);
by (rtac S_compatible_le_scheme_lists 1);
by (Asm_simp_tac 1);
qed "has_type_cl_sub";
