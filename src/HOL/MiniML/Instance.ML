(* Title:     HOL/MiniML/Instance.ML
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

(* lemmatas for instatiation *)


(* lemmatas for bound_typ_inst *)

goal thy "bound_typ_inst S (mk_scheme t) = t";
by (typ.induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "bound_typ_inst_mk_scheme";

Addsimps [bound_typ_inst_mk_scheme];

goal thy "!!S. bound_typ_inst ($S o R) ($S sch) = $S (bound_typ_inst R sch)";
by (type_scheme.induct_tac "sch" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "bound_typ_inst_composed_subst";

Addsimps [bound_typ_inst_composed_subst];

goal thy "!!S. S = S' ==> sch = sch' ==> bound_typ_inst S sch = bound_typ_inst S' sch'";
by (Asm_full_simp_tac 1);
qed "bound_typ_inst_eq";



(* lemmatas for bound_scheme_inst *)

goal thy "!!t. bound_scheme_inst B (mk_scheme t) = mk_scheme t";
by (typ.induct_tac "t" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "bound_scheme_inst_mk_scheme";

Addsimps [bound_scheme_inst_mk_scheme];

goal thy "!!S. $S (bound_scheme_inst B sch) = (bound_scheme_inst ($S o B) ($ S sch))";
by (type_scheme.induct_tac "sch" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "substitution_lemma";

goal thy "!t. mk_scheme t = bound_scheme_inst B sch --> \
\         (? S. !x:bound_tv sch. B x = mk_scheme (S x))";
by (type_scheme.induct_tac "sch" 1);
by (Simp_tac 1);
by (safe_tac (!claset));
by (rtac exI 1);
by (rtac ballI 1);
by (rtac sym 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (dtac mk_scheme_Fun 1);
by (REPEAT (etac exE 1));
by (etac conjE 1);
by (dtac sym 1);
by (dtac sym 1);
by (REPEAT ((dtac mp 1) THEN (Fast_tac 1)));
by (safe_tac (!claset));
by (rename_tac "S1 S2" 1);
by (res_inst_tac [("x","%x. if x:bound_tv type_scheme1 then (S1 x) else (S2 x)")] exI 1);
by (safe_tac (!claset));
by (asm_simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (asm_simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (strip_tac 1);
by (dres_inst_tac [("x","x")] bspec 1);
ba 1;
by (dres_inst_tac [("x","x")] bspec 1);
by (Asm_simp_tac 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "bound_scheme_inst_type";


(* lemmatas for subst_to_scheme *)

goal thy "!!sch. new_tv n sch --> subst_to_scheme (%k. if n <= k then BVar (k - n) else FVar k) \
\                                                 (bound_typ_inst (%k. TVar (k + n)) sch) = sch";
by (type_scheme.induct_tac "sch" 1);
by (simp_tac (!simpset setloop (split_tac [expand_if]) addsimps [leD]) 1);
by (simp_tac (!simpset setloop (split_tac [expand_if]) addsimps [le_add2,diff_add_inverse2]) 1);
by (Asm_simp_tac 1);
qed_spec_mp "subst_to_scheme_inverse";

goal thy "!!t t'. t = t' ==> subst_to_scheme (%k. if n <= k then BVar (k - n) else FVar k) t = \
\                            subst_to_scheme (%k. if n <= k then BVar (k - n) else FVar k) t'";
by (Fast_tac 1);
val aux = result ();

goal thy "new_tv n sch --> \
\        (subst_to_scheme (%k. if n <= k then BVar (k - n) else FVar k) (bound_typ_inst S sch) = \
\                         bound_scheme_inst ((subst_to_scheme (%k. if n <= k then BVar (k - n) else FVar k)) o S) sch)";
by (type_scheme.induct_tac "sch" 1);
by (simp_tac (!simpset setloop (split_tac [expand_if]) addsimps [leD]) 1);
by (Asm_simp_tac 1);
by (asm_full_simp_tac (!simpset setloop (split_tac [expand_if]) addsimps [leD]) 1);
val aux2 = result () RS mp;


(* lemmata for <= *)

goalw thy [le_type_scheme_def,is_bound_typ_instance]
      "!!(sch::type_scheme) sch'. (sch' <= sch) = (? B. sch' = bound_scheme_inst B sch)";
by (rtac iffI 1);
by (cut_inst_tac [("sch","sch")] fresh_variable_type_schemes 1); 
by (cut_inst_tac [("sch","sch'")] fresh_variable_type_schemes 1);
by (dtac make_one_new_out_of_two 1);
ba 1;
by (thin_tac "? n. new_tv n sch'" 1); 
by (etac exE 1);
by (etac allE 1);
by (dtac mp 1);
by (res_inst_tac [("x","(%k. TVar (k + n))")] exI 1);
by (rtac refl 1);
by (etac exE 1);
by (REPEAT (etac conjE 1));
by (dres_inst_tac [("n","n")] aux 1);
by (asm_full_simp_tac (!simpset addsimps [subst_to_scheme_inverse]) 1);
by (res_inst_tac [("x","(subst_to_scheme (%k. if n <= k then BVar (k - n) else FVar k)) o S")] exI 1);
by (asm_simp_tac (!simpset addsimps [aux2]) 1);
by (safe_tac (!claset));
by (res_inst_tac [("x","%n. bound_typ_inst S (B n)")] exI 1);
by (type_scheme.induct_tac "sch" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "le_type_scheme_def2";

goalw thy [is_bound_typ_instance] "(mk_scheme t) <= sch = t <| sch";
by (simp_tac (!simpset addsimps [le_type_scheme_def2]) 1); 
by (rtac iffI 1); 
by (etac exE 1); 
by (forward_tac [bound_scheme_inst_type] 1);
by (etac exE 1);
by (rtac exI 1);
by (rtac mk_scheme_injective 1); 
by (Asm_full_simp_tac 1);
by (rotate_tac 1 1);
by (rtac mp 1);
ba 2;
by (type_scheme.induct_tac "sch" 1);
by (Simp_tac 1);
by (Asm_full_simp_tac 1);
by (Fast_tac 1);
by (strip_tac 1);
by (Asm_full_simp_tac 1);
by (etac exE 1);
by (Asm_full_simp_tac 1);
by (rtac exI 1);
by (type_scheme.induct_tac "sch" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "le_type_eq_is_bound_typ_instance";

goalw thy [le_env_def]
  "(sch # A <= sch' # B) = (sch <= (sch'::type_scheme) & A <= B)";
by(Simp_tac 1);
br iffI 1;
 by(SELECT_GOAL(safe_tac (!claset))1);
  by(eres_inst_tac [("x","0")] allE 1);
  by(Asm_full_simp_tac 1);
 by(eres_inst_tac [("x","Suc i")] allE 1);
 by(Asm_full_simp_tac 1);
br conjI 1;
 by(Fast_tac 1);
br allI 1;
by(nat_ind_tac "i" 1);
by(ALLGOALS Asm_simp_tac);
qed "le_env_Cons";
AddIffs [le_env_Cons];

goalw thy [is_bound_typ_instance]"!!t. t <| sch ==> $S t <| $S sch";
by (etac exE 1);
by (rename_tac "SA" 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("x","$S o SA")] exI 1);
by (Simp_tac 1);
qed "is_bound_typ_instance_closed_subst";

goal thy "!!(sch::type_scheme) sch'. sch' <= sch ==> $S sch' <= $ S sch";
by (asm_full_simp_tac (!simpset addsimps [le_type_scheme_def2]) 1);
by (etac exE 1);
by (asm_full_simp_tac (!simpset addsimps [substitution_lemma]) 1);
by (Fast_tac 1);
qed "S_compatible_le_scheme";

goalw thy [le_env_def,app_subst_list] "!!(A::type_scheme list) A'. A' <= A ==> $S A' <= $ S A";
by (simp_tac (!simpset addcongs [conj_cong]) 1);
by (fast_tac (!claset addSIs [S_compatible_le_scheme]) 1);
qed "S_compatible_le_scheme_lists";

goalw thy [le_type_scheme_def] "!!t.[| t <| sch; sch <= sch' |] ==> t <| sch'";
by(Fast_tac 1);
qed "bound_typ_instance_trans";

goalw thy [le_type_scheme_def] "sch <= (sch::type_scheme)";
by(Fast_tac 1);
qed "le_type_scheme_refl";
AddIffs [le_type_scheme_refl];

goalw thy [le_env_def] "A <= (A::type_scheme list)";
by(Fast_tac 1);
qed "le_env_refl";
AddIffs [le_env_refl];

goalw thy [le_type_scheme_def,is_bound_typ_instance] "sch <= BVar n";
by(strip_tac 1);
by(res_inst_tac [("x","%a.t")]exI 1);
by(Simp_tac 1);
qed "bound_typ_instance_BVar";
AddIffs [bound_typ_instance_BVar];

goalw thy [le_type_scheme_def,is_bound_typ_instance] "(sch <= FVar n) = (sch = FVar n)";
by(type_scheme.induct_tac "sch" 1);
  by(Simp_tac 1);
 by(Simp_tac 1);
 by(SELECT_GOAL(safe_tac(!claset))1);
 by(eres_inst_tac [("x","TVar n -> TVar n")] allE 1);
 by(Asm_full_simp_tac 1);
 by(Fast_tac 1);
by(Asm_full_simp_tac 1);
br iffI 1;
 by(eres_inst_tac [("x","bound_typ_inst S type_scheme1 -> bound_typ_inst S type_scheme2")] allE 1);
 by(Asm_full_simp_tac 1);
 by(Fast_tac 1);
by(Fast_tac 1);
qed "le_FVar";
Addsimps [le_FVar];

goalw thy [le_type_scheme_def,is_bound_typ_instance] "~(FVar n <= sch1 =-> sch2)";
by(Simp_tac 1);
qed "not_FVar_le_Fun";
AddIffs [not_FVar_le_Fun];

goalw thy [le_type_scheme_def,is_bound_typ_instance] "~(BVar n <= sch1 =-> sch2)";
by(Simp_tac 1);
by(res_inst_tac [("x","TVar n")] exI 1);
by(Simp_tac 1);
by(Fast_tac 1);
qed "not_BVar_le_Fun";
AddIffs [not_BVar_le_Fun];

goalw thy [le_type_scheme_def,is_bound_typ_instance]
  "!!sch1. (sch1 =-> sch2 <= sch1' =-> sch2') ==> sch1 <= sch1' & sch2 <= sch2'";
by(fast_tac (!claset addss !simpset) 1);
qed "Fun_le_FunD";

goal thy "(sch' <= sch1 =-> sch2) --> (? sch'1 sch'2. sch' = sch'1 =-> sch'2)";
by (type_scheme.induct_tac "sch'" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (Fast_tac 1);
qed_spec_mp "scheme_le_Fun";

goal thy "!sch'::type_scheme. sch <= sch' --> free_tv sch' <= free_tv sch";
by(type_scheme.induct_tac "sch" 1);
  br allI 1;
  by(type_scheme.induct_tac "sch'" 1);
    by(Simp_tac 1);
   by(Simp_tac 1);
  by(Simp_tac 1);
 br allI 1;
 by(type_scheme.induct_tac "sch'" 1);
   by(Simp_tac 1);
  by(Simp_tac 1);
 by(Simp_tac 1);
br allI 1;
by(type_scheme.induct_tac "sch'" 1);
  by(Simp_tac 1);
 by(Simp_tac 1);
by(Asm_full_simp_tac 1);
by(strip_tac 1);
bd Fun_le_FunD 1;
by(Fast_tac 1);
qed_spec_mp "le_type_scheme_free_tv";

goal thy "!A::type_scheme list. A <= B --> free_tv B <= free_tv A";
by(list.induct_tac "B" 1);
 by(Simp_tac 1);
br allI 1;
by(list.induct_tac "A" 1);
 by(simp_tac (!simpset addsimps [le_env_def]) 1);
by(Simp_tac 1);
by(fast_tac (!claset addDs [le_type_scheme_free_tv]) 1);
qed_spec_mp "le_env_free_tv";
