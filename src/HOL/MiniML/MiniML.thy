(* Title:     HOL/MiniML/MiniML.thy
   ID:        $Id$
   Author:    Dieter Nazareth, Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen

Mini_ML with type inference rules.
*)

theory MiniML = Generalize:

(* expressions *)
datatype
        expr = Var nat | Abs expr | App expr expr | LET expr expr

(* type inference rules *)
consts
        has_type :: "(ctxt * expr * typ)set"
syntax
        "@has_type" :: "[ctxt, expr, typ] => bool"
                       ("((_) |-/ (_) :: (_))" [60,0,60] 60)
translations 
        "A |- e :: t" == "(A,e,t):has_type"

inductive has_type
intros
  VarI: "[| n < length A; t <| A!n |] ==> A |- Var n :: t"
  AbsI: "[| (mk_scheme t1)#A |- e :: t2 |] ==> A |- Abs e :: t1 -> t2"
  AppI: "[| A |- e1 :: t2 -> t1; A |- e2 :: t2 |] 
         ==> A |- App e1 e2 :: t1"
  LETI: "[| A |- e1 :: t1; (gen A t1)#A |- e2 :: t |] ==> A |- LET e1 e2 :: t"


declare has_type.intros [simp]
declare Un_upper1 [simp] Un_upper2 [simp]

declare is_bound_typ_instance_closed_subst [simp]


lemma s'_t_equals_s_t: "!!t::typ. $(%n. if n : (free_tv A) Un (free_tv t) then (S n) else (TVar n)) t = $S t"
apply (rule typ_substitutions_only_on_free_variables)
apply (simp add: Ball_def)
done

declare s'_t_equals_s_t [simp]

lemma s'_a_equals_s_a: "!!A::type_scheme list. $(%n. if n : (free_tv A) Un (free_tv t) then (S n) else (TVar n)) A = $S A"
apply (rule scheme_list_substitutions_only_on_free_variables)
apply (simp add: Ball_def)
done

declare s'_a_equals_s_a [simp]

lemma replace_s_by_s': 
 "$(%n. if n : (free_tv A) Un (free_tv t) then S n else TVar n) A |-  
     e :: $(%n. if n : (free_tv A) Un (free_tv t) then S n else TVar n) t  
  ==> $S A |- e :: $S t"

apply (rule_tac P = "%A. A |- e :: $S t" in ssubst)
apply (rule s'_a_equals_s_a [symmetric])
apply (rule_tac P = "%t. $ (%n. if n : free_tv A Un free_tv (?t1 S) then S n else TVar n) A |- e :: t" in ssubst)
apply (rule s'_t_equals_s_t [symmetric])
apply simp
done

lemma alpha_A': "!!A::type_scheme list. $ (%x. TVar (if x : free_tv A then x else n + x)) A = $ id_subst A"
apply (rule scheme_list_substitutions_only_on_free_variables)
apply (simp add: id_subst_def)
done

lemma alpha_A: "!!A::type_scheme list. $ (%x. TVar (if x : free_tv A then x else n + x)) A = A"
apply (rule alpha_A' [THEN ssubst])
apply simp
done

lemma S_o_alpha_typ: "$ (S o alpha) (t::typ) = $ S ($ (%x. TVar (alpha x)) t)"
apply (induct_tac "t")
apply (simp_all)
done

lemma S_o_alpha_typ': "$ (%u. (S o alpha) u) (t::typ) = $ S ($ (%x. TVar (alpha x)) t)"
apply (induct_tac "t")
apply (simp_all)
done

lemma S_o_alpha_type_scheme: "$ (S o alpha) (sch::type_scheme) = $ S ($ (%x. TVar (alpha x)) sch)"
apply (induct_tac "sch")
apply (simp_all)
done

lemma S_o_alpha_type_scheme_list: "$ (S o alpha) (A::type_scheme list) = $ S ($ (%x. TVar (alpha x)) A)"
apply (induct_tac "A")
apply (simp_all) 
apply (rule S_o_alpha_type_scheme [unfolded o_def])
done

lemma S'_A_eq_S'_alpha_A: "!!A::type_scheme list.  
      $ (%n. if n : free_tv A Un free_tv t then S n else TVar n) A =  
      $ ((%x. if x : free_tv A Un free_tv t then S x else TVar x) o  
         (%x. if x : free_tv A then x else n + x)) A"
apply (subst S_o_alpha_type_scheme_list)
apply (subst alpha_A)
apply (rule refl)
done

lemma dom_S': 
 "dom (%n. if n : free_tv A Un free_tv t then S n else TVar n) <=  
  free_tv A Un free_tv t"
apply (unfold free_tv_subst dom_def)
apply (simp (no_asm))
apply fast
done

lemma cod_S': 
  "!!(A::type_scheme list) (t::typ).   
   cod (%n. if n : free_tv A Un free_tv t then S n else TVar n) <=  
   free_tv ($ S A) Un free_tv ($ S t)"
apply (unfold free_tv_subst cod_def subset_def)
apply (rule ballI)
apply (erule UN_E)
apply (drule dom_S' [THEN subsetD])
apply simp
apply (fast dest: free_tv_of_substitutions_extend_to_scheme_lists intro: free_tv_of_substitutions_extend_to_types [THEN subsetD])
done

lemma free_tv_S': 
 "!!(A::type_scheme list) (t::typ).  
  free_tv (%n. if n : free_tv A Un free_tv t then S n else TVar n) <=  
  free_tv A Un free_tv ($ S A) Un free_tv t Un free_tv ($ S t)"
apply (unfold free_tv_subst)
apply (fast dest: dom_S' [THEN subsetD] cod_S' [THEN subsetD])
done

lemma free_tv_alpha: "!!t1::typ.  
      (free_tv ($ (%x. TVar (if x : free_tv A then x else n + x)) t1) - free_tv A) <=  
          {x. ? y. x = n + y}"
apply (induct_tac "t1")
apply (simp (no_asm))
apply fast
apply (simp (no_asm))
apply fast
done

lemma aux_plus: "!!(k::nat). n <= n + k"
apply (induct_tac "k" rule: nat_induct)
apply (simp (no_asm))
apply (simp (no_asm_simp))
done

declare aux_plus [simp]

lemma new_tv_Int_free_tv_empty_type: "!!t::typ. new_tv n t ==> {x. ? y. x = n + y} Int free_tv t = {}"
apply safe
apply (cut_tac aux_plus)
apply (drule new_tv_le)
apply assumption
apply (rotate_tac 1)
apply (drule new_tv_not_free_tv)
apply fast
done

lemma new_tv_Int_free_tv_empty_scheme: "!!sch::type_scheme. new_tv n sch ==> {x. ? y. x = n + y} Int free_tv sch = {}"
apply safe
apply (cut_tac aux_plus)
apply (drule new_tv_le)
apply assumption
apply (rotate_tac 1)
apply (drule new_tv_not_free_tv)
apply fast
done

lemma new_tv_Int_free_tv_empty_scheme_list: "!A::type_scheme list. new_tv n A --> {x. ? y. x = n + y} Int free_tv A = {}"
apply (rule allI)
apply (induct_tac "A")
apply (simp (no_asm))
apply (simp (no_asm))
apply (fast dest: new_tv_Int_free_tv_empty_scheme)
done

lemma gen_t_le_gen_alpha_t [rule_format (no_asm)]: 
   "new_tv n A --> gen A t <= gen A ($ (%x. TVar (if x : free_tv A then x else n + x)) t)"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (intro strip)
apply (erule exE)
apply (hypsubst)
apply (rule_tac x = " (%x. S (if n <= x then x - n else x))" in exI)
apply (induct_tac "t")
apply (simp (no_asm))
apply (case_tac "nat : free_tv A")
apply (simp (no_asm_simp))
apply (subgoal_tac "n <= n + nat")
apply (drule new_tv_le)
apply assumption
apply (drule new_tv_not_free_tv)
apply (drule new_tv_not_free_tv)
apply (simp (no_asm_simp) add: diff_add_inverse)
apply (simp (no_asm))
apply (simp (no_asm_simp))
done

declare has_type.intros [intro!]

lemma has_type_le_env [rule_format (no_asm)]: "A |- e::t ==> !B. A <= B -->  B |- e::t"
apply (erule has_type.induct)
   apply (simp (no_asm) add: le_env_def)
   apply (fastsimp elim: bound_typ_instance_trans)
  apply simp
 apply fast
apply (slow elim: le_env_free_tv [THEN free_tv_subset_gen_le])
done

(* has_type is closed w.r.t. substitution *)
lemma has_type_cl_sub: "A |- e :: t ==> !S. $S A |- e :: $S t"
apply (erule has_type.induct)
(* case VarI *)
   apply (rule allI)
   apply (rule has_type.VarI)
    apply (simp add: app_subst_list)
   apply (simp (no_asm_simp) add: app_subst_list)
  (* case AbsI *)
  apply (rule allI)
  apply (simp (no_asm))
  apply (rule has_type.AbsI)
  apply simp
 (* case AppI *)
 apply (rule allI)
 apply (rule has_type.AppI)
  apply simp
  apply (erule spec)
 apply (erule spec)
(* case LetI *)
apply (rule allI)
apply (rule replace_s_by_s')
apply (cut_tac A = "$ S A" and A' = "A" and t = "t" and t' = "$ S t" in ex_fresh_variable)
apply (erule exE)
apply (erule conjE)+ 
apply (rule_tac ?t1.0 = "$ ((%x. if x : free_tv A Un free_tv t then S x else TVar x) o (%x. if x : free_tv A then x else n + x)) t1" in has_type.LETI)
 apply (drule_tac x = " (%x. if x : free_tv A Un free_tv t then S x else TVar x) o (%x. if x : free_tv A then x else n + x) " in spec)
 apply (subst S'_A_eq_S'_alpha_A)
 apply assumption
apply (subst S_o_alpha_typ)
apply (subst gen_subst_commutes)
 apply (rule subset_antisym)
  apply (rule subsetI)
  apply (erule IntE)
  apply (drule free_tv_S' [THEN subsetD])
  apply (drule free_tv_alpha [THEN subsetD])
  apply (simp del: full_SetCompr_eq)
  apply (erule exE)
  apply (hypsubst)
  apply (subgoal_tac "new_tv (n + y) ($ S A) ")
   apply (subgoal_tac "new_tv (n + y) ($ S t) ")
    apply (subgoal_tac "new_tv (n + y) A")
     apply (subgoal_tac "new_tv (n + y) t")
      apply (drule new_tv_not_free_tv)+
      apply fast
     apply (rule new_tv_le) prefer 2 apply assumption apply simp
    apply (rule new_tv_le) prefer 2 apply assumption apply simp
   apply (rule new_tv_le) prefer 2 apply assumption apply simp
  apply (rule new_tv_le) prefer 2 apply assumption apply simp
 apply fast
apply (rule has_type_le_env)
 apply (drule spec)
 apply (drule spec)
 apply assumption
apply (rule app_subst_Cons [THEN subst])
apply (rule S_compatible_le_scheme_lists)
apply (simp (no_asm_simp))
done


end
