(* Title:     HOL/MiniML/Instance.thy
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen

Instances of type schemes
*)

theory Instance = Type:

  
(* generic instances of a type scheme *)

consts
  bound_typ_inst :: "[subst, type_scheme] => typ"

primrec
  "bound_typ_inst S (FVar n) = (TVar n)"
  "bound_typ_inst S (BVar n) = (S n)"
  "bound_typ_inst S (sch1 =-> sch2) = ((bound_typ_inst S sch1) -> (bound_typ_inst S sch2))"

consts
  bound_scheme_inst :: "[nat => type_scheme, type_scheme] => type_scheme"

primrec
  "bound_scheme_inst S (FVar n) = (FVar n)"
  "bound_scheme_inst S (BVar n) = (S n)"
  "bound_scheme_inst S (sch1 =-> sch2) = ((bound_scheme_inst S sch1) =-> (bound_scheme_inst S sch2))"
  
consts
  "<|" :: "[typ, type_scheme] => bool" (infixr 70)
defs
  is_bound_typ_instance: "t <| sch == ? S. t = (bound_typ_inst S sch)" 

instance type_scheme :: ord ..
defs le_type_scheme_def: "sch' <= (sch::type_scheme) == !t. t <| sch' --> t <| sch"

consts
  subst_to_scheme :: "[nat => type_scheme, typ] => type_scheme"

primrec
  "subst_to_scheme B (TVar n) = (B n)"
  "subst_to_scheme B (t1 -> t2) = ((subst_to_scheme B t1) =-> (subst_to_scheme B t2))"
  
instance list :: (ord)ord ..
defs le_env_def:
  "A <= B == length B = length A & (!i. i < length A --> A!i <= B!i)"


(* lemmatas for instatiation *)


(* lemmatas for bound_typ_inst *)

lemma bound_typ_inst_mk_scheme: "bound_typ_inst S (mk_scheme t) = t"
apply (induct_tac "t")
apply (simp_all (no_asm_simp))
done

declare bound_typ_inst_mk_scheme [simp]

lemma bound_typ_inst_composed_subst: "bound_typ_inst ($S o R) ($S sch) = $S (bound_typ_inst R sch)"
apply (induct_tac "sch")
apply simp_all
done

declare bound_typ_inst_composed_subst [simp]

lemma bound_typ_inst_eq: "S = S' ==> sch = sch' ==> bound_typ_inst S sch = bound_typ_inst S' sch'"
apply simp
done



(* lemmatas for bound_scheme_inst *)

lemma bound_scheme_inst_mk_scheme: "bound_scheme_inst B (mk_scheme t) = mk_scheme t"
apply (induct_tac "t")
apply (simp (no_asm))
apply (simp (no_asm_simp))
done

declare bound_scheme_inst_mk_scheme [simp]

lemma substitution_lemma: "$S (bound_scheme_inst B sch) = (bound_scheme_inst ($S o B) ($ S sch))"
apply (induct_tac "sch")
apply (simp (no_asm))
apply (simp (no_asm))
apply (simp (no_asm_simp))
done

lemma bound_scheme_inst_type [rule_format (no_asm)]: "!t. mk_scheme t = bound_scheme_inst B sch -->  
          (? S. !x:bound_tv sch. B x = mk_scheme (S x))"
apply (induct_tac "sch")
apply (simp (no_asm))
apply safe
apply (rule exI)
apply (rule ballI)
apply (rule sym)
apply simp
apply simp
apply (drule mk_scheme_Fun)
apply (erule exE)+
apply (erule conjE)
apply (drule sym)
apply (drule sym)
apply (drule mp, fast)+
apply safe
apply (rename_tac S1 S2)
apply (rule_tac x = "%x. if x:bound_tv type_scheme1 then (S1 x) else (S2 x) " in exI)
apply auto
done


(* lemmas for subst_to_scheme *)

lemma subst_to_scheme_inverse [rule_format (no_asm)]: "new_tv n sch --> subst_to_scheme (%k. if n <= k then BVar (k - n) else FVar k)  
                                                  (bound_typ_inst (%k. TVar (k + n)) sch) = sch"
apply (induct_tac "sch")
apply (simp (no_asm) add: le_def)
apply (simp (no_asm) add: le_add2 diff_add_inverse2)
apply (simp (no_asm_simp))
done

lemma aux: "t = t' ==>  
      subst_to_scheme (%k. if n <= k then BVar (k - n) else FVar k) t =  
      subst_to_scheme (%k. if n <= k then BVar (k - n) else FVar k) t'"
apply fast
done

lemma aux2 [rule_format]: "new_tv n sch -->  
      subst_to_scheme (%k. if n <= k then BVar (k - n) else FVar k) (bound_typ_inst S sch) =  
       bound_scheme_inst ((subst_to_scheme (%k. if n <= k then BVar (k - n) else FVar k)) o S) sch"
apply (induct_tac "sch")
apply auto
done


(* lemmata for <= *)

lemma le_type_scheme_def2: 
  "!!(sch::type_scheme) sch'.  
   (sch' <= sch) = (? B. sch' = bound_scheme_inst B sch)"

apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (rule iffI)
apply (cut_tac sch = "sch" in fresh_variable_type_schemes)
apply (cut_tac sch = "sch'" in fresh_variable_type_schemes)
apply (drule make_one_new_out_of_two)
apply assumption
apply (erule_tac V = "? n. new_tv n sch'" in thin_rl)
apply (erule exE)
apply (erule allE)
apply (drule mp)
apply (rule_tac x = " (%k. TVar (k + n))" in exI)
apply (rule refl)
apply (erule exE)
apply (erule conjE)+
apply (drule_tac n = "n" in aux)
apply (simp add: subst_to_scheme_inverse)
apply (rule_tac x = " (subst_to_scheme (%k. if n <= k then BVar (k - n) else FVar k)) o S" in exI)
apply (simp (no_asm_simp) add: aux2)
apply safe
apply (rule_tac x = "%n. bound_typ_inst S (B n) " in exI)
apply (induct_tac "sch")
apply (simp (no_asm))
apply (simp (no_asm))
apply (simp (no_asm_simp))
done

lemma le_type_eq_is_bound_typ_instance [rule_format (no_asm)]: "(mk_scheme t) <= sch = t <| sch"
apply (unfold is_bound_typ_instance)
apply (simp (no_asm) add: le_type_scheme_def2)
apply (rule iffI)
apply (erule exE)
apply (frule bound_scheme_inst_type)
apply (erule exE)
apply (rule exI)
apply (rule mk_scheme_injective)
apply simp
apply (rotate_tac 1)
apply (rule mp)
prefer 2 apply (assumption)
apply (induct_tac "sch")
apply (simp (no_asm))
apply simp
apply fast
apply (intro strip)
apply simp
apply (erule exE)
apply simp
apply (rule exI)
apply (induct_tac "sch")
apply (simp (no_asm))
apply (simp (no_asm))
apply simp
done

lemma le_env_Cons: 
  "(sch # A <= sch' # B) = (sch <= (sch'::type_scheme) & A <= B)"
apply (unfold le_env_def)
apply (simp (no_asm))
apply (rule iffI)
 apply clarify
 apply (rule conjI) 
  apply (erule_tac x = "0" in allE)
  apply simp
 apply (rule conjI, assumption)
 apply clarify
 apply (erule_tac x = "Suc i" in allE) 
 apply simp
apply (rule conjI)
 apply fast
apply (rule allI)
apply (induct_tac "i")
apply (simp_all (no_asm_simp))
done
declare le_env_Cons [iff]

lemma is_bound_typ_instance_closed_subst: "t <| sch ==> $S t <| $S sch"
apply (unfold is_bound_typ_instance)
apply (erule exE)
apply (rename_tac "SA") 
apply (simp)
apply (rule_tac x = "$S o SA" in exI)
apply (simp (no_asm))
done

lemma S_compatible_le_scheme: "!!(sch::type_scheme) sch'. sch' <= sch ==> $S sch' <= $ S sch"
apply (simp add: le_type_scheme_def2)
apply (erule exE)
apply (simp add: substitution_lemma)
apply fast
done

lemma S_compatible_le_scheme_lists: 
 "!!(A::type_scheme list) A'. A' <= A ==> $S A' <= $ S A"
apply (unfold le_env_def app_subst_list)
apply (simp (no_asm) cong add: conj_cong)
apply (fast intro!: S_compatible_le_scheme)
done

lemma bound_typ_instance_trans: "[| t <| sch; sch <= sch' |] ==> t <| sch'"
apply (unfold le_type_scheme_def)
apply fast
done

lemma le_type_scheme_refl: "sch <= (sch::type_scheme)"
apply (unfold le_type_scheme_def)
apply fast
done
declare le_type_scheme_refl [iff]

lemma le_env_refl: "A <= (A::type_scheme list)"
apply (unfold le_env_def)
apply fast
done
declare le_env_refl [iff]

lemma bound_typ_instance_BVar: "sch <= BVar n"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (intro strip)
apply (rule_tac x = "%a. t" in exI)
apply (simp (no_asm))
done
declare bound_typ_instance_BVar [iff]

lemma le_FVar: 
 "(sch <= FVar n) = (sch = FVar n)"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (induct_tac "sch")
  apply (simp (no_asm))
 apply (simp (no_asm))
 apply fast
apply simp
apply fast
done
declare le_FVar [simp]

lemma not_FVar_le_Fun: "~(FVar n <= sch1 =-> sch2)"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (simp (no_asm))
done
declare not_FVar_le_Fun [iff]

lemma not_BVar_le_Fun: "~(BVar n <= sch1 =-> sch2)"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (simp (no_asm))
apply (rule_tac x = "TVar n" in exI)
apply (simp (no_asm))
apply fast
done
declare not_BVar_le_Fun [iff]

lemma Fun_le_FunD: 
  "(sch1 =-> sch2 <= sch1' =-> sch2') ==> sch1 <= sch1' & sch2 <= sch2'"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (fastsimp)
done

lemma scheme_le_Fun [rule_format (no_asm)]: "(sch' <= sch1 =-> sch2) --> (? sch'1 sch'2. sch' = sch'1 =-> sch'2)"
apply (induct_tac "sch'")
apply (simp (no_asm_simp))
apply (simp (no_asm_simp))
apply fast
done

lemma le_type_scheme_free_tv [rule_format (no_asm)]: "!sch'::type_scheme. sch <= sch' --> free_tv sch' <= free_tv sch"
apply (induct_tac "sch")
  apply (rule allI)
  apply (induct_tac "sch'")
    apply (simp (no_asm))
   apply (simp (no_asm))
  apply (simp (no_asm))
 apply (rule allI)
 apply (induct_tac "sch'")
   apply (simp (no_asm))
  apply (simp (no_asm))
 apply (simp (no_asm))
apply (rule allI)
apply (induct_tac "sch'")
  apply (simp (no_asm))
 apply (simp (no_asm))
apply simp
apply (intro strip)
apply (drule Fun_le_FunD)
apply fast
done

lemma le_env_free_tv [rule_format (no_asm)]: "!A::type_scheme list. A <= B --> free_tv B <= free_tv A"
apply (induct_tac "B")
 apply (simp (no_asm))
apply (rule allI)
apply (induct_tac "A")
 apply (simp (no_asm) add: le_env_def)
apply (simp (no_asm))
apply (fast dest: le_type_scheme_free_tv)
done


end
