(* Title:     HOL/MiniML/Generalize.thy
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen

Generalizing type schemes with respect to a context
*)

theory Generalize = Instance:


(* gen: binding (generalising) the variables which are not free in the context *)

types ctxt = "type_scheme list"
    
consts
  gen :: "[ctxt, typ] => type_scheme"

primrec
  "gen A (TVar n) = (if (n:(free_tv A)) then (FVar n) else (BVar n))"
  "gen A (t1 -> t2) = (gen A t1) =-> (gen A t2)"

(* executable version of gen: Implementation with free_tv_ML *)

consts
  gen_ML_aux :: "[nat list, typ] => type_scheme"
primrec
  "gen_ML_aux A (TVar n) = (if (n: set A) then (FVar n) else (BVar n))"
  "gen_ML_aux A (t1 -> t2) = (gen_ML_aux A t1) =-> (gen_ML_aux A t2)"

consts
  gen_ML :: "[ctxt, typ] => type_scheme"
defs
  gen_ML_def: "gen_ML A t == gen_ML_aux (free_tv_ML A) t"


declare equalityE [elim!]

lemma gen_eq_on_free_tv: "free_tv A = free_tv B ==> gen A t = gen B t"
apply (induct_tac "t")
apply (simp_all (no_asm_simp))
done

lemma gen_without_effect [rule_format (no_asm)]: "(free_tv t) <= (free_tv sch) --> gen sch t = (mk_scheme t)"
apply (induct_tac "t")
apply (simp (no_asm_simp))
apply (simp (no_asm))
apply fast
done

declare gen_without_effect [simp]

lemma free_tv_gen: "free_tv (gen ($ S A) t) = free_tv t Int free_tv ($ S A)"
apply (induct_tac "t")
apply (simp (no_asm))
apply (case_tac "nat : free_tv ($ S A) ")
apply (simp (no_asm_simp))
apply fast
apply (simp (no_asm_simp))
apply fast
apply simp
apply fast
done

declare free_tv_gen [simp]

lemma free_tv_gen_cons: "free_tv (gen ($ S A) t # $ S A) = free_tv ($ S A)"
apply (simp (no_asm))
apply fast
done

declare free_tv_gen_cons [simp]

lemma bound_tv_gen: "bound_tv (gen A t1) = (free_tv t1) - (free_tv A)"
apply (induct_tac "t1")
apply (simp (no_asm))
apply (case_tac "nat : free_tv A")
apply (simp (no_asm_simp))
apply (simp (no_asm_simp))
apply fast
apply (simp (no_asm_simp))
apply fast
done

declare bound_tv_gen [simp]

lemma new_tv_compatible_gen [rule_format (no_asm)]: "new_tv n t --> new_tv n (gen A t)"
apply (induct_tac "t")
apply auto
done

lemma gen_eq_gen_ML: "gen A t = gen_ML A t"
apply (unfold gen_ML_def)
apply (induct_tac "t")
 apply (simp (no_asm) add: free_tv_ML_scheme_list)
apply (simp (no_asm_simp) add: free_tv_ML_scheme_list)
done

lemma gen_subst_commutes [rule_format (no_asm)]: "(free_tv S) Int ((free_tv t) - (free_tv A)) = {}  
      --> gen ($ S A) ($ S t) = $ S (gen A t)"
apply (induct_tac "t")
 apply (intro strip)
 apply (case_tac "nat: (free_tv A) ")
  apply (simp (no_asm_simp))
 apply simp
 apply (subgoal_tac "nat ~: free_tv S")
  prefer 2 apply (fast)
 apply (simp add: free_tv_subst dom_def)
 apply (cut_tac free_tv_app_subst_scheme_list)
 apply fast
apply (simp (no_asm_simp))
apply blast
done

lemma bound_typ_inst_gen [rule_format (no_asm)]: "free_tv(t::typ) <= free_tv(A) --> bound_typ_inst S (gen A t) = t"
apply (induct_tac "t")
apply (simp_all (no_asm_simp))
apply fast
done
declare bound_typ_inst_gen [simp]

lemma gen_bound_typ_instance: 
  "gen ($ S A) ($ S t) <= $ S (gen A t)"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply safe
apply (rename_tac "R")
apply (rule_tac x = " (%a. bound_typ_inst R (gen ($S A) (S a))) " in exI)
apply (induct_tac "t")
 apply (simp (no_asm))
apply (simp (no_asm_simp))
done

lemma free_tv_subset_gen_le: 
  "free_tv B <= free_tv A ==> gen A t <= gen B t"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply safe
apply (rename_tac "S")
apply (rule_tac x = "%b. if b:free_tv A then TVar b else S b" in exI)
apply (induct_tac "t")
 apply (simp (no_asm_simp))
 apply fast
apply (simp (no_asm_simp))
done

lemma gen_t_le_gen_alpha_t [rule_format (no_asm)]: 
  "new_tv n A -->  
   gen A t <= gen A ($ (%x. TVar (if x : free_tv A then x else n + x)) t)"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (intro strip)
apply (erule exE)
apply (hypsubst)
apply (rule_tac x = " (%x. S (if n <= x then x - n else x))" in exI)
apply (induct_tac "t")
apply (simp (no_asm))
apply (case_tac "nat : free_tv A")
apply (simp (no_asm_simp))
apply (simp (no_asm_simp))
apply (subgoal_tac "n <= n + nat")
apply (frule_tac t = "A" in new_tv_le)
apply assumption
apply (drule new_tv_not_free_tv)
apply (drule new_tv_not_free_tv)
apply (simp (no_asm_simp) add: diff_add_inverse)
apply (simp (no_asm) add: le_add1)
apply (simp (no_asm_simp))
done

declare gen_t_le_gen_alpha_t [simp]


end
