(* Title:     HOL/MiniML/Generalize.ML
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

AddSEs [equalityE];

goal thy "!!A B. free_tv A = free_tv B ==> gen A t = gen B t";
by (typ.induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "gen_eq_on_free_tv";

goal thy "!!t.(free_tv t) <= (free_tv sch) --> gen sch t = (mk_scheme t)";
by (typ.induct_tac "t" 1);
by (Asm_simp_tac 1);
by (Simp_tac 1);
by (Fast_tac 1);
qed_spec_mp "gen_without_effect";

Addsimps [gen_without_effect];

goal thy "!!A. free_tv (gen ($ S A) t) = free_tv t Int free_tv ($ S A)";
by (typ.induct_tac "t" 1);
by (Simp_tac 1);
by (case_tac "nat : free_tv ($ S A)" 1);
by (Asm_simp_tac 1);
by (Fast_tac 1);
by (Asm_simp_tac 1);
by (Fast_tac 1);
by (Asm_full_simp_tac 1);
by (Fast_tac 1);
qed "free_tv_gen";

Addsimps [free_tv_gen];

goal thy "!!A. free_tv (gen ($ S A) t # $ S A) = free_tv ($ S A)";
by (Simp_tac 1);
by (Fast_tac 1);
qed "free_tv_gen_cons";

Addsimps [free_tv_gen_cons];

goal thy "!!A. bound_tv (gen A t1) = (free_tv t1) - (free_tv A)";
by (typ.induct_tac "t1" 1);
by (Simp_tac 1);
by (case_tac "nat : free_tv A" 1);
by (asm_simp_tac (simpset() addsplits [expand_if]) 1);
by (asm_simp_tac (simpset() addsplits [expand_if]) 1);
by (Fast_tac 1);
by (Asm_simp_tac 1);
by (Fast_tac 1);
qed "bound_tv_gen";

Addsimps [bound_tv_gen];

goal thy "!!A. new_tv n t --> new_tv n (gen A t)";
by (typ.induct_tac "t" 1);
by (Simp_tac 1);
by (case_tac "nat : free_tv A" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "new_tv_compatible_gen";

goalw thy [gen_ML_def] "!!A. gen A t = gen_ML A t";
by (typ.induct_tac "t" 1);
by (simp_tac (simpset() addsimps [free_tv_ML_scheme_list]) 1);
by (asm_simp_tac (simpset() addsimps [free_tv_ML_scheme_list]) 1);
qed "gen_eq_gen_ML";

goal thy "!!S. (free_tv S) Int ((free_tv t) - (free_tv A)) = {} \
\          --> gen ($ S A) ($ S t) = $ S (gen A t)";
by (typ.induct_tac "t" 1);
by (strip_tac 1);
by (case_tac "nat:(free_tv A)" 1);
by (Asm_simp_tac 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "nat ~: free_tv S" 1);
by (Fast_tac 2);
by (asm_full_simp_tac (simpset() addsimps [free_tv_subst,dom_def,de_Morgan_disj]) 1);
by (split_tac [expand_if] 1);
by (cut_facts_tac [free_tv_app_subst_scheme_list] 1);
by (Fast_tac 1);
by (Asm_simp_tac 1);
by (Best_tac 1);
qed_spec_mp "gen_subst_commutes";

goal Generalize.thy "free_tv(t::typ) <= free_tv(A) --> bound_typ_inst S (gen A t) = t";
by (typ.induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
by (Fast_tac 1);
qed_spec_mp "bound_typ_inst_gen";
Addsimps [bound_typ_inst_gen];

goalw Generalize.thy [le_type_scheme_def,is_bound_typ_instance]
  "gen ($ S A) ($ S t) <= $ S (gen A t)";
by Safe_tac;
by (rename_tac "R" 1);
by (res_inst_tac [("x", "(%a. bound_typ_inst R (gen ($S A) (S a)))")] exI 1);
by (typ.induct_tac "t" 1);
 by (simp_tac (simpset() addsplits [expand_if]) 1);
by (Asm_simp_tac 1);
qed "gen_bound_typ_instance";

goalw Generalize.thy [le_type_scheme_def,is_bound_typ_instance]
  "!!A B. free_tv B <= free_tv A ==> gen A t <= gen B t";
by Safe_tac;
by (rename_tac "S" 1);
by (res_inst_tac [("x","%b. if b:free_tv A then TVar b else S b")] exI 1);
by (typ.induct_tac "t" 1);
 by (asm_simp_tac (simpset() addsplits [expand_if]) 1);
 by (Fast_tac 1);
by (Asm_simp_tac 1);
qed "free_tv_subset_gen_le";

goalw thy [le_type_scheme_def,is_bound_typ_instance] 
      "!!A. new_tv n A --> gen A t <= gen A ($ (%x. TVar (if x : free_tv A then x else n + x)) t)";
by (strip_tac 1);
by (etac exE 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("x","(%x. S (if n <= x then x - n else x))")] exI 1);
by (typ.induct_tac "t" 1);
by (Simp_tac 1);
by (case_tac "nat : free_tv A" 1);
by (asm_simp_tac (simpset() addsplits [expand_if]) 1);
by (asm_simp_tac (simpset() addsplits [expand_if]) 1);
by (subgoal_tac "n <= n + nat" 1);
by (forw_inst_tac [("t","A")] new_tv_le 1);
by (assume_tac 1);
by (dtac new_tv_not_free_tv 1);
by (dtac new_tv_not_free_tv 1);
by (asm_simp_tac (simpset() addsimps [diff_add_inverse]) 1);
by (simp_tac (simpset() addsimps [le_add1]) 1);
by (Asm_simp_tac 1);
qed_spec_mp "gen_t_le_gen_alpha_t";

Addsimps [gen_t_le_gen_alpha_t];
