(*  Title:      HOL/BCV/JVM.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

Addsimps [Let_def];

Addsimps [is_type_def];

Goalw [states_def,JVM.sl_def,Opt.sl_def,Err.sl_def,
       stk_esl_def,reg_sl_def,Product.esl_def,
       Listn.sl_def,upto_esl_def,JType.esl_def,Err.esl_def]
 "states S maxs maxr == opt(err((Union {list n (types S) |n. n <= maxs}) <*>\
\                                list maxr (err(types S))))";
by (Simp_tac 1);
qed "JVM_states_unfold";

Goalw [JVM.le_def,JVM.sl_def,Opt.sl_def,Err.sl_def,
       stk_esl_def,reg_sl_def,Product.esl_def,
       Listn.sl_def,upto_esl_def,JType.esl_def,Err.esl_def]
 "JVM.le S m n == \
\ Opt.le(Err.le(Product.le(Listn.le(subtype S))(Listn.le(Err.le(subtype S)))))";
by (Simp_tac 1);
qed "JVM_le_unfold";

Goalw [wfis_def,wfi_def]
 "[| wfis S md maxr bs; bs!p = Load n; p < size bs |] ==> n < maxr";
by (auto_tac (claset(),simpset()addsimps [all_set_conv_all_nth]));
qed "wf_LoadD";

Goalw [wfis_def,wfi_def]
 "[| wfis S md maxr bs; bs!p = Store n; p < size bs |] ==> n < maxr";
by (auto_tac (claset(),simpset()addsimps [all_set_conv_all_nth]));
qed "wf_StoreD";

Goalw [wfis_def,wfi_def]
 "[| wfis S md m bs; bs!p = New C; p < size bs |] ==> (C,Object):S^*";
by (auto_tac (claset(),simpset()addsimps [all_set_conv_all_nth]));
qed "wf_NewD";

Goalw [wfis_def,wfi_def,wf_mdict_def]
 "[| wfis S md maxr bs; wf_mdict S md; bs!p = Invoke C m pT (Class R); \
\    p < size bs |] ==> (R,Object):S^*";
by (force_tac (claset(),simpset()addsimps [all_set_conv_all_nth]) 1);
qed "wf_InvokeD";

Goalw [wfis_def,wfi_def]
 "[|wfis S md m bs; bs!p = Getfield (Class C) D; p < size bs|] ==> \
\ (C,Object):S^*";
by (auto_tac (claset(),simpset()addsimps [all_set_conv_all_nth]));
qed "wf_GetfieldD";

Goal "(? X. (? n. X = A n & P n) & Q X) = (? n. Q(A n) & P n)";
by (Blast_tac 1);
qed "special_ex_swap_lemma";
AddIffs [special_ex_swap_lemma];

Goalw [pres_type_def,list_def,step_def,JVM_states_unfold]
 "[| wfis S md maxr bs; wf_mdict S md |] ==> \
\ pres_type (step S maxs rT bs) (size bs) (states S maxs maxr)";
by (clarify_tac (claset() addSEs [option_map_in_optionI,lift_in_errI]) 1);
by (asm_simp_tac (simpset()addsimps [exec_def] addsplits [instr.split]) 1);

by (rtac conjI 1);
by (fast_tac (claset() addDs [refl RS nth_in] addSEs [wf_LoadD] addss
      (simpset() delsimps [is_type_def]addsplits [err.split])) 1);

by (rtac conjI 1);
by (fast_tac (claset() addDs [set_update_subset_insert RS subsetD]
               addSEs [wf_StoreD] addss (simpset() addsplits [list.split])) 1);

by (rtac conjI 1);
by (fast_tac (claset() addss (simpset() addsplits [list.split])) 1);

by (rtac conjI 1);
by (fast_tac (claset() addIs [wf_GetfieldD]
              addss (simpset() addsplits [list.split,ty.split])) 1);

by (rtac conjI 1);
by (fast_tac (claset() addss (simpset() addsplits [list.split])) 1);

by (rtac conjI 1);
by (fast_tac (claset() addIs [wf_NewD] addss simpset()) 1);

by (rtac conjI 1);
by (DEPTH_SOLVE_1(rtac conjI 1 ORELSE
    Clarify_tac 1 THEN asm_full_simp_tac (simpset() addsimps [wf_InvokeD]
      addsplits [list.split,ty.split,option.split]) 1));

by (fast_tac (claset() addss (simpset() addsplits [list.split])) 1);

qed "exec_pres_type";

Goalw [wti_is_stable_topless_def,wti_def,stable_def,step_def,
       option_map_def,lift_def,bounded_def,JVM_le_unfold]
 "[| bounded (succs bs) (size bs) |] ==> \
\ wti_is_stable_topless (JVM.le S maxs maxr) \
\    (Some Err) \
\    (step S maxs rT bs) \
\    (wti S maxs rT bs) \
\    (succs bs) (size bs) (states S maxs maxr)";
by (simp_tac (simpset() addsplits [option.split]) 1);
by (simp_tac (simpset() addsplits [err.split]) 1);
by (Clarify_tac 1);
by (rtac conjI 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (EVERY1[etac allE, mp_tac]);
by (rewrite_goals_tac [exec_def,succs_def]);
by (split_tac [instr.split] 1);

by (rtac conjI 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsplits [option.split,list.split,err.split]) 1);

by (rtac conjI 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsplits [option.split,list.split]) 1);

by (rtac conjI 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsplits [option.split,list.split]) 1);

by (rtac conjI 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsplits [option.split,list.split]) 1);

by (rtac conjI 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsplits [option.split,list.split]) 1);
by (Blast_tac 1);

by (rtac conjI 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsplits [option.split,list.split]) 1);

by (rtac conjI 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsplits [option.split,list.split]) 1);

by (rtac conjI 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsplits [option.split,list.split]) 1);

by (rtac conjI 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsplits [option.split,list.split,ty.split]) 1);

by (rtac conjI 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsplits [option.split,list.split]) 1);
by (Blast_tac 1);

by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsplits [option.split,list.split]
                                addsimps [le_list_refl,le_err_refl] ) 1);
qed "wti_is_stable_topless";

Goalw [mono_def,step_def,option_map_def,lift_def,
       JVM_states_unfold,JVM_le_unfold]
 "[| wfis S md maxr bs; wf_mdict S md |] ==> \
\ mono (JVM.le S maxs maxr) (step S maxs rT bs) (size bs) (states S maxs maxr)";
by (Clarify_tac 1);
by (simp_tac (simpset() addsplits [option.split]) 1);
by (Clarify_tac 1);
by (Asm_simp_tac 1);
by (split_tac [err.split] 1);
by (rtac conjI 1);
 by (Clarify_tac 1);
by (Clarify_tac 1);
by (simp_tac (simpset() addsimps [exec_def] delsplits [split_if]) 1);
by (split_tac [instr.split] 1);

by (rtac conjI 1);
by (fast_tac (claset() addDs [le_listD] addSEs [wf_LoadD]
       addss (simpset() addsplits [err.split])) 1);

by (rtac conjI 1);
by (fast_tac (claset() addIs [list_update_le_cong,le_listD] addSEs [wf_StoreD]
       addss (simpset() addsplits [list.split])) 1);

by (rtac conjI 1);
by (Asm_simp_tac 1);

by (rtac conjI 1);
by (Asm_simp_tac 1);

by (rtac conjI 1);
by (force_tac (claset(), simpset() addsplits [list.split]) 1);

by (rtac conjI 1);
by (fast_tac (claset() delrules [r_into_rtrancl]
		       addDs [rtrancl_trans]
       addss (simpset() addsplits [list.split])) 1);

by (rtac conjI 1);
 by (Clarify_tac 1);
 by (asm_full_simp_tac (simpset() addsplits [list.split]) 1);
 by (rtac conjI 1);
  by (Clarify_tac 1);
 by (Clarify_tac 1);
 by (rtac conjI 1);
  by (Clarify_tac 1);
 by (Clarify_tac 1);
 by (rtac conjI 1);
  by (Clarify_tac 1);
 by (Clarify_tac 1);
 by (Asm_full_simp_tac 1);
 by (blast_tac (claset() addIs [rtrancl_trans,subtype_transD]) 1);

by (rtac conjI 1);
by (asm_full_simp_tac (simpset() addsimps [reflD] addsplits [list.split]) 1);

by (rtac conjI 1);
(* 39 *)
 by (Clarify_tac 1);
 by (asm_full_simp_tac (simpset() addsplits [list.split]) 1);
 by (blast_tac (claset() addIs [rtrancl_trans,subtype_transD]) 1);

by (rtac conjI 1);
by (fast_tac (claset() addss (simpset() addsplits [list.split,ty.split_asm]
                                       addsimps [is_Class_def,is_ref_def])) 1);

by (asm_simp_tac (simpset() addsplits [list.split]) 1);
by (blast_tac (claset() addIs [subtype_transD]) 1);

qed "exec_mono";


Goalw [JVM.sl_def,stk_esl_def,reg_sl_def]
 "[| single_valued S; acyclic S |] ==> semilat(JVM.sl S maxs maxr)";
by (REPEAT(ares_tac [semilat_opt,err_semilat_Product_esl,err_semilat_upto_esl,
          err_semilat_eslI,semilat_Listn_sl,err_semilat_JType_esl] 1));
qed "semilat_JVM_slI";

Goal "JVM.sl S maxs maxr == \
\     (states S maxs maxr, JVM.le S maxs maxr, JVM.sup S maxs maxr)";
by (simp_tac (simpset() addsimps [states_def,JVM.le_def,JVM.sup_def,
      surjective_pairing RS sym]) 1);
qed "sl_triple_conv";

Goalw [kiljvm_def,sl_triple_conv]
 "[| single_valued S; wf(S^-1); wfis S md maxr bs; wf_mdict S md; \
\    bounded (succs bs) (size bs) |] ==> \
\ is_bcv (JVM.le S maxs maxr) (Some Err) (wti S maxs rT bs) \
\        (size bs) (states S maxs maxr) (kiljvm S maxs maxr rT bs)";
by (rtac is_bcv_kildall 1);
      by (simp_tac (simpset() addsimps [symmetric sl_triple_conv]) 1);
      by (blast_tac (claset() addSIs [semilat_JVM_slI] addDs [wf_acyclic]) 1);
     by (simp_tac (simpset() addsimps [JVM_le_unfold]) 1);
     by (blast_tac (claset()
       addSIs [acyclic_impl_order_subtype,wf_converse_subcls1_impl_acc_subtype]
       addDs [wf_acyclic]) 1);
    by (simp_tac (simpset() addsimps [JVM_le_unfold]) 1);
   by (etac exec_pres_type 1);
   by (assume_tac 1);
  by (assume_tac 1);
 by (etac exec_mono 1);
 by (assume_tac 1);
by (etac wti_is_stable_topless 1);
qed "is_bcv_kiljvm";
