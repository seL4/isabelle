(*  Title:      HOL/MicroJava/Digest.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen

This file contains a digest of all MicroJava theorems.
Should be generated automatically in some form in the future.
*)

header {* Theorem Digest *}

theory Digest = JTypeSafe + Example + BVSpecTypeSafe + LBVCorrect + LBVComplete:

subsubsection {* Theory BVSpec *}
text {*
{\bf lemma} @{text wt_jvm_progD}:\\
@{thm [display] wt_jvm_progD [no_vars]}
\medskip

{\bf lemma} @{text wt_jvm_prog_impl_wt_instr}:\\
@{thm [display] wt_jvm_prog_impl_wt_instr [no_vars]}
\medskip

{\bf lemma} @{text wt_jvm_prog_impl_wt_start}:\\
@{thm [display] wt_jvm_prog_impl_wt_start [no_vars]}
\medskip

*}

subsubsection {* Theory BVSpecTypeSafe *}
text {*
{\bf lemma} @{text wt_jvm_prog_impl_wt_instr_cor}:\\
@{thm [display] wt_jvm_prog_impl_wt_instr_cor [no_vars]}
\medskip

{\bf lemma} @{text Load_correct}:\\
@{thm [display] Load_correct [no_vars]}
\medskip

{\bf lemma} @{text Store_correct}:\\
@{thm [display] Store_correct [no_vars]}
\medskip

{\bf lemma} @{text conf_Intg_Integer}:\\
@{thm [display] conf_Intg_Integer [no_vars]}
\medskip

{\bf lemma} @{text Bipush_correct}:\\
@{thm [display] Bipush_correct [no_vars]}
\medskip

{\bf lemma} @{text NT_subtype_conv}:\\
@{thm [display] NT_subtype_conv [no_vars]}
\medskip

{\bf lemma} @{text Aconst_null_correct}:\\
@{thm [display] Aconst_null_correct [no_vars]}
\medskip

{\bf lemma} @{text Cast_conf2}:\\
@{thm [display] Cast_conf2 [no_vars]}
\medskip

{\bf lemma} @{text Checkcast_correct}:\\
@{thm [display] Checkcast_correct [no_vars]}
\medskip

{\bf lemma} @{text Getfield_correct}:\\
@{thm [display] Getfield_correct [no_vars]}
\medskip

{\bf lemma} @{text Putfield_correct}:\\
@{thm [display] Putfield_correct [no_vars]}
\medskip

{\bf lemma} @{text collapse_paired_All}:\\
@{thm [display] collapse_paired_All [no_vars]}
\medskip

{\bf lemma} @{text New_correct}:\\
@{thm [display] New_correct [no_vars]}
\medskip

{\bf lemma} @{text Invoke_correct}:\\
@{thm [display] Invoke_correct [no_vars]}
\medskip

{\bf lemma} @{text Return_correct}:\\
@{thm [display] Return_correct [no_vars]}
\medskip

{\bf lemma} @{text Goto_correct}:\\
@{thm [display] Goto_correct [no_vars]}
\medskip

{\bf lemma} @{text Ifcmpeq_correct}:\\
@{thm [display] Ifcmpeq_correct [no_vars]}
\medskip

{\bf lemma} @{text Pop_correct}:\\
@{thm [display] Pop_correct [no_vars]}
\medskip

{\bf lemma} @{text Dup_correct}:\\
@{thm [display] Dup_correct [no_vars]}
\medskip

{\bf lemma} @{text Dup_x1_correct}:\\
@{thm [display] Dup_x1_correct [no_vars]}
\medskip

{\bf lemma} @{text Dup_x2_correct}:\\
@{thm [display] Dup_x2_correct [no_vars]}
\medskip

{\bf lemma} @{text Swap_correct}:\\
@{thm [display] Swap_correct [no_vars]}
\medskip

{\bf lemma} @{text IAdd_correct}:\\
@{thm [display] IAdd_correct [no_vars]}
\medskip

{\bf lemma} @{text instr_correct}:\\
@{thm [display] instr_correct [no_vars]}
\medskip

{\bf lemma} @{text correct_state_impl_Some_method}:\\
@{thm [display] correct_state_impl_Some_method [no_vars]}
\medskip

{\bf lemma} @{text BV_correct_1}:\\
@{thm [display] BV_correct_1 [no_vars]}
\medskip

{\bf lemma} @{text L0}:\\
@{thm [display] L0 [no_vars]}
\medskip

{\bf lemma} @{text L1}:\\
@{thm [display] L1 [no_vars]}
\medskip

{\bf theorem} @{text BV_correct}:\\
@{thm [display] BV_correct [no_vars]}
\medskip

{\bf theorem} @{text BV_correct_initial}:\\
@{thm [display] BV_correct_initial [no_vars]}
\medskip

*}

subsubsection {* Theory Conform *}
text {*
{\bf theorem} @{text conf_VoidI}:\\
@{thm [display] conf_VoidI [no_vars]}
\medskip

{\bf theorem} @{text conf_BooleanI}:\\
@{thm [display] conf_BooleanI [no_vars]}
\medskip

{\bf theorem} @{text conf_IntegerI}:\\
@{thm [display] conf_IntegerI [no_vars]}
\medskip

{\bf theorem} @{text defval_conf}:\\
@{thm [display] defval_conf [no_vars]}
\medskip

{\bf theorem} @{text conf_widen}:\\
@{thm [display] conf_widen [no_vars]}
\medskip

{\bf theorem} @{text conf_hext}:\\
@{thm [display] conf_hext [no_vars]}
\medskip

{\bf theorem} @{text conf_RefTD}:\\
@{thm [display] conf_RefTD [no_vars]}
\medskip

{\bf theorem} @{text non_np_objD'}:\\
@{thm [display] non_np_objD' [no_vars]}
\medskip

{\bf theorem} @{text conf_list_gext_widen}:\\
@{thm [display] conf_list_gext_widen [no_vars]}
\medskip

{\bf theorem} @{text lconf_upd}:\\
@{thm [display] lconf_upd [no_vars]}
\medskip

{\bf theorem} @{text lconf_init_vars_lemma}:\\
@{thm [display] lconf_init_vars_lemma [no_vars]}
\medskip

{\bf theorem} @{text lconf_init_vars}:\\
@{thm [display] lconf_init_vars [no_vars]}
\medskip

{\bf theorem} @{text lconf_ext_list}:\\
@{thm [display] lconf_ext_list [no_vars]}
\medskip

{\bf theorem} @{text hconfD}:\\
@{thm [display] hconfD [no_vars]}
\medskip

{\bf theorem} @{text hconfI}:\\
@{thm [display] hconfI [no_vars]}
\medskip

{\bf theorem} @{text conforms_hext}:\\
@{thm [display] conforms_hext [no_vars]}
\medskip

{\bf theorem} @{text conforms_upd_obj}:\\
@{thm [display] conforms_upd_obj [no_vars]}
\medskip

{\bf theorem} @{text conforms_upd_local}:\\
@{thm [display] conforms_upd_local [no_vars]}
\medskip

*}

subsubsection {* Theory Convert *}
text {*
{\bf lemma} @{text not_Err_eq}:\\
@{thm [display] not_Err_eq [no_vars]}
\medskip

{\bf lemma} @{text not_Some_eq}:\\
@{thm [display] not_Some_eq [no_vars]}
\medskip

{\bf lemma} @{text lift_top_refl}:\\
@{thm [display] lift_top_refl [no_vars]}
\medskip

{\bf lemma} @{text lift_top_trans}:\\
@{thm [display] lift_top_trans [no_vars]}
\medskip

{\bf lemma} @{text lift_top_Err_any}:\\
@{thm [display] lift_top_Err_any [no_vars]}
\medskip

{\bf lemma} @{text lift_top_OK_OK}:\\
@{thm [display] lift_top_OK_OK [no_vars]}
\medskip

{\bf lemma} @{text lift_top_any_OK}:\\
@{thm [display] lift_top_any_OK [no_vars]}
\medskip

{\bf lemma} @{text lift_top_OK_any}:\\
@{thm [display] lift_top_OK_any [no_vars]}
\medskip

{\bf lemma} @{text lift_bottom_refl}:\\
@{thm [display] lift_bottom_refl [no_vars]}
\medskip

{\bf lemma} @{text lift_bottom_trans}:\\
@{thm [display] lift_bottom_trans [no_vars]}
\medskip

{\bf lemma} @{text lift_bottom_any_None}:\\
@{thm [display] lift_bottom_any_None [no_vars]}
\medskip

{\bf lemma} @{text lift_bottom_Some_Some}:\\
@{thm [display] lift_bottom_Some_Some [no_vars]}
\medskip

{\bf lemma} @{text lift_bottom_any_Some}:\\
@{thm [display] lift_bottom_any_Some [no_vars]}
\medskip

{\bf lemma} @{text lift_bottom_Some_any}:\\
@{thm [display] lift_bottom_Some_any [no_vars]}
\medskip

{\bf theorem} @{text sup_ty_opt_refl}:\\
@{thm [display] sup_ty_opt_refl [no_vars]}
\medskip

{\bf theorem} @{text sup_loc_refl}:\\
@{thm [display] sup_loc_refl [no_vars]}
\medskip

{\bf theorem} @{text sup_state_refl}:\\
@{thm [display] sup_state_refl [no_vars]}
\medskip

{\bf theorem} @{text sup_state_opt_refl}:\\
@{thm [display] sup_state_opt_refl [no_vars]}
\medskip

{\bf theorem} @{text anyConvErr}:\\
@{thm [display] anyConvErr [no_vars]}
\medskip

{\bf theorem} @{text OKanyConvOK}:\\
@{thm [display] OKanyConvOK [no_vars]}
\medskip

{\bf theorem} @{text sup_ty_opt_OK}:\\
@{thm [display] sup_ty_opt_OK [no_vars]}
\medskip

{\bf lemma} @{text widen_PrimT_conv1}:\\
@{thm [display] widen_PrimT_conv1 [no_vars]}
\medskip

{\bf theorem} @{text sup_PTS_eq}:\\
@{thm [display] sup_PTS_eq [no_vars]}
\medskip

{\bf theorem} @{text sup_loc_Nil}:\\
@{thm [display] sup_loc_Nil [no_vars]}
\medskip

{\bf theorem} @{text sup_loc_Cons}:\\
@{thm [display] sup_loc_Cons [no_vars]}
\medskip

{\bf theorem} @{text sup_loc_Cons2}:\\
@{thm [display] sup_loc_Cons2 [no_vars]}
\medskip

{\bf theorem} @{text sup_loc_length}:\\
@{thm [display] sup_loc_length [no_vars]}
\medskip

{\bf theorem} @{text sup_loc_nth}:\\
@{thm [display] sup_loc_nth [no_vars]}
\medskip

{\bf theorem} @{text all_nth_sup_loc}:\\
@{thm [display] all_nth_sup_loc [no_vars]}
\medskip

{\bf theorem} @{text sup_loc_append}:\\
@{thm [display] sup_loc_append [no_vars]}
\medskip

{\bf theorem} @{text sup_loc_rev}:\\
@{thm [display] sup_loc_rev [no_vars]}
\medskip

{\bf theorem} @{text sup_loc_update}:\\
@{thm [display] sup_loc_update [no_vars]}
\medskip

{\bf theorem} @{text sup_state_length}:\\
@{thm [display] sup_state_length [no_vars]}
\medskip

{\bf theorem} @{text sup_state_append_snd}:\\
@{thm [display] sup_state_append_snd [no_vars]}
\medskip

{\bf theorem} @{text sup_state_append_fst}:\\
@{thm [display] sup_state_append_fst [no_vars]}
\medskip

{\bf theorem} @{text sup_state_Cons1}:\\
@{thm [display] sup_state_Cons1 [no_vars]}
\medskip

{\bf theorem} @{text sup_state_Cons2}:\\
@{thm [display] sup_state_Cons2 [no_vars]}
\medskip

{\bf theorem} @{text sup_state_ignore_fst}:\\
@{thm [display] sup_state_ignore_fst [no_vars]}
\medskip

{\bf theorem} @{text sup_state_rev_fst}:\\
@{thm [display] sup_state_rev_fst [no_vars]}
\medskip

{\bf lemma} @{text sup_state_opt_None_any}:\\
@{thm [display] sup_state_opt_None_any [no_vars]}
\medskip

{\bf lemma} @{text sup_state_opt_any_None}:\\
@{thm [display] sup_state_opt_any_None [no_vars]}
\medskip

{\bf lemma} @{text sup_state_opt_Some_Some}:\\
@{thm [display] sup_state_opt_Some_Some [no_vars]}
\medskip

{\bf lemma} @{text sup_state_opt_any_Some}:\\
@{thm [display] sup_state_opt_any_Some [no_vars]}
\medskip

{\bf lemma} @{text sup_state_opt_Some_any}:\\
@{thm [display] sup_state_opt_Some_any [no_vars]}
\medskip

{\bf theorem} @{text sup_ty_opt_trans}:\\
@{thm [display] sup_ty_opt_trans [no_vars]}
\medskip

{\bf theorem} @{text sup_loc_trans}:\\
@{thm [display] sup_loc_trans [no_vars]}
\medskip

{\bf theorem} @{text sup_state_trans}:\\
@{thm [display] sup_state_trans [no_vars]}
\medskip

{\bf theorem} @{text sup_state_opt_trans}:\\
@{thm [display] sup_state_opt_trans [no_vars]}
\medskip

*}

subsubsection {* Theory Correct *}
text {*
{\bf lemma} @{text sup_heap_newref}:\\
@{thm [display] sup_heap_newref [no_vars]}
\medskip

{\bf lemma} @{text sup_heap_update_value}:\\
@{thm [display] sup_heap_update_value [no_vars]}
\medskip

{\bf lemma} @{text approx_val_Err}:\\
@{thm [display] approx_val_Err [no_vars]}
\medskip

{\bf lemma} @{text approx_val_Null}:\\
@{thm [display] approx_val_Null [no_vars]}
\medskip

{\bf lemma} @{text approx_val_imp_approx_val_assConvertible}:\\
@{thm [display] approx_val_imp_approx_val_assConvertible [no_vars]}
\medskip

{\bf lemma} @{text approx_val_imp_approx_val_sup_heap}:\\
@{thm [display] approx_val_imp_approx_val_sup_heap [no_vars]}
\medskip

{\bf lemma} @{text approx_val_imp_approx_val_heap_update}:\\
@{thm [display] approx_val_imp_approx_val_heap_update [no_vars]}
\medskip

{\bf lemma} @{text approx_val_imp_approx_val_sup}:\\
@{thm [display] approx_val_imp_approx_val_sup [no_vars]}
\medskip

{\bf lemma} @{text approx_loc_imp_approx_val_sup}:\\
@{thm [display] approx_loc_imp_approx_val_sup [no_vars]}
\medskip

{\bf lemma} @{text approx_loc_Cons}:\\
@{thm [display] approx_loc_Cons [no_vars]}
\medskip

{\bf lemma} @{text assConv_approx_stk_imp_approx_loc}:\\
@{thm [display] assConv_approx_stk_imp_approx_loc [no_vars]}
\medskip

{\bf lemma} @{text approx_loc_imp_approx_loc_sup_heap}:\\
@{thm [display] approx_loc_imp_approx_loc_sup_heap [no_vars]}
\medskip

{\bf lemma} @{text approx_loc_imp_approx_loc_sup}:\\
@{thm [display] approx_loc_imp_approx_loc_sup [no_vars]}
\medskip

{\bf lemma} @{text approx_loc_imp_approx_loc_subst}:\\
@{thm [display] approx_loc_imp_approx_loc_subst [no_vars]}
\medskip

{\bf lemma} @{text approx_loc_append}:\\
@{thm [display] approx_loc_append [no_vars]}
\medskip

{\bf lemma} @{text approx_stk_rev_lem}:\\
@{thm [display] approx_stk_rev_lem [no_vars]}
\medskip

{\bf lemma} @{text approx_stk_rev}:\\
@{thm [display] approx_stk_rev [no_vars]}
\medskip

{\bf lemma} @{text approx_stk_imp_approx_stk_sup_heap}:\\
@{thm [display] approx_stk_imp_approx_stk_sup_heap [no_vars]}
\medskip

{\bf lemma} @{text approx_stk_imp_approx_stk_sup}:\\
@{thm [display] approx_stk_imp_approx_stk_sup [no_vars]}
\medskip

{\bf lemma} @{text approx_stk_Nil}:\\
@{thm [display] approx_stk_Nil [no_vars]}
\medskip

{\bf lemma} @{text approx_stk_Cons}:\\
@{thm [display] approx_stk_Cons [no_vars]}
\medskip

{\bf lemma} @{text approx_stk_Cons_lemma}:\\
@{thm [display] approx_stk_Cons_lemma [no_vars]}
\medskip

{\bf lemma} @{text approx_stk_append_lemma}:\\
@{thm [display] approx_stk_append_lemma [no_vars]}
\medskip

{\bf lemma} @{text correct_init_obj}:\\
@{thm [display] correct_init_obj [no_vars]}
\medskip

{\bf lemma} @{text oconf_imp_oconf_field_update}:\\
@{thm [display] oconf_imp_oconf_field_update [no_vars]}
\medskip

{\bf lemma} @{text oconf_imp_oconf_heap_newref}:\\
@{thm [display] oconf_imp_oconf_heap_newref [no_vars]}
\medskip

{\bf lemma} @{text oconf_imp_oconf_heap_update}:\\
@{thm [display] oconf_imp_oconf_heap_update [no_vars]}
\medskip

{\bf lemma} @{text hconf_imp_hconf_newref}:\\
@{thm [display] hconf_imp_hconf_newref [no_vars]}
\medskip

{\bf lemma} @{text hconf_imp_hconf_field_update}:\\
@{thm [display] hconf_imp_hconf_field_update [no_vars]}
\medskip

{\bf lemma} @{text correct_frames_imp_correct_frames_field_update}:\\
@{thm [display] correct_frames_imp_correct_frames_field_update [no_vars]}
\medskip

{\bf lemma} @{text correct_frames_imp_correct_frames_newref}:\\
@{thm [display] correct_frames_imp_correct_frames_newref [no_vars]}
\medskip

*}

subsubsection {* Theory Decl *}
text {*
no theorems
*}

subsubsection {* Theory Digest *}
text {*
no theorems
*}

subsubsection {* Theory Eval *}
text {*
{\bf theorem} @{text NewCI}:\\
@{thm [display] NewCI [no_vars]}
\medskip

{\bf theorem} @{text eval_evals_exec_no_xcpt}:\\
@{thm [display] eval_evals_exec_no_xcpt [no_vars]}
\medskip

*}

subsubsection {* Theory Example *}
text {*
{\bf theorem} @{text not_Object_subcls}:\\
@{thm [display] not_Object_subcls [no_vars]}
\medskip

{\bf theorem} @{text subcls_ObjectD}:\\
@{thm [display] subcls_ObjectD [no_vars]}
\medskip

{\bf theorem} @{text not_Base_subcls_Ext}:\\
@{thm [display] not_Base_subcls_Ext [no_vars]}
\medskip

{\bf theorem} @{text class_tprgD}:\\
@{thm [display] class_tprgD [no_vars]}
\medskip

{\bf theorem} @{text not_class_subcls_class}:\\
@{thm [display] not_class_subcls_class [no_vars]}
\medskip

{\bf theorem} @{text unique_classes}:\\
@{thm [display] unique_classes [no_vars]}
\medskip

{\bf theorem} @{text subcls_direct}:\\
@{thm [display] subcls_direct [no_vars]}
\medskip

{\bf theorem} @{text Ext_subcls_Base}:\\
@{thm [display] Ext_subcls_Base [no_vars]}
\medskip

{\bf theorem} @{text Ext_widen_Base}:\\
@{thm [display] Ext_widen_Base [no_vars]}
\medskip

{\bf theorem} @{text acyclic_subcls1_}:\\
@{thm [display] acyclic_subcls1_ [no_vars]}
\medskip

{\bf theorem} @{text fields_Object}:\\
@{thm [display] fields_Object [no_vars]}
\medskip

{\bf theorem} @{text fields_Base}:\\
@{thm [display] fields_Base [no_vars]}
\medskip

{\bf theorem} @{text fields_Ext}:\\
@{thm [display] fields_Ext [no_vars]}
\medskip

{\bf theorem} @{text method_Object}:\\
@{thm [display] method_Object [no_vars]}
\medskip

{\bf theorem} @{text method_Base}:\\
@{thm [display] method_Base [no_vars]}
\medskip

{\bf theorem} @{text method_Ext}:\\
@{thm [display] method_Ext [no_vars]}
\medskip

{\bf theorem} @{text wf_foo_Base}:\\
@{thm [display] wf_foo_Base [no_vars]}
\medskip

{\bf theorem} @{text wf_foo_Ext}:\\
@{thm [display] wf_foo_Ext [no_vars]}
\medskip

{\bf theorem} @{text wf_ObjectC}:\\
@{thm [display] wf_ObjectC [no_vars]}
\medskip

{\bf theorem} @{text wf_BaseC}:\\
@{thm [display] wf_BaseC [no_vars]}
\medskip

{\bf theorem} @{text wf_ExtC}:\\
@{thm [display] wf_ExtC [no_vars]}
\medskip

{\bf theorem} @{text wf_tprg}:\\
@{thm [display] wf_tprg [no_vars]}
\medskip

{\bf theorem} @{text appl_methds_foo_Base}:\\
@{thm [display] appl_methds_foo_Base [no_vars]}
\medskip

{\bf theorem} @{text max_spec_foo_Base}:\\
@{thm [display] max_spec_foo_Base [no_vars]}
\medskip

{\bf theorem} @{text wt_test}:\\
@{thm [display] wt_test [no_vars]}
\medskip

{\bf theorem} @{text exec_test}:\\
@{thm [display] exec_test [no_vars]}
\medskip

*}

subsubsection {* Theory JBasis *}
text {*
{\bf theorem} @{text image_rev}:\\
@{thm [display] image_rev [no_vars]}
\medskip

{\bf theorem} @{text some_subset_the}:\\
@{thm [display] some_subset_the [no_vars]}
\medskip

{\bf theorem} @{text fst_in_set_lemma}:\\
@{thm [display] fst_in_set_lemma [no_vars]}
\medskip

{\bf theorem} @{text unique_Nil}:\\
@{thm [display] unique_Nil [no_vars]}
\medskip

{\bf theorem} @{text unique_Cons}:\\
@{thm [display] unique_Cons [no_vars]}
\medskip

{\bf theorem} @{text unique_append}:\\
@{thm [display] unique_append [no_vars]}
\medskip

{\bf theorem} @{text unique_map_inj}:\\
@{thm [display] unique_map_inj [no_vars]}
\medskip

{\bf theorem} @{text unique_map_Pair}:\\
@{thm [display] unique_map_Pair [no_vars]}
\medskip

{\bf theorem} @{text image_cong}:\\
@{thm [display] image_cong [no_vars]}
\medskip

{\bf theorem} @{text unique_map_of_Some_conv}:\\
@{thm [display] unique_map_of_Some_conv [no_vars]}
\medskip

{\bf theorem} @{text Ball_set_table}:\\
@{thm [display] Ball_set_table [no_vars]}
\medskip

{\bf theorem} @{text map_of_map}:\\
@{thm [display] map_of_map [no_vars]}
\medskip

*}

subsubsection {* Theory JTypeSafe *}
text {*
{\bf theorem} @{text NewC_conforms}:\\
@{thm [display] NewC_conforms [no_vars]}
\medskip

{\bf theorem} @{text Cast_conf}:\\
@{thm [display] Cast_conf [no_vars]}
\medskip

{\bf theorem} @{text FAcc_type_sound}:\\
@{thm [display] FAcc_type_sound [no_vars]}
\medskip

{\bf theorem} @{text FAss_type_sound}:\\
@{thm [display] FAss_type_sound [no_vars]}
\medskip

{\bf theorem} @{text Call_lemma2}:\\
@{thm [display] Call_lemma2 [no_vars]}
\medskip

{\bf theorem} @{text Call_type_sound}:\\
@{thm [display] Call_type_sound [no_vars]}
\medskip

{\bf theorem} @{text eval_evals_exec_type_sound}:\\
@{thm [display] eval_evals_exec_type_sound [no_vars]}
\medskip

{\bf theorem} @{text eval_type_sound}:\\
@{thm [display] eval_type_sound [no_vars]}
\medskip

{\bf theorem} @{text exec_type_sound}:\\
@{thm [display] exec_type_sound [no_vars]}
\medskip

{\bf theorem} @{text all_methods_understood}:\\
@{thm [display] all_methods_understood [no_vars]}
\medskip

*}

subsubsection {* Theory JVMExec *}
text {*
no theorems
*}

subsubsection {* Theory JVMExecInstr *}
text {*
no theorems
*}

subsubsection {* Theory JVMInstructions *}
text {*
no theorems
*}

subsubsection {* Theory JVMState *}
text {*
no theorems
*}

subsubsection {* Theory LBVComplete *}
text {*
{\bf lemma} @{text make_cert_target}:\\
@{thm [display] make_cert_target [no_vars]}
\medskip

{\bf lemma} @{text make_cert_approx}:\\
@{thm [display] make_cert_approx [no_vars]}
\medskip

{\bf lemma} @{text make_cert_contains_targets}:\\
@{thm [display] make_cert_contains_targets [no_vars]}
\medskip

{\bf theorem} @{text fits_make_cert}:\\
@{thm [display] fits_make_cert [no_vars]}
\medskip

{\bf lemma} @{text fitsD}:\\
@{thm [display] fitsD [no_vars]}
\medskip

{\bf lemma} @{text fitsD2}:\\
@{thm [display] fitsD2 [no_vars]}
\medskip

{\bf lemma} @{text wtl_inst_mono}:\\
@{thm [display] wtl_inst_mono [no_vars]}
\medskip

{\bf lemma} @{text wtl_cert_mono}:\\
@{thm [display] wtl_cert_mono [no_vars]}
\medskip

{\bf lemma} @{text wt_instr_imp_wtl_inst}:\\
@{thm [display] wt_instr_imp_wtl_inst [no_vars]}
\medskip

{\bf lemma} @{text wt_less_wtl}:\\
@{thm [display] wt_less_wtl [no_vars]}
\medskip

{\bf lemma} @{text wt_instr_imp_wtl_cert}:\\
@{thm [display] wt_instr_imp_wtl_cert [no_vars]}
\medskip

{\bf lemma} @{text wt_less_wtl_cert}:\\
@{thm [display] wt_less_wtl_cert [no_vars]}
\medskip

{\bf theorem} @{text wt_imp_wtl_inst_list}:\\
@{thm [display] wt_imp_wtl_inst_list [no_vars]}
\medskip

{\bf lemma} @{text fits_imp_wtl_method_complete}:\\
@{thm [display] fits_imp_wtl_method_complete [no_vars]}
\medskip

{\bf lemma} @{text wtl_method_complete}:\\
@{thm [display] wtl_method_complete [no_vars]}
\medskip

{\bf lemma} @{text unique_set}:\\
@{thm [display] unique_set [no_vars]}
\medskip

{\bf lemma} @{text unique_epsilon}:\\
@{thm [display] unique_epsilon [no_vars]}
\medskip

{\bf theorem} @{text wtl_complete}:\\
@{thm [display] wtl_complete [no_vars]}
\medskip

*}

subsubsection {* Theory LBVCorrect *}
text {*
{\bf lemma} @{text fitsD_None}:\\
@{thm [display] fitsD_None [no_vars]}
\medskip

{\bf lemma} @{text fitsD_Some}:\\
@{thm [display] fitsD_Some [no_vars]}
\medskip

{\bf lemma} @{text make_phi_Some}:\\
@{thm [display] make_phi_Some [no_vars]}
\medskip

{\bf lemma} @{text make_phi_None}:\\
@{thm [display] make_phi_None [no_vars]}
\medskip

{\bf lemma} @{text exists_phi}:\\
@{thm [display] exists_phi [no_vars]}
\medskip

{\bf lemma} @{text fits_lemma1}:\\
@{thm [display] fits_lemma1 [no_vars]}
\medskip

{\bf lemma} @{text wtl_suc_pc}:\\
@{thm [display] wtl_suc_pc [no_vars]}
\medskip

{\bf lemma} @{text wtl_fits_wt}:\\
@{thm [display] wtl_fits_wt [no_vars]}
\medskip

{\bf lemma} @{text fits_first}:\\
@{thm [display] fits_first [no_vars]}
\medskip

{\bf lemma} @{text wtl_method_correct}:\\
@{thm [display] wtl_method_correct [no_vars]}
\medskip

{\bf lemma} @{text unique_set}:\\
@{thm [display] unique_set [no_vars]}
\medskip

{\bf lemma} @{text unique_epsilon}:\\
@{thm [display] unique_epsilon [no_vars]}
\medskip

{\bf theorem} @{text wtl_correct}:\\
@{thm [display] wtl_correct [no_vars]}
\medskip

*}

subsubsection {* Theory LBVSpec *}
text {*
{\bf lemma} @{text wtl_inst_OK}:\\
@{thm [display] wtl_inst_OK [no_vars]}
\medskip

{\bf lemma} @{text strict_Some}:\\
@{thm [display] strict_Some [no_vars]}
\medskip

{\bf lemma} @{text wtl_Cons}:\\
@{thm [display] wtl_Cons [no_vars]}
\medskip

{\bf lemma} @{text wtl_append}:\\
@{thm [display] wtl_append [no_vars]}
\medskip

{\bf lemma} @{text wtl_take}:\\
@{thm [display] wtl_take [no_vars]}
\medskip

{\bf lemma} @{text take_Suc}:\\
@{thm [display] take_Suc [no_vars]}
\medskip

{\bf lemma} @{text wtl_Suc}:\\
@{thm [display] wtl_Suc [no_vars]}
\medskip

{\bf lemma} @{text wtl_all}:\\
@{thm [display] wtl_all [no_vars]}
\medskip

*}

subsubsection {* Theory State *}
text {*
{\bf theorem} @{text np_raise_if}:\\
@{thm [display] np_raise_if [no_vars]}
\medskip

*}

subsubsection {* Theory Step *}
text {*
{\bf lemma} @{text 1}:\\
@{thm [display] 1 [no_vars]}
\medskip

{\bf lemma} @{text 2}:\\
@{thm [display] 2 [no_vars]}
\medskip

{\bf lemma} @{text appNone}:\\
@{thm [display] appNone [no_vars]}
\medskip

{\bf lemma} @{text appLoad}:\\
@{thm [display] appLoad [no_vars]}
\medskip

{\bf lemma} @{text appStore}:\\
@{thm [display] appStore [no_vars]}
\medskip

{\bf lemma} @{text appBipush}:\\
@{thm [display] appBipush [no_vars]}
\medskip

{\bf lemma} @{text appAconst}:\\
@{thm [display] appAconst [no_vars]}
\medskip

{\bf lemma} @{text appGetField}:\\
@{thm [display] appGetField [no_vars]}
\medskip

{\bf lemma} @{text appPutField}:\\
@{thm [display] appPutField [no_vars]}
\medskip

{\bf lemma} @{text appNew}:\\
@{thm [display] appNew [no_vars]}
\medskip

{\bf lemma} @{text appCheckcast}:\\
@{thm [display] appCheckcast [no_vars]}
\medskip

{\bf lemma} @{text appPop}:\\
@{thm [display] appPop [no_vars]}
\medskip

{\bf lemma} @{text appDup}:\\
@{thm [display] appDup [no_vars]}
\medskip

{\bf lemma} @{text appDup_x1}:\\
@{thm [display] appDup_x1 [no_vars]}
\medskip

{\bf lemma} @{text appDup_x2}:\\
@{thm [display] appDup_x2 [no_vars]}
\medskip

{\bf lemma} @{text appSwap}:\\
@{thm [display] appSwap [no_vars]}
\medskip

{\bf lemma} @{text appIAdd}:\\
@{thm [display] appIAdd [no_vars]}
\medskip

{\bf lemma} @{text appIfcmpeq}:\\
@{thm [display] appIfcmpeq [no_vars]}
\medskip

{\bf lemma} @{text appReturn}:\\
@{thm [display] appReturn [no_vars]}
\medskip

{\bf lemma} @{text appGoto}:\\
@{thm [display] appGoto [no_vars]}
\medskip

{\bf lemma} @{text appInvoke}:\\
@{thm [display] appInvoke [no_vars]}
\medskip

{\bf lemma} @{text step_Some}:\\
@{thm [display] step_Some [no_vars]}
\medskip

{\bf lemma} @{text step_None}:\\
@{thm [display] step_None [no_vars]}
\medskip

*}

subsubsection {* Theory StepMono *}
text {*
{\bf lemma} @{text PrimT_PrimT}:\\
@{thm [display] PrimT_PrimT [no_vars]}
\medskip

{\bf lemma} @{text sup_loc_some}:\\
@{thm [display] sup_loc_some [no_vars]}
\medskip

{\bf lemma} @{text all_widen_is_sup_loc}:\\
@{thm [display] all_widen_is_sup_loc [no_vars]}
\medskip

{\bf lemma} @{text append_length_n}:\\
@{thm [display] append_length_n [no_vars]}
\medskip

{\bf lemma} @{text rev_append_cons}:\\
@{thm [display] rev_append_cons [no_vars]}
\medskip

{\bf lemma} @{text app_mono}:\\
@{thm [display] app_mono [no_vars]}
\medskip

{\bf lemma} @{text step_mono_Some}:\\
@{thm [display] step_mono_Some [no_vars]}
\medskip

{\bf lemma} @{text step_mono}:\\
@{thm [display] step_mono [no_vars]}
\medskip

*}

subsubsection {* Theory Store *}
text {*
{\bf theorem} @{text newref_None}:\\
@{thm [display] newref_None [no_vars]}
\medskip

*}

subsubsection {* Theory Term *}
text {*
no theorems
*}

subsubsection {* Theory Type *}
text {*
no theorems
*}

subsubsection {* Theory TypeRel *}
text {*
{\bf theorem} @{text finite_subcls1}:\\
@{thm [display] finite_subcls1 [no_vars]}
\medskip

{\bf theorem} @{text subcls_is_class}:\\
@{thm [display] subcls_is_class [no_vars]}
\medskip

{\bf theorem} @{text wf_rel_lemma}:\\
@{thm [display] wf_rel_lemma [no_vars]}
\medskip

{\bf theorem} @{text wf_subcls1_rel}:\\
@{thm [display] wf_subcls1_rel [no_vars]}
\medskip

{\bf theorem} @{text widen_PrimT_RefT}:\\
@{thm [display] widen_PrimT_RefT [no_vars]}
\medskip

{\bf theorem} @{text widen_RefT}:\\
@{thm [display] widen_RefT [no_vars]}
\medskip

{\bf theorem} @{text widen_RefT2}:\\
@{thm [display] widen_RefT2 [no_vars]}
\medskip

{\bf theorem} @{text widen_Class}:\\
@{thm [display] widen_Class [no_vars]}
\medskip

{\bf theorem} @{text widen_Class_NullT}:\\
@{thm [display] widen_Class_NullT [no_vars]}
\medskip

{\bf theorem} @{text widen_Class_Class}:\\
@{thm [display] widen_Class_Class [no_vars]}
\medskip

{\bf theorem} @{text widen_trans}:\\
@{thm [display] widen_trans [no_vars]}
\medskip

*}

subsubsection {* Theory Value *}
text {*
no theorems
*}

subsubsection {* Theory WellForm *}
text {*
{\bf theorem} @{text subcls1_wfD}:\\
@{thm [display] subcls1_wfD [no_vars]}
\medskip

{\bf theorem} @{text subcls_asym}:\\
@{thm [display] subcls_asym [no_vars]}
\medskip

{\bf theorem} @{text subcls_induct}:\\
@{thm [display] subcls_induct [no_vars]}
\medskip

{\bf theorem} @{text subcls1_induct}:\\
@{thm [display] subcls1_induct [no_vars]}
\medskip

{\bf theorem} @{text method_rec_lemma}:\\
@{thm [display] method_rec_lemma [no_vars]}
\medskip

{\bf theorem} @{text method_rec}:\\
@{thm [display] method_rec [no_vars]}
\medskip

{\bf theorem} @{text fields_rec_lemma}:\\
@{thm [display] fields_rec_lemma [no_vars]}
\medskip

{\bf theorem} @{text fields_rec}:\\
@{thm [display] fields_rec [no_vars]}
\medskip

{\bf theorem} @{text subcls_C_Object}:\\
@{thm [display] subcls_C_Object [no_vars]}
\medskip

{\bf theorem} @{text fields_mono}:\\
@{thm [display] fields_mono [no_vars]}
\medskip

{\bf theorem} @{text widen_fields_defpl'}:\\
@{thm [display] widen_fields_defpl' [no_vars]}
\medskip

{\bf theorem} @{text widen_fields_defpl}:\\
@{thm [display] widen_fields_defpl [no_vars]}
\medskip

{\bf theorem} @{text unique_fields}:\\
@{thm [display] unique_fields [no_vars]}
\medskip

{\bf theorem} @{text widen_fields_mono}:\\
@{thm [display] widen_fields_mono [no_vars]}
\medskip

{\bf theorem} @{text widen_cfs_fields}:\\
@{thm [display] widen_cfs_fields [no_vars]}
\medskip

{\bf theorem} @{text method_wf_mdecl}:\\
@{thm [display] method_wf_mdecl [no_vars]}
\medskip

{\bf theorem} @{text subcls_widen_methd}:\\
@{thm [display] subcls_widen_methd [no_vars]}
\medskip

{\bf theorem} @{text subtype_widen_methd}:\\
@{thm [display] subtype_widen_methd [no_vars]}
\medskip

{\bf theorem} @{text method_in_md}:\\
@{thm [display] method_in_md [no_vars]}
\medskip

{\bf theorem} @{text is_type_fields}:\\
@{thm [display] is_type_fields [no_vars]}
\medskip

*}

subsubsection {* Theory WellType *}
text {*
{\bf theorem} @{text widen_methd}:\\
@{thm [display] widen_methd [no_vars]}
\medskip

{\bf theorem} @{text Call_lemma}:\\
@{thm [display] Call_lemma [no_vars]}
\medskip

{\bf theorem} @{text method_Object}:\\
@{thm [display] method_Object [no_vars]}
\medskip

{\bf theorem} @{text max_spec2appl_meths}:\\
@{thm [display] max_spec2appl_meths [no_vars]}
\medskip

{\bf theorem} @{text appl_methsD}:\\
@{thm [display] appl_methsD [no_vars]}
\medskip

*}
end
