(*  Title:      HOL/UNITY/UNITY_tactics.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge

Specialized UNITY tactics, and ML bindings of theorems
*)

(*Union*)
val Init_SKIP = thm "Init_SKIP";
val Acts_SKIP = thm "Acts_SKIP";
val AllowedActs_SKIP = thm "AllowedActs_SKIP";
val reachable_SKIP = thm "reachable_SKIP";
val SKIP_in_constrains_iff = thm "SKIP_in_constrains_iff";
val SKIP_in_Constrains_iff = thm "SKIP_in_Constrains_iff";
val SKIP_in_stable = thm "SKIP_in_stable";
val Init_Join = thm "Init_Join";
val Acts_Join = thm "Acts_Join";
val AllowedActs_Join = thm "AllowedActs_Join";
val JN_empty = thm "JN_empty";
val JN_insert = thm "JN_insert";
val Init_JN = thm "Init_JN";
val Acts_JN = thm "Acts_JN";
val AllowedActs_JN = thm "AllowedActs_JN";
val JN_cong = thm "JN_cong";
val Join_commute = thm "Join_commute";
val Join_assoc = thm "Join_assoc";
val Join_left_commute = thm "Join_left_commute";
val Join_SKIP_left = thm "Join_SKIP_left";
val Join_SKIP_right = thm "Join_SKIP_right";
val Join_absorb = thm "Join_absorb";
val Join_left_absorb = thm "Join_left_absorb";
val Join_ac = thms "Join_ac";
val JN_absorb = thm "JN_absorb";
val JN_Un = thm "JN_Un";
val JN_constant = thm "JN_constant";
val JN_Join_distrib = thm "JN_Join_distrib";
val JN_Join_miniscope = thm "JN_Join_miniscope";
val JN_Join_diff = thm "JN_Join_diff";
val JN_constrains = thm "JN_constrains";
val Join_constrains = thm "Join_constrains";
val Join_unless = thm "Join_unless";
val Join_constrains_weaken = thm "Join_constrains_weaken";
val JN_constrains_weaken = thm "JN_constrains_weaken";
val JN_stable = thm "JN_stable";
val invariant_JN_I = thm "invariant_JN_I";
val Join_stable = thm "Join_stable";
val Join_increasing = thm "Join_increasing";
val invariant_JoinI = thm "invariant_JoinI";
val FP_JN = thm "FP_JN";
val JN_transient = thm "JN_transient";
val Join_transient = thm "Join_transient";
val Join_transient_I1 = thm "Join_transient_I1";
val Join_transient_I2 = thm "Join_transient_I2";
val JN_ensures = thm "JN_ensures";
val Join_ensures = thm "Join_ensures";
val stable_Join_constrains = thm "stable_Join_constrains";
val stable_Join_Always1 = thm "stable_Join_Always1";
val stable_Join_Always2 = thm "stable_Join_Always2";
val stable_Join_ensures1 = thm "stable_Join_ensures1";
val stable_Join_ensures2 = thm "stable_Join_ensures2";
val ok_SKIP1 = thm "ok_SKIP1";
val ok_SKIP2 = thm "ok_SKIP2";
val ok_Join_commute = thm "ok_Join_commute";
val ok_commute = thm "ok_commute";
val ok_sym = thm "ok_sym";
val ok_iff_OK = thm "ok_iff_OK";
val ok_Join_iff1 = thm "ok_Join_iff1";
val ok_Join_iff2 = thm "ok_Join_iff2";
val ok_Join_commute_I = thm "ok_Join_commute_I";
val ok_JN_iff1 = thm "ok_JN_iff1";
val ok_JN_iff2 = thm "ok_JN_iff2";
val OK_iff_ok = thm "OK_iff_ok";
val OK_imp_ok = thm "OK_imp_ok";
val Allowed_SKIP = thm "Allowed_SKIP";
val Allowed_Join = thm "Allowed_Join";
val Allowed_JN = thm "Allowed_JN";
val ok_iff_Allowed = thm "ok_iff_Allowed";
val OK_iff_Allowed = thm "OK_iff_Allowed";
val safety_prop_Acts_iff = thm "safety_prop_Acts_iff";
val safety_prop_AllowedActs_iff_Allowed = thm "safety_prop_AllowedActs_iff_Allowed";
val Allowed_eq = thm "Allowed_eq";
val def_prg_Allowed = thm "def_prg_Allowed";
val safety_prop_constrains = thm "safety_prop_constrains";
val safety_prop_stable = thm "safety_prop_stable";
val safety_prop_Int = thm "safety_prop_Int";
val safety_prop_INTER1 = thm "safety_prop_INTER1";
val safety_prop_INTER = thm "safety_prop_INTER";
val def_UNION_ok_iff = thm "def_UNION_ok_iff";

(*Comp*)
val preserves_def = thm "preserves_def";
val funPair_def = thm "funPair_def";
val componentI = thm "componentI";
val component_eq_subset = thm "component_eq_subset";
val component_SKIP = thm "component_SKIP";
val component_refl = thm "component_refl";
val SKIP_minimal = thm "SKIP_minimal";
val component_Join1 = thm "component_Join1";
val component_Join2 = thm "component_Join2";
val Join_absorb1 = thm "Join_absorb1";
val Join_absorb2 = thm "Join_absorb2";
val JN_component_iff = thm "JN_component_iff";
val component_JN = thm "component_JN";
val component_trans = thm "component_trans";
val component_antisym = thm "component_antisym";
val Join_component_iff = thm "Join_component_iff";
val component_constrains = thm "component_constrains";
val program_less_le = thm "program_less_le";
val preservesI = thm "preservesI";
val preserves_imp_eq = thm "preserves_imp_eq";
val Join_preserves = thm "Join_preserves";
val JN_preserves = thm "JN_preserves";
val SKIP_preserves = thm "SKIP_preserves";
val funPair_apply = thm "funPair_apply";
val preserves_funPair = thm "preserves_funPair";
val funPair_o_distrib = thm "funPair_o_distrib";
val fst_o_funPair = thm "fst_o_funPair";
val snd_o_funPair = thm "snd_o_funPair";
val subset_preserves_o = thm "subset_preserves_o";
val preserves_subset_stable = thm "preserves_subset_stable";
val preserves_subset_increasing = thm "preserves_subset_increasing";
val preserves_id_subset_stable = thm "preserves_id_subset_stable";
val safety_prop_preserves = thm "safety_prop_preserves";
val stable_localTo_stable2 = thm "stable_localTo_stable2";
val Increasing_preserves_Stable = thm "Increasing_preserves_Stable";
val component_of_imp_component = thm "component_of_imp_component";
val component_of_refl = thm "component_of_refl";
val component_of_SKIP = thm "component_of_SKIP";
val component_of_trans = thm "component_of_trans";
val strict_component_of_eq = thm "strict_component_of_eq";
val localize_Init_eq = thm "localize_Init_eq";
val localize_Acts_eq = thm "localize_Acts_eq";
val localize_AllowedActs_eq = thm "localize_AllowedActs_eq";

(*Guar*)
val guar_def = thm "guar_def";
val OK_insert_iff = thm "OK_insert_iff";
val ex1 = thm "ex1";
val ex2 = thm "ex2";
val ex_prop_finite = thm "ex_prop_finite";
val ex_prop_equiv = thm "ex_prop_equiv";
val uv1 = thm "uv1";
val uv2 = thm "uv2";
val uv_prop_finite = thm "uv_prop_finite";
val guaranteesI = thm "guaranteesI";
val guaranteesD = thm "guaranteesD";
val component_guaranteesD = thm "component_guaranteesD";
val guarantees_weaken = thm "guarantees_weaken";
val subset_imp_guarantees_UNIV = thm "subset_imp_guarantees_UNIV";
val subset_imp_guarantees = thm "subset_imp_guarantees";
val ex_prop_imp = thm "ex_prop_imp";
val guarantees_imp = thm "guarantees_imp";
val ex_prop_equiv2 = thm "ex_prop_equiv2";
val guarantees_UN_left = thm "guarantees_UN_left";
val guarantees_Un_left = thm "guarantees_Un_left";
val guarantees_INT_right = thm "guarantees_INT_right";
val guarantees_Int_right = thm "guarantees_Int_right";
val guarantees_Int_right_I = thm "guarantees_Int_right_I";
val guarantees_INT_right_iff = thm "guarantees_INT_right_iff";
val shunting = thm "shunting";
val contrapositive = thm "contrapositive";
val combining1 = thm "combining1";
val combining2 = thm "combining2";
val all_guarantees = thm "all_guarantees";
val ex_guarantees = thm "ex_guarantees";
val guarantees_Join_Int = thm "guarantees_Join_Int";
val guarantees_Join_Un = thm "guarantees_Join_Un";
val guarantees_JN_INT = thm "guarantees_JN_INT";
val guarantees_JN_UN = thm "guarantees_JN_UN";
val guarantees_Join_I1 = thm "guarantees_Join_I1";
val guarantees_Join_I2 = thm "guarantees_Join_I2";
val guarantees_JN_I = thm "guarantees_JN_I";
val Join_welldef_D1 = thm "Join_welldef_D1";
val Join_welldef_D2 = thm "Join_welldef_D2";
val refines_refl = thm "refines_refl";
val ex_refinement_thm = thm "ex_refinement_thm";
val uv_refinement_thm = thm "uv_refinement_thm";
val guarantees_equiv = thm "guarantees_equiv";
val wg_weakest = thm "wg_weakest";
val wg_guarantees = thm "wg_guarantees";
val wg_equiv = thm "wg_equiv";
val component_of_wg = thm "component_of_wg";
val wg_finite = thm "wg_finite";
val wg_ex_prop = thm "wg_ex_prop";
val wx_subset = thm "wx_subset";
val wx_ex_prop = thm "wx_ex_prop";
val wx_weakest = thm "wx_weakest";
val wx'_ex_prop = thm "wx'_ex_prop";
val wx_equiv = thm "wx_equiv";
val guarantees_wx_eq = thm "guarantees_wx_eq";
val stable_guarantees_Always = thm "stable_guarantees_Always";
val leadsTo_Basis = thm "leadsTo_Basis";
val constrains_guarantees_leadsTo = thm "constrains_guarantees_leadsTo";

(*Extend*)
val Restrict_iff = thm "Restrict_iff";
val Restrict_UNIV = thm "Restrict_UNIV";
val Restrict_empty = thm "Restrict_empty";
val Restrict_Int = thm "Restrict_Int";
val Restrict_triv = thm "Restrict_triv";
val Restrict_subset = thm "Restrict_subset";
val Restrict_eq_mono = thm "Restrict_eq_mono";
val Restrict_imageI = thm "Restrict_imageI";
val Domain_Restrict = thm "Domain_Restrict";
val Image_Restrict = thm "Image_Restrict";
val insert_Id_image_Acts = thm "insert_Id_image_Acts";
val good_mapI = thm "good_mapI";
val good_map_is_surj = thm "good_map_is_surj";
val fst_inv_equalityI = thm "fst_inv_equalityI";
val project_set_iff = thm "project_set_iff";
val extend_set_mono = thm "extend_set_mono";
val extend_set_empty = thm "extend_set_empty";
val project_set_Int_subset = thm "project_set_Int_subset";
val Init_extend = thm "Init_extend";
val Init_project = thm "Init_project";
val Acts_project = thm "Acts_project";
val project_set_UNIV = thm "project_set_UNIV";
val project_set_Union = thm "project_set_Union";
val project_act_mono = thm "project_act_mono";
val project_constrains_project_set = thm "project_constrains_project_set";
val project_stable_project_set = thm "project_stable_project_set";


(*Rename*)
val good_map_bij = thm "good_map_bij";
val fst_o_inv_eq_inv = thm "fst_o_inv_eq_inv";
val mem_rename_set_iff = thm "mem_rename_set_iff";
val extend_set_eq_image = thm "extend_set_eq_image";
val Init_rename = thm "Init_rename";
val extend_set_inv = thm "extend_set_inv";
val bij_extend_act_eq_project_act = thm "bij_extend_act_eq_project_act";
val bij_extend_act = thm "bij_extend_act";
val bij_project_act = thm "bij_project_act";
val bij_inv_project_act_eq = thm "bij_inv_project_act_eq";
val Acts_project = thm "Acts_project";
val extend_inv = thm "extend_inv";
val rename_inv_rename = thm "rename_inv_rename";
val rename_rename_inv = thm "rename_rename_inv";
val rename_inv_eq = thm "rename_inv_eq";
val bij_extend = thm "bij_extend";
val bij_project = thm "bij_project";
val inv_project_eq = thm "inv_project_eq";
val Allowed_rename = thm "Allowed_rename";
val bij_rename = thm "bij_rename";
val surj_rename = thm "surj_rename";
val inj_rename_imp_inj = thm "inj_rename_imp_inj";
val surj_rename_imp_surj = thm "surj_rename_imp_surj";
val bij_rename_imp_bij = thm "bij_rename_imp_bij";
val bij_rename_iff = thm "bij_rename_iff";
val rename_SKIP = thm "rename_SKIP";
val rename_Join = thm "rename_Join";
val rename_JN = thm "rename_JN";
val rename_constrains = thm "rename_constrains";
val rename_stable = thm "rename_stable";
val rename_invariant = thm "rename_invariant";
val rename_increasing = thm "rename_increasing";
val reachable_rename_eq = thm "reachable_rename_eq";
val rename_Constrains = thm "rename_Constrains";
val rename_Stable = thm "rename_Stable";
val rename_Always = thm "rename_Always";
val rename_Increasing = thm "rename_Increasing";
val rename_transient = thm "rename_transient";
val rename_ensures = thm "rename_ensures";
val rename_leadsTo = thm "rename_leadsTo";
val rename_LeadsTo = thm "rename_LeadsTo";
val rename_rename_guarantees_eq = thm "rename_rename_guarantees_eq";
val rename_guarantees_eq_rename_inv = thm "rename_guarantees_eq_rename_inv";
val rename_preserves = thm "rename_preserves";
val ok_rename_iff = thm "ok_rename_iff";
val OK_rename_iff = thm "OK_rename_iff";
val bij_eq_rename = thm "bij_eq_rename";
val rename_image_constrains = thm "rename_image_constrains";
val rename_image_stable = thm "rename_image_stable";
val rename_image_increasing = thm "rename_image_increasing";
val rename_image_invariant = thm "rename_image_invariant";
val rename_image_Constrains = thm "rename_image_Constrains";
val rename_image_preserves = thm "rename_image_preserves";
val rename_image_Stable = thm "rename_image_Stable";
val rename_image_Increasing = thm "rename_image_Increasing";
val rename_image_Always = thm "rename_image_Always";
val rename_image_leadsTo = thm "rename_image_leadsTo";
val rename_image_LeadsTo = thm "rename_image_LeadsTo";



(*Lift_prog*)
val sub_def = thm "sub_def";
val lift_map_def = thm "lift_map_def";
val drop_map_def = thm "drop_map_def";
val insert_map_inverse = thm "insert_map_inverse";
val insert_map_delete_map_eq = thm "insert_map_delete_map_eq";
val insert_map_inject1 = thm "insert_map_inject1";
val insert_map_inject2 = thm "insert_map_inject2";
val insert_map_inject = thm "insert_map_inject";
val insert_map_inject = thm "insert_map_inject";
val lift_map_eq_iff = thm "lift_map_eq_iff";
val drop_map_lift_map_eq = thm "drop_map_lift_map_eq";
val inj_lift_map = thm "inj_lift_map";
val lift_map_drop_map_eq = thm "lift_map_drop_map_eq";
val drop_map_inject = thm "drop_map_inject";
val surj_lift_map = thm "surj_lift_map";
val bij_lift_map = thm "bij_lift_map";
val inv_lift_map_eq = thm "inv_lift_map_eq";
val inv_drop_map_eq = thm "inv_drop_map_eq";
val bij_drop_map = thm "bij_drop_map";
val sub_apply = thm "sub_apply";
val lift_set_empty = thm "lift_set_empty";
val lift_set_iff = thm "lift_set_iff";
val lift_set_iff2 = thm "lift_set_iff2";
val lift_set_mono = thm "lift_set_mono";
val lift_set_Un_distrib = thm "lift_set_Un_distrib";
val lift_set_Diff_distrib = thm "lift_set_Diff_distrib";
val bij_lift = thm "bij_lift";
val lift_SKIP = thm "lift_SKIP";
val lift_Join = thm "lift_Join";
val lift_JN = thm "lift_JN";
val lift_constrains = thm "lift_constrains";
val lift_stable = thm "lift_stable";
val lift_invariant = thm "lift_invariant";
val lift_Constrains = thm "lift_Constrains";
val lift_Stable = thm "lift_Stable";
val lift_Always = thm "lift_Always";
val lift_transient = thm "lift_transient";
val lift_ensures = thm "lift_ensures";
val lift_leadsTo = thm "lift_leadsTo";
val lift_LeadsTo = thm "lift_LeadsTo";
val lift_lift_guarantees_eq = thm "lift_lift_guarantees_eq";
val lift_guarantees_eq_lift_inv = thm "lift_guarantees_eq_lift_inv";
val lift_preserves_snd_I = thm "lift_preserves_snd_I";
val delete_map_eqE = thm "delete_map_eqE";
val delete_map_eqE = thm "delete_map_eqE";
val delete_map_neq_apply = thm "delete_map_neq_apply";
val vimage_o_fst_eq = thm "vimage_o_fst_eq";
val vimage_sub_eq_lift_set = thm "vimage_sub_eq_lift_set";
val mem_lift_act_iff = thm "mem_lift_act_iff";
val preserves_snd_lift_stable = thm "preserves_snd_lift_stable";
val constrains_imp_lift_constrains = thm "constrains_imp_lift_constrains";
val insert_map_upd_same = thm "insert_map_upd_same";
val insert_map_upd = thm "insert_map_upd";
val insert_map_eq_diff = thm "insert_map_eq_diff";
val lift_map_eq_diff = thm "lift_map_eq_diff";
val lift_transient_eq_disj = thm "lift_transient_eq_disj";
val lift_map_image_Times = thm "lift_map_image_Times";
val lift_preserves_eq = thm "lift_preserves_eq";
val lift_preserves_sub = thm "lift_preserves_sub";
val o_equiv_assoc = thm "o_equiv_assoc";
val o_equiv_apply = thm "o_equiv_apply";
val fst_o_lift_map = thm "fst_o_lift_map";
val snd_o_lift_map = thm "snd_o_lift_map";
val extend_act_extend_act = thm "extend_act_extend_act";
val project_act_project_act = thm "project_act_project_act";
val project_act_extend_act = thm "project_act_extend_act";
val act_in_UNION_preserves_fst = thm "act_in_UNION_preserves_fst";
val UNION_OK_lift_I = thm "UNION_OK_lift_I";
val OK_lift_I = thm "OK_lift_I";
val Allowed_lift = thm "Allowed_lift";
val lift_image_preserves = thm "lift_image_preserves";


(*PPROD*)
val Init_PLam = thm "Init_PLam";
val PLam_empty = thm "PLam_empty";
val PLam_SKIP = thm "PLam_SKIP";
val PLam_insert = thm "PLam_insert";
val PLam_component_iff = thm "PLam_component_iff";
val component_PLam = thm "component_PLam";
val PLam_constrains = thm "PLam_constrains";
val PLam_stable = thm "PLam_stable";
val PLam_transient = thm "PLam_transient";
val PLam_ensures = thm "PLam_ensures";
val PLam_leadsTo_Basis = thm "PLam_leadsTo_Basis";
val invariant_imp_PLam_invariant = thm "invariant_imp_PLam_invariant";
val PLam_preserves_fst = thm "PLam_preserves_fst";
val PLam_preserves_snd = thm "PLam_preserves_snd";
val guarantees_PLam_I = thm "guarantees_PLam_I";
val Allowed_PLam = thm "Allowed_PLam";
val PLam_preserves = thm "PLam_preserves";


(*proves "co" properties when the program is specified*)
fun gen_constrains_tac(cs,ss) i = 
   SELECT_GOAL
      (EVERY [REPEAT (Always_Int_tac 1),
	      REPEAT (etac Always_ConstrainsI 1
		      ORELSE
		      resolve_tac [StableI, stableI,
				   constrains_imp_Constrains] 1),
	      rtac constrainsI 1,
	      full_simp_tac ss 1,
	      REPEAT (FIRSTGOAL (etac disjE)),
	      ALLGOALS (clarify_tac cs),
	      ALLGOALS (asm_lr_simp_tac ss)]) i;

(*proves "ensures/leadsTo" properties when the program is specified*)
fun gen_ensures_tac(cs,ss) sact = 
    SELECT_GOAL
      (EVERY [REPEAT (Always_Int_tac 1),
	      etac Always_LeadsTo_Basis 1 
	          ORELSE   (*subgoal may involve LeadsTo, leadsTo or ensures*)
		  REPEAT (ares_tac [LeadsTo_Basis, leadsTo_Basis,
				    EnsuresI, ensuresI] 1),
	      (*now there are two subgoals: co & transient*)
	      simp_tac ss 2,
	      res_inst_tac [("act", sact)] transientI 2,
                 (*simplify the command's domain*)
	      simp_tac (ss addsimps [Domain_def]) 3,
	      gen_constrains_tac (cs,ss) 1,
	      ALLGOALS (clarify_tac cs),
	      ALLGOALS (asm_lr_simp_tac ss)]);


(*Composition equivalences, from Lift_prog*)

fun make_o_equivs th =
    [th,
     th RS o_equiv_assoc |> simplify (HOL_ss addsimps [o_assoc]),
     th RS o_equiv_apply |> simplify (HOL_ss addsimps [o_def, sub_def])];

Addsimps (make_o_equivs fst_o_funPair @ make_o_equivs snd_o_funPair);

Addsimps (make_o_equivs fst_o_lift_map @ make_o_equivs snd_o_lift_map);
