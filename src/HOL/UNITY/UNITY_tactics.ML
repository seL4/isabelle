(*  Title:      HOL/UNITY/UNITY_tactics.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge

Specialized UNITY tactics, and ML bindings of theorems
*)


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
