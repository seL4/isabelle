(*  Title:      HOL/UNITY/Lift
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Lift-Control Example
*)

val always_defs = [above_def, below_def, queueing_def, 
		   goingup_def, goingdown_def, ready_def];

val cmd_defs = [Lprg_def, 
		request_act_def, open_act_def, close_act_def,
		req_up_act_def, req_down_act_def, move_up_def, move_down_def];

AddIffs [min_le_max];

Goalw [Lprg_def] "id : Acts Lprg";
by (Simp_tac 1);
qed "id_in_Acts";
AddIffs [id_in_Acts];


(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper "split_all_tac";

(*Simplification for records*)
Addsimps (thms"state.update_defs");

Addsimps [Suc_le_eq];

Addsimps [bounded_def, open_stop_def, open_move_def, stop_floor_def,
	  moving_up_def, moving_down_def];


Goal "0 < n ==> (m <= n-1) = (m<n)";
by (exhaust_tac "n" 1);
by Auto_tac;
by (REPEAT_FIRST trans_tac);
qed "le_pred_eq";

Goal "m < n ==> m <= n-1";
by (asm_simp_tac (simpset() addsimps [gr_implies_gr0 RS le_pred_eq]) 1);
qed "less_imp_le_pred";


Goalw [Lprg_def] "invariant Lprg open_stop";
by (rtac invariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
qed "open_stop";

Goalw [Lprg_def] "invariant Lprg stop_floor";
by (rtac invariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
qed "stop_floor";

(*Should not have to prove open_stop concurrently!!*)
Goalw [Lprg_def] "invariant Lprg (open_stop Int open_move)";
by (rtac invariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
qed "open_move";

Goalw [Lprg_def] "invariant Lprg moving_up";
by (rtac invariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
by (blast_tac (claset() addDs [le_imp_less_or_eq]) 1);
qed "moving_up";

Goalw [Lprg_def] "invariant Lprg moving_down";
by (rtac invariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
by (dres_inst_tac [("m","f")] le_imp_less_or_eq 3);
by (auto_tac (claset(),
	      simpset() addsimps [gr_implies_gr0 RS le_pred_eq]));
qed "moving_down";


xxxxxxxxxxxxxxxx;

Goalw [Lprg_def] "invariant Lprg bounded";
by (rtac invariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [gr_implies_gr0 RS le_pred_eq])));
by (REPEAT_FIRST trans_tac);
by (blast_tac (claset() addIs [diff_le_self, le_trans]) 1);
by (blast_tac (claset() addIs [diff_le_self, le_trans]) 1);
by (blast_tac (claset() addIs [diff_le_self, le_trans]) 3);
qed "bounded";

Goalw [Lprg_def] "invariant Lprg invariantV";
by (rtac invariantI 1);
by (constrains_tac cmd_defs 2);
by Auto_tac;
qed "invariantV";

val invariantUV = invariant_Int_rule [invariantU, invariantV];


(*The safety property: mutual exclusion*)
Goal "(reachable Lprg) Int {s. MM s = 3 & NN s = 3} = {}";
by (cut_facts_tac [invariantUV RS invariant_includes_reachable] 1);
by Auto_tac;
qed "mutual_exclusion";


(*** Progress for U ***)

Goalw [unless_def] "unless (Acts Lprg) {s. MM s=2} {s. MM s=3}";
by (constrains_tac cmd_defs 1);
qed "U_F0";

Goal "LeadsTo Lprg {s. MM s=1} {s. PP s = VV s & MM s = 2}";
by (ensures_tac cmd_defs "cmd1U" 1);
qed "U_F1";

Goal "LeadsTo Lprg {s. ~ PP s & MM s = 2} {s. MM s = 3}";
by (cut_facts_tac [invariantUV] 1);
bw Lprg_def;
by (ensures_tac cmd_defs "cmd2U" 1);
qed "U_F2";

Goal "LeadsTo Lprg {s. MM s = 3} {s. PP s}";
by (rtac leadsTo_imp_LeadsTo 1); 
by (res_inst_tac [("B", "{s. MM s = 4}")] leadsTo_Trans 1);
by (ensures_tac cmd_defs "cmd4U" 2);
by (ensures_tac cmd_defs "cmd3U" 1);
qed "U_F3";

Goal "LeadsTo Lprg {s. MM s = 2} {s. PP s}";
by (rtac ([LeadsTo_weaken_L, subset_refl RS subset_imp_LeadsTo] 
	  MRS LeadsTo_Diff) 1);
by (rtac ([U_F2, U_F3] MRS LeadsTo_Trans) 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
val U_lemma2 = result();

