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


val nat_exhaust_less_pred = 
    read_instantiate_sg (sign_of thy) [("P", "?m < ?y-1")] nat.exhaust;

val nat_exhaust_le_pred = 
    read_instantiate_sg (sign_of thy) [("P", "?m <= ?y-1")] nat.exhaust;

val nat_exhaust_pred_le = 
    read_instantiate_sg (sign_of thy) [("P", "?y-1 <= ?m")] nat.exhaust;

Goal "0 < n ==> (m <= n-1) = (m<n)";
by (exhaust_tac "n" 1);
by Auto_tac;
qed "le_pred_eq";

Goal "m < n ==> m <= n-1";
by (asm_simp_tac (simpset() addsimps [gr_implies_gr0 RS le_pred_eq]) 1);
qed "less_imp_le_pred";


Goalw [Lprg_def] "Invariant Lprg open_stop";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
qed "open_stop";

Goalw [Lprg_def] "Invariant Lprg stop_floor";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
qed "stop_floor";

(*This one needs open_stop, which was proved above*)
Goal "Invariant Lprg open_move";
by (rtac InvariantI 1);
br (open_stop RS Invariant_ConstrainsI RS StableI) 2;
bw Lprg_def;
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
qed "open_move";

Goalw [Lprg_def] "Invariant Lprg moving_up";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
by (blast_tac (claset() addDs [le_imp_less_or_eq]) 1);
qed "moving_up";

Goalw [Lprg_def] "Invariant Lprg moving_down";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
by (dres_inst_tac [("m","f")] le_imp_less_or_eq 3);
by (auto_tac (claset(),
	      simpset() addsimps [gr_implies_gr0 RS le_pred_eq]));
qed "moving_down";


Goal "Invariant Lprg bounded";
by (rtac InvariantI 1);
br (Invariant_Int_rule [moving_up, moving_down] RS Invariant_StableI) 2;
bw Lprg_def;
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
by (TRYALL (resolve_tac [nat_exhaust_le_pred, nat_exhaust_pred_le]));
by (auto_tac (claset(), simpset() addsimps [less_Suc_eq]));
by (auto_tac (claset(), simpset() addsimps [less_Suc_eq, le_eq_less_or_eq]));
qed "bounded";



(*** Progress ***)


val abbrev_defs = [moving_def, stopped_def, 
		   opened_def, closed_def, atFloor_def];

val defs = cmd_defs@always_defs@abbrev_defs;

(***

Goal "LeadsTo Lprg (stopped Int atFloor n) (opened Int atFloor n)";
by (ensures_tac defs "open_act" 1);
qed "U_F1";

Goal "LeadsTo Lprg {s. ~ PP s & MM s = 2} {s. MM s = 3}";
by (cut_facts_tac [invariantUV] 1);
by (rewtac Lprg_def);
by (ensures_tac defs "cmd2U" 1);
qed "U_F2";

Goal "LeadsTo Lprg {s. MM s = 3} {s. PP s}";
by (rtac leadsTo_imp_LeadsTo 1); 
by (res_inst_tac [("B", "{s. MM s = 4}")] leadsTo_Trans 1);
by (ensures_tac defs "cmd4U" 2);
by (ensures_tac defs "cmd3U" 1);
qed "U_F3";

Goal "LeadsTo Lprg {s. MM s = 2} {s. PP s}";
by (rtac ([LeadsTo_weaken_L, subset_refl RS subset_imp_LeadsTo] 
	  MRS LeadsTo_Diff) 1);
by (rtac ([U_F2, U_F3] MRS LeadsTo_Trans) 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
val U_lemma2 = result();

***)
