val aut_simps = [cockpit_def,cockpit_asig_def,cockpit_trans_def,
		cockpit_initial_def,cockpit_hide_def,
		Al_before_Ack_def,Al_before_Ack_asig_def,
		Al_before_Ack_initial_def,Al_before_Ack_trans_def,
		Info_while_Al_def,Info_while_Al_asig_def,
		Info_while_Al_initial_def,Info_while_Al_trans_def,
		Info_before_Al_def,Info_before_Al_asig_def,
		Info_before_Al_initial_def,Info_before_Al_trans_def];

(*

(* to prove, that info is always set at the recent alarm *)
goal thy "cockpit =<| Info_while_Al";
by (is_sim_tac thy aut_simps 1);
qed"cockpit_implements_Info_while_Al";

(* to prove that before any alarm arrives (and after each acknowledgement),
	 info remains at None *)
goal thy "cockpit =<| Info_before_Al";
by (is_sim_tac thy aut_simps 1);       
qed"cockpit_implements_Info_before_Al";

(* to prove that before any alarm vould be acknowledged, it must be arrived *)
goal thy "cockpit_hide =<| Al_before_Ack";
by (is_sim_tac thy aut_simps 1);       
by Auto_tac;
qed"cockpit_implements_Al_before_Ack";

*)	
