(* 
    File:        RPC.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: RPC specification (ML file)
*)

val RPC_action_defs = 
   [RPCInit_def RS inteq_reflection]
   @ [RPCFwd_def, RPCReject_def, RPCFail_def, RPCReply_def, RPCNext_def];

val RPC_temp_defs = [RPCIPSpec_def, RPCISpec_def];

(* The RPC component engages in an action for process p only if there is an outstanding,
   unanswered call for that process.
*)

qed_goal "RPCidle" RPC.thy
   ".~ $(Calling send p) .-> .~ RPCNext send rcv rst p"
   (fn _ => [ auto_tac (action_css addsimps2 (Return_def::RPC_action_defs)) ]);

qed_goal "RPCbusy" RPC.thy
   "$(Calling rcv p) .& ($(rst@p) .= #rpcB) .-> .~ RPCNext send rcv rst p"
   (fn _ => [ auto_tac (action_css addsimps2 (RP_simps @ RPC_action_defs)) ]);

(* unlifted versions as introduction rules *)

bind_thm("RPCidleI", action_mp RPCidle);
bind_thm("RPCbusyI", action_mp RPCbusy);

(* RPC failure actions are visible. *)
qed_goal "RPCFail_vis" RPC.thy
   "RPCFail send rcv rst p .-> <RPCNext send rcv rst p>_<rst@p, rtrner send @ p, caller rcv @ p>"
   (fn _ => [auto_tac (!claset addSEs [Return_changedE],
		       !simpset addsimps [angle_def,RPCNext_def,RPCFail_def])
	    ]);

qed_goal "RPCFail_Next_enabled" RPC.thy
   "Enabled (RPCFail send rcv rst p) s \
\   ==> Enabled (<RPCNext send rcv rst p>_<rst@p, rtrner send @ p, caller rcv @ p>) s"
   (fn [prem] => [REPEAT (resolve_tac [prem RS enabled_mono,RPCFail_vis] 1)]);

(* Enabledness of some actions *)

qed_goal "RPCFail_enabled" RPC.thy
   "!!p. base_var <rtrner send @ p, caller rcv @ p, rst@p> ==> \
\        .~ $(Calling rcv p) .& $(Calling send p) .-> $(Enabled (RPCFail send rcv rst p))"
   (fn _ => [action_simp_tac (!simpset addsimps [RPCFail_def,Return_def,caller_def,rtrner_def])
                             [] [base_enabled,Pair_inject] 1
	    ]);

qed_goal "RPCReply_enabled" RPC.thy
   "!!p. base_var <rtrner send @ p, caller rcv @ p, rst@p> ==> \
\        .~ $(Calling rcv p) .& $(Calling send p) .& $(rst@p) .= #rpcB \
\        .-> $(Enabled (RPCReply send rcv rst p))"
   (fn _ => [action_simp_tac (!simpset addsimps [RPCReply_def,Return_def,caller_def,rtrner_def])
                             [] [base_enabled,Pair_inject] 1]);

