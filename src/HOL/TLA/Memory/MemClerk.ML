(* 
    File:        MemClerk.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: Memory clerk specification (ML file)
*)

val MC_action_defs = 
   [MClkInit_def RS inteq_reflection]
   @ [MClkFwd_def, MClkRetry_def, MClkReply_def, MClkNext_def];

val MC_temp_defs = [MClkIPSpec_def, MClkISpec_def];

(* The Clerk engages in an action for process p only if there is an outstanding,
   unanswered call for that process.
*)

qed_goal "MClkidle" MemClerk.thy
   ".~ $(Calling send p) .& ($(cst@p) .= #clkA) .-> .~ MClkNext send rcv cst p"
   (fn _ => [ auto_tac (claset(),
                        simpset() addsimps (MC_action_defs @ [Return_def]))
            ]);

qed_goal "MClkbusy" MemClerk.thy
   "$(Calling rcv p) .-> .~ MClkNext send rcv cst p"
   (fn _ => [ auto_tac (claset(),
                        simpset() addsimps (MC_action_defs @ [Call_def]))
            ]);

(* unlifted versions as introduction rules *)

bind_thm("MClkidleI", action_mp MClkidle);
bind_thm("MClkbusyI", action_mp MClkbusy);

(* Enabledness of actions *)

qed_goal "MClkFwd_enabled" MemClerk.thy
   "!!p. base_var <rtrner send @ p, caller rcv @ p, cst@p> ==> \
\        $(Calling send p) .& .~ $(Calling rcv p) .& ($(cst@p) .= #clkA)  \
\        .-> $(Enabled (MClkFwd send rcv cst p))"
   (fn _ => [action_simp_tac (simpset() addsimps [MClkFwd_def,Call_def,caller_def,rtrner_def])
                             [] [base_enabled,Pair_inject] 1]);

qed_goal "MClkFwd_ch_enabled" MemClerk.thy
   "Enabled (MClkFwd send rcv cst p) s  \
\   ==> Enabled (<MClkFwd send rcv cst p>_<cst@p, rtrner send @ p, caller rcv @ p>) s"
   (fn [prem] => [auto_tac (claset() addSIs [prem RS enabled_mono],
			    simpset() addsimps [angle_def,MClkFwd_def])
		 ]);

qed_goal "MClkReply_change" MemClerk.thy
   "MClkReply send rcv cst p .-> <MClkReply send rcv cst p>_<cst@p, rtrner send @ p, caller rcv @ p>"
   (fn _ => [auto_tac (action_css addsimps2 [angle_def,MClkReply_def]
			          addEs2 [Return_changedE])
            ]);

qed_goal "MClkReply_enabled" MemClerk.thy
   "!!p. base_var <rtrner send @ p, caller rcv @ p, cst@p> ==> \
\        $(Calling send p) .& .~ $(Calling rcv p) .& ($(cst@p) .= #clkB)  \
\        .-> $(Enabled (<MClkReply send rcv cst p>_<cst@p, rtrner send @ p, caller rcv @ p>))"
   (fn _ => [action_simp_tac (simpset()) [MClkReply_change RSN (2,enabled_mono)] [] 1,
	     action_simp_tac (simpset() addsimps [MClkReply_def,Return_def,caller_def,rtrner_def])
                             [] [base_enabled,Pair_inject] 1
	    ]);

qed_goal "MClkReplyNotRetry" MemClerk.thy
   "MClkReply send rcv cst p .-> .~(MClkRetry send rcv cst p)"
   (fn _ => [ auto_tac (claset(),
			simpset() addsimps [MClkReply_def,MClkRetry_def]) 
	    ]);
