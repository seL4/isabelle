(* 
    File:        RPC.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: RPC specification (theorems and proofs)
*)

val RPC_action_defs = [RPCInit_def, RPCFwd_def, RPCReject_def, RPCFail_def, 
                       RPCReply_def, RPCNext_def];

val RPC_temp_defs = [RPCIPSpec_def, RPCISpec_def];

val mem_css = (claset(), simpset());

(* The RPC component engages in an action for process p only if there is an outstanding,
   unanswered call for that process.
*)

Goal "|- ~$(Calling send p) --> ~RPCNext send rcv rst p";
by (auto_tac (mem_css addsimps2 (Return_def::RPC_action_defs)));
qed "RPCidle";

Goal "|- $(Calling rcv p) & $(rst!p) = #rpcB --> ~RPCNext send rcv rst p";
by (auto_tac (mem_css addsimps2 RPC_action_defs));
qed "RPCbusy";

(* RPC failure actions are visible. *)
Goal "|- RPCFail send rcv rst p --> \
\        <RPCNext send rcv rst p>_(rst!p, rtrner send!p, caller rcv!p)";
by (auto_tac (claset() addSDs [Return_changed],
	     simpset() addsimps [angle_def,RPCNext_def,RPCFail_def]));
qed "RPCFail_vis";

Goal "|- Enabled (RPCFail send rcv rst p) --> \
\        Enabled (<RPCNext send rcv rst p>_(rst!p, rtrner send!p, caller rcv!p))";
by (force_tac (mem_css addSEs2 [enabled_mono,RPCFail_vis]) 1);
qed "RPCFail_Next_enabled";

(* Enabledness of some actions *)
Goal "!!p. basevars (rtrner send!p, caller rcv!p, rst!p) ==> \
\     |- ~Calling rcv p & Calling send p --> Enabled (RPCFail send rcv rst p)";
by (action_simp_tac (simpset() addsimps [RPCFail_def,Return_def,caller_def,rtrner_def])
                    [exI] [base_enabled,Pair_inject] 1);
qed "RPCFail_enabled";

Goal "!!p. basevars (rtrner send!p, caller rcv!p, rst!p) ==> \
\     |- ~Calling rcv p & Calling send p & rst!p = #rpcB \
\        --> Enabled (RPCReply send rcv rst p)";
by (action_simp_tac (simpset() addsimps [RPCReply_def,Return_def,caller_def,rtrner_def])
                    [exI] [base_enabled,Pair_inject] 1);
qed "RPCReply_enabled";
