(* 
    File:        MemClerk.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: Memory clerk specification (theorems and proofs)
*)

val MC_action_defs = 
   [MClkInit_def, MClkFwd_def, MClkRetry_def, MClkReply_def, MClkNext_def];

val MC_temp_defs = [MClkIPSpec_def, MClkISpec_def];

val mem_css = (claset(), simpset());

(* The Clerk engages in an action for process p only if there is an outstanding,
   unanswered call for that process.
*)
Goal "|- ~$Calling send p & $(cst!p) = #clkA --> ~MClkNext send rcv cst p";
by (auto_tac (mem_css addsimps2 (Return_def::MC_action_defs)));
qed "MClkidle";

Goal "|- $Calling rcv p --> ~MClkNext send rcv cst p";
by (auto_tac (mem_css addsimps2 (Call_def::MC_action_defs)));
qed "MClkbusy";

(* Enabledness of actions *)

Goal "!!p. basevars (rtrner send!p, caller rcv!p, cst!p) ==> \
\     |- Calling send p & ~Calling rcv p & cst!p = #clkA  \
\        --> Enabled (MClkFwd send rcv cst p)";
by (action_simp_tac (simpset() addsimps [MClkFwd_def,Call_def,caller_def,rtrner_def])
                    [exI] [base_enabled,Pair_inject] 1);
qed "MClkFwd_enabled";

Goal "|- Enabled (MClkFwd send rcv cst p)  -->  \
\        Enabled (<MClkFwd send rcv cst p>_(cst!p, rtrner send!p, caller rcv!p))";
by (auto_tac (mem_css addSEs2 [enabled_mono] addsimps2 [angle_def,MClkFwd_def]));
qed "MClkFwd_ch_enabled";

Goal "|- MClkReply send rcv cst p --> \
\        <MClkReply send rcv cst p>_(cst!p, rtrner send!p, caller rcv!p)";
by (auto_tac (mem_css addsimps2 [angle_def,MClkReply_def]
	              addEs2 [Return_changed]));
qed "MClkReply_change";

Goal "!!p. basevars (rtrner send!p, caller rcv!p, cst!p) ==> \
\     |- Calling send p & ~Calling rcv p & cst!p = #clkB  \
\        --> Enabled (<MClkReply send rcv cst p>_(cst!p, rtrner send!p, caller rcv!p))";
by (action_simp_tac (simpset()) [MClkReply_change RSN (2,enabled_mono)] [] 1);
by (action_simp_tac (simpset() addsimps [MClkReply_def,Return_def,caller_def,rtrner_def])
                    [exI] [base_enabled,Pair_inject] 1);
qed "MClkReply_enabled";

Goal "|- MClkReply send rcv cst p --> ~MClkRetry send rcv cst p";
by (auto_tac (mem_css addsimps2 [MClkReply_def,MClkRetry_def]));
qed "MClkReplyNotRetry";
