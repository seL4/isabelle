(*
    File:        RPC.thy
    ID:          $Id$
    Author:      Stephan Merz
    Copyright:   1997 University of Munich
*)

header {* RPC-Memory example: RPC specification *}

theory RPC
imports RPCParameters ProcedureInterface Memory
begin

types
  rpcSndChType  = "(rpcOp,Vals) channel"
  rpcRcvChType  = "memChType"
  rpcStType     = "(PrIds => rpcState) stfun"

consts
  (* state predicates *)
  RPCInit      :: "rpcRcvChType => rpcStType => PrIds => stpred"

  (* actions *)
  RPCFwd     :: "rpcSndChType => rpcRcvChType => rpcStType => PrIds => action"
  RPCReject  :: "rpcSndChType => rpcRcvChType => rpcStType => PrIds => action"
  RPCFail    :: "rpcSndChType => rpcRcvChType => rpcStType => PrIds => action"
  RPCReply   :: "rpcSndChType => rpcRcvChType => rpcStType => PrIds => action"
  RPCNext    :: "rpcSndChType => rpcRcvChType => rpcStType => PrIds => action"

  (* temporal *)
  RPCIPSpec   :: "rpcSndChType => rpcRcvChType => rpcStType => PrIds => temporal"
  RPCISpec   :: "rpcSndChType => rpcRcvChType => rpcStType => temporal"

defs
  RPCInit_def:       "RPCInit rcv rst p == PRED ((rst!p = #rpcA) & ~Calling rcv p)"

  RPCFwd_def:        "RPCFwd send rcv rst p == ACT
                         $(Calling send p)
                         & $(rst!p) = # rpcA
                         & IsLegalRcvArg<arg<$(send!p)>>
                         & Call rcv p RPCRelayArg<arg<send!p>>
                         & (rst!p)$ = # rpcB
                         & unchanged (rtrner send!p)"

  RPCReject_def:     "RPCReject send rcv rst p == ACT
                           $(rst!p) = # rpcA
                         & ~IsLegalRcvArg<arg<$(send!p)>>
                         & Return send p #BadCall
                         & unchanged ((rst!p), (caller rcv!p))"

  RPCFail_def:       "RPCFail send rcv rst p == ACT
                           ~$(Calling rcv p)
                         & Return send p #RPCFailure
                         & (rst!p)$ = #rpcA
                         & unchanged (caller rcv!p)"

  RPCReply_def:      "RPCReply send rcv rst p == ACT
                           ~$(Calling rcv p)
                         & $(rst!p) = #rpcB
                         & Return send p res<rcv!p>
                         & (rst!p)$ = #rpcA
                         & unchanged (caller rcv!p)"

  RPCNext_def:       "RPCNext send rcv rst p == ACT
                        (  RPCFwd send rcv rst p
                         | RPCReject send rcv rst p
                         | RPCFail send rcv rst p
                         | RPCReply send rcv rst p)"

  RPCIPSpec_def:     "RPCIPSpec send rcv rst p == TEMP
                           Init RPCInit rcv rst p
                         & [][ RPCNext send rcv rst p ]_(rst!p, rtrner send!p, caller rcv!p)
                         & WF(RPCNext send rcv rst p)_(rst!p, rtrner send!p, caller rcv!p)"

  RPCISpec_def:      "RPCISpec send rcv rst == TEMP (ALL p. RPCIPSpec send rcv rst p)"


lemmas RPC_action_defs =
  RPCInit_def RPCFwd_def RPCReject_def RPCFail_def RPCReply_def RPCNext_def

lemmas RPC_temp_defs = RPCIPSpec_def RPCISpec_def


(* The RPC component engages in an action for process p only if there is an outstanding,
   unanswered call for that process.
*)

lemma RPCidle: "|- ~$(Calling send p) --> ~RPCNext send rcv rst p"
  by (auto simp: Return_def RPC_action_defs)

lemma RPCbusy: "|- $(Calling rcv p) & $(rst!p) = #rpcB --> ~RPCNext send rcv rst p"
  by (auto simp: RPC_action_defs)

(* RPC failure actions are visible. *)
lemma RPCFail_vis: "|- RPCFail send rcv rst p -->  
    <RPCNext send rcv rst p>_(rst!p, rtrner send!p, caller rcv!p)"
  by (auto dest!: Return_changed [temp_use] simp: angle_def RPCNext_def RPCFail_def)

lemma RPCFail_Next_enabled: "|- Enabled (RPCFail send rcv rst p) -->  
    Enabled (<RPCNext send rcv rst p>_(rst!p, rtrner send!p, caller rcv!p))"
  by (force elim!: enabled_mono [temp_use] RPCFail_vis [temp_use])

(* Enabledness of some actions *)
lemma RPCFail_enabled: "!!p. basevars (rtrner send!p, caller rcv!p, rst!p) ==>  
    |- ~Calling rcv p & Calling send p --> Enabled (RPCFail send rcv rst p)"
  by (tactic {* action_simp_tac (@{simpset} addsimps [thm "RPCFail_def",
    thm "Return_def", thm "caller_def", thm "rtrner_def"]) [exI]
    [thm "base_enabled", thm "Pair_inject"] 1 *})

lemma RPCReply_enabled: "!!p. basevars (rtrner send!p, caller rcv!p, rst!p) ==>  
      |- ~Calling rcv p & Calling send p & rst!p = #rpcB  
         --> Enabled (RPCReply send rcv rst p)"
  by (tactic {* action_simp_tac (@{simpset} addsimps [thm "RPCReply_def",
    thm "Return_def", thm "caller_def", thm "rtrner_def"]) [exI]
    [thm "base_enabled", thm "Pair_inject"] 1 *})

end
