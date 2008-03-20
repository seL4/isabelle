(*
    File:        MemClerk.thy
    ID:          $Id$
    Author:      Stephan Merz
    Copyright:   1997 University of Munich
*)

header {* RPC-Memory example: specification of the memory clerk *}

theory MemClerk
imports Memory RPC MemClerkParameters
begin

types
  (* The clerk takes the same arguments as the memory and sends requests to the RPC *)
  mClkSndChType = "memChType"
  mClkRcvChType = "rpcSndChType"
  mClkStType    = "(PrIds => mClkState) stfun"

constdefs
  (* state predicates *)
  MClkInit      :: "mClkRcvChType => mClkStType => PrIds => stpred"
     "MClkInit rcv cst p == PRED (cst!p = #clkA  &  ~Calling rcv p)"

  (* actions *)
  MClkFwd       :: "mClkSndChType => mClkRcvChType => mClkStType => PrIds => action"
     "MClkFwd send rcv cst p == ACT
                           $Calling send p
                         & $(cst!p) = #clkA
                         & Call rcv p MClkRelayArg<arg<send!p>>
                         & (cst!p)$ = #clkB
                         & unchanged (rtrner send!p)"

  MClkRetry     :: "mClkSndChType => mClkRcvChType => mClkStType => PrIds => action"
     "MClkRetry send rcv cst p == ACT
                           $(cst!p) = #clkB
                         & res<$(rcv!p)> = #RPCFailure
                         & Call rcv p MClkRelayArg<arg<send!p>>
                         & unchanged (cst!p, rtrner send!p)"

  MClkReply     :: "mClkSndChType => mClkRcvChType => mClkStType => PrIds => action"
     "MClkReply send rcv cst p == ACT
                           ~$Calling rcv p
                         & $(cst!p) = #clkB
                         & Return send p MClkReplyVal<res<rcv!p>>
                         & (cst!p)$ = #clkA
                         & unchanged (caller rcv!p)"

  MClkNext      :: "mClkSndChType => mClkRcvChType => mClkStType => PrIds => action"
      "MClkNext send rcv cst p == ACT
                        (  MClkFwd send rcv cst p
                         | MClkRetry send rcv cst p
                         | MClkReply send rcv cst p)"


  (* temporal *)
  MClkIPSpec    :: "mClkSndChType => mClkRcvChType => mClkStType => PrIds => temporal"
      "MClkIPSpec send rcv cst p == TEMP
                           Init MClkInit rcv cst p
                         & [][ MClkNext send rcv cst p ]_(cst!p, rtrner send!p, caller rcv!p)
                         & WF(MClkFwd send rcv cst p)_(cst!p, rtrner send!p, caller rcv!p)
                         & SF(MClkReply send rcv cst p)_(cst!p, rtrner send!p, caller rcv!p)"

  MClkISpec     :: "mClkSndChType => mClkRcvChType => mClkStType => temporal"
      "MClkISpec send rcv cst == TEMP (ALL p. MClkIPSpec send rcv cst p)"

lemmas MC_action_defs =
  MClkInit_def MClkFwd_def MClkRetry_def MClkReply_def MClkNext_def

lemmas MC_temp_defs = MClkIPSpec_def MClkISpec_def

(* The Clerk engages in an action for process p only if there is an outstanding,
   unanswered call for that process.
*)
lemma MClkidle: "|- ~$Calling send p & $(cst!p) = #clkA --> ~MClkNext send rcv cst p"
  by (auto simp: Return_def MC_action_defs)

lemma MClkbusy: "|- $Calling rcv p --> ~MClkNext send rcv cst p"
  by (auto simp: Call_def MC_action_defs)


(* Enabledness of actions *)

lemma MClkFwd_enabled: "!!p. basevars (rtrner send!p, caller rcv!p, cst!p) ==>  
      |- Calling send p & ~Calling rcv p & cst!p = #clkA   
         --> Enabled (MClkFwd send rcv cst p)"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm MClkFwd_def},
    @{thm Call_def}, @{thm caller_def}, @{thm rtrner_def}]) [exI]
    [@{thm base_enabled}, @{thm Pair_inject}] 1 *})

lemma MClkFwd_ch_enabled: "|- Enabled (MClkFwd send rcv cst p)  -->   
         Enabled (<MClkFwd send rcv cst p>_(cst!p, rtrner send!p, caller rcv!p))"
  by (auto elim!: enabled_mono simp: angle_def MClkFwd_def)

lemma MClkReply_change: "|- MClkReply send rcv cst p -->  
         <MClkReply send rcv cst p>_(cst!p, rtrner send!p, caller rcv!p)"
  by (auto simp: angle_def MClkReply_def elim: Return_changed [temp_use])

lemma MClkReply_enabled: "!!p. basevars (rtrner send!p, caller rcv!p, cst!p) ==>  
      |- Calling send p & ~Calling rcv p & cst!p = #clkB   
         --> Enabled (<MClkReply send rcv cst p>_(cst!p, rtrner send!p, caller rcv!p))"
  apply (tactic {* action_simp_tac @{simpset}
    [@{thm MClkReply_change} RSN (2, @{thm enabled_mono})] [] 1 *})
  apply (tactic {* action_simp_tac (@{simpset} addsimps
    [@{thm MClkReply_def}, @{thm Return_def}, @{thm caller_def}, @{thm rtrner_def}])
    [exI] [@{thm base_enabled}, @{thm Pair_inject}] 1 *})
  done

lemma MClkReplyNotRetry: "|- MClkReply send rcv cst p --> ~MClkRetry send rcv cst p"
  by (auto simp: MClkReply_def MClkRetry_def)

end
