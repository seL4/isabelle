(*  Title:      HOL/TLA/Memory/MemClerk.thy
    Author:     Stephan Merz, University of Munich
*)

section {* RPC-Memory example: specification of the memory clerk *}

theory MemClerk
imports Memory RPC MemClerkParameters
begin

(* The clerk takes the same arguments as the memory and sends requests to the RPC *)
type_synonym mClkSndChType = "memChType"
type_synonym mClkRcvChType = "rpcSndChType"
type_synonym mClkStType = "(PrIds \<Rightarrow> mClkState) stfun"

definition
  (* state predicates *)
  MClkInit      :: "mClkRcvChType \<Rightarrow> mClkStType \<Rightarrow> PrIds \<Rightarrow> stpred"
  where "MClkInit rcv cst p = PRED (cst!p = #clkA  &  \<not>Calling rcv p)"

definition
  (* actions *)
  MClkFwd       :: "mClkSndChType \<Rightarrow> mClkRcvChType \<Rightarrow> mClkStType \<Rightarrow> PrIds \<Rightarrow> action"
  where "MClkFwd send rcv cst p = ACT
                           $Calling send p
                         & $(cst!p) = #clkA
                         & Call rcv p MClkRelayArg<arg<send!p>>
                         & (cst!p)$ = #clkB
                         & unchanged (rtrner send!p)"

definition
  MClkRetry     :: "mClkSndChType \<Rightarrow> mClkRcvChType \<Rightarrow> mClkStType \<Rightarrow> PrIds \<Rightarrow> action"
  where "MClkRetry send rcv cst p = ACT
                           $(cst!p) = #clkB
                         & res<$(rcv!p)> = #RPCFailure
                         & Call rcv p MClkRelayArg<arg<send!p>>
                         & unchanged (cst!p, rtrner send!p)"

definition
  MClkReply     :: "mClkSndChType \<Rightarrow> mClkRcvChType \<Rightarrow> mClkStType \<Rightarrow> PrIds \<Rightarrow> action"
  where "MClkReply send rcv cst p = ACT
                           \<not>$Calling rcv p
                         & $(cst!p) = #clkB
                         & Return send p MClkReplyVal<res<rcv!p>>
                         & (cst!p)$ = #clkA
                         & unchanged (caller rcv!p)"

definition
  MClkNext      :: "mClkSndChType \<Rightarrow> mClkRcvChType \<Rightarrow> mClkStType \<Rightarrow> PrIds \<Rightarrow> action"
  where "MClkNext send rcv cst p = ACT
                        (  MClkFwd send rcv cst p
                         | MClkRetry send rcv cst p
                         | MClkReply send rcv cst p)"

definition
  (* temporal *)
  MClkIPSpec    :: "mClkSndChType \<Rightarrow> mClkRcvChType \<Rightarrow> mClkStType \<Rightarrow> PrIds \<Rightarrow> temporal"
  where "MClkIPSpec send rcv cst p = TEMP
                           Init MClkInit rcv cst p
                         & \<box>[ MClkNext send rcv cst p ]_(cst!p, rtrner send!p, caller rcv!p)
                         & WF(MClkFwd send rcv cst p)_(cst!p, rtrner send!p, caller rcv!p)
                         & SF(MClkReply send rcv cst p)_(cst!p, rtrner send!p, caller rcv!p)"

definition
  MClkISpec     :: "mClkSndChType \<Rightarrow> mClkRcvChType \<Rightarrow> mClkStType \<Rightarrow> temporal"
  where "MClkISpec send rcv cst = TEMP (\<forall>p. MClkIPSpec send rcv cst p)"

lemmas MC_action_defs =
  MClkInit_def MClkFwd_def MClkRetry_def MClkReply_def MClkNext_def

lemmas MC_temp_defs = MClkIPSpec_def MClkISpec_def

(* The Clerk engages in an action for process p only if there is an outstanding,
   unanswered call for that process.
*)
lemma MClkidle: "\<turnstile> \<not>$Calling send p & $(cst!p) = #clkA \<longrightarrow> \<not>MClkNext send rcv cst p"
  by (auto simp: Return_def MC_action_defs)

lemma MClkbusy: "\<turnstile> $Calling rcv p \<longrightarrow> \<not>MClkNext send rcv cst p"
  by (auto simp: Call_def MC_action_defs)


(* Enabledness of actions *)

lemma MClkFwd_enabled: "\<And>p. basevars (rtrner send!p, caller rcv!p, cst!p) \<Longrightarrow>  
      \<turnstile> Calling send p & \<not>Calling rcv p & cst!p = #clkA   
         \<longrightarrow> Enabled (MClkFwd send rcv cst p)"
  by (tactic {* action_simp_tac (@{context} addsimps [@{thm MClkFwd_def},
    @{thm Call_def}, @{thm caller_def}, @{thm rtrner_def}]) [exI]
    [@{thm base_enabled}, @{thm Pair_inject}] 1 *})

lemma MClkFwd_ch_enabled: "\<turnstile> Enabled (MClkFwd send rcv cst p)  \<longrightarrow>   
         Enabled (<MClkFwd send rcv cst p>_(cst!p, rtrner send!p, caller rcv!p))"
  by (auto elim!: enabled_mono simp: angle_def MClkFwd_def)

lemma MClkReply_change: "\<turnstile> MClkReply send rcv cst p \<longrightarrow>  
         <MClkReply send rcv cst p>_(cst!p, rtrner send!p, caller rcv!p)"
  by (auto simp: angle_def MClkReply_def elim: Return_changed [temp_use])

lemma MClkReply_enabled: "\<And>p. basevars (rtrner send!p, caller rcv!p, cst!p) \<Longrightarrow>  
      \<turnstile> Calling send p & \<not>Calling rcv p & cst!p = #clkB   
         \<longrightarrow> Enabled (<MClkReply send rcv cst p>_(cst!p, rtrner send!p, caller rcv!p))"
  apply (tactic {* action_simp_tac @{context}
    [@{thm MClkReply_change} RSN (2, @{thm enabled_mono})] [] 1 *})
  apply (tactic {* action_simp_tac (@{context} addsimps
    [@{thm MClkReply_def}, @{thm Return_def}, @{thm caller_def}, @{thm rtrner_def}])
    [exI] [@{thm base_enabled}, @{thm Pair_inject}] 1 *})
  done

lemma MClkReplyNotRetry: "\<turnstile> MClkReply send rcv cst p \<longrightarrow> \<not>MClkRetry send rcv cst p"
  by (auto simp: MClkReply_def MClkRetry_def)

end
