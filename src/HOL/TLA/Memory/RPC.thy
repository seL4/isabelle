(*  Title:      HOL/TLA/Memory/RPC.thy
    Author:     Stephan Merz, University of Munich
*)

section \<open>RPC-Memory example: RPC specification\<close>

theory RPC
imports RPCParameters ProcedureInterface Memory
begin

type_synonym rpcSndChType = "(rpcOp,Vals) channel"
type_synonym rpcRcvChType = "memChType"
type_synonym rpcStType = "(PrIds \<Rightarrow> rpcState) stfun"


(* state predicates *)

definition RPCInit :: "rpcRcvChType \<Rightarrow> rpcStType \<Rightarrow> PrIds \<Rightarrow> stpred"
  where "RPCInit rcv rst p == PRED ((rst!p = #rpcA) \<and> \<not>Calling rcv p)"


(* actions *)

definition RPCFwd :: "rpcSndChType \<Rightarrow> rpcRcvChType \<Rightarrow> rpcStType \<Rightarrow> PrIds \<Rightarrow> action"
  where "RPCFwd send rcv rst p == ACT
      $(Calling send p)
    \<and> $(rst!p) = # rpcA
    \<and> IsLegalRcvArg<arg<$(send!p)>>
    \<and> Call rcv p RPCRelayArg<arg<send!p>>
    \<and> (rst!p)$ = # rpcB
    \<and> unchanged (rtrner send!p)"

definition RPCReject :: "rpcSndChType \<Rightarrow> rpcRcvChType \<Rightarrow> rpcStType \<Rightarrow> PrIds \<Rightarrow> action"
  where "RPCReject send rcv rst p == ACT
      $(rst!p) = # rpcA
    \<and> \<not>IsLegalRcvArg<arg<$(send!p)>>
    \<and> Return send p #BadCall
    \<and> unchanged ((rst!p), (caller rcv!p))"

definition RPCFail :: "rpcSndChType \<Rightarrow> rpcRcvChType \<Rightarrow> rpcStType \<Rightarrow> PrIds \<Rightarrow> action"
  where "RPCFail send rcv rst p == ACT
      \<not>$(Calling rcv p)
    \<and> Return send p #RPCFailure
    \<and> (rst!p)$ = #rpcA
    \<and> unchanged (caller rcv!p)"

definition RPCReply :: "rpcSndChType \<Rightarrow> rpcRcvChType \<Rightarrow> rpcStType \<Rightarrow> PrIds \<Rightarrow> action"
  where "RPCReply send rcv rst p == ACT
      \<not>$(Calling rcv p)
    \<and> $(rst!p) = #rpcB
    \<and> Return send p res<rcv!p>
    \<and> (rst!p)$ = #rpcA
    \<and> unchanged (caller rcv!p)"

definition RPCNext :: "rpcSndChType \<Rightarrow> rpcRcvChType \<Rightarrow> rpcStType \<Rightarrow> PrIds \<Rightarrow> action"
  where "RPCNext send rcv rst p == ACT
    (  RPCFwd send rcv rst p
     \<or> RPCReject send rcv rst p
     \<or> RPCFail send rcv rst p
     \<or> RPCReply send rcv rst p)"


(* temporal *)

definition RPCIPSpec :: "rpcSndChType \<Rightarrow> rpcRcvChType \<Rightarrow> rpcStType \<Rightarrow> PrIds \<Rightarrow> temporal"
  where "RPCIPSpec send rcv rst p == TEMP
     Init RPCInit rcv rst p
   \<and> \<box>[ RPCNext send rcv rst p ]_(rst!p, rtrner send!p, caller rcv!p)
   \<and> WF(RPCNext send rcv rst p)_(rst!p, rtrner send!p, caller rcv!p)"

definition RPCISpec :: "rpcSndChType \<Rightarrow> rpcRcvChType \<Rightarrow> rpcStType \<Rightarrow> temporal"
  where "RPCISpec send rcv rst == TEMP (\<forall>p. RPCIPSpec send rcv rst p)"


lemmas RPC_action_defs =
  RPCInit_def RPCFwd_def RPCReject_def RPCFail_def RPCReply_def RPCNext_def

lemmas RPC_temp_defs = RPCIPSpec_def RPCISpec_def


(* The RPC component engages in an action for process p only if there is an outstanding,
   unanswered call for that process.
*)

lemma RPCidle: "\<turnstile> \<not>$(Calling send p) \<longrightarrow> \<not>RPCNext send rcv rst p"
  by (auto simp: AReturn_def RPC_action_defs)

lemma RPCbusy: "\<turnstile> $(Calling rcv p) \<and> $(rst!p) = #rpcB \<longrightarrow> \<not>RPCNext send rcv rst p"
  by (auto simp: RPC_action_defs)

(* RPC failure actions are visible. *)
lemma RPCFail_vis: "\<turnstile> RPCFail send rcv rst p \<longrightarrow>  
    <RPCNext send rcv rst p>_(rst!p, rtrner send!p, caller rcv!p)"
  by (auto dest!: Return_changed [temp_use] simp: angle_def RPCNext_def RPCFail_def)

lemma RPCFail_Next_enabled: "\<turnstile> Enabled (RPCFail send rcv rst p) \<longrightarrow>  
    Enabled (<RPCNext send rcv rst p>_(rst!p, rtrner send!p, caller rcv!p))"
  by (force elim!: enabled_mono [temp_use] RPCFail_vis [temp_use])

(* Enabledness of some actions *)
lemma RPCFail_enabled: "\<And>p. basevars (rtrner send!p, caller rcv!p, rst!p) \<Longrightarrow>  
    \<turnstile> \<not>Calling rcv p \<and> Calling send p \<longrightarrow> Enabled (RPCFail send rcv rst p)"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm RPCFail_def},
    @{thm AReturn_def}, @{thm caller_def}, @{thm rtrner_def}]) [exI]
    [@{thm base_enabled}, @{thm Pair_inject}] 1\<close>)

lemma RPCReply_enabled: "\<And>p. basevars (rtrner send!p, caller rcv!p, rst!p) \<Longrightarrow>  
      \<turnstile> \<not>Calling rcv p \<and> Calling send p \<and> rst!p = #rpcB  
         \<longrightarrow> Enabled (RPCReply send rcv rst p)"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm RPCReply_def},
    @{thm AReturn_def}, @{thm caller_def}, @{thm rtrner_def}]) [exI]
    [@{thm base_enabled}, @{thm Pair_inject}] 1\<close>)

end
