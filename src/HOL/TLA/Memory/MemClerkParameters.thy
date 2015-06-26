(*  Title:      HOL/TLA/Memory/MemClerkParameters.thy
    Author:     Stephan Merz, University of Munich
*)

section \<open>RPC-Memory example: Parameters of the memory clerk\<close>

theory MemClerkParameters
imports RPCParameters
begin

datatype mClkState = clkA | clkB

(* types sent on the clerk's send and receive channels are argument types
   of the memory and the RPC, respectively *)
type_synonym mClkSndArgType = "memOp"
type_synonym mClkRcvArgType = "rpcOp"

definition
  (* translate a memory call to an RPC call *)
  MClkRelayArg     :: "memOp \<Rightarrow> rpcOp"
  where "MClkRelayArg marg = memcall marg"

definition
  (* translate RPC failures to memory failures *)
  MClkReplyVal     :: "Vals \<Rightarrow> Vals"
  where "MClkReplyVal v = (if v = RPCFailure then MemFailure else v)"

end
