(*
    File:        MemClerkParameters.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: MemClerkParameters
    Logic Image: TLA

    RPC-Memory example: Parameters of the memory clerk.
*)

MemClerkParameters = RPCParameters + 

datatype  mClkState  =  clkA | clkB

types
  (* types sent on the clerk's send and receive channels are argument types
     of the memory and the RPC, respectively *)
  mClkSndArgType   = "memArgType"
  mClkRcvArgType   = "rpcArgType"

consts
  (* translate a memory call to an RPC call *)
  MClkRelayArg     :: "memArgType => rpcArgType"
  (* translate RPC failures to memory failures *)
  MClkReplyVal     :: "Vals => Vals"

rules
  MClkRelayArg_def    "MClkRelayArg marg == Inl (remoteCall, marg)"
  MClkReplyVal_def    "MClkReplyVal v == 
                           if v = RPCFailure then MemFailure else v"

end

