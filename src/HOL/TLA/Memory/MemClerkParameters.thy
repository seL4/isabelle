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
  mClkSndArgType   = "memOp"
  mClkRcvArgType   = "rpcOp"

constdefs
  (* translate a memory call to an RPC call *)
  MClkRelayArg     :: "memOp => rpcOp"
    "MClkRelayArg marg == memcall marg"
  (* translate RPC failures to memory failures *)
  MClkReplyVal     :: "Vals => Vals"
    "MClkReplyVal v == if v = RPCFailure then MemFailure else v"

end

