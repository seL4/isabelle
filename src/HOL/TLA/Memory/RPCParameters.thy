(*
    File:        RPCParameters.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: RPCParameters
    Logic Image: TLA

    RPC-Memory example: RPC parameters
    For simplicity, specify the instance of RPC that is used in the
    memory implementation.
*)

RPCParameters = MemoryParameters +

datatype  rpcOp = memcall memOp | othercall Vals
datatype  rpcState = rpcA | rpcB

consts
  (* some particular return values *)
  RPCFailure     :: Vals
  BadCall        :: Vals
  
  (* Translate an rpc call to a memory call and test if the current argument
     is legal for the receiver (i.e., the memory). This can now be a little
     simpler than for the generic RPC component. RelayArg returns an arbitrary
     memory call for illegal arguments. *)
  IsLegalRcvArg  :: rpcOp => bool
  RPCRelayArg    :: rpcOp => memOp

rules
  (* RPCFailure is different from MemVals and exceptions *)
  RFNoMemVal        "RPCFailure ~: MemVal"
  NotAResultNotRF   "NotAResult ~= RPCFailure"
  OKNotRF           "OK ~= RPCFailure"
  BANotRF           "BadArg ~= RPCFailure"

defs
  IsLegalRcvArg_def "IsLegalRcvArg ra ==
		         case ra of (memcall m) => True
		                  | (othercall v) => False"
  RPCRelayArg_def   "RPCRelayArg ra ==
		         case ra of (memcall m) => m
		                  | (othercall v) => arbitrary"
end


