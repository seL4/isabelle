(*  Title:      HOL/TLA/Memory/RPCParameters.thy
    Author:     Stephan Merz, University of Munich
*)

header {* RPC-Memory example: RPC parameters *}

theory RPCParameters
imports MemoryParameters
begin

(*
  For simplicity, specify the instance of RPC that is used in the
  memory implementation.
*)

datatype rpcOp = memcall memOp | othercall Vals
datatype rpcState = rpcA | rpcB

consts
  (* some particular return values *)
  RPCFailure     :: Vals
  BadCall        :: Vals
  
  (* Translate an rpc call to a memory call and test if the current argument
     is legal for the receiver (i.e., the memory). This can now be a little
     simpler than for the generic RPC component. RelayArg returns an arbitrary
     memory call for illegal arguments. *)
  IsLegalRcvArg  :: "rpcOp => bool"
  RPCRelayArg    :: "rpcOp => memOp"

axiomatization where
  (* RPCFailure is different from MemVals and exceptions *)
  RFNoMemVal:        "RPCFailure ~: MemVal" and
  NotAResultNotRF:   "NotAResult ~= RPCFailure" and
  OKNotRF:           "OK ~= RPCFailure" and
  BANotRF:           "BadArg ~= RPCFailure"

defs
  IsLegalRcvArg_def: "IsLegalRcvArg ra ==
                         case ra of (memcall m) => True
                                  | (othercall v) => False"
  RPCRelayArg_def:   "RPCRelayArg ra ==
                         case ra of (memcall m) => m
                                  | (othercall v) => undefined"

lemmas [simp] = RFNoMemVal NotAResultNotRF OKNotRF BANotRF
  NotAResultNotRF [symmetric] OKNotRF [symmetric] BANotRF [symmetric]

end
