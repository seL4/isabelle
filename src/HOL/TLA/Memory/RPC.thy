(*
    File:        RPC.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: RPC
    Logic Image: TLA

    RPC-Memory example: RPC specification
*)

RPC = RPCParameters + ProcedureInterface + Memory +

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

rules
  RPCInit_def       "RPCInit rcv rst p == PRED ((rst!p = #rpcA) & ~Calling rcv p)"

  RPCFwd_def        "RPCFwd send rcv rst p == ACT
                         $(Calling send p)
                         & $(rst!p) = # rpcA
                         & IsLegalRcvArg<arg<$(send!p)>>
                         & Call rcv p RPCRelayArg<arg<send!p>>
                         & (rst!p)$ = # rpcB
                         & unchanged (rtrner send!p)"

  RPCReject_def     "RPCReject send rcv rst p == ACT
                           $(rst!p) = # rpcA
                         & ~IsLegalRcvArg<arg<$(send!p)>>
                         & Return send p #BadCall
                         & unchanged ((rst!p), (caller rcv!p))"

  RPCFail_def       "RPCFail send rcv rst p == ACT
                           ~$(Calling rcv p)
                         & Return send p #RPCFailure
                         & (rst!p)$ = #rpcA
                         & unchanged (caller rcv!p)"

  RPCReply_def      "RPCReply send rcv rst p == ACT
                           ~$(Calling rcv p)
                         & $(rst!p) = #rpcB
		         & Return send p res<rcv!p>
                         & (rst!p)$ = #rpcA
                         & unchanged (caller rcv!p)"

  RPCNext_def       "RPCNext send rcv rst p == ACT
                        (  RPCFwd send rcv rst p
                         | RPCReject send rcv rst p
                         | RPCFail send rcv rst p
                         | RPCReply send rcv rst p)"

  RPCIPSpec_def     "RPCIPSpec send rcv rst p == TEMP
                           Init RPCInit rcv rst p
                         & [][ RPCNext send rcv rst p ]_(rst!p, rtrner send!p, caller rcv!p)
                         & WF(RPCNext send rcv rst p)_(rst!p, rtrner send!p, caller rcv!p)"

  RPCISpec_def      "RPCISpec send rcv rst == TEMP (ALL p. RPCIPSpec send rcv rst p)"

end



