(*
    File:        MemClerk.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: MemClerk
    Logic Image: TLA

    RPC-Memory example: specification of the memory clerk.
*)

MemClerk = Memory + RPC + MemClerkParameters +

types
  (* The clerk takes the same arguments as the memory and sends requests to the RPC *)
  mClkSndChType = "memChType"
  mClkRcvChType = "rpcSndChType"
  mClkStType    = "(PrIds => mClkState) stfun"

consts
  (* state predicates *)
  MClkInit      :: "mClkRcvChType => mClkStType => PrIds => stpred"

  (* actions *)
  MClkFwd       :: "mClkSndChType => mClkRcvChType => mClkStType => PrIds => action"
  MClkRetry     :: "mClkSndChType => mClkRcvChType => mClkStType => PrIds => action"
  MClkReply     :: "mClkSndChType => mClkRcvChType => mClkStType => PrIds => action"
  MClkNext      :: "mClkSndChType => mClkRcvChType => mClkStType => PrIds => action"

  (* temporal *)
  MClkIPSpec    :: "mClkSndChType => mClkRcvChType => mClkStType => PrIds => temporal"
  MClkISpec     :: "mClkSndChType => mClkRcvChType => mClkStType => temporal"

rules
  MClkInit_def     "$(MClkInit rcv cst p) .=
                        ($(cst@p) .= #clkA  .&  .~ $(Calling rcv p))"

  MClkFwd_def      "MClkFwd send rcv cst p ==
                        $(Calling send p)
                        .& $(cst@p) .= #clkA
                        .& Call rcv p (MClkRelayArg[ arg[$(send@p)] ])
                        .& (cst@p)$ .= #clkB
                        .& unchanged (rtrner send @ p)"

  MClkRetry_def    "MClkRetry send rcv cst p ==
                        $(cst@p) .= #clkB
                        .& res[$(rcv@p)] .= #RPCFailure
                        .& Call rcv p (MClkRelayArg[ arg[$(send@p)] ])
                        .& unchanged <cst@p, rtrner send @ p>"

  MClkReply_def    "MClkReply send rcv cst p ==
                        .~ $(Calling rcv p)
                        .& $(cst@p) .= #clkB
                        .& Return send p (MClkReplyVal[ res[$(rcv@p)] ])
                        .& (cst@p)$ .= #clkA
                        .& unchanged (caller rcv @ p)"

  MClkNext_def     "MClkNext send rcv cst p ==
                        MClkFwd send rcv cst p
                        .| MClkRetry send rcv cst p
                        .| MClkReply send rcv cst p"

  MClkIPSpec_def   "MClkIPSpec send rcv cst p ==
                        Init($(MClkInit rcv cst p))
                        .& [][ MClkNext send rcv cst p ]_<cst@p, rtrner send @ p, caller rcv @ p>
                        .& WF(MClkFwd send rcv cst p)_<cst@p, rtrner send @ p, caller rcv @ p>
                        .& SF(MClkReply send rcv cst p)_<cst@p, rtrner send @ p, caller rcv @ p>"

  MClkISpec_def    "MClkISpec send rcv cst == RALL p. MClkIPSpec send rcv cst p"
end


