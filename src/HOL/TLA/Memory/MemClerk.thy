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

end


