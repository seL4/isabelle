(*
    File:        Memory.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: Memory
    Logic Image: TLA

    RPC-Memory example: Memory specification
*)

Memory = MemoryParameters + ProcedureInterface +

types
  memChType  = "(memOp, Vals) channel"
  memType = "(Locs => Vals) stfun"      (* intention: MemLocs => MemVals *)
  resType = "(PrIds => Vals) stfun"

consts
  (* state predicates *)
  MInit      :: "memType => Locs => stpred"
  PInit      :: "resType => PrIds => stpred"
  (* auxiliary predicates: is there a pending read/write request for
     some process id and location/value? *)
  RdRequest  :: "memChType => PrIds => Locs => stpred"
  WrRequest  :: "memChType => PrIds => Locs => Vals => stpred"

  (* actions *)
  GoodRead   :: "memType => resType => PrIds => Locs => action"
  BadRead    :: "memType => resType => PrIds => Locs => action"
  ReadInner  :: "memChType => memType => resType => PrIds => Locs => action"
  Read       :: "memChType => memType => resType => PrIds => action"
  GoodWrite  :: "memType => resType => PrIds => Locs => Vals => action"
  BadWrite   :: "memType => resType => PrIds => Locs => Vals => action"
  WriteInner :: "memChType => memType => resType => PrIds => Locs => Vals => action"
  Write      :: "memChType => memType => resType => PrIds => Locs => action"
  MemReturn  :: "memChType => resType => PrIds => action"
  MemFail    :: "memChType => resType => PrIds => action"
  RNext      :: "memChType => memType => resType => PrIds => action"
  UNext      :: "memChType => memType => resType => PrIds => action"

  (* temporal formulas *)
  RPSpec     :: "memChType => memType => resType => PrIds => temporal"
  UPSpec     :: "memChType => memType => resType => PrIds => temporal"
  MSpec      :: "memChType => memType => resType => Locs => temporal"
  IRSpec     :: "memChType => memType => resType => temporal"
  IUSpec     :: "memChType => memType => resType => temporal"

  RSpec      :: "memChType => resType => temporal"
  USpec      :: "memChType => temporal"

  (* memory invariant: in the paper, the invariant is hidden in the definition of
     the predicate S used in the implementation proof, but it is easier to verify 
     at this level. *)
  MemInv    :: "memType => Locs => stpred"

rules
  MInit_def         "MInit mm l == PRED mm!l = #InitVal"
  PInit_def         "PInit rs p == PRED rs!p = #NotAResult"

  RdRequest_def     "RdRequest ch p l == PRED
                         Calling ch p & (arg<ch!p> = #(read l))"
  WrRequest_def     "WrRequest ch p l v == PRED
                         Calling ch p & (arg<ch!p> = #(write l v))"
  (* a read that doesn't raise BadArg *)
  GoodRead_def      "GoodRead mm rs p l == ACT
                        #l : #MemLoc & ((rs!p)$ = $(mm!l))"
  (* a read that raises BadArg *)
  BadRead_def       "BadRead mm rs p l == ACT
                        #l ~: #MemLoc & ((rs!p)$ = #BadArg)"
  (* the read action with l visible *)
  ReadInner_def     "ReadInner ch mm rs p l == ACT
                         $(RdRequest ch p l)
                         & (GoodRead mm rs p l  |  BadRead mm rs p l)
                         & unchanged (rtrner ch ! p)"
  (* the read action with l quantified *)
  Read_def          "Read ch mm rs p == ACT (? l. ReadInner ch mm rs p l)"

  (* similar definitions for the write action *)
  GoodWrite_def     "GoodWrite mm rs p l v == ACT
                        #l : #MemLoc & #v : #MemVal
                        & ((mm!l)$ = #v) & ((rs!p)$ = #OK)"
  BadWrite_def      "BadWrite mm rs p l v == ACT
                        ~ (#l : #MemLoc & #v : #MemVal)
                        & ((rs!p)$ = #BadArg) & unchanged (mm!l)"
  WriteInner_def    "WriteInner ch mm rs p l v == ACT
                        $(WrRequest ch p l v)
                        & (GoodWrite mm rs p l v  |  BadWrite mm rs p l v)
                        & unchanged (rtrner ch ! p)"
  Write_def         "Write ch mm rs p l == ACT (? v. WriteInner ch mm rs p l v)"

  (* the return action *)
  MemReturn_def     "MemReturn ch rs p == ACT
                       (   ($(rs!p) ~= #NotAResult)
                        & ((rs!p)$ = #NotAResult)
                        & Return ch p (rs!p))"

  (* the failure action of the unreliable memory *)
  MemFail_def       "MemFail ch rs p == ACT
                        $(Calling ch p)
                        & ((rs!p)$ = #MemFailure)
                        & unchanged (rtrner ch ! p)"
  (* next-state relations for reliable / unreliable memory *)
  RNext_def         "RNext ch mm rs p == ACT 
                       (  Read ch mm rs p
                        | (? l. Write ch mm rs p l)
                        | MemReturn ch rs p)"
  UNext_def         "UNext ch mm rs p == ACT
                        (RNext ch mm rs p | MemFail ch rs p)"

  RPSpec_def        "RPSpec ch mm rs p == TEMP
                        Init(PInit rs p)
                        & [][ RNext ch mm rs p ]_(rtrner ch ! p, rs!p)
                        & WF(RNext ch mm rs p)_(rtrner ch ! p, rs!p)
                        & WF(MemReturn ch rs p)_(rtrner ch ! p, rs!p)"
  UPSpec_def        "UPSpec ch mm rs p == TEMP
                        Init(PInit rs p)
                        & [][ UNext ch mm rs p ]_(rtrner ch ! p, rs!p)
                        & WF(RNext ch mm rs p)_(rtrner ch ! p, rs!p)
                        & WF(MemReturn ch rs p)_(rtrner ch ! p, rs!p)"
  MSpec_def         "MSpec ch mm rs l == TEMP
                        Init(MInit mm l)
                        & [][ ? p. Write ch mm rs p l ]_(mm!l)"
  IRSpec_def        "IRSpec ch mm rs == TEMP
                        (! p. RPSpec ch mm rs p)
                        & (! l. #l : #MemLoc --> MSpec ch mm rs l)"
  IUSpec_def        "IUSpec ch mm rs == TEMP
                        (! p. UPSpec ch mm rs p)
                        & (! l. #l : #MemLoc --> MSpec ch mm rs l)"

  RSpec_def         "RSpec ch rs == TEMP (EEX mm. IRSpec ch mm rs)"
  USpec_def         "USpec ch == TEMP (EEX mm rs. IUSpec ch mm rs)"

  MemInv_def        "MemInv mm l == PRED  #l : #MemLoc --> mm!l : #MemVal"
end



