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
  memChType  = "(memArgType,Vals) channel"
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
  MInit_def         "$(MInit mm l) .= ($(mm@l) .= # InitVal)"
  PInit_def         "$(PInit rs p) .= ($(rs@p) .= # NotAResult)"

  RdRequest_def     "$(RdRequest ch p l) .= 
                         ($(Calling ch p) .& (arg[$(ch@p)] .= #(Inl (read,l))))"
  WrRequest_def     "$(WrRequest ch p l v) .=
                         ($(Calling ch p) .& (arg[$(ch@p)] .= #(Inr (write,l,v))))"
  (* a read that doesn't raise BadArg *)
  GoodRead_def      "GoodRead mm rs p l ==
                        #(MemLoc l) .& (rs@p)$ .= $(mm@l)"
  (* a read that raises BadArg *)
  BadRead_def       "BadRead mm rs p l ==
                        .~ #(MemLoc l) .& (rs@p)$ .= #BadArg"
  (* the read action with l visible *)
  ReadInner_def     "ReadInner ch mm rs p l ==
                         $(RdRequest ch p l)
                         .& (GoodRead mm rs p l  .|  BadRead mm rs p l)
                         .& unchanged (rtrner ch @ p)"
  (* the read action with l quantified *)
  Read_def          "Read ch mm rs p == REX l. ReadInner ch mm rs p l"

  (* similar definitions for the write action *)
  GoodWrite_def     "GoodWrite mm rs p l v ==
                        #(MemLoc l) .& #(MemVal v) 
                        .& (mm@l)$ .= #v .& (rs@p)$ .= #OK"
  BadWrite_def      "BadWrite mm rs p l v ==
                        .~ (#(MemLoc l) .& #(MemVal v))
                        .& (rs@p)$ .= #BadArg .& unchanged (mm@l)"
  WriteInner_def    "WriteInner ch mm rs p l v ==
                        $(WrRequest ch p l v)
                        .& (GoodWrite mm rs p l v  .|  BadWrite mm rs p l v)
                        .& unchanged (rtrner ch @ p)"
  Write_def         "Write ch mm rs p l == REX v. WriteInner ch mm rs p l v"

  (* the return action *)
  MemReturn_def     "MemReturn ch rs p ==
                        $(rs@p) .~= #NotAResult
                        .& (rs@p)$ .= #NotAResult
                        .& Return ch p ($(rs@p))"
  (* the failure action of the unreliable memory *)
  MemFail_def       "MemFail ch rs p ==
                        $(Calling ch p)
                        .& (rs@p)$ .= #MemFailure
                        .& unchanged (rtrner ch @ p)"
  RNext_def         "RNext ch mm rs p ==
                        Read ch mm rs p
                        .| (REX l. Write ch mm rs p l)
                        .| MemReturn ch rs p"
  UNext_def         "UNext ch mm rs p ==
                        RNext ch mm rs p .| MemFail ch rs p"

  RPSpec_def        "RPSpec ch mm rs p ==
                        Init($(PInit rs p))
                        .& [][ RNext ch mm rs p ]_<rtrner ch @ p, rs@p>
                        .& WF(RNext ch mm rs p)_<rtrner ch @ p, rs@p>
                        .& WF(MemReturn ch rs p)_<rtrner ch @ p, rs@p>"
  UPSpec_def        "UPSpec ch mm rs p ==
                        Init($(PInit rs p))
                        .& [][ UNext ch mm rs p ]_<rtrner ch @ p, rs@p>
                        .& WF(RNext ch mm rs p)_<rtrner ch @ p, rs@p>
                        .& WF(MemReturn ch rs p)_<rtrner ch @ p, rs@p>"
  MSpec_def         "MSpec ch mm rs l ==
                        Init($(MInit mm l))
                        .& [][ REX p. Write ch mm rs p l ]_(mm@l)"
  IRSpec_def        "IRSpec ch mm rs ==
                        (RALL p. RPSpec ch mm rs p)
                        .& (RALL l. #(MemLoc l) .-> MSpec ch mm rs l)"
  IUSpec_def        "IUSpec ch mm rs ==
                        (RALL p. UPSpec ch mm rs p)
                        .& (RALL l. #(MemLoc l) .-> MSpec ch mm rs l)"

  RSpec_def         "RSpec ch rs == EEX mm. IRSpec ch mm rs"
  USpec_def         "USpec ch == EEX mm rs. IUSpec ch mm rs"

  MemInv_def        "$(MemInv mm l) .=
                        (#(MemLoc l) .-> MemVal[ $(mm@l)])"
end



