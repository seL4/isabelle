(*
    File:        Memory.thy
    ID:          $Id$
    Author:      Stephan Merz
    Copyright:   1997 University of Munich
*)

header {* RPC-Memory example: Memory specification *}

theory Memory
imports MemoryParameters ProcedureInterface
begin

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

defs
  MInit_def:         "MInit mm l == PRED mm!l = #InitVal"
  PInit_def:         "PInit rs p == PRED rs!p = #NotAResult"

  RdRequest_def:     "RdRequest ch p l == PRED
                         Calling ch p & (arg<ch!p> = #(read l))"
  WrRequest_def:     "WrRequest ch p l v == PRED
                         Calling ch p & (arg<ch!p> = #(write l v))"
  (* a read that doesn't raise BadArg *)
  GoodRead_def:      "GoodRead mm rs p l == ACT
                        #l : #MemLoc & ((rs!p)$ = $(mm!l))"
  (* a read that raises BadArg *)
  BadRead_def:       "BadRead mm rs p l == ACT
                        #l ~: #MemLoc & ((rs!p)$ = #BadArg)"
  (* the read action with l visible *)
  ReadInner_def:     "ReadInner ch mm rs p l == ACT
                         $(RdRequest ch p l)
                         & (GoodRead mm rs p l  |  BadRead mm rs p l)
                         & unchanged (rtrner ch ! p)"
  (* the read action with l quantified *)
  Read_def:          "Read ch mm rs p == ACT (EX l. ReadInner ch mm rs p l)"

  (* similar definitions for the write action *)
  GoodWrite_def:     "GoodWrite mm rs p l v == ACT
                        #l : #MemLoc & #v : #MemVal
                        & ((mm!l)$ = #v) & ((rs!p)$ = #OK)"
  BadWrite_def:      "BadWrite mm rs p l v == ACT
                        ~ (#l : #MemLoc & #v : #MemVal)
                        & ((rs!p)$ = #BadArg) & unchanged (mm!l)"
  WriteInner_def:    "WriteInner ch mm rs p l v == ACT
                        $(WrRequest ch p l v)
                        & (GoodWrite mm rs p l v  |  BadWrite mm rs p l v)
                        & unchanged (rtrner ch ! p)"
  Write_def:         "Write ch mm rs p l == ACT (EX v. WriteInner ch mm rs p l v)"

  (* the return action *)
  MemReturn_def:     "MemReturn ch rs p == ACT
                       (   ($(rs!p) ~= #NotAResult)
                        & ((rs!p)$ = #NotAResult)
                        & Return ch p (rs!p))"

  (* the failure action of the unreliable memory *)
  MemFail_def:       "MemFail ch rs p == ACT
                        $(Calling ch p)
                        & ((rs!p)$ = #MemFailure)
                        & unchanged (rtrner ch ! p)"
  (* next-state relations for reliable / unreliable memory *)
  RNext_def:         "RNext ch mm rs p == ACT
                       (  Read ch mm rs p
                        | (EX l. Write ch mm rs p l)
                        | MemReturn ch rs p)"
  UNext_def:         "UNext ch mm rs p == ACT
                        (RNext ch mm rs p | MemFail ch rs p)"

  RPSpec_def:        "RPSpec ch mm rs p == TEMP
                        Init(PInit rs p)
                        & [][ RNext ch mm rs p ]_(rtrner ch ! p, rs!p)
                        & WF(RNext ch mm rs p)_(rtrner ch ! p, rs!p)
                        & WF(MemReturn ch rs p)_(rtrner ch ! p, rs!p)"
  UPSpec_def:        "UPSpec ch mm rs p == TEMP
                        Init(PInit rs p)
                        & [][ UNext ch mm rs p ]_(rtrner ch ! p, rs!p)
                        & WF(RNext ch mm rs p)_(rtrner ch ! p, rs!p)
                        & WF(MemReturn ch rs p)_(rtrner ch ! p, rs!p)"
  MSpec_def:         "MSpec ch mm rs l == TEMP
                        Init(MInit mm l)
                        & [][ EX p. Write ch mm rs p l ]_(mm!l)"
  IRSpec_def:        "IRSpec ch mm rs == TEMP
                        (ALL p. RPSpec ch mm rs p)
                        & (ALL l. #l : #MemLoc --> MSpec ch mm rs l)"
  IUSpec_def:        "IUSpec ch mm rs == TEMP
                        (ALL p. UPSpec ch mm rs p)
                        & (ALL l. #l : #MemLoc --> MSpec ch mm rs l)"

  RSpec_def:         "RSpec ch rs == TEMP (EEX mm. IRSpec ch mm rs)"
  USpec_def:         "USpec ch == TEMP (EEX mm rs. IUSpec ch mm rs)"

  MemInv_def:        "MemInv mm l == PRED  #l : #MemLoc --> mm!l : #MemVal"

lemmas RM_action_defs =
  MInit_def PInit_def RdRequest_def WrRequest_def MemInv_def
  GoodRead_def BadRead_def ReadInner_def Read_def
  GoodWrite_def BadWrite_def WriteInner_def Write_def
  MemReturn_def RNext_def

lemmas UM_action_defs = RM_action_defs MemFail_def UNext_def

lemmas RM_temp_defs = RPSpec_def MSpec_def IRSpec_def
lemmas UM_temp_defs = UPSpec_def MSpec_def IUSpec_def


(* The reliable memory is an implementation of the unreliable one *)
lemma ReliableImplementsUnReliable: "|- IRSpec ch mm rs --> IUSpec ch mm rs"
  by (force simp: UNext_def UPSpec_def IUSpec_def RM_temp_defs elim!: STL4E [temp_use] squareE)

(* The memory spec implies the memory invariant *)
lemma MemoryInvariant: "|- MSpec ch mm rs l --> [](MemInv mm l)"
  by (tactic {* auto_inv_tac
    (simpset () addsimps (thms "RM_temp_defs" @ thms "RM_action_defs")) 1 *})

(* The invariant is trivial for non-locations *)
lemma NonMemLocInvariant: "|- #l ~: #MemLoc --> [](MemInv mm l)"
  by (auto simp: MemInv_def intro!: necT [temp_use])

lemma MemoryInvariantAll:
    "|- (ALL l. #l : #MemLoc --> MSpec ch mm rs l) --> (ALL l. [](MemInv mm l))"
  apply clarify
  apply (case_tac "l : MemLoc")
  apply (auto elim!: MemoryInvariant [temp_use] NonMemLocInvariant [temp_use])
  done

(* The memory engages in an action for process p only if there is an
   unanswered call from p.
   We need this only for the reliable memory.
*)

lemma Memoryidle: "|- ~$(Calling ch p) --> ~ RNext ch mm rs p"
  by (auto simp: Return_def RM_action_defs)

(* Enabledness conditions *)

lemma MemReturn_change: "|- MemReturn ch rs p --> <MemReturn ch rs p>_(rtrner ch ! p, rs!p)"
  by (force simp: MemReturn_def angle_def)

lemma MemReturn_enabled: "!!p. basevars (rtrner ch ! p, rs!p) ==>
      |- Calling ch p & (rs!p ~= #NotAResult)
         --> Enabled (<MemReturn ch rs p>_(rtrner ch ! p, rs!p))"
  apply (tactic
    {* action_simp_tac (simpset ()) [thm "MemReturn_change" RSN (2, thm "enabled_mono") ] [] 1 *})
  apply (tactic
    {* action_simp_tac (simpset () addsimps [thm "MemReturn_def", thm "Return_def",
      thm "rtrner_def"]) [exI] [thm "base_enabled", thm "Pair_inject"] 1 *})
  done

lemma ReadInner_enabled: "!!p. basevars (rtrner ch ! p, rs!p) ==>
      |- Calling ch p & (arg<ch!p> = #(read l)) --> Enabled (ReadInner ch mm rs p l)"
  apply (case_tac "l : MemLoc")
  apply (force simp: ReadInner_def GoodRead_def BadRead_def RdRequest_def
    intro!: exI elim!: base_enabled [temp_use])+
  done

lemma WriteInner_enabled: "!!p. basevars (mm!l, rtrner ch ! p, rs!p) ==>
      |- Calling ch p & (arg<ch!p> = #(write l v))
         --> Enabled (WriteInner ch mm rs p l v)"
  apply (case_tac "l:MemLoc & v:MemVal")
  apply (force simp: WriteInner_def GoodWrite_def BadWrite_def WrRequest_def
    intro!: exI elim!: base_enabled [temp_use])+
  done

lemma ReadResult: "|- Read ch mm rs p & (!l. $(MemInv mm l)) --> (rs!p)` ~= #NotAResult"
  by (force simp: Read_def ReadInner_def GoodRead_def BadRead_def MemInv_def)

lemma WriteResult: "|- Write ch mm rs p l --> (rs!p)` ~= #NotAResult"
  by (auto simp: Write_def WriteInner_def GoodWrite_def BadWrite_def)

lemma ReturnNotReadWrite: "|- (ALL l. $MemInv mm l) & MemReturn ch rs p
         --> ~ Read ch mm rs p & (ALL l. ~ Write ch mm rs p l)"
  by (auto simp: MemReturn_def dest!: WriteResult [temp_use] ReadResult [temp_use])

lemma RWRNext_enabled: "|- (rs!p = #NotAResult) & (!l. MemInv mm l)
         & Enabled (Read ch mm rs p | (? l. Write ch mm rs p l))
         --> Enabled (<RNext ch mm rs p>_(rtrner ch ! p, rs!p))"
  by (force simp: RNext_def angle_def elim!: enabled_mono2
    dest: ReadResult [temp_use] WriteResult [temp_use])


(* Combine previous lemmas: the memory can make a visible step if there is an
   outstanding call for which no result has been produced.
*)
lemma RNext_enabled: "!!p. !l. basevars (mm!l, rtrner ch!p, rs!p) ==>
      |- (rs!p = #NotAResult) & Calling ch p & (!l. MemInv mm l)
         --> Enabled (<RNext ch mm rs p>_(rtrner ch ! p, rs!p))"
  apply (auto simp: enabled_disj [try_rewrite] intro!: RWRNext_enabled [temp_use])
  apply (case_tac "arg (ch w p)")
   apply (tactic {* action_simp_tac (simpset () addsimps [thm "Read_def",
     temp_rewrite (thm "enabled_ex")]) [thm "ReadInner_enabled", exI] [] 1 *})
   apply (force dest: base_pair [temp_use])
  apply (erule contrapos_np)
  apply (tactic {* action_simp_tac (simpset () addsimps [thm "Write_def",
    temp_rewrite (thm "enabled_ex")])
    [thm "WriteInner_enabled", exI] [] 1 *})
  done

end
