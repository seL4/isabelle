(*
    File:        MemoryImplementation.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: MemoryImplementation
    Logic Image: TLA

    RPC-Memory example: Memory implementation
*)

MemoryImplementation = Memory + RPC + MemClerk + Datatype +

datatype  histState  =  histA | histB

types
  histType  = "(PrIds => histState) stfun"     (* the type of the history variable *)

consts
  (* the specification *)
     (* channel (external) *)
  memCh         :: "memChType"
     (* internal variables *)
  mm            :: "memType"
  
  (* the state variables of the implementation *)
     (* channels *)
  (* same interface channel memCh *)
  crCh          :: "rpcSndChType"
  rmCh          :: "rpcRcvChType"
     (* internal variables *)
  (* identity refinement mapping for mm -- simply reused *)
  rst           :: "rpcStType"
  cst           :: "mClkStType"
  ires          :: "resType"
(* the history variable : not defined as a constant
  rmhist        :: "histType"
*)

constdefs
  (* auxiliary predicates *)
  MVOKBARF      :: "Vals => bool"
     "MVOKBARF v == (v : MemVal) | (v = OK) | (v = BadArg) | (v = RPCFailure)"
  MVOKBA        :: "Vals => bool"
     "MVOKBA v   == (v : MemVal) | (v = OK) | (v = BadArg)"
  MVNROKBA      :: "Vals => bool"
     "MVNROKBA v == (v : MemVal) | (v = NotAResult) | (v = OK) | (v = BadArg)"

  (* tuples of state functions changed by the various components *)
  e             :: "PrIds => (bit * memOp) stfun"
     "e p == PRED (caller memCh!p)"
  c             :: "PrIds => (mClkState * (bit * Vals) * (bit * rpcOp)) stfun"
     "c p == PRED (cst!p, rtrner memCh!p, caller crCh!p)"
  r             :: "PrIds => (rpcState * (bit * Vals) * (bit * memOp)) stfun"
     "r p == PRED (rst!p, rtrner crCh!p, caller rmCh!p)"
  m             :: "PrIds => ((bit * Vals) * Vals) stfun"
     "m p == PRED (rtrner rmCh!p, ires!p)"

  (* the environment action *)
  ENext         :: "PrIds => action"
     "ENext p == ACT (? l. #l : #MemLoc & Call memCh p #(read l))"


  (* specification of the history variable *)
  HInit         :: "histType => PrIds => stpred"
     "HInit rmhist p == PRED rmhist!p = #histA"

  HNext         :: "histType => PrIds => action"
     "HNext rmhist p == ACT (rmhist!p)$ =
                     (if (MemReturn rmCh ires p | RPCFail crCh rmCh rst p)
                      then #histB
                      else if (MClkReply memCh crCh cst p)
                           then #histA
                           else $(rmhist!p))"

  HistP         :: "histType => PrIds => temporal"
     "HistP rmhist p == TEMP Init HInit rmhist p
                           & [][HNext rmhist p]_(c p,r p,m p, rmhist!p)"

  Hist          :: "histType => temporal"
      "Hist rmhist == TEMP (!p. HistP rmhist p)"

  (* the implementation *)
  IPImp          :: "PrIds => temporal"
     "IPImp p == TEMP (  Init ~Calling memCh p & [][ENext p]_(e p)
	               & MClkIPSpec memCh crCh cst p
  	               & RPCIPSpec crCh rmCh rst p
	               & RPSpec rmCh mm ires p
		       & (! l. #l : #MemLoc --> MSpec rmCh mm ires l))"

  ImpInit        :: "PrIds => stpred"
      "ImpInit p == PRED (  ~Calling memCh p
                          & MClkInit crCh cst p
	                  & RPCInit rmCh rst p
	                  & PInit ires p)"

  ImpNext        :: "PrIds => action"
      "ImpNext p == ACT  [ENext p]_(e p) 
                       & [MClkNext memCh crCh cst p]_(c p)
                       & [RPCNext crCh rmCh rst p]_(r p) 
                       & [RNext rmCh mm ires p]_(m p)"

  ImpLive        :: "PrIds => temporal"
      "ImpLive p == TEMP  WF(MClkFwd memCh crCh cst p)_(c p) 
			& SF(MClkReply memCh crCh cst p)_(c p)
			& WF(RPCNext crCh rmCh rst p)_(r p) 
			& WF(RNext rmCh mm ires p)_(m p)
			& WF(MemReturn rmCh ires p)_(m p)"

  Implementation :: "temporal"
      "Implementation == TEMP ( (!p. Init (~Calling memCh p) & [][ENext p]_(e p))
                               & MClkISpec memCh crCh cst
                               & RPCISpec crCh rmCh rst
                               & IRSpec rmCh mm ires)"

  (* the predicate S describes the states of the implementation.
     slight simplification: two "histState" parameters instead of a
     (one- or two-element) set.
     NB: The second conjunct of the definition in the paper is taken care of by
     the type definitions. The last conjunct is asserted separately as the memory
     invariant MemInv, proved in Memory.ML. *)
  S :: "histType => bool => bool => bool => mClkState => rpcState => histState => histState => PrIds => stpred"
      "S rmhist ecalling ccalling rcalling cs rs hs1 hs2 p == PRED
                Calling memCh p = #ecalling
              & Calling crCh p  = #ccalling
              & (#ccalling --> arg<crCh!p> = MClkRelayArg<arg<memCh!p>>)
              & (~ #ccalling & cst!p = #clkB --> MVOKBARF<res<crCh!p>>)
              & Calling rmCh p  = #rcalling
              & (#rcalling --> arg<rmCh!p> = RPCRelayArg<arg<crCh!p>>)
              & (~ #rcalling --> ires!p = #NotAResult)
              & (~ #rcalling & rst!p = #rpcB --> MVOKBA<res<rmCh!p>>)
              & cst!p = #cs
              & rst!p = #rs
              & (rmhist!p = #hs1 | rmhist!p = #hs2)
              & MVNROKBA<ires!p>"

  (* predicates S1 -- S6 define special instances of S *)
  S1            :: "histType => PrIds => stpred"
      "S1 rmhist p == S rmhist False False False clkA rpcA histA histA p"
  S2            :: "histType => PrIds => stpred"
      "S2 rmhist p == S rmhist True False False clkA rpcA histA histA p"
  S3            :: "histType => PrIds => stpred"
      "S3 rmhist p == S rmhist True True False clkB rpcA histA histB p"
  S4            :: "histType => PrIds => stpred"
      "S4 rmhist p == S rmhist True True True clkB rpcB histA histB p"
  S5            :: "histType => PrIds => stpred"
      "S5 rmhist p == S rmhist True True False clkB rpcB histB histB p"
  S6            :: "histType => PrIds => stpred"
      "S6 rmhist p == S rmhist True False False clkB rpcA histB histB p"

  (* The invariant asserts that the system is always in one of S1 - S6, for every p *)
  ImpInv         :: "histType => PrIds => stpred"
      "ImpInv rmhist p == PRED (  S1 rmhist p | S2 rmhist p | S3 rmhist p
				| S4 rmhist p | S5 rmhist p | S6 rmhist p)"

  resbar        :: "histType => resType"        (* refinement mapping *)
      "resbar rmhist s p == 
                  (if (S1 rmhist p s | S2 rmhist p s)
                   then ires s p
                   else if S3 rmhist p s
                   then if rmhist s p = histA 
                        then ires s p else MemFailure
                   else if S4 rmhist p s
                   then if (rmhist s p = histB & ires s p = NotAResult)
                        then MemFailure else ires s p
                   else if S5 rmhist p s
                   then res (rmCh s p)
                   else if S6 rmhist p s
                   then if res (crCh s p) = RPCFailure
                        then MemFailure else res (crCh s p)
                   else NotAResult)" (* dummy value *)

rules
  (* the "base" variables: everything except resbar and hist (for any index) *)
  MI_base       "basevars (caller memCh!p,
			   (rtrner memCh!p, caller crCh!p, cst!p),
			   (rtrner crCh!p, caller rmCh!p, rst!p),
			   (mm!l, rtrner rmCh!p, ires!p))"

end

