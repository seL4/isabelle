(*
    File:        MemoryImplementation.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: MemoryImplementation
    Logic Image: TLA

    RPC-Memory example: Memory implementation
*)

MemoryImplementation = Memory + RPC + MemClerk + MIParameters +

types
  histType  = "(PrIds => histState) stfun"     (* the type of the history variable *)

consts
  (* the specification *)
     (* channel (external) *)
  memCh         :: "memChType"
     (* internal variables *)
  mem           :: "memType"
  resbar        :: "histType => resType"        (* defined by refinement mapping *)
  
  (* the state variables of the implementation *)
     (* channels *)
  (* same interface channel memCh *)
  crCh          :: "rpcSndChType"
  rmCh          :: "rpcRcvChType"
     (* internal variables *)
  (* identity refinement mapping for mem -- simply reused *)
  rst           :: "rpcStType"
  cst           :: "mClkStType"
  ires          :: "resType"
(* the history variable : not defined as a constant
  rmhist        :: "histType"
*)

  (* the environment action *)
  ENext         :: "PrIds => action"

  (* specification of the history variable *)
  HInit         :: "histType => PrIds => stpred"
  HNext         :: "histType => PrIds => action"
  HistP         :: "histType => PrIds => temporal"
  Hist          :: "histType => temporal"

  (* the implementation *)
  ImpInit        :: "PrIds => stpred"
  ImpNext        :: "PrIds => action"
  ImpLive        :: "PrIds => temporal"
  IPImp          :: "PrIds => temporal"
  Implementation :: "temporal"
  ImpInv         :: "histType => PrIds => stpred"

  (* tuples of state functions changed by the various components *)
  e             :: "PrIds => (bit * memArgType) stfun"
  c             :: "PrIds => (mClkState * (bit * Vals) * (bit * rpcArgType)) stfun"
  r             :: "PrIds => (rpcState * (bit * Vals) * (bit * memArgType)) stfun"
  m             :: "PrIds => ((bit * Vals) * Vals) stfun"

  (* the predicate S describes the states of the implementation.
     slight simplification: two "histState" parameters instead of a (one- or
     two-element) set. *)
  S             :: "histType => bool => bool => bool => mClkState => rpcState => histState => histState => PrIds => stpred"

  (* predicates S1 -- S6 define special instances of S *)
  S1            :: "histType => PrIds => stpred"
  S2            :: "histType => PrIds => stpred"
  S3            :: "histType => PrIds => stpred"
  S4            :: "histType => PrIds => stpred"
  S5            :: "histType => PrIds => stpred"
  S6            :: "histType => PrIds => stpred"

  (* auxiliary predicates *)
  MVOKBARF      :: "Vals => bool"
  MVOKBA        :: "Vals => bool"
  MVNROKBA      :: "Vals => bool"

rules
  MVOKBARF_def  "MVOKBARF v == (MemVal v) | (v = OK) | (v = BadArg) | (v = RPCFailure)"
  MVOKBA_def    "MVOKBA v   == (MemVal v) | (v = OK) | (v = BadArg)"
  MVNROKBA_def  "MVNROKBA v == (MemVal v) | (v = NotAResult) | (v = OK) | (v = BadArg)"

  (* the "base" variables: everything except resbar and hist (for any index) *)
  MI_base       "base_var <caller memCh @ p, rtrner memCh @ p, 
                           caller crCh @ p, rtrner crCh @ p,
                           caller rmCh @ p, rtrner rmCh @ p,
                           rst@p, cst@p, mem@l, ires@p>"

  (* Environment's next-state relation *)
  ENext_def     "ENext p == REX l. #(MemLoc l) .& Call memCh p (#(Inl (read,l)))"

  (* Specification of the history variable used in the proof *)
  HInit_def     "$(HInit rmhist p) .= ($(rmhist@p) .= #histA)"
  HNext_def     "HNext rmhist p == 
                   (rmhist@p)$ .=
                     (.if (MemReturn rmCh ires p .| RPCFail crCh rmCh rst p)
                      .then #histB
                      .else .if (MClkReply memCh crCh cst p)
                            .then #histA
                            .else $(rmhist@p))"
  HistP_def     "HistP rmhist p == 
                    Init($(HInit rmhist p))
                    .& [][HNext rmhist p]_<c p,r p,m p, rmhist@p>"
  Hist_def      "Hist rmhist == RALL p. HistP rmhist p"

  (* definitions of e,c,r,m *)
  e_def         "e p == caller memCh @ p"
  c_def         "c p == <cst@p, rtrner memCh @ p, caller crCh @ p>"
  r_def         "r p == <rst@p, rtrner crCh @ p, caller rmCh @ p>"
  m_def         "m p == <rtrner rmCh @ p, ires@p>"

  (* definition of the implementation (without the history variable) *)
  IPImp_def     "IPImp p ==    Init(.~ $(Calling memCh p)) .& [][ENext p]_(e p)
			           .& MClkIPSpec memCh crCh cst p
			           .& RPCIPSpec crCh rmCh rst p
			           .& RPSpec rmCh mem ires p 
			           .& (RALL l. #(MemLoc l) .-> MSpec rmCh mem ires l)"

  ImpInit_def   "$(ImpInit p) .= (   .~ $(Calling memCh p)    \
\		                  .& $(MClkInit crCh cst p)   \
\		                  .& $(RPCInit rmCh rst p)   \
\		                  .& $(PInit ires p))"

  ImpNext_def   "ImpNext p ==   [ENext p]_(e p) 
                             .& [MClkNext memCh crCh cst p]_(c p)
                             .& [RPCNext crCh rmCh rst p]_(r p) 
                             .& [RNext rmCh mem ires p]_(m p)"

  ImpLive_def  "ImpLive p ==   WF(MClkFwd memCh crCh cst p)_(c p) 
			    .& SF(MClkReply memCh crCh cst p)_(c p)
			    .& WF(RPCNext crCh rmCh rst p)_(r p) 
			    .& WF(RNext rmCh mem ires p)_(m p)
			    .& WF(MemReturn rmCh ires p)_(m p)"

  Impl_def   "Implementation ==    (RALL p. Init(.~ $(Calling memCh p)) .& [][ENext p]_(e p))
                                .& MClkISpec memCh crCh cst
                                .& RPCISpec crCh rmCh rst
                                .& IRSpec rmCh mem ires"

  ImpInv_def "$(ImpInv rmhist p) .= ($(S1 rmhist p) .| $(S2 rmhist p) .| $(S3 rmhist p) .| 
                                     $(S4 rmhist p) .| $(S5 rmhist p) .| $(S6 rmhist p))"

  (* Definition of predicate S.
     NB: The second conjunct of the definition in the paper is taken care of by
     the type definitions. The last conjunct is asserted separately as the memory
     invariant MemInv, proved in Memory.ML. *)
  S_def    "$(S rmhist ecalling ccalling rcalling cs rs hs1 hs2 p) .=
              (  ($(Calling memCh p) .= # ecalling)
              .& ($(Calling crCh p) .= # ccalling)
              .& (# ccalling .-> (arg[ $(crCh@p)] .= MClkRelayArg[ arg[$(memCh@p)] ]))
              .& ((.~ # ccalling .& ($(cst@p) .= # clkB)) .-> MVOKBARF[ res[$(crCh@p)] ])
              .& ($(Calling rmCh p) .= # rcalling)
              .& (# rcalling .-> (arg[ $(rmCh@p)] .= RPCRelayArg[ arg[$(crCh@p)] ]))
              .& (.~ # rcalling .-> ($(ires@p) .= # NotAResult))
              .& ((.~ # rcalling .& ($(rst@p) .= # rpcB)) .-> MVOKBA[ res[$(rmCh@p)] ])
              .& ($(cst@p) .= # cs)
              .& ($(rst@p) .= # rs)
              .& (($(rmhist@p) .= #hs1) .| ($(rmhist@p) .= #hs2))
              .& (MVNROKBA[ $(ires@p)]))"

  S1_def   "$(S1 rmhist p) .= $(S rmhist False False False clkA rpcA histA histA p)"
  S2_def   "$(S2 rmhist p) .= $(S rmhist True False False clkA rpcA histA histA p)"
  S3_def   "$(S3 rmhist p) .= $(S rmhist True True False clkB rpcA histA histB p)"
  S4_def   "$(S4 rmhist p) .= $(S rmhist True True True clkB rpcB histA histB p)"
  S5_def   "$(S5 rmhist p) .= $(S rmhist True True False clkB rpcB histB histB p)"
  S6_def   "$(S6 rmhist p) .= $(S rmhist True False False clkB rpcA histB histB p)"

  (* Definition of the refinement mapping resbar for result *)
  resbar_def   "$((resbar rmhist) @ p) .=
                  (.if ($(S1 rmhist p) .| $(S2 rmhist p))
                   .then $(ires@p)
                   .else .if $(S3 rmhist p)
                   .then .if $(rmhist@p) .= #histA 
                         .then $(ires@p) .else # MemFailure
                   .else .if $(S4 rmhist p)
                   .then .if ($(rmhist@p) .= #histB) .& ($(ires@p) .= # NotAResult)
                         .then #MemFailure .else $(ires@p)
                   .else .if $(S5 rmhist p)
                   .then res[$(rmCh@p)]
                   .else .if $(S6 rmhist p)
                   .then .if res[$(crCh@p)] .= #RPCFailure
                         .then #MemFailure .else res[$(crCh@p)]
                   .else #NotAResult)" (* dummy value *)

end

