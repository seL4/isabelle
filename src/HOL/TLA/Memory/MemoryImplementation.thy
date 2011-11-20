(*  Title:      HOL/TLA/Memory/MemoryImplementation.thy
    Author:     Stephan Merz, University of Munich
*)

header {* RPC-Memory example: Memory implementation *}

theory MemoryImplementation
imports Memory RPC MemClerk
begin

datatype histState = histA | histB

type_synonym histType = "(PrIds => histState) stfun"  (* the type of the history variable *)

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

definition
  (* auxiliary predicates *)
  MVOKBARF      :: "Vals => bool"
  where "MVOKBARF v <-> (v : MemVal) | (v = OK) | (v = BadArg) | (v = RPCFailure)"

definition
  MVOKBA        :: "Vals => bool"
  where "MVOKBA v <-> (v : MemVal) | (v = OK) | (v = BadArg)"

definition
  MVNROKBA      :: "Vals => bool"
  where "MVNROKBA v <-> (v : MemVal) | (v = NotAResult) | (v = OK) | (v = BadArg)"

definition
  (* tuples of state functions changed by the various components *)
  e             :: "PrIds => (bit * memOp) stfun"
  where "e p = PRED (caller memCh!p)"

definition
  c             :: "PrIds => (mClkState * (bit * Vals) * (bit * rpcOp)) stfun"
  where "c p = PRED (cst!p, rtrner memCh!p, caller crCh!p)"

definition
  r             :: "PrIds => (rpcState * (bit * Vals) * (bit * memOp)) stfun"
  where "r p = PRED (rst!p, rtrner crCh!p, caller rmCh!p)"

definition
  m             :: "PrIds => ((bit * Vals) * Vals) stfun"
  where "m p = PRED (rtrner rmCh!p, ires!p)"

definition
  (* the environment action *)
  ENext         :: "PrIds => action"
  where "ENext p = ACT (? l. #l : #MemLoc & Call memCh p #(read l))"


definition
  (* specification of the history variable *)
  HInit         :: "histType => PrIds => stpred"
  where "HInit rmhist p = PRED rmhist!p = #histA"

definition
  HNext         :: "histType => PrIds => action"
  where "HNext rmhist p = ACT (rmhist!p)$ =
                     (if (MemReturn rmCh ires p | RPCFail crCh rmCh rst p)
                      then #histB
                      else if (MClkReply memCh crCh cst p)
                           then #histA
                           else $(rmhist!p))"

definition
  HistP         :: "histType => PrIds => temporal"
  where "HistP rmhist p = (TEMP Init HInit rmhist p
                           & [][HNext rmhist p]_(c p,r p,m p, rmhist!p))"

definition
  Hist          :: "histType => temporal"
  where "Hist rmhist = TEMP (ALL p. HistP rmhist p)"

definition
  (* the implementation *)
  IPImp          :: "PrIds => temporal"
  where "IPImp p = (TEMP (  Init ~Calling memCh p & [][ENext p]_(e p)
                       & MClkIPSpec memCh crCh cst p
                       & RPCIPSpec crCh rmCh rst p
                       & RPSpec rmCh mm ires p
                       & (ALL l. #l : #MemLoc --> MSpec rmCh mm ires l)))"

definition
  ImpInit        :: "PrIds => stpred"
  where "ImpInit p = PRED (  ~Calling memCh p
                          & MClkInit crCh cst p
                          & RPCInit rmCh rst p
                          & PInit ires p)"

definition
  ImpNext        :: "PrIds => action"
  where "ImpNext p = (ACT  [ENext p]_(e p)
                       & [MClkNext memCh crCh cst p]_(c p)
                       & [RPCNext crCh rmCh rst p]_(r p)
                       & [RNext rmCh mm ires p]_(m p))"

definition
  ImpLive        :: "PrIds => temporal"
  where "ImpLive p = (TEMP  WF(MClkFwd memCh crCh cst p)_(c p)
                        & SF(MClkReply memCh crCh cst p)_(c p)
                        & WF(RPCNext crCh rmCh rst p)_(r p)
                        & WF(RNext rmCh mm ires p)_(m p)
                        & WF(MemReturn rmCh ires p)_(m p))"

definition
  Implementation :: "temporal"
  where "Implementation = (TEMP ( (ALL p. Init (~Calling memCh p) & [][ENext p]_(e p))
                               & MClkISpec memCh crCh cst
                               & RPCISpec crCh rmCh rst
                               & IRSpec rmCh mm ires))"

definition
  (* the predicate S describes the states of the implementation.
     slight simplification: two "histState" parameters instead of a
     (one- or two-element) set.
     NB: The second conjunct of the definition in the paper is taken care of by
     the type definitions. The last conjunct is asserted separately as the memory
     invariant MemInv, proved in Memory.thy. *)
  S :: "histType => bool => bool => bool => mClkState => rpcState => histState => histState => PrIds => stpred"
  where "S rmhist ecalling ccalling rcalling cs rs hs1 hs2 p = (PRED
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
              & MVNROKBA<ires!p>)"

definition
  (* predicates S1 -- S6 define special instances of S *)
  S1            :: "histType => PrIds => stpred"
  where "S1 rmhist p = S rmhist False False False clkA rpcA histA histA p"

definition
  S2            :: "histType => PrIds => stpred"
  where "S2 rmhist p = S rmhist True False False clkA rpcA histA histA p"

definition
  S3            :: "histType => PrIds => stpred"
  where "S3 rmhist p = S rmhist True True False clkB rpcA histA histB p"

definition
  S4            :: "histType => PrIds => stpred"
  where "S4 rmhist p = S rmhist True True True clkB rpcB histA histB p"

definition
  S5            :: "histType => PrIds => stpred"
  where "S5 rmhist p = S rmhist True True False clkB rpcB histB histB p"

definition
  S6            :: "histType => PrIds => stpred"
  where "S6 rmhist p = S rmhist True False False clkB rpcA histB histB p"

definition
  (* The invariant asserts that the system is always in one of S1 - S6, for every p *)
  ImpInv         :: "histType => PrIds => stpred"
  where "ImpInv rmhist p = (PRED (S1 rmhist p | S2 rmhist p | S3 rmhist p
                                | S4 rmhist p | S5 rmhist p | S6 rmhist p))"

definition
  resbar        :: "histType => resType"        (* refinement mapping *)
  where"resbar rmhist s p =
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

axiomatization where
  (* the "base" variables: everything except resbar and hist (for any index) *)
  MI_base:       "basevars (caller memCh!p,
                           (rtrner memCh!p, caller crCh!p, cst!p),
                           (rtrner crCh!p, caller rmCh!p, rst!p),
                           (mm!l, rtrner rmCh!p, ires!p))"

(*
    The main theorem is theorem "Implementation" at the end of this file,
    which shows that the composition of a reliable memory, an RPC component, and
    a memory clerk implements an unreliable memory. The files "MIsafe.thy" and
    "MIlive.thy" contain lower-level lemmas for the safety and liveness parts.

    Steps are (roughly) numbered as in the hand proof.
*)

(* --------------------------- automatic prover --------------------------- *)

declare if_weak_cong [cong del]

(* A more aggressive variant that tries to solve subgoals by assumption
   or contradiction during the simplification.
   THIS IS UNSAFE, BECAUSE IT DOESN'T RECORD THE CHOICES!!
   (but it can be a lot faster than the default setup)
*)
ML {*
  val config_fast_solver = Attrib.setup_config_bool @{binding fast_solver} (K false);
  val fast_solver = mk_solver "fast_solver" (fn ss =>
    if Config.get (Simplifier.the_context ss) config_fast_solver
    then assume_tac ORELSE' (etac notE)
    else K no_tac);
*}

declaration {* K (Simplifier.map_ss (fn ss => ss addSSolver fast_solver)) *}

ML {* val temp_elim = make_elim o temp_use *}



(****************************** The history variable ******************************)

section "History variable"

lemma HistoryLemma: "|- Init(ALL p. ImpInit p) & [](ALL p. ImpNext p)
         --> (EEX rmhist. Init(ALL p. HInit rmhist p)
                          & [](ALL p. [HNext rmhist p]_(c p, r p, m p, rmhist!p)))"
  apply clarsimp
  apply (rule historyI)
      apply assumption+
  apply (rule MI_base)
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm HInit_def}]) [] [] 1 *})
   apply (erule fun_cong)
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm HNext_def}])
    [@{thm busy_squareI}] [] 1 *})
  apply (erule fun_cong)
  done

lemma History: "|- Implementation --> (EEX rmhist. Hist rmhist)"
  apply clarsimp
  apply (rule HistoryLemma [temp_use, THEN eex_mono])
    prefer 3
    apply (force simp: Hist_def HistP_def Init_def all_box [try_rewrite]
      split_box_conj [try_rewrite])
   apply (auto simp: Implementation_def MClkISpec_def RPCISpec_def
     IRSpec_def MClkIPSpec_def RPCIPSpec_def RPSpec_def ImpInit_def
     Init_def ImpNext_def c_def r_def m_def all_box [temp_use] split_box_conj [temp_use])
  done

(******************************** The safety part *********************************)

section "The safety part"

(* ------------------------- Include lower-level lemmas ------------------------- *)

(* RPCFailure notin MemVals U {OK,BadArg} *)

lemma MVOKBAnotRF: "MVOKBA x ==> x ~= RPCFailure"
  apply (unfold MVOKBA_def)
  apply auto
  done

(* NotAResult notin MemVals U {OK,BadArg,RPCFailure} *)

lemma MVOKBARFnotNR: "MVOKBARF x ==> x ~= NotAResult"
  apply (unfold MVOKBARF_def)
  apply auto
  done

(* ================ Si's are mutually exclusive ================================ *)
(* Si and Sj are mutually exclusive for i # j. This helps to simplify the big
   conditional in the definition of resbar when doing the step-simulation proof.
   We prove a weaker result, which suffices for our purposes:
   Si implies (not Sj), for j<i.
*)

(* --- not used ---
lemma S1_excl: "|- S1 rmhist p --> S1 rmhist p & ~S2 rmhist p & ~S3 rmhist p &
    ~S4 rmhist p & ~S5 rmhist p & ~S6 rmhist p"
  by (auto simp: S_def S1_def S2_def S3_def S4_def S5_def S6_def)
*)

lemma S2_excl: "|- S2 rmhist p --> S2 rmhist p & ~S1 rmhist p"
  by (auto simp: S_def S1_def S2_def)

lemma S3_excl: "|- S3 rmhist p --> S3 rmhist p & ~S1 rmhist p & ~S2 rmhist p"
  by (auto simp: S_def S1_def S2_def S3_def)

lemma S4_excl: "|- S4 rmhist p --> S4 rmhist p & ~S1 rmhist p & ~S2 rmhist p & ~S3 rmhist p"
  by (auto simp: S_def S1_def S2_def S3_def S4_def)

lemma S5_excl: "|- S5 rmhist p --> S5 rmhist p & ~S1 rmhist p & ~S2 rmhist p
                         & ~S3 rmhist p & ~S4 rmhist p"
  by (auto simp: S_def S1_def S2_def S3_def S4_def S5_def)

lemma S6_excl: "|- S6 rmhist p --> S6 rmhist p & ~S1 rmhist p & ~S2 rmhist p
                         & ~S3 rmhist p & ~S4 rmhist p & ~S5 rmhist p"
  by (auto simp: S_def S1_def S2_def S3_def S4_def S5_def S6_def)


(* ==================== Lemmas about the environment ============================== *)

lemma Envbusy: "|- $(Calling memCh p) --> ~ENext p"
  by (auto simp: ENext_def Call_def)

(* ==================== Lemmas about the implementation's states ==================== *)

(* The following series of lemmas are used in establishing the implementation's
   next-state relation (Step 1.2 of the proof in the paper). For each state Si, we
   determine which component actions are possible and what state they result in.
*)

(* ------------------------------ State S1 ---------------------------------------- *)

lemma S1Env: "|- ENext p & $(S1 rmhist p) & unchanged (c p, r p, m p, rmhist!p)
         --> (S2 rmhist p)$"
  by (force simp: ENext_def Call_def c_def r_def m_def
    caller_def rtrner_def MVNROKBA_def S_def S1_def S2_def Calling_def)

lemma S1ClerkUnch: "|- [MClkNext memCh crCh cst p]_(c p) & $(S1 rmhist p) --> unchanged (c p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] dest!: MClkidle [temp_use] simp: S_def S1_def)

lemma S1RPCUnch: "|- [RPCNext crCh rmCh rst p]_(r p) & $(S1 rmhist p) --> unchanged (r p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] dest!: RPCidle [temp_use] simp: S_def S1_def)

lemma S1MemUnch: "|- [RNext rmCh mm ires p]_(m p) & $(S1 rmhist p) --> unchanged (m p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] dest!: Memoryidle [temp_use] simp: S_def S1_def)

lemma S1Hist: "|- [HNext rmhist p]_(c p,r p,m p,rmhist!p) & $(S1 rmhist p)
         --> unchanged (rmhist!p)"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm HNext_def}, @{thm S_def},
    @{thm S1_def}, @{thm MemReturn_def}, @{thm RPCFail_def}, @{thm MClkReply_def},
    @{thm Return_def}]) [] [temp_use @{thm squareE}] 1 *})


(* ------------------------------ State S2 ---------------------------------------- *)

lemma S2EnvUnch: "|- [ENext p]_(e p) & $(S2 rmhist p) --> unchanged (e p)"
  by (auto dest!: Envbusy [temp_use] simp: S_def S2_def)

lemma S2Clerk: "|- MClkNext memCh crCh cst p & $(S2 rmhist p) --> MClkFwd memCh crCh cst p"
  by (auto simp: MClkNext_def MClkRetry_def MClkReply_def S_def S2_def)

lemma S2Forward: "|- $(S2 rmhist p) & MClkFwd memCh crCh cst p
         & unchanged (e p, r p, m p, rmhist!p)
         --> (S3 rmhist p)$"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm MClkFwd_def},
    @{thm Call_def}, @{thm e_def}, @{thm r_def}, @{thm m_def}, @{thm caller_def},
    @{thm rtrner_def}, @{thm S_def}, @{thm S2_def}, @{thm S3_def}, @{thm Calling_def}]) [] [] 1 *})

lemma S2RPCUnch: "|- [RPCNext crCh rmCh rst p]_(r p) & $(S2 rmhist p) --> unchanged (r p)"
  by (auto simp: S_def S2_def dest!: RPCidle [temp_use])

lemma S2MemUnch: "|- [RNext rmCh mm ires p]_(m p) & $(S2 rmhist p) --> unchanged (m p)"
  by (auto simp: S_def S2_def dest!: Memoryidle [temp_use])

lemma S2Hist: "|- [HNext rmhist p]_(c p,r p,m p,rmhist!p) & $(S2 rmhist p)
         --> unchanged (rmhist!p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] simp: HNext_def MemReturn_def RPCFail_def
    MClkReply_def Return_def S_def S2_def)

(* ------------------------------ State S3 ---------------------------------------- *)

lemma S3EnvUnch: "|- [ENext p]_(e p) & $(S3 rmhist p) --> unchanged (e p)"
  by (auto dest!: Envbusy [temp_use] simp: S_def S3_def)

lemma S3ClerkUnch: "|- [MClkNext memCh crCh cst p]_(c p) & $(S3 rmhist p) --> unchanged (c p)"
  by (auto dest!: MClkbusy [temp_use] simp: square_def S_def S3_def)

lemma S3LegalRcvArg: "|- S3 rmhist p --> IsLegalRcvArg<arg<crCh!p>>"
  by (auto simp: IsLegalRcvArg_def MClkRelayArg_def S_def S3_def)

lemma S3RPC: "|- RPCNext crCh rmCh rst p & $(S3 rmhist p)
         --> RPCFwd crCh rmCh rst p | RPCFail crCh rmCh rst p"
  apply clarsimp
  apply (frule S3LegalRcvArg [action_use])
  apply (auto simp: RPCNext_def RPCReject_def RPCReply_def S_def S3_def)
  done

lemma S3Forward: "|- RPCFwd crCh rmCh rst p & HNext rmhist p & $(S3 rmhist p)
         & unchanged (e p, c p, m p)
         --> (S4 rmhist p)$ & unchanged (rmhist!p)"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm RPCFwd_def},
    @{thm HNext_def}, @{thm MemReturn_def}, @{thm RPCFail_def},
    @{thm MClkReply_def}, @{thm Return_def}, @{thm Call_def}, @{thm e_def},
    @{thm c_def}, @{thm m_def}, @{thm caller_def}, @{thm rtrner_def}, @{thm S_def},
    @{thm S3_def}, @{thm S4_def}, @{thm Calling_def}]) [] [] 1 *})

lemma S3Fail: "|- RPCFail crCh rmCh rst p & $(S3 rmhist p) & HNext rmhist p
         & unchanged (e p, c p, m p)
         --> (S6 rmhist p)$"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm HNext_def},
    @{thm RPCFail_def}, @{thm Return_def}, @{thm e_def}, @{thm c_def},
    @{thm m_def}, @{thm caller_def}, @{thm rtrner_def}, @{thm MVOKBARF_def},
    @{thm S_def}, @{thm S3_def}, @{thm S6_def}, @{thm Calling_def}]) [] [] 1 *})

lemma S3MemUnch: "|- [RNext rmCh mm ires p]_(m p) & $(S3 rmhist p) --> unchanged (m p)"
  by (auto simp: S_def S3_def dest!: Memoryidle [temp_use])

lemma S3Hist: "|- HNext rmhist p & $(S3 rmhist p) & unchanged (r p) --> unchanged (rmhist!p)"
  by (auto simp: HNext_def MemReturn_def RPCFail_def MClkReply_def
    Return_def r_def rtrner_def S_def S3_def Calling_def)

(* ------------------------------ State S4 ---------------------------------------- *)

lemma S4EnvUnch: "|- [ENext p]_(e p) & $(S4 rmhist p) --> unchanged (e p)"
  by (auto simp: S_def S4_def dest!: Envbusy [temp_use])

lemma S4ClerkUnch: "|- [MClkNext memCh crCh cst p]_(c p) & $(S4 rmhist p) --> unchanged (c p)"
  by (auto simp: S_def S4_def dest!: MClkbusy [temp_use])

lemma S4RPCUnch: "|- [RPCNext crCh rmCh rst p]_(r p) & $(S4 rmhist p) --> unchanged (r p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] dest!: RPCbusy [temp_use] simp: S_def S4_def)

lemma S4ReadInner: "|- ReadInner rmCh mm ires p l & $(S4 rmhist p) & unchanged (e p, c p, r p)
         & HNext rmhist p & $(MemInv mm l)
         --> (S4 rmhist p)$ & unchanged (rmhist!p)"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm ReadInner_def},
    @{thm GoodRead_def}, @{thm BadRead_def}, @{thm HNext_def}, @{thm MemReturn_def},
    @{thm RPCFail_def}, @{thm MClkReply_def}, @{thm Return_def}, @{thm e_def},
    @{thm c_def}, @{thm r_def}, @{thm rtrner_def}, @{thm caller_def},
    @{thm MVNROKBA_def}, @{thm S_def}, @{thm S4_def}, @{thm RdRequest_def},
    @{thm Calling_def}, @{thm MemInv_def}]) [] [] 1 *})

lemma S4Read: "|- Read rmCh mm ires p & $(S4 rmhist p) & unchanged (e p, c p, r p)
         & HNext rmhist p & (!l. $MemInv mm l)
         --> (S4 rmhist p)$ & unchanged (rmhist!p)"
  by (auto simp: Read_def dest!: S4ReadInner [temp_use])

lemma S4WriteInner: "|- WriteInner rmCh mm ires p l v & $(S4 rmhist p) & unchanged (e p, c p, r p)           & HNext rmhist p
         --> (S4 rmhist p)$ & unchanged (rmhist!p)"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm WriteInner_def},
    @{thm GoodWrite_def}, @{thm BadWrite_def}, @{thm HNext_def}, @{thm MemReturn_def},
    @{thm RPCFail_def}, @{thm MClkReply_def}, @{thm Return_def}, @{thm e_def},
    @{thm c_def}, @{thm r_def}, @{thm rtrner_def}, @{thm caller_def}, @{thm MVNROKBA_def},
    @{thm S_def}, @{thm S4_def}, @{thm WrRequest_def}, @{thm Calling_def}]) [] [] 1 *})

lemma S4Write: "|- Write rmCh mm ires p l & $(S4 rmhist p) & unchanged (e p, c p, r p)
         & (HNext rmhist p)
         --> (S4 rmhist p)$ & unchanged (rmhist!p)"
  by (auto simp: Write_def dest!: S4WriteInner [temp_use])

lemma WriteS4: "|- $ImpInv rmhist p & Write rmCh mm ires p l --> $S4 rmhist p"
  by (auto simp: Write_def WriteInner_def ImpInv_def
    WrRequest_def S_def S1_def S2_def S3_def S4_def S5_def S6_def)

lemma S4Return: "|- MemReturn rmCh ires p & $S4 rmhist p & unchanged (e p, c p, r p)
         & HNext rmhist p
         --> (S5 rmhist p)$"
  by (auto simp: HNext_def MemReturn_def Return_def e_def c_def r_def
    rtrner_def caller_def MVNROKBA_def MVOKBA_def S_def S4_def S5_def Calling_def)

lemma S4Hist: "|- HNext rmhist p & $S4 rmhist p & (m p)$ = $(m p) --> (rmhist!p)$ = $(rmhist!p)"
  by (auto simp: HNext_def MemReturn_def RPCFail_def MClkReply_def
    Return_def m_def rtrner_def S_def S4_def Calling_def)

(* ------------------------------ State S5 ---------------------------------------- *)

lemma S5EnvUnch: "|- [ENext p]_(e p) & $(S5 rmhist p) --> unchanged (e p)"
  by (auto simp: S_def S5_def dest!: Envbusy [temp_use])

lemma S5ClerkUnch: "|- [MClkNext memCh crCh cst p]_(c p) & $(S5 rmhist p) --> unchanged (c p)"
  by (auto simp: S_def S5_def dest!: MClkbusy [temp_use])

lemma S5RPC: "|- RPCNext crCh rmCh rst p & $(S5 rmhist p)
         --> RPCReply crCh rmCh rst p | RPCFail crCh rmCh rst p"
  by (auto simp: RPCNext_def RPCReject_def RPCFwd_def S_def S5_def)

lemma S5Reply: "|- RPCReply crCh rmCh rst p & $(S5 rmhist p) & unchanged (e p, c p, m p,rmhist!p)
       --> (S6 rmhist p)$"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm RPCReply_def},
    @{thm Return_def}, @{thm e_def}, @{thm c_def}, @{thm m_def}, @{thm MVOKBA_def},
    @{thm MVOKBARF_def}, @{thm caller_def}, @{thm rtrner_def}, @{thm S_def},
    @{thm S5_def}, @{thm S6_def}, @{thm Calling_def}]) [] [] 1 *})

lemma S5Fail: "|- RPCFail crCh rmCh rst p & $(S5 rmhist p) & unchanged (e p, c p, m p,rmhist!p)
         --> (S6 rmhist p)$"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm RPCFail_def},
    @{thm Return_def}, @{thm e_def}, @{thm c_def}, @{thm m_def},
    @{thm MVOKBARF_def}, @{thm caller_def}, @{thm rtrner_def},
    @{thm S_def}, @{thm S5_def}, @{thm S6_def}, @{thm Calling_def}]) [] [] 1 *})

lemma S5MemUnch: "|- [RNext rmCh mm ires p]_(m p) & $(S5 rmhist p) --> unchanged (m p)"
  by (auto simp: S_def S5_def dest!: Memoryidle [temp_use])

lemma S5Hist: "|- [HNext rmhist p]_(c p, r p, m p, rmhist!p) & $(S5 rmhist p)
         --> (rmhist!p)$ = $(rmhist!p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] simp: HNext_def MemReturn_def RPCFail_def
    MClkReply_def Return_def S_def S5_def)

(* ------------------------------ State S6 ---------------------------------------- *)

lemma S6EnvUnch: "|- [ENext p]_(e p) & $(S6 rmhist p) --> unchanged (e p)"
  by (auto simp: S_def S6_def dest!: Envbusy [temp_use])

lemma S6Clerk: "|- MClkNext memCh crCh cst p & $(S6 rmhist p)
         --> MClkRetry memCh crCh cst p | MClkReply memCh crCh cst p"
  by (auto simp: MClkNext_def MClkFwd_def S_def S6_def)

lemma S6Retry: "|- MClkRetry memCh crCh cst p & HNext rmhist p & $S6 rmhist p
         & unchanged (e p,r p,m p)
         --> (S3 rmhist p)$ & unchanged (rmhist!p)"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm HNext_def},
    @{thm MClkReply_def}, @{thm MClkRetry_def}, @{thm Call_def}, @{thm Return_def},
    @{thm e_def}, @{thm r_def}, @{thm m_def}, @{thm caller_def}, @{thm rtrner_def},
    @{thm S_def}, @{thm S6_def}, @{thm S3_def}, @{thm Calling_def}]) [] [] 1 *})

lemma S6Reply: "|- MClkReply memCh crCh cst p & HNext rmhist p & $S6 rmhist p
         & unchanged (e p,r p,m p)
         --> (S1 rmhist p)$"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm HNext_def},
    @{thm MemReturn_def}, @{thm RPCFail_def}, @{thm Return_def}, @{thm MClkReply_def},
    @{thm e_def}, @{thm r_def}, @{thm m_def}, @{thm caller_def}, @{thm rtrner_def},
    @{thm S_def}, @{thm S6_def}, @{thm S1_def}, @{thm Calling_def}]) [] [] 1 *})

lemma S6RPCUnch: "|- [RPCNext crCh rmCh rst p]_(r p) & $S6 rmhist p --> unchanged (r p)"
  by (auto simp: S_def S6_def dest!: RPCidle [temp_use])

lemma S6MemUnch: "|- [RNext rmCh mm ires p]_(m p) & $(S6 rmhist p) --> unchanged (m p)"
  by (auto simp: S_def S6_def dest!: Memoryidle [temp_use])

lemma S6Hist: "|- HNext rmhist p & $S6 rmhist p & (c p)$ = $(c p) --> (rmhist!p)$ = $(rmhist!p)"
  by (auto simp: HNext_def MClkReply_def Return_def c_def rtrner_def S_def S6_def Calling_def)


section "Correctness of predicate-action diagram"


(* ========== Step 1.1 ================================================= *)
(* The implementation's initial condition implies the state predicate S1 *)

lemma Step1_1: "|- ImpInit p & HInit rmhist p --> S1 rmhist p"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] simp: MVNROKBA_def
    MClkInit_def RPCInit_def PInit_def HInit_def ImpInit_def S_def S1_def)

(* ========== Step 1.2 ================================================== *)
(* Figure 16 is a predicate-action diagram for the implementation. *)

lemma Step1_2_1: "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p
         & ~unchanged (e p, c p, r p, m p, rmhist!p)  & $S1 rmhist p
         --> (S2 rmhist p)$ & ENext p & unchanged (c p, r p, m p)"
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm ImpNext_def}]) []
      (map temp_elim [@{thm S1ClerkUnch}, @{thm S1RPCUnch}, @{thm S1MemUnch}, @{thm S1Hist}]) 1 *})
   using [[fast_solver]]
   apply (auto elim!: squareE [temp_use] intro!: S1Env [temp_use])
  done

lemma Step1_2_2: "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p
         & ~unchanged (e p, c p, r p, m p, rmhist!p) & $S2 rmhist p
         --> (S3 rmhist p)$ & MClkFwd memCh crCh cst p
             & unchanged (e p, r p, m p, rmhist!p)"
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm ImpNext_def}]) []
    (map temp_elim [@{thm S2EnvUnch}, @{thm S2RPCUnch}, @{thm S2MemUnch}, @{thm S2Hist}]) 1 *})
   using [[fast_solver]]
   apply (auto elim!: squareE [temp_use] intro!: S2Clerk [temp_use] S2Forward [temp_use])
  done

lemma Step1_2_3: "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p
         & ~unchanged (e p, c p, r p, m p, rmhist!p) & $S3 rmhist p
         --> ((S4 rmhist p)$ & RPCFwd crCh rmCh rst p & unchanged (e p, c p, m p, rmhist!p))
             | ((S6 rmhist p)$ & RPCFail crCh rmCh rst p & unchanged (e p, c p, m p))"
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm ImpNext_def}]) []
    (map temp_elim [@{thm S3EnvUnch}, @{thm S3ClerkUnch}, @{thm S3MemUnch}]) 1 *})
  apply (tactic {* action_simp_tac @{simpset} []
    (@{thm squareE} :: map temp_elim [@{thm S3RPC}, @{thm S3Forward}, @{thm S3Fail}]) 1 *})
   apply (auto dest!: S3Hist [temp_use])
  done

lemma Step1_2_4: "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p
              & ~unchanged (e p, c p, r p, m p, rmhist!p)
              & $S4 rmhist p & (!l. $(MemInv mm l))
         --> ((S4 rmhist p)$ & Read rmCh mm ires p & unchanged (e p, c p, r p, rmhist!p))
             | ((S4 rmhist p)$ & (? l. Write rmCh mm ires p l) & unchanged (e p, c p, r p, rmhist!p))
             | ((S5 rmhist p)$ & MemReturn rmCh ires p & unchanged (e p, c p, r p))"
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm ImpNext_def}]) []
    (map temp_elim [@{thm S4EnvUnch}, @{thm S4ClerkUnch}, @{thm S4RPCUnch}]) 1 *})
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm RNext_def}]) []
    (@{thm squareE} :: map temp_elim [@{thm S4Read}, @{thm S4Write}, @{thm S4Return}]) 1 *})
  apply (auto dest!: S4Hist [temp_use])
  done

lemma Step1_2_5: "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p
              & ~unchanged (e p, c p, r p, m p, rmhist!p) & $S5 rmhist p
         --> ((S6 rmhist p)$ & RPCReply crCh rmCh rst p & unchanged (e p, c p, m p))
             | ((S6 rmhist p)$ & RPCFail crCh rmCh rst p & unchanged (e p, c p, m p))"
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm ImpNext_def}]) []
    (map temp_elim [@{thm S5EnvUnch}, @{thm S5ClerkUnch}, @{thm S5MemUnch}, @{thm S5Hist}]) 1 *})
  apply (tactic {* action_simp_tac @{simpset} [] [@{thm squareE}, temp_elim @{thm S5RPC}] 1 *})
   using [[fast_solver]]
   apply (auto elim!: squareE [temp_use] dest!: S5Reply [temp_use] S5Fail [temp_use])
  done

lemma Step1_2_6: "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p
              & ~unchanged (e p, c p, r p, m p, rmhist!p) & $S6 rmhist p
         --> ((S1 rmhist p)$ & MClkReply memCh crCh cst p & unchanged (e p, r p, m p))
             | ((S3 rmhist p)$ & MClkRetry memCh crCh cst p & unchanged (e p,r p,m p,rmhist!p))"
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm ImpNext_def}]) []
    (map temp_elim [@{thm S6EnvUnch}, @{thm S6RPCUnch}, @{thm S6MemUnch}]) 1 *})
  apply (tactic {* action_simp_tac @{simpset} []
    (@{thm squareE} :: map temp_elim [@{thm S6Clerk}, @{thm S6Retry}, @{thm S6Reply}]) 1 *})
     apply (auto dest: S6Hist [temp_use])
  done

(* --------------------------------------------------------------------------
   Step 1.3: S1 implies the barred initial condition.
*)

section "Initialization (Step 1.3)"

lemma Step1_3: "|- S1 rmhist p --> PInit (resbar rmhist) p"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm resbar_def},
    @{thm PInit_def}, @{thm S_def}, @{thm S1_def}]) [] [] 1 *})

(* ----------------------------------------------------------------------
   Step 1.4: Implementation's next-state relation simulates specification's
             next-state relation (with appropriate substitutions)
*)

section "Step simulation (Step 1.4)"

lemma Step1_4_1: "|- ENext p & $S1 rmhist p & (S2 rmhist p)$ & unchanged (c p, r p, m p)
         --> unchanged (rtrner memCh!p, resbar rmhist!p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] simp: c_def r_def m_def resbar_def)

lemma Step1_4_2: "|- MClkFwd memCh crCh cst p & $S2 rmhist p & (S3 rmhist p)$
         & unchanged (e p, r p, m p, rmhist!p)
         --> unchanged (rtrner memCh!p, resbar rmhist!p)"
  by (tactic {* action_simp_tac
    (@{simpset} addsimps [@{thm MClkFwd_def}, @{thm e_def}, @{thm r_def}, @{thm m_def},
    @{thm resbar_def}, @{thm S_def}, @{thm S2_def}, @{thm S3_def}]) [] [] 1 *})

lemma Step1_4_3a: "|- RPCFwd crCh rmCh rst p & $S3 rmhist p & (S4 rmhist p)$
         & unchanged (e p, c p, m p, rmhist!p)
         --> unchanged (rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (drule S3_excl [temp_use] S4_excl [temp_use])+
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm e_def},
    @{thm c_def}, @{thm m_def}, @{thm resbar_def}, @{thm S_def}, @{thm S3_def}]) [] [] 1 *})
  done

lemma Step1_4_3b: "|- RPCFail crCh rmCh rst p & $S3 rmhist p & (S6 rmhist p)$
         & unchanged (e p, c p, m p)
         --> MemFail memCh (resbar rmhist) p"
  apply clarsimp
  apply (drule S6_excl [temp_use])
  apply (auto simp: RPCFail_def MemFail_def e_def c_def m_def resbar_def)
    apply (force simp: S3_def S_def)
   apply (auto simp: Return_def)
  done

lemma Step1_4_4a1: "|- $S4 rmhist p & (S4 rmhist p)$ & ReadInner rmCh mm ires p l
         & unchanged (e p, c p, r p, rmhist!p) & $MemInv mm l
         --> ReadInner memCh mm (resbar rmhist) p l"
  apply clarsimp
  apply (drule S4_excl [temp_use])+
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm ReadInner_def},
    @{thm GoodRead_def}, @{thm BadRead_def}, @{thm e_def}, @{thm c_def}, @{thm m_def}]) [] [] 1 *})
     apply (auto simp: resbar_def)
       apply (tactic {* ALLGOALS (action_simp_tac
                (@{simpset} addsimps [@{thm RPCRelayArg_def}, @{thm MClkRelayArg_def},
                  @{thm S_def}, @{thm S4_def}, @{thm RdRequest_def}, @{thm MemInv_def}])
                [] [@{thm impE}, @{thm MemValNotAResultE}]) *})
  done

lemma Step1_4_4a: "|- Read rmCh mm ires p & $S4 rmhist p & (S4 rmhist p)$
         & unchanged (e p, c p, r p, rmhist!p) & (!l. $(MemInv mm l))
         --> Read memCh mm (resbar rmhist) p"
  by (force simp: Read_def elim!: Step1_4_4a1 [temp_use])

lemma Step1_4_4b1: "|- $S4 rmhist p & (S4 rmhist p)$ & WriteInner rmCh mm ires p l v
         & unchanged (e p, c p, r p, rmhist!p)
         --> WriteInner memCh mm (resbar rmhist) p l v"
  apply clarsimp
  apply (drule S4_excl [temp_use])+
  apply (tactic {* action_simp_tac (@{simpset} addsimps
    [@{thm WriteInner_def}, @{thm GoodWrite_def}, @{thm BadWrite_def}, @{thm e_def},
    @{thm c_def}, @{thm m_def}]) [] [] 1 *})
     apply (auto simp: resbar_def)
    apply (tactic {* ALLGOALS (action_simp_tac (@{simpset} addsimps
      [@{thm RPCRelayArg_def}, @{thm MClkRelayArg_def}, @{thm S_def},
      @{thm S4_def}, @{thm WrRequest_def}]) [] []) *})
  done

lemma Step1_4_4b: "|- Write rmCh mm ires p l & $S4 rmhist p & (S4 rmhist p)$
         & unchanged (e p, c p, r p, rmhist!p)
         --> Write memCh mm (resbar rmhist) p l"
  by (force simp: Write_def elim!: Step1_4_4b1 [temp_use])

lemma Step1_4_4c: "|- MemReturn rmCh ires p & $S4 rmhist p & (S5 rmhist p)$
         & unchanged (e p, c p, r p)
         --> unchanged (rtrner memCh!p, resbar rmhist!p)"
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm e_def},
    @{thm c_def}, @{thm r_def}, @{thm resbar_def}]) [] [] 1 *})
  apply (drule S4_excl [temp_use] S5_excl [temp_use])+
  using [[fast_solver]]
  apply (auto elim!: squareE [temp_use] simp: MemReturn_def Return_def)
  done

lemma Step1_4_5a: "|- RPCReply crCh rmCh rst p & $S5 rmhist p & (S6 rmhist p)$
         & unchanged (e p, c p, m p)
         --> unchanged (rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (drule S5_excl [temp_use] S6_excl [temp_use])+
  apply (auto simp: e_def c_def m_def resbar_def)
   apply (auto simp: RPCReply_def Return_def S5_def S_def dest!: MVOKBAnotRF [temp_use])
  done

lemma Step1_4_5b: "|- RPCFail crCh rmCh rst p & $S5 rmhist p & (S6 rmhist p)$
         & unchanged (e p, c p, m p)
         --> MemFail memCh (resbar rmhist) p"
  apply clarsimp
  apply (drule S6_excl [temp_use])
  apply (auto simp: e_def c_def m_def RPCFail_def Return_def MemFail_def resbar_def)
   apply (auto simp: S5_def S_def)
  done

lemma Step1_4_6a: "|- MClkReply memCh crCh cst p & $S6 rmhist p & (S1 rmhist p)$
         & unchanged (e p, r p, m p)
         --> MemReturn memCh (resbar rmhist) p"
  apply clarsimp
  apply (drule S6_excl [temp_use])+
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm e_def},
    @{thm r_def}, @{thm m_def}, @{thm MClkReply_def}, @{thm MemReturn_def},
    @{thm Return_def}, @{thm resbar_def}]) [] [] 1 *})
    apply simp_all (* simplify if-then-else *)
    apply (tactic {* ALLGOALS (action_simp_tac (@{simpset} addsimps
      [@{thm MClkReplyVal_def}, @{thm S6_def}, @{thm S_def}]) [] [@{thm MVOKBARFnotNR}]) *})
  done

lemma Step1_4_6b: "|- MClkRetry memCh crCh cst p & $S6 rmhist p & (S3 rmhist p)$
         & unchanged (e p, r p, m p, rmhist!p)
         --> MemFail memCh (resbar rmhist) p"
  apply clarsimp
  apply (drule S3_excl [temp_use])+
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm e_def}, @{thm r_def},
    @{thm m_def}, @{thm MClkRetry_def}, @{thm MemFail_def}, @{thm resbar_def}]) [] [] 1 *})
   apply (auto simp: S6_def S_def)
  done

lemma S_lemma: "|- unchanged (e p, c p, r p, m p, rmhist!p)
         --> unchanged (S rmhist ec cc rc cs rs hs1 hs2 p)"
  by (auto simp: e_def c_def r_def m_def caller_def rtrner_def S_def Calling_def)

lemma Step1_4_7H: "|- unchanged (e p, c p, r p, m p, rmhist!p)
         --> unchanged (rtrner memCh!p, S1 rmhist p, S2 rmhist p, S3 rmhist p,
                        S4 rmhist p, S5 rmhist p, S6 rmhist p)"
  apply clarsimp
  apply (rule conjI)
   apply (force simp: c_def)
  apply (force simp: S1_def S2_def S3_def S4_def S5_def S6_def intro!: S_lemma [temp_use])
  done

lemma Step1_4_7: "|- unchanged (e p, c p, r p, m p, rmhist!p)
         --> unchanged (rtrner memCh!p, resbar rmhist!p, S1 rmhist p, S2 rmhist p,
                        S3 rmhist p, S4 rmhist p, S5 rmhist p, S6 rmhist p)"
  apply (rule actionI)
  apply (unfold action_rews)
  apply (rule impI)
  apply (frule Step1_4_7H [temp_use])
  apply (auto simp: e_def c_def r_def m_def rtrner_def resbar_def)
  done

(* Frequently needed abbreviation: distinguish between idling and non-idling
   steps of the implementation, and try to solve the idling case by simplification
*)
ML {*
fun split_idle_tac ctxt =
  SELECT_GOAL
   (TRY (rtac @{thm actionI} 1) THEN
    Induct_Tacs.case_tac ctxt "(s,t) |= unchanged (e p, c p, r p, m p, rmhist!p)" 1 THEN
    rewrite_goals_tac @{thms action_rews} THEN
    forward_tac [temp_use @{thm Step1_4_7}] 1 THEN
    asm_full_simp_tac (simpset_of ctxt) 1);
*}

method_setup split_idle = {*
  Method.sections (Simplifier.simp_modifiers @ Splitter.split_modifiers)
    >> (K (SIMPLE_METHOD' o split_idle_tac))
*}

(* ----------------------------------------------------------------------
   Combine steps 1.2 and 1.4 to prove that the implementation satisfies
   the specification's next-state relation.
*)

(* Steps that leave all variables unchanged are safe, so I may assume
   that some variable changes in the proof that a step is safe. *)
lemma unchanged_safe: "|- (~unchanged (e p, c p, r p, m p, rmhist!p)
             --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p))
         --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply (split_idle simp: square_def)
  apply force
  done
(* turn into (unsafe, looping!) introduction rule *)
lemmas unchanged_safeI = impI [THEN unchanged_safe [action_use]]

lemma S1safe: "|- $S1 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (rule unchanged_safeI)
  apply (rule idle_squareI)
  apply (auto dest!: Step1_2_1 [temp_use] Step1_4_1 [temp_use])
  done

lemma S2safe: "|- $S2 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (rule unchanged_safeI)
  apply (rule idle_squareI)
  apply (auto dest!: Step1_2_2 [temp_use] Step1_4_2 [temp_use])
  done

lemma S3safe: "|- $S3 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (rule unchanged_safeI)
  apply (auto dest!: Step1_2_3 [temp_use])
  apply (auto simp: square_def UNext_def dest!: Step1_4_3a [temp_use] Step1_4_3b [temp_use])
  done

lemma S4safe: "|- $S4 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         & (!l. $(MemInv mm l))
         --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (rule unchanged_safeI)
  apply (auto dest!: Step1_2_4 [temp_use])
     apply (auto simp: square_def UNext_def RNext_def
       dest!: Step1_4_4a [temp_use] Step1_4_4b [temp_use] Step1_4_4c [temp_use])
  done

lemma S5safe: "|- $S5 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (rule unchanged_safeI)
  apply (auto dest!: Step1_2_5 [temp_use])
  apply (auto simp: square_def UNext_def dest!: Step1_4_5a [temp_use] Step1_4_5b [temp_use])
  done

lemma S6safe: "|- $S6 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (rule unchanged_safeI)
  apply (auto dest!: Step1_2_6 [temp_use])
    apply (auto simp: square_def UNext_def RNext_def
      dest!: Step1_4_6a [temp_use] Step1_4_6b [temp_use])
  done

(* ----------------------------------------------------------------------
   Step 1.5: Temporal refinement proof, based on previous steps.
*)

section "The liveness part"

(* Liveness assertions for the different implementation states, based on the
   fairness conditions. Prove subgoals of WF1 / SF1 rules as separate lemmas
   for readability. Reuse action proofs from safety part.
*)

(* ------------------------------ State S1 ------------------------------ *)

lemma S1_successors: "|- $S1 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> (S1 rmhist p)$ | (S2 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_1 [temp_use])
  done

(* Show that the implementation can satisfy the high-level fairness requirements
   by entering the state S1 infinitely often.
*)

lemma S1_RNextdisabled: "|- S1 rmhist p -->
         ~Enabled (<RNext memCh mm (resbar rmhist) p>_(rtrner memCh!p, resbar rmhist!p))"
  apply (tactic {* action_simp_tac (@{simpset} addsimps [@{thm angle_def},
    @{thm S_def}, @{thm S1_def}]) [notI] [@{thm enabledE}, temp_elim @{thm Memoryidle}] 1 *})
  apply force
  done

lemma S1_Returndisabled: "|- S1 rmhist p -->
         ~Enabled (<MemReturn memCh (resbar rmhist) p>_(rtrner memCh!p, resbar rmhist!p))"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm angle_def}, @{thm MemReturn_def},
    @{thm Return_def}, @{thm S_def}, @{thm S1_def}]) [notI] [@{thm enabledE}] 1 *})

lemma RNext_fair: "|- []<>S1 rmhist p
         --> WF(RNext memCh mm (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)"
  by (auto simp: WF_alt [try_rewrite] intro!: S1_RNextdisabled [temp_use]
    elim!: STL4E [temp_use] DmdImplE [temp_use])

lemma Return_fair: "|- []<>S1 rmhist p
         --> WF(MemReturn memCh (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)"
  by (auto simp: WF_alt [try_rewrite]
    intro!: S1_Returndisabled [temp_use] elim!: STL4E [temp_use] DmdImplE [temp_use])

(* ------------------------------ State S2 ------------------------------ *)

lemma S2_successors: "|- $S2 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> (S2 rmhist p)$ | (S3 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_2 [temp_use])
  done

lemma S2MClkFwd_successors: "|- ($S2 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         & <MClkFwd memCh crCh cst p>_(c p)
         --> (S3 rmhist p)$"
  by (auto simp: angle_def dest!: Step1_2_2 [temp_use])

lemma S2MClkFwd_enabled: "|- $S2 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> $Enabled (<MClkFwd memCh crCh cst p>_(c p))"
  apply (auto simp: c_def intro!: MClkFwd_ch_enabled [temp_use] MClkFwd_enabled [temp_use])
     apply (cut_tac MI_base)
     apply (blast dest: base_pair)
    apply (simp_all add: S_def S2_def)
  done

lemma S2_live: "|- [](ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         & WF(MClkFwd memCh crCh cst p)_(c p)
         --> (S2 rmhist p ~> S3 rmhist p)"
  by (rule WF1 S2_successors S2MClkFwd_successors S2MClkFwd_enabled)+

(* ------------------------------ State S3 ------------------------------ *)

lemma S3_successors: "|- $S3 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> (S3 rmhist p)$ | (S4 rmhist p | S6 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_3 [temp_use])
  done

lemma S3RPC_successors: "|- ($S3 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         & <RPCNext crCh rmCh rst p>_(r p)
         --> (S4 rmhist p | S6 rmhist p)$"
  apply (auto simp: angle_def dest!: Step1_2_3 [temp_use])
  done

lemma S3RPC_enabled: "|- $S3 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> $Enabled (<RPCNext crCh rmCh rst p>_(r p))"
  apply (auto simp: r_def intro!: RPCFail_Next_enabled [temp_use] RPCFail_enabled [temp_use])
    apply (cut_tac MI_base)
    apply (blast dest: base_pair)
   apply (simp_all add: S_def S3_def)
  done

lemma S3_live: "|- [](ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         & WF(RPCNext crCh rmCh rst p)_(r p)
         --> (S3 rmhist p ~> S4 rmhist p | S6 rmhist p)"
  by (rule WF1 S3_successors S3RPC_successors S3RPC_enabled)+

(* ------------- State S4 -------------------------------------------------- *)

lemma S4_successors: "|- $S4 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
        & (ALL l. $MemInv mm l)
        --> (S4 rmhist p)$ | (S5 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_4 [temp_use])
  done

(* --------- State S4a: S4 /\ (ires p = NotAResult) ------------------------ *)

lemma S4a_successors: "|- $(S4 rmhist p & ires!p = #NotAResult)
         & ImpNext p & [HNext rmhist p]_(c p,r p,m p,rmhist!p) & (ALL l. $MemInv mm l)
         --> (S4 rmhist p & ires!p = #NotAResult)$
             | ((S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_4 [temp_use])
  done

lemma S4aRNext_successors: "|- ($(S4 rmhist p & ires!p = #NotAResult)
         & ImpNext p & [HNext rmhist p]_(c p,r p,m p,rmhist!p) & (ALL l. $MemInv mm l))
         & <RNext rmCh mm ires p>_(m p)
         --> ((S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p)$"
  by (auto simp: angle_def
    dest!: Step1_2_4 [temp_use] ReadResult [temp_use] WriteResult [temp_use])

lemma S4aRNext_enabled: "|- $(S4 rmhist p & ires!p = #NotAResult)
         & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) & (ALL l. $MemInv mm l)
         --> $Enabled (<RNext rmCh mm ires p>_(m p))"
  apply (auto simp: m_def intro!: RNext_enabled [temp_use])
   apply (cut_tac MI_base)
   apply (blast dest: base_pair)
  apply (simp add: S_def S4_def)
  done

lemma S4a_live: "|- [](ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         & (ALL l. $MemInv mm l)) & WF(RNext rmCh mm ires p)_(m p)
         --> (S4 rmhist p & ires!p = #NotAResult
              ~> (S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p)"
  by (rule WF1 S4a_successors S4aRNext_successors S4aRNext_enabled)+

(* ---------- State S4b: S4 /\ (ires p # NotAResult) --------------------------- *)

lemma S4b_successors: "|- $(S4 rmhist p & ires!p ~= #NotAResult)
         & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) & (ALL l. $MemInv mm l)
         --> (S4 rmhist p & ires!p ~= #NotAResult)$ | (S5 rmhist p)$"
  apply (split_idle simp: m_def)
  apply (auto dest!: WriteResult [temp_use] Step1_2_4 [temp_use] ReadResult [temp_use])
  done

lemma S4bReturn_successors: "|- ($(S4 rmhist p & ires!p ~= #NotAResult)
         & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         & (ALL l. $MemInv mm l)) & <MemReturn rmCh ires p>_(m p)
         --> (S5 rmhist p)$"
  by (force simp: angle_def dest!: Step1_2_4 [temp_use] dest: ReturnNotReadWrite [temp_use])

lemma S4bReturn_enabled: "|- $(S4 rmhist p & ires!p ~= #NotAResult)
         & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         & (ALL l. $MemInv mm l)
         --> $Enabled (<MemReturn rmCh ires p>_(m p))"
  apply (auto simp: m_def intro!: MemReturn_enabled [temp_use])
   apply (cut_tac MI_base)
   apply (blast dest: base_pair)
  apply (simp add: S_def S4_def)
  done

lemma S4b_live: "|- [](ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) & (!l. $MemInv mm l))
         & WF(MemReturn rmCh ires p)_(m p)
         --> (S4 rmhist p & ires!p ~= #NotAResult ~> S5 rmhist p)"
  by (rule WF1 S4b_successors S4bReturn_successors S4bReturn_enabled)+

(* ------------------------------ State S5 ------------------------------ *)

lemma S5_successors: "|- $S5 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> (S5 rmhist p)$ | (S6 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_5 [temp_use])
  done

lemma S5RPC_successors: "|- ($S5 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         & <RPCNext crCh rmCh rst p>_(r p)
         --> (S6 rmhist p)$"
  by (auto simp: angle_def dest!: Step1_2_5 [temp_use])

lemma S5RPC_enabled: "|- $S5 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> $Enabled (<RPCNext crCh rmCh rst p>_(r p))"
  apply (auto simp: r_def intro!: RPCFail_Next_enabled [temp_use] RPCFail_enabled [temp_use])
    apply (cut_tac MI_base)
    apply (blast dest: base_pair)
   apply (simp_all add: S_def S5_def)
  done

lemma S5_live: "|- [](ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         & WF(RPCNext crCh rmCh rst p)_(r p)
         --> (S5 rmhist p ~> S6 rmhist p)"
  by (rule WF1 S5_successors S5RPC_successors S5RPC_enabled)+

(* ------------------------------ State S6 ------------------------------ *)

lemma S6_successors: "|- $S6 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         --> (S1 rmhist p)$ | (S3 rmhist p)$ | (S6 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_6 [temp_use])
  done

lemma S6MClkReply_successors:
  "|- ($S6 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         & <MClkReply memCh crCh cst p>_(c p)
         --> (S1 rmhist p)$"
  by (auto simp: angle_def dest!: Step1_2_6 [temp_use] MClkReplyNotRetry [temp_use])

lemma MClkReplyS6:
  "|- $ImpInv rmhist p & <MClkReply memCh crCh cst p>_(c p) --> $S6 rmhist p"
  by (tactic {* action_simp_tac (@{simpset} addsimps [@{thm angle_def},
    @{thm MClkReply_def}, @{thm Return_def}, @{thm ImpInv_def}, @{thm S_def},
    @{thm S1_def}, @{thm S2_def}, @{thm S3_def}, @{thm S4_def}, @{thm S5_def}]) [] [] 1 *})

lemma S6MClkReply_enabled: "|- S6 rmhist p --> Enabled (<MClkReply memCh crCh cst p>_(c p))"
  apply (auto simp: c_def intro!: MClkReply_enabled [temp_use])
     apply (cut_tac MI_base)
     apply (blast dest: base_pair)
    apply (tactic {* ALLGOALS (action_simp_tac (@{simpset}
      addsimps [@{thm S_def}, @{thm S6_def}]) [] []) *})
  done

lemma S6_live: "|- [](ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) & $(ImpInv rmhist p))
         & SF(MClkReply memCh crCh cst p)_(c p) & []<>(S6 rmhist p)
         --> []<>(S1 rmhist p)"
  apply clarsimp
  apply (subgoal_tac "sigma |= []<> (<MClkReply memCh crCh cst p>_ (c p))")
   apply (erule InfiniteEnsures)
    apply assumption
   apply (tactic {* action_simp_tac @{simpset} []
     (map temp_elim [@{thm MClkReplyS6}, @{thm S6MClkReply_successors}]) 1 *})
  apply (auto simp: SF_def)
  apply (erule contrapos_np)
  apply (auto intro!: S6MClkReply_enabled [temp_use] elim!: STL4E [temp_use] DmdImplE [temp_use])
  done

(* --------------- aggregate leadsto properties----------------------------- *)

lemma S5S6LeadstoS6: "sigma |= S5 rmhist p ~> S6 rmhist p
      ==> sigma |= (S5 rmhist p | S6 rmhist p) ~> S6 rmhist p"
  by (auto intro!: LatticeDisjunctionIntro [temp_use] LatticeReflexivity [temp_use])

lemma S4bS5S6LeadstoS6: "[| sigma |= S4 rmhist p & ires!p ~= #NotAResult ~> S5 rmhist p;
         sigma |= S5 rmhist p ~> S6 rmhist p |]
      ==> sigma |= (S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p | S6 rmhist p
                    ~> S6 rmhist p"
  by (auto intro!: LatticeDisjunctionIntro [temp_use]
    S5S6LeadstoS6 [temp_use] intro: LatticeTransitivity [temp_use])

lemma S4S5S6LeadstoS6: "[| sigma |= S4 rmhist p & ires!p = #NotAResult
                  ~> (S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p;
         sigma |= S4 rmhist p & ires!p ~= #NotAResult ~> S5 rmhist p;
         sigma |= S5 rmhist p ~> S6 rmhist p |]
      ==> sigma |= S4 rmhist p | S5 rmhist p | S6 rmhist p ~> S6 rmhist p"
  apply (subgoal_tac "sigma |= (S4 rmhist p & ires!p = #NotAResult) |
    (S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p | S6 rmhist p ~> S6 rmhist p")
   apply (erule_tac G = "PRED ((S4 rmhist p & ires!p = #NotAResult) |
     (S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p | S6 rmhist p)" in
     LatticeTransitivity [temp_use])
   apply (force simp: Init_defs intro!: ImplLeadsto_gen [temp_use] necT [temp_use])
  apply (rule LatticeDisjunctionIntro [temp_use])
   apply (erule LatticeTransitivity [temp_use])
   apply (erule LatticeTriangle2 [temp_use])
   apply assumption
  apply (auto intro!: S4bS5S6LeadstoS6 [temp_use])
  done

lemma S3S4S5S6LeadstoS6: "[| sigma |= S3 rmhist p ~> S4 rmhist p | S6 rmhist p;
         sigma |= S4 rmhist p & ires!p = #NotAResult
                  ~> (S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p;
         sigma |= S4 rmhist p & ires!p ~= #NotAResult ~> S5 rmhist p;
         sigma |= S5 rmhist p ~> S6 rmhist p |]
      ==> sigma |= S3 rmhist p | S4 rmhist p | S5 rmhist p | S6 rmhist p ~> S6 rmhist p"
  apply (rule LatticeDisjunctionIntro [temp_use])
   apply (erule LatticeTriangle2 [temp_use])
   apply (rule S4S5S6LeadstoS6 [THEN LatticeTransitivity [temp_use]])
      apply (auto intro!: S4S5S6LeadstoS6 [temp_use] necT [temp_use]
        intro: ImplLeadsto_gen [temp_use] simp: Init_defs)
  done

lemma S2S3S4S5S6LeadstoS6: "[| sigma |= S2 rmhist p ~> S3 rmhist p;
         sigma |= S3 rmhist p ~> S4 rmhist p | S6 rmhist p;
         sigma |= S4 rmhist p & ires!p = #NotAResult
                  ~> S4 rmhist p & ires!p ~= #NotAResult | S5 rmhist p;
         sigma |= S4 rmhist p & ires!p ~= #NotAResult ~> S5 rmhist p;
         sigma |= S5 rmhist p ~> S6 rmhist p |]
      ==> sigma |= S2 rmhist p | S3 rmhist p | S4 rmhist p | S5 rmhist p | S6 rmhist p
                   ~> S6 rmhist p"
  apply (rule LatticeDisjunctionIntro [temp_use])
   apply (rule LatticeTransitivity [temp_use])
    prefer 2 apply assumption
   apply (rule S3S4S5S6LeadstoS6 [THEN LatticeTransitivity [temp_use]])
       apply (auto intro!: S3S4S5S6LeadstoS6 [temp_use] necT [temp_use]
         intro: ImplLeadsto_gen [temp_use] simp: Init_defs)
  done

lemma NotS1LeadstoS6: "[| sigma |= []ImpInv rmhist p;
         sigma |= S2 rmhist p ~> S3 rmhist p;
         sigma |= S3 rmhist p ~> S4 rmhist p | S6 rmhist p;
         sigma |= S4 rmhist p & ires!p = #NotAResult
                  ~> S4 rmhist p & ires!p ~= #NotAResult | S5 rmhist p;
         sigma |= S4 rmhist p & ires!p ~= #NotAResult ~> S5 rmhist p;
         sigma |= S5 rmhist p ~> S6 rmhist p |]
      ==> sigma |= ~S1 rmhist p ~> S6 rmhist p"
  apply (rule S2S3S4S5S6LeadstoS6 [THEN LatticeTransitivity [temp_use]])
       apply assumption+
  apply (erule INV_leadsto [temp_use])
  apply (rule ImplLeadsto_gen [temp_use])
  apply (rule necT [temp_use])
  apply (auto simp: ImpInv_def Init_defs intro!: necT [temp_use])
  done

lemma S1Infinite: "[| sigma |= ~S1 rmhist p ~> S6 rmhist p;
         sigma |= []<>S6 rmhist p --> []<>S1 rmhist p |]
      ==> sigma |= []<>S1 rmhist p"
  apply (rule classical)
  apply (tactic {* asm_lr_simp_tac (@{simpset} addsimps
    [temp_use @{thm NotBox}, temp_rewrite @{thm NotDmd}]) 1 *})
  apply (auto elim!: leadsto_infinite [temp_use] mp dest!: DBImplBD [temp_use])
  done

section "Refinement proof (step 1.5)"

(* Prove invariants of the implementation:
   a. memory invariant
   b. "implementation invariant": always in states S1,...,S6
*)
lemma Step1_5_1a: "|- IPImp p --> (ALL l. []$MemInv mm l)"
  by (auto simp: IPImp_def box_stp_act [temp_use] intro!: MemoryInvariantAll [temp_use])

lemma Step1_5_1b: "|- Init(ImpInit p & HInit rmhist p) & [](ImpNext p)
         & [][HNext rmhist p]_(c p, r p, m p, rmhist!p) & [](ALL l. $MemInv mm l)
         --> []ImpInv rmhist p"
  apply invariant
   apply (auto simp: Init_def ImpInv_def box_stp_act [temp_use]
     dest!: Step1_1 [temp_use] dest: S1_successors [temp_use] S2_successors [temp_use]
     S3_successors [temp_use] S4_successors [temp_use] S5_successors [temp_use]
     S6_successors [temp_use])
  done

(*** Initialization ***)
lemma Step1_5_2a: "|- Init(ImpInit p & HInit rmhist p) --> Init(PInit (resbar rmhist) p)"
  by (auto simp: Init_def intro!: Step1_1 [temp_use] Step1_3  [temp_use])

(*** step simulation ***)
lemma Step1_5_2b: "|- [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p)
         & $ImpInv rmhist p & (!l. $MemInv mm l))
         --> [][UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  by (auto simp: ImpInv_def elim!: STL4E [temp_use]
    dest!: S1safe [temp_use] S2safe [temp_use] S3safe [temp_use] S4safe [temp_use]
    S5safe [temp_use] S6safe [temp_use])

(*** Liveness ***)
lemma GoodImpl: "|- IPImp p & HistP rmhist p
         -->   Init(ImpInit p & HInit rmhist p)
             & [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p))
             & [](ALL l. $MemInv mm l) & []($ImpInv rmhist p)
             & ImpLive p"
  apply clarsimp
    apply (subgoal_tac "sigma |= Init (ImpInit p & HInit rmhist p) & [] (ImpNext p) &
      [][HNext rmhist p]_ (c p, r p, m p, rmhist!p) & [] (ALL l. $MemInv mm l)")
   apply (auto simp: split_box_conj [try_rewrite] box_stp_act [try_rewrite]
       dest!: Step1_5_1b [temp_use])
      apply (force simp: IPImp_def MClkIPSpec_def RPCIPSpec_def RPSpec_def
        ImpLive_def c_def r_def m_def)
      apply (force simp: IPImp_def MClkIPSpec_def RPCIPSpec_def RPSpec_def
        HistP_def Init_def ImpInit_def)
    apply (force simp: IPImp_def MClkIPSpec_def RPCIPSpec_def RPSpec_def
      ImpNext_def c_def r_def m_def split_box_conj [temp_use])
   apply (force simp: HistP_def)
  apply (force simp: allT [temp_use] dest!: Step1_5_1a [temp_use])
  done

(* The implementation is infinitely often in state S1... *)
lemma Step1_5_3a: "|- [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p))
         & [](ALL l. $MemInv mm l)
         & []($ImpInv rmhist p) & ImpLive p
         --> []<>S1 rmhist p"
  apply (clarsimp simp: ImpLive_def)
  apply (rule S1Infinite)
   apply (force simp: split_box_conj [try_rewrite] box_stp_act [try_rewrite]
     intro!: NotS1LeadstoS6 [temp_use] S2_live [temp_use] S3_live [temp_use]
     S4a_live [temp_use] S4b_live [temp_use] S5_live [temp_use])
  apply (auto simp: split_box_conj [temp_use] intro!: S6_live [temp_use])
  done

(* ... and therefore satisfies the fairness requirements of the specification *)
lemma Step1_5_3b: "|- [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p))
         & [](ALL l. $MemInv mm l) & []($ImpInv rmhist p) & ImpLive p
         --> WF(RNext memCh mm (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)"
  by (auto intro!: RNext_fair [temp_use] Step1_5_3a [temp_use])

lemma Step1_5_3c: "|- [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p))
         & [](ALL l. $MemInv mm l) & []($ImpInv rmhist p) & ImpLive p
         --> WF(MemReturn memCh (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)"
  by (auto intro!: Return_fair [temp_use] Step1_5_3a [temp_use])

(* QED step of step 1 *)
lemma Step1: "|- IPImp p & HistP rmhist p --> UPSpec memCh mm (resbar rmhist) p"
  by (auto simp: UPSpec_def split_box_conj [temp_use]
    dest!: GoodImpl [temp_use] intro!: Step1_5_2a [temp_use] Step1_5_2b [temp_use]
    Step1_5_3b [temp_use] Step1_5_3c [temp_use])

(* ------------------------------ Step 2 ------------------------------ *)
section "Step 2"

lemma Step2_2a: "|- Write rmCh mm ires p l & ImpNext p
         & [HNext rmhist p]_(c p, r p, m p, rmhist!p)
         & $ImpInv rmhist p
         --> (S4 rmhist p)$ & unchanged (e p, c p, r p, rmhist!p)"
  apply clarsimp
  apply (drule WriteS4 [action_use])
   apply assumption
  apply split_idle
  apply (auto simp: ImpNext_def dest!: S4EnvUnch [temp_use] S4ClerkUnch [temp_use]
    S4RPCUnch [temp_use])
     apply (auto simp: square_def dest: S4Write [temp_use])
  done

lemma Step2_2: "|-   (ALL p. ImpNext p)
         & (ALL p. [HNext rmhist p]_(c p, r p, m p, rmhist!p))
         & (ALL p. $ImpInv rmhist p)
         & [EX q. Write rmCh mm ires q l]_(mm!l)
         --> [EX q. Write memCh mm (resbar rmhist) q l]_(mm!l)"
  apply (auto intro!: squareCI elim!: squareE)
  apply (assumption | rule exI Step1_4_4b [action_use])+
    apply (force intro!: WriteS4 [temp_use])
   apply (auto dest!: Step2_2a [temp_use])
  done

lemma Step2_lemma: "|- [](  (ALL p. ImpNext p)
            & (ALL p. [HNext rmhist p]_(c p, r p, m p, rmhist!p))
            & (ALL p. $ImpInv rmhist p)
            & [EX q. Write rmCh mm ires q l]_(mm!l))
         --> [][EX q. Write memCh mm (resbar rmhist) q l]_(mm!l)"
  by (force elim!: STL4E [temp_use] dest!: Step2_2 [temp_use])

lemma Step2: "|- #l : #MemLoc & (ALL p. IPImp p & HistP rmhist p)
         --> MSpec memCh mm (resbar rmhist) l"
  apply (auto simp: MSpec_def)
   apply (force simp: IPImp_def MSpec_def)
  apply (auto intro!: Step2_lemma [temp_use] simp: split_box_conj [temp_use] all_box [temp_use])
     prefer 4
     apply (force simp: IPImp_def MSpec_def)
    apply (auto simp: split_box_conj [temp_use] elim!: allE dest!: GoodImpl [temp_use])
  done

(* ----------------------------- Main theorem --------------------------------- *)
section "Memory implementation"

(* The combination of a legal caller, the memory clerk, the RPC component,
   and a reliable memory implement the unreliable memory.
*)

(* Implementation of internal specification by combination of implementation
   and history variable with explicit refinement mapping
*)
lemma Impl_IUSpec: "|- Implementation & Hist rmhist --> IUSpec memCh mm (resbar rmhist)"
  by (auto simp: IUSpec_def Implementation_def IPImp_def MClkISpec_def
    RPCISpec_def IRSpec_def Hist_def intro!: Step1 [temp_use] Step2 [temp_use])

(* The main theorem: introduce hiding and eliminate history variable. *)
lemma Implementation: "|- Implementation --> USpec memCh"
  apply clarsimp
  apply (frule History [temp_use])
  apply (auto simp: USpec_def intro: eexI [temp_use] Impl_IUSpec [temp_use]
    MI_base [temp_use] elim!: eexE)
  done

end
