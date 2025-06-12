(*  Title:      HOL/TLA/Memory/MemoryImplementation.thy
    Author:     Stephan Merz, University of Munich
*)

section \<open>RPC-Memory example: Memory implementation\<close>

theory MemoryImplementation
imports Memory RPC MemClerk
begin

datatype histState = histA | histB

type_synonym histType = "(PrIds \<Rightarrow> histState) stfun"  (* the type of the history variable *)

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
  MVOKBARF      :: "Vals \<Rightarrow> bool"
  where "MVOKBARF v \<longleftrightarrow> (v \<in> MemVal) \<or> (v = OK) \<or> (v = BadArg) \<or> (v = RPCFailure)"

definition
  MVOKBA        :: "Vals \<Rightarrow> bool"
  where "MVOKBA v \<longleftrightarrow> (v \<in> MemVal) \<or> (v = OK) \<or> (v = BadArg)"

definition
  MVNROKBA      :: "Vals \<Rightarrow> bool"
  where "MVNROKBA v \<longleftrightarrow> (v \<in> MemVal) \<or> (v = NotAResult) \<or> (v = OK) \<or> (v = BadArg)"

definition
  (* tuples of state functions changed by the various components *)
  e             :: "PrIds => (bit * memOp) stfun"
  where "e p = PRED (caller memCh!p)"

definition
  c             :: "PrIds \<Rightarrow> (mClkState * (bit * Vals) * (bit * rpcOp)) stfun"
  where "c p = PRED (cst!p, rtrner memCh!p, caller crCh!p)"

definition
  r             :: "PrIds \<Rightarrow> (rpcState * (bit * Vals) * (bit * memOp)) stfun"
  where "r p = PRED (rst!p, rtrner crCh!p, caller rmCh!p)"

definition
  m             :: "PrIds \<Rightarrow> ((bit * Vals) * Vals) stfun"
  where "m p = PRED (rtrner rmCh!p, ires!p)"

definition
  (* the environment action *)
  ENext         :: "PrIds \<Rightarrow> action"
  where "ENext p = ACT (\<exists>l. #l \<in> #MemLoc \<and> Call memCh p #(read l))"


definition
  (* specification of the history variable *)
  HInit         :: "histType \<Rightarrow> PrIds \<Rightarrow> stpred"
  where "HInit rmhist p = PRED rmhist!p = #histA"

definition
  HNext         :: "histType \<Rightarrow> PrIds \<Rightarrow> action"
  where "HNext rmhist p = ACT (rmhist!p)$ =
                     (if (MemReturn rmCh ires p \<or> RPCFail crCh rmCh rst p)
                      then #histB
                      else if (MClkReply memCh crCh cst p)
                           then #histA
                           else $(rmhist!p))"

definition
  HistP         :: "histType \<Rightarrow> PrIds \<Rightarrow> temporal"
  where "HistP rmhist p = (TEMP Init HInit rmhist p
                           \<and> \<box>[HNext rmhist p]_(c p,r p,m p, rmhist!p))"

definition
  Hist          :: "histType \<Rightarrow> temporal"
  where "Hist rmhist = TEMP (\<forall>p. HistP rmhist p)"

definition
  (* the implementation *)
  IPImp          :: "PrIds \<Rightarrow> temporal"
  where "IPImp p = (TEMP (  Init \<not>Calling memCh p \<and> \<box>[ENext p]_(e p)
                       \<and> MClkIPSpec memCh crCh cst p
                       \<and> RPCIPSpec crCh rmCh rst p
                       \<and> RPSpec rmCh mm ires p
                       \<and> (\<forall>l. #l \<in> #MemLoc \<longrightarrow> MSpec rmCh mm ires l)))"

definition
  ImpInit        :: "PrIds \<Rightarrow> stpred"
  where "ImpInit p = PRED (  \<not>Calling memCh p
                          \<and> MClkInit crCh cst p
                          \<and> RPCInit rmCh rst p
                          \<and> PInit ires p)"

definition
  ImpNext        :: "PrIds \<Rightarrow> action"
  where "ImpNext p = (ACT  [ENext p]_(e p)
                       \<and> [MClkNext memCh crCh cst p]_(c p)
                       \<and> [RPCNext crCh rmCh rst p]_(r p)
                       \<and> [RNext rmCh mm ires p]_(m p))"

definition
  ImpLive        :: "PrIds \<Rightarrow> temporal"
  where "ImpLive p = (TEMP  WF(MClkFwd memCh crCh cst p)_(c p)
                        \<and> SF(MClkReply memCh crCh cst p)_(c p)
                        \<and> WF(RPCNext crCh rmCh rst p)_(r p)
                        \<and> WF(RNext rmCh mm ires p)_(m p)
                        \<and> WF(MemReturn rmCh ires p)_(m p))"

definition
  Implementation :: "temporal"
  where "Implementation = (TEMP ( (\<forall>p. Init (\<not>Calling memCh p) \<and> \<box>[ENext p]_(e p))
                               \<and> MClkISpec memCh crCh cst
                               \<and> RPCISpec crCh rmCh rst
                               \<and> IRSpec rmCh mm ires))"

definition
  (* the predicate S describes the states of the implementation.
     slight simplification: two "histState" parameters instead of a
     (one- or two-element) set.
     NB: The second conjunct of the definition in the paper is taken care of by
     the type definitions. The last conjunct is asserted separately as the memory
     invariant MemInv, proved in Memory.thy. *)
  S :: "histType \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> mClkState \<Rightarrow> rpcState \<Rightarrow> histState \<Rightarrow> histState \<Rightarrow> PrIds \<Rightarrow> stpred"
  where "S rmhist ecalling ccalling rcalling cs rs hs1 hs2 p = (PRED
                Calling memCh p = #ecalling
              \<and> Calling crCh p  = #ccalling
              \<and> (#ccalling \<longrightarrow> arg<crCh!p> = MClkRelayArg<arg<memCh!p>>)
              \<and> (\<not> #ccalling \<and> cst!p = #clkB \<longrightarrow> MVOKBARF<res<crCh!p>>)
              \<and> Calling rmCh p  = #rcalling
              \<and> (#rcalling \<longrightarrow> arg<rmCh!p> = RPCRelayArg<arg<crCh!p>>)
              \<and> (\<not> #rcalling \<longrightarrow> ires!p = #NotAResult)
              \<and> (\<not> #rcalling \<and> rst!p = #rpcB \<longrightarrow> MVOKBA<res<rmCh!p>>)
              \<and> cst!p = #cs
              \<and> rst!p = #rs
              \<and> (rmhist!p = #hs1 \<or> rmhist!p = #hs2)
              \<and> MVNROKBA<ires!p>)"

definition
  (* predicates S1 -- S6 define special instances of S *)
  S1            :: "histType \<Rightarrow> PrIds \<Rightarrow> stpred"
  where "S1 rmhist p = S rmhist False False False clkA rpcA histA histA p"

definition
  S2            :: "histType \<Rightarrow> PrIds \<Rightarrow> stpred"
  where "S2 rmhist p = S rmhist True False False clkA rpcA histA histA p"

definition
  S3            :: "histType \<Rightarrow> PrIds \<Rightarrow> stpred"
  where "S3 rmhist p = S rmhist True True False clkB rpcA histA histB p"

definition
  S4            :: "histType \<Rightarrow> PrIds \<Rightarrow> stpred"
  where "S4 rmhist p = S rmhist True True True clkB rpcB histA histB p"

definition
  S5            :: "histType \<Rightarrow> PrIds \<Rightarrow> stpred"
  where "S5 rmhist p = S rmhist True True False clkB rpcB histB histB p"

definition
  S6            :: "histType \<Rightarrow> PrIds \<Rightarrow> stpred"
  where "S6 rmhist p = S rmhist True False False clkB rpcA histB histB p"

definition
  (* The invariant asserts that the system is always in one of S1 - S6, for every p *)
  ImpInv         :: "histType \<Rightarrow> PrIds \<Rightarrow> stpred"
  where "ImpInv rmhist p = (PRED (S1 rmhist p \<or> S2 rmhist p \<or> S3 rmhist p
                                \<or> S4 rmhist p \<or> S5 rmhist p \<or> S6 rmhist p))"

definition
  resbar        :: "histType \<Rightarrow> resType"        (* refinement mapping *)
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
ML \<open>
  val config_fast_solver = Attrib.setup_config_bool \<^binding>\<open>fast_solver\<close> (K false);
  val fast_solver = mk_solver "fast_solver" (fn ctxt =>
    if Config.get ctxt config_fast_solver
    then assume_tac ctxt ORELSE' (eresolve_tac ctxt [notE])
    else K no_tac);
\<close>

setup \<open>map_theory_simpset (fn ctxt => ctxt |> Simplifier.add_safe_solver fast_solver)\<close>

ML \<open>val temp_elim = make_elim oo temp_use\<close>



(****************************** The history variable ******************************)

section "History variable"

lemma HistoryLemma: "\<turnstile> Init(\<forall>p. ImpInit p) \<and> \<box>(\<forall>p. ImpNext p)
         \<longrightarrow> (\<exists>\<exists>rmhist. Init(\<forall>p. HInit rmhist p)
                          \<and> \<box>(\<forall>p. [HNext rmhist p]_(c p, r p, m p, rmhist!p)))"
  apply clarsimp
  apply (rule historyI)
      apply assumption+
  apply (rule MI_base)
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm HInit_def}]) [] [] 1\<close>)
   apply (erule fun_cong)
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm HNext_def}])
    [@{thm busy_squareI}] [] 1\<close>)
  apply (erule fun_cong)
  done

lemma History: "\<turnstile> Implementation \<longrightarrow> (\<exists>\<exists>rmhist. Hist rmhist)"
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

lemma MVOKBAnotRF: "MVOKBA x \<Longrightarrow> x \<noteq> RPCFailure"
  apply (unfold MVOKBA_def)
  apply auto
  done

(* NotAResult notin MemVals U {OK,BadArg,RPCFailure} *)

lemma MVOKBARFnotNR: "MVOKBARF x \<Longrightarrow> x \<noteq> NotAResult"
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
lemma S1_excl: "\<turnstile> S1 rmhist p \<longrightarrow> S1 rmhist p & \<not>S2 rmhist p & \<not>S3 rmhist p &
    \<not>S4 rmhist p & \<not>S5 rmhist p & \<not>S6 rmhist p"
  by (auto simp: S_def S1_def S2_def S3_def S4_def S5_def S6_def)
*)

lemma S2_excl: "\<turnstile> S2 rmhist p \<longrightarrow> S2 rmhist p \<and> \<not>S1 rmhist p"
  by (auto simp: S_def S1_def S2_def)

lemma S3_excl: "\<turnstile> S3 rmhist p \<longrightarrow> S3 rmhist p \<and> \<not>S1 rmhist p \<and> \<not>S2 rmhist p"
  by (auto simp: S_def S1_def S2_def S3_def)

lemma S4_excl: "\<turnstile> S4 rmhist p \<longrightarrow> S4 rmhist p \<and> \<not>S1 rmhist p \<and> \<not>S2 rmhist p \<and> \<not>S3 rmhist p"
  by (auto simp: S_def S1_def S2_def S3_def S4_def)

lemma S5_excl: "\<turnstile> S5 rmhist p \<longrightarrow> S5 rmhist p \<and> \<not>S1 rmhist p \<and> \<not>S2 rmhist p
                         \<and> \<not>S3 rmhist p \<and> \<not>S4 rmhist p"
  by (auto simp: S_def S1_def S2_def S3_def S4_def S5_def)

lemma S6_excl: "\<turnstile> S6 rmhist p \<longrightarrow> S6 rmhist p \<and> \<not>S1 rmhist p \<and> \<not>S2 rmhist p
                         \<and> \<not>S3 rmhist p \<and> \<not>S4 rmhist p \<and> \<not>S5 rmhist p"
  by (auto simp: S_def S1_def S2_def S3_def S4_def S5_def S6_def)


(* ==================== Lemmas about the environment ============================== *)

lemma Envbusy: "\<turnstile> $(Calling memCh p) \<longrightarrow> \<not>ENext p"
  by (auto simp: ENext_def ACall_def)

(* ==================== Lemmas about the implementation's states ==================== *)

(* The following series of lemmas are used in establishing the implementation's
   next-state relation (Step 1.2 of the proof in the paper). For each state Si, we
   determine which component actions are possible and what state they result in.
*)

(* ------------------------------ State S1 ---------------------------------------- *)

lemma S1Env: "\<turnstile> ENext p \<and> $(S1 rmhist p) \<and> unchanged (c p, r p, m p, rmhist!p)
         \<longrightarrow> (S2 rmhist p)$"
  by (force simp: ENext_def ACall_def c_def r_def m_def
    caller_def rtrner_def MVNROKBA_def S_def S1_def S2_def Calling_def)

lemma S1ClerkUnch: "\<turnstile> [MClkNext memCh crCh cst p]_(c p) \<and> $(S1 rmhist p) \<longrightarrow> unchanged (c p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] dest!: MClkidle [temp_use] simp: S_def S1_def)

lemma S1RPCUnch: "\<turnstile> [RPCNext crCh rmCh rst p]_(r p) \<and> $(S1 rmhist p) \<longrightarrow> unchanged (r p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] dest!: RPCidle [temp_use] simp: S_def S1_def)

lemma S1MemUnch: "\<turnstile> [RNext rmCh mm ires p]_(m p) \<and> $(S1 rmhist p) \<longrightarrow> unchanged (m p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] dest!: Memoryidle [temp_use] simp: S_def S1_def)

lemma S1Hist: "\<turnstile> [HNext rmhist p]_(c p,r p,m p,rmhist!p) \<and> $(S1 rmhist p)
         \<longrightarrow> unchanged (rmhist!p)"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm HNext_def}, @{thm S_def},
    @{thm S1_def}, @{thm MemReturn_def}, @{thm RPCFail_def}, @{thm MClkReply_def},
    @{thm AReturn_def}]) [] [temp_use \<^context> @{thm squareE}] 1\<close>)


(* ------------------------------ State S2 ---------------------------------------- *)

lemma S2EnvUnch: "\<turnstile> [ENext p]_(e p) \<and> $(S2 rmhist p) \<longrightarrow> unchanged (e p)"
  by (auto dest!: Envbusy [temp_use] simp: S_def S2_def)

lemma S2Clerk: "\<turnstile> MClkNext memCh crCh cst p \<and> $(S2 rmhist p) \<longrightarrow> MClkFwd memCh crCh cst p"
  by (auto simp: MClkNext_def MClkRetry_def MClkReply_def S_def S2_def)

lemma S2Forward: "\<turnstile> $(S2 rmhist p) \<and> MClkFwd memCh crCh cst p
         \<and> unchanged (e p, r p, m p, rmhist!p)
         \<longrightarrow> (S3 rmhist p)$"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm MClkFwd_def},
    @{thm ACall_def}, @{thm e_def}, @{thm r_def}, @{thm m_def}, @{thm caller_def},
    @{thm rtrner_def}, @{thm S_def}, @{thm S2_def}, @{thm S3_def}, @{thm Calling_def}]) [] [] 1\<close>)

lemma S2RPCUnch: "\<turnstile> [RPCNext crCh rmCh rst p]_(r p) \<and> $(S2 rmhist p) \<longrightarrow> unchanged (r p)"
  by (auto simp: S_def S2_def dest!: RPCidle [temp_use])

lemma S2MemUnch: "\<turnstile> [RNext rmCh mm ires p]_(m p) \<and> $(S2 rmhist p) \<longrightarrow> unchanged (m p)"
  by (auto simp: S_def S2_def dest!: Memoryidle [temp_use])

lemma S2Hist: "\<turnstile> [HNext rmhist p]_(c p,r p,m p,rmhist!p) \<and> $(S2 rmhist p)
         \<longrightarrow> unchanged (rmhist!p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] simp: HNext_def MemReturn_def RPCFail_def
    MClkReply_def AReturn_def S_def S2_def)

(* ------------------------------ State S3 ---------------------------------------- *)

lemma S3EnvUnch: "\<turnstile> [ENext p]_(e p) \<and> $(S3 rmhist p) \<longrightarrow> unchanged (e p)"
  by (auto dest!: Envbusy [temp_use] simp: S_def S3_def)

lemma S3ClerkUnch: "\<turnstile> [MClkNext memCh crCh cst p]_(c p) \<and> $(S3 rmhist p) \<longrightarrow> unchanged (c p)"
  by (auto dest!: MClkbusy [temp_use] simp: square_def S_def S3_def)

lemma S3LegalRcvArg: "\<turnstile> S3 rmhist p \<longrightarrow> IsLegalRcvArg<arg<crCh!p>>"
  by (auto simp: IsLegalRcvArg_def MClkRelayArg_def S_def S3_def)

lemma S3RPC: "\<turnstile> RPCNext crCh rmCh rst p \<and> $(S3 rmhist p)
         \<longrightarrow> RPCFwd crCh rmCh rst p \<or> RPCFail crCh rmCh rst p"
  apply clarsimp
  apply (frule S3LegalRcvArg [action_use])
  apply (auto simp: RPCNext_def RPCReject_def RPCReply_def S_def S3_def)
  done

lemma S3Forward: "\<turnstile> RPCFwd crCh rmCh rst p \<and> HNext rmhist p \<and> $(S3 rmhist p)
         \<and> unchanged (e p, c p, m p)
         \<longrightarrow> (S4 rmhist p)$ \<and> unchanged (rmhist!p)"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm RPCFwd_def},
    @{thm HNext_def}, @{thm MemReturn_def}, @{thm RPCFail_def},
    @{thm MClkReply_def}, @{thm AReturn_def}, @{thm ACall_def}, @{thm e_def},
    @{thm c_def}, @{thm m_def}, @{thm caller_def}, @{thm rtrner_def}, @{thm S_def},
    @{thm S3_def}, @{thm S4_def}, @{thm Calling_def}]) [] [] 1\<close>)

lemma S3Fail: "\<turnstile> RPCFail crCh rmCh rst p \<and> $(S3 rmhist p) \<and> HNext rmhist p
         \<and> unchanged (e p, c p, m p)
         \<longrightarrow> (S6 rmhist p)$"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm HNext_def},
    @{thm RPCFail_def}, @{thm AReturn_def}, @{thm e_def}, @{thm c_def},
    @{thm m_def}, @{thm caller_def}, @{thm rtrner_def}, @{thm MVOKBARF_def},
    @{thm S_def}, @{thm S3_def}, @{thm S6_def}, @{thm Calling_def}]) [] [] 1\<close>)

lemma S3MemUnch: "\<turnstile> [RNext rmCh mm ires p]_(m p) \<and> $(S3 rmhist p) \<longrightarrow> unchanged (m p)"
  by (auto simp: S_def S3_def dest!: Memoryidle [temp_use])

lemma S3Hist: "\<turnstile> HNext rmhist p \<and> $(S3 rmhist p) \<and> unchanged (r p) \<longrightarrow> unchanged (rmhist!p)"
  by (auto simp: HNext_def MemReturn_def RPCFail_def MClkReply_def
    AReturn_def r_def rtrner_def S_def S3_def Calling_def)

(* ------------------------------ State S4 ---------------------------------------- *)

lemma S4EnvUnch: "\<turnstile> [ENext p]_(e p) \<and> $(S4 rmhist p) \<longrightarrow> unchanged (e p)"
  by (auto simp: S_def S4_def dest!: Envbusy [temp_use])

lemma S4ClerkUnch: "\<turnstile> [MClkNext memCh crCh cst p]_(c p) \<and> $(S4 rmhist p) \<longrightarrow> unchanged (c p)"
  by (auto simp: S_def S4_def dest!: MClkbusy [temp_use])

lemma S4RPCUnch: "\<turnstile> [RPCNext crCh rmCh rst p]_(r p) \<and> $(S4 rmhist p) \<longrightarrow> unchanged (r p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] dest!: RPCbusy [temp_use] simp: S_def S4_def)

lemma S4ReadInner: "\<turnstile> ReadInner rmCh mm ires p l \<and> $(S4 rmhist p) \<and> unchanged (e p, c p, r p)
         \<and> HNext rmhist p \<and> $(MemInv mm l)
         \<longrightarrow> (S4 rmhist p)$ \<and> unchanged (rmhist!p)"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm ReadInner_def},
    @{thm GoodRead_def}, @{thm BadRead_def}, @{thm HNext_def}, @{thm MemReturn_def},
    @{thm RPCFail_def}, @{thm MClkReply_def}, @{thm AReturn_def}, @{thm e_def},
    @{thm c_def}, @{thm r_def}, @{thm rtrner_def}, @{thm caller_def},
    @{thm MVNROKBA_def}, @{thm S_def}, @{thm S4_def}, @{thm RdRequest_def},
    @{thm Calling_def}, @{thm MemInv_def}]) [] [] 1\<close>)

lemma S4Read: "\<turnstile> Read rmCh mm ires p \<and> $(S4 rmhist p) \<and> unchanged (e p, c p, r p)
         \<and> HNext rmhist p \<and> (\<forall>l. $MemInv mm l)
         \<longrightarrow> (S4 rmhist p)$ \<and> unchanged (rmhist!p)"
  by (auto simp: Read_def dest!: S4ReadInner [temp_use])

lemma S4WriteInner: "\<turnstile> WriteInner rmCh mm ires p l v \<and> $(S4 rmhist p) \<and> unchanged (e p, c p, r p) \<and> HNext rmhist p
         \<longrightarrow> (S4 rmhist p)$ \<and> unchanged (rmhist!p)"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm WriteInner_def},
    @{thm GoodWrite_def}, @{thm BadWrite_def}, @{thm HNext_def}, @{thm MemReturn_def},
    @{thm RPCFail_def}, @{thm MClkReply_def}, @{thm AReturn_def}, @{thm e_def},
    @{thm c_def}, @{thm r_def}, @{thm rtrner_def}, @{thm caller_def}, @{thm MVNROKBA_def},
    @{thm S_def}, @{thm S4_def}, @{thm WrRequest_def}, @{thm Calling_def}]) [] [] 1\<close>)

lemma S4Write: "\<turnstile> Write rmCh mm ires p l \<and> $(S4 rmhist p) \<and> unchanged (e p, c p, r p)
         \<and> (HNext rmhist p)
         \<longrightarrow> (S4 rmhist p)$ \<and> unchanged (rmhist!p)"
  by (auto simp: Write_def dest!: S4WriteInner [temp_use])

lemma WriteS4: "\<turnstile> $ImpInv rmhist p \<and> Write rmCh mm ires p l \<longrightarrow> $S4 rmhist p"
  by (auto simp: Write_def WriteInner_def ImpInv_def
    WrRequest_def S_def S1_def S2_def S3_def S4_def S5_def S6_def)

lemma S4Return: "\<turnstile> MemReturn rmCh ires p \<and> $S4 rmhist p \<and> unchanged (e p, c p, r p)
         \<and> HNext rmhist p
         \<longrightarrow> (S5 rmhist p)$"
  by (auto simp: HNext_def MemReturn_def AReturn_def e_def c_def r_def
    rtrner_def caller_def MVNROKBA_def MVOKBA_def S_def S4_def S5_def Calling_def)

lemma S4Hist: "\<turnstile> HNext rmhist p \<and> $S4 rmhist p \<and> (m p)$ = $(m p) \<longrightarrow> (rmhist!p)$ = $(rmhist!p)"
  by (auto simp: HNext_def MemReturn_def RPCFail_def MClkReply_def
    AReturn_def m_def rtrner_def S_def S4_def Calling_def)

(* ------------------------------ State S5 ---------------------------------------- *)

lemma S5EnvUnch: "\<turnstile> [ENext p]_(e p) \<and> $(S5 rmhist p) \<longrightarrow> unchanged (e p)"
  by (auto simp: S_def S5_def dest!: Envbusy [temp_use])

lemma S5ClerkUnch: "\<turnstile> [MClkNext memCh crCh cst p]_(c p) \<and> $(S5 rmhist p) \<longrightarrow> unchanged (c p)"
  by (auto simp: S_def S5_def dest!: MClkbusy [temp_use])

lemma S5RPC: "\<turnstile> RPCNext crCh rmCh rst p \<and> $(S5 rmhist p)
         \<longrightarrow> RPCReply crCh rmCh rst p \<or> RPCFail crCh rmCh rst p"
  by (auto simp: RPCNext_def RPCReject_def RPCFwd_def S_def S5_def)

lemma S5Reply: "\<turnstile> RPCReply crCh rmCh rst p \<and> $(S5 rmhist p) \<and> unchanged (e p, c p, m p,rmhist!p)
       \<longrightarrow> (S6 rmhist p)$"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm RPCReply_def},
    @{thm AReturn_def}, @{thm e_def}, @{thm c_def}, @{thm m_def}, @{thm MVOKBA_def},
    @{thm MVOKBARF_def}, @{thm caller_def}, @{thm rtrner_def}, @{thm S_def},
    @{thm S5_def}, @{thm S6_def}, @{thm Calling_def}]) [] [] 1\<close>)

lemma S5Fail: "\<turnstile> RPCFail crCh rmCh rst p \<and> $(S5 rmhist p) \<and> unchanged (e p, c p, m p,rmhist!p)
         \<longrightarrow> (S6 rmhist p)$"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm RPCFail_def},
    @{thm AReturn_def}, @{thm e_def}, @{thm c_def}, @{thm m_def},
    @{thm MVOKBARF_def}, @{thm caller_def}, @{thm rtrner_def},
    @{thm S_def}, @{thm S5_def}, @{thm S6_def}, @{thm Calling_def}]) [] [] 1\<close>)

lemma S5MemUnch: "\<turnstile> [RNext rmCh mm ires p]_(m p) \<and> $(S5 rmhist p) \<longrightarrow> unchanged (m p)"
  by (auto simp: S_def S5_def dest!: Memoryidle [temp_use])

lemma S5Hist: "\<turnstile> [HNext rmhist p]_(c p, r p, m p, rmhist!p) \<and> $(S5 rmhist p)
         \<longrightarrow> (rmhist!p)$ = $(rmhist!p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] simp: HNext_def MemReturn_def RPCFail_def
    MClkReply_def AReturn_def S_def S5_def)

(* ------------------------------ State S6 ---------------------------------------- *)

lemma S6EnvUnch: "\<turnstile> [ENext p]_(e p) \<and> $(S6 rmhist p) \<longrightarrow> unchanged (e p)"
  by (auto simp: S_def S6_def dest!: Envbusy [temp_use])

lemma S6Clerk: "\<turnstile> MClkNext memCh crCh cst p \<and> $(S6 rmhist p)
         \<longrightarrow> MClkRetry memCh crCh cst p \<or> MClkReply memCh crCh cst p"
  by (auto simp: MClkNext_def MClkFwd_def S_def S6_def)

lemma S6Retry: "\<turnstile> MClkRetry memCh crCh cst p \<and> HNext rmhist p \<and> $S6 rmhist p
         \<and> unchanged (e p,r p,m p)
         \<longrightarrow> (S3 rmhist p)$ \<and> unchanged (rmhist!p)"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm HNext_def},
    @{thm MClkReply_def}, @{thm MClkRetry_def}, @{thm ACall_def}, @{thm AReturn_def},
    @{thm e_def}, @{thm r_def}, @{thm m_def}, @{thm caller_def}, @{thm rtrner_def},
    @{thm S_def}, @{thm S6_def}, @{thm S3_def}, @{thm Calling_def}]) [] [] 1\<close>)

lemma S6Reply: "\<turnstile> MClkReply memCh crCh cst p \<and> HNext rmhist p \<and> $S6 rmhist p
         \<and> unchanged (e p,r p,m p)
         \<longrightarrow> (S1 rmhist p)$"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm HNext_def},
    @{thm MemReturn_def}, @{thm RPCFail_def}, @{thm AReturn_def}, @{thm MClkReply_def},
    @{thm e_def}, @{thm r_def}, @{thm m_def}, @{thm caller_def}, @{thm rtrner_def},
    @{thm S_def}, @{thm S6_def}, @{thm S1_def}, @{thm Calling_def}]) [] [] 1\<close>)

lemma S6RPCUnch: "\<turnstile> [RPCNext crCh rmCh rst p]_(r p) \<and> $S6 rmhist p \<longrightarrow> unchanged (r p)"
  by (auto simp: S_def S6_def dest!: RPCidle [temp_use])

lemma S6MemUnch: "\<turnstile> [RNext rmCh mm ires p]_(m p) \<and> $(S6 rmhist p) \<longrightarrow> unchanged (m p)"
  by (auto simp: S_def S6_def dest!: Memoryidle [temp_use])

lemma S6Hist: "\<turnstile> HNext rmhist p \<and> $S6 rmhist p \<and> (c p)$ = $(c p) \<longrightarrow> (rmhist!p)$ = $(rmhist!p)"
  by (auto simp: HNext_def MClkReply_def AReturn_def c_def rtrner_def S_def S6_def Calling_def)


section "Correctness of predicate-action diagram"


(* ========== Step 1.1 ================================================= *)
(* The implementation's initial condition implies the state predicate S1 *)

lemma Step1_1: "\<turnstile> ImpInit p \<and> HInit rmhist p \<longrightarrow> S1 rmhist p"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] simp: MVNROKBA_def
    MClkInit_def RPCInit_def PInit_def HInit_def ImpInit_def S_def S1_def)

(* ========== Step 1.2 ================================================== *)
(* Figure 16 is a predicate-action diagram for the implementation. *)

lemma Step1_2_1: "\<turnstile> [HNext rmhist p]_(c p,r p,m p, rmhist!p) \<and> ImpNext p
         \<and> \<not>unchanged (e p, c p, r p, m p, rmhist!p)  \<and> $S1 rmhist p
         \<longrightarrow> (S2 rmhist p)$ \<and> ENext p \<and> unchanged (c p, r p, m p)"
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm ImpNext_def}]) []
      (map (temp_elim \<^context>)
        [@{thm S1ClerkUnch}, @{thm S1RPCUnch}, @{thm S1MemUnch}, @{thm S1Hist}]) 1\<close>)
   using [[fast_solver]]
   apply (auto elim!: squareE [temp_use] intro!: S1Env [temp_use])
  done

lemma Step1_2_2: "\<turnstile> [HNext rmhist p]_(c p,r p,m p, rmhist!p) \<and> ImpNext p
         \<and> \<not>unchanged (e p, c p, r p, m p, rmhist!p) \<and> $S2 rmhist p
         \<longrightarrow> (S3 rmhist p)$ \<and> MClkFwd memCh crCh cst p
             \<and> unchanged (e p, r p, m p, rmhist!p)"
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm ImpNext_def}]) []
    (map (temp_elim \<^context>)
      [@{thm S2EnvUnch}, @{thm S2RPCUnch}, @{thm S2MemUnch}, @{thm S2Hist}]) 1\<close>)
   using [[fast_solver]]
   apply (auto elim!: squareE [temp_use] intro!: S2Clerk [temp_use] S2Forward [temp_use])
  done

lemma Step1_2_3: "\<turnstile> [HNext rmhist p]_(c p,r p,m p, rmhist!p) \<and> ImpNext p
         \<and> \<not>unchanged (e p, c p, r p, m p, rmhist!p) \<and> $S3 rmhist p
         \<longrightarrow> ((S4 rmhist p)$ \<and> RPCFwd crCh rmCh rst p \<and> unchanged (e p, c p, m p, rmhist!p))
             \<or> ((S6 rmhist p)$ \<and> RPCFail crCh rmCh rst p \<and> unchanged (e p, c p, m p))"
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm ImpNext_def}]) []
    (map (temp_elim \<^context>) [@{thm S3EnvUnch}, @{thm S3ClerkUnch}, @{thm S3MemUnch}]) 1\<close>)
  apply (tactic \<open>action_simp_tac \<^context> []
    (@{thm squareE} ::
      map (temp_elim \<^context>) [@{thm S3RPC}, @{thm S3Forward}, @{thm S3Fail}]) 1\<close>)
   apply (auto dest!: S3Hist [temp_use])
  done

lemma Step1_2_4: "\<turnstile> [HNext rmhist p]_(c p,r p,m p, rmhist!p) \<and> ImpNext p
              \<and> \<not>unchanged (e p, c p, r p, m p, rmhist!p)
              \<and> $S4 rmhist p \<and> (\<forall>l. $(MemInv mm l))
         \<longrightarrow> ((S4 rmhist p)$ \<and> Read rmCh mm ires p \<and> unchanged (e p, c p, r p, rmhist!p))
             \<or> ((S4 rmhist p)$ \<and> (\<exists>l. Write rmCh mm ires p l) \<and> unchanged (e p, c p, r p, rmhist!p))
             \<or> ((S5 rmhist p)$ \<and> MemReturn rmCh ires p \<and> unchanged (e p, c p, r p))"
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm ImpNext_def}]) []
    (map (temp_elim \<^context>) [@{thm S4EnvUnch}, @{thm S4ClerkUnch}, @{thm S4RPCUnch}]) 1\<close>)
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm RNext_def}]) []
    (@{thm squareE} ::
      map (temp_elim \<^context>) [@{thm S4Read}, @{thm S4Write}, @{thm S4Return}]) 1\<close>)
  apply (auto dest!: S4Hist [temp_use])
  done

lemma Step1_2_5: "\<turnstile> [HNext rmhist p]_(c p,r p,m p, rmhist!p) \<and> ImpNext p
              \<and> \<not>unchanged (e p, c p, r p, m p, rmhist!p) \<and> $S5 rmhist p
         \<longrightarrow> ((S6 rmhist p)$ \<and> RPCReply crCh rmCh rst p \<and> unchanged (e p, c p, m p))
             \<or> ((S6 rmhist p)$ \<and> RPCFail crCh rmCh rst p \<and> unchanged (e p, c p, m p))"
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm ImpNext_def}]) []
    (map (temp_elim \<^context>) [@{thm S5EnvUnch}, @{thm S5ClerkUnch}, @{thm S5MemUnch}, @{thm S5Hist}]) 1\<close>)
  apply (tactic \<open>action_simp_tac \<^context> [] [@{thm squareE}, temp_elim \<^context> @{thm S5RPC}] 1\<close>)
   using [[fast_solver]]
   apply (auto elim!: squareE [temp_use] dest!: S5Reply [temp_use] S5Fail [temp_use])
  done

lemma Step1_2_6: "\<turnstile> [HNext rmhist p]_(c p,r p,m p, rmhist!p) \<and> ImpNext p
              \<and> \<not>unchanged (e p, c p, r p, m p, rmhist!p) \<and> $S6 rmhist p
         \<longrightarrow> ((S1 rmhist p)$ \<and> MClkReply memCh crCh cst p \<and> unchanged (e p, r p, m p))
             \<or> ((S3 rmhist p)$ \<and> MClkRetry memCh crCh cst p \<and> unchanged (e p,r p,m p,rmhist!p))"
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm ImpNext_def}]) []
    (map (temp_elim \<^context>) [@{thm S6EnvUnch}, @{thm S6RPCUnch}, @{thm S6MemUnch}]) 1\<close>)
  apply (tactic \<open>action_simp_tac \<^context> []
    (@{thm squareE} :: map (temp_elim \<^context>) [@{thm S6Clerk}, @{thm S6Retry}, @{thm S6Reply}]) 1\<close>)
     apply (auto dest: S6Hist [temp_use])
  done

(* --------------------------------------------------------------------------
   Step 1.3: S1 implies the barred initial condition.
*)

section "Initialization (Step 1.3)"

lemma Step1_3: "\<turnstile> S1 rmhist p \<longrightarrow> PInit (resbar rmhist) p"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm resbar_def},
    @{thm PInit_def}, @{thm S_def}, @{thm S1_def}]) [] [] 1\<close>)

(* ----------------------------------------------------------------------
   Step 1.4: Implementation's next-state relation simulates specification's
             next-state relation (with appropriate substitutions)
*)

section "Step simulation (Step 1.4)"

lemma Step1_4_1: "\<turnstile> ENext p \<and> $S1 rmhist p \<and> (S2 rmhist p)$ \<and> unchanged (c p, r p, m p)
         \<longrightarrow> unchanged (rtrner memCh!p, resbar rmhist!p)"
  using [[fast_solver]]
  by (auto elim!: squareE [temp_use] simp: c_def r_def m_def resbar_def)

lemma Step1_4_2: "\<turnstile> MClkFwd memCh crCh cst p \<and> $S2 rmhist p \<and> (S3 rmhist p)$
         \<and> unchanged (e p, r p, m p, rmhist!p)
         \<longrightarrow> unchanged (rtrner memCh!p, resbar rmhist!p)"
  by (tactic \<open>action_simp_tac
    (\<^context> addsimps [@{thm MClkFwd_def}, @{thm e_def}, @{thm r_def}, @{thm m_def},
    @{thm resbar_def}, @{thm S_def}, @{thm S2_def}, @{thm S3_def}]) [] [] 1\<close>)

lemma Step1_4_3a: "\<turnstile> RPCFwd crCh rmCh rst p \<and> $S3 rmhist p \<and> (S4 rmhist p)$
         \<and> unchanged (e p, c p, m p, rmhist!p)
         \<longrightarrow> unchanged (rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (drule S3_excl [temp_use] S4_excl [temp_use])+
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm e_def},
    @{thm c_def}, @{thm m_def}, @{thm resbar_def}, @{thm S_def}, @{thm S3_def}]) [] [] 1\<close>)
  done

lemma Step1_4_3b: "\<turnstile> RPCFail crCh rmCh rst p \<and> $S3 rmhist p \<and> (S6 rmhist p)$
         \<and> unchanged (e p, c p, m p)
         \<longrightarrow> MemFail memCh (resbar rmhist) p"
  apply clarsimp
  apply (drule S6_excl [temp_use])
  apply (auto simp: RPCFail_def MemFail_def e_def c_def m_def resbar_def)
    apply (force simp: S3_def S_def)
   apply (auto simp: AReturn_def)
  done

lemma Step1_4_4a1: "\<turnstile> $S4 rmhist p \<and> (S4 rmhist p)$ \<and> ReadInner rmCh mm ires p l
         \<and> unchanged (e p, c p, r p, rmhist!p) \<and> $MemInv mm l
         \<longrightarrow> ReadInner memCh mm (resbar rmhist) p l"
  apply clarsimp
  apply (drule S4_excl [temp_use])+
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm ReadInner_def},
    @{thm GoodRead_def}, @{thm BadRead_def}, @{thm e_def}, @{thm c_def}, @{thm m_def}]) [] [] 1\<close>)
     apply (auto simp: resbar_def)
       apply (tactic \<open>ALLGOALS (action_simp_tac
                (\<^context> addsimps [@{thm RPCRelayArg_def}, @{thm MClkRelayArg_def},
                  @{thm S_def}, @{thm S4_def}, @{thm RdRequest_def}, @{thm MemInv_def}])
                [] [@{thm impE}, @{thm MemValNotAResultE}])\<close>)
  done

lemma Step1_4_4a: "\<turnstile> Read rmCh mm ires p \<and> $S4 rmhist p \<and> (S4 rmhist p)$
         \<and> unchanged (e p, c p, r p, rmhist!p) \<and> (\<forall>l. $(MemInv mm l))
         \<longrightarrow> Read memCh mm (resbar rmhist) p"
  by (force simp: Read_def elim!: Step1_4_4a1 [temp_use])

lemma Step1_4_4b1: "\<turnstile> $S4 rmhist p \<and> (S4 rmhist p)$ \<and> WriteInner rmCh mm ires p l v
         \<and> unchanged (e p, c p, r p, rmhist!p)
         \<longrightarrow> WriteInner memCh mm (resbar rmhist) p l v"
  apply clarsimp
  apply (drule S4_excl [temp_use])+
  apply (tactic \<open>action_simp_tac (\<^context> addsimps
    [@{thm WriteInner_def}, @{thm GoodWrite_def}, @{thm BadWrite_def}, @{thm e_def},
    @{thm c_def}, @{thm m_def}]) [] [] 1\<close>)
     apply (auto simp: resbar_def)
    apply (tactic \<open>ALLGOALS (action_simp_tac (\<^context> addsimps
      [@{thm RPCRelayArg_def}, @{thm MClkRelayArg_def}, @{thm S_def},
      @{thm S4_def}, @{thm WrRequest_def}]) [] [])\<close>)
  done

lemma Step1_4_4b: "\<turnstile> Write rmCh mm ires p l \<and> $S4 rmhist p \<and> (S4 rmhist p)$
         \<and> unchanged (e p, c p, r p, rmhist!p)
         \<longrightarrow> Write memCh mm (resbar rmhist) p l"
  by (force simp: Write_def elim!: Step1_4_4b1 [temp_use])

lemma Step1_4_4c: "\<turnstile> MemReturn rmCh ires p \<and> $S4 rmhist p \<and> (S5 rmhist p)$
         \<and> unchanged (e p, c p, r p)
         \<longrightarrow> unchanged (rtrner memCh!p, resbar rmhist!p)"
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm e_def},
    @{thm c_def}, @{thm r_def}, @{thm resbar_def}]) [] [] 1\<close>)
  apply (drule S4_excl [temp_use] S5_excl [temp_use])+
  using [[fast_solver]]
  apply (auto elim!: squareE [temp_use] simp: MemReturn_def AReturn_def)
  done

lemma Step1_4_5a: "\<turnstile> RPCReply crCh rmCh rst p \<and> $S5 rmhist p \<and> (S6 rmhist p)$
         \<and> unchanged (e p, c p, m p)
         \<longrightarrow> unchanged (rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (drule S5_excl [temp_use] S6_excl [temp_use])+
  apply (auto simp: e_def c_def m_def resbar_def)
   apply (auto simp: RPCReply_def AReturn_def S5_def S_def dest!: MVOKBAnotRF [temp_use])
  done

lemma Step1_4_5b: "\<turnstile> RPCFail crCh rmCh rst p \<and> $S5 rmhist p \<and> (S6 rmhist p)$
         \<and> unchanged (e p, c p, m p)
         \<longrightarrow> MemFail memCh (resbar rmhist) p"
  apply clarsimp
  apply (drule S6_excl [temp_use])
  apply (auto simp: e_def c_def m_def RPCFail_def AReturn_def MemFail_def resbar_def)
   apply (auto simp: S5_def S_def)
  done

lemma Step1_4_6a: "\<turnstile> MClkReply memCh crCh cst p \<and> $S6 rmhist p \<and> (S1 rmhist p)$
         \<and> unchanged (e p, r p, m p)
         \<longrightarrow> MemReturn memCh (resbar rmhist) p"
  apply clarsimp
  apply (drule S6_excl [temp_use])+
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm e_def},
    @{thm r_def}, @{thm m_def}, @{thm MClkReply_def}, @{thm MemReturn_def},
    @{thm AReturn_def}, @{thm resbar_def}]) [] [] 1\<close>)
    apply simp_all (* simplify if-then-else *)
    apply (tactic \<open>ALLGOALS (action_simp_tac (\<^context> addsimps
      [@{thm MClkReplyVal_def}, @{thm S6_def}, @{thm S_def}]) [] [@{thm MVOKBARFnotNR}])\<close>)
  done

lemma Step1_4_6b: "\<turnstile> MClkRetry memCh crCh cst p \<and> $S6 rmhist p \<and> (S3 rmhist p)$
         \<and> unchanged (e p, r p, m p, rmhist!p)
         \<longrightarrow> MemFail memCh (resbar rmhist) p"
  apply clarsimp
  apply (drule S3_excl [temp_use])+
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm e_def}, @{thm r_def},
    @{thm m_def}, @{thm MClkRetry_def}, @{thm MemFail_def}, @{thm resbar_def}]) [] [] 1\<close>)
   apply (auto simp: S6_def S_def)
  done

lemma S_lemma: "\<turnstile> unchanged (e p, c p, r p, m p, rmhist!p)
         \<longrightarrow> unchanged (S rmhist ec cc rc cs rs hs1 hs2 p)"
  by (auto simp: e_def c_def r_def m_def caller_def rtrner_def S_def Calling_def)

lemma Step1_4_7H: "\<turnstile> unchanged (e p, c p, r p, m p, rmhist!p)
         \<longrightarrow> unchanged (rtrner memCh!p, S1 rmhist p, S2 rmhist p, S3 rmhist p,
                        S4 rmhist p, S5 rmhist p, S6 rmhist p)"
  apply clarsimp
  apply (rule conjI)
   apply (force simp: c_def)
  apply (force simp: S1_def S2_def S3_def S4_def S5_def S6_def intro!: S_lemma [temp_use])
  done

lemma Step1_4_7: "\<turnstile> unchanged (e p, c p, r p, m p, rmhist!p)
         \<longrightarrow> unchanged (rtrner memCh!p, resbar rmhist!p, S1 rmhist p, S2 rmhist p,
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
ML \<open>
fun split_idle_tac ctxt =
  SELECT_GOAL
   (TRY (resolve_tac ctxt @{thms actionI} 1) THEN
    Induct_Tacs.case_tac ctxt "(s,t) \<Turnstile> unchanged (e p, c p, r p, m p, rmhist!p)" [] NONE 1 THEN
    rewrite_goals_tac ctxt @{thms action_rews} THEN
    forward_tac ctxt [temp_use ctxt @{thm Step1_4_7}] 1 THEN
    asm_full_simp_tac ctxt 1);
\<close>

method_setup split_idle = \<open>
  Method.sections (Simplifier.simp_modifiers @ Splitter.split_modifiers)
    >> (K (SIMPLE_METHOD' o split_idle_tac))
\<close>

(* ----------------------------------------------------------------------
   Combine steps 1.2 and 1.4 to prove that the implementation satisfies
   the specification's next-state relation.
*)

(* Steps that leave all variables unchanged are safe, so I may assume
   that some variable changes in the proof that a step is safe. *)
lemma unchanged_safe: "\<turnstile> (\<not>unchanged (e p, c p, r p, m p, rmhist!p)
             \<longrightarrow> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p))
         \<longrightarrow> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply (split_idle simp: square_def)
  apply force
  done
(* turn into (unsafe, looping!) introduction rule *)
lemmas unchanged_safeI = impI [THEN unchanged_safe [action_use]]

lemma S1safe: "\<turnstile> $S1 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (rule unchanged_safeI)
  apply (rule idle_squareI)
  apply (auto dest!: Step1_2_1 [temp_use] Step1_4_1 [temp_use])
  done

lemma S2safe: "\<turnstile> $S2 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (rule unchanged_safeI)
  apply (rule idle_squareI)
  apply (auto dest!: Step1_2_2 [temp_use] Step1_4_2 [temp_use])
  done

lemma S3safe: "\<turnstile> $S3 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (rule unchanged_safeI)
  apply (auto dest!: Step1_2_3 [temp_use])
  apply (auto simp: square_def UNext_def dest!: Step1_4_3a [temp_use] Step1_4_3b [temp_use])
  done

lemma S4safe: "\<turnstile> $S4 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<and> (\<forall>l. $(MemInv mm l))
         \<longrightarrow> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (rule unchanged_safeI)
  apply (auto dest!: Step1_2_4 [temp_use])
     apply (auto simp: square_def UNext_def RNext_def
       dest!: Step1_4_4a [temp_use] Step1_4_4b [temp_use] Step1_4_4c [temp_use])
  done

lemma S5safe: "\<turnstile> $S5 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  apply clarsimp
  apply (rule unchanged_safeI)
  apply (auto dest!: Step1_2_5 [temp_use])
  apply (auto simp: square_def UNext_def dest!: Step1_4_5a [temp_use] Step1_4_5b [temp_use])
  done

lemma S6safe: "\<turnstile> $S6 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
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

lemma S1_successors: "\<turnstile> $S1 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> (S1 rmhist p)$ \<or> (S2 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_1 [temp_use])
  done

(* Show that the implementation can satisfy the high-level fairness requirements
   by entering the state S1 infinitely often.
*)

lemma S1_RNextdisabled: "\<turnstile> S1 rmhist p \<longrightarrow>
         \<not>Enabled (<RNext memCh mm (resbar rmhist) p>_(rtrner memCh!p, resbar rmhist!p))"
  apply (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm angle_def},
    @{thm S_def}, @{thm S1_def}]) [notI] [@{thm enabledE}, temp_elim \<^context> @{thm Memoryidle}] 1\<close>)
  apply force
  done

lemma S1_Returndisabled: "\<turnstile> S1 rmhist p \<longrightarrow>
         \<not>Enabled (<MemReturn memCh (resbar rmhist) p>_(rtrner memCh!p, resbar rmhist!p))"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm angle_def}, @{thm MemReturn_def},
    @{thm AReturn_def}, @{thm S_def}, @{thm S1_def}]) [notI] [@{thm enabledE}] 1\<close>)

lemma RNext_fair: "\<turnstile> \<box>\<diamond>S1 rmhist p
         \<longrightarrow> WF(RNext memCh mm (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)"
  by (auto simp: WF_alt [try_rewrite] intro!: S1_RNextdisabled [temp_use]
    elim!: STL4E [temp_use] DmdImplE [temp_use])

lemma Return_fair: "\<turnstile> \<box>\<diamond>S1 rmhist p
         \<longrightarrow> WF(MemReturn memCh (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)"
  by (auto simp: WF_alt [try_rewrite]
    intro!: S1_Returndisabled [temp_use] elim!: STL4E [temp_use] DmdImplE [temp_use])

(* ------------------------------ State S2 ------------------------------ *)

lemma S2_successors: "\<turnstile> $S2 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> (S2 rmhist p)$ \<or> (S3 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_2 [temp_use])
  done

lemma S2MClkFwd_successors: "\<turnstile> ($S2 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         \<and> <MClkFwd memCh crCh cst p>_(c p)
         \<longrightarrow> (S3 rmhist p)$"
  by (auto simp: angle_def dest!: Step1_2_2 [temp_use])

lemma S2MClkFwd_enabled: "\<turnstile> $S2 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> $Enabled (<MClkFwd memCh crCh cst p>_(c p))"
  apply (auto simp: c_def intro!: MClkFwd_ch_enabled [temp_use] MClkFwd_enabled [temp_use])
     apply (cut_tac MI_base)
     apply (blast dest: base_pair)
    apply (simp_all add: S_def S2_def)
  done

lemma S2_live: "\<turnstile> \<box>(ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         \<and> WF(MClkFwd memCh crCh cst p)_(c p)
         \<longrightarrow> (S2 rmhist p \<leadsto> S3 rmhist p)"
  by (rule WF1 S2_successors S2MClkFwd_successors S2MClkFwd_enabled)+

(* ------------------------------ State S3 ------------------------------ *)

lemma S3_successors: "\<turnstile> $S3 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> (S3 rmhist p)$ \<or> (S4 rmhist p \<or> S6 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_3 [temp_use])
  done

lemma S3RPC_successors: "\<turnstile> ($S3 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         \<and> <RPCNext crCh rmCh rst p>_(r p)
         \<longrightarrow> (S4 rmhist p \<or> S6 rmhist p)$"
  apply (auto simp: angle_def dest!: Step1_2_3 [temp_use])
  done

lemma S3RPC_enabled: "\<turnstile> $S3 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> $Enabled (<RPCNext crCh rmCh rst p>_(r p))"
  apply (auto simp: r_def intro!: RPCFail_Next_enabled [temp_use] RPCFail_enabled [temp_use])
    apply (cut_tac MI_base)
    apply (blast dest: base_pair)
   apply (simp_all add: S_def S3_def)
  done

lemma S3_live: "\<turnstile> \<box>(ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         \<and> WF(RPCNext crCh rmCh rst p)_(r p)
         \<longrightarrow> (S3 rmhist p \<leadsto> S4 rmhist p \<or> S6 rmhist p)"
  by (rule WF1 S3_successors S3RPC_successors S3RPC_enabled)+

(* ------------- State S4 -------------------------------------------------- *)

lemma S4_successors: "\<turnstile> $S4 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
        \<and> (\<forall>l. $MemInv mm l)
        \<longrightarrow> (S4 rmhist p)$ \<or> (S5 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_4 [temp_use])
  done

(* --------- State S4a: S4 /\ (ires p = NotAResult) ------------------------ *)

lemma S4a_successors: "\<turnstile> $(S4 rmhist p \<and> ires!p = #NotAResult)
         \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p,rmhist!p) \<and> (\<forall>l. $MemInv mm l)
         \<longrightarrow> (S4 rmhist p \<and> ires!p = #NotAResult)$
             \<or> ((S4 rmhist p \<and> ires!p \<noteq> #NotAResult) \<or> S5 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_4 [temp_use])
  done

lemma S4aRNext_successors: "\<turnstile> ($(S4 rmhist p \<and> ires!p = #NotAResult)
         \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p,rmhist!p) \<and> (\<forall>l. $MemInv mm l))
         \<and> <RNext rmCh mm ires p>_(m p)
         \<longrightarrow> ((S4 rmhist p \<and> ires!p \<noteq> #NotAResult) \<or> S5 rmhist p)$"
  by (auto simp: angle_def
    dest!: Step1_2_4 [temp_use] ReadResult [temp_use] WriteResult [temp_use])

lemma S4aRNext_enabled: "\<turnstile> $(S4 rmhist p \<and> ires!p = #NotAResult)
         \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p) \<and> (\<forall>l. $MemInv mm l)
         \<longrightarrow> $Enabled (<RNext rmCh mm ires p>_(m p))"
  apply (auto simp: m_def intro!: RNext_enabled [temp_use])
   apply (cut_tac MI_base)
   apply (blast dest: base_pair)
  apply (simp add: S_def S4_def)
  done

lemma S4a_live: "\<turnstile> \<box>(ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<and> (\<forall>l. $MemInv mm l)) \<and> WF(RNext rmCh mm ires p)_(m p)
         \<longrightarrow> (S4 rmhist p \<and> ires!p = #NotAResult
              \<leadsto> (S4 rmhist p \<and> ires!p \<noteq> #NotAResult) \<or> S5 rmhist p)"
  by (rule WF1 S4a_successors S4aRNext_successors S4aRNext_enabled)+

(* ---------- State S4b: S4 /\ (ires p # NotAResult) --------------------------- *)

lemma S4b_successors: "\<turnstile> $(S4 rmhist p \<and> ires!p \<noteq> #NotAResult)
         \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p) \<and> (\<forall>l. $MemInv mm l)
         \<longrightarrow> (S4 rmhist p \<and> ires!p \<noteq> #NotAResult)$ \<or> (S5 rmhist p)$"
  apply (split_idle simp: m_def)
  apply (auto dest!: WriteResult [temp_use] Step1_2_4 [temp_use] ReadResult [temp_use])
  done

lemma S4bReturn_successors: "\<turnstile> ($(S4 rmhist p \<and> ires!p \<noteq> #NotAResult)
         \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<and> (\<forall>l. $MemInv mm l)) \<and> <MemReturn rmCh ires p>_(m p)
         \<longrightarrow> (S5 rmhist p)$"
  by (force simp: angle_def dest!: Step1_2_4 [temp_use] dest: ReturnNotReadWrite [temp_use])

lemma S4bReturn_enabled: "\<turnstile> $(S4 rmhist p \<and> ires!p \<noteq> #NotAResult)
         \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<and> (\<forall>l. $MemInv mm l)
         \<longrightarrow> $Enabled (<MemReturn rmCh ires p>_(m p))"
  apply (auto simp: m_def intro!: MemReturn_enabled [temp_use])
   apply (cut_tac MI_base)
   apply (blast dest: base_pair)
  apply (simp add: S_def S4_def)
  done

lemma S4b_live: "\<turnstile> \<box>(ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p) \<and> (\<forall>l. $MemInv mm l))
         \<and> WF(MemReturn rmCh ires p)_(m p)
         \<longrightarrow> (S4 rmhist p \<and> ires!p \<noteq> #NotAResult \<leadsto> S5 rmhist p)"
  by (rule WF1 S4b_successors S4bReturn_successors S4bReturn_enabled)+

(* ------------------------------ State S5 ------------------------------ *)

lemma S5_successors: "\<turnstile> $S5 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> (S5 rmhist p)$ \<or> (S6 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_5 [temp_use])
  done

lemma S5RPC_successors: "\<turnstile> ($S5 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         \<and> <RPCNext crCh rmCh rst p>_(r p)
         \<longrightarrow> (S6 rmhist p)$"
  by (auto simp: angle_def dest!: Step1_2_5 [temp_use])

lemma S5RPC_enabled: "\<turnstile> $S5 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> $Enabled (<RPCNext crCh rmCh rst p>_(r p))"
  apply (auto simp: r_def intro!: RPCFail_Next_enabled [temp_use] RPCFail_enabled [temp_use])
    apply (cut_tac MI_base)
    apply (blast dest: base_pair)
   apply (simp_all add: S_def S5_def)
  done

lemma S5_live: "\<turnstile> \<box>(ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         \<and> WF(RPCNext crCh rmCh rst p)_(r p)
         \<longrightarrow> (S5 rmhist p \<leadsto> S6 rmhist p)"
  by (rule WF1 S5_successors S5RPC_successors S5RPC_enabled)+

(* ------------------------------ State S6 ------------------------------ *)

lemma S6_successors: "\<turnstile> $S6 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p)
         \<longrightarrow> (S1 rmhist p)$ \<or> (S3 rmhist p)$ \<or> (S6 rmhist p)$"
  apply split_idle
  apply (auto dest!: Step1_2_6 [temp_use])
  done

lemma S6MClkReply_successors:
  "\<turnstile> ($S6 rmhist p \<and> ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p))
         \<and> <MClkReply memCh crCh cst p>_(c p)
         \<longrightarrow> (S1 rmhist p)$"
  by (auto simp: angle_def dest!: Step1_2_6 [temp_use] MClkReplyNotRetry [temp_use])

lemma MClkReplyS6:
  "\<turnstile> $ImpInv rmhist p \<and> <MClkReply memCh crCh cst p>_(c p) \<longrightarrow> $S6 rmhist p"
  by (tactic \<open>action_simp_tac (\<^context> addsimps [@{thm angle_def},
    @{thm MClkReply_def}, @{thm AReturn_def}, @{thm ImpInv_def}, @{thm S_def},
    @{thm S1_def}, @{thm S2_def}, @{thm S3_def}, @{thm S4_def}, @{thm S5_def}]) [] [] 1\<close>)

lemma S6MClkReply_enabled: "\<turnstile> S6 rmhist p \<longrightarrow> Enabled (<MClkReply memCh crCh cst p>_(c p))"
  apply (auto simp: c_def intro!: MClkReply_enabled [temp_use])
     apply (cut_tac MI_base)
     apply (blast dest: base_pair)
    apply (tactic \<open>ALLGOALS (action_simp_tac (\<^context>
      addsimps [@{thm S_def}, @{thm S6_def}]) [] [])\<close>)
  done

lemma S6_live: "\<turnstile> \<box>(ImpNext p \<and> [HNext rmhist p]_(c p,r p,m p, rmhist!p) \<and> $(ImpInv rmhist p))
         \<and> SF(MClkReply memCh crCh cst p)_(c p) \<and> \<box>\<diamond>(S6 rmhist p)
         \<longrightarrow> \<box>\<diamond>(S1 rmhist p)"
  apply clarsimp
  apply (subgoal_tac "sigma \<Turnstile> \<box>\<diamond> (<MClkReply memCh crCh cst p>_ (c p))")
   apply (erule InfiniteEnsures)
    apply assumption
   apply (tactic \<open>action_simp_tac \<^context> []
     (map (temp_elim \<^context>) [@{thm MClkReplyS6}, @{thm S6MClkReply_successors}]) 1\<close>)
  apply (auto simp: SF_def)
  apply (erule contrapos_np)
  apply (auto intro!: S6MClkReply_enabled [temp_use] elim!: STL4E [temp_use] DmdImplE [temp_use])
  done

(* --------------- aggregate leadsto properties----------------------------- *)

lemma S5S6LeadstoS6: "sigma \<Turnstile> S5 rmhist p \<leadsto> S6 rmhist p
      \<Longrightarrow> sigma \<Turnstile> (S5 rmhist p \<or> S6 rmhist p) \<leadsto> S6 rmhist p"
  by (auto intro!: LatticeDisjunctionIntro [temp_use] LatticeReflexivity [temp_use])

lemma S4bS5S6LeadstoS6: "\<lbrakk> sigma \<Turnstile> S4 rmhist p \<and> ires!p \<noteq> #NotAResult \<leadsto> S5 rmhist p;
         sigma \<Turnstile> S5 rmhist p \<leadsto> S6 rmhist p \<rbrakk>
      \<Longrightarrow> sigma \<Turnstile> (S4 rmhist p \<and> ires!p \<noteq> #NotAResult) \<or> S5 rmhist p \<or> S6 rmhist p
                    \<leadsto> S6 rmhist p"
  by (auto intro!: LatticeDisjunctionIntro [temp_use]
    S5S6LeadstoS6 [temp_use] intro: LatticeTransitivity [temp_use])

lemma S4S5S6LeadstoS6: "\<lbrakk> sigma \<Turnstile> S4 rmhist p \<and> ires!p = #NotAResult
                  \<leadsto> (S4 rmhist p \<and> ires!p \<noteq> #NotAResult) \<or> S5 rmhist p;
         sigma \<Turnstile> S4 rmhist p \<and> ires!p \<noteq> #NotAResult \<leadsto> S5 rmhist p;
         sigma \<Turnstile> S5 rmhist p \<leadsto> S6 rmhist p \<rbrakk>
      \<Longrightarrow> sigma \<Turnstile> S4 rmhist p \<or> S5 rmhist p \<or> S6 rmhist p \<leadsto> S6 rmhist p"
  apply (subgoal_tac "sigma \<Turnstile> (S4 rmhist p \<and> ires!p = #NotAResult) \<or>
    (S4 rmhist p \<and> ires!p \<noteq> #NotAResult) \<or> S5 rmhist p \<or> S6 rmhist p \<leadsto> S6 rmhist p")
   apply (erule_tac G = "PRED ((S4 rmhist p \<and> ires!p = #NotAResult) \<or>
     (S4 rmhist p \<and> ires!p \<noteq> #NotAResult) \<or> S5 rmhist p \<or> S6 rmhist p)" in
     LatticeTransitivity [temp_use])
   apply (force simp: Init_defs intro!: ImplLeadsto_gen [temp_use] necT [temp_use])
  apply (rule LatticeDisjunctionIntro [temp_use])
   apply (erule LatticeTransitivity [temp_use])
   apply (erule LatticeTriangle2 [temp_use])
   apply assumption
  apply (auto intro!: S4bS5S6LeadstoS6 [temp_use])
  done

lemma S3S4S5S6LeadstoS6: "\<lbrakk> sigma \<Turnstile> S3 rmhist p \<leadsto> S4 rmhist p \<or> S6 rmhist p;
         sigma \<Turnstile> S4 rmhist p \<and> ires!p = #NotAResult
                  \<leadsto> (S4 rmhist p \<and> ires!p \<noteq> #NotAResult) \<or> S5 rmhist p;
         sigma \<Turnstile> S4 rmhist p \<and> ires!p \<noteq> #NotAResult \<leadsto> S5 rmhist p;
         sigma \<Turnstile> S5 rmhist p \<leadsto> S6 rmhist p \<rbrakk>
      \<Longrightarrow> sigma \<Turnstile> S3 rmhist p \<or> S4 rmhist p \<or> S5 rmhist p \<or> S6 rmhist p \<leadsto> S6 rmhist p"
  apply (rule LatticeDisjunctionIntro [temp_use])
   apply (erule LatticeTriangle2 [temp_use])
   apply (rule S4S5S6LeadstoS6 [THEN LatticeTransitivity [temp_use]])
      apply (auto intro!: S4S5S6LeadstoS6 [temp_use] necT [temp_use]
        intro: ImplLeadsto_gen [temp_use] simp: Init_defs)
  done

lemma S2S3S4S5S6LeadstoS6: "\<lbrakk> sigma \<Turnstile> S2 rmhist p \<leadsto> S3 rmhist p;
         sigma \<Turnstile> S3 rmhist p \<leadsto> S4 rmhist p \<or> S6 rmhist p;
         sigma \<Turnstile> S4 rmhist p \<and> ires!p = #NotAResult
                  \<leadsto> S4 rmhist p \<and> ires!p \<noteq> #NotAResult \<or> S5 rmhist p;
         sigma \<Turnstile> S4 rmhist p \<and> ires!p \<noteq> #NotAResult \<leadsto> S5 rmhist p;
         sigma \<Turnstile> S5 rmhist p \<leadsto> S6 rmhist p \<rbrakk>
      \<Longrightarrow> sigma \<Turnstile> S2 rmhist p \<or> S3 rmhist p \<or> S4 rmhist p \<or> S5 rmhist p \<or> S6 rmhist p
                   \<leadsto> S6 rmhist p"
  apply (rule LatticeDisjunctionIntro [temp_use])
   apply (rule LatticeTransitivity [temp_use])
    prefer 2 apply assumption
   apply (rule S3S4S5S6LeadstoS6 [THEN LatticeTransitivity [temp_use]])
       apply (auto intro!: S3S4S5S6LeadstoS6 [temp_use] necT [temp_use]
         intro: ImplLeadsto_gen [temp_use] simp: Init_defs)
  done

lemma NotS1LeadstoS6: "\<lbrakk> sigma \<Turnstile> \<box>ImpInv rmhist p;
         sigma \<Turnstile> S2 rmhist p \<leadsto> S3 rmhist p;
         sigma \<Turnstile> S3 rmhist p \<leadsto> S4 rmhist p \<or> S6 rmhist p;
         sigma \<Turnstile> S4 rmhist p \<and> ires!p = #NotAResult
                  \<leadsto> S4 rmhist p \<and> ires!p \<noteq> #NotAResult \<or> S5 rmhist p;
         sigma \<Turnstile> S4 rmhist p \<and> ires!p \<noteq> #NotAResult \<leadsto> S5 rmhist p;
         sigma \<Turnstile> S5 rmhist p \<leadsto> S6 rmhist p \<rbrakk>
      \<Longrightarrow> sigma \<Turnstile> \<not>S1 rmhist p \<leadsto> S6 rmhist p"
  apply (rule S2S3S4S5S6LeadstoS6 [THEN LatticeTransitivity [temp_use]])
       apply assumption+
  apply (erule INV_leadsto [temp_use])
  apply (rule ImplLeadsto_gen [temp_use])
  apply (rule necT [temp_use])
  apply (auto simp: ImpInv_def Init_defs intro!: necT [temp_use])
  done

lemma S1Infinite: "\<lbrakk> sigma \<Turnstile> \<not>S1 rmhist p \<leadsto> S6 rmhist p;
         sigma \<Turnstile> \<box>\<diamond>S6 rmhist p \<longrightarrow> \<box>\<diamond>S1 rmhist p \<rbrakk>
      \<Longrightarrow> sigma \<Turnstile> \<box>\<diamond>S1 rmhist p"
  apply (rule classical)
  apply (tactic \<open>asm_lr_simp_tac (\<^context> addsimps
    [temp_use \<^context> @{thm NotBox}, temp_rewrite \<^context> @{thm NotDmd}]) 1\<close>)
  apply (auto elim!: leadsto_infinite [temp_use] mp dest!: DBImplBD [temp_use])
  done

section "Refinement proof (step 1.5)"

(* Prove invariants of the implementation:
   a. memory invariant
   b. "implementation invariant": always in states S1,...,S6
*)
lemma Step1_5_1a: "\<turnstile> IPImp p \<longrightarrow> (\<forall>l. \<box>$MemInv mm l)"
  by (auto simp: IPImp_def box_stp_act [temp_use] intro!: MemoryInvariantAll [temp_use])

lemma Step1_5_1b: "\<turnstile> Init(ImpInit p \<and> HInit rmhist p) \<and> \<box>(ImpNext p)
         \<and> \<box>[HNext rmhist p]_(c p, r p, m p, rmhist!p) \<and> \<box>(\<forall>l. $MemInv mm l)
         \<longrightarrow> \<box>ImpInv rmhist p"
  apply invariant
   apply (auto simp: Init_def ImpInv_def box_stp_act [temp_use]
     dest!: Step1_1 [temp_use] dest: S1_successors [temp_use] S2_successors [temp_use]
     S3_successors [temp_use] S4_successors [temp_use] S5_successors [temp_use]
     S6_successors [temp_use])
  done

(*** Initialization ***)
lemma Step1_5_2a: "\<turnstile> Init(ImpInit p \<and> HInit rmhist p) \<longrightarrow> Init(PInit (resbar rmhist) p)"
  by (auto simp: Init_def intro!: Step1_1 [temp_use] Step1_3  [temp_use])

(*** step simulation ***)
lemma Step1_5_2b: "\<turnstile> \<box>(ImpNext p \<and> [HNext rmhist p]_(c p, r p, m p, rmhist!p)
         \<and> $ImpInv rmhist p \<and> (\<forall>l. $MemInv mm l))
         \<longrightarrow> \<box>[UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
  by (auto simp: ImpInv_def elim!: STL4E [temp_use]
    dest!: S1safe [temp_use] S2safe [temp_use] S3safe [temp_use] S4safe [temp_use]
    S5safe [temp_use] S6safe [temp_use])

(*** Liveness ***)
lemma GoodImpl: "\<turnstile> IPImp p \<and> HistP rmhist p
         \<longrightarrow>   Init(ImpInit p \<and> HInit rmhist p)
             \<and> \<box>(ImpNext p \<and> [HNext rmhist p]_(c p, r p, m p, rmhist!p))
             \<and> \<box>(\<forall>l. $MemInv mm l) \<and> \<box>($ImpInv rmhist p)
             \<and> ImpLive p"
  apply clarsimp
    apply (subgoal_tac "sigma \<Turnstile> Init (ImpInit p \<and> HInit rmhist p) \<and> \<box> (ImpNext p) \<and>
      \<box>[HNext rmhist p]_ (c p, r p, m p, rmhist!p) \<and> \<box> (\<forall>l. $MemInv mm l)")
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
lemma Step1_5_3a: "\<turnstile> \<box>(ImpNext p \<and> [HNext rmhist p]_(c p, r p, m p, rmhist!p))
         \<and> \<box>(\<forall>l. $MemInv mm l)
         \<and> \<box>($ImpInv rmhist p) \<and> ImpLive p
         \<longrightarrow> \<box>\<diamond>S1 rmhist p"
  apply (clarsimp simp: ImpLive_def)
  apply (rule S1Infinite)
   apply (force simp: split_box_conj [try_rewrite] box_stp_act [try_rewrite]
     intro!: NotS1LeadstoS6 [temp_use] S2_live [temp_use] S3_live [temp_use]
     S4a_live [temp_use] S4b_live [temp_use] S5_live [temp_use])
  apply (auto simp: split_box_conj [temp_use] intro!: S6_live [temp_use])
  done

(* ... and therefore satisfies the fairness requirements of the specification *)
lemma Step1_5_3b: "\<turnstile> \<box>(ImpNext p \<and> [HNext rmhist p]_(c p, r p, m p, rmhist!p))
         \<and> \<box>(\<forall>l. $MemInv mm l) \<and> \<box>($ImpInv rmhist p) \<and> ImpLive p
         \<longrightarrow> WF(RNext memCh mm (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)"
  by (auto intro!: RNext_fair [temp_use] Step1_5_3a [temp_use])

lemma Step1_5_3c: "\<turnstile> \<box>(ImpNext p \<and> [HNext rmhist p]_(c p, r p, m p, rmhist!p))
         \<and> \<box>(\<forall>l. $MemInv mm l) \<and> \<box>($ImpInv rmhist p) \<and> ImpLive p
         \<longrightarrow> WF(MemReturn memCh (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)"
  by (auto intro!: Return_fair [temp_use] Step1_5_3a [temp_use])

(* QED step of step 1 *)
lemma Step1: "\<turnstile> IPImp p \<and> HistP rmhist p \<longrightarrow> UPSpec memCh mm (resbar rmhist) p"
  by (auto simp: UPSpec_def split_box_conj [temp_use]
    dest!: GoodImpl [temp_use] intro!: Step1_5_2a [temp_use] Step1_5_2b [temp_use]
    Step1_5_3b [temp_use] Step1_5_3c [temp_use])

(* ------------------------------ Step 2 ------------------------------ *)
section "Step 2"

lemma Step2_2a: "\<turnstile> Write rmCh mm ires p l \<and> ImpNext p
         \<and> [HNext rmhist p]_(c p, r p, m p, rmhist!p)
         \<and> $ImpInv rmhist p
         \<longrightarrow> (S4 rmhist p)$ \<and> unchanged (e p, c p, r p, rmhist!p)"
  apply clarsimp
  apply (drule WriteS4 [action_use])
   apply assumption
  apply split_idle
  apply (auto simp: ImpNext_def dest!: S4EnvUnch [temp_use] S4ClerkUnch [temp_use]
    S4RPCUnch [temp_use])
     apply (auto simp: square_def dest: S4Write [temp_use])
  done

lemma Step2_2: "\<turnstile>   (\<forall>p. ImpNext p)
         \<and> (\<forall>p. [HNext rmhist p]_(c p, r p, m p, rmhist!p))
         \<and> (\<forall>p. $ImpInv rmhist p)
         \<and> [\<exists>q. Write rmCh mm ires q l]_(mm!l)
         \<longrightarrow> [\<exists>q. Write memCh mm (resbar rmhist) q l]_(mm!l)"
  apply (auto intro!: squareCI elim!: squareE)
  apply (assumption | rule exI Step1_4_4b [action_use])+
    apply (force intro!: WriteS4 [temp_use])
   apply (auto dest!: Step2_2a [temp_use])
  done

lemma Step2_lemma: "\<turnstile> \<box>(  (\<forall>p. ImpNext p)
            \<and> (\<forall>p. [HNext rmhist p]_(c p, r p, m p, rmhist!p))
            \<and> (\<forall>p. $ImpInv rmhist p)
            \<and> [\<exists>q. Write rmCh mm ires q l]_(mm!l))
         \<longrightarrow> \<box>[\<exists>q. Write memCh mm (resbar rmhist) q l]_(mm!l)"
  by (force elim!: STL4E [temp_use] dest!: Step2_2 [temp_use])

lemma Step2: "\<turnstile> #l \<in> #MemLoc \<and> (\<forall>p. IPImp p \<and> HistP rmhist p)
         \<longrightarrow> MSpec memCh mm (resbar rmhist) l"
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
lemma Impl_IUSpec: "\<turnstile> Implementation \<and> Hist rmhist \<longrightarrow> IUSpec memCh mm (resbar rmhist)"
  by (auto simp: IUSpec_def Implementation_def IPImp_def MClkISpec_def
    RPCISpec_def IRSpec_def Hist_def intro!: Step1 [temp_use] Step2 [temp_use])

(* The main theorem: introduce hiding and eliminate history variable. *)
lemma Implementation: "\<turnstile> Implementation \<longrightarrow> USpec memCh"
  apply clarsimp
  apply (frule History [temp_use])
  apply (auto simp: USpec_def intro: eexI [temp_use] Impl_IUSpec [temp_use]
    MI_base [temp_use] elim!: eexE)
  done

end
