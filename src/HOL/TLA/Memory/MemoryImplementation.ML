(* 
    File:        MemoryImplementation.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: Memory implementation (ML file)

    The main theorem is theorem "Implementation" at the end of this file,
    which shows that the composition of a reliable memory, an RPC component, and
    a memory clerk implements an unreliable memory. The files "MIsafe.ML" and
    "MIlive.ML" contain lower-level lemmas for the safety and liveness parts.

    Steps are (roughly) numbered as in the hand proof.
*)

(* --------------------------- automatic prover --------------------------- *)

Delcongs [if_weak_cong];

val MI_css = (claset(), simpset());

(* A more aggressive variant that tries to solve subgoals by assumption
   or contradiction during the simplification.
   THIS IS UNSAFE, BECAUSE IT DOESN'T RECORD THE CHOICES!!
   (but it can be a lot faster than MI_css)
*)
val MI_fast_css =
  let 
    val (cs,ss) = MI_css
  in
    (cs addSEs [squareE], ss addSSolver (mk_solver "" (fn thms => assume_tac ORELSE' (etac notE))))
end;

val temp_elim = make_elim o temp_use;

(****************************** The history variable ******************************)
section "History variable";

Goal "|- Init(ALL p. ImpInit p) & [](ALL p. ImpNext p)  \
\        --> (EEX rmhist. Init(ALL p. HInit rmhist p) \
\                         & [](ALL p. [HNext rmhist p]_(c p, r p, m p, rmhist!p)))";
by (Clarsimp_tac 1);
by (rtac historyI 1); 
by (TRYALL atac); 
by (rtac MI_base 1);
by (action_simp_tac (simpset() addsimps [HInit_def]) [] [] 1);
by (etac fun_cong 1);
by (action_simp_tac (simpset() addsimps [HNext_def]) [busy_squareI] [] 1);
by (etac fun_cong 1);
qed "HistoryLemma";

Goal "|- Implementation --> (EEX rmhist. Hist rmhist)";
by (Clarsimp_tac 1);
by (rtac ((temp_use HistoryLemma) RS eex_mono) 1);
by (force_tac (MI_css 
               addsimps2 [Hist_def,HistP_def,Init_def,all_box,split_box_conj]) 3);
by (auto_tac (MI_css
              addsimps2 [Implementation_def,MClkISpec_def,RPCISpec_def,IRSpec_def,
                         MClkIPSpec_def,RPCIPSpec_def,RPSpec_def,
                         ImpInit_def,Init_def,ImpNext_def,
                         c_def,r_def,m_def,all_box,split_box_conj]));
qed "History";

(******************************** The safety part *********************************)

section "The safety part";

(* ------------------------- Include lower-level lemmas ------------------------- *)
use "MIsafe.ML";

section "Correctness of predicate-action diagram";


(* ========== Step 1.1 ================================================= *)
(* The implementation's initial condition implies the state predicate S1 *)

Goal "|- ImpInit p & HInit rmhist p --> S1 rmhist p";
by (auto_tac (MI_fast_css
              addsimps2 [MVNROKBA_def,MClkInit_def,RPCInit_def,PInit_def,
		         HInit_def,ImpInit_def,S_def,S1_def]));
qed "Step1_1";

(* ========== Step 1.2 ================================================== *)
(* Figure 16 is a predicate-action diagram for the implementation. *)

Goal "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p  \
\        & ~unchanged (e p, c p, r p, m p, rmhist!p)  & $S1 rmhist p \
\        --> (S2 rmhist p)$ & ENext p & unchanged (c p, r p, m p)";
by (action_simp_tac (simpset() addsimps [ImpNext_def]) []
                    (map temp_elim [S1ClerkUnch,S1RPCUnch,S1MemUnch,S1Hist]) 1);
by (auto_tac (MI_fast_css addSIs2 [S1Env]));
qed "Step1_2_1";

Goal "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p  \
\        & ~unchanged (e p, c p, r p, m p, rmhist!p) & $S2 rmhist p \
\        --> (S3 rmhist p)$ & MClkFwd memCh crCh cst p\
\            & unchanged (e p, r p, m p, rmhist!p)";
by (action_simp_tac (simpset() addsimps [ImpNext_def]) []
                    (map temp_elim [S2EnvUnch,S2RPCUnch,S2MemUnch,S2Hist]) 1);
by (auto_tac (MI_fast_css addSIs2 [S2Clerk,S2Forward]));
qed "Step1_2_2";

Goal "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p  \
\        & ~unchanged (e p, c p, r p, m p, rmhist!p) & $S3 rmhist p \
\        --> ((S4 rmhist p)$ & RPCFwd crCh rmCh rst p & unchanged (e p, c p, m p, rmhist!p)) \
\            | ((S6 rmhist p)$ & RPCFail crCh rmCh rst p & unchanged (e p, c p, m p))";
by (action_simp_tac (simpset() addsimps [ImpNext_def]) []
	            (map temp_elim [S3EnvUnch,S3ClerkUnch,S3MemUnch]) 1);
by (action_simp_tac (simpset()) [] 
                    (squareE::map temp_elim [S3RPC,S3Forward,S3Fail]) 1);
by (auto_tac (MI_css addDs2 [S3Hist]));
qed "Step1_2_3";

Goal "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p  \
\             & ~unchanged (e p, c p, r p, m p, rmhist!p) \
\             & $S4 rmhist p & (!l. $(MemInv mm l))     \
\        --> ((S4 rmhist p)$ & Read rmCh mm ires p & unchanged (e p, c p, r p, rmhist!p)) \
\            | ((S4 rmhist p)$ & (? l. Write rmCh mm ires p l) & unchanged (e p, c p, r p, rmhist!p)) \
\            | ((S5 rmhist p)$ & MemReturn rmCh ires p & unchanged (e p, c p, r p))";
by (action_simp_tac (simpset() addsimps [ImpNext_def]) []
                    (map temp_elim [S4EnvUnch,S4ClerkUnch,S4RPCUnch]) 1);
by (action_simp_tac (simpset() addsimps [RNext_def]) []
                    (squareE::map temp_elim [S4Read,S4Write,S4Return]) 1);
by (auto_tac (MI_css addDs2 [S4Hist]));
qed "Step1_2_4";

Goal "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p  \
\             & ~unchanged (e p, c p, r p, m p, rmhist!p) & $S5 rmhist p \
\        --> ((S6 rmhist p)$ & RPCReply crCh rmCh rst p & unchanged (e p, c p, m p)) \
\            | ((S6 rmhist p)$ & RPCFail crCh rmCh rst p & unchanged (e p, c p, m p))";
by (action_simp_tac (simpset() addsimps [ImpNext_def]) []
                    (map temp_elim [S5EnvUnch,S5ClerkUnch,S5MemUnch,S5Hist]) 1);
by (action_simp_tac (simpset()) [] [squareE, temp_elim S5RPC] 1);
by (auto_tac (MI_fast_css addSDs2 [S5Reply,S5Fail]));
qed "Step1_2_5";

Goal "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p  \
\             & ~unchanged (e p, c p, r p, m p, rmhist!p) & $S6 rmhist p \
\        --> ((S1 rmhist p)$ & MClkReply memCh crCh cst p & unchanged (e p, r p, m p))\
\            | ((S3 rmhist p)$ & MClkRetry memCh crCh cst p & unchanged (e p,r p,m p,rmhist!p))";
by (action_simp_tac (simpset() addsimps [ImpNext_def]) []
                    (map temp_elim [S6EnvUnch,S6RPCUnch,S6MemUnch]) 1);
by (action_simp_tac (simpset()) []
                    (squareE::map temp_elim [S6Clerk,S6Retry,S6Reply]) 1);
by (auto_tac (MI_css addDs2 [S6Hist]));
qed "Step1_2_6";

(* --------------------------------------------------------------------------
   Step 1.3: S1 implies the barred initial condition.
*)

section "Initialization (Step 1.3)";

Goal "|- S1 rmhist p --> PInit (resbar rmhist) p";
by (action_simp_tac (simpset() addsimps [resbar_def,PInit_def,S_def,S1_def])
                    [] [] 1);
qed "Step1_3";

(* ----------------------------------------------------------------------
   Step 1.4: Implementation's next-state relation simulates specification's
             next-state relation (with appropriate substitutions)
*)

section "Step simulation (Step 1.4)";

Goal "|- ENext p & $S1 rmhist p & (S2 rmhist p)$ & unchanged (c p, r p, m p) \
\        --> unchanged (rtrner memCh!p, resbar rmhist!p)";
by (auto_tac (MI_fast_css addsimps2 [c_def,r_def,m_def,resbar_def]));
qed "Step1_4_1";

Goal "|- MClkFwd memCh crCh cst p & $S2 rmhist p & (S3 rmhist p)$  \
\        & unchanged (e p, r p, m p, rmhist!p) \
\        --> unchanged (rtrner memCh!p, resbar rmhist!p)";
by (action_simp_tac
      (simpset() addsimps [MClkFwd_def, e_def, r_def, m_def, resbar_def,
                           S_def, S2_def, S3_def]) [] [] 1);
qed "Step1_4_2";

Goal "|- RPCFwd crCh rmCh rst p & $S3 rmhist p & (S4 rmhist p)$    \
\        & unchanged (e p, c p, m p, rmhist!p) \
\        --> unchanged (rtrner memCh!p, resbar rmhist!p)";
by (Clarsimp_tac 1);
by (REPEAT (dresolve_tac (map temp_use [S3_excl,S4_excl]) 1));
by (action_simp_tac 
      (simpset() addsimps [e_def,c_def,m_def,resbar_def,S_def, S3_def]) [] [] 1);
qed "Step1_4_3a";

Goal "|- RPCFail crCh rmCh rst p & $S3 rmhist p & (S6 rmhist p)$\
\        & unchanged (e p, c p, m p) \
\        --> MemFail memCh (resbar rmhist) p";
by (Clarsimp_tac 1);
by (dtac (temp_use S6_excl) 1);
by (auto_tac (MI_css addsimps2 [RPCFail_def,MemFail_def,e_def,c_def,m_def,
	                        resbar_def]));
by (force_tac (MI_css addsimps2 [S3_def,S_def]) 1);
by (auto_tac (MI_css addsimps2 [Return_def]));
qed "Step1_4_3b";

Goal "|- $S4 rmhist p & (S4 rmhist p)$ & ReadInner rmCh mm ires p l \
\        & unchanged (e p, c p, r p, rmhist!p) & $MemInv mm l \
\        --> ReadInner memCh mm (resbar rmhist) p l";
by (Clarsimp_tac 1);
by (REPEAT (dtac (temp_use S4_excl) 1));
by (action_simp_tac 
      (simpset() addsimps [ReadInner_def,GoodRead_def,BadRead_def,e_def,c_def,m_def]) 
      [] [] 1);
by (auto_tac (MI_css addsimps2 [resbar_def]));
by (ALLGOALS (action_simp_tac 
                (simpset() addsimps [RPCRelayArg_def,MClkRelayArg_def,
	                             S_def,S4_def,RdRequest_def,MemInv_def])
		[] [impE,MemValNotAResultE]));
qed "Step1_4_4a1";

Goal "|- Read rmCh mm ires p & $S4 rmhist p & (S4 rmhist p)$ \
\        & unchanged (e p, c p, r p, rmhist!p) & (!l. $(MemInv mm l)) \
\        --> Read memCh mm (resbar rmhist) p";
by (force_tac (MI_css addsimps2 [Read_def] addSEs2 [Step1_4_4a1]) 1);
qed "Step1_4_4a";

Goal "|- $S4 rmhist p & (S4 rmhist p)$ & WriteInner rmCh mm ires p l v   \
\        & unchanged (e p, c p, r p, rmhist!p) \
\        --> WriteInner memCh mm (resbar rmhist) p l v";
by (Clarsimp_tac 1);
by (REPEAT (dtac (temp_use S4_excl) 1));
by (action_simp_tac 
      (simpset() addsimps [WriteInner_def, GoodWrite_def, BadWrite_def,
		           e_def, c_def, m_def])
      [] [] 1);
by (auto_tac (MI_css addsimps2 [resbar_def]));
by (ALLGOALS (action_simp_tac
                (simpset() addsimps [RPCRelayArg_def,MClkRelayArg_def,
	                             S_def,S4_def,WrRequest_def])
		[] []));
qed "Step1_4_4b1";

Goal "|- Write rmCh mm ires p l & $S4 rmhist p & (S4 rmhist p)$   \
\        & unchanged (e p, c p, r p, rmhist!p) \
\        --> Write memCh mm (resbar rmhist) p l";
by (force_tac (MI_css addsimps2 [Write_def] addSEs2 [Step1_4_4b1]) 1);
qed "Step1_4_4b";

Goal "|- MemReturn rmCh ires p & $S4 rmhist p & (S5 rmhist p)$\
\        & unchanged (e p, c p, r p) \
\        --> unchanged (rtrner memCh!p, resbar rmhist!p)";
by (action_simp_tac
      (simpset() addsimps [e_def,c_def,r_def,resbar_def]) [] [] 1);
by (REPEAT (dresolve_tac [temp_use S4_excl, temp_use S5_excl] 1));
by (auto_tac (MI_fast_css addsimps2 [MemReturn_def,Return_def]));
qed "Step1_4_4c";

Goal "|- RPCReply crCh rmCh rst p & $S5 rmhist p & (S6 rmhist p)$\
\        & unchanged (e p, c p, m p) \
\        --> unchanged (rtrner memCh!p, resbar rmhist!p)";
by (Clarsimp_tac 1);
by (REPEAT (dresolve_tac [temp_use S5_excl, temp_use S6_excl] 1));
by (auto_tac (MI_css addsimps2 [e_def,c_def,m_def, resbar_def]));
by (auto_tac (MI_css addsimps2 [RPCReply_def,Return_def,S5_def,S_def] 
                     addSDs2 [MVOKBAnotRF]));
qed "Step1_4_5a";

Goal "|- RPCFail crCh rmCh rst p & $S5 rmhist p & (S6 rmhist p)$\
\        & unchanged (e p, c p, m p) \
\        --> MemFail memCh (resbar rmhist) p";
by (Clarsimp_tac 1);
by (dtac (temp_use S6_excl) 1);
by (auto_tac (MI_css addsimps2 [e_def, c_def, m_def, RPCFail_def, Return_def,
		 		MemFail_def, resbar_def]));
by (auto_tac (MI_css addsimps2 [S5_def,S_def]));
qed "Step1_4_5b";

Goal "|- MClkReply memCh crCh cst p & $S6 rmhist p & (S1 rmhist p)$\
\        & unchanged (e p, r p, m p) \
\        --> MemReturn memCh (resbar rmhist) p";
by (Clarsimp_tac 1);
by (dtac (temp_use S6_excl) 1);
by (action_simp_tac
      (simpset() addsimps [e_def,r_def,m_def,MClkReply_def,MemReturn_def,
		           Return_def,resbar_def]) [] [] 1);
by (ALLGOALS Asm_full_simp_tac);  (* simplify if-then-else *)
by (ALLGOALS (action_simp_tac
                (simpset() addsimps [MClkReplyVal_def,S6_def,S_def])
	        [] [MVOKBARFnotNR]));
qed "Step1_4_6a";

Goal "|- MClkRetry memCh crCh cst p & $S6 rmhist p & (S3 rmhist p)$   \
\        & unchanged (e p, r p, m p, rmhist!p) \
\        --> MemFail memCh (resbar rmhist) p";
by (Clarsimp_tac 1);
by (dtac (temp_use S3_excl) 1);
by (action_simp_tac
      (simpset() addsimps [e_def, r_def, m_def, MClkRetry_def, MemFail_def, resbar_def])
      [] [] 1);
by (auto_tac (MI_css addsimps2 [S6_def,S_def]));
qed "Step1_4_6b";

Goal "|- unchanged (e p, c p, r p, m p, rmhist!p) \
\        --> unchanged (S rmhist ec cc rc cs rs hs1 hs2 p)";
by (auto_tac (MI_css addsimps2 [e_def,c_def,r_def,m_def,caller_def,rtrner_def,
			        S_def,Calling_def]));
qed "S_lemma";

Goal "|- unchanged (e p, c p, r p, m p, rmhist!p) \
\        --> unchanged (rtrner memCh!p, S1 rmhist p, S2 rmhist p, S3 rmhist p, \
\                       S4 rmhist p, S5 rmhist p, S6 rmhist p)";
by (Clarsimp_tac 1);
by (rtac conjI 1);
by (force_tac (MI_css addsimps2 [c_def]) 1);
by (force_tac (MI_css addsimps2 [S1_def,S2_def,S3_def,S4_def,S5_def,S6_def]
                      addSIs2 [S_lemma]) 1);
qed "Step1_4_7H";

Goal "|- unchanged (e p, c p, r p, m p, rmhist!p) \
\        --> unchanged (rtrner memCh!p, resbar rmhist!p, S1 rmhist p, S2 rmhist p, \
\                       S3 rmhist p, S4 rmhist p, S5 rmhist p, S6 rmhist p)";
by (rtac actionI 1);
by (rewrite_goals_tac action_rews);
by (rtac impI 1);
by (forward_tac [temp_use Step1_4_7H] 1);
by (auto_tac (MI_css addsimps2 [e_def,c_def,r_def,m_def,rtrner_def,resbar_def]));
qed "Step1_4_7";

(* Frequently needed abbreviation: distinguish between idling and non-idling
   steps of the implementation, and try to solve the idling case by simplification
*)
fun split_idle_tac simps i = 
    EVERY [TRY (rtac actionI i),
	   case_tac "(s,t) |= unchanged (e p, c p, r p, m p, rmhist!p)" i,
	   rewrite_goals_tac action_rews,
	   forward_tac [temp_use Step1_4_7] i,
	   asm_full_simp_tac (simpset() addsimps simps) i
	  ];

(* ----------------------------------------------------------------------
   Combine steps 1.2 and 1.4 to prove that the implementation satisfies
   the specification's next-state relation.
*)

(* Steps that leave all variables unchanged are safe, so I may assume
   that some variable changes in the proof that a step is safe. *)
Goal "|- (~unchanged (e p, c p, r p, m p, rmhist!p) \
\            --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)) \
\        --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)";
by (split_idle_tac [square_def] 1);
by (Force_tac 1);
qed "unchanged_safe";
(* turn into (unsafe, looping!) introduction rule *)
bind_thm("unchanged_safeI", impI RS (action_use unchanged_safe));

Goal "|- $S1 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)   \
\        --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)";
by (Clarsimp_tac 1);
by (rtac unchanged_safeI 1);
by (rtac idle_squareI 1);
by (auto_tac (MI_css addSDs2 [Step1_2_1,Step1_4_1]));
qed "S1safe";

Goal "|- $S2 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)   \
\        --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)";
by (Clarsimp_tac 1);
by (rtac unchanged_safeI 1);
by (rtac idle_squareI 1);
by (auto_tac (MI_css addSDs2 [Step1_2_2,Step1_4_2]));
qed "S2safe";

Goal "|- $S3 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)   \
\        --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)";
by (Clarsimp_tac 1);
by (rtac unchanged_safeI 1);
by (auto_tac (MI_css addSDs2 [Step1_2_3]));
by (auto_tac (MI_css addsimps2 [square_def,UNext_def] addSDs2 [Step1_4_3a,Step1_4_3b]));
qed "S3safe";

Goal "|- $S4 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)  \
\        & (!l. $(MemInv mm l)) \
\        --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)";
by (Clarsimp_tac 1);
by (rtac unchanged_safeI 1);
by (auto_tac (MI_css addSDs2 [Step1_2_4]));
by (auto_tac (MI_css addsimps2 [square_def,UNext_def,RNext_def]
                     addSDs2 [Step1_4_4a,Step1_4_4b,Step1_4_4c]));
qed "S4safe";

Goal "|- $S5 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)  \
\        --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)";
by (Clarsimp_tac 1);
by (rtac unchanged_safeI 1);
by (auto_tac (MI_css addSDs2 [Step1_2_5]));
by (auto_tac (MI_css addsimps2 [square_def,UNext_def]
	             addSDs2 [Step1_4_5a,Step1_4_5b]));
qed "S5safe";

Goal "|- $S6 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)   \
\        --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)";
by (Clarsimp_tac 1);
by (rtac unchanged_safeI 1);
by (auto_tac (MI_css addSDs2 [Step1_2_6]));
by (auto_tac (MI_css addsimps2 [square_def,UNext_def,RNext_def]
	             addSDs2 [Step1_4_6a,Step1_4_6b]));
qed "S6safe";

(* ----------------------------------------------------------------------
   Step 1.5: Temporal refinement proof, based on previous steps.
*)

section "The liveness part";

(* Liveness assertions for the different implementation states, based on the
   fairness conditions. Prove subgoals of WF1 / SF1 rules as separate lemmas
   for readability. Reuse action proofs from safety part.
*)

(* ------------------------------ State S1 ------------------------------ *)

Goal "|- $S1 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)  \
\        --> (S1 rmhist p)$ | (S2 rmhist p)$";
by (split_idle_tac [] 1);
by (auto_tac (MI_css addSDs2 [Step1_2_1]));
qed "S1_successors";

(* Show that the implementation can satisfy the high-level fairness requirements
   by entering the state S1 infinitely often.
*)

Goal "|- S1 rmhist p --> \
\        ~Enabled (<RNext memCh mm (resbar rmhist) p>_(rtrner memCh!p, resbar rmhist!p))";
by (action_simp_tac (simpset() addsimps [angle_def,S_def,S1_def])
	            [notI] [enabledE,temp_elim Memoryidle] 1);
by (Force_tac 1);
qed "S1_RNextdisabled";

Goal "|- S1 rmhist p --> \
\        ~Enabled (<MemReturn memCh (resbar rmhist) p>_(rtrner memCh!p, resbar rmhist!p))";
by (action_simp_tac 
      (simpset() addsimps [angle_def,MemReturn_def,Return_def,S_def,S1_def])
      [notI] [enabledE] 1);
qed "S1_Returndisabled";

Goal "|- []<>S1 rmhist p   \
\        --> WF(RNext memCh mm (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)";
by (auto_tac (MI_css addsimps2 [WF_alt]
		     addSIs2 [S1_RNextdisabled] addSEs2 [STL4E,DmdImplE]));
qed "RNext_fair";

Goal "|- []<>S1 rmhist p   \
\        --> WF(MemReturn memCh (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)";
by (auto_tac (MI_css addsimps2 [WF_alt]
		     addSIs2 [S1_Returndisabled] addSEs2 [STL4E,DmdImplE]));
qed "Return_fair";

(* ------------------------------ State S2 ------------------------------ *)

Goal "|- $S2 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)   \
\        --> (S2 rmhist p)$ | (S3 rmhist p)$";
by (split_idle_tac [] 1);
by (auto_tac (MI_css addSDs2 [Step1_2_2]));
qed "S2_successors";

Goal "|- ($S2 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p))\
\        & <MClkFwd memCh crCh cst p>_(c p) \
\        --> (S3 rmhist p)$";
by (auto_tac (MI_css addsimps2 [angle_def] addSDs2 [Step1_2_2]));
qed "S2MClkFwd_successors";

Goal "|- $S2 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)\
\        --> $Enabled (<MClkFwd memCh crCh cst p>_(c p))";
by (auto_tac (MI_css addsimps2 [c_def] addSIs2 [MClkFwd_ch_enabled,MClkFwd_enabled]));
by (cut_facts_tac [MI_base] 1);
by (blast_tac (claset() addDs [base_pair]) 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [S_def,S2_def])));
qed "S2MClkFwd_enabled";

Goal "|- [](ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p))\
\        & WF(MClkFwd memCh crCh cst p)_(c p) \
\        --> (S2 rmhist p ~> S3 rmhist p)";
by (REPEAT (resolve_tac [WF1,S2_successors,
                         S2MClkFwd_successors,S2MClkFwd_enabled] 1));
qed "S2_live";

(* ------------------------------ State S3 ------------------------------ *)

Goal "|- $S3 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)\
\        --> (S3 rmhist p)$ | (S4 rmhist p | S6 rmhist p)$";
by (split_idle_tac [] 1);
by (auto_tac (MI_css addSDs2 [Step1_2_3]));
qed "S3_successors";

Goal "|- ($S3 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p))\
\        & <RPCNext crCh rmCh rst p>_(r p) \
\        --> (S4 rmhist p | S6 rmhist p)$";
by (auto_tac (MI_css addsimps2 [angle_def] addSDs2 [Step1_2_3]));
qed "S3RPC_successors";

Goal "|- $S3 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)\
\        --> $Enabled (<RPCNext crCh rmCh rst p>_(r p))";
by (auto_tac (MI_css addsimps2 [r_def]
		     addSIs2 [RPCFail_Next_enabled,RPCFail_enabled]));
by (cut_facts_tac [MI_base] 1);
by (blast_tac (claset() addDs [base_pair]) 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [S_def,S3_def])));
qed "S3RPC_enabled";

Goal "|- [](ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p))\
\        & WF(RPCNext crCh rmCh rst p)_(r p) \
\        --> (S3 rmhist p ~> S4 rmhist p | S6 rmhist p)";
by (REPEAT (resolve_tac [WF1,S3_successors,S3RPC_successors,S3RPC_enabled] 1));
qed "S3_live";

(* ------------- State S4 -------------------------------------------------- *)

Goal"|- $S4 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) \
\       & (ALL l. $MemInv mm l)  \
\       --> (S4 rmhist p)$ | (S5 rmhist p)$";
by (split_idle_tac [] 1);
by (auto_tac (MI_css addSDs2 [Step1_2_4]));
qed "S4_successors";

(* --------- State S4a: S4 /\ (ires p = NotAResult) ------------------------ *)

Goal "|- $(S4 rmhist p & ires!p = #NotAResult) \
\        & ImpNext p & [HNext rmhist p]_(c p,r p,m p,rmhist!p) & (ALL l. $MemInv mm l)\
\        --> (S4 rmhist p & ires!p = #NotAResult)$  \
\            | ((S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p)$";
by (split_idle_tac [m_def] 1);
by (auto_tac (MI_css addSDs2 [Step1_2_4]));
qed "S4a_successors";

Goal "|- ($(S4 rmhist p & ires!p = #NotAResult)  \
\        & ImpNext p & [HNext rmhist p]_(c p,r p,m p,rmhist!p) & (ALL l. $MemInv mm l))\
\        & <RNext rmCh mm ires p>_(m p) \
\        --> ((S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p)$";
by (auto_tac (MI_css addsimps2 [angle_def]
		     addSDs2 [Step1_2_4, ReadResult, WriteResult]));
qed "S4aRNext_successors";

Goal "|- $(S4 rmhist p & ires!p = #NotAResult) \
\        & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) & (ALL l. $MemInv mm l)\
\        --> $Enabled (<RNext rmCh mm ires p>_(m p))";
by (auto_tac (MI_css addsimps2 [m_def] addSIs2 [RNext_enabled]));
by (cut_facts_tac [MI_base] 1);
by (blast_tac (claset() addDs [base_pair]) 1);
by (asm_full_simp_tac (simpset() addsimps [S_def,S4_def]) 1);
qed "S4aRNext_enabled";

Goal "|- [](ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)\
\        & (ALL l. $MemInv mm l)) & WF(RNext rmCh mm ires p)_(m p) \
\        --> (S4 rmhist p & ires!p = #NotAResult  \
\             ~> (S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p)";
by (REPEAT (resolve_tac [WF1, S4a_successors, S4aRNext_successors, S4aRNext_enabled] 1));
qed "S4a_live";

(* ---------- State S4b: S4 /\ (ires p # NotAResult) --------------------------- *)

Goal "|- $(S4 rmhist p & ires!p ~= #NotAResult)  \
\        & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) & (ALL l. $MemInv mm l)\
\        --> (S4 rmhist p & ires!p ~= #NotAResult)$ | (S5 rmhist p)$";
by (split_idle_tac [m_def] 1);
by (auto_tac (MI_css addSDs2 [WriteResult,Step1_2_4,ReadResult]));
qed "S4b_successors";

Goal "|- ($(S4 rmhist p & ires!p ~= #NotAResult)  \
\        & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) \
\        & (ALL l. $MemInv mm l)) & <MemReturn rmCh ires p>_(m p) \
\        --> (S5 rmhist p)$";
by (force_tac (MI_css addsimps2 [angle_def] addSDs2 [Step1_2_4]
                      addDs2 [ReturnNotReadWrite]) 1);
qed "S4bReturn_successors";

Goal "|- $(S4 rmhist p & ires!p ~= #NotAResult)  \
\        & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)\
\        & (ALL l. $MemInv mm l)  \
\        --> $Enabled (<MemReturn rmCh ires p>_(m p))";
by (auto_tac (MI_css addsimps2 [m_def] addSIs2 [MemReturn_enabled]));
by (cut_facts_tac [MI_base] 1);
by (blast_tac (claset() addDs [base_pair]) 1);
by (asm_full_simp_tac (simpset() addsimps [S_def,S4_def]) 1);
qed "S4bReturn_enabled";

Goal "|- [](ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) & (!l. $MemInv mm l)) \
\        & WF(MemReturn rmCh ires p)_(m p) \
\        --> (S4 rmhist p & ires!p ~= #NotAResult ~> S5 rmhist p)";
by (REPEAT (resolve_tac [WF1, S4b_successors,S4bReturn_successors, S4bReturn_enabled] 1));
qed "S4b_live";

(* ------------------------------ State S5 ------------------------------ *)

Goal "|- $S5 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) \
\        --> (S5 rmhist p)$ | (S6 rmhist p)$";
by (split_idle_tac [] 1);
by (auto_tac (MI_css addSDs2 [Step1_2_5]));
qed "S5_successors";

Goal "|- ($S5 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)) \
\        & <RPCNext crCh rmCh rst p>_(r p) \
\        --> (S6 rmhist p)$";
by (auto_tac (MI_css addsimps2 [angle_def] addSDs2 [Step1_2_5]));
qed "S5RPC_successors";

Goal "|- $S5 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) \
\        --> $Enabled (<RPCNext crCh rmCh rst p>_(r p))";
by (auto_tac (MI_css addsimps2 [r_def]
		     addSIs2 [RPCFail_Next_enabled, RPCFail_enabled]));
by (cut_facts_tac [MI_base] 1);
by (blast_tac (claset() addDs [base_pair]) 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [S_def,S5_def])));
qed "S5RPC_enabled";

Goal "|- [](ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p))\
\        & WF(RPCNext crCh rmCh rst p)_(r p) \
\        --> (S5 rmhist p ~> S6 rmhist p)";
by (REPEAT (resolve_tac [WF1,S5_successors,S5RPC_successors,S5RPC_enabled] 1));
qed "S5_live";

(* ------------------------------ State S6 ------------------------------ *)

Goal "|- $S6 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) \
\        --> (S1 rmhist p)$ | (S3 rmhist p)$ | (S6 rmhist p)$";
by (split_idle_tac [] 1);
by (auto_tac (MI_css addSDs2 [Step1_2_6]));
qed "S6_successors";

Goal "|- ($S6 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)) \
\        & <MClkReply memCh crCh cst p>_(c p) \
\        --> (S1 rmhist p)$";
by (auto_tac (MI_css addsimps2 [angle_def] addSDs2 [Step1_2_6, MClkReplyNotRetry]));
qed "S6MClkReply_successors";

Goal "|- $ImpInv rmhist p & <MClkReply memCh crCh cst p>_(c p) --> $S6 rmhist p";
by (action_simp_tac
      (simpset() addsimps [angle_def,MClkReply_def,Return_def,
		     ImpInv_def,S_def,S1_def,S2_def,S3_def,S4_def,S5_def])
      [] [] 1);
qed "MClkReplyS6";

Goal "|- S6 rmhist p --> Enabled (<MClkReply memCh crCh cst p>_(c p))";
by (auto_tac (MI_css addsimps2 [c_def] addSIs2 [MClkReply_enabled]));
by (cut_facts_tac [MI_base] 1);
by (blast_tac (claset() addDs [base_pair]) 1);
by (ALLGOALS (action_simp_tac (simpset() addsimps [S_def,S6_def]) [] []));
qed "S6MClkReply_enabled";

Goal "|- [](ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p) & $(ImpInv rmhist p))\
\        & SF(MClkReply memCh crCh cst p)_(c p) & []<>(S6 rmhist p)  \
\        --> []<>(S1 rmhist p)";
by (Clarsimp_tac 1);
by (subgoal_tac "sigma |= []<>(<MClkReply memCh crCh cst p>_(c p))" 1);
by (etac InfiniteEnsures 1); 
by (atac 1);
by (action_simp_tac (simpset()) []
	            (map temp_elim [MClkReplyS6,S6MClkReply_successors]) 1);
by (auto_tac (MI_css addsimps2 [SF_def]));
by (etac contrapos_np 1);
by (auto_tac (MI_css addSIs2 [S6MClkReply_enabled] addSEs2 [STL4E, DmdImplE]));
qed "S6_live";

(* --------------- aggregate leadsto properties----------------------------- *)

Goal "sigma |= S5 rmhist p ~> S6 rmhist p \
\     ==> sigma |= (S5 rmhist p | S6 rmhist p) ~> S6 rmhist p";
by (auto_tac (MI_css addSIs2 [LatticeDisjunctionIntro, LatticeReflexivity]));
qed "S5S6LeadstoS6";

Goal "[| sigma |= S4 rmhist p & ires!p ~= #NotAResult ~> S5 rmhist p;\
\        sigma |= S5 rmhist p ~> S6 rmhist p |]  \
\     ==> sigma |= (S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p | S6 rmhist p \
\                   ~> S6 rmhist p";
by (auto_tac (MI_css addSIs2 [LatticeDisjunctionIntro,S5S6LeadstoS6]
		     addIs2 [LatticeTransitivity]));
qed "S4bS5S6LeadstoS6";

Goal "[| sigma |= S4 rmhist p & ires!p = #NotAResult \
\                 ~> (S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p; \
\        sigma |= S4 rmhist p & ires!p ~= #NotAResult ~> S5 rmhist p;  \
\        sigma |= S5 rmhist p ~> S6 rmhist p |]  \
\     ==> sigma |= S4 rmhist p | S5 rmhist p | S6 rmhist p ~> S6 rmhist p";
by (subgoal_tac 
     "sigma |= (S4 rmhist p & ires!p = #NotAResult)\
\            | (S4 rmhist p & ires!p ~= #NotAResult)\
\            | S5 rmhist p | S6 rmhist p ~> S6 rmhist p" 1);
 by (eres_inst_tac 
      [("G", "PRED ((S4 rmhist p & ires!p = #NotAResult)\
\                | (S4 rmhist p & ires!p ~= #NotAResult)\
\                | S5 rmhist p | S6 rmhist p)")] 
      (temp_use LatticeTransitivity) 1);
 by (force_tac (MI_css addsimps2 Init_defs addSIs2 [ImplLeadsto_gen, necT]) 1);
by (rtac (temp_use LatticeDisjunctionIntro) 1);
by (etac (temp_use LatticeTransitivity) 1);
by (etac (temp_use LatticeTriangle2) 1); 
by (atac 1);
by (auto_tac (MI_css addSIs2 [S4bS5S6LeadstoS6]));
qed "S4S5S6LeadstoS6";

Goal "[| sigma |= S3 rmhist p ~> S4 rmhist p | S6 rmhist p;   \
\        sigma |= S4 rmhist p & ires!p = #NotAResult \
\                 ~> (S4 rmhist p & ires!p ~= #NotAResult) | S5 rmhist p; \
\        sigma |= S4 rmhist p & ires!p ~= #NotAResult ~> S5 rmhist p;  \
\        sigma |= S5 rmhist p ~> S6 rmhist p |]  \
\     ==> sigma |= S3 rmhist p | S4 rmhist p | S5 rmhist p | S6 rmhist p ~> S6 rmhist p";
by (rtac (temp_use LatticeDisjunctionIntro) 1);
by (etac (temp_use LatticeTriangle2) 1);
by (rtac (S4S5S6LeadstoS6 RS (temp_use LatticeTransitivity)) 1);
by (auto_tac (MI_css addSIs2 [S4S5S6LeadstoS6,necT]
	             addIs2 [ImplLeadsto_gen] addsimps2 Init_defs));
qed "S3S4S5S6LeadstoS6";

Goal "[| sigma |= S2 rmhist p ~> S3 rmhist p; \
\        sigma |= S3 rmhist p ~> S4 rmhist p | S6 rmhist p;   \
\        sigma |= S4 rmhist p & ires!p = #NotAResult \
\                 ~> S4 rmhist p & ires!p ~= #NotAResult | S5 rmhist p; \
\        sigma |= S4 rmhist p & ires!p ~= #NotAResult ~> S5 rmhist p;  \
\        sigma |= S5 rmhist p ~> S6 rmhist p |]  \
\     ==> sigma |= S2 rmhist p | S3 rmhist p | S4 rmhist p | S5 rmhist p | S6 rmhist p \
\                  ~> S6 rmhist p";
by (rtac (temp_use LatticeDisjunctionIntro) 1);
by (rtac (temp_use LatticeTransitivity) 1); 
by (atac 2);
by (rtac (S3S4S5S6LeadstoS6 RS (temp_use LatticeTransitivity)) 1);
by (auto_tac (MI_css addSIs2 [S3S4S5S6LeadstoS6,necT]
	             addIs2 [ImplLeadsto_gen] addsimps2 Init_defs));
qed "S2S3S4S5S6LeadstoS6";

Goal "[| sigma |= []ImpInv rmhist p; \
\        sigma |= S2 rmhist p ~> S3 rmhist p; \
\        sigma |= S3 rmhist p ~> S4 rmhist p | S6 rmhist p; \
\        sigma |= S4 rmhist p & ires!p = #NotAResult \
\                 ~> S4 rmhist p & ires!p ~= #NotAResult | S5 rmhist p; \
\        sigma |= S4 rmhist p & ires!p ~= #NotAResult ~> S5 rmhist p;  \
\        sigma |= S5 rmhist p ~> S6 rmhist p |] \
\     ==> sigma |= ~S1 rmhist p ~> S6 rmhist p";
by (rtac (S2S3S4S5S6LeadstoS6 RS (temp_use LatticeTransitivity)) 1);
by (TRYALL atac);
by (etac (temp_use INV_leadsto) 1);
by (rtac (temp_use ImplLeadsto_gen) 1);
by (rtac (temp_use necT) 1);
by (auto_tac (MI_css addsimps2 ImpInv_def::Init_defs addSIs2 [necT]));
qed "NotS1LeadstoS6";

Goal "[| sigma |= ~S1 rmhist p ~> S6 rmhist p; \
\        sigma |= []<>S6 rmhist p --> []<>S1 rmhist p |] \
\     ==> sigma |= []<>S1 rmhist p";
by (rtac classical 1);
by (asm_lr_simp_tac (simpset() addsimps [temp_use NotBox, NotDmd]) 1);
by (auto_tac (MI_css addSEs2 [mp,leadsto_infinite] addSDs2 [DBImplBD]));
qed "S1Infinite";

section "Refinement proof (step 1.5)";

(* Prove invariants of the implementation:
   a. memory invariant
   b. "implementation invariant": always in states S1,...,S6
*)
Goal "|- IPImp p --> (ALL l. []$MemInv mm l)";
by (auto_tac (MI_css addsimps2 [IPImp_def,box_stp_act]
	             addSIs2 [MemoryInvariantAll]));
qed "Step1_5_1a";

Goal "|- Init(ImpInit p & HInit rmhist p) & [](ImpNext p) \
\        & [][HNext rmhist p]_(c p, r p, m p, rmhist!p) & [](ALL l. $MemInv mm l) \
\        --> []ImpInv rmhist p";
by (inv_tac MI_css 1);
by (auto_tac (MI_css addsimps2 [Init_def, ImpInv_def, box_stp_act]
                     addSDs2 [Step1_1]
	             addDs2 [S1_successors,S2_successors,S3_successors,
		             S4_successors,S5_successors,S6_successors]));
qed "Step1_5_1b";

(*** Initialization ***)
Goal "|- Init(ImpInit p & HInit rmhist p) --> Init(PInit (resbar rmhist) p)";
by (auto_tac (MI_css addsimps2 [Init_def] addSIs2 [Step1_1,Step1_3]));
qed "Step1_5_2a";

(*** step simulation ***)
Goal "|- [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p)   \
\        & $ImpInv rmhist p & (!l. $MemInv mm l)) \
\        --> [][UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)";
by (auto_tac (MI_css addsimps2 [ImpInv_def] addSEs2 [STL4E]
                     addSDs2 [S1safe,S2safe,S3safe,S4safe,S5safe,S6safe]));
qed "Step1_5_2b";

(*** Liveness ***)
Goal "|- IPImp p & HistP rmhist p  \
\        -->   Init(ImpInit p & HInit rmhist p)   \
\            & [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p)) \
\            & [](ALL l. $MemInv mm l) & []($ImpInv rmhist p) \
\            & ImpLive p";
by (Clarsimp_tac 1);
by (subgoal_tac
      "sigma |= Init(ImpInit p & HInit rmhist p) \
\             & [](ImpNext p) \
\             & [][HNext rmhist p]_(c p, r p, m p, rmhist!p) \
\             & [](ALL l. $MemInv mm l)" 1);
by (auto_tac (MI_css addsimps2 [split_box_conj,box_stp_act] addSDs2 [Step1_5_1b]));
by (force_tac (MI_css addsimps2 [IPImp_def,MClkIPSpec_def,RPCIPSpec_def,RPSpec_def,
				 ImpLive_def,c_def,r_def,m_def]) 1);
by (force_tac (MI_css addsimps2 [IPImp_def,MClkIPSpec_def,RPCIPSpec_def,RPSpec_def,
	                         HistP_def,Init_def,ImpInit_def]) 1);
by (force_tac (MI_css addsimps2 [IPImp_def,MClkIPSpec_def,RPCIPSpec_def,RPSpec_def,
                                 ImpNext_def,c_def,r_def,m_def,split_box_conj]) 1);
by (force_tac (MI_css addsimps2 [HistP_def]) 1);
by (force_tac (MI_css addsimps2 [temp_use allT] addSDs2 [Step1_5_1a]) 1);
qed "GoodImpl";

(* The implementation is infinitely often in state S1... *)
Goal "|- [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p)) \
\        & [](ALL l. $MemInv mm l)  \
\        & []($ImpInv rmhist p) & ImpLive p  \
\        --> []<>S1 rmhist p";
by (clarsimp_tac (MI_css addsimps2 [ImpLive_def]) 1);
by (rtac S1Infinite 1);
by (force_tac
      (MI_css addsimps2 [split_box_conj,box_stp_act]
              addSIs2 [NotS1LeadstoS6,S2_live,S3_live,S4a_live,S4b_live,S5_live]) 1);
by (auto_tac (MI_css addsimps2 [split_box_conj] addSIs2 [S6_live]));
qed "Step1_5_3a";

(* ... and therefore satisfies the fairness requirements of the specification *)
Goal "|- [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p)) \
\        & [](ALL l. $MemInv mm l) & []($ImpInv rmhist p) & ImpLive p  \
\        --> WF(RNext memCh mm (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)";
by (auto_tac (MI_css addSIs2 [RNext_fair,Step1_5_3a]));
qed "Step1_5_3b";

Goal "|- [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p)) \
\        & [](ALL l. $MemInv mm l) & []($ImpInv rmhist p) & ImpLive p  \
\        --> WF(MemReturn memCh (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)";
by (auto_tac (MI_css addSIs2 [Return_fair,Step1_5_3a]));
qed "Step1_5_3c";

(* QED step of step 1 *)
Goal "|- IPImp p & HistP rmhist p --> UPSpec memCh mm (resbar rmhist) p";
by (auto_tac (MI_css addsimps2 [UPSpec_def,split_box_conj]
		     addSDs2 [GoodImpl]
                     addSIs2 [Step1_5_2a,Step1_5_2b,Step1_5_3b,Step1_5_3c]));
qed "Step1";

(* ------------------------------ Step 2 ------------------------------ *)
section "Step 2";

Goal "|- Write rmCh mm ires p l & ImpNext p\
\        & [HNext rmhist p]_(c p, r p, m p, rmhist!p) \
\        & $ImpInv rmhist p  \
\        --> (S4 rmhist p)$ & unchanged (e p, c p, r p, rmhist!p)";
by (Clarsimp_tac 1);
by (dtac (action_use WriteS4) 1); 
by (atac 1);
by (split_idle_tac [] 1);
by (auto_tac (MI_css addsimps2 [ImpNext_def] 
                     addSDs2 [S4EnvUnch,S4ClerkUnch,S4RPCUnch]));
by (auto_tac (MI_css addsimps2 [square_def] addDs2 [S4Write]));
qed "Step2_2a";

Goal "|-   (ALL p. ImpNext p) \
\        & (ALL p. [HNext rmhist p]_(c p, r p, m p, rmhist!p)) \
\        & (ALL p. $ImpInv rmhist p) \
\        & [EX q. Write rmCh mm ires q l]_(mm!l) \
\        --> [EX q. Write memCh mm (resbar rmhist) q l]_(mm!l)";
by (auto_tac (MI_css addSIs2 [squareCI] addSEs2 [squareE]));
by (REPEAT (ares_tac [exI, action_use Step1_4_4b] 1));
by (force_tac (MI_css addSIs2 [WriteS4]) 1);
by (auto_tac (MI_css addSDs2 [Step2_2a]));
qed "Step2_2";

Goal "|- [](  (ALL p. ImpNext p) \
\           & (ALL p. [HNext rmhist p]_(c p, r p, m p, rmhist!p)) \
\           & (ALL p. $ImpInv rmhist p) \
\           & [EX q. Write rmCh mm ires q l]_(mm!l)) \
\        --> [][EX q. Write memCh mm (resbar rmhist) q l]_(mm!l)";
by (force_tac (MI_css addSEs2 [STL4E] addSDs2 [Step2_2]) 1);
qed "Step2_lemma";

Goal "|- #l : #MemLoc & (ALL p. IPImp p & HistP rmhist p)  \
\        --> MSpec memCh mm (resbar rmhist) l";
by (auto_tac (MI_css addsimps2 [MSpec_def]));
by (force_tac (MI_css addsimps2 [IPImp_def,MSpec_def]) 1);
by (auto_tac (MI_css addSIs2 [Step2_lemma]
	             addsimps2 [split_box_conj,all_box]));
by (force_tac (MI_css addsimps2 [IPImp_def,MSpec_def]) 4);
by (auto_tac (MI_css addsimps2 [split_box_conj] addSEs2 [allE] addSDs2 [GoodImpl]));
qed "Step2";

(* ----------------------------- Main theorem --------------------------------- *)
section "Memory implementation";

(* The combination of a legal caller, the memory clerk, the RPC component,
   and a reliable memory implement the unreliable memory.
*)

(* Implementation of internal specification by combination of implementation
   and history variable with explicit refinement mapping
*)
Goal "|- Implementation & Hist rmhist --> IUSpec memCh mm (resbar rmhist)";
by (auto_tac (MI_css addsimps2 [IUSpec_def,Implementation_def,IPImp_def,
			        MClkISpec_def,RPCISpec_def,IRSpec_def,Hist_def]
		     addSIs2 [Step1,Step2]));
qed "Impl_IUSpec";

(* The main theorem: introduce hiding and eliminate history variable. *)
Goal "|- Implementation --> USpec memCh";
by (Clarsimp_tac 1);
by (forward_tac [temp_use History] 1);
by (auto_tac (MI_css addsimps2 [USpec_def] 
                     addIs2 [eexI, Impl_IUSpec, MI_base]
                     addSEs2 [eexE]));
qed "Implementation";
