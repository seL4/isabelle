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
    (cs addSEs [squareE], ss addSSolver (fn thms => assume_tac ORELSE' (etac notE)))
end;

val temp_elim = make_elim o temp_use;

(****************************** The history variable ******************************)
section "History variable";

qed_goal "HistoryLemma" MemoryImplementation.thy
   "|- Init(!p. ImpInit p) & [](!p. ImpNext p)  \
\      --> (EEX rmhist. Init(! p. HInit rmhist p) \
\                     & [](!p. [HNext rmhist p]_(c p, r p, m p, rmhist!p)))"
   (fn _ => [Clarsimp_tac 1,
             rtac historyI 1, TRYALL atac, rtac MI_base 1,
             action_simp_tac (simpset() addsimps [HInit_def]) [] [] 1,
             etac fun_cong 1,
             action_simp_tac (simpset() addsimps [HNext_def]) [busy_squareI] [] 1,
             etac fun_cong 1
            ]);

qed_goal "History" MemoryImplementation.thy
   "|- Implementation --> (EEX rmhist. Hist rmhist)"
   (fn _ => [Clarsimp_tac 1,
             rtac ((temp_use HistoryLemma) RS eex_mono) 1,
             force_tac (MI_css 
                        addsimps2 [Hist_def,HistP_def,Init_def,all_box,split_box_conj]) 3,
             auto_tac (MI_css
                       addsimps2 [Implementation_def,MClkISpec_def,RPCISpec_def,IRSpec_def,
                                  MClkIPSpec_def,RPCIPSpec_def,RPSpec_def,
                                  ImpInit_def,Init_def,ImpNext_def,
                                  c_def,r_def,m_def,all_box,split_box_conj])
            ]);

(******************************** The safety part *********************************)

section "The safety part";

(* ------------------------- Include lower-level lemmas ------------------------- *)
use "MIsafe.ML";

section "Correctness of predicate-action diagram";


(* ========== Step 1.1 ================================================= *)
(* The implementation's initial condition implies the state predicate S1 *)

qed_goal "Step1_1" MemoryImplementation.thy
   "|- ImpInit p & HInit rmhist p --> S1 rmhist p"
   (fn _ => [auto_tac (MI_fast_css
		       addsimps2 [MVNROKBA_def,MClkInit_def,RPCInit_def,PInit_def,
			          HInit_def,ImpInit_def,S_def,S1_def])
	    ]);

(* ========== Step 1.2 ================================================== *)
(* Figure 16 is a predicate-action diagram for the implementation. *)

qed_goal "Step1_2_1" MemoryImplementation.thy
   "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p  \
\             & ~unchanged (e p, c p, r p, m p, rmhist!p)  & $S1 rmhist p \
\      --> (S2 rmhist p)$ & ENext p & unchanged (c p, r p, m p)"
   (fn _ => [action_simp_tac (simpset() addsimps [ImpNext_def]) []
                             (map temp_elim [S1ClerkUnch,S1RPCUnch,S1MemUnch,S1Hist]) 1,
             auto_tac (MI_fast_css addSIs2 [S1Env])
	    ]);

qed_goal "Step1_2_2" MemoryImplementation.thy
   "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p  \
\             & ~unchanged (e p, c p, r p, m p, rmhist!p) & $S2 rmhist p \
\      --> (S3 rmhist p)$ & MClkFwd memCh crCh cst p & unchanged (e p, r p, m p, rmhist!p)"
   (fn _ => [action_simp_tac (simpset() addsimps [ImpNext_def]) []
                             (map temp_elim [S2EnvUnch,S2RPCUnch,S2MemUnch,S2Hist]) 1,
	     auto_tac (MI_fast_css addSIs2 [S2Clerk,S2Forward])
	    ]);

qed_goal "Step1_2_3" MemoryImplementation.thy
   "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p  \
\             & ~unchanged (e p, c p, r p, m p, rmhist!p) & $S3 rmhist p \
\      --> ((S4 rmhist p)$ & RPCFwd crCh rmCh rst p & unchanged (e p, c p, m p, rmhist!p)) \
\        | ((S6 rmhist p)$ & RPCFail crCh rmCh rst p & unchanged (e p, c p, m p))"
   (fn _ => [action_simp_tac (simpset() addsimps [ImpNext_def]) []
	          (map temp_elim [S3EnvUnch,S3ClerkUnch,S3MemUnch]) 1,
             action_simp_tac (simpset()) [] 
                  (squareE::map temp_elim [S3RPC,S3Forward,S3Fail]) 1,
             auto_tac (MI_css addDs2 [S3Hist])
	    ]);

qed_goal "Step1_2_4" MemoryImplementation.thy
   "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p  \
\             & ~unchanged (e p, c p, r p, m p, rmhist!p) \
\             & $S4 rmhist p & (!l. $(MemInv mm l))     \
\      --> ((S4 rmhist p)$ & Read rmCh mm ires p & unchanged (e p, c p, r p, rmhist!p)) \
\        | ((S4 rmhist p)$ & (? l. Write rmCh mm ires p l) & unchanged (e p, c p, r p, rmhist!p)) \
\        | ((S5 rmhist p)$ & MemReturn rmCh ires p & unchanged (e p, c p, r p))"
   (fn _ => [action_simp_tac (simpset() addsimps [ImpNext_def]) []
                             (map temp_elim [S4EnvUnch,S4ClerkUnch,S4RPCUnch]) 1,
             action_simp_tac (simpset() addsimps [RNext_def]) []
                             (squareE::map temp_elim [S4Read,S4Write,S4Return]) 1,
             auto_tac (MI_css addDs2 [S4Hist])
            ]);

qed_goal "Step1_2_5" MemoryImplementation.thy
   "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p  \
\             & ~unchanged (e p, c p, r p, m p, rmhist!p) & $S5 rmhist p \
\      --> ((S6 rmhist p)$ & RPCReply crCh rmCh rst p & unchanged (e p, c p, m p)) \
\        | ((S6 rmhist p)$ & RPCFail crCh rmCh rst p & unchanged (e p, c p, m p))"
   (fn _ => [action_simp_tac (simpset() addsimps [ImpNext_def]) []
                             (map temp_elim [S5EnvUnch,S5ClerkUnch,S5MemUnch,S5Hist]) 1,
	     action_simp_tac (simpset()) [] [squareE, temp_elim S5RPC] 1,
	     auto_tac (MI_fast_css addSDs2 [S5Reply,S5Fail])
	    ]);

qed_goal "Step1_2_6" MemoryImplementation.thy
   "|- [HNext rmhist p]_(c p,r p,m p, rmhist!p) & ImpNext p  \
\             & ~unchanged (e p, c p, r p, m p, rmhist!p) & $S6 rmhist p \
\      --> ((S1 rmhist p)$ & MClkReply memCh crCh cst p & unchanged (e p, r p, m p))\
\        | ((S3 rmhist p)$ & MClkRetry memCh crCh cst p & unchanged (e p,r p,m p,rmhist!p))"
   (fn _ => [action_simp_tac (simpset() addsimps [ImpNext_def]) []
                             (map temp_elim [S6EnvUnch,S6RPCUnch,S6MemUnch]) 1,
             action_simp_tac (simpset()) []
                             (squareE::map temp_elim [S6Clerk,S6Retry,S6Reply]) 1,
             auto_tac (MI_css addDs2 [S6Hist])
            ]);

(* --------------------------------------------------------------------------
   Step 1.3: S1 implies the barred initial condition.
*)

section "Initialization (Step 1.3)";

qed_goal "Step1_3" MemoryImplementation.thy 
   "|- S1 rmhist p --> PInit (resbar rmhist) p"
   (fn _ => [action_simp_tac (simpset() addsimps [resbar_def,PInit_def,S_def,S1_def])
                             [] [] 1
            ]);

(* ----------------------------------------------------------------------
   Step 1.4: Implementation's next-state relation simulates specification's
             next-state relation (with appropriate substitutions)
*)

section "Step simulation (Step 1.4)";

qed_goal "Step1_4_1" MemoryImplementation.thy
   "|- ENext p & $S1 rmhist p & (S2 rmhist p)$ & unchanged (c p, r p, m p) \
\      --> unchanged (rtrner memCh!p, resbar rmhist!p)"
  (fn _ => [ auto_tac (MI_fast_css addsimps2 [c_def,r_def,m_def,resbar_def]) ]);

qed_goal "Step1_4_2" MemoryImplementation.thy
   "|- MClkFwd memCh crCh cst p & $S2 rmhist p & (S3 rmhist p)$  \
\                & unchanged (e p, r p, m p, rmhist!p) \
\      --> unchanged (rtrner memCh!p, resbar rmhist!p)"
  (fn _ => [action_simp_tac
                (simpset() addsimps [MClkFwd_def, e_def, r_def, m_def, resbar_def,
                                     S_def, S2_def, S3_def]) [] [] 1
           ]);

qed_goal "Step1_4_3a" MemoryImplementation.thy
   "|- RPCFwd crCh rmCh rst p & $S3 rmhist p & (S4 rmhist p)$    \
\                  & unchanged (e p, c p, m p, rmhist!p) \
\      --> unchanged (rtrner memCh!p, resbar rmhist!p)"
  (fn _ => [Clarsimp_tac 1,
            REPEAT (dresolve_tac (map temp_use [S3_excl,S4_excl]) 1),
            action_simp_tac 
                 (simpset() addsimps [e_def,c_def,m_def,resbar_def,S_def, S3_def]) [] [] 1
           ]);

qed_goal "Step1_4_3b" MemoryImplementation.thy
   "|- RPCFail crCh rmCh rst p & $S3 rmhist p & (S6 rmhist p)$ & unchanged (e p, c p, m p) \
\      --> MemFail memCh (resbar rmhist) p"
  (fn _ => [Clarsimp_tac 1,
            dtac (temp_use S6_excl) 1,
            auto_tac (MI_css addsimps2 [RPCFail_def,MemFail_def,e_def,c_def,m_def,
		                        resbar_def]),
            force_tac (MI_css addsimps2 [S3_def,S_def]) 1,
            auto_tac (MI_css addsimps2 [Return_def])
           ]);


qed_goal "Step1_4_4a1" MemoryImplementation.thy
   "|- $S4 rmhist p & (S4 rmhist p)$ & ReadInner rmCh mm ires p l \
\             & unchanged (e p, c p, r p, rmhist!p) & $MemInv mm l \
\      --> ReadInner memCh mm (resbar rmhist) p l"
  (fn _ => [Clarsimp_tac 1,
            REPEAT (dtac (temp_use S4_excl) 1),
            action_simp_tac 
               (simpset() addsimps [ReadInner_def,GoodRead_def,BadRead_def,e_def,c_def,m_def]) 
               [] [] 1,
            auto_tac (MI_css addsimps2 [resbar_def]),
	    ALLGOALS (action_simp_tac 
                        (simpset() addsimps [RPCRelayArg_def,MClkRelayArg_def,
		                            S_def,S4_def,RdRequest_def,MemInv_def])
		      [] [impE,MemValNotAResultE])
           ]);

qed_goal "Step1_4_4a" MemoryImplementation.thy
   "|- Read rmCh mm ires p & $S4 rmhist p & (S4 rmhist p)$ \
\           & unchanged (e p, c p, r p, rmhist!p) & (!l. $(MemInv mm l)) \
\      --> Read memCh mm (resbar rmhist) p"
  (fn _ => [ force_tac (MI_css addsimps2 [Read_def] addSEs2 [Step1_4_4a1]) 1 ]);

qed_goal "Step1_4_4b1" MemoryImplementation.thy
   "|- $S4 rmhist p & (S4 rmhist p)$ & WriteInner rmCh mm ires p l v   \
\                   & unchanged (e p, c p, r p, rmhist!p) \
\      --> WriteInner memCh mm (resbar rmhist) p l v"
  (fn _ => [Clarsimp_tac 1,
            REPEAT (dtac (temp_use S4_excl) 1),
            action_simp_tac 
               (simpset() addsimps [WriteInner_def, GoodWrite_def, BadWrite_def,
			           e_def, c_def, m_def])
               [] [] 1,
	    auto_tac (MI_css addsimps2 [resbar_def]),
	    ALLGOALS (action_simp_tac
                        (simpset() addsimps [RPCRelayArg_def,MClkRelayArg_def,
		                            S_def,S4_def,WrRequest_def])
		      [] [])
           ]);

qed_goal "Step1_4_4b" MemoryImplementation.thy
   "|- Write rmCh mm ires p l & $S4 rmhist p & (S4 rmhist p)$   \
\                 & unchanged (e p, c p, r p, rmhist!p) \
\      --> Write memCh mm (resbar rmhist) p l"
  (fn _ => [ force_tac (MI_css addsimps2 [Write_def] addSEs2 [Step1_4_4b1]) 1 ]);

qed_goal "Step1_4_4c" MemoryImplementation.thy
   "|- MemReturn rmCh ires p & $S4 rmhist p & (S5 rmhist p)$ & unchanged (e p, c p, r p) \
\      --> unchanged (rtrner memCh!p, resbar rmhist!p)"
  (fn _ => [action_simp_tac
	       (simpset() addsimps [e_def,c_def,r_def,resbar_def]) [] [] 1,
	    REPEAT (dresolve_tac [temp_use S4_excl, temp_use S5_excl] 1),
	    auto_tac (MI_fast_css addsimps2 [MemReturn_def,Return_def])
           ]);

qed_goal "Step1_4_5a" MemoryImplementation.thy
   "|- RPCReply crCh rmCh rst p & $S5 rmhist p & (S6 rmhist p)$ & unchanged (e p, c p, m p) \
\      --> unchanged (rtrner memCh!p, resbar rmhist!p)"
  (fn _ => [Clarsimp_tac 1,
            REPEAT (dresolve_tac [temp_use S5_excl, temp_use S6_excl] 1),
            auto_tac (MI_css addsimps2 [e_def,c_def,m_def, resbar_def]),
	    auto_tac (MI_css addsimps2 [RPCReply_def,Return_def,S5_def,S_def] 
                             addSDs2 [MVOKBAnotRF])
           ]);

qed_goal "Step1_4_5b" MemoryImplementation.thy
   "|- RPCFail crCh rmCh rst p & $S5 rmhist p & (S6 rmhist p)$ & unchanged (e p, c p, m p) \
\      --> MemFail memCh (resbar rmhist) p"
  (fn _ => [Clarsimp_tac 1,
            dtac (temp_use S6_excl) 1,
            auto_tac (MI_css addsimps2 [e_def, c_def, m_def, RPCFail_def, Return_def,
		 		        MemFail_def, resbar_def]),
	    auto_tac (MI_css addsimps2 [S5_def,S_def])
           ]);

qed_goal "Step1_4_6a" MemoryImplementation.thy
   "|- MClkReply memCh crCh cst p & $S6 rmhist p & (S1 rmhist p)$ & unchanged (e p, r p, m p) \
\      --> MemReturn memCh (resbar rmhist) p"
  (fn _ => [Clarsimp_tac 1,
            dtac (temp_use S6_excl) 1,
            action_simp_tac
	      (simpset() addsimps [e_def, r_def, m_def, MClkReply_def, MemReturn_def,
				  Return_def, resbar_def]) [] [] 1,
	    ALLGOALS Asm_full_simp_tac,  (* simplify if-then-else *)
	    ALLGOALS (action_simp_tac
    	              (simpset() addsimps [MClkReplyVal_def,S6_def,S_def])
		      [] [MVOKBARFnotNR])
           ]);

qed_goal "Step1_4_6b" MemoryImplementation.thy
   "|- MClkRetry memCh crCh cst p & $S6 rmhist p & (S3 rmhist p)$   \
\                & unchanged (e p, r p, m p, rmhist!p) \
\      --> MemFail memCh (resbar rmhist) p"
  (fn _ => [Clarsimp_tac 1,
            dtac (temp_use S3_excl) 1,
            action_simp_tac
	       (simpset() addsimps [e_def, r_def, m_def, MClkRetry_def, MemFail_def, resbar_def])
	       [] [] 1,
	    auto_tac (MI_css addsimps2 [S6_def,S_def])
           ]);

qed_goal "S_lemma" MemoryImplementation.thy
   "|- unchanged (e p, c p, r p, m p, rmhist!p) \
\      --> unchanged (S rmhist ec cc rc cs rs hs1 hs2 p)"
   (fn _ => [auto_tac (MI_css addsimps2 [e_def,c_def,r_def,m_def,caller_def,rtrner_def,
					 S_def,Calling_def])
            ]);

qed_goal "Step1_4_7H" MemoryImplementation.thy
   "|- unchanged (e p, c p, r p, m p, rmhist!p) \
\      --> unchanged (rtrner memCh!p, S1 rmhist p, S2 rmhist p, S3 rmhist p, \
\                     S4 rmhist p, S5 rmhist p, S6 rmhist p)"
   (fn _ => [Clarsimp_tac 1,
             rtac conjI 1,
             force_tac (MI_css addsimps2 [c_def]) 1,
             force_tac (MI_css addsimps2 [S1_def,S2_def,S3_def,S4_def,S5_def,S6_def]
                               addSIs2 [S_lemma]) 1
            ]);

qed_goal "Step1_4_7" MemoryImplementation.thy
   "|- unchanged (e p, c p, r p, m p, rmhist!p) \
\      --> unchanged (rtrner memCh!p, resbar rmhist!p, S1 rmhist p, S2 rmhist p, S3 rmhist p, \
\                     S4 rmhist p, S5 rmhist p, S6 rmhist p)"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac action_rews,
            rtac impI 1,
            forward_tac [temp_use Step1_4_7H] 1,
	    auto_tac (MI_css addsimps2 [e_def,c_def,r_def,m_def,rtrner_def,resbar_def])
           ]);


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
qed_goal "unchanged_safe" MemoryImplementation.thy
   "|- (~unchanged (e p, c p, r p, m p, rmhist!p) \
\        --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)) \
\      --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
   (fn _ => [split_idle_tac [square_def] 1,
             Force_tac 1
            ]);
(* turn into (unsafe, looping!) introduction rule *)
bind_thm("unchanged_safeI", impI RS (action_use unchanged_safe));

qed_goal "S1safe" MemoryImplementation.thy
   "|- $S1 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)   \
\      --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
   (fn _ => [Clarsimp_tac 1, 
             rtac unchanged_safeI 1,
             rtac idle_squareI 1,
	     auto_tac (MI_css addSDs2 [Step1_2_1,Step1_4_1])
	    ]);

qed_goal "S2safe" MemoryImplementation.thy
   "|- $S2 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)   \
\      --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
   (fn _ => [Clarsimp_tac 1, 
             rtac unchanged_safeI 1,
             rtac idle_squareI 1,
	     auto_tac (MI_css addSDs2 [Step1_2_2,Step1_4_2])
	    ]);

qed_goal "S3safe" MemoryImplementation.thy
   "|- $S3 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)   \
\      --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
   (fn _ => [Clarsimp_tac 1,
	     rtac unchanged_safeI 1,
             auto_tac (MI_css addSDs2 [Step1_2_3]),
	     auto_tac (MI_css addsimps2 [square_def,UNext_def]
		              addSDs2 [Step1_4_3a,Step1_4_3b])
	    ]);

qed_goal "S4safe" MemoryImplementation.thy
   "|- $S4 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)  \
\                   & (!l. $(MemInv mm l)) \
\      --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
   (fn _ => [Clarsimp_tac 1,
	     rtac unchanged_safeI 1,
             auto_tac (MI_css addSDs2 [Step1_2_4]),
	     auto_tac (MI_css addsimps2 [square_def,UNext_def,RNext_def]
                              addSDs2 [Step1_4_4a,Step1_4_4b,Step1_4_4c])
	    ]);

qed_goal "S5safe" MemoryImplementation.thy
   "|- $S5 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)  \
\      --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
   (fn _ => [Clarsimp_tac 1,
	     rtac unchanged_safeI 1,
             auto_tac (MI_css addSDs2 [Step1_2_5]),
	     auto_tac (MI_css addsimps2 [square_def,UNext_def]
		              addSDs2 [Step1_4_5a,Step1_4_5b])
	    ]);

qed_goal "S6safe" MemoryImplementation.thy
   "|- $S6 rmhist p & ImpNext p & [HNext rmhist p]_(c p,r p,m p, rmhist!p)   \
\      --> [UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
   (fn _ => [Clarsimp_tac 1,
	     rtac unchanged_safeI 1,
             auto_tac (MI_css addSDs2 [Step1_2_6]),
	     auto_tac (MI_css addsimps2 [square_def,UNext_def,RNext_def]
		              addSDs2 [Step1_4_6a,Step1_4_6b])
	    ]);

(* ----------------------------------------------------------------------
   Step 1.5: Temporal refinement proof, based on previous steps.
*)

section "The liveness part";

use "MIlive.ML";

section "Refinement proof (step 1.5)";

(* Prove invariants of the implementation:
   a. memory invariant
   b. "implementation invariant": always in states S1,...,S6
*)
qed_goal "Step1_5_1a" MemoryImplementation.thy 
   "|- IPImp p --> (!l. []$MemInv mm l)"
   (fn _ => [auto_tac (MI_css addsimps2 [IPImp_def,box_stp_act]
			      addSIs2 [MemoryInvariantAll])
	    ]);

qed_goal "Step1_5_1b" MemoryImplementation.thy
   "|- Init(ImpInit p & HInit rmhist p) & [](ImpNext p) \
\      & [][HNext rmhist p]_(c p, r p, m p, rmhist!p) & [](!l. $MemInv mm l) \
\      --> []ImpInv rmhist p"
   (fn _ => [inv_tac MI_css 1,
	     auto_tac (MI_css addsimps2 [Init_def, ImpInv_def, box_stp_act]
                              addSDs2 [Step1_1]
		              addDs2 [S1_successors,S2_successors,S3_successors,
			              S4_successors,S5_successors,S6_successors])
            ]);

(*** Initialization ***)
qed_goal "Step1_5_2a" MemoryImplementation.thy
   "|- Init(ImpInit p & HInit rmhist p) --> Init(PInit (resbar rmhist) p)"
   (fn _ => [auto_tac (MI_css addsimps2 [Init_def]
                              addSIs2 [Step1_1,Step1_3])
            ]);

(*** step simulation ***)
qed_goal "Step1_5_2b" MemoryImplementation.thy
   "|- [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p)   \
\                   & $ImpInv rmhist p & (!l. $MemInv mm l))       \
\      --> [][UNext memCh mm (resbar rmhist) p]_(rtrner memCh!p, resbar rmhist!p)"
   (fn _ => [auto_tac (MI_css 
                          addsimps2 [ImpInv_def] addSEs2 [STL4E]
                          addSDs2 [S1safe,S2safe,S3safe,S4safe,S5safe,S6safe])
            ]);


(*** Liveness ***)
qed_goal "GoodImpl" MemoryImplementation.thy
   "|- IPImp p & HistP rmhist p  \
\      -->   Init(ImpInit p & HInit rmhist p)   \
\          & [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p)) \
\          & [](!l. $MemInv mm l) & []($ImpInv rmhist p) \
\          & ImpLive p"
   (fn _ => [Clarsimp_tac 1,
	     subgoal_tac
	       "sigma |= Init(ImpInit p & HInit rmhist p) \
\                        & [](ImpNext p) \
\                        & [][HNext rmhist p]_(c p, r p, m p, rmhist!p) \
\                        & [](!l. $MemInv mm l)" 1,
	     auto_tac (MI_css addsimps2 [split_box_conj,box_stp_act] addSDs2 [Step1_5_1b]),
	     force_tac (MI_css addsimps2 [IPImp_def,MClkIPSpec_def,RPCIPSpec_def,RPSpec_def,
					  ImpLive_def,c_def,r_def,m_def]) 1,
	     force_tac (MI_css addsimps2 [IPImp_def,MClkIPSpec_def,RPCIPSpec_def,RPSpec_def,
					  HistP_def,Init_def,ImpInit_def]) 1,
	     force_tac (MI_css addsimps2 [IPImp_def,MClkIPSpec_def,RPCIPSpec_def,RPSpec_def,
					  ImpNext_def,c_def,r_def,m_def,split_box_conj]) 1,
	     force_tac (MI_css addsimps2 [HistP_def]) 1,
             force_tac (MI_css addsimps2 [temp_use allT] addSDs2 [Step1_5_1a]) 1
	    ]);

(* The implementation is infinitely often in state S1... *)
qed_goal "Step1_5_3a" MemoryImplementation.thy
   "|- [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p)) \
\      & [](!l. $MemInv mm l)  \
\      & []($ImpInv rmhist p) & ImpLive p  \
\      --> []<>S1 rmhist p"
   (fn _ => [clarsimp_tac (MI_css addsimps2 [ImpLive_def]) 1,
             rtac S1Infinite 1,
	     force_tac (MI_css
			  addsimps2 [split_box_conj,box_stp_act]
			  addSIs2 [NotS1LeadstoS6,S2_live,S3_live,S4a_live,S4b_live,S5_live]) 1,
             auto_tac (MI_css addsimps2 [split_box_conj] addSIs2 [S6_live])
            ]);

(* ... which implies that it satisfies the fairness requirements of the specification *)
qed_goal "Step1_5_3b" MemoryImplementation.thy
   "|- [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p)) \
\      & [](!l. $MemInv mm l) & []($ImpInv rmhist p) & ImpLive p  \
\      --> WF(RNext memCh mm (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)"
   (fn _ => [ auto_tac (MI_css addSIs2 [RNext_fair,Step1_5_3a]) ]);

qed_goal "Step1_5_3c" MemoryImplementation.thy
   "|- [](ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p)) \
\      & [](!l. $MemInv mm l) & []($ImpInv rmhist p) & ImpLive p  \
\      --> WF(MemReturn memCh (resbar rmhist) p)_(rtrner memCh!p, resbar rmhist!p)"
   (fn _ => [ auto_tac (MI_css addSIs2 [Return_fair,Step1_5_3a]) ]);


(* QED step of step 1 *)
qed_goal "Step1" MemoryImplementation.thy
   "|- IPImp p & HistP rmhist p --> UPSpec memCh mm (resbar rmhist) p"
   (fn _ => [auto_tac
               (MI_css addsimps2 [UPSpec_def,split_box_conj]
		       addSDs2 [GoodImpl]
                       addSIs2 [Step1_5_2a,Step1_5_2b,Step1_5_3b,Step1_5_3c])
            ]);


(* ------------------------------ Step 2 ------------------------------ *)
section "Step 2";

qed_goal "Step2_2a" MemoryImplementation.thy
   "|- Write rmCh mm ires p l & ImpNext p & [HNext rmhist p]_(c p, r p, m p, rmhist!p) \
\      & $ImpInv rmhist p  \
\      --> (S4 rmhist p)` & unchanged (e p, c p, r p, rmhist!p)"
   (fn _ => [Clarsimp_tac 1,
             dtac (action_use WriteS4) 1, atac 1,
             split_idle_tac [] 1,
             auto_tac (MI_css addsimps2 [ImpNext_def] 
                              addSDs2 [S4EnvUnch,S4ClerkUnch,S4RPCUnch]),
             auto_tac (MI_css addsimps2 [square_def] addDs2 [S4Write])
            ]);

qed_goal "Step2_2" MemoryImplementation.thy
   "|-   (!p. ImpNext p) \
\      & (!p. [HNext rmhist p]_(c p, r p, m p, rmhist!p)) \
\      & (!p. $ImpInv rmhist p) \
\      & [? q. Write rmCh mm ires q l]_(mm!l) \
\      --> [? q. Write memCh mm (resbar rmhist) q l]_(mm!l)"
   (fn _ => [auto_tac (MI_css addSIs2 [squareCI] addSEs2 [squareE]),
             REPEAT (ares_tac [exI, action_use Step1_4_4b] 1),
             force_tac (MI_css addSIs2 [WriteS4]) 1,
             auto_tac (MI_css addSDs2 [Step2_2a])
            ]);

qed_goal "Step2_lemma" MemoryImplementation.thy
   "|-  [](  (!p. ImpNext p) \
\          & (!p. [HNext rmhist p]_(c p, r p, m p, rmhist!p)) \
\          & (!p. $ImpInv rmhist p) \
\          & [? q. Write rmCh mm ires q l]_(mm!l)) \
\       --> [][? q. Write memCh mm (resbar rmhist) q l]_(mm!l)"
   (fn _ => [ force_tac (MI_css addSEs2 [STL4E] addSDs2 [Step2_2]) 1 ]);

qed_goal "Step2" MemoryImplementation.thy
   "|- #l : #MemLoc & (!p. IPImp p & HistP rmhist p)  \
\      --> MSpec memCh mm (resbar rmhist) l"
   (fn _ => [auto_tac (MI_css addsimps2 [MSpec_def]),
	     force_tac (MI_css addsimps2 [IPImp_def,MSpec_def]) 1,
	     auto_tac (MI_css addSIs2 [Step2_lemma]
		              addsimps2 [split_box_conj,all_box]),
	     force_tac (MI_css addsimps2 [IPImp_def,MSpec_def]) 4,
             auto_tac (MI_css addsimps2 [split_box_conj] addSEs2 [allE] addSDs2 [GoodImpl])
	    ]);

(* ----------------------------- Main theorem --------------------------------- *)
section "Memory implementation";

(* The combination of a legal caller, the memory clerk, the RPC component,
   and a reliable memory implement the unreliable memory.
*)

(* Implementation of internal specification by combination of implementation
   and history variable with explicit refinement mapping
*)
qed_goal "Impl_IUSpec" MemoryImplementation.thy
   "|- Implementation & Hist rmhist --> IUSpec memCh mm (resbar rmhist)"
   (fn _ => [auto_tac (MI_css addsimps2 [IUSpec_def,Implementation_def,IPImp_def,
					 MClkISpec_def,RPCISpec_def,IRSpec_def,Hist_def]
		              addSIs2 [Step1,Step2])
	    ]);

(* The main theorem: introduce hiding and eliminate history variable. *)
qed_goal "Implementation" MemoryImplementation.thy
   "|- Implementation --> USpec memCh"
   (fn _ => [Clarsimp_tac 1,
             forward_tac [temp_use History] 1,
             auto_tac (MI_css addsimps2 [USpec_def] 
                              addIs2 [eexI, Impl_IUSpec, MI_base]
                              addSEs2 [eexE])
            ]);


