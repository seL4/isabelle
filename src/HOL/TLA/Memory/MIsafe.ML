(* 
    File:        MIsafe.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: Lower-level lemmas about memory implementation (safety)
*)

(* ========================= Lemmas about values ========================= *)

(* RPCFailure notin MemVals U {OK,BadArg} *)

qed_goalw "MVOKBAnotRF" MemoryImplementation.thy [MVOKBA_def]
   "!!x. MVOKBA x ==> x ~= RPCFailure"
   (fn _ => [ Auto_tac ]);

(* NotAResult notin MemVals U {OK,BadArg,RPCFailure} *)

qed_goalw "MVOKBARFnotNR" MemoryImplementation.thy [MVOKBARF_def]
   "!!x. MVOKBARF x ==> x ~= NotAResult"
   (fn _ => [ Auto_tac ]);

(* ========================= Si's are mutually exclusive ==================================== *)
(* Si and Sj are mutually exclusive for i # j. This helps to simplify the big
   conditional in the definition of resbar when doing the step-simulation proof.
   We prove a weaker result, which suffices for our purposes: 
   Si implies (not Sj), for j<i.
*)

(* --- not used ---
qed_goal "S1_excl" MemoryImplementation.thy 
     "|- S1 rmhist p --> S1 rmhist p & ~S2 rmhist p & ~S3 rmhist p & \
\                        ~S4 rmhist p & ~S5 rmhist p & ~S6 rmhist p"
   (fn _ => [ auto_tac (MI_css addsimps2 [S_def, S1_def, S2_def,
                                          S3_def, S4_def, S5_def, S6_def])
            ]);
*)

qed_goal "S2_excl" MemoryImplementation.thy 
     "|- S2 rmhist p --> S2 rmhist p & ~S1 rmhist p"
   (fn _ => [ auto_tac (MI_css addsimps2 [S_def, S1_def, S2_def]) ]);

qed_goal "S3_excl" MemoryImplementation.thy 
     "|- S3 rmhist p --> S3 rmhist p & ~S1 rmhist p & ~S2 rmhist p"
   (fn _ => [ auto_tac (MI_css addsimps2 [S_def, S1_def, S2_def, S3_def]) ]);

qed_goal "S4_excl" MemoryImplementation.thy 
     "|- S4 rmhist p --> S4 rmhist p & ~S1 rmhist p & ~S2 rmhist p & ~S3 rmhist p"
   (fn _ => [ auto_tac (MI_css addsimps2 [S_def,S1_def,S2_def,S3_def,S4_def]) ]);

qed_goal "S5_excl" MemoryImplementation.thy 
     "|- S5 rmhist p --> S5 rmhist p & ~S1 rmhist p & ~S2 rmhist p \
\                        & ~S3 rmhist p & ~S4 rmhist p"
   (fn _ => [ auto_tac (MI_css addsimps2 [S_def,S1_def,S2_def,S3_def,S4_def,S5_def]) ]);

qed_goal "S6_excl" MemoryImplementation.thy 
     "|- S6 rmhist p --> S6 rmhist p & ~S1 rmhist p & ~S2 rmhist p  \
\                        & ~S3 rmhist p & ~S4 rmhist p & ~S5 rmhist p"
   (fn _ => [ auto_tac (MI_css addsimps2 [S_def,S1_def,S2_def,S3_def,S4_def,S5_def,S6_def]) ]);


(* ==================== Lemmas about the environment ============================== *)

qed_goal "Envbusy" MemoryImplementation.thy
   "|- $(Calling memCh p) --> ~ENext p"
   (fn _ => [ auto_tac (MI_css addsimps2 [ENext_def,Call_def]) ]);

(* ==================== Lemmas about the implementation's states ==================== *)

(* The following series of lemmas are used in establishing the implementation's
   next-state relation (Step 1.2 of the proof in the paper). For each state Si, we
   determine which component actions are possible and what state they result in.
*)

(* ------------------------------ State S1 ---------------------------------------- *) 

qed_goal "S1Env" MemoryImplementation.thy
   "|- ENext p & $(S1 rmhist p) & unchanged (c p, r p, m p, rmhist!p) --> (S2 rmhist p)$"
   (fn _ => [force_tac (MI_css
		        addsimps2 [ENext_def,Call_def,c_def,r_def,m_def,
			   	   caller_def,rtrner_def,MVNROKBA_def,
                                   S_def,S1_def,S2_def,Calling_def]) 1
	    ]);

qed_goal "S1ClerkUnch" MemoryImplementation.thy 
   "|- [MClkNext memCh crCh cst p]_(c p) & $(S1 rmhist p) --> unchanged (c p)"
   (fn _ => [auto_tac (MI_fast_css addSDs2 [MClkidle] addsimps2 [S_def,S1_def]) ]);

qed_goal "S1RPCUnch" MemoryImplementation.thy
   "|- [RPCNext crCh rmCh rst p]_(r p) & $(S1 rmhist p) --> unchanged (r p)"
   (fn _ => [auto_tac (MI_fast_css addSDs2 [RPCidle] addsimps2 [S_def,S1_def]) ]);

qed_goal "S1MemUnch" MemoryImplementation.thy
   "|- [RNext rmCh mm ires p]_(m p) & $(S1 rmhist p) --> unchanged (m p)"
   (fn _ => [auto_tac (MI_fast_css addSDs2 [Memoryidle] addsimps2 [S_def,S1_def]) ]);

qed_goal "S1Hist" MemoryImplementation.thy
   "|- [HNext rmhist p]_(c p,r p,m p,rmhist!p) & $(S1 rmhist p) --> unchanged (rmhist!p)"
   (fn _ => [action_simp_tac (simpset() addsimps [HNext_def, S_def, S1_def, MemReturn_def, 
                                                  RPCFail_def,MClkReply_def,Return_def])
                             [] [squareE] 1
	    ]);

(* ------------------------------ State S2 ---------------------------------------- *)

qed_goal "S2EnvUnch" MemoryImplementation.thy
   "|- [ENext p]_(e p) & $(S2 rmhist p) --> unchanged (e p)"
   (fn _ => [auto_tac (MI_css addSDs2 [Envbusy] addsimps2 [S_def,S2_def]) ]);

qed_goal "S2Clerk" MemoryImplementation.thy
   "|- MClkNext memCh crCh cst p & $(S2 rmhist p) --> MClkFwd memCh crCh cst p"
   (fn _ => [auto_tac (MI_css addsimps2 [MClkNext_def,MClkRetry_def,MClkReply_def,
					 S_def,S2_def])
	    ]);

qed_goal "S2Forward" MemoryImplementation.thy
   "|- $(S2 rmhist p) & MClkFwd memCh crCh cst p & unchanged (e p, r p, m p, rmhist!p) \
\      --> (S3 rmhist p)$"
   (fn _ => [action_simp_tac (simpset() addsimps
                [MClkFwd_def,Call_def,e_def,r_def,m_def,caller_def,rtrner_def,
                 S_def,S2_def,S3_def,Calling_def])
               [] [] 1
	     ]);

qed_goal "S2RPCUnch" MemoryImplementation.thy
   "|- [RPCNext crCh rmCh rst p]_(r p) & $(S2 rmhist p) --> unchanged (r p)"
   (fn _ => [auto_tac (MI_css addsimps2 [S_def,S2_def] addSDs2 [RPCidle]) ]);

qed_goal "S2MemUnch" MemoryImplementation.thy
   "|- [RNext rmCh mm ires p]_(m p) & $(S2 rmhist p) --> unchanged (m p)"
   (fn _ => [auto_tac (MI_css addsimps2 [S_def,S2_def] addSDs2 [Memoryidle]) ]);

qed_goal "S2Hist" MemoryImplementation.thy
   "|- [HNext rmhist p]_(c p,r p,m p,rmhist!p) & $(S2 rmhist p) --> unchanged (rmhist!p)"
   (fn _ => [auto_tac (MI_fast_css
		       addsimps2 [HNext_def,MemReturn_def,
				  RPCFail_def,MClkReply_def,Return_def,S_def,S2_def])
	    ]);

(* ------------------------------ State S3 ---------------------------------------- *)

qed_goal "S3EnvUnch" MemoryImplementation.thy
   "|- [ENext p]_(e p) & $(S3 rmhist p) --> unchanged (e p)"
   (fn _ => [auto_tac (MI_css addSDs2 [Envbusy] addsimps2 [S_def,S3_def]) ]);

qed_goal "S3ClerkUnch" MemoryImplementation.thy 
   "|- [MClkNext memCh crCh cst p]_(c p) & $(S3 rmhist p) --> unchanged (c p)"
   (fn _ => [auto_tac (MI_css addSDs2 [MClkbusy] addsimps2 [square_def,S_def,S3_def]) ]);

qed_goal "S3LegalRcvArg" MemoryImplementation.thy
   "|- S3 rmhist p --> IsLegalRcvArg<arg<crCh!p>>"
   (fn _ => [auto_tac (MI_css addsimps2 [IsLegalRcvArg_def,MClkRelayArg_def,S_def,S3_def]) ]);

qed_goal "S3RPC" MemoryImplementation.thy
   "|- RPCNext crCh rmCh rst p & $(S3 rmhist p) \
\      --> RPCFwd crCh rmCh rst p | RPCFail crCh rmCh rst p"
   (fn _ => [Clarsimp_tac 1,
             forward_tac [action_use S3LegalRcvArg] 1,
	     auto_tac (MI_css addsimps2 [RPCNext_def,RPCReject_def,RPCReply_def,S_def,S3_def])
	    ]);

qed_goal "S3Forward" MemoryImplementation.thy
   "|- RPCFwd crCh rmCh rst p & HNext rmhist p & $(S3 rmhist p) & unchanged (e p, c p, m p) \
\      --> (S4 rmhist p)$ & unchanged (rmhist!p)"
   (fn _ => [action_simp_tac 
               (simpset() addsimps [RPCFwd_def,HNext_def,MemReturn_def,RPCFail_def,MClkReply_def,
				   Return_def,Call_def,e_def,c_def,m_def,caller_def,rtrner_def, 
				   S_def,S3_def,S4_def,Calling_def])
	       [] [] 1
	    ]);

qed_goal "S3Fail" MemoryImplementation.thy
   "|- RPCFail crCh rmCh rst p & $(S3 rmhist p) & HNext rmhist p & unchanged (e p, c p, m p) \
\      --> (S6 rmhist p)$"
   (fn _ => [action_simp_tac 
               (simpset() addsimps [HNext_def,RPCFail_def,Return_def,e_def,c_def,m_def,
				   caller_def,rtrner_def,MVOKBARF_def,
				   S_def,S3_def,S6_def,Calling_def])
               [] [] 1
	    ]);

qed_goal "S3MemUnch" MemoryImplementation.thy
   "|- [RNext rmCh mm ires p]_(m p) & $(S3 rmhist p) --> unchanged (m p)"
   (fn _ => [auto_tac (MI_css addsimps2 [S_def,S3_def] addSDs2 [Memoryidle]) ]);

qed_goal "S3Hist" MemoryImplementation.thy
   "|- HNext rmhist p & $(S3 rmhist p) & unchanged (r p) --> unchanged (rmhist!p)"
   (fn _ => [auto_tac (MI_css
		       addsimps2 [HNext_def,MemReturn_def,RPCFail_def,MClkReply_def,
				  Return_def,r_def,rtrner_def,S_def,S3_def,Calling_def])
	    ]);


(* ------------------------------ State S4 ---------------------------------------- *)

qed_goal "S4EnvUnch" MemoryImplementation.thy
   "|- [ENext p]_(e p) & $(S4 rmhist p) --> unchanged (e p)"
   (fn _ => [auto_tac (MI_css addsimps2 [S_def,S4_def] addSDs2 [Envbusy]) ]);

qed_goal "S4ClerkUnch" MemoryImplementation.thy
   "|- [MClkNext memCh crCh cst p]_(c p) & $(S4 rmhist p) --> unchanged (c p)"
   (fn _ => [auto_tac (MI_css addsimps2 [S_def,S4_def] addSDs2 [MClkbusy]) ]);

qed_goal "S4RPCUnch" MemoryImplementation.thy
   "|- [RPCNext crCh rmCh rst p]_(r p) & $(S4 rmhist p) --> unchanged (r p)"
   (fn _ => [auto_tac (MI_fast_css addsimps2 [S_def,S4_def] addSDs2 [RPCbusy]) ]);

qed_goal "S4ReadInner" MemoryImplementation.thy
   "|- ReadInner rmCh mm ires p l & $(S4 rmhist p) & unchanged (e p, c p, r p) \
\           & HNext rmhist p & $(MemInv mm l) \
\      --> (S4 rmhist p)$ & unchanged (rmhist!p)"
   (fn _ => [action_simp_tac 
               (simpset() addsimps [ReadInner_def,GoodRead_def, BadRead_def,HNext_def,
				   MemReturn_def, RPCFail_def,MClkReply_def,Return_def,
				   e_def,c_def,r_def,rtrner_def,caller_def,MVNROKBA_def,
				   S_def,S4_def,RdRequest_def,Calling_def,MemInv_def])
               [] [] 1
	    ]);

qed_goal "S4Read" MemoryImplementation.thy
   "|- Read rmCh mm ires p & $(S4 rmhist p) & unchanged (e p, c p, r p) \
\           & HNext rmhist p & (!l. $MemInv mm l) \
\      --> (S4 rmhist p)$ & unchanged (rmhist!p)"
   (fn _ => [auto_tac (MI_css addsimps2 [Read_def] addSDs2 [S4ReadInner]) ]);

qed_goal "S4WriteInner" MemoryImplementation.thy
   "|- WriteInner rmCh mm ires p l v & $(S4 rmhist p) & unchanged (e p, c p, r p) \
\           & HNext rmhist p \
\      --> (S4 rmhist p)$ & unchanged (rmhist!p)"
   (fn _ => [action_simp_tac 
               (simpset() addsimps [WriteInner_def,GoodWrite_def, BadWrite_def,HNext_def,
				   MemReturn_def,RPCFail_def,MClkReply_def,Return_def,
				   e_def,c_def,r_def,rtrner_def,caller_def,MVNROKBA_def, 
				   S_def,S4_def,WrRequest_def,Calling_def])
               [] [] 1
	    ]);

qed_goal "S4Write" MemoryImplementation.thy
   "|- Write rmCh mm ires p l & $(S4 rmhist p) & unchanged (e p, c p, r p) & (HNext rmhist p) \
\      --> (S4 rmhist p)$ & unchanged (rmhist!p)"
   (fn _ => [ auto_tac (MI_css addsimps2 [Write_def] addSDs2 [S4WriteInner]) ]);

qed_goal "WriteS4" MemoryImplementation.thy
   "|- $ImpInv rmhist p & Write rmCh mm ires p l --> $S4 rmhist p"
   (fn _ => [auto_tac (MI_css
		       addsimps2 [Write_def,WriteInner_def,ImpInv_def,WrRequest_def,
				  S_def,S1_def,S2_def,S3_def,S4_def,S5_def,S6_def])
            ]);

qed_goal "S4Return" MemoryImplementation.thy
   "|- MemReturn rmCh ires p & $S4 rmhist p & unchanged (e p, c p, r p) & HNext rmhist p \
\      --> (S5 rmhist p)$"
   (fn _ => [auto_tac (MI_css
		       addsimps2 [HNext_def,MemReturn_def,Return_def,e_def,c_def,r_def,
				  rtrner_def,caller_def,MVNROKBA_def,MVOKBA_def,
		                  S_def,S4_def,S5_def,Calling_def])
	    ]);

qed_goal "S4Hist" MemoryImplementation.thy
   "|- HNext rmhist p & $S4 rmhist p & (m p)$ = $(m p) --> (rmhist!p)$ = $(rmhist!p)"
   (fn _ => [auto_tac (MI_css
		       addsimps2 [HNext_def,MemReturn_def,RPCFail_def,MClkReply_def,
				  Return_def,m_def,rtrner_def,S_def,S4_def,Calling_def])
	    ]);

(* ------------------------------ State S5 ---------------------------------------- *)

qed_goal "S5EnvUnch" MemoryImplementation.thy
   "|- [ENext p]_(e p) & $(S5 rmhist p) --> unchanged (e p)"
   (fn _ => [auto_tac (MI_css addsimps2 [S_def,S5_def] addSDs2 [Envbusy]) ]);

qed_goal "S5ClerkUnch" MemoryImplementation.thy
   "|- [MClkNext memCh crCh cst p]_(c p) & $(S5 rmhist p) --> unchanged (c p)"
   (fn _ => [auto_tac (MI_css addsimps2 [S_def,S5_def] addSDs2 [MClkbusy]) ]);

qed_goal "S5RPC" MemoryImplementation.thy
   "|- RPCNext crCh rmCh rst p & $(S5 rmhist p)   \
\      --> RPCReply crCh rmCh rst p | RPCFail crCh rmCh rst p"
   (fn _ => [auto_tac (MI_css
		       addsimps2 [RPCNext_def,RPCReject_def,RPCFwd_def,S_def,S5_def])
	    ]);

qed_goal "S5Reply" MemoryImplementation.thy
   "|- RPCReply crCh rmCh rst p & $(S5 rmhist p) & unchanged (e p, c p, m p,rmhist!p) \
\      --> (S6 rmhist p)$"
   (fn _ => [action_simp_tac 
               (simpset()
		addsimps [RPCReply_def,Return_def,e_def,c_def,m_def,
			  MVOKBA_def,MVOKBARF_def,caller_def,rtrner_def,
			  S_def,S5_def,S6_def,Calling_def])
               [] [] 1
	    ]);

qed_goal "S5Fail" MemoryImplementation.thy
   "|- RPCFail crCh rmCh rst p & $(S5 rmhist p) & unchanged (e p, c p, m p,rmhist!p) \
\      --> (S6 rmhist p)$"
   (fn _ => [action_simp_tac
	       (simpset()
		addsimps [RPCFail_def,Return_def,e_def,c_def,m_def,
			  MVOKBARF_def,caller_def,rtrner_def,
			  S_def,S5_def,S6_def,Calling_def])
               [] [] 1
	    ]);

qed_goal "S5MemUnch" MemoryImplementation.thy
   "|- [RNext rmCh mm ires p]_(m p) & $(S5 rmhist p) --> unchanged (m p)"
   (fn _ => [auto_tac (MI_css addsimps2 [S_def,S5_def] addSDs2 [Memoryidle]) ]);

qed_goal "S5Hist" MemoryImplementation.thy
   "|- [HNext rmhist p]_(c p, r p, m p, rmhist!p) & $(S5 rmhist p) --> (rmhist!p)$ = $(rmhist!p)"
   (fn _ => [auto_tac (MI_fast_css
		       addsimps2 [HNext_def,MemReturn_def,
				  RPCFail_def,MClkReply_def,Return_def,S_def,S5_def])
	    ]);

(* ------------------------------ State S6 ---------------------------------------- *)

qed_goal "S6EnvUnch" MemoryImplementation.thy
   "|- [ENext p]_(e p) & $(S6 rmhist p) --> unchanged (e p)"
   (fn _ => [auto_tac (MI_css addsimps2 [S_def,S6_def] addSDs2 [Envbusy]) ]);

qed_goal "S6Clerk" MemoryImplementation.thy
   "|- MClkNext memCh crCh cst p & $(S6 rmhist p) \
\      --> MClkRetry memCh crCh cst p | MClkReply memCh crCh cst p"
   (fn _ => [ auto_tac (MI_css addsimps2 [MClkNext_def,MClkFwd_def,S_def,S6_def]) ]);

qed_goal "S6Retry" MemoryImplementation.thy
   "|- MClkRetry memCh crCh cst p & HNext rmhist p & $S6 rmhist p & unchanged (e p,r p,m p) \
\      --> (S3 rmhist p)$ & unchanged (rmhist!p)"
   (fn _ => [action_simp_tac
	        (simpset() addsimps [HNext_def,MClkReply_def,MClkRetry_def,Call_def,
				    Return_def,e_def,r_def,m_def,caller_def,rtrner_def,
		                    S_def,S6_def,S3_def,Calling_def])
                [] [] 1]);

qed_goal "S6Reply" MemoryImplementation.thy
   "|- MClkReply memCh crCh cst p & HNext rmhist p & $S6 rmhist p & unchanged (e p,r p,m p) \
\      --> (S1 rmhist p)$"
   (fn _ => [action_simp_tac (simpset()
			      addsimps [HNext_def,MemReturn_def,RPCFail_def,Return_def,
					MClkReply_def,e_def,r_def,m_def,caller_def,rtrner_def,
					S_def,S6_def,S1_def,Calling_def])
	                     [] [] 1
	    ]);

qed_goal "S6RPCUnch" MemoryImplementation.thy
   "|- [RPCNext crCh rmCh rst p]_(r p) & $S6 rmhist p --> unchanged (r p)"
   (fn _ => [auto_tac (MI_css addsimps2 [S_def,S6_def] addSDs2 [RPCidle]) ]);

qed_goal "S6MemUnch" MemoryImplementation.thy
   "|- [RNext rmCh mm ires p]_(m p) & $(S6 rmhist p) --> unchanged (m p)"
   (fn _ => [auto_tac (MI_css addsimps2 [S_def,S6_def] addSDs2 [Memoryidle]) ]);

qed_goal "S6Hist" MemoryImplementation.thy
   "|- HNext rmhist p & $S6 rmhist p & (c p)$ = $(c p) --> (rmhist!p)$ = $(rmhist!p)"
   (fn _ => [auto_tac (MI_css
		       addsimps2 [HNext_def,MClkReply_def,Return_def,c_def,rtrner_def,
		                  S_def,S6_def,Calling_def])
	    ]);

