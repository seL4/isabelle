(* 
    File:        MIsafe.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: Lower-level lemmas about memory implementation (safety)
*)

(* ========================= Lemmas about values ========================= *)

(* RPCFailure notin MemVals U {OK,BadArg} *)

Goalw [MVOKBA_def] "MVOKBA x ==> x ~= RPCFailure";
by Auto_tac;
qed "MVOKBAnotRF";

(* NotAResult notin MemVals U {OK,BadArg,RPCFailure} *)

Goalw [MVOKBARF_def] "MVOKBARF x ==> x ~= NotAResult";
by Auto_tac;
qed "MVOKBARFnotNR";

(* ================ Si's are mutually exclusive ================================ *)
(* Si and Sj are mutually exclusive for i # j. This helps to simplify the big
   conditional in the definition of resbar when doing the step-simulation proof.
   We prove a weaker result, which suffices for our purposes: 
   Si implies (not Sj), for j<i.
*)

(* --- not used ---
Goal "|- S1 rmhist p --> S1 rmhist p & ~S2 rmhist p & ~S3 rmhist p & \
\                        ~S4 rmhist p & ~S5 rmhist p & ~S6 rmhist p";
by (auto_tac (MI_css addsimps2 [S_def, S1_def, S2_def,
                                S3_def, S4_def, S5_def, S6_def]));
qed "S1_excl";
*)

Goal "|- S2 rmhist p --> S2 rmhist p & ~S1 rmhist p";
by (auto_tac (MI_css addsimps2 [S_def, S1_def, S2_def]));
qed "S2_excl";

Goal "|- S3 rmhist p --> S3 rmhist p & ~S1 rmhist p & ~S2 rmhist p";
by (auto_tac (MI_css addsimps2 [S_def, S1_def, S2_def, S3_def]));
qed "S3_excl";

Goal "|- S4 rmhist p --> S4 rmhist p & ~S1 rmhist p & ~S2 rmhist p & ~S3 rmhist p";
by (auto_tac (MI_css addsimps2 [S_def,S1_def,S2_def,S3_def,S4_def]));
qed "S4_excl";

Goal "|- S5 rmhist p --> S5 rmhist p & ~S1 rmhist p & ~S2 rmhist p \
\                        & ~S3 rmhist p & ~S4 rmhist p";
by (auto_tac (MI_css addsimps2 [S_def,S1_def,S2_def,S3_def,S4_def,S5_def]));
qed "S5_excl";

Goal "|- S6 rmhist p --> S6 rmhist p & ~S1 rmhist p & ~S2 rmhist p  \
\                        & ~S3 rmhist p & ~S4 rmhist p & ~S5 rmhist p";
by (auto_tac (MI_css addsimps2 [S_def,S1_def,S2_def,S3_def,S4_def,S5_def,S6_def]));
qed "S6_excl";


(* ==================== Lemmas about the environment ============================== *)

Goal "|- $(Calling memCh p) --> ~ENext p";
by (auto_tac (MI_css addsimps2 [ENext_def,Call_def]));
qed "Envbusy";

(* ==================== Lemmas about the implementation's states ==================== *)

(* The following series of lemmas are used in establishing the implementation's
   next-state relation (Step 1.2 of the proof in the paper). For each state Si, we
   determine which component actions are possible and what state they result in.
*)

(* ------------------------------ State S1 ---------------------------------------- *) 

Goal "|- ENext p & $(S1 rmhist p) & unchanged (c p, r p, m p, rmhist!p) \
\        --> (S2 rmhist p)$";
by (force_tac (MI_css addsimps2 [ENext_def,Call_def,c_def,r_def,m_def,
                                 caller_def,rtrner_def,MVNROKBA_def,
                                 S_def,S1_def,S2_def,Calling_def]) 1);
qed "S1Env";

Goal "|- [MClkNext memCh crCh cst p]_(c p) & $(S1 rmhist p) --> unchanged (c p)";
by (auto_tac (MI_fast_css addSDs2 [MClkidle] addsimps2 [S_def,S1_def]));
qed "S1ClerkUnch";

Goal "|- [RPCNext crCh rmCh rst p]_(r p) & $(S1 rmhist p) --> unchanged (r p)";
by (auto_tac (MI_fast_css addSDs2 [RPCidle] addsimps2 [S_def,S1_def]));
qed "S1RPCUnch";

Goal "|- [RNext rmCh mm ires p]_(m p) & $(S1 rmhist p) --> unchanged (m p)";
by (auto_tac (MI_fast_css addSDs2 [Memoryidle] addsimps2 [S_def,S1_def]));
qed "S1MemUnch";

Goal "|- [HNext rmhist p]_(c p,r p,m p,rmhist!p) & $(S1 rmhist p)\
\        --> unchanged (rmhist!p)";
by (action_simp_tac (simpset() addsimps [HNext_def, S_def, S1_def, MemReturn_def, 
                                         RPCFail_def,MClkReply_def,Return_def])
                    [] [squareE] 1);
qed "S1Hist";

(* ------------------------------ State S2 ---------------------------------------- *)

Goal "|- [ENext p]_(e p) & $(S2 rmhist p) --> unchanged (e p)";
by (auto_tac (MI_css addSDs2 [Envbusy] addsimps2 [S_def,S2_def]));
qed "S2EnvUnch";

Goal "|- MClkNext memCh crCh cst p & $(S2 rmhist p) --> MClkFwd memCh crCh cst p";
by (auto_tac (MI_css addsimps2 [MClkNext_def,MClkRetry_def,MClkReply_def,
                                S_def,S2_def]));
qed "S2Clerk";

Goal "|- $(S2 rmhist p) & MClkFwd memCh crCh cst p\
\        & unchanged (e p, r p, m p, rmhist!p) \
\        --> (S3 rmhist p)$";
by (action_simp_tac 
         (simpset() addsimps
                [MClkFwd_def,Call_def,e_def,r_def,m_def,caller_def,rtrner_def,
                 S_def,S2_def,S3_def,Calling_def])
         [] [] 1);
qed "S2Forward";

Goal "|- [RPCNext crCh rmCh rst p]_(r p) & $(S2 rmhist p) --> unchanged (r p)";
by (auto_tac (MI_css addsimps2 [S_def,S2_def] addSDs2 [RPCidle]));
qed "S2RPCUnch";

Goal "|- [RNext rmCh mm ires p]_(m p) & $(S2 rmhist p) --> unchanged (m p)";
by (auto_tac (MI_css addsimps2 [S_def,S2_def] addSDs2 [Memoryidle]));
qed "S2MemUnch";

Goal "|- [HNext rmhist p]_(c p,r p,m p,rmhist!p) & $(S2 rmhist p)\
\        --> unchanged (rmhist!p)";
by (auto_tac (MI_fast_css
		addsimps2 [HNext_def,MemReturn_def,
		           RPCFail_def,MClkReply_def,Return_def,S_def,S2_def]));
qed "S2Hist";

(* ------------------------------ State S3 ---------------------------------------- *)

Goal "|- [ENext p]_(e p) & $(S3 rmhist p) --> unchanged (e p)";
by (auto_tac (MI_css addSDs2 [Envbusy] addsimps2 [S_def,S3_def]));
qed "S3EnvUnch";

Goal "|- [MClkNext memCh crCh cst p]_(c p) & $(S3 rmhist p) --> unchanged (c p)";
by (auto_tac (MI_css addSDs2 [MClkbusy] addsimps2 [square_def,S_def,S3_def]));
qed "S3ClerkUnch";

Goal "|- S3 rmhist p --> IsLegalRcvArg<arg<crCh!p>>";
by (auto_tac (MI_css addsimps2 [IsLegalRcvArg_def,MClkRelayArg_def,S_def,S3_def]));
qed "S3LegalRcvArg";

Goal "|- RPCNext crCh rmCh rst p & $(S3 rmhist p) \
\        --> RPCFwd crCh rmCh rst p | RPCFail crCh rmCh rst p";
by (Clarsimp_tac 1);
by (forward_tac [action_use S3LegalRcvArg] 1);
by (auto_tac (MI_css addsimps2 [RPCNext_def,RPCReject_def,RPCReply_def,S_def,S3_def]));
qed "S3RPC";

Goal "|- RPCFwd crCh rmCh rst p & HNext rmhist p & $(S3 rmhist p)\
\        & unchanged (e p, c p, m p) \
\        --> (S4 rmhist p)$ & unchanged (rmhist!p)";
by (action_simp_tac 
      (simpset() addsimps [RPCFwd_def,HNext_def,MemReturn_def,RPCFail_def,MClkReply_def,
	                   Return_def,Call_def,e_def,c_def,m_def,caller_def,rtrner_def, 
                           S_def,S3_def,S4_def,Calling_def])
      [] [] 1);
qed "S3Forward";

Goal "|- RPCFail crCh rmCh rst p & $(S3 rmhist p) & HNext rmhist p\
\        & unchanged (e p, c p, m p) \
\        --> (S6 rmhist p)$";
by (action_simp_tac 
      (simpset() addsimps [HNext_def,RPCFail_def,Return_def,e_def,c_def,m_def,
			   caller_def,rtrner_def,MVOKBARF_def,
			   S_def,S3_def,S6_def,Calling_def])
      [] [] 1);
qed "S3Fail";

Goal "|- [RNext rmCh mm ires p]_(m p) & $(S3 rmhist p) --> unchanged (m p)";
by (auto_tac (MI_css addsimps2 [S_def,S3_def] addSDs2 [Memoryidle]));
qed "S3MemUnch";

Goal "|- HNext rmhist p & $(S3 rmhist p) & unchanged (r p) --> unchanged (rmhist!p)";
by (auto_tac (MI_css addsimps2 [HNext_def,MemReturn_def,RPCFail_def,MClkReply_def,
			        Return_def,r_def,rtrner_def,S_def,S3_def,Calling_def]));
qed "S3Hist";

(* ------------------------------ State S4 ---------------------------------------- *)

Goal "|- [ENext p]_(e p) & $(S4 rmhist p) --> unchanged (e p)";
by (auto_tac (MI_css addsimps2 [S_def,S4_def] addSDs2 [Envbusy]));
qed "S4EnvUnch";

Goal "|- [MClkNext memCh crCh cst p]_(c p) & $(S4 rmhist p) --> unchanged (c p)";
by (auto_tac (MI_css addsimps2 [S_def,S4_def] addSDs2 [MClkbusy]));
qed "S4ClerkUnch";

Goal "|- [RPCNext crCh rmCh rst p]_(r p) & $(S4 rmhist p) --> unchanged (r p)";
by (auto_tac (MI_fast_css addsimps2 [S_def,S4_def] addSDs2 [RPCbusy]));
qed "S4RPCUnch";

Goal "|- ReadInner rmCh mm ires p l & $(S4 rmhist p) & unchanged (e p, c p, r p) \
\        & HNext rmhist p & $(MemInv mm l) \
\        --> (S4 rmhist p)$ & unchanged (rmhist!p)";
by (action_simp_tac 
      (simpset() addsimps [ReadInner_def,GoodRead_def, BadRead_def,HNext_def,
			   MemReturn_def, RPCFail_def,MClkReply_def,Return_def,
			   e_def,c_def,r_def,rtrner_def,caller_def,MVNROKBA_def,
			   S_def,S4_def,RdRequest_def,Calling_def,MemInv_def])
      [] [] 1);
qed "S4ReadInner";

Goal "|- Read rmCh mm ires p & $(S4 rmhist p) & unchanged (e p, c p, r p) \
\        & HNext rmhist p & (!l. $MemInv mm l) \
\        --> (S4 rmhist p)$ & unchanged (rmhist!p)";
by (auto_tac (MI_css addsimps2 [Read_def] addSDs2 [S4ReadInner]));
qed "S4Read";

Goal "|- WriteInner rmCh mm ires p l v & $(S4 rmhist p) & unchanged (e p, c p, r p) \
\        & HNext rmhist p \
\        --> (S4 rmhist p)$ & unchanged (rmhist!p)";
by (action_simp_tac 
      (simpset() addsimps [WriteInner_def,GoodWrite_def, BadWrite_def,HNext_def,
			   MemReturn_def,RPCFail_def,MClkReply_def,Return_def,
			   e_def,c_def,r_def,rtrner_def,caller_def,MVNROKBA_def, 
			   S_def,S4_def,WrRequest_def,Calling_def])
      [] [] 1);
qed "S4WriteInner";

Goal "|- Write rmCh mm ires p l & $(S4 rmhist p) & unchanged (e p, c p, r p)\
\        & (HNext rmhist p) \
\        --> (S4 rmhist p)$ & unchanged (rmhist!p)";
by (auto_tac (MI_css addsimps2 [Write_def] addSDs2 [S4WriteInner]));
qed "S4Write";

Goal "|- $ImpInv rmhist p & Write rmCh mm ires p l --> $S4 rmhist p";
by (auto_tac (MI_css addsimps2 [Write_def,WriteInner_def,ImpInv_def,WrRequest_def,
			        S_def,S1_def,S2_def,S3_def,S4_def,S5_def,S6_def]));
qed "WriteS4";

Goal "|- MemReturn rmCh ires p & $S4 rmhist p & unchanged (e p, c p, r p)\
\        & HNext rmhist p \
\        --> (S5 rmhist p)$";
by (auto_tac (MI_css addsimps2 [HNext_def,MemReturn_def,Return_def,e_def,c_def,r_def,
				rtrner_def,caller_def,MVNROKBA_def,MVOKBA_def,
		                S_def,S4_def,S5_def,Calling_def]));
qed "S4Return";

Goal "|- HNext rmhist p & $S4 rmhist p & (m p)$ = $(m p) --> (rmhist!p)$ = $(rmhist!p)";
by (auto_tac (MI_css addsimps2 [HNext_def,MemReturn_def,RPCFail_def,MClkReply_def,
				Return_def,m_def,rtrner_def,S_def,S4_def,Calling_def]));
qed "S4Hist";

(* ------------------------------ State S5 ---------------------------------------- *)

Goal "|- [ENext p]_(e p) & $(S5 rmhist p) --> unchanged (e p)";
by (auto_tac (MI_css addsimps2 [S_def,S5_def] addSDs2 [Envbusy]));
qed "S5EnvUnch";

Goal "|- [MClkNext memCh crCh cst p]_(c p) & $(S5 rmhist p) --> unchanged (c p)";
by (auto_tac (MI_css addsimps2 [S_def,S5_def] addSDs2 [MClkbusy]));
qed "S5ClerkUnch";

Goal "|- RPCNext crCh rmCh rst p & $(S5 rmhist p)   \
\        --> RPCReply crCh rmCh rst p | RPCFail crCh rmCh rst p";
by (auto_tac (MI_css addsimps2 [RPCNext_def,RPCReject_def,RPCFwd_def,S_def,S5_def]));
qed "S5RPC";

Goal "|- RPCReply crCh rmCh rst p & $(S5 rmhist p) & unchanged (e p, c p, m p,rmhist!p)\
\      --> (S6 rmhist p)$";
by (action_simp_tac 
      (simpset() addsimps [RPCReply_def,Return_def,e_def,c_def,m_def,
			   MVOKBA_def,MVOKBARF_def,caller_def,rtrner_def,
			   S_def,S5_def,S6_def,Calling_def])
      [] [] 1);
qed "S5Reply";

Goal "|- RPCFail crCh rmCh rst p & $(S5 rmhist p) & unchanged (e p, c p, m p,rmhist!p) \
\        --> (S6 rmhist p)$";
by (action_simp_tac
      (simpset() addsimps [RPCFail_def,Return_def,e_def,c_def,m_def,
			   MVOKBARF_def,caller_def,rtrner_def,
			   S_def,S5_def,S6_def,Calling_def])
      [] [] 1);
qed "S5Fail";

Goal "|- [RNext rmCh mm ires p]_(m p) & $(S5 rmhist p) --> unchanged (m p)";
by (auto_tac (MI_css addsimps2 [S_def,S5_def] addSDs2 [Memoryidle]));
qed "S5MemUnch";

Goal "|- [HNext rmhist p]_(c p, r p, m p, rmhist!p) & $(S5 rmhist p)\
\        --> (rmhist!p)$ = $(rmhist!p)";
by (auto_tac (MI_fast_css
	      addsimps2 [HNext_def,MemReturn_def,
		         RPCFail_def,MClkReply_def,Return_def,S_def,S5_def]));
qed "S5Hist";

(* ------------------------------ State S6 ---------------------------------------- *)

Goal "|- [ENext p]_(e p) & $(S6 rmhist p) --> unchanged (e p)";
by (auto_tac (MI_css addsimps2 [S_def,S6_def] addSDs2 [Envbusy]));
qed "S6EnvUnch";

Goal "|- MClkNext memCh crCh cst p & $(S6 rmhist p) \
\        --> MClkRetry memCh crCh cst p | MClkReply memCh crCh cst p";
by (auto_tac (MI_css addsimps2 [MClkNext_def,MClkFwd_def,S_def,S6_def]));
qed "S6Clerk";

Goal "|- MClkRetry memCh crCh cst p & HNext rmhist p & $S6 rmhist p\
\        & unchanged (e p,r p,m p) \
\        --> (S3 rmhist p)$ & unchanged (rmhist!p)";
by (action_simp_tac
      (simpset() addsimps [HNext_def,MClkReply_def,MClkRetry_def,Call_def,
	                   Return_def,e_def,r_def,m_def,caller_def,rtrner_def,
                           S_def,S6_def,S3_def,Calling_def])
      [] [] 1);
qed "S6Retry";

Goal "|- MClkReply memCh crCh cst p & HNext rmhist p & $S6 rmhist p\
\        & unchanged (e p,r p,m p) \
\        --> (S1 rmhist p)$";
by (action_simp_tac 
      (simpset() addsimps [HNext_def,MemReturn_def,RPCFail_def,Return_def,
		           MClkReply_def,e_def,r_def,m_def,caller_def,rtrner_def,
                           S_def,S6_def,S1_def,Calling_def])
      [] [] 1);
qed "S6Reply";

Goal "|- [RPCNext crCh rmCh rst p]_(r p) & $S6 rmhist p --> unchanged (r p)";
by (auto_tac (MI_css addsimps2 [S_def,S6_def] addSDs2 [RPCidle]));
qed "S6RPCUnch";

Goal "|- [RNext rmCh mm ires p]_(m p) & $(S6 rmhist p) --> unchanged (m p)";
by (auto_tac (MI_css addsimps2 [S_def,S6_def] addSDs2 [Memoryidle]));
qed "S6MemUnch";

Goal "|- HNext rmhist p & $S6 rmhist p & (c p)$ = $(c p) --> (rmhist!p)$ = $(rmhist!p)";
by (auto_tac (MI_css addsimps2 [HNext_def,MClkReply_def,Return_def,c_def,rtrner_def,
		                S_def,S6_def,Calling_def]));
qed "S6Hist";
