(* 
    File:        MIlive.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: Lower-level lemmas for the liveness proof
*)

(* Liveness assertions for the different implementation states, based on the
   fairness conditions. Prove subgoals of WF1 / SF1 rules as separate lemmas
   for readability. Reuse action proofs from safety part.
*)

(* ------------------------------ State S1 ------------------------------ *)

qed_goal "S1_successors" MemoryImplementation.thy
   "$(S1 rmhist p) .& ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>  \
\   .-> $(S1 rmhist p)` .| $(S2 rmhist p)`"
   (fn _ => [split_idle_tac [] 1,
	     auto_tac (MI_css addSEs2 [action_conjimpE Step1_2_1])
	    ]);

(* Show that the implementation can satisfy the high-level fairness requirements
   by entering the state S1 infinitely often.
*)

qed_goal "S1_RNextdisabled" MemoryImplementation.thy
   "$(S1 rmhist p) .-> \
\   .~$(Enabled (<RNext memCh mem (resbar rmhist) p>_<rtrner memCh @ p, resbar rmhist @ p>))"
   (fn _ => [action_simp_tac (simpset() addsimps [angle_def,S_def,S1_def])
	                     [notI] [enabledE,MemoryidleE] 1,
	     auto_tac MI_fast_css
	    ]);

qed_goal "S1_Returndisabled" MemoryImplementation.thy
   "$(S1 rmhist p) .-> \
\   .~$(Enabled (<MemReturn memCh (resbar rmhist) p>_<rtrner memCh @ p, resbar rmhist @ p>))"
   (fn _ => [action_simp_tac (simpset() addsimps [angle_def,MemReturn_def,Return_def,S_def,S1_def])
	                     [notI] [enabledE] 1
	    ]);

qed_goal "RNext_fair" MemoryImplementation.thy
   "!!sigma. (sigma |= []<>($(S1 rmhist p)))   \
\     ==> (sigma |= WF(RNext memCh mem (resbar rmhist) p)_<rtrner memCh @ p, resbar rmhist @ p>)"
   (fn _ => [auto_tac (MI_css addsimps2 [temp_rewrite WF_alt]
			      addSIs2 [S1_RNextdisabled] addSEs2 [STL4E,DmdImplE])
	    ]);

qed_goal "Return_fair" MemoryImplementation.thy
   "!!sigma. (sigma |= []<>($(S1 rmhist p)))   \
\     ==> (sigma |= WF(MemReturn memCh (resbar rmhist) p)_<rtrner memCh @ p, resbar rmhist @ p>)"
   (fn _ => [auto_tac (MI_css addsimps2 [temp_rewrite WF_alt]
			      addSIs2 [S1_Returndisabled] addSEs2 [STL4E,DmdImplE])
	    ]);

(* ------------------------------ State S2 ------------------------------ *)

qed_goal "S2_successors" MemoryImplementation.thy
   "$(S2 rmhist p) .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>)   \
\   .-> $(S2 rmhist p)` .| $(S3 rmhist p)`"
   (fn _ => [split_idle_tac [] 1,
	     auto_tac (MI_css addSEs2 [action_conjimpE Step1_2_2])
	    ]);

qed_goal "S2MClkFwd_successors" MemoryImplementation.thy
   "$(S2 rmhist p) .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>)    \
\                  .& <MClkFwd memCh crCh cst p>_(c p) \
\   .-> $(S3 rmhist p)`"
   (fn _ => [ auto_tac (MI_css addsimps2 [angle_def] addSEs2 [action_conjimpE Step1_2_2]) ]);

qed_goal "S2MClkFwd_enabled" MemoryImplementation.thy
   "$(S2 rmhist p) .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>)   \
\   .-> $(Enabled (<MClkFwd memCh crCh cst p>_(c p)))"
   (fn _ => [cut_facts_tac [MI_base] 1,
	     auto_tac (MI_css addsimps2 [c_def,base_pair]
		              addSIs2 [MClkFwd_ch_enabled,action_mp MClkFwd_enabled]),
	     ALLGOALS (action_simp_tac (simpset() addsimps [S_def,S2_def]) [] [])
	    ]);

qed_goal "S2_live" MemoryImplementation.thy
   "[](ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>) .& WF(MClkFwd memCh crCh cst p)_(c p) \
\   .-> ($(S2 rmhist p) ~> $(S3 rmhist p))"
   (fn _ => [REPEAT (resolve_tac [WF1,S2_successors,
				  S2MClkFwd_successors,S2MClkFwd_enabled] 1)
	    ]);


(* ------------------------------ State S3 ------------------------------ *)

qed_goal "S3_successors" MemoryImplementation.thy
   "$(S3 rmhist p) .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>)   \
\   .-> $(S3 rmhist p)` .| ($(S4 rmhist p) .| $(S6 rmhist p))`"
   (fn _ => [split_idle_tac [] 1,
	     auto_tac (MI_css addSEs2 [action_conjimpE Step1_2_3])
	    ]);

qed_goal "S3RPC_successors" MemoryImplementation.thy
   "$(S3 rmhist p) .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>)   \
\                  .& <RPCNext crCh rmCh rst p>_(r p) \
\   .-> ($(S4 rmhist p) .| $(S6 rmhist p))`"
   (fn _ => [ auto_tac (MI_css addsimps2 [angle_def] addSEs2 [action_conjimpE Step1_2_3]) ]);

qed_goal "S3RPC_enabled" MemoryImplementation.thy
   "$(S3 rmhist p) .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>)   \
\   .-> $(Enabled (<RPCNext crCh rmCh rst p>_(r p)))"
   (fn _ => [cut_facts_tac [MI_base] 1,
	     auto_tac (MI_css addsimps2 [r_def,base_pair]
		              addSIs2 [RPCFail_Next_enabled,action_mp RPCFail_enabled]),
	     ALLGOALS (action_simp_tac (simpset() addsimps [S_def,S3_def]) [] [])
	    ]);

qed_goal "S3_live" MemoryImplementation.thy
   "[](ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>)  \
\        .& WF(RPCNext crCh rmCh rst p)_(r p) \
\   .-> ($(S3 rmhist p) ~> ($(S4 rmhist p) .| $(S6 rmhist p)))"
   (fn _ => [REPEAT (resolve_tac [WF1,S3_successors,S3RPC_successors,S3RPC_enabled] 1)]);

(* ------------- State S4 -------------------------------------------------- *)

qed_goal "S4_successors" MemoryImplementation.thy
   "$(S4 rmhist p) .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p> \
\                                .& (RALL l. $(MemInv mem l)))  \
\   .-> $(S4 rmhist p)` .| $(S5 rmhist p)`"
   (fn _ => [split_idle_tac [] 1,
	     auto_tac (MI_css addSEs2 [action_conjimpE Step1_2_4])
	    ]);

(* ------------- State S4a: S4 /\ (ires p = NotAResult) ------------------------------ *)

qed_goal "S4a_successors" MemoryImplementation.thy
   "($(S4 rmhist p) .& ($(ires@p) .= #NotAResult)) \
\                   .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p> \
\                                 .& (RALL l. $(MemInv mem l))) \
\   .-> ($(S4 rmhist p) .& ($(ires@p) .= #NotAResult))`  \
\       .| (($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) .| $(S5 rmhist p))`"
   (fn _ => [split_idle_tac [m_def] 1,
	     auto_tac (MI_css addsimps2 [m_def] addSEs2 [action_conjimpE Step1_2_4])
	    ]);

qed_goal "S4aRNext_successors" MemoryImplementation.thy
   "($(S4 rmhist p) .& ($(ires@p) .= #NotAResult))  \
\   .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>   \
\                 .& (RALL l. $(MemInv mem l)))  \
\   .& <RNext rmCh mem ires p>_(m p) \
\   .-> (($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) .| $(S5 rmhist p))`"
   (fn _ => [auto_tac (MI_css addsimps2 [angle_def]
		              addSEs2 [action_conjimpE Step1_2_4,
				       action_conjimpE ReadResult, action_impE WriteResult])
	    ]);

qed_goal "S4aRNext_enabled" MemoryImplementation.thy
   "($(S4 rmhist p) .& ($(ires@p) .= #NotAResult)) \
\   .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>   \
\                 .& (RALL l. $(MemInv mem l)))  \
\   .-> $(Enabled (<RNext rmCh mem ires p>_(m p)))"
   (fn _ => [auto_tac (MI_css addsimps2 [m_def] addSIs2 [action_mp RNext_enabled]),
	     ALLGOALS (cut_facts_tac [MI_base]),
	     auto_tac (MI_css addsimps2 [base_pair]),
	        (* it's faster to expand S4 only where necessary *)
	     action_simp_tac (simpset() addsimps [S_def,S4_def]) [] [] 1
	    ]);

qed_goal "S4a_live" MemoryImplementation.thy
  "[](ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p> .& (RALL l. $(MemInv mem l))) \
\  .& WF(RNext rmCh mem ires p)_(m p) \
\  .-> (($(S4 rmhist p) .& ($(ires@p) .= #NotAResult))  \
\        ~> ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) .| $(S5 rmhist p))"
   (fn _ => [rtac WF1 1,
	     ALLGOALS (action_simp_tac (simpset())
		                       (map ((rewrite_rule [slice_def]) o action_mp) 
                                            [S4a_successors,S4aRNext_successors,S4aRNext_enabled])
				       [])
	    ]);

(* ------------- State S4b: S4 /\ (ires p # NotAResult) ------------------------------ *)

qed_goal "S4b_successors" MemoryImplementation.thy
   "($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult))  \
\                   .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p> \
\                                 .& (RALL l. $(MemInv mem l))) \
\   .-> ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult))` .| $(S5 rmhist p)`"
   (fn _ => [split_idle_tac [m_def] 1,
	     auto_tac (MI_css addSEs2 (action_impE WriteResult
				       :: map action_conjimpE [Step1_2_4,ReadResult]))
	    ]);

qed_goal "S4bReturn_successors" MemoryImplementation.thy
   "($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult))  \
\   .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p> \
\                 .& (RALL l. $(MemInv mem l)))   \
\   .& <MemReturn rmCh ires p>_(m p) \
\   .-> ($(S5 rmhist p))`"
   (fn _ => [auto_tac (MI_css addsimps2 [angle_def]
	                      addSEs2 [action_conjimpE Step1_2_4]
		              addEs2 [action_conjimpE ReturnNotReadWrite])
	    ]);

qed_goal "S4bReturn_enabled" MemoryImplementation.thy
   "($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult))  \
\   .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p> \
\                 .& (RALL l. $(MemInv mem l)))  \
\   .-> $(Enabled (<MemReturn rmCh ires p>_(m p)))"
   (fn _ => [cut_facts_tac [MI_base] 1,
             auto_tac (MI_css addsimps2 [m_def,base_pair]
		              addSIs2 [action_mp MemReturn_enabled]),
	     ALLGOALS (action_simp_tac (simpset() addsimps [S_def,S4_def]) [] [])
	    ]);

qed_goal "S4b_live" MemoryImplementation.thy
  "[](ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p> .& (RALL l. $(MemInv mem l))) \
\  .& WF(MemReturn rmCh ires p)_(m p) \
\  .-> (($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) ~> $(S5 rmhist p))"
   (fn _ => [rtac WF1 1,
	     ALLGOALS (action_simp_tac (simpset())
		                       (map ((rewrite_rule [slice_def]) o action_mp) 
                                            [S4b_successors,S4bReturn_successors,S4bReturn_enabled])
				       [allE])
	    ]);

(* ------------------------------ State S5 ------------------------------ *)

qed_goal "S5_successors" MemoryImplementation.thy
   "$(S5 rmhist p) .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>) \
\   .-> $(S5 rmhist p)` .| $(S6 rmhist p)`"
   (fn _ => [split_idle_tac [] 1,
	     auto_tac (MI_css addSEs2 [action_conjimpE Step1_2_5])
	    ]);

qed_goal "S5RPC_successors" MemoryImplementation.thy
   "$(S5 rmhist p) .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>) \
\   .& <RPCNext crCh rmCh rst p>_(r p) \
\   .-> $(S6 rmhist p)`"
   (fn _ => [ auto_tac (MI_css addsimps2 [angle_def] addSEs2 [action_conjimpE Step1_2_5]) ]);

qed_goal "S5RPC_enabled" MemoryImplementation.thy
   "$(S5 rmhist p) .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>) \
\   .-> $(Enabled (<RPCNext crCh rmCh rst p>_(r p)))"
   (fn _ => [cut_facts_tac [MI_base] 1,
	     auto_tac (MI_css addsimps2 [r_def,base_pair]
		              addSIs2 [RPCFail_Next_enabled,action_mp RPCFail_enabled]),
	     ALLGOALS (action_simp_tac (simpset() addsimps [S_def,S5_def]) [] [])
	    ]);

qed_goal "S5_live" MemoryImplementation.thy
   "[](ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>)   \
\   .& WF(RPCNext crCh rmCh rst p)_(r p) \
\   .-> ($(S5 rmhist p) ~> $(S6 rmhist p))"
   (fn _ => [REPEAT (resolve_tac [WF1,S5_successors,S5RPC_successors,S5RPC_enabled] 1)]);


(* ------------------------------ State S6 ------------------------------ *)

qed_goal "S6_successors" MemoryImplementation.thy
   "$(S6 rmhist p) .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>) \
\   .-> $(S1 rmhist p)` .| $(S3 rmhist p)` .| $(S6 rmhist p)`"
   (fn _ => [split_idle_tac [] 1,
	     auto_tac (MI_css addSEs2 [action_conjimpE Step1_2_6])
	    ]);

qed_goal "S6MClkReply_successors" MemoryImplementation.thy
   "$(S6 rmhist p) .& (ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>) \
\   .& <MClkReply memCh crCh cst p>_(c p) \
\   .-> $(S1 rmhist p)`"
   (fn _ => [auto_tac (MI_css addsimps2 [angle_def] addSEs2 [action_conjimpE Step1_2_6,
							     action_impE MClkReplyNotRetry])
	    ]);

qed_goal "MClkReplyS6" MemoryImplementation.thy
   "$(ImpInv rmhist p) .& <MClkReply memCh crCh cst p>_(c p) .-> $(S6 rmhist p)"
   (fn _ => [action_simp_tac
	        (simpset() addsimps
		    [angle_def,MClkReply_def,Return_def,
		     ImpInv_def,S_def,S1_def,S2_def,S3_def,S4_def,S5_def])
		[] [] 1
	    ]);

qed_goal "S6MClkReply_enabled" MemoryImplementation.thy
   "$(S6 rmhist p) .-> $(Enabled (<MClkReply memCh crCh cst p>_(c p)))"
   (fn _ => [cut_facts_tac [MI_base] 1,
	     auto_tac (MI_css addsimps2 [c_def,base_pair]
		              addSIs2 [action_mp MClkReply_enabled]),
	     ALLGOALS (action_simp_tac (simpset() addsimps [S_def,S6_def]) [] [])
	    ]);

qed_goal "S6_live" MemoryImplementation.thy
   "[](ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p> .& $(ImpInv rmhist p)) \
\   .& SF(MClkReply memCh crCh cst p)_(c p) .& []<>($(S6 rmhist p))  \
\   .-> []<>($(S1 rmhist p))"
   (fn _ => [Auto_tac,
	     subgoal_tac "sigma |= []<>(<MClkReply memCh crCh cst p>_(c p))" 1,
	     eres_inst_tac [("P","<MClkReply memCh crCh cst p>_(c p)")]
	                   EnsuresInfinite 1, atac 1,
	     action_simp_tac (simpset()) []
	                     (map action_conjimpE [MClkReplyS6,S6MClkReply_successors]) 1,
	     auto_tac (MI_css addsimps2 [SF_def]),
	     etac swap 1,
	     auto_tac (MI_css addSIs2 [action_mp S6MClkReply_enabled]
		              addSEs2 [STL4E,DmdImplE])
	    ]);

(* ------------------------------ complex leadsto properties ------------------------------ *)

qed_goal "S5S6LeadstoS6" MemoryImplementation.thy
   "!!sigma. (sigma |= $(S5 rmhist p) ~> $(S6 rmhist p)) \
\      ==> (sigma |= ($(S5 rmhist p) .| $(S6 rmhist p)) ~> $(S6 rmhist p))"
   (fn _ => [auto_tac (MI_css addSIs2 [LatticeDisjunctionIntro,
				       temp_unlift LatticeReflexivity])
	    ]);

qed_goal "S4bS5S6LeadstoS6" MemoryImplementation.thy
   "!!sigma. [| (sigma |= ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) ~> $(S5 rmhist p));  \
\               (sigma |= $(S5 rmhist p) ~> $(S6 rmhist p)) |]  \
\      ==> (sigma |= (($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) .| $(S5 rmhist p) .| $(S6 rmhist p)) ~> $(S6 rmhist p))"
   (fn _ => [auto_tac (MI_css addSIs2 [LatticeDisjunctionIntro,S5S6LeadstoS6]
		              addIs2 [LatticeTransitivity])
            ]);

qed_goal "S4S5S6LeadstoS6" MemoryImplementation.thy
   "!!sigma. [| (sigma |= ($(S4 rmhist p) .& ($(ires@p) .= #NotAResult)) \
\                             ~> ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) .| $(S5 rmhist p)); \
\               (sigma |= ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) ~> $(S5 rmhist p));  \
\               (sigma |= $(S5 rmhist p) ~> $(S6 rmhist p)) |]  \
\      ==> (sigma |= ($(S4 rmhist p) .| $(S5 rmhist p) .| $(S6 rmhist p)) ~> $(S6 rmhist p))"
   (fn _ => [subgoal_tac "sigma |= (($(S4 rmhist p) .& ($(ires@p) .= #NotAResult)) .| ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) .| $(S5 rmhist p) .| $(S6 rmhist p)) ~> $(S6 rmhist p)" 1,
	     eres_inst_tac [("G", "($(S4 rmhist p) .& ($(ires@p) .= #NotAResult)) .| ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) .| $(S5 rmhist p) .| $(S6 rmhist p)")] LatticeTransitivity 1,
	     SELECT_GOAL (auto_tac (MI_css addSIs2 [ImplLeadsto, temp_unlift necT])) 1,
	     rtac LatticeDisjunctionIntro 1,
	     etac LatticeTransitivity 1,
	     etac LatticeTriangle 1, atac 1,
	     auto_tac (MI_css addSIs2 [S4bS5S6LeadstoS6])
	    ]);

qed_goal "S3S4S5S6LeadstoS6" MemoryImplementation.thy
   "!!sigma. [| (sigma |= $(S3 rmhist p) ~> ($(S4 rmhist p) .| $(S6 rmhist p)));   \
\               (sigma |= ($(S4 rmhist p) .& ($(ires@p) .= #NotAResult)) \
\                         ~> ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) .| $(S5 rmhist p)); \
\               (sigma |= ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) ~> $(S5 rmhist p));  \
\               (sigma |= $(S5 rmhist p) ~> $(S6 rmhist p)) |]  \
\      ==> (sigma |= ($(S3 rmhist p) .| $(S4 rmhist p) .| $(S5 rmhist p) .| $(S6 rmhist p)) ~> $(S6 rmhist p))"
   (fn _ => [rtac LatticeDisjunctionIntro 1,
	     rtac LatticeTriangle 1, atac 2,
	     rtac (S4S5S6LeadstoS6 RS LatticeTransitivity) 1,
	     auto_tac (MI_css addSIs2 [S4S5S6LeadstoS6,temp_unlift necT]
			      addIs2 [ImplLeadsto])
	    ]);

qed_goal "S2S3S4S5S6LeadstoS6" MemoryImplementation.thy
   "!!sigma. [| (sigma |= $(S2 rmhist p) ~> $(S3 rmhist p)); \
\               (sigma |= $(S3 rmhist p) ~> ($(S4 rmhist p) .| $(S6 rmhist p)));   \
\               (sigma |= ($(S4 rmhist p) .& ($(ires@p) .= #NotAResult)) \
\                         ~> ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) .| $(S5 rmhist p)); \
\               (sigma |= ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) ~> $(S5 rmhist p));  \
\               (sigma |= $(S5 rmhist p) ~> $(S6 rmhist p)) |]  \
\      ==> (sigma |= ($(S2 rmhist p) .| $(S3 rmhist p) .| $(S4 rmhist p) .| $(S5 rmhist p) .| $(S6 rmhist p)) ~> $(S6 rmhist p))"
   (fn _ => [rtac LatticeDisjunctionIntro 1,
	     rtac LatticeTransitivity 1, atac 2,
	     rtac (S3S4S5S6LeadstoS6 RS LatticeTransitivity) 1,
	     auto_tac (MI_css addSIs2 [S3S4S5S6LeadstoS6,temp_unlift necT]
			      addIs2 [ImplLeadsto])
	    ]);

qed_goal "NotS1LeadstoS6" MemoryImplementation.thy
   "!!sigma. [| (sigma |= []($(ImpInv rmhist p))); \
\        (sigma |= $(S2 rmhist p) ~> $(S3 rmhist p)); \
\        (sigma |= $(S3 rmhist p) ~> ($(S4 rmhist p) .| $(S6 rmhist p))); \
\        (sigma |= ($(S4 rmhist p) .& ($(ires@p) .= #NotAResult)) \
\                  ~> ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) .| $(S5 rmhist p)); \
\        (sigma |= ($(S4 rmhist p) .& ($(ires@p) .~= #NotAResult)) ~> $(S5 rmhist p));  \
\        (sigma |= $(S5 rmhist p) ~> $(S6 rmhist p)) |] \
\        ==> (sigma |= .~$(S1 rmhist p) ~> $(S6 rmhist p))"
   (fn _ => [rtac (S2S3S4S5S6LeadstoS6 RS LatticeTransitivity) 1,
	     auto_tac (MI_css addsimps2 [ImpInv_def] addIs2 [ImplLeadsto] addSEs2 [STL4E])
	    ]);

qed_goal "S1Infinite" MemoryImplementation.thy
   "!!sigma. [| (sigma |= .~$(S1 rmhist p) ~> $(S6 rmhist p)); \
\               (sigma |= []<>($(S6 rmhist p)) .-> []<>($(S1 rmhist p))) |] \
\            ==> (sigma |= []<>($(S1 rmhist p)))"
   (fn _ => [rtac classical 1,
	     asm_full_simp_tac (simpset() addsimps [NotBox, temp_rewrite NotDmd]) 1,
	     auto_tac (MI_css addSEs2 [mp,leadsto_infinite] addSDs2 [temp_mp DBImplBDAct])
	    ]);
