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


(* ------------------------------ HOL lemmas ------------------------------ *)
(* Add the following simple lemmas as default simplification rules. *)

section "Auxiliary lemmas";

qed_goal "equal_false_not" HOL.thy "(P = False) = (~P)"
   (fn _ => [fast_tac prop_cs 1]);

Addsimps [equal_false_not];


(* A variant of the implication elimination rule that keeps the antecedent.
   Use "thm RS impdupE" to generate an unsafe (looping) elimination rule. 
*)

qed_goal "impdupE" HOL.thy
   "[| P --> Q; P; [| P;Q |] ==> R |] ==> R"
   (fn maj::prems => [REPEAT (resolve_tac ([maj RS mp] @ prems) 1)]);


(* Introduction/elimination rules for if-then-else *)

qed_goal "ifI" HOL.thy 
   "[| Q ==> P(x); ~Q ==> P(y) |] ==> P(if Q then x else y)"
   (fn prems => [case_tac "Q" 1, ALLGOALS (Asm_simp_tac THEN' (eresolve_tac prems))]);

qed_goal "ifE" HOL.thy
   "[| P(if Q then x else y); [| Q; P(x) |] ==> R; [| ~Q; P(y) |] ==> R |] ==> R"
   (fn (prem1::prems) => [case_tac "Q" 1,
                          ALLGOALS ((cut_facts_tac [prem1])
                                    THEN' Asm_full_simp_tac 
                                    THEN' (REPEAT o ((eresolve_tac prems) ORELSE' atac)))
                         ]);

(* --------------------------- automatic prover --------------------------- *)
(* Set up a clasimpset that contains data-level simplifications. *)

val MI_css = temp_css addsimps2 (CP_simps @ histState.simps
                                 @ [slice_def,equal_false_not,if_cancel,sum_case_Inl, sum_case_Inr]);

(* A more aggressive variant that tries to solve subgoals by assumption
   or contradiction during the simplification.
   THIS IS UNSAFE, BECAUSE IT DOESN'T RECORD THE CHOICES!!
   (but sometimes a lot faster than MI_css)
*)
val MI_fast_css =
  let 
    val (cs,ss) = MI_css
  in
    (cs, ss addSSolver (fn thms => assume_tac ORELSE' (etac notE)))
end;

(* Make sure the simpset accepts non-boolean simplifications *)
simpset_ref() := let val (_,ss) = MI_css in ss end;


(****************************** The history variable ******************************)
section "History variable";

qed_goal "HistoryLemma" MemoryImplementation.thy
   "Init(RALL p. $(ImpInit p)) .& [](RALL p. ImpNext p)  \
\   .-> (EEX rmhist.    Init(RALL p. $(HInit rmhist p)) \
\                    .& [](RALL p. [HNext rmhist p]_<c p, r p, m p, rmhist@p>))"
   (fn _ => [Auto_tac(),
             rtac historyI 1, TRYALL atac,
             action_simp_tac (simpset() addsimps [HInit_def]) [] [] 1,
             res_inst_tac [("x","p")] fun_cong 1, atac 1,
             action_simp_tac (simpset() addsimps [HNext_def]) [busy_squareI] [] 1,
             res_inst_tac [("x","p")] fun_cong 1, atac 1
            ]);

qed_goal "History" MemoryImplementation.thy
   "Implementation .-> (EEX rmhist. Hist rmhist)"
   (fn _ => [Auto_tac(),
             rtac ((temp_mp HistoryLemma) RS eex_mono) 1,
             SELECT_GOAL 
               (auto_tac (MI_css 
                          addsimps2 [Impl_def,MClkISpec_def,RPCISpec_def,IRSpec_def,
                                     MClkIPSpec_def,RPCIPSpec_def,RPSpec_def,
                                     ImpInit_def,Init_def,ImpNext_def,
                                     c_def,r_def,m_def,all_box,split_box_conj])) 1,
             auto_tac (MI_css 
                       addsimps2 [Hist_def,HistP_def,Init_def,all_box,split_box_conj])
            ]);

(******************************** The safety part *********************************)

section "The safety part";

(* ------------------------- Include lower-level lemmas ------------------------- *)
use "MIsafe.ML";

section "Correctness of predicate-action diagram";

(* ========== Step 1.1 ================================================= *)
(* The implementation's initial condition implies the state predicate S1 *)

qed_goal "Step1_1" MemoryImplementation.thy
   "$(ImpInit p) .& $(HInit rmhist p) .-> $(S1 rmhist p)"
   (fn _ => [auto_tac (MI_fast_css
		       addsimps2 [MVNROKBA_def,MClkInit_def,RPCInit_def,PInit_def,
			          HInit_def,ImpInit_def,S_def,S1_def])
	    ]);

(* ========== Step 1.2 ================================================== *)
(* Figure 16 is a predicate-action diagram for the implementation. *)

qed_goal "Step1_2_1" MemoryImplementation.thy
   "[HNext rmhist p]_<c p,r p,m p, rmhist@p> .& ImpNext p  \
\             .& .~ unchanged <e p, c p, r p, m p, rmhist@p>  .& $(S1 rmhist p) \
\   .-> (S2 rmhist p)$ .& (ENext p) .& unchanged <c p, r p, m p>"
   (fn _ => [auto_tac (MI_css addsimps2 [ImpNext_def]
		              addSEs2 [S1ClerkUnchE,S1RPCUnchE,S1MemUnchE,S1HistE]),
	     ALLGOALS (action_simp_tac (simpset() addsimps [square_def]) [] [S1EnvE])
	    ]);

qed_goal "Step1_2_2" MemoryImplementation.thy
   "[HNext rmhist p]_<c p,r p,m p, rmhist@p> .& ImpNext p  \
\             .& .~ unchanged <e p, c p, r p, m p, rmhist@p>  .& $(S2 rmhist p) \
\   .-> (S3 rmhist p)$ .& (MClkFwd memCh crCh cst p) .& unchanged <e p, r p, m p, rmhist@p>"
   (fn _ => [auto_tac (MI_css addsimps2 [ImpNext_def]
		              addSEs2 [S2EnvUnchE,S2RPCUnchE,S2MemUnchE,S2HistE]),
	     ALLGOALS (action_simp_tac (simpset() addsimps [square_def]) [] [S2ClerkE,S2ForwardE])
	    ]);

qed_goal "Step1_2_3" MemoryImplementation.thy
   "[HNext rmhist p]_<c p,r p,m p, rmhist@p> .& ImpNext p  \
\             .& .~ unchanged <e p, c p, r p, m p, rmhist@p>  .& $(S3 rmhist p) \
\   .-> ((S4 rmhist p)$ .& RPCFwd crCh rmCh rst p .& unchanged <e p, c p, m p, rmhist@p>) \
\        .| ((S6 rmhist p)$ .& RPCFail crCh rmCh rst p .& unchanged <e p, c p, m p>)"
   (fn _ => [action_simp_tac (simpset() addsimps [ImpNext_def])
	                     [] [S3EnvUnchE,S3ClerkUnchE,S3MemUnchE] 1,
             ALLGOALS (action_simp_tac (simpset() addsimps [square_def])
		                       [] [S3RPCE,S3ForwardE,S3FailE]),
             auto_tac (MI_css addEs2 [S3HistE])
	    ]);

qed_goal "Step1_2_4" MemoryImplementation.thy
   "[HNext rmhist p]_<c p,r p,m p, rmhist@p> .& ImpNext p  \
\             .& .~ unchanged <e p, c p, r p, m p, rmhist@p> \
\             .& $(S4 rmhist p) .& (RALL l. $(MemInv mem l))     \
\   .-> ((S4 rmhist p)$ .& Read rmCh mem ires p .& unchanged <e p, c p, r p, rmhist@p>) \
\        .| ((S4 rmhist p)$ .& (REX l. Write rmCh mem ires p l) .& unchanged <e p, c p, r p, rmhist@p>) \
\        .| ((S5 rmhist p)$ .& MemReturn rmCh ires p .& unchanged <e p, c p, r p>)"
   (fn _ => [action_simp_tac (simpset() addsimps [ImpNext_def]) 
                             [] [S4EnvUnchE,S4ClerkUnchE,S4RPCUnchE] 1,
             ALLGOALS (action_simp_tac (simpset() addsimps [square_def,RNext_def])
                                       [] [S4ReadE,S4WriteE,S4ReturnE]),
             auto_tac (MI_css addEs2 [S4HistE])
            ]);

qed_goal "Step1_2_5" MemoryImplementation.thy
   "[HNext rmhist p]_<c p,r p,m p, rmhist@p> .& ImpNext p  \
\             .& .~ unchanged <e p, c p, r p, m p, rmhist@p>  .& $(S5 rmhist p) \
\   .-> ((S6 rmhist p)$ .& RPCReply crCh rmCh rst p .& unchanged <e p, c p, m p>) \
\        .| ((S6 rmhist p)$ .& RPCFail crCh rmCh rst p .& unchanged <e p, c p, m p>)"
   (fn _ => [action_simp_tac (simpset() addsimps [ImpNext_def]) 
                             [] [S5EnvUnchE,S5ClerkUnchE,S5MemUnchE,S5HistE] 1,
	     action_simp_tac (simpset() addsimps [square_def]) [] [S5RPCE] 1,
	     auto_tac (MI_fast_css addSEs2 [S5ReplyE,S5FailE])
	    ]);

qed_goal "Step1_2_6" MemoryImplementation.thy
   "[HNext rmhist p]_<c p,r p,m p, rmhist@p> .& ImpNext p  \
\             .& .~ unchanged <e p, c p, r p, m p, rmhist@p>  .& $(S6 rmhist p) \
\   .-> ((S1 rmhist p)$ .& (MClkReply memCh crCh cst p) .& unchanged <e p, r p, m p>)\
\        .| ((S3 rmhist p)$ .& (MClkRetry memCh crCh cst p) .& unchanged <e p,r p,m p,rmhist@p>)"
   (fn _ => [action_simp_tac (simpset() addsimps [ImpNext_def]) 
                             [] [S6EnvUnchE,S6RPCUnchE,S6MemUnchE] 1,
             ALLGOALS (action_simp_tac (simpset() addsimps [square_def]) 
                                       [] [S6ClerkE,S6RetryE,S6ReplyE]),
             auto_tac (MI_css addEs2 [S6HistE])
            ]);


(* --------------------------------------------------------------------------
   Step 1.3: S1 implies the barred initial condition.
*)

section "Initialization (Step 1.3)";

val resbar_unl = rewrite_rule [slice_def] (action_unlift resbar_def);

qed_goal "Step1_3" MemoryImplementation.thy 
   "$(S1 rmhist p) .-> $(PInit (resbar rmhist) p)"
   (fn _ => [action_simp_tac (simpset() addsimps [resbar_unl,PInit_def,S_def,S1_def])
                             [] [] 1
            ]);

(* ----------------------------------------------------------------------
   Step 1.4: Implementation's next-state relation simulates specification's
             next-state relation (with appropriate substitutions)
*)

section "Step simulation (Step 1.4)";

qed_goal "Step1_4_1" MemoryImplementation.thy
   "ENext p .& $(S1 rmhist p) .& (S2 rmhist p)$ .& unchanged <c p, r p, m p> \
\   .-> unchanged <rtrner memCh @ p, resbar rmhist @ p>"
  (fn _ => [ auto_tac (MI_fast_css addsimps2 [c_def,r_def,m_def,resbar_unl]) ]);

qed_goal "Step1_4_2" MemoryImplementation.thy
   "MClkFwd memCh crCh cst p .& $(S2 rmhist p) .& (S3 rmhist p)$  \
\                            .& unchanged <e p, r p, m p, rmhist@p> \
\   .-> unchanged <rtrner memCh @ p, resbar rmhist @ p>"
  (fn _ => [auto_tac (MI_fast_css 
                      addsimps2 [MClkFwd_def, e_def, r_def, m_def, resbar_unl,
                                 S_def, S2_def, S3_def])
           ]);

qed_goal "Step1_4_3a" MemoryImplementation.thy
   "RPCFwd crCh rmCh rst p .& $(S3 rmhist p) .& (S4 rmhist p)$    \
\                          .& unchanged <e p, c p, m p, rmhist@p> \
\   .-> unchanged <rtrner memCh @ p, resbar rmhist @ p>"
  (fn _ => [auto_tac (MI_fast_css addsimps2 [e_def,c_def,m_def,resbar_unl]),
	      (* NB: Adding S3_exclE,S4_exclE as safe elims above would loop,
                     adding them as unsafe elims doesn't help, 
                     because auto_tac doesn't find the proof! *)
            REPEAT (eresolve_tac [S3_exclE,S4_exclE] 1),
            action_simp_tac (simpset() addsimps [S_def, S3_def]) [] [] 1
           ]);

qed_goal "Step1_4_3b" MemoryImplementation.thy
   "RPCFail crCh rmCh rst p .& $(S3 rmhist p) .& (S6 rmhist p)$ .& unchanged <e p, c p, m p>\
\   .-> MemFail memCh (resbar rmhist) p"
  (fn _ => [auto_tac (MI_css addsimps2 [RPCFail_def,MemFail_def,e_def,c_def,m_def,
		                        resbar_unl]),
	        (* It's faster not to expand S3 at once *)
            action_simp_tac (simpset() addsimps [S3_def,S_def]) [] [] 1,
            etac S6_exclE 1,
            auto_tac (MI_fast_css addsimps2 [Return_def])
           ]);


qed_goal "Step1_4_4a1" MemoryImplementation.thy
   "$(S4 rmhist p) .& (S4 rmhist p)$ .& ReadInner rmCh mem ires p l \
\   .& unchanged <e p, c p, r p, rmhist@p> .& $(MemInv mem l) \
\   .-> ReadInner memCh mem (resbar rmhist) p l"
  (fn _ => [action_simp_tac 
               (simpset() addsimps [ReadInner_def,GoodRead_def,BadRead_def,e_def,c_def,m_def]) 
               [] [] 1,
            ALLGOALS (REPEAT o (etac S4_exclE)),
            auto_tac (MI_css addsimps2 [resbar_unl]),
	    ALLGOALS (action_simp_tac 
                        (simpset() addsimps [RPCRelayArg_def,MClkRelayArg_def,
		                            S_def,S4_def,RdRequest_def,MemInv_def])
		      [] [impE,MemValNotAResultE])
           ]);

qed_goal "Step1_4_4a" MemoryImplementation.thy
   "Read rmCh mem ires p .& $(S4 rmhist p) .& (S4 rmhist p)$ \
\   .& unchanged <e p, c p, r p, rmhist@p> .& (RALL l. $(MemInv mem l)) \
\   .-> Read memCh mem (resbar rmhist) p"
  (fn _ => [ auto_tac (MI_css addsimps2 [Read_def] addSIs2 [action_mp Step1_4_4a1]) ]);

qed_goal "Step1_4_4b1" MemoryImplementation.thy
   "$(S4 rmhist p) .& (S4 rmhist p)$ .& WriteInner rmCh mem ires p l v   \
\                                    .& unchanged <e p, c p, r p, rmhist@p> \
\   .-> WriteInner memCh mem (resbar rmhist) p l v"
  (fn _ => [action_simp_tac 
               (simpset() addsimps [WriteInner_def, GoodWrite_def, BadWrite_def,
			           e_def, c_def, m_def])
               [] [] 1,
            ALLGOALS (REPEAT o (etac S4_exclE)),
	    auto_tac (MI_css addsimps2 [resbar_unl]),
               (* it's faster not to merge the two simplifications *)
	    ALLGOALS (action_simp_tac
                        (simpset() addsimps [RPCRelayArg_def,MClkRelayArg_def,
		                            S_def,S4_def,WrRequest_def])
		      [] [])
           ]);

qed_goal "Step1_4_4b" MemoryImplementation.thy
   "Write rmCh mem ires p l .& $(S4 rmhist p) .& (S4 rmhist p)$   \
\                           .& unchanged <e p, c p, r p, rmhist@p> \
\   .-> Write memCh mem (resbar rmhist) p l"
  (fn _ => [ auto_tac (MI_css addsimps2 [Write_def] addSIs2 [action_mp Step1_4_4b1]) ]);

qed_goal "Step1_4_4c" MemoryImplementation.thy
   "MemReturn rmCh ires p .& $(S4 rmhist p) .& (S5 rmhist p)$ .& unchanged <e p, c p, r p> \
\   .-> unchanged <rtrner memCh @ p, resbar rmhist @ p>"
  (fn _ => [action_simp_tac
	       (simpset() addsimps [e_def,c_def,r_def,resbar_unl]) [] [] 1,
	    REPEAT (eresolve_tac [S4_exclE,S5_exclE] 1),
	    auto_tac (MI_fast_css addsimps2 [MemReturn_def,Return_def])
           ]);

qed_goal "Step1_4_5a" MemoryImplementation.thy
   "RPCReply crCh rmCh rst p .& $(S5 rmhist p) .& (S6 rmhist p)$ .& unchanged <e p, c p, m p> \
\   .-> unchanged <rtrner memCh @ p, resbar rmhist @ p>"
  (fn _ => [auto_tac (MI_css addsimps2 [e_def,c_def,m_def, resbar_unl]),
            REPEAT (eresolve_tac [S5_exclE,S6_exclE] 1),
	    auto_tac (MI_css addsimps2 [RPCReply_def,Return_def,S5_def,S_def]
		             addSEs2 [MVOKBAnotRFE])
           ]);

qed_goal "Step1_4_5b" MemoryImplementation.thy
   "RPCFail crCh rmCh rst p .& $(S5 rmhist p) .& (S6 rmhist p)$ .& unchanged <e p, c p, m p>\
\   .-> MemFail memCh (resbar rmhist) p"
  (fn _ => [action_simp_tac
	       (simpset() addsimps [e_def, c_def, m_def, RPCFail_def, Return_def,
				   MemFail_def, resbar_unl])
	       [] [] 1,
	    action_simp_tac (simpset() addsimps [S5_def,S_def]) [] [] 1,
            etac S6_exclE 1,
	    auto_tac MI_css
           ]);

qed_goal "Step1_4_6a" MemoryImplementation.thy
   "MClkReply memCh crCh cst p .& $(S6 rmhist p) .& (S1 rmhist p)$ .& unchanged <e p, r p, m p> \
\   .-> MemReturn memCh (resbar rmhist) p"
  (fn _ => [action_simp_tac
	      (simpset() addsimps [e_def, r_def, m_def, MClkReply_def, MemReturn_def,
				  Return_def, resbar_unl]) 
              [] [] 1,
            ALLGOALS (etac S6_exclE),
	    ALLGOALS Asm_full_simp_tac,  (* simplify if-then-else *)
	    ALLGOALS (action_simp_tac
    	              (simpset() addsimps [MClkReplyVal_def,S6_def,S_def])
		      [] []),
            rtac ifI 1,
            ALLGOALS (action_simp_tac (simpset()) [] [MVOKBARFnotNRE])
           ]);

qed_goal "Step1_4_6b" MemoryImplementation.thy
   "MClkRetry memCh crCh cst p .& $(S6 rmhist p) .& (S3 rmhist p)$   \
\                              .& unchanged <e p, r p, m p, rmhist@p> \
\   .-> MemFail memCh (resbar rmhist) p"
  (fn _ => [action_simp_tac
	       (simpset() addsimps [e_def, r_def, m_def, MClkRetry_def, MemFail_def, resbar_unl])
	       [] [] 1,
	    SELECT_GOAL (auto_tac (MI_css addsimps2 [S6_def,S_def])) 1,
            etac S3_exclE 1,
            Asm_full_simp_tac 1,
	    action_simp_tac (simpset() addsimps [S6_def,S3_def,S_def]) [] [] 1
           ]);

qed_goal "S_lemma" MemoryImplementation.thy
   "unchanged <e p, c p, r p, m p, rmhist@p> \
\   .-> unchanged (S rmhist ec cc rc cs rs hs1 hs2 p)"
   (fn _ => [auto_tac (MI_css addsimps2 [e_def,c_def,r_def,m_def,caller_def,rtrner_def,
					 S_def,Calling_def])
            ]);

qed_goal "Step1_4_7H" MemoryImplementation.thy
   "unchanged <e p, c p, r p, m p, rmhist@p> \
\   .-> unchanged <rtrner memCh @ p, S1 rmhist p, S2 rmhist p, S3 rmhist p, \
\                                    S4 rmhist p, S5 rmhist p, S6 rmhist p>"
   (fn _ => [Action_simp_tac 1,
	     SELECT_GOAL (auto_tac (MI_fast_css addsimps2 [c_def])) 1,
             ALLGOALS (simp_tac (simpset()
				 addsimps [S1_def,S2_def,S3_def,S4_def,S5_def,S6_def])),
	     auto_tac (MI_css addSIs2 [action_mp S_lemma])
            ]);

(* unlifted version as elimination rule *)
bind_thm("Step1_4_7h",
	 (rewrite_rule action_rews (Step1_4_7H RS actionD)) RS impdupE);

qed_goal "Step1_4_7" MemoryImplementation.thy
   "unchanged <e p, c p, r p, m p, rmhist@p> .-> unchanged <rtrner memCh @ p, resbar rmhist @ p>"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac action_rews,
            rtac impI 1,
            etac Step1_4_7h 1,
	    auto_tac (MI_css addsimps2 [e_def,c_def,r_def,m_def,rtrner_def,resbar_unl])
           ]);


(* Frequently needed abbreviation: distinguish between idling and non-idling
   steps of the implementation, and try to solve the idling case by simplification
*)
fun split_idle_tac simps i = 
    EVERY [rtac actionI i,
	   case_tac "(unchanged <e p, c p, r p, m p, rmhist@p>) [[s,t]]" i,
	   rewrite_goals_tac action_rews,
	   etac Step1_4_7h i,
	   asm_full_simp_tac (simpset() addsimps simps) i
	  ];

(* ----------------------------------------------------------------------
   Combine steps 1.2 and 1.4 to prove that the implementation satisfies
   the specification's next-state relation.
*)

(* Steps that leave all variables unchanged are safe, so I may assume
   that some variable changes in the proof that a step is safe. *)
qed_goal "unchanged_safe" MemoryImplementation.thy
   "(.~ (unchanged <e p, c p, r p, m p, rmhist@p>) \
\      .-> [UNext memCh mem (resbar rmhist) p]_<rtrner memCh @ p, resbar rmhist @ p>) \
\   .-> [UNext memCh mem (resbar rmhist) p]_<rtrner memCh @ p, resbar rmhist @ p>"
   (fn _ => [rtac actionI 1,
             case_tac "(unchanged <e p, c p, r p, m p, rmhist@p>) [[s,t]]" 1,
	     rewrite_goals_tac action_rews,
	     auto_tac (MI_css addsimps2 [square_def] addSEs2 [action_impE Step1_4_7])
            ]);
(* turn into (unsafe, looping!) introduction rule *)
bind_thm("unchanged_safeI", impI RS (action_mp unchanged_safe));

qed_goal "S1safe" MemoryImplementation.thy
   "$(S1 rmhist p) .& ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>   \
\  .-> [UNext memCh mem (resbar rmhist) p]_<rtrner memCh @ p, resbar rmhist @ p>"
   (fn _ => [Action_simp_tac 1, 
             rtac unchanged_safeI 1,
             rtac idle_squareI 1,
	     auto_tac (MI_css addSEs2 (map action_conjimpE [Step1_2_1,Step1_4_1]))
	    ]);

qed_goal "S2safe" MemoryImplementation.thy
   "$(S2 rmhist p) .& ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>   \
\  .-> [UNext memCh mem (resbar rmhist) p]_<rtrner memCh @ p, resbar rmhist @ p>"
   (fn _ => [Action_simp_tac 1, 
             rtac unchanged_safeI 1,
             rtac idle_squareI 1,
	     auto_tac (MI_fast_css addSEs2 (map action_conjimpE [Step1_2_2,Step1_4_2]))
	    ]);

qed_goal "S3safe" MemoryImplementation.thy
   "$(S3 rmhist p) .& ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>   \
\  .-> [UNext memCh mem (resbar rmhist) p]_<rtrner memCh @ p, resbar rmhist @ p>"
   (fn _ => [Action_simp_tac 1,
	     rtac unchanged_safeI 1,
             auto_tac (MI_css addSEs2 [action_conjimpE Step1_2_3]),
	     auto_tac (MI_fast_css addsimps2 [square_def,UNext_def]
		              addSEs2 (map action_conjimpE [Step1_4_3a,Step1_4_3b]))
	    ]);

qed_goal "S4safe" MemoryImplementation.thy
   "$(S4 rmhist p) .& ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>  \
\                  .& (RALL l. $(MemInv mem l)) \
\  .-> [UNext memCh mem (resbar rmhist) p]_<rtrner memCh @ p, resbar rmhist @ p>"
   (fn _ => [Action_simp_tac 1,
	     rtac unchanged_safeI 1,
             auto_tac (MI_css addSEs2 [action_conjimpE Step1_2_4]),
             ALLGOALS (action_simp_tac (simpset() addsimps [square_def,UNext_def,RNext_def]) [] []),
	     auto_tac (MI_fast_css addSEs2 (map action_conjimpE 
                                                [Step1_4_4a,Step1_4_4b,Step1_4_4c]))
	    ]);

qed_goal "S5safe" MemoryImplementation.thy
   "$(S5 rmhist p) .& ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>  \
\  .-> [UNext memCh mem (resbar rmhist) p]_<rtrner memCh @ p, resbar rmhist @ p>"
   (fn _ => [Action_simp_tac 1,
	     rtac unchanged_safeI 1,
             auto_tac (MI_css addSEs2 [action_conjimpE Step1_2_5]),
	     auto_tac (MI_fast_css addsimps2 [square_def,UNext_def]
		              addSEs2 (map action_conjimpE [Step1_4_5a,Step1_4_5b]))
	    ]);

qed_goal "S6safe" MemoryImplementation.thy
   "$(S6 rmhist p) .& ImpNext p .& [HNext rmhist p]_<c p,r p,m p, rmhist@p>   \
\  .-> [UNext memCh mem (resbar rmhist) p]_<rtrner memCh @ p, resbar rmhist @ p>"
   (fn _ => [Action_simp_tac 1,
	     rtac unchanged_safeI 1,
             auto_tac (MI_css addSEs2 [action_conjimpE Step1_2_6]),
	     auto_tac (MI_fast_css addsimps2 [square_def,UNext_def,RNext_def]
		              addSEs2 (map action_conjimpE [Step1_4_6a,Step1_4_6b]))
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
   "IPImp p .-> (RALL l. []$(MemInv mem l))"
   (fn _ => [auto_tac (MI_css addsimps2 [IPImp_def]
			      addSIs2 [temp_mp MemoryInvariantAll])
	    ]);
bind_thm("MemInvI", (rewrite_rule intensional_rews (Step1_5_1a RS tempD)) RS impdupE);

qed_goal "Step1_5_1b" MemoryImplementation.thy
   "   Init($(ImpInit p) .& $(HInit rmhist p)) .& [](ImpNext p) \
\         .& [][HNext rmhist p]_<c p, r p, m p, rmhist@p> .& [](RALL l. $(MemInv mem l)) \
\   .-> []($(ImpInv rmhist p))"
   (fn _ => [inv_tac MI_css 1,
	     auto_tac (MI_css
		       addsimps2 [Init_def, ImpInv_def]
		       addSEs2 [action_impE Step1_1]
		       addEs2 (map action_conjimpE
			           [S1_successors,S2_successors,S3_successors,
			            S4_successors,S5_successors,S6_successors]))
            ]);
bind_thm("ImpInvI", (rewrite_rule intensional_rews (Step1_5_1b RS tempD)) RS impdupE);

(*** Initialization ***)
qed_goal "Step1_5_2a" MemoryImplementation.thy
   "Init($(ImpInit p) .& $(HInit rmhist p)) .-> Init($PInit (resbar rmhist) p)"
   (fn _ => [auto_tac (MI_css addsimps2 [Init_def]
                              addSIs2 (map action_mp [Step1_1,Step1_3]))
            ]);

(*** step simulation ***)
qed_goal "Step1_5_2b" MemoryImplementation.thy
   "[](ImpNext p .& [HNext rmhist p]_<c p, r p, m p, rmhist@p>   \
\                .& $(ImpInv rmhist p) .& (RALL l. $(MemInv mem l)))   \
\   .-> [][UNext memCh mem (resbar rmhist) p]_<rtrner memCh @ p, resbar rmhist @ p>"
   (fn _ => [auto_tac (MI_fast_css 
                          addsimps2 [ImpInv_def] 
                          addSEs2 (STL4E::(map action_conjimpE
                                         [S1safe,S2safe,S3safe,S4safe,S5safe,S6safe])))
            ]);


(*** Liveness ***)
qed_goal "GoodImpl" MemoryImplementation.thy
   "IPImp p .& HistP rmhist p  \
\   .->   Init($(ImpInit p) .& $(HInit rmhist p))   \
\      .& [](ImpNext p .& [HNext rmhist p]_<c p, r p, m p, rmhist@p>) \
\      .& [](RALL l. $(MemInv mem l)) .& []($(ImpInv rmhist p)) \
\      .& ImpLive p"
   (fn _ => [(* need some subgoals to prove [](ImpInv p), avoid duplication *)
	     rtac tempI 1, rewrite_goals_tac intensional_rews, rtac impI 1,
             subgoal_tac
	       "sigma |= Init($(ImpInit p) .& $(HInit rmhist p)) \
\                        .& [](ImpNext p) \
\                        .& [][HNext rmhist p]_<c p, r p, m p, rmhist@p> \
\                        .& [](RALL l. $(MemInv mem l))" 1,
	     auto_tac (MI_css addsimps2 [split_box_conj]
                              addSEs2 [temp_conjimpE Step1_5_1b]),
	     SELECT_GOAL
	        (auto_tac (MI_css addsimps2 [IPImp_def,MClkIPSpec_def,RPCIPSpec_def,RPSpec_def,
					     ImpLive_def,c_def,r_def,m_def])) 1,
	     SELECT_GOAL
	        (auto_tac (MI_css addsimps2 [IPImp_def,MClkIPSpec_def,RPCIPSpec_def,RPSpec_def,
					     HistP_def,Init_def,action_unlift ImpInit_def])) 1,
	     SELECT_GOAL
	        (auto_tac (MI_css addsimps2 [IPImp_def,MClkIPSpec_def,RPCIPSpec_def,RPSpec_def,
					     ImpNext_def,c_def,r_def,m_def,
					     split_box_conj])) 1,
	     SELECT_GOAL (auto_tac (MI_css addsimps2 [HistP_def])) 1,
             etac ((temp_mp Step1_5_1a) RS ((temp_unlift allT) RS iffD1)) 1
	    ]);

(* The implementation is infinitely often in state S1 *)
qed_goal "Step1_5_3a" MemoryImplementation.thy
   "[](ImpNext p .& [HNext rmhist p]_<c p, r p, m p, rmhist@p>) \
\   .& [](RALL l. $(MemInv mem l))  \
\   .& []($(ImpInv rmhist p)) .& ImpLive p  \
\   .-> []<>($(S1 rmhist p))"
   (fn _ => [auto_tac (MI_css addsimps2 [ImpLive_def]),
             rtac S1Infinite 1,
	     SELECT_GOAL
	       (auto_tac (MI_css
			  addsimps2 [split_box_conj]
			  addSIs2 (NotS1LeadstoS6::
				   map temp_mp [S2_live,S3_live,S4a_live,S4b_live,S5_live]))) 1,
             auto_tac (MI_css addsimps2 [split_box_conj] addSIs2 [temp_mp S6_live])
            ]);

(* Hence, it satisfies the fairness requirements of the specification *)
qed_goal "Step1_5_3b" MemoryImplementation.thy
   "[](ImpNext p .& [HNext rmhist p]_<c p, r p, m p, rmhist@p>) \
\   .& [](RALL l. $(MemInv mem l)) .& []($(ImpInv rmhist p)) .& ImpLive p  \
\   .-> WF(RNext memCh mem (resbar rmhist) p)_<rtrner memCh @ p, resbar rmhist @ p>"
   (fn _ => [ auto_tac (MI_fast_css addSIs2 [RNext_fair,temp_mp Step1_5_3a]) ]);

qed_goal "Step1_5_3c" MemoryImplementation.thy
   "[](ImpNext p .& [HNext rmhist p]_<c p, r p, m p, rmhist@p>) \
\   .& [](RALL l. $(MemInv mem l)) .& []($(ImpInv rmhist p)) .& ImpLive p  \
\   .-> WF(MemReturn memCh (resbar rmhist) p)_<rtrner memCh @ p, resbar rmhist @ p>"
   (fn _ => [ auto_tac (MI_fast_css addSIs2 [Return_fair,temp_mp Step1_5_3a]) ]);


(* QED step of step 1 *)
qed_goal "Step1" MemoryImplementation.thy
   "IPImp p .& HistP rmhist p .-> UPSpec memCh mem (resbar rmhist) p"
   (fn _ => [auto_tac
               (MI_css addsimps2 [UPSpec_def,split_box_conj]
		       addSEs2 [temp_impE GoodImpl]
                       addSIs2 (map temp_mp [Step1_5_2a,Step1_5_2b,
                                             Step1_5_3b,Step1_5_3c]))
            ]);


(* ------------------------------ Step 2 ------------------------------ *)
section "Step 2";

qed_goal "Step2_2a" MemoryImplementation.thy
   "ImpNext p .& [HNext rmhist p]_<c p, r p, m p, rmhist@p> \
\   .& $(S4 rmhist p) .& Write rmCh mem ires p l \
\   .-> (S4 rmhist p)$ .& unchanged <e p, c p, r p, rmhist@p>"
   (fn _ => [split_idle_tac [] 1,
             action_simp_tac (simpset() addsimps [ImpNext_def])
                             [] [S4EnvUnchE,S4ClerkUnchE,S4RPCUnchE] 1,
             TRYALL (action_simp_tac (simpset() addsimps [square_def]) [] [S4WriteE]),
             Auto_tac()
            ]);

qed_goal "Step2_2" MemoryImplementation.thy
   "      (RALL p. ImpNext p) \
\      .& (RALL p. [HNext rmhist p]_<c p, r p, m p, rmhist@p>) \
\      .& (RALL p. $(ImpInv rmhist p)) \
\      .& [REX q. Write rmCh mem ires q l]_(mem@l) \
\   .-> [REX q. Write memCh mem (resbar rmhist) q l]_(mem@l)"
   (fn _ => [auto_tac (MI_css addsimps2 [square_def]
                                   addSIs2 [action_mp Step1_4_4b]
		                   addSEs2 [WriteS4E, action_conjimpE Step2_2a])
            ]);

qed_goal "Step2_lemma" MemoryImplementation.thy
   "    [](   (RALL p. ImpNext p) \
\          .& (RALL p. [HNext rmhist p]_<c p, r p, m p, rmhist@p>) \
\          .& (RALL p. $(ImpInv rmhist p)) \
\          .& [REX q. Write rmCh mem ires q l]_(mem@l)) \
\   .-> [][REX q. Write memCh mem (resbar rmhist) q l]_(mem@l)"
   (fn _ => [ auto_tac (MI_css addSEs2 [STL4E, action_conjimpE Step2_2]) ]);

qed_goal "Step2" MemoryImplementation.thy
   "#(MemLoc l) .& (RALL p. IPImp p .& HistP rmhist p)  \
\   .-> MSpec memCh mem (resbar rmhist) l"
   (fn _ => [auto_tac (MI_css addsimps2 [MSpec_def]),
	         (* prove initial condition, don't expand IPImp in other subgoal *)
	     SELECT_GOAL (auto_tac (MI_css addsimps2 [IPImp_def,MSpec_def])) 1,
	     auto_tac (MI_css addSIs2 [temp_mp Step2_lemma]
		              addsimps2 [split_box_conj,all_box]),
	     SELECT_GOAL (auto_tac (MI_css addsimps2 [IPImp_def,MSpec_def])) 4,
             auto_tac (MI_css addsimps2 [split_box_conj]
			      addSEs2 [temp_impE GoodImpl])
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
   "Implementation .& Hist rmhist .-> IUSpec memCh mem (resbar rmhist)"
   (fn _ => [auto_tac (MI_css addsimps2 [IUSpec_def,Impl_def,IPImp_def,MClkISpec_def,
					 RPCISpec_def,IRSpec_def,Hist_def]
		              addSIs2 (map temp_mp [Step1,Step2]))
	    ]);

(* The main theorem: introduce hiding and eliminate history variable. *)
qed_goal "Implementation" MemoryImplementation.thy
   "Implementation .-> USpec memCh"
   (fn _ => [Auto_tac(),
             forward_tac [temp_mp History] 1,
             auto_tac (MI_css addsimps2 [USpec_def] 
                              addIs2 (map temp_mp [eexI, Impl_IUSpec])
                              addSEs2 [eexE])
            ]);
