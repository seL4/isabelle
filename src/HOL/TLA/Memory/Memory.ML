(* 
    File:        Memory.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: Memory specification (ML file)
*)

val RM_action_defs = 
   (map (fn t => t RS inteq_reflection)
        [MInit_def, PInit_def, RdRequest_def, WrRequest_def, MemInv_def])
   @ [GoodRead_def, BadRead_def, ReadInner_def, Read_def,
      GoodWrite_def, BadWrite_def, WriteInner_def, Write_def,
      MemReturn_def, RNext_def];

val UM_action_defs = RM_action_defs @ [MemFail_def, UNext_def];

val RM_temp_defs = [RPSpec_def, MSpec_def, IRSpec_def];
val UM_temp_defs = [UPSpec_def, MSpec_def, IUSpec_def];

(* Make sure the simpset accepts non-boolean simplifications *)
simpset_ref() := simpset() setmksimps ((mksimps mksimps_pairs) o maybe_unlift);

(* -------------------- Proofs ---------------------------------------------- *)

(* The reliable memory is an implementation of the unreliable one *)
qed_goal "ReliableImplementsUnReliable" Memory.thy 
   "IRSpec ch mm rs .-> IUSpec ch mm rs"
   (fn _ => [auto_tac (temp_css addsimps2 ([square_def,UNext_def] @ 
			RM_temp_defs @ UM_temp_defs) addSEs2 [STL4E])]);

(* The memory spec implies the memory invariant *)
qed_goal "MemoryInvariant" Memory.thy 
   "(MSpec ch mm rs l) .-> []($(MemInv mm l))"
   (fn _ => [ auto_inv_tac (simpset() addsimps RM_temp_defs @ 
					MP_simps @ RM_action_defs) 1 ]);

(* The invariant is trivial for non-locations *)
qed_goal "NonMemLocInvariant" Memory.thy
   ".~ #(MemLoc l) .-> []($MemInv mm l)"
   (K [ auto_tac (temp_css addsimps2 [MemInv_def] addSIs2 [necT RS tempD]) ]);

qed_goal "MemoryInvariantAll" Memory.thy
   "((RALL l. #(MemLoc l) .-> MSpec ch mm rs l)) .-> (RALL l. []($MemInv mm l))"
    (K [step_tac temp_cs 1,
	case_tac "MemLoc l" 1,
	auto_tac (temp_css addSEs2 (map temp_mp [MemoryInvariant,
			NonMemLocInvariant]))]);

(* The memory engages in an action for process p only if there is an 
   unanswered call from p.
   We need this only for the reliable memory.
*)

qed_goal "Memoryidle" Memory.thy
   ".~ $(Calling ch p) .-> .~ RNext ch mm rs p"
   (K [ auto_tac (action_css addsimps2 (RM_action_defs @ [Return_def])) ]);

bind_thm("MemoryidleI", action_mp Memoryidle);
bind_thm("MemoryidleE", action_impE Memoryidle);


(* Enabledness conditions *)

qed_goal "MemReturn_change" Memory.thy
   "MemReturn ch rs p .-> <MemReturn ch rs p>_<rtrner ch @ p, rs@p>"
   (fn _ => [ auto_tac (action_css addsimps2 [MemReturn_def,angle_def]) ]);

qed_goal "MemReturn_enabled" Memory.thy
   "!!p. base_var <rtrner ch @ p, rs@p> ==> \
\        $(Calling ch p) .& ($(rs@p) .~= #NotAResult) \
\        .-> $(Enabled (<MemReturn ch rs p>_<rtrner ch @ p, rs@p>))"
  (K [action_simp_tac (simpset()) [MemReturn_change RSN (2,enabled_mono)] [] 1,
      action_simp_tac (simpset() addsimps [MemReturn_def,Return_def,rtrner_def])
                             [] [base_enabled,Pair_inject] 1
	    ]);

qed_goal "ReadInner_enabled" Memory.thy
   "!!p. base_var <rtrner ch @ p, rs@p> ==> \
\        $(Calling ch p) .& (arg[$(ch@p)] .= #(Inl (read,l))) \
\        .-> $(Enabled (ReadInner ch mm rs p l))"
   (fn _ => [Action_simp_tac 1,
(* unlift before applying case_tac: case_split_thm expects boolean conclusion *)
	     case_tac "MemLoc l" 1,
             ALLGOALS
	        (action_simp_tac 
                    (simpset() addsimps [ReadInner_def,GoodRead_def,BadRead_def,
					RdRequest_def])
                    [] [base_enabled,Pair_inject])
            ]);

qed_goal "WriteInner_enabled" Memory.thy
   "!!p. base_var <rtrner ch @ p, mm@l, rs@p> ==> \
\        $(Calling ch p) .& (arg[$(ch@p)] .= #(Inr (write,l,v))) \
\        .-> $(Enabled (WriteInner ch mm rs p l v))"
   (fn _ => [Action_simp_tac 1,
	     case_tac "MemLoc l & MemVal v" 1,
             ALLGOALS (action_simp_tac 
                 (simpset() addsimps [WriteInner_def,GoodWrite_def,BadWrite_def,
					WrRequest_def] delsimps [disj_not1])
                    [] [base_enabled,Pair_inject])
            ]);

qed_goal "ReadResult" Memory.thy
   "(Read ch mm rs p) .& (RALL l. $(MemInv mm l)) .-> (rs@p)$ .~= #NotAResult"
   (fn _ => [action_simp_tac 
               (simpset() addsimps (MP_simps 
				   @ [Read_def,ReadInner_def,GoodRead_def,
				      BadRead_def,MemInv_def]))
	       [] [] 1,
	     auto_tac (action_css addsimps2 MP_simps) ]);

qed_goal "WriteResult" Memory.thy
   "(Write ch mm rs p l) .-> (rs@p)$ .~= #NotAResult"
   (fn _ => [auto_tac (claset(),
		       simpset() addsimps (MP_simps @
		   [Write_def,WriteInner_def,GoodWrite_def,BadWrite_def]))
	    ]);

qed_goal "ReturnNotReadWrite" Memory.thy
   "(RALL l. $MemInv mm l) .& (MemReturn ch rs p) \
\   .-> .~(Read ch mm rs p) .& (RALL l. .~(Write ch mm rs p l))"
   (fn _ => [auto_tac
	       (action_css addsimps2 [MemReturn_def]
	          addSEs2 [action_impE WriteResult,action_conjimpE ReadResult])
	    ]);

qed_goal "RWRNext_enabled" Memory.thy
   "($(rs@p) .= #NotAResult) .& (RALL l. $(MemInv mm l))  \
\      .& $(Enabled (Read ch mm rs p .| (REX l. Write ch mm rs p l))) \
\   .-> $(Enabled (<RNext ch mm rs p>_<rtrner ch @ p, rs@p>))"
   (fn _ => [auto_tac
	       (action_css addsimps2 [RNext_def,angle_def]
		     addSEs2 [enabled_mono2]
		     addEs2[action_conjimpE ReadResult,action_impE WriteResult])
	    ]);


(* Combine previous lemmas: the memory can make a visible step if there is an
   outstanding call for which no result has been produced.
*)
qed_goal "RNext_enabled" Memory.thy
"!!p. (ALL l. base_var <rtrner ch @ p, mm@l, rs@p>) ==> \
\     ($(rs@p) .= #NotAResult) .& $(Calling ch p) .& (RALL l. $(MemInv mm l))  \
\        .-> $(Enabled (<RNext ch mm rs p>_<rtrner ch @ p, rs@p>))" (K [
	     auto_tac (action_css addsimps2 [enabled_disj]
		                  addSIs2 [action_mp RWRNext_enabled]),
	     res_inst_tac [("s","arg(ch s p)")] sumE 1,
	      action_simp_tac (simpset()addsimps[Read_def,enabled_ex,base_pair])
	                      [action_mp ReadInner_enabled,exI] [] 1,
	      split_all_tac 1, rename_tac "a b" 1, Rd.induct_tac "a" 1,
	     (* introduce a trivial subgoal to solve flex-flex constraint?! *)
	      subgoal_tac "b = snd(a,b)" 1,
	       TRYALL Simp_tac,  (* solves "read" case *)
	     etac swap 1,
	     action_simp_tac (simpset()addsimps[Write_def,enabled_ex,base_pair])
	                     [action_mp WriteInner_enabled,exI] [] 1,
	     split_all_tac 1, rename_tac "a aa b" 1, Wr.induct_tac "a" 1,
	     subgoal_tac "(aa = fst(snd(a,aa,b))) & (b = snd(snd(a,aa,b)))" 1,
	     ALLGOALS Simp_tac ]);
