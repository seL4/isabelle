(* 
    File:        Memory.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: Memory specification (theorems and proofs)
*)

val RM_action_defs = 
   [MInit_def, PInit_def, RdRequest_def, WrRequest_def, MemInv_def,
    GoodRead_def, BadRead_def, ReadInner_def, Read_def,
    GoodWrite_def, BadWrite_def, WriteInner_def, Write_def,
    MemReturn_def, RNext_def];

val UM_action_defs = RM_action_defs @ [MemFail_def, UNext_def];

val RM_temp_defs = [RPSpec_def, MSpec_def, IRSpec_def];
val UM_temp_defs = [UPSpec_def, MSpec_def, IUSpec_def];

val mem_css = (claset(), simpset());

(* -------------------- Proofs ---------------------------------------------- *)

(* The reliable memory is an implementation of the unreliable one *)
qed_goal "ReliableImplementsUnReliable" Memory.thy 
   "|- IRSpec ch mm rs --> IUSpec ch mm rs"
   (K [force_tac (temp_css addsimps2 ([UNext_def,UPSpec_def,IUSpec_def] @ RM_temp_defs)
			   addSEs2 [STL4E,squareE]) 1]);

(* The memory spec implies the memory invariant *)
qed_goal "MemoryInvariant" Memory.thy 
   "|- MSpec ch mm rs l --> [](MemInv mm l)"
   (fn _ => [ auto_inv_tac (simpset() addsimps RM_temp_defs @ RM_action_defs) 1 ]);

(* The invariant is trivial for non-locations *)
qed_goal "NonMemLocInvariant" Memory.thy
   "|- #l ~: #MemLoc --> [](MemInv mm l)"
   (K [ auto_tac (temp_css addsimps2 [MemInv_def] addSIs2 [necT]) ]);

qed_goal "MemoryInvariantAll" Memory.thy
   "|- (!l. #l : #MemLoc --> MSpec ch mm rs l) --> (!l. [](MemInv mm l))"
    (K [step_tac temp_cs 1,
	case_tac "l : MemLoc" 1,
	auto_tac (temp_css addSEs2 [MemoryInvariant,NonMemLocInvariant]) ]);

(* The memory engages in an action for process p only if there is an 
   unanswered call from p.
   We need this only for the reliable memory.
*)

qed_goal "Memoryidle" Memory.thy
   "|- ~$(Calling ch p) --> ~ RNext ch mm rs p"
   (K [ auto_tac (mem_css addsimps2 (Return_def::RM_action_defs)) ]);

(* Enabledness conditions *)

qed_goal "MemReturn_change" Memory.thy
   "|- MemReturn ch rs p --> <MemReturn ch rs p>_(rtrner ch ! p, rs!p)"
   (K [ force_tac (mem_css addsimps2 [MemReturn_def,angle_def]) 1]);

qed_goal "MemReturn_enabled" Memory.thy
   "!!p. basevars (rtrner ch ! p, rs!p) ==> \
\        |- Calling ch p & (rs!p ~= #NotAResult) \
\           --> Enabled (<MemReturn ch rs p>_(rtrner ch ! p, rs!p))"
  (K [action_simp_tac (simpset()) [MemReturn_change RSN (2,enabled_mono)] [] 1,
      action_simp_tac (simpset() addsimps [MemReturn_def,Return_def,rtrner_def])
                             [] [base_enabled,Pair_inject] 1
	    ]);

qed_goal "ReadInner_enabled" Memory.thy
 "!!p. basevars (rtrner ch ! p, rs!p) ==> \
\      |- Calling ch p & (arg<ch!p> = #(read l)) --> Enabled (ReadInner ch mm rs p l)"
   (fn _ => [case_tac "l : MemLoc" 1,
             ALLGOALS
	        (action_simp_tac 
                    (simpset() addsimps [ReadInner_def,GoodRead_def,BadRead_def,
					RdRequest_def])
                    [] [base_enabled,Pair_inject])
            ]);

qed_goal "WriteInner_enabled" Memory.thy
   "!!p. basevars (mm!l, rtrner ch ! p, rs!p) ==> \
\        |- Calling ch p & (arg<ch!p> = #(write l v)) \
\           --> Enabled (WriteInner ch mm rs p l v)"
   (fn _ => [case_tac "l:MemLoc & v:MemVal" 1,
             ALLGOALS (action_simp_tac 
                 (simpset() addsimps [WriteInner_def,GoodWrite_def,BadWrite_def,
					WrRequest_def] delsimps [disj_not1])
                    [] [base_enabled,Pair_inject])
            ]);

qed_goal "ReadResult" Memory.thy
   "|- Read ch mm rs p & (!l. $(MemInv mm l)) --> (rs!p)` ~= #NotAResult"
   (fn _ => [force_tac (mem_css addsimps2 
                            [Read_def,ReadInner_def,GoodRead_def,BadRead_def,MemInv_def]) 1]);

qed_goal "WriteResult" Memory.thy
   "|- Write ch mm rs p l --> (rs!p)` ~= #NotAResult"
   (fn _ => [auto_tac (mem_css addsimps2 ([Write_def,WriteInner_def,GoodWrite_def,BadWrite_def]))
	    ]);

qed_goal "ReturnNotReadWrite" Memory.thy
   "|- (!l. $MemInv mm l) & MemReturn ch rs p \
\      --> ~ Read ch mm rs p & (!l. ~ Write ch mm rs p l)"
   (fn _ => [auto_tac
	       (mem_css addsimps2 [MemReturn_def] addSDs2 [WriteResult, ReadResult])
	    ]);

qed_goal "RWRNext_enabled" Memory.thy
   "|- (rs!p = #NotAResult) & (!l. MemInv mm l)  \
\          & Enabled (Read ch mm rs p | (? l. Write ch mm rs p l)) \
\      --> Enabled (<RNext ch mm rs p>_(rtrner ch ! p, rs!p))"
   (K [force_tac (mem_css addsimps2 [RNext_def,angle_def]
	     addSEs2 [enabled_mono2]
	     addDs2 [ReadResult, WriteResult]) 1]);


(* Combine previous lemmas: the memory can make a visible step if there is an
   outstanding call for which no result has been produced.
*)
qed_goal "RNext_enabled" Memory.thy
"!!p. !l. basevars (mm!l, rtrner ch!p, rs!p) ==> \
\     |- (rs!p = #NotAResult) & Calling ch p & (!l. MemInv mm l)  \
\        --> Enabled (<RNext ch mm rs p>_(rtrner ch ! p, rs!p))" (K [
	     auto_tac (mem_css addsimps2 [enabled_disj]
		                  addSIs2 [RWRNext_enabled]),
             exhaust_tac "arg(ch w p)" 1,
 	      action_simp_tac (simpset()addsimps[Read_def,enabled_ex])
	                      [ReadInner_enabled,exI] [] 1,
              force_tac (mem_css addDs2 [base_pair]) 1,
	     etac swap 1,
	     action_simp_tac (simpset() addsimps [Write_def,enabled_ex])
	                     [WriteInner_enabled,exI] [] 1]);

