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
Goal "|- IRSpec ch mm rs --> IUSpec ch mm rs";
by (force_tac (temp_css addsimps2 ([UNext_def,UPSpec_def,IUSpec_def] @ RM_temp_defs)
			addSEs2 [STL4E,squareE]) 1);
qed "ReliableImplementsUnReliable";

(* The memory spec implies the memory invariant *)
Goal "|- MSpec ch mm rs l --> [](MemInv mm l)";
by (auto_inv_tac (simpset() addsimps RM_temp_defs @ RM_action_defs) 1);
qed "MemoryInvariant";

(* The invariant is trivial for non-locations *)
Goal "|- #l ~: #MemLoc --> [](MemInv mm l)";
by (auto_tac (temp_css addsimps2 [MemInv_def] addSIs2 [necT]));
qed "NonMemLocInvariant";

Goal "|- (ALL l. #l : #MemLoc --> MSpec ch mm rs l) --> (ALL l. [](MemInv mm l))";
by (step_tac temp_cs 1);
by (case_tac "l : MemLoc" 1);
by (auto_tac (temp_css addSEs2 [MemoryInvariant,NonMemLocInvariant]));
qed "MemoryInvariantAll";

(* The memory engages in an action for process p only if there is an 
   unanswered call from p.
   We need this only for the reliable memory.
*)

Goal "|- ~$(Calling ch p) --> ~ RNext ch mm rs p";
by (auto_tac (mem_css addsimps2 (Return_def::RM_action_defs)));
qed "Memoryidle";

(* Enabledness conditions *)

Goal "|- MemReturn ch rs p --> <MemReturn ch rs p>_(rtrner ch ! p, rs!p)";
by (force_tac (mem_css addsimps2 [MemReturn_def,angle_def]) 1);
qed "MemReturn_change";

Goal "!!p. basevars (rtrner ch ! p, rs!p) ==> \
\     |- Calling ch p & (rs!p ~= #NotAResult) \
\        --> Enabled (<MemReturn ch rs p>_(rtrner ch ! p, rs!p))";
by (action_simp_tac (simpset()) [MemReturn_change RSN (2,enabled_mono)] [] 1);
by (action_simp_tac (simpset() addsimps [MemReturn_def,Return_def,rtrner_def])
                    [exI] [base_enabled,Pair_inject] 1);
qed "MemReturn_enabled";

Goal "!!p. basevars (rtrner ch ! p, rs!p) ==> \
\     |- Calling ch p & (arg<ch!p> = #(read l)) --> Enabled (ReadInner ch mm rs p l)";
by (case_tac "l : MemLoc" 1);
by (ALLGOALS
     (force_tac (mem_css addsimps2 [ReadInner_def,GoodRead_def,
                                    BadRead_def,RdRequest_def]
                         addSIs2 [exI] addSEs2 [base_enabled])));
qed "ReadInner_enabled";

Goal "!!p. basevars (mm!l, rtrner ch ! p, rs!p) ==> \
\     |- Calling ch p & (arg<ch!p> = #(write l v)) \
\        --> Enabled (WriteInner ch mm rs p l v)";
by (case_tac "l:MemLoc & v:MemVal" 1);
by (ALLGOALS 
     (force_tac (mem_css addsimps2 [WriteInner_def,GoodWrite_def,
                                    BadWrite_def,WrRequest_def]
                         addSIs2 [exI] addSEs2 [base_enabled])));
qed "WriteInner_enabled";

Goal "|- Read ch mm rs p & (!l. $(MemInv mm l)) --> (rs!p)` ~= #NotAResult";
by (force_tac (mem_css addsimps2 
                       [Read_def,ReadInner_def,GoodRead_def,BadRead_def,MemInv_def]) 1);
qed "ReadResult";

Goal "|- Write ch mm rs p l --> (rs!p)` ~= #NotAResult";
by (auto_tac (mem_css addsimps2 ([Write_def,WriteInner_def,GoodWrite_def,BadWrite_def])));
qed "WriteResult";

Goal "|- (ALL l. $MemInv mm l) & MemReturn ch rs p \
\        --> ~ Read ch mm rs p & (ALL l. ~ Write ch mm rs p l)";
by (auto_tac (mem_css addsimps2 [MemReturn_def] addSDs2 [WriteResult, ReadResult]));
qed "ReturnNotReadWrite";

Goal "|- (rs!p = #NotAResult) & (!l. MemInv mm l)  \
\        & Enabled (Read ch mm rs p | (? l. Write ch mm rs p l)) \
\        --> Enabled (<RNext ch mm rs p>_(rtrner ch ! p, rs!p))";
by (force_tac (mem_css addsimps2 [RNext_def,angle_def]
	               addSEs2 [enabled_mono2]
	               addDs2 [ReadResult, WriteResult]) 1);
qed "RWRNext_enabled";


(* Combine previous lemmas: the memory can make a visible step if there is an
   outstanding call for which no result has been produced.
*)
Goal "!!p. !l. basevars (mm!l, rtrner ch!p, rs!p) ==> \
\     |- (rs!p = #NotAResult) & Calling ch p & (!l. MemInv mm l)  \
\        --> Enabled (<RNext ch mm rs p>_(rtrner ch ! p, rs!p))";
by (auto_tac (mem_css addsimps2 [enabled_disj] addSIs2 [RWRNext_enabled]));
by (case_tac "arg(ch w p)" 1);
 by (action_simp_tac (simpset()addsimps[Read_def,enabled_ex])
                     [ReadInner_enabled,exI] [] 1);
 by (force_tac (mem_css addDs2 [base_pair]) 1);
by (etac swap 1);
by (action_simp_tac (simpset() addsimps [Write_def,enabled_ex])
	            [WriteInner_enabled,exI] [] 1);
qed "RNext_enabled";
