(* 
    File:        MemoryParameters.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: memory parameters (ML file)
*)

val MP_simps = [BadArgNoMemVal,MemFailNoMemVal,InitValMemVal,NotAResultNotVal,
                  NotAResultNotOK, NotAResultNotBA, NotAResultNotMF]
               @ (map (fn x => x RS not_sym) 
                      [NotAResultNotOK, NotAResultNotBA, NotAResultNotMF]);


(* Auxiliary rules *)

qed_goal "MemValNotAResultE" MemoryParameters.thy
   "[| MemVal x; (x ~= NotAResult ==> P) |] ==> P"
   (fn [min,maj] => [rtac maj 1,
                     case_tac "x = NotAResult" 1,
                     cut_facts_tac [min,NotAResultNotVal] 1,
                     ALLGOALS Asm_full_simp_tac
                    ]);

