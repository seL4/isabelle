(* 
    File:        MemoryParameters.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: memory parameters (ML file)
*)

(*
val MP_simps = [BadArgNoMemVal,MemFailNoMemVal,InitValMemVal,NotAResultNotVal,
                  NotAResultNotOK, NotAResultNotBA, NotAResultNotMF]
               @ (map (fn x => x RS not_sym) 
                      [NotAResultNotOK, NotAResultNotBA, NotAResultNotMF]);
*)

Addsimps ([BadArgNoMemVal,MemFailNoMemVal,InitValMemVal,NotAResultNotVal,
                  NotAResultNotOK, NotAResultNotBA, NotAResultNotMF]
               @ (map (fn x => x RS not_sym) 
                      [NotAResultNotOK, NotAResultNotBA, NotAResultNotMF]));

(* Auxiliary rules *)

qed_goal "MemValNotAResultE" MemoryParameters.thy
   "[| x : MemVal; (x ~= NotAResult ==> P) |] ==> P"
   (fn prems => [resolve_tac prems 1,
                 cut_facts_tac (NotAResultNotVal::prems) 1,
                 Force_tac 1
                ]);

