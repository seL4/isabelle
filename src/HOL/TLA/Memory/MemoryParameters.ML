(* 
    File:        MemoryParameters.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: memory parameters (ML file)
*)

Addsimps ([BadArgNoMemVal,MemFailNoMemVal,InitValMemVal,NotAResultNotVal,
                  NotAResultNotOK, NotAResultNotBA, NotAResultNotMF]
               @ (map (fn x => x RS not_sym) 
                      [NotAResultNotOK, NotAResultNotBA, NotAResultNotMF]));

val prems = goal thy "[| x : MemVal; (x ~= NotAResult ==> P) |] ==> P";
by (resolve_tac prems 1);
by (cut_facts_tac (NotAResultNotVal::prems) 1);
by (Force_tac 1);
qed "MemValNotAResultE";
