(* 
    File:        RPCParameters.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: RPC parameters (theorems and proofs)
*)


(*
val RP_simps = MP_simps @ [RFNoMemVal, NotAResultNotRF, OKNotRF, BANotRF]
                        @ (map (fn x => x RS not_sym) [NotAResultNotRF, OKNotRF, BANotRF])
                        @ rpcState.simps @ rpcOp.simps;
*)

Addsimps ([RFNoMemVal, NotAResultNotRF, OKNotRF, BANotRF]
          @ (map (fn x => x RS not_sym) [NotAResultNotRF, OKNotRF, BANotRF]));
