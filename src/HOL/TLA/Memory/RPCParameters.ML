(* 
    File:        RPCParameters.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    RPC-Memory example: RPC parameters (ML file)
*)


val RP_simps = MP_simps @ [RFNoMemVal, NotAResultNotRF, OKNotRF, BANotRF]
                        @ (map (fn x => x RS not_sym) [NotAResultNotRF, OKNotRF, BANotRF])
                        @ rpcOps.simps @ rpcState.simps;
