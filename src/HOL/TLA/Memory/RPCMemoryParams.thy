(* 
    File:        RPCMemoryParams.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: RPCMemoryParams
    Logic Image: TLA

    Basic declarations for the RPC-memory example.
*)

theory RPCMemoryParams = Main:

types
  bit = "bool"   (* Signal wires for the procedure interface.
                    Defined as bool for simplicity. All I should really need is
                    the existence of two distinct values. *)

(* all of these are simple (HOL) types *)
typedecl Locs    (* "syntactic" value type *)
typedecl Vals    (* "syntactic" value type *)
typedecl PrIds   (* process id's *)

end
