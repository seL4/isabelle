(* 
    File:        RPCMemoryParams.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: RPCMemoryParams
    Logic Image: TLA

    Basic declarations for the RPC-memory example.
*)

RPCMemoryParams = HOL +

types
  bit = "bool"   (* Signal wires for the procedure interface.
                    Defined as bool for simplicity. All I should really need is
                    the existence of two distinct values. *)
  Locs           (* "syntactic" value type *)
  Vals           (* "syntactic" value type *)
  PrIds          (* process id's *)

(* all of these are simple (HOL) types *)
arities
  Locs   :: term
  Vals   :: term
  PrIds  :: term

end
