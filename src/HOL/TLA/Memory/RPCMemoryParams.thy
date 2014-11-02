(*  Title:      HOL/TLA/Memory/RPCMemoryParams.thy
    Author:     Stephan Merz, University of Munich
*)

section {* Basic declarations for the RPC-memory example *}

theory RPCMemoryParams
imports Main
begin

type_synonym bit = "bool"
 (* Signal wires for the procedure interface.
    Defined as bool for simplicity. All I should really need is
    the existence of two distinct values. *)

(* all of these are simple (HOL) types *)
typedecl Locs    (* "syntactic" value type *)
typedecl Vals    (* "syntactic" value type *)
typedecl PrIds   (* process id's *)

end
