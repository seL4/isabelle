(*
    File:        MemoryParameters.thy
    ID:          $Id$
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: MemoryParameters
    Logic Image: TLA

    RPC-Memory example: Memory parameters
*)

theory MemoryParameters
imports RPCMemoryParams
begin

(* the memory operations *)
datatype memOp = read Locs | write Locs Vals

consts
  (* memory locations and contents *)
  MemLoc         :: "Locs set"
  MemVal         :: "Vals set"

  (* some particular values *)
  OK             :: "Vals"
  BadArg         :: "Vals"
  MemFailure     :: "Vals"
  NotAResult     :: "Vals"  (* defined here for simplicity *)

  (* the initial value stored in each memory cell *)
  InitVal        :: "Vals"

axioms
  (* basic assumptions about the above constants and predicates *)
  BadArgNoMemVal:    "BadArg ~: MemVal"
  MemFailNoMemVal:   "MemFailure ~: MemVal"
  InitValMemVal:     "InitVal : MemVal"
  NotAResultNotVal:  "NotAResult ~: MemVal"
  NotAResultNotOK:   "NotAResult ~= OK"
  NotAResultNotBA:   "NotAResult ~= BadArg"
  NotAResultNotMF:   "NotAResult ~= MemFailure"

ML {* use_legacy_bindings (the_context ()) *}

end
