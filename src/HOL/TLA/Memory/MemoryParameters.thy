(*  Title:      HOL/TLA/Memory/MemoryParameters.thy
    Author:     Stephan Merz, University of Munich
*)

header {* RPC-Memory example: Memory parameters *}

theory MemoryParameters
imports RPCMemoryParams
begin

(* the memory operations *)
datatype memOp = read Locs | "write" Locs Vals

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

axiomatization where
  (* basic assumptions about the above constants and predicates *)
  BadArgNoMemVal:    "BadArg ~: MemVal" and
  MemFailNoMemVal:   "MemFailure ~: MemVal" and
  InitValMemVal:     "InitVal : MemVal" and
  NotAResultNotVal:  "NotAResult ~: MemVal" and
  NotAResultNotOK:   "NotAResult ~= OK" and
  NotAResultNotBA:   "NotAResult ~= BadArg" and
  NotAResultNotMF:   "NotAResult ~= MemFailure"

lemmas [simp] =
  BadArgNoMemVal MemFailNoMemVal InitValMemVal NotAResultNotVal
  NotAResultNotOK NotAResultNotBA NotAResultNotMF
  NotAResultNotOK [symmetric] NotAResultNotBA [symmetric] NotAResultNotMF [symmetric]

lemma MemValNotAResultE: "[| x : MemVal; (x ~= NotAResult ==> P) |] ==> P"
  using NotAResultNotVal by blast

end
