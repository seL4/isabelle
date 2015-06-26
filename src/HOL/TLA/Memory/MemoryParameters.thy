(*  Title:      HOL/TLA/Memory/MemoryParameters.thy
    Author:     Stephan Merz, University of Munich
*)

section {* RPC-Memory example: Memory parameters *}

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
  BadArgNoMemVal:    "BadArg \<notin> MemVal" and
  MemFailNoMemVal:   "MemFailure \<notin> MemVal" and
  InitValMemVal:     "InitVal : MemVal" and
  NotAResultNotVal:  "NotAResult \<notin> MemVal" and
  NotAResultNotOK:   "NotAResult \<noteq> OK" and
  NotAResultNotBA:   "NotAResult \<noteq> BadArg" and
  NotAResultNotMF:   "NotAResult \<noteq> MemFailure"

lemmas [simp] =
  BadArgNoMemVal MemFailNoMemVal InitValMemVal NotAResultNotVal
  NotAResultNotOK NotAResultNotBA NotAResultNotMF
  NotAResultNotOK [symmetric] NotAResultNotBA [symmetric] NotAResultNotMF [symmetric]

lemma MemValNotAResultE: "[| x : MemVal; (x \<noteq> NotAResult ==> P) |] ==> P"
  using NotAResultNotVal by blast

end
