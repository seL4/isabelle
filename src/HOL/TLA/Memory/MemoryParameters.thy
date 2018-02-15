(*  Title:      HOL/TLA/Memory/MemoryParameters.thy
    Author:     Stephan Merz, University of Munich
*)

section \<open>RPC-Memory example: Memory parameters\<close>

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
  InitValMemVal:     "InitVal \<in> MemVal" and
  NotAResultNotVal:  "NotAResult \<notin> MemVal" and
  NotAResultNotOK:   "NotAResult \<noteq> OK" and
  NotAResultNotBA:   "NotAResult \<noteq> BadArg" and
  NotAResultNotMF:   "NotAResult \<noteq> MemFailure"

lemmas [simp] =
  BadArgNoMemVal MemFailNoMemVal InitValMemVal NotAResultNotVal
  NotAResultNotOK NotAResultNotBA NotAResultNotMF
  NotAResultNotOK [symmetric] NotAResultNotBA [symmetric] NotAResultNotMF [symmetric]

lemma MemValNotAResultE: "\<lbrakk> x \<in> MemVal; (x \<noteq> NotAResult \<Longrightarrow> P) \<rbrakk> \<Longrightarrow> P"
  using NotAResultNotVal by blast

end
