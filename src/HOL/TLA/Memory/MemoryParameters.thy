(*
    File:        MemoryParameters.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: MemoryParameters
    Logic Image: TLA

    RPC-Memory example: Memory parameters
*)

MemoryParameters = Prod + Sum + Arith + RPCMemoryParams +

(* the memory operations. nb: data types must be defined in theories
   that do not include Intensional -- otherwise the induction rule
   can't be type-checked unambiguously.
*)
datatype  Rd = read
datatype  Wr = write

types
  (* legal arguments for the memory *)
  memArgType = "(Rd * Locs) + (Wr * Locs * Vals)"

consts
  (* memory locations and contents *)
  MemLoc         :: "Locs => bool"
  MemVal         :: "Vals => bool"

  (* some particular values *)
  OK             :: "Vals"
  BadArg         :: "Vals"
  MemFailure     :: "Vals"
  NotAResult     :: "Vals"  (* defined here for simplicity *)
  
  (* the initial value stored in each memory cell *)
  InitVal        :: "Vals"

rules
  (* basic assumptions about the above constants and predicates *)
  BadArgNoMemVal    "~MemVal(BadArg)"
  MemFailNoMemVal   "~MemVal(MemFailure)"
  InitValMemVal     "MemVal(InitVal)"
  NotAResultNotVal  "~MemVal(NotAResult)"
  NotAResultNotOK   "NotAResult ~= OK"
  NotAResultNotBA   "NotAResult ~= BadArg"
  NotAResultNotMF   "NotAResult ~= MemFailure"
end


