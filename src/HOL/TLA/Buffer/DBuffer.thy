(*
    File:        DBuffer.thy
    ID:          $Id$
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

   Theory Name: DBuffer
   Logic Image: TLA
*)

header {* Two FIFO buffers in a row, with interleaving assumption *}

theory DBuffer
imports Buffer
begin

consts
  (* implementation variables *)
  inp  :: "nat stfun"
  mid  :: "nat stfun"
  out  :: "nat stfun"
  q1   :: "nat list stfun"
  q2   :: "nat list stfun"
  qc   :: "nat list stfun"

  DBInit :: stpred
  DBEnq :: action
  DBDeq :: action
  DBPass :: action
  DBNext :: action
  DBuffer :: temporal

axioms
  DB_base:        "basevars (inp,mid,out,q1,q2)"

  (* the concatenation of the two buffers *)
  qc_def:         "PRED qc == PRED (q2 @ q1)"

  DBInit_def:     "DBInit   == PRED (BInit inp q1 mid  &  BInit mid q2 out)"
  DBEnq_def:      "DBEnq    == ACT  Enq inp q1 mid  &  unchanged (q2,out)"
  DBDeq_def:      "DBDeq    == ACT  Deq mid q2 out  &  unchanged (inp,q1)"
  DBPass_def:     "DBPass   == ACT  Deq inp q1 mid
                                 & (q2$ = $q2 @ [ mid$ ])
                                 & (out$ = $out)"
  DBNext_def:     "DBNext   == ACT  (DBEnq | DBDeq | DBPass)"
  DBuffer_def:    "DBuffer  == TEMP Init DBInit
                                 & [][DBNext]_(inp,mid,out,q1,q2)
                                 & WF(DBDeq)_(inp,mid,out,q1,q2)
                                 & WF(DBPass)_(inp,mid,out,q1,q2)"

ML {* use_legacy_bindings (the_context ()) *}

end