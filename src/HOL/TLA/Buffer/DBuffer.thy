(*
    File:        DBuffer.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

   Theory Name: DBuffer
   Logic Image: TLA

   Two FIFO buffers in a row, with interleaving assumption.
*)

DBuffer = Buffer +

consts
  (* implementation variables *)
  inp, mid, out  :: nat stfun
  q1, q2, qc     :: nat list stfun

  DBInit                         :: stpred
  DBEnq, DBDeq, DBPass, DBNext   :: action
  DBuffer                        :: temporal

rules
  DB_base        "basevars (inp,mid,out,q1,q2)"

  (* the concatenation of the two buffers *)
  qc_def         "PRED qc == PRED (q2 @ q1)"

  DBInit_def     "DBInit   == PRED (BInit inp q1 mid  &  BInit mid q2 out)"
  DBEnq_def      "DBEnq    == ACT  Enq inp q1 mid  &  unchanged (q2,out)"
  DBDeq_def      "DBDeq    == ACT  Deq mid q2 out  &  unchanged (inp,q1)"
  DBPass_def     "DBPass   == ACT  Deq inp q1 mid
                                 & (q2$ = $q2 @ [ mid$ ])
                                 & (out$ = $out)"
  DBNext_def     "DBNext   == ACT  (DBEnq | DBDeq | DBPass)"
  DBuffer_def    "DBuffer  == TEMP Init DBInit
                                 & [][DBNext]_(inp,mid,out,q1,q2)
                                 & WF(DBDeq)_(inp,mid,out,q1,q2)
                                 & WF(DBPass)_(inp,mid,out,q1,q2)"

end