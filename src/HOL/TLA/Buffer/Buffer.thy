(*
    File:        Buffer.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

   Theory Name: Buffer
   Logic Image: TLA

   A simple FIFO buffer (synchronous communication, interleaving)
*)

Buffer = TLA +

consts
  (* actions *)
  BInit     :: "'a stfun => 'a list stfun => 'a stfun => stpred"
  Enq       :: "'a stfun => 'a list stfun => 'a stfun => action"
  Deq       :: "'a stfun => 'a list stfun => 'a stfun => action"
  Next      :: "'a stfun => 'a list stfun => 'a stfun => action"

  (* temporal formulas *)
  IBuffer   :: "'a stfun => 'a list stfun => 'a stfun => temporal"
  Buffer    :: "'a stfun => 'a stfun => temporal"

rules
  BInit_def   "BInit ic q oc    == PRED q = #[]"
  Enq_def     "Enq ic q oc      == ACT (ic$ ~= $ic) 
                                     & (q$ = $q @ [ ic$ ]) 
                                     & (oc$ = $oc)"
  Deq_def     "Deq ic q oc      == ACT ($q ~= #[])
                                     & (oc$ = hd< $q >)
                                     & (q$ = tl< $q >)
                                     & (ic$ = $ic)"
  Next_def    "Next ic q oc     == ACT (Enq ic q oc | Deq ic q oc)"
  IBuffer_def "IBuffer ic q oc  == TEMP Init (BInit ic q oc)
                                      & [][Next ic q oc]_(ic,q,oc)
                                      & WF(Deq ic q oc)_(ic,q,oc)"
  Buffer_def  "Buffer ic oc     == TEMP (EEX q. IBuffer ic q oc)"
end



