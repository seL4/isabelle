(*
    File:        Buffer.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

   Theory Name: Buffer
   Logic Image: TLA

   A simple FIFO buffer (synchronous communication, interleaving)
*)

Buffer = TLA + List +

consts
  (* infix syntax for list operations *)
  "IntNil"  :: 'w::world => 'a list                                       (".[]")
  "IntCons" :: ['w::world => 'a, 'w => 'a list] => ('w => 'a list)        ("(_ .#/ _)" [65,66] 65)
  "IntApp"  :: ['w::world => 'a list, 'w => 'a list] => ('w => 'a list)   ("(_ .@/ _)" [65,66] 65)

  (* actions *)
  BInit     :: "'a stfun => 'a list stfun => 'a stfun => action"
  Enq       :: "'a stfun => 'a list stfun => 'a stfun => action"
  Deq       :: "'a stfun => 'a list stfun => 'a stfun => action"
  Next      :: "'a stfun => 'a list stfun => 'a stfun => action"

  (* temporal formulas *)
  IBuffer   :: "'a stfun => 'a list stfun => 'a stfun => temporal"
  Buffer    :: "'a stfun => 'a stfun => temporal"

syntax
  "@listInt" :: args => ('a list, 'w) term      (".[(_)]")

translations
  ".[]"          == "con []"
  "x .# xs"      == "lift2 (op #) x xs"
  "xs .@ ys"     == "lift2 (op @) xs ys"
  ".[ x, xs ]"   == "x .# .[xs]"
  ".[ x ]"       == "x .# .[]"

rules
  BInit_def   "BInit ic q oc    == $q .= .[]"
  Enq_def     "Enq ic q oc      ==    (ic$ .~= $ic) 
                                   .& (q$ .= $q .@ .[ ic$ ]) 
                                   .& (oc$ .= $oc)"
  Deq_def     "Deq ic q oc      ==    ($q .~= .[])
                                   .& (oc$ .= hd[ $q ])
                                   .& (q$ .= tl[ $q ])
                                   .& (ic$ .= $ic)"
  Next_def    "Next ic q oc     == Enq ic q oc .| Deq ic q oc"
  IBuffer_def "IBuffer ic q oc  ==    Init (BInit ic q oc)
                                   .& [][Next ic q oc]_<ic,q,oc>
                                   .& WF(Deq ic q oc)_<ic,q,oc>"
  Buffer_def  "Buffer ic oc     == EEX q. IBuffer ic q oc"
end



