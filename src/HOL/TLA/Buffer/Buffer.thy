(*  Title:      HOL/TLA/Buffer/Buffer.thy
    Author:     Stephan Merz, University of Munich
*)

section {* A simple FIFO buffer (synchronous communication, interleaving) *}

theory Buffer
imports TLA
begin

consts
  (* actions *)
  BInit     :: "'a stfun => 'a list stfun => 'a stfun => stpred"
  Enq       :: "'a stfun => 'a list stfun => 'a stfun => action"
  Deq       :: "'a stfun => 'a list stfun => 'a stfun => action"
  Next      :: "'a stfun => 'a list stfun => 'a stfun => action"

  (* temporal formulas *)
  IBuffer   :: "'a stfun => 'a list stfun => 'a stfun => temporal"
  Buffer    :: "'a stfun => 'a stfun => temporal"

defs
  BInit_def:   "BInit ic q oc    == PRED q = #[]"
  Enq_def:     "Enq ic q oc      == ACT (ic$ ~= $ic)
                                     & (q$ = $q @ [ ic$ ])
                                     & (oc$ = $oc)"
  Deq_def:     "Deq ic q oc      == ACT ($q ~= #[])
                                     & (oc$ = hd< $q >)
                                     & (q$ = tl< $q >)
                                     & (ic$ = $ic)"
  Next_def:    "Next ic q oc     == ACT (Enq ic q oc | Deq ic q oc)"
  IBuffer_def: "IBuffer ic q oc  == TEMP Init (BInit ic q oc)
                                      & [][Next ic q oc]_(ic,q,oc)
                                      & WF(Deq ic q oc)_(ic,q,oc)"
  Buffer_def:  "Buffer ic oc     == TEMP (EEX q. IBuffer ic q oc)"


(* ---------------------------- Data lemmas ---------------------------- *)

(*FIXME: move to theory List? Maybe as (tl xs = xs) = (xs = [])"?*)
lemma tl_not_self [simp]: "xs ~= [] ==> tl xs ~= xs"
  by (auto simp: neq_Nil_conv)


(* ---------------------------- Action lemmas ---------------------------- *)

(* Dequeue is visible *)
lemma Deq_visible: "|- <Deq ic q oc>_(ic,q,oc) = Deq ic q oc"
  apply (unfold angle_def Deq_def)
  apply (safe, simp (asm_lr))+
  done

(* Enabling condition for dequeue -- NOT NEEDED *)
lemma Deq_enabled: 
    "!!q. basevars (ic,q,oc) ==> |- Enabled (<Deq ic q oc>_(ic,q,oc)) = (q ~= #[])"
  apply (unfold Deq_visible [temp_rewrite])
  apply (force elim!: base_enabled [temp_use] enabledE [temp_use] simp: Deq_def)
  done

(* For the left-to-right implication, we don't need the base variable stuff *)
lemma Deq_enabledE: 
    "|- Enabled (<Deq ic q oc>_(ic,q,oc)) --> (q ~= #[])"
  apply (unfold Deq_visible [temp_rewrite])
  apply (auto elim!: enabledE simp add: Deq_def)
  done

end
