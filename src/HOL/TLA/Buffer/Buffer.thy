(*  Title:      HOL/TLA/Buffer/Buffer.thy
    Author:     Stephan Merz, University of Munich
*)

section \<open>A simple FIFO buffer (synchronous communication, interleaving)\<close>

theory Buffer
imports "HOL-TLA.TLA"
begin

(* actions *)

definition BInit :: "'a stfun \<Rightarrow> 'a list stfun \<Rightarrow> 'a stfun \<Rightarrow> stpred"
  where "BInit ic q oc == PRED q = #[]"

definition Enq :: "'a stfun \<Rightarrow> 'a list stfun \<Rightarrow> 'a stfun \<Rightarrow> action"
  where "Enq ic q oc == ACT (ic$ \<noteq> $ic)
                         \<and> (q$ = $q @ [ ic$ ])
                         \<and> (oc$ = $oc)"

definition Deq :: "'a stfun \<Rightarrow> 'a list stfun \<Rightarrow> 'a stfun \<Rightarrow> action"
  where "Deq ic q oc == ACT ($q \<noteq> #[])
                         \<and> (oc$ = hd< $q >)
                         \<and> (q$ = tl< $q >)
                         \<and> (ic$ = $ic)"

definition Next :: "'a stfun \<Rightarrow> 'a list stfun \<Rightarrow> 'a stfun \<Rightarrow> action"
  where "Next ic q oc == ACT (Enq ic q oc \<or> Deq ic q oc)"


(* temporal formulas *)

definition IBuffer :: "'a stfun \<Rightarrow> 'a list stfun \<Rightarrow> 'a stfun \<Rightarrow> temporal"
  where "IBuffer ic q oc == TEMP Init (BInit ic q oc)
                                  \<and> \<box>[Next ic q oc]_(ic,q,oc)
                                  \<and> WF(Deq ic q oc)_(ic,q,oc)"

definition Buffer :: "'a stfun \<Rightarrow> 'a stfun \<Rightarrow> temporal"
  where "Buffer ic oc == TEMP (\<exists>\<exists>q. IBuffer ic q oc)"


(* ---------------------------- Data lemmas ---------------------------- *)

(*FIXME: move to theory List? Maybe as (tl xs = xs) = (xs = [])"?*)
lemma tl_not_self [simp]: "xs \<noteq> [] \<Longrightarrow> tl xs \<noteq> xs"
  by (auto simp: neq_Nil_conv)


(* ---------------------------- Action lemmas ---------------------------- *)

(* Dequeue is visible *)
lemma Deq_visible: "\<turnstile> <Deq ic q oc>_(ic,q,oc) = Deq ic q oc"
  apply (unfold angle_def Deq_def)
  apply (safe, simp (asm_lr))+
  done

(* Enabling condition for dequeue -- NOT NEEDED *)
lemma Deq_enabled: 
    "\<And>q. basevars (ic,q,oc) \<Longrightarrow> \<turnstile> Enabled (<Deq ic q oc>_(ic,q,oc)) = (q \<noteq> #[])"
  apply (unfold Deq_visible [temp_rewrite])
  apply (force elim!: base_enabled [temp_use] enabledE [temp_use] simp: Deq_def)
  done

(* For the left-to-right implication, we don't need the base variable stuff *)
lemma Deq_enabledE: 
    "\<turnstile> Enabled (<Deq ic q oc>_(ic,q,oc)) \<longrightarrow> (q \<noteq> #[])"
  apply (unfold Deq_visible [temp_rewrite])
  apply (auto elim!: enabledE simp add: Deq_def)
  done

end
