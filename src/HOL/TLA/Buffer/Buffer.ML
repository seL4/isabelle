(* 
    File:        Buffer.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Simple FIFO buffer (theorems and proofs)
*)

(* ---------------------------- Data lemmas ---------------------------- *)

context List.thy;
goal List.thy "xs ~= [] --> tl xs ~= xs";
by (auto_tac (claset(), simpset() addsimps [neq_Nil_conv]));
qed_spec_mp "tl_not_self";
context Buffer.thy;

Addsimps [tl_not_self];

(* ---------------------------- Action lemmas ---------------------------- *)

(* Dequeue is visible *)
Goal "|- <Deq ic q oc>_(ic,q,oc) = Deq ic q oc";
by (auto_tac (claset(), simpset() addsimps [angle_def,Deq_def]));
qed "Deq_visible";

(* Enabling condition for dequeue -- NOT NEEDED *)
Goalw [temp_rewrite Deq_visible]
   "!!q. basevars (ic,q,oc) ==> |- Enabled (<Deq ic q oc>_(ic,q,oc)) = (q ~= #[])";
by (force_tac (claset() addSEs [base_enabled,enabledE], simpset() addsimps [Deq_def]) 1);
qed "Deq_enabled";

(* For the left-to-right implication, we don't need the base variable stuff *)
Goalw [temp_rewrite Deq_visible] 
   "|- Enabled (<Deq ic q oc>_(ic,q,oc)) --> (q ~= #[])";
by (auto_tac (claset() addSEs [enabledE], simpset() addsimps [Deq_def]));
qed "Deq_enabledE";
