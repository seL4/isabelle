(* 
    File:        Buffer.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Simple FIFO buffer (theorems and proofs)
*)

(* ---------------------------- Data lemmas ---------------------------- *)

(*FIXME: move to List.thy? Maybe as (tl xs = xs) = (xs = [])"?*)
Goal "xs ~= [] --> tl xs ~= xs";
by (auto_tac (claset(), simpset() addsimps [neq_Nil_conv]));
qed_spec_mp "tl_not_self";
context Buffer.thy;

Addsimps [tl_not_self];

(* ---------------------------- Action lemmas ---------------------------- *)

(* Dequeue is visible *)
Goalw [angle_def,Deq_def] "|- <Deq ic q oc>_(ic,q,oc) = Deq ic q oc";
by (REPEAT (Safe_tac THEN Asm_lr_simp_tac 1));
qed "Deq_visible";

(* Enabling condition for dequeue -- NOT NEEDED *)
Goalw [temp_rewrite Deq_visible]
   "!!q. basevars (ic,q,oc) ==> |- Enabled (<Deq ic q oc>_(ic,q,oc)) = (q ~= #[])";
by (force_tac (claset() addSEs [base_enabled,enabledE], 
               simpset() addsimps [Deq_def]) 1);
qed "Deq_enabled";

(* For the left-to-right implication, we don't need the base variable stuff *)
Goalw [temp_rewrite Deq_visible] 
   "|- Enabled (<Deq ic q oc>_(ic,q,oc)) --> (q ~= #[])";
by (auto_tac (claset() addSEs [enabledE], simpset() addsimps [Deq_def]));
qed "Deq_enabledE";
