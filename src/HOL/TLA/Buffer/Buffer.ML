(* 
    File:        Buffer.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Simple FIFO buffer (theorems and proofs)
*)

(* ---------------------------- Data lemmas ---------------------------- *)

(* "xs ~= [] --> tl(xs @ ys) = (tl xs) @ ys" *)
Addsimps [tl_append2];

goal List.thy "xs ~= [] --> tl xs ~= xs";
by (auto_tac (claset(), simpset() addsimps [neq_Nil_conv]));
qed_spec_mp "tl_not_self";
Addsimps [tl_not_self];

(* "!ys zs. (ys @ xs = zs @ xs) = (ys=zs)" has been subsumed *)

(* ---------------------------- Action lemmas ---------------------------- *)

(* Dequeue is visible *)
goal Buffer.thy "<Deq ic q oc>_<ic,q,oc> .= Deq ic q oc";
by (auto_tac (claset(), simpset() addsimps [angle_def,Deq_def]));
qed "Deq_visible";

(* Enabling condition for dequeue -- NOT NEEDED *)
goalw Buffer.thy [temp_rewrite Deq_visible]
   "!!q. base_var <ic,q,oc> ==> $Enabled (<Deq ic q oc>_<ic,q,oc>) .= ($q .~= .[])";
by (auto_tac (claset() addSEs [base_enabled,enabledE], simpset() addsimps [Deq_def]));
qed "Deq_enabled";

(* For the left-to-right implication, we don't need the base variable stuff *)
goalw Buffer.thy [temp_rewrite Deq_visible] 
   "$Enabled (<Deq ic q oc>_<ic,q,oc>) .-> ($q .~= .[])";
by (auto_tac (claset() addSEs [enabledE], simpset() addsimps [Deq_def]));
qed "Deq_enabledE";
