(*  Title:      HOL/ex/Acc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Inductive definition of acc(r)

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

(*The intended introduction rule*)
val prems = goal Acc.thy
    "[| !!b. (b,a):r ==> b: acc(r) |] ==> a: acc(r)";
by (fast_tac (claset() addIs prems @ 
                             map (rewrite_rule [pred_def]) acc.intrs) 1);
qed "accI";

Goal "[| b: acc(r);  (a,b): r |] ==> a: acc(r)";
by (etac acc.elim 1);
by (rewtac pred_def);
by (Fast_tac 1);
qed "acc_downward";

Goal "(b,a) : r^* ==> a : acc r --> b : acc r";
by (etac rtrancl_induct 1);
by (Blast_tac 1);
 by (blast_tac (claset() addDs [acc_downward]) 1);
val lemma = result();
Goal "[| a : acc r; (b,a) : r^* |] ==> b : acc r";
by (blast_tac (claset() addDs [lemma]) 1);
qed "acc_downwards";

val [major,indhyp] = goal Acc.thy
    "[| a : acc(r);                                             \
\       !!x. [| x: acc(r);  ALL y. (y,x):r --> P(y) |] ==> P(x) \
\    |] ==> P(a)";
by (rtac (major RS acc.induct) 1);
by (rtac indhyp 1);
by (resolve_tac acc.intrs 1);
by (rewtac pred_def);
by (Fast_tac 2);
by (etac (Int_lower1 RS Pow_mono RS subsetD) 1);
qed "acc_induct";

Goal "!x. x : acc(r) ==> wf(r)";
by (rtac wfUNIVI 1);
by (deepen_tac (claset() addEs [acc_induct]) 1 1);
qed "acc_wfI";

Goal "wf(r) ==> x : acc(r)";
by (etac wf_induct 1);
by (rtac accI 1);
by (Blast_tac 1);
qed "acc_wfD";

Goal "wf(r)  =  (!x. x : acc(r))";
by (blast_tac (claset() addIs [acc_wfI] addDs [acc_wfD]) 1);
qed "wf_acc_iff";
