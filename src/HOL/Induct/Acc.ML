(*  Title:      HOL/ex/Acc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Inductive definition of acc(r)

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

open Acc;

(*The intended introduction rule*)
val prems = goal Acc.thy
    "[| !!b. (b,a):r ==> b: acc(r) |] ==> a: acc(r)";
by (fast_tac (!claset addIs (prems @ 
                            map (rewrite_rule [pred_def]) acc.intrs)) 1);
qed "accI";

goal Acc.thy "!!a b r. [| b: acc(r);  (a,b): r |] ==> a: acc(r)";
by (etac acc.elim 1);
by (rewtac pred_def);
by (Fast_tac 1);
qed "acc_downward";

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


val [major] = goal Acc.thy "r <= (acc r) Times (acc r) ==> wf(r)";
by (rtac (major RS wfI) 1);
by (etac acc.induct 1);
by (rewtac pred_def);
by (Fast_tac 1);
qed "acc_wfI";

val [major] = goal Acc.thy "wf(r) ==> ALL x. (x,y): r | (y,x):r --> y: acc(r)";
by (rtac (major RS wf_induct) 1);
by (rtac (impI RS allI) 1);
by (rtac accI 1);
by (Fast_tac 1);
qed "acc_wfD_lemma";

val [major] = goal Acc.thy "wf(r) ==> r <= (acc r) Times (acc r)";
by (rtac subsetI 1);
by (res_inst_tac [("p", "x")] PairE 1);
by (fast_tac (!claset addSIs [SigmaI,
                             major RS acc_wfD_lemma RS spec RS mp]) 1);
qed "acc_wfD";

goal Acc.thy "wf(r)  =  (r <= (acc r) Times (acc r))";
by (EVERY1 [rtac iffI, etac acc_wfD, etac acc_wfI]);
qed "wf_acc_iff";
