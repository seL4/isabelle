(*  Title: 	ZF/ex/acc
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Inductive definition of acc(r)

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

open Acc;

(*The introduction rule must require  a:field(r)  
  Otherwise acc(r) would be a proper class!    *)

(*The intended introduction rule*)
val prems = goal Acc.thy
    "[| !!b. <b,a>:r ==> b: acc(r);  a: field(r) |] ==> a: acc(r)";
by (fast_tac (ZF_cs addIs (prems@acc.intrs)) 1);
qed "accI";

goal Acc.thy "!!a b r. [| b: acc(r);  <a,b>: r |] ==> a: acc(r)";
by (etac acc.elim 1);
by (fast_tac ZF_cs 1);
qed "acc_downward";

val [major,indhyp] = goal Acc.thy
    "[| a : acc(r);						\
\       !!x. [| x: acc(r);  ALL y. <y,x>:r --> P(y) |] ==> P(x)	\
\    |] ==> P(a)";
by (rtac (major RS acc.induct) 1);
by (rtac indhyp 1);
by (fast_tac ZF_cs 2);
by (resolve_tac acc.intrs 1);
by (assume_tac 2);
by (etac (Collect_subset RS Pow_mono RS subsetD) 1);
qed "acc_induct";

goal Acc.thy "wf[acc(r)](r)";
by (rtac wf_onI2 1);
by (etac acc_induct 1);
by (fast_tac ZF_cs 1);
qed "wf_on_acc";

(* field(r) <= acc(r) ==> wf(r) *)
val acc_wfI = wf_on_acc RS wf_on_subset_A RS wf_on_field_imp_wf;

val [major] = goal Acc.thy "wf(r) ==> field(r) <= acc(r)";
by (rtac subsetI 1);
by (etac (major RS wf_induct2) 1);
by (rtac subset_refl 1);
by (rtac accI 1);
by (assume_tac 2);
by (fast_tac ZF_cs 1);
qed "acc_wfD";

goal Acc.thy "wf(r) <-> field(r) <= acc(r)";
by (EVERY1 [rtac iffI, etac acc_wfD, etac acc_wfI]);
qed "wf_acc_iff";
