(*  Title: 	ZF/ex/acc
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Inductive definition of acc(r)

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

structure Acc = Inductive_Fun
 (val thy        = WF.thy addconsts [(["acc"],"i=>i")]
  val rec_doms   = [("acc", "field(r)")]
  val sintrs     = ["[| r-``{a}: Pow(acc(r)); a: field(r) |] ==> a: acc(r)"]
  val monos      = [Pow_mono]
  val con_defs   = []
  val type_intrs = []
  val type_elims = []);

(*The introduction rule must require  a:field(r)  
  Otherwise acc(r) would be a proper class!    *)

goal Acc.thy "!!a b r. [| b: acc(r);  <a,b>: r |] ==> a: acc(r)";
by (etac Acc.elim 1);
by (fast_tac ZF_cs 1);
val acc_downward = result();

val [major,indhyp] = goal Acc.thy
    "[| a : acc(r);						\
\       !!x. [| x: acc(r);  ALL y. <y,x>:r --> P(y) |] ==> P(x)	\
\    |] ==> P(a)";
by (rtac (major RS Acc.induct) 1);
by (rtac indhyp 1);
by (fast_tac ZF_cs 2);
by (resolve_tac Acc.intrs 1);
by (assume_tac 2);
by (fast_tac ZF_cs 1);
val acc_induct = result();

goal Acc.thy "wf[acc(r)](r)";
by (rtac wf_onI2 1);
by (etac acc_induct 1);
by (fast_tac ZF_cs 1);
val wf_on_acc = result();

(* field(r) <= acc(r) ==> wf(r) *)
val acc_wfI = wf_on_acc RS wf_on_subset_A RS wf_on_field_imp_wf;

val [major] = goal Acc.thy "wf(r) ==> field(r) <= acc(r)";
by (rtac subsetI 1);
by (etac (major RS wf_induct2) 1);
by (rtac subset_refl 1);
by (resolve_tac Acc.intrs 1);
by (assume_tac 2);
by (fast_tac ZF_cs 1);
val acc_wfD = result();

goal Acc.thy "wf(r) <-> field(r) <= acc(r)";
by (EVERY1 [rtac iffI, etac acc_wfD, etac acc_wfI]);
val wf_acc_iff = result();
