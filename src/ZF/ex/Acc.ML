(*  Title: 	ZF/ex/acc
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Inductive definition of acc(r)

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

structure Acc = Inductive_Fun
 (val thy = WF.thy addconsts [(["acc"],"i=>i")];
  val rec_doms = [("acc", "field(r)")];
  val sintrs = 
      ["[| r-``{b} : Pow(acc(r));  b : field(r) |] ==> b : acc(r)"];
  val monos = [Pow_mono];
  val con_defs = [];
  val type_intrs = [];
  val type_elims = []);

goal Acc.thy "!!a b r. [| b: acc(r);  <a,b>: r |] ==> a: acc(r)";
by (etac Acc.elim 1);
by (fast_tac ZF_cs 1);
val acc_downward = result();

val [major] = goal Acc.thy "field(r) <= acc(r) ==> wf(r)";
by (rtac (major RS wfI2) 1);
by (rtac subsetI 1);
by (etac Acc.induct 1);
by (etac (bspec RS mp) 1);
by (resolve_tac Acc.intrs 1);
by (assume_tac 2);
by (ALLGOALS (fast_tac ZF_cs));
val acc_wfI = result();

goal ZF.thy "!!r A. field(r Int A*A) <= field(r) Int A";
by (fast_tac ZF_cs 1);
val field_Int_prodself = result();

goal Acc.thy "wf(r Int (acc(r)*acc(r)))";
by (rtac (field_Int_prodself RS wfI2) 1);
by (rtac subsetI 1);
by (etac IntE 1);
by (etac Acc.induct 1);
by (etac (bspec RS mp) 1);
by (rtac IntI 1);
by (assume_tac 1);
by (resolve_tac Acc.intrs 1);
by (assume_tac 2);
by (ALLGOALS (fast_tac ZF_cs));
val wf_acc_Int = result();

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
