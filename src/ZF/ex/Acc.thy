(*  Title: 	ZF/ex/Acc.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Inductive definition of acc(r)

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

Acc = WF + "inductive" +

consts
  "acc" :: "i=>i"

inductive
  domains "acc(r)" <= "field(r)"
  intrs
    vimage  "[| r-``{a}: Pow(acc(r)); a: field(r) |] ==> a: acc(r)"
  monos     "[Pow_mono]"

end
