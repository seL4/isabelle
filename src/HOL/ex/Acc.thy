(*  Title:      HOL/ex/Acc.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Inductive definition of acc(r)

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

Acc = WF + 

consts
  pred :: "['b, ('a * 'b)set] => 'a set"        (*Set of predecessors*)
  acc  :: "('a * 'a)set => 'a set"              (*Accessible part*)

defs
  pred_def  "pred x r == {y. (y,x):r}"

inductive "acc(r)"
  intrs
    pred    "pred a r: Pow(acc(r)) ==> a: acc(r)"
  monos     "[Pow_mono]"

end
