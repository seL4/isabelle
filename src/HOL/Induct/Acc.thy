(*  Title:      HOL/ex/Acc.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Inductive definition of acc(r)

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

header {* The acessible part of a relation *};

theory Acc = WF + Inductive:;

consts
  acc  :: "('a * 'a)set => 'a set"  -- {* accessible part *};

inductive "acc r"
  intrs
    accI [rulify_prems]:
      "ALL y. (y, x) : r --> y : acc r ==> x : acc r"

syntax
  termi :: "('a * 'a)set => 'a set"
translations
  "termi r" == "acc(r^-1)"

end
