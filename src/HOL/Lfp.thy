(*  Title:      HOL/Lfp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The Knaster-Tarski Theorem
*)

theory Lfp = Product_Type:

constdefs
  lfp :: "['a set \<Rightarrow> 'a set] \<Rightarrow> 'a set"
  "lfp(f) == Inter({u. f(u) <= u})"    (*least fixed point*)

end
