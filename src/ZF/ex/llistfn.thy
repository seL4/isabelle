(*  Title: 	ZF/ex/llist-fn.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Functions for Lazy Lists in Zermelo-Fraenkel Set Theory 
*)

LListFn = LList +
consts
  lconst   :: "i => i"

rules
  lconst_def  "lconst(a) == lfp(univ(a), %l. LCons(a,l))"

end
