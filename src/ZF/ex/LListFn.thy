(*  Title: 	ZF/ex/llist-fn.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Functions for Lazy Lists in Zermelo-Fraenkel Set Theory 

STILL NEEDS:
co_recursion for defining lconst, flip, etc.
a typing rule for it, based on some notion of "productivity..."
*)

LListFn = LList + LList_Eq +
consts
  lconst   :: "i => i"
  flip     :: "i => i"

rules
  lconst_def  "lconst(a) == lfp(univ(a), %l. LCons(a,l))"

  flip_LNil   "flip(LNil) = LNil"

  flip_LCons  "[| x:bool; l: llist(bool) |] ==> \
\              flip(LCons(x,l)) = LCons(not(x), flip(l))"

end
