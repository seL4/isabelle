(*  Title: 	ZF/ex/LList.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Codatatype definition of Lazy Lists

Equality for llist(A) as a greatest fixed point

Functions for Lazy Lists

STILL NEEDS:
co_recursion for defining lconst, flip, etc.
a typing rule for it, based on some notion of "productivity..."
*)

LList = QUniv + "Datatype" +

consts
  llist  :: "i=>i"

codatatype
  "llist(A)" = LNil | LCons ("a: A", "l: llist(A)")


(*Coinductive definition of equality*)
consts
  lleq :: "i=>i"

(*Previously used <*> in the domain and variant pairs as elements.  But
  standard pairs work just as well.  To use variant pairs, must change prefix
  a q/Q to the Sigma, Pair and converse rules.*)
coinductive
  domains "lleq(A)" <= "llist(A) * llist(A)"
  intrs
    LNil  "<LNil, LNil> : lleq(A)"
    LCons "[| a:A; <l,l'>: lleq(A) |] ==> <LCons(a,l), LCons(a,l')>: lleq(A)"
  type_intrs  "llist.intrs"


(*Lazy list functions; flip is not definitional!*)
consts
  lconst   :: "i => i"
  flip     :: "i => i"

rules
  lconst_def  "lconst(a) == lfp(univ(a), %l. LCons(a,l))"

  flip_LNil   "flip(LNil) = LNil"

  flip_LCons  "[| x:bool; l: llist(bool) |] ==> \
\              flip(LCons(x,l)) = LCons(not(x), flip(l))"

end

