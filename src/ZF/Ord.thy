(*  Title: 	ZF/ordinal.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Ordinals in Zermelo-Fraenkel Set Theory 
*)

Ord = WF +
consts
    Memrel      	::      "i=>i"
    Transset,Ord        ::      "i=>o"

rules
  Memrel_def  	"Memrel(A)   == {z: A*A . EX x y. z=<x,y> & x:y }"
  Transset_def	"Transset(i) == ALL x:i. x<=i"
  Ord_def     	"Ord(i)      == Transset(i) & (ALL x:i. Transset(x))"

end
