(*  Title: 	ZF/ordinal.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Ordinals in Zermelo-Fraenkel Set Theory 
*)

Ord = WF + "simpdata" + "equalities" +
consts
  Memrel      	:: "i=>i"
  Transset,Ord  :: "i=>o"
  "<"           :: "[i,i] => o"  (infixl 50) (*less than on ordinals*)
  "le"          :: "[i,i] => o"  (infixl 50) (*less than or equals*)

translations
  "x le y"      == "x < succ(y)"

rules
  Memrel_def  	"Memrel(A)   == {z: A*A . EX x y. z=<x,y> & x:y }"
  Transset_def	"Transset(i) == ALL x:i. x<=i"
  Ord_def     	"Ord(i)      == Transset(i) & (ALL x:i. Transset(x))"
  lt_def        "i<j         == i:j & Ord(j)"

end
