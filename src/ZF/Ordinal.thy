(*  Title:      ZF/Ordinal.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Ordinals in Zermelo-Fraenkel Set Theory 
*)

Ordinal = WF + Bool + equalities +
consts
  Memrel        :: i=>i
  Transset,Ord  :: i=>o
  "<"           :: [i,i] => o  (infixl 50) (*less than on ordinals*)
  Limit         :: i=>o

syntax
  "le"          :: [i,i] => o  (infixl 50) (*less than or equals*)

translations
  "x le y"      == "x < succ(y)"

syntax (xsymbols)
  "op le"       :: [i,i] => o  (infixl "\\<le>" 50) (*less than or equals*)

defs
  Memrel_def    "Memrel(A)   == {z: A*A . EX x y. z=<x,y> & x:y }"
  Transset_def  "Transset(i) == ALL x:i. x<=i"
  Ord_def       "Ord(i)      == Transset(i) & (ALL x:i. Transset(x))"
  lt_def        "i<j         == i:j & Ord(j)"
  Limit_def     "Limit(i)    == Ord(i) & 0<i & (ALL y. y<i --> succ(y)<i)"

end
