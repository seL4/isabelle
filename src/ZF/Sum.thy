(*  Title: 	ZF/sum.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Disjoint sums in Zermelo-Fraenkel Set Theory 
"Part" primitive for simultaneous recursive type definitions
*)

Sum = Bool + "simpdata" +
consts
    "+"    	:: "[i,i]=>i"      		(infixr 65)
    Inl,Inr     :: "i=>i"
    case        :: "[i=>i, i=>i, i]=>i"
    Part        :: "[i,i=>i] => i"

rules
    sum_def     "A+B == {0}*A Un {1}*B"
    Inl_def     "Inl(a) == <0,a>"
    Inr_def     "Inr(b) == <1,b>"
    case_def    "case(c,d) == split(%y z. cond(y, d(z), c(z)))"

  (*operator for selecting out the various summands*)
    Part_def	"Part(A,h) == {x: A. EX z. x = h(z)}"
end
