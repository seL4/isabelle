(*  Title:	WilsonBij.thy
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge
*)

WilsonBij = BijectionRel + IntFact +

consts
  reciR  :: "int => [int,int] => bool"
  inv    :: "[int,int] => int"

defs
  reciR_def "reciR p == (%a b. zcong (a*b) #1 p & 
                               #1<a & a<p-#1 & #1<b & b<p-#1)"
  inv_def   "inv p a == (if p:zprime & #0<a & a<p then
                           (@x. #0<=x & x<p & zcong (a*x) #1 p)
                         else #0)"

end
