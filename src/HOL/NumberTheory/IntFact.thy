(*  Title:	IntFact.thy
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge
*)

IntFact = IntPrimes + 

consts
  zfact    :: int => int
  setprod  :: int set => int
  d22set   :: int => int set

recdef zfact "measure ((% n.(nat n)) ::int=>nat)"
    "zfact n = (if n<=#0 then #1 else n*zfact(n-#1))"

defs
  setprod_def  "setprod A == (if finite A then fold (op*) #1 A else #1)"

recdef d22set "measure ((%a.(nat a)) ::int=>nat)"
    "d22set a = (if #1<a then insert a (d22set (a-#1)) else {})"

end