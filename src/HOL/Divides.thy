(*  Title:      HOL/Divides.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The division operators div, mod and the divides relation "dvd"
*)

Divides = Arith +

consts
  div, mod  :: [nat, nat] => nat          (infixl 70)
  dvd     :: [nat,nat]=>bool              (infixl 70) 


defs
  mod_def   "m mod n == wfrec (trancl pred_nat)
                          (%f j. if j<n then j else f (j-n)) m"
  div_def   "m div n == wfrec (trancl pred_nat) 
                          (%f j. if j<n then 0 else Suc (f (j-n))) m"

  dvd_def   "m dvd n == EX k. n = m*k"

end
