(*  Title:      HOL/Divides.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

The division operators div, mod and the divides relation "dvd"
*)

Divides = Arith +

(*We use the same class for div and mod;
  moreover, dvd is defined whenever multiplication is*)
axclass
  div < term

instance
  nat :: div

consts
  div  :: ['a::div, 'a]  => 'a          (infixl 70)
  mod  :: ['a::div, 'a]  => 'a          (infixl 70)
  dvd  :: ['a::times, 'a] => bool       (infixl 70) 


(*Remainder and quotient are defined here by algorithms and later proved to
  satisfy the traditional definition (theorem mod_div_equality)
*)
defs

  mod_def   "m mod n == wfrec (trancl pred_nat)
                          (%f j. if j<n | n=0 then j else f (j-n)) m"

  div_def   "m div n == wfrec (trancl pred_nat) 
                          (%f j. if j<n | n=0 then 0 else Suc (f (j-n))) m"

(*The definition of dvd is polymorphic!*)
  dvd_def   "m dvd n == EX k. n = m*k"

end
