(*  Title:      HOL/Divides.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

The division operators div, mod and the divides relation "dvd"
*)

Divides = NatArith +

(*We use the same class for div and mod;
  moreover, dvd is defined whenever multiplication is*)
axclass
  div < type

instance  nat :: div
instance  nat :: plus_ac0 (add_commute,add_assoc,add_0)

consts
  div  :: ['a::div, 'a]  => 'a          (infixl 70)
  mod  :: ['a::div, 'a]  => 'a          (infixl 70)
  dvd  :: ['a::times, 'a] => bool       (infixl 50) 


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

(*This definition helps prove the harder properties of div and mod.
  It is copied from IntDiv.thy; should it be overloaded?*)
constdefs
  quorem :: "(nat*nat) * (nat*nat) => bool"
    "quorem == %((a,b), (q,r)).
                      a = b*q + r &
                      (if 0<b then 0<=r & r<b else b<r & r <=0)"

end
