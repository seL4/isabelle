(*  Title:      HOL/Arith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Arithmetic operators + - and * (for div, mod and dvd, see Divides)
*)

Arith = Nat +

instance
  nat :: {plus, minus, times, power}

(* size of a datatype value; overloaded *)
consts size :: 'a => nat

primrec
  add_0    "0 + n = n"
  add_Suc  "Suc m + n = Suc(m + n)"

primrec
  diff_0   "m - 0 = m"
  diff_Suc "m - Suc n = (case m - n of 0 => 0 | Suc k => k)"

primrec
  mult_0   "0 * n = 0"
  mult_Suc "Suc m * n = n + (m * n)"

(*We overload the constant for all + types*)
consts sum_below :: "[nat=>'a, nat] => ('a::{zero,plus})"
primrec 
  sum_below_0    "sum_below f 0 = 0"
  sum_below_Suc  "sum_below f (Suc n) = f(n) + sum_below f n"

end
