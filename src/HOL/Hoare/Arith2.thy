(*  Title:      HOL/Hoare/Arith2.thy
    ID:         $Id$
    Author:     Norbert Galm
    Copyright   1995 TUM

More arithmetic.
*)

Arith2 = Arith +

consts
  divides :: [nat, nat] => bool                 (infixl 70)
  cd      :: [nat, nat, nat] => bool
  gcd     :: [nat, nat] => nat

  pow     :: [nat, nat] => nat                  (infixl 75)
  fac     :: nat => nat

defs
  divides_def   "x divides n == 0<n & 0<x & (n mod x) = 0"
  cd_def        "cd x m n  == x divides m & x divides n"
  gcd_def       "gcd m n     == @x.(cd x m n) & (!y.(cd y m n) --> y<=x)"

  pow_def       "m pow n     == nat_rec n (Suc 0) (%u v.m*v)"
  fac_def       "fac m       == nat_rec m (Suc 0) (%u v.(Suc u)*v)"

end
