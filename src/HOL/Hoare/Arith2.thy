(*  Title:      HOL/Hoare/Arith2.thy
    ID:         $Id$
    Author:     Norbert Galm
    Copyright   1995 TUM

More arithmetic.
*)

Arith2 = Arith +

constdefs
  divides :: [nat, nat] => bool                             (infixl 70)
  "x divides n == 0<n & 0<x & (n mod x) = 0"

  cd      :: [nat, nat, nat] => bool
  "cd x m n  == x divides m & x divides n"

  gcd     :: [nat, nat] => nat
  "gcd m n     == @x.(cd x m n) & (!y.(cd y m n) --> y<=x)"

  pow     :: [nat, nat] => nat                              (infixl 75)
  "m pow n     == nat_rec n (Suc 0) (%u v.m*v)"

  fac     :: nat => nat
  "fac m       == nat_rec m (Suc 0) (%u v.(Suc u)*v)"

end
