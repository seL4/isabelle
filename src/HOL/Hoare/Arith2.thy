(*  Title:      HOL/Hoare/Arith2.thy
    ID:         $Id$
    Author:     Norbert Galm
    Copyright   1995 TUM

More arithmetic.  Much of this duplicates ex/Primes.
*)

Arith2 = Divides +

constdefs
  cd      :: [nat, nat, nat] => bool
  "cd x m n  == x dvd m & x dvd n"

  gcd     :: [nat, nat] => nat
  "gcd m n     == @x.(cd x m n) & (!y.(cd y m n) --> y<=x)"

  pow     :: [nat, nat] => nat                              (infixl 75)
  "m pow n     == nat_rec (Suc 0) (%u v. m*v) n"

  fac     :: nat => nat
  "fac m       == nat_rec (Suc 0) (%u v.(Suc u)*v) m"

end
