(*  Title:      HOL/Hoare/Arith2.thy
    ID:         $Id$
    Author:     Norbert Galm
    Copyright   1995 TUM

More arithmetic.  Much of this duplicates ex/Primes.
*)

Arith2 = Power +

constdefs
  cd      :: [nat, nat, nat] => bool
  "cd x m n  == x dvd m & x dvd n"

  gcd     :: [nat, nat] => nat
  "gcd m n     == @x.(cd x m n) & (!y.(cd y m n) --> y<=x)"

consts fac     :: nat => nat
primrec fac nat
"fac 0 = Suc 0"
"fac(Suc n) = (Suc n)*fac(n)"

end
