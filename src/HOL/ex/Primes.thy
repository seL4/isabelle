(*  Title:      HOL/ex/Primes.thy
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge

The "divides" relation, the Greatest Common Divisor and Euclid's algorithm
*)

Primes = Arith + WF_Rel +
consts
  dvd     :: [nat,nat]=>bool              (infixl 70) 
  is_gcd  :: [nat,nat,nat]=>bool          (*gcd as a relation*)
  gcd     :: "nat*nat=>nat"               (*Euclid's algorithm *)
  coprime :: [nat,nat]=>bool
  prime   :: nat=>bool
  
recdef gcd "measure ((%(x,y).y) ::nat*nat=>nat)"
    "gcd (m, n) = (if n=0 then m else gcd(n, m mod n))"

defs
  dvd_def     "m dvd n == EX k. n = m*k"

  is_gcd_def  "is_gcd p m n == p dvd m  &  p dvd n  &
                               (ALL d. d dvd m & d dvd n --> d dvd p)"

  coprime_def "coprime m n == gcd(m,n) = 1"

  prime_def   "prime(n) == (1<n) & (ALL m. 1<m & m<n --> ~(m dvd n))"

end
