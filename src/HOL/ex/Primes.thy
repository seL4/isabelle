(*  Title:      HOL/ex/Primes.thy
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge

The "divides" relation, the greatest common divisor and Euclid's algorithm
*)

Primes = Arith +
consts
  dvd     :: [nat,nat]=>bool              (infixl 70) 
  gcd     :: [nat,nat,nat]=>bool          (* great common divisor *)
  egcd    :: [nat,nat]=>nat               (* gcd by Euclid's algorithm *)
  coprime :: [nat,nat]=>bool              (* coprime definition *)
  prime   :: nat=>bool                    (* prime definition *)
  
defs
  dvd_def     "m dvd n == EX k. n = m*k"

  gcd_def     "gcd p m n == ((p dvd m) & (p dvd n))   &
               (ALL d. (d dvd m) & (d dvd n) --> d dvd p)"

  egcd_def    "egcd m n ==   
               wfrec (pred_nat^+)
                     (%f n m. if n=0 then m else f (m mod n) n) n m"

  coprime_def "coprime m n == egcd m n = 1"

  prime_def   "prime(n) == (1<n) & (ALL m. 1<m & m<n --> ~(m dvd n))"

end
