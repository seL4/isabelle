(*  Title:      ZF/ex/Primes.thy
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge

The "divides" relation, the greatest common divisor and Euclid's algorithm
*)

Primes = Main +
consts
  dvd     :: [i,i]=>o              (infixl 70) 
  gcd     :: [i,i,i]=>o            (* great common divisor *)
  egcd    :: [i,i]=>i              (* gcd by Euclid's algorithm *)
  coprime :: [i,i]=>o              (* coprime definition *)
  prime   :: i=>o                  (* prime definition *)
  
defs
  dvd_def     "m dvd n == m \\<in> nat & n \\<in> nat & (\\<exists>k \\<in> nat. n = m#*k)"

  gcd_def     "gcd(p,m,n) == ((p dvd m) & (p dvd n))   &
               (\\<forall>d. (d dvd m) & (d dvd n) --> d dvd p)"

  egcd_def    "egcd(m,n) ==   
               transrec(n, %n f. \\<lambda>m \\<in> nat. if(n=0, m, f`(m mod n)`n)) ` m"

  coprime_def "coprime(m,n) == egcd(m,n) = 1"

  prime_def   "prime(n) == (1<n) & (\\<forall>m \\<in> nat. 1<m & m<n --> ~(m dvd n))"

end
