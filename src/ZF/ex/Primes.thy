(*  Title:      ZF/ex/Primes.thy
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge

The "divides" relation, the greatest common divisor and Euclid's algorithm
*)

Primes = Main +
consts
  dvd     :: [i,i]=>o              (infixl 50) 
  is_gcd  :: [i,i,i]=>o            (* great common divisor *)
  gcd     :: [i,i]=>i              (* gcd by Euclid's algorithm *)
  
defs
  dvd_def     "m dvd n == m \\<in> nat & n \\<in> nat & (\\<exists>k \\<in> nat. n = m#*k)"

  is_gcd_def  "is_gcd(p,m,n) == ((p dvd m) & (p dvd n))   &
               (\\<forall>d\\<in>nat. (d dvd m) & (d dvd n) --> d dvd p)"

  gcd_def     "gcd(m,n) ==   
               transrec(natify(n),
			%n f. \\<lambda>m \\<in> nat.
			        if n=0 then m else f`(m mod n)`n) ` natify(m)"

constdefs
  coprime :: [i,i]=>o              (* coprime relation *)
    "coprime(m,n) == gcd(m,n) = 1"
  
  prime   :: i                     (* set of prime numbers *)
   "prime == {p \\<in> nat. 1<p & (\\<forall>m \\<in> nat. m dvd p --> m=1 | m=p)}"

end
