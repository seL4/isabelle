(*  Title       : NSPrimes.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2002 University of Edinburgh
    Description : The nonstandard primes as an extension of 
                  the prime numbers

These can be used to derive an alternative proof of the infinitude of primes by
considering a property of nonstandard sets.
*)

NSPrimes = Factorization + Complex_Main +

consts
  hdvd  :: [hypnat, hypnat] => bool       (infixl 50) 
  
defs
  hdvd_def "(M::hypnat) hdvd N ==
	           EX X Y. X: Rep_hypnat(M) & Y: Rep_hypnat(N) & 
                               {n::nat. X n dvd Y n} : FreeUltrafilterNat"

constdefs
  starprime :: hypnat set
  "starprime == ( *sNat* prime)"

constdefs
  choicefun :: 'a set => 'a
  "choicefun E == (@x. EX X: Pow(E) -{{}}. x : X)" 

consts injf_max :: "nat => ('a::{order} set) => 'a"  
primrec
  injf_max_zero "injf_max 0 E = choicefun E"
  injf_max_Suc  "injf_max (Suc n) E = choicefun({e. e : E & injf_max n E < e})"

end


