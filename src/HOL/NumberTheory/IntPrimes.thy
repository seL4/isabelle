(*  Title:	IntPrimes.thy
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge
*)

IntPrimes = Main + IntDiv + Primes +

consts
  xzgcda   :: "int*int*int*int*int*int*int*int => int*int*int"
  xzgcd    :: "[int,int] => int*int*int" 
  zprime   :: int set
  zcong    :: [int,int,int] => bool     ("(1[_ = _] '(mod _'))")
  
recdef xzgcda 
       "measure ((%(m,n,r',r,s',s,t',t).(nat r))
                 ::int*int*int*int*int*int*int*int=>nat)"
        simpset "simpset() addsimps [pos_mod_bound]"
       "xzgcda (m,n,r',r,s',s,t',t) = 
          (if r<=#0 then (r',s',t') else  
           xzgcda(m,n,r,r' mod r,s,s'-(r' div r)*s,t,t'-(r' div r)*t))"

constdefs
  zgcd     :: "int*int => int"              
      "zgcd == %(x,y). int (gcd(nat (abs x), nat (abs y)))"

defs
  xzgcd_def    "xzgcd m n == xzgcda (m,n,m,n,#1,#0,#0,#1)"

  zprime_def   "zprime == {p. #1<p & (ALL m. m dvd p --> m=#1 | m=p)}"

  zcong_def    "[a=b] (mod m) == m dvd (a-b)"

end
