(*  Title:	IntPrimes.thy
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge
*)

IntPrimes = Main + IntDiv +

consts
  is_zgcd  :: [int,int,int] => bool         
  zgcd     :: "int*int => int"              
  xzgcda   :: "int*int*int*int*int*int*int*int => int*int*int"
  xzgcd    :: "[int,int] => int*int*int" 
  zprime   :: int set
  zcong    :: [int,int,int] => bool     ("(1[_ = _] '(mod _'))")
  
recdef zgcd "measure ((%(m,n).(nat n)) ::int*int=>nat)"
    simpset "simpset() addsimps [pos_mod_bound]"
    "zgcd (m, n) = (if n<=#0 then m else zgcd(n, m mod n))"

recdef xzgcda 
       "measure ((%(m,n,r',r,s',s,t',t).(nat r))
                 ::int*int*int*int*int*int*int*int=>nat)"
        simpset "simpset() addsimps [pos_mod_bound]"
       "xzgcda (m,n,r',r,s',s,t',t) = 
          (if r<=#0 then (r',s',t') else  
           xzgcda(m,n,r,r' mod r,s,s'-(r' div r)*s,t,t'-(r' div r)*t))"

defs
  xzgcd_def    "xzgcd m n == xzgcda (m,n,m,n,#1,#0,#0,#1)"

  is_zgcd_def  "is_zgcd p m n == #0 < p  &  p dvd m  &  p dvd n  &
                                 (ALL d. d dvd m & d dvd n --> d dvd p)"

  zprime_def   "zprime == {p. #1<p & (ALL m. m dvd p --> m=#1 | m=p)}"

  zcong_def    "[a=b] (mod m) == m dvd (a-b)"

end
