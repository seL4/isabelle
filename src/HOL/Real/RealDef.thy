(*  Title       : Real/RealDef.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The reals
*) 

RealDef = PReal +

constdefs
  realrel   ::  "((preal * preal) * (preal * preal)) set"
  "realrel == {p. ? x1 y1 x2 y2. p = ((x1,y1),(x2,y2)) & x1+y2 = x2+y1}" 

typedef real = "{x::(preal*preal).True}/realrel"          (Equiv.quotient_def)


instance
   real  :: {ord, plus, times, minus}

consts 

  "0r"       :: real               ("0r")   
  "1r"       :: real               ("1r")  

defs

  real_zero_def  
     "0r == Abs_real(realrel^^{(preal_of_prat(prat_of_pnat 1p),
                                preal_of_prat(prat_of_pnat 1p))})"
  real_one_def   
     "1r == Abs_real(realrel^^{(preal_of_prat(prat_of_pnat 1p) + 
            preal_of_prat(prat_of_pnat 1p),preal_of_prat(prat_of_pnat 1p))})"

  real_minus_def
    "- R ==  Abs_real(UN (x,y):Rep_real(R). realrel^^{(y,x)})"

  real_diff_def "x - y == x + (- y :: real)"

constdefs

  real_of_preal :: preal => real            
  "real_of_preal m     ==
           Abs_real(realrel^^{(m+preal_of_prat(prat_of_pnat 1p),
                               preal_of_prat(prat_of_pnat 1p))})"

  rinv       :: real => real
  "rinv(R)   == (@S. R ~= 0r & S*R = 1r)"

  real_of_posnat :: nat => real             
  "real_of_posnat n == real_of_preal(preal_of_prat(prat_of_pnat(pnat_of_nat n)))"

  real_of_nat :: nat => real          
  "real_of_nat n    == real_of_posnat n + (-1r)"

defs

  real_add_def  
  "P + Q == Abs_real(UN p1:Rep_real(P). UN p2:Rep_real(Q).
                split(%x1 y1. split(%x2 y2. realrel^^{(x1+x2, y1+y2)}) p2) p1)"
  
  real_mult_def  
  "P * Q == Abs_real(UN p1:Rep_real(P). UN p2:Rep_real(Q).
                split(%x1 y1. split(%x2 y2. realrel^^{(x1*x2+y1*y2,x1*y2+x2*y1)}) p2) p1)"

  real_less_def
  "P < Q == EX x1 y1 x2 y2. x1 + y2 < x2 + y1 & 
                                   (x1,y1):Rep_real(P) &
                                   (x2,y2):Rep_real(Q)" 
  real_le_def
  "P <= (Q::real) == ~(Q < P)"

end
