(*  Title       : PRat.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The positive rationals
*) 

PRat = PNat + Equiv +

constdefs
    ratrel   ::  "((pnat * pnat) * (pnat * pnat)) set"
    "ratrel  ==  {p. ? x1 y1 x2 y2. p=((x1::pnat,y1),(x2,y2)) & x1*y2 = x2*y1}" 

typedef prat = "{x::(pnat*pnat).True}/ratrel"          (Equiv.quotient_def)

instance
   prat  :: {ord,plus,times}


constdefs

  prat_of_pnat :: pnat => prat           
  "prat_of_pnat m     == Abs_prat(ratrel^^{(m,Abs_pnat 1)})"

  qinv      :: prat => prat
  "qinv(Q)  == Abs_prat(UN (x,y):Rep_prat(Q). ratrel^^{(y,x)})" 

defs

  prat_add_def  
  "P + Q == Abs_prat(UN p1:Rep_prat(P). UN p2:Rep_prat(Q).
                split(%x1 y1. split(%x2 y2. ratrel^^{(x1*y2 + x2*y1, y1*y2)}) p2) p1)"

  prat_mult_def  
  "P * Q == Abs_prat(UN p1:Rep_prat(P). UN p2:Rep_prat(Q).
                split(%x1 y1. split(%x2 y2. ratrel^^{(x1*x2, y1*y2)}) p2) p1)"
 
  (*** Gleason p. 119 ***)
  prat_less_def
  "P < (Q::prat) == ? T. P + T = Q"

  prat_le_def
  "P <= (Q::prat) == ~(Q < P)" 

end
  




