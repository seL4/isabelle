(*  Title       : PRat.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The positive rationals
*) 

PRat = PNat +

constdefs
    ratrel   ::  "((pnat * pnat) * (pnat * pnat)) set"
    "ratrel  ==  {p. ? x1 y1 x2 y2. p=((x1::pnat,y1),(x2,y2)) & x1*y2 = x2*y1}" 

typedef prat = "UNIV//ratrel"          (Equiv.quotient_def)

instance
   prat  :: {ord,plus,times}


constdefs

  prat_of_pnat :: pnat => prat           
  "prat_of_pnat m == Abs_prat(ratrel```{(m,Abs_pnat 1)})"

  qinv      :: prat => prat
  "qinv(Q)  == Abs_prat(UN (x,y):Rep_prat(Q). ratrel```{(y,x)})" 

defs

  prat_add_def  
  "P + Q == Abs_prat(UN (x1,y1):Rep_prat(P). UN (x2,y2):Rep_prat(Q).
		     ratrel```{(x1*y2 + x2*y1, y1*y2)})"

  prat_mult_def  
  "P * Q == Abs_prat(UN (x1,y1):Rep_prat(P). UN (x2,y2):Rep_prat(Q).
		     ratrel```{(x1*x2, y1*y2)})"
 
  (*** Gleason p. 119 ***)
  prat_less_def
  "P < (Q::prat) == EX T. P + T = Q"

  prat_le_def
  "P <= (Q::prat) == ~(Q < P)" 

end
  




