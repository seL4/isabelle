(*  Title       : PNat.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The positive naturals
*) 


PNat = Main +

typedef
  pnat = "lfp(%X. {Suc 0} Un Suc`X)"   (lfp_def)

instance
   pnat :: {ord, plus, times}

consts

  pSuc       :: pnat => pnat
  "1p"       :: pnat                ("1p")

constdefs
  
  pnat_of_nat  :: nat => pnat           
  "pnat_of_nat n     == Abs_pnat(n + 1)"
 
defs

  pnat_one_def      
       "1p == Abs_pnat(Suc 0)"
  pnat_Suc_def      
       "pSuc == (%n. Abs_pnat(Suc(Rep_pnat(n))))"

  pnat_add_def
       "x + y == Abs_pnat(Rep_pnat(x) +  Rep_pnat(y))"

  pnat_mult_def
       "x * y == Abs_pnat(Rep_pnat(x) * Rep_pnat(y))"

  pnat_less_def
       "x < (y::pnat) == Rep_pnat(x) < Rep_pnat(y)"

  pnat_le_def
       "x <= (y::pnat) ==  ~(y < x)"

end
