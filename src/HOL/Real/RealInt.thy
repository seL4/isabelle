(*  Title:       RealInt.thy
    ID:         $Id$
    Author:      Jacques D. Fleuriot
    Copyright:   1999 University of Edinburgh
    Description: Embedding the integers in the reals
*)

RealInt = RealOrd +

constdefs 
   real_of_int :: int => real
   "real_of_int z == Abs_real(UN (i,j): Rep_Integ z. realrel ```
                     {(preal_of_prat(prat_of_pnat(pnat_of_nat i)),
                       preal_of_prat(prat_of_pnat(pnat_of_nat j)))})"


end
