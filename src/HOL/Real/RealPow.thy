(*  Title       : RealPow.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Description : Natural powers theory

*)

RealPow = WF_Rel + RealAbs + 

instance real :: {power}

primrec
     realpow_0   "r ^ 0       = 1r"
     realpow_Suc "r ^ (Suc n) = (r::real) * (r ^ n)"

end
