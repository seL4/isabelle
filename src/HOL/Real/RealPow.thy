(*  Title       : HOL/Real/RealPow.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Description : Natural powers theory

*)

theory RealPow = RealAbs:

(*belongs to theory RealAbs*)
lemmas [arith_split] = abs_split


instance real :: power
  by intro_classes

primrec (realpow)
     realpow_0:   "r ^ 0       = #1"
     realpow_Suc: "r ^ (Suc n) = (r::real) * (r ^ n)"

end
