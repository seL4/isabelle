(*  Title       : HRealAbs.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Absolute value function for the hyperreals
*) 

HRealAbs = HyperArith + RealArith + 

constdefs
  
  hypreal_of_nat :: nat => hypreal                   
  "hypreal_of_nat (n::nat) == hypreal_of_real (real n)"

end