(*  Title       : Fact.thy 
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Factorial function
*)

Fact = NatStar + 

consts fact :: nat => nat 
primrec 
   fact_0     "fact 0 = 1"
   fact_Suc   "fact (Suc n) = (Suc n) * fact n" 

end