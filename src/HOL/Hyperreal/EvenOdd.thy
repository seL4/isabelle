(*  Title       : EvenOdd.thy
    Author      : Jacques D. Fleuriot  
    Copyright   : 1999  University of Edinburgh
    Description : Even and odd numbers defined 
*)

EvenOdd = NthRoot +  

consts even :: "nat => bool"
primrec 
   even_0   "even 0 = True"
   even_Suc "even (Suc n) = (~ (even n))"    

consts odd :: "nat => bool"
primrec 
   odd_0   "odd 0 = False"
   odd_Suc "odd (Suc n) = (~ (odd n))"    

end

