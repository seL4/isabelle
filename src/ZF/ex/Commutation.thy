(*  Title:      HOL/Lambda/Commutation.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Sidi Ould Ehmety
    Copyright   1995  TU Muenchen

Commutation theory for proving the Church Rosser theorem
	ported from Isabelle/HOL  by Sidi Ould Ehmety
*)

Commutation = Main +    

constdefs
  square  :: [i, i, i, i] => o
   "square(r,s,t,u) ==
   (\\<forall>a b. <a,b>:r --> (\\<forall>c. <a, c>:s
                          --> (\\<exists>x. <b,x>:t & <c,x>:u)))"

   commute :: [i, i] => o       
   "commute(r,s) == square(r,s,s,r)"

  diamond :: i=>o
  "diamond(r)   == commute(r, r)"

  strip :: i=>o  
  "strip(r) == commute(r^*, r)"

  Church_Rosser :: i => o     
  "Church_Rosser(r) == (\\<forall>x y. <x,y>: (r Un converse(r))^* -->
			(\\<exists>z. <x,z>:r^* & <y,z>:r^*))"
  confluent :: i=>o    
  "confluent(r) == diamond(r^*)"
end          
