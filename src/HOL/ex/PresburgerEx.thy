(*  Title:      HOL/ex/PresburgerEx.thy
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Some examples for Presburger Arithmetic
*)

theory PresburgerEx = Main:

theorem "(ALL (y::int). (3 dvd y)) ==> ALL (x::int). b < x --> a <= x"
  by presburger

theorem "!! (y::int) (z::int) (n::int). 3 dvd z ==> 2 dvd (y::int) ==>
  (EX (x::int).  2*x =  y) & (EX (k::int). 3*k = z)"
  by presburger

theorem "!! (y::int) (z::int) n. Suc(n::nat) < 6 ==>  3 dvd z ==>
  2 dvd (y::int) ==> (EX (x::int).  2*x =  y) & (EX (k::int). 3*k = z)"
  by presburger

theorem "ALL (x::nat). EX (y::nat). (0::nat) <= 5 --> y = 5 + x ";
  by presburger

theorem "ALL (x::nat). EX (y::nat). y = 5 + x | x div 6 + 1= 2";
  by presburger

theorem "EX (x::int). 0 < x" by presburger

theorem "ALL (x::int) y. x < y --> 2 * x + 1 < 2 * y" by presburger
 
theorem "ALL (x::int) y. ~(2 * x + 1 = 2 * y)" by presburger
 
theorem
   "EX (x::int) y. 0 < x  & 0 <= y  & 3 * x - 5 * y = 1" by presburger

theorem "~ (EX (x::int) (y::int) (z::int). 4*x + (-6::int)*y = 1)"
  by presburger

theorem "ALL (x::int). b < x --> a <= x"
  apply (presburger no_quantify)
  oops

theorem "ALL (x::int). b < x --> a <= x"
  apply (presburger no_quantify)
  oops

theorem "~ (EX (x::int). False)"
  by presburger

theorem "ALL (x::int). (a::int) < 3 * x --> b < 3 * x"
  apply (presburger no_quantify)
  oops

theorem "ALL (x::int). (2 dvd x) --> (EX (y::int). x = 2*y)" by presburger 

theorem "ALL (x::int). (2 dvd x) --> (EX (y::int). x = 2*y)" by presburger 

theorem "ALL (x::int). (2 dvd x) = (EX (y::int). x = 2*y)" by presburger 
  
theorem "ALL (x::int). ((2 dvd x) = (ALL (y::int). ~(x = 2*y + 1)))" by presburger 

theorem "ALL (x::int). ((2 dvd x) = (ALL (y::int). ~(x = 2*y + 1)))" by presburger 

theorem "~ (ALL (x::int). ((2 dvd x) = (ALL (y::int). ~(x = 2*y+1))| (EX (q::int) (u::int) i. 3*i + 2*q - u < 17) --> 0 < x | ((~ 3 dvd x) &(x + 8 = 0))))"
  by presburger
 
theorem 
   "~ (ALL (i::int). 4 <= i --> (EX (x::int) y. 0 <= x & 0 <= y & 3 * x + 5 * y = i))"
  by presburger

theorem
    "ALL (i::int). 8 <= i --> (EX (x::int) y. 0 <= x & 0 <= y & 3 * x + 5 * y = i)" by presburger
   
theorem
   "EX (j::int). (ALL (i::int). j <= i --> (EX (x::int) y. 0 <= x & 0 <= y & 3 * x + 5 * y = i))" by presburger

theorem
   "~ (ALL j (i::int). j <= i --> (EX (x::int) y. 0 <= x & 0 <= y & 3 * x + 5 * y = i))"
  by presburger

theorem "(EX m::nat. n = 2 * m) --> (n + 1) div 2 = n div 2" by presburger

theorem "(EX m::int. n = 2 * m) --> (n + 1) div 2 = n div 2" by presburger

end