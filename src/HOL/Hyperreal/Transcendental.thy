(*  Title       : Transcendental.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998,1999 University of Cambridge
                  1999 University of Edinburgh
    Description : Power Series, transcendental functions etc.
*)

Transcendental = NthRoot + Fact + HSeries + EvenOdd + Lim + 

constdefs
    root :: [nat,real] => real
    "root n x == (@u. ((0::real) < x --> 0 < u) & (u ^ n = x))"

    sqrt :: real => real
    "sqrt x == root 2 x"

    exp :: real => real
    "exp x == suminf(%n. inverse(real (fact n)) * (x ^ n))"

    sin :: real => real
    "sin x == suminf(%n. (if even(n) then 0 else
             ((- 1) ^ ((n - Suc 0) div 2))/(real (fact n))) * x ^ n)"
 
    diffs :: (nat => real) => nat => real
    "diffs c == (%n. real (Suc n) * c(Suc n))"

    cos :: real => real
    "cos x == suminf(%n. (if even(n) then ((- 1) ^ (n div 2))/(real (fact n)) 
                          else 0) * x ^ n)"
  
    ln :: real => real
    "ln x == (@u. exp u = x)"

    pi :: real
    "pi == 2 * (@x. 0 <= (x::real) & x <= 2 & cos x = 0)"

    tan :: real => real
    "tan x == (sin x)/(cos x)"

    arcsin :: real => real
    "arcsin y == (@x. -(pi/2) <= x & x <= pi/2 & sin x = y)"

    arcos :: real => real
    "arcos y == (@x. 0 <= x & x <= pi & cos x = y)"
     
    arctan :: real => real
    "arctan y == (@x. -(pi/2) < x & x < pi/2 & tan x = y)"
  
end 
