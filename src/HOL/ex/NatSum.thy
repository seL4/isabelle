(*  Title: 	HOL/ex/natsum.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1994 TU Muenchen

A summation operator. sum(f,n+1) is the sum of all f(i), i=0...n.
*)

NatSum = Arith +
consts sum     :: "[nat=>nat, nat] => nat"
rules  sum_0      "sum f 0 = 0"
       sum_Suc    "sum f (Suc n) = f(n) + sum f n"
end
