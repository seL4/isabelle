(*  Title:      HOL/ex/Natsum.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Lawrence C Paulson

A summation operator. sum(f,n+1) is the sum of all f(i), i=0...n.

Note: n is a natural number but the sum is an integer,
                            and f maps integers to integers
*)

NatSum = Main +

consts sum     :: [i=>i, i] => i
primrec 
  "sum (f,0) = #0"
  "sum (f, succ(n)) = f($#n) $+ sum(f,n)"

end