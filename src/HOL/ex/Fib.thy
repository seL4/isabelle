(*  Title:      ex/Fib
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Fibonacci numbers and other simple examples of recursive definitions
	(the TFL package)
*)

Fib = WF_Rel + Divides +

consts fib  :: "nat => nat"
recdef fib "less_than"
    "fib 0 = 0"
    "fib 1 = 1"
    "fib (Suc(Suc x)) = (fib x + fib (Suc x))"

end
