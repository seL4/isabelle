(*  Title:      HOL/IOA/ABP/Correctness.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Olaf Mueller
    Copyright   1994  TU Muenchen

The main correctness proof: System_fin implements System
*)

Correctness = Solve + Env + Impl + Impl_finite + 

consts

reduce :: "'a list => 'a list"

primrec
  reduce List.list  
  reduce_Nil  "reduce [] = []"
  reduce_Cons "reduce(x#xs) =   \
\	         (case xs of   \
\	             [] => [x]   \
\	       |   y#ys => (if (x=y)   \
\	                      then reduce xs   \
\	                      else (x#(reduce xs))))"

end


  