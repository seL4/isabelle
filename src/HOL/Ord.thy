(*  Title:      HOL/Ord.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The type class for ordered types    (* FIXME improve comment *)
*)

Ord = HOL +

axclass
  ord < term

consts
  "op <"        :: ['a::ord, 'a] => bool             ("(_/ < _)"  [50,51] 50)
  "op <="       :: ['a::ord, 'a] => bool             ("(_/ <= _)" [50,51] 50)
  mono          :: ['a::ord => 'b::ord] => bool       (*monotonicity*)
  min, max      :: ['a::ord, 'a] => 'a

defs
  mono_def      "mono(f) == (!A B. A <= B --> f(A) <= f(B))"
  min_def       "min a b == (if a <= b then a else b)"
  max_def       "max a b == (if a <= b then b else a)"

end

