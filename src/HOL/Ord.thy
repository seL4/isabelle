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
  "<", "<="     :: "['a::ord, 'a] => bool"              (infixl 50)
  mono          :: "['a::ord => 'b::ord] => bool"       (*monotonicity*)
  min, max      :: "['a::ord, 'a] => 'a"

defs
  mono_def      "mono(f) == (!A B. A <= B --> f(A) <= f(B))"
  min_def       "min a b == if (a <= b) a b"
  max_def       "max a b == if (a <= b) b a"

end

