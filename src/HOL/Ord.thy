(*  Title:      HOL/Ord.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Type classes for order signatures and orders.
*)

Ord = HOL +

axclass
  ord < term

consts
  "op <"        :: ['a::ord, 'a] => bool             ("(_/ < _)"  [50, 51] 50)
  "op <="       :: ['a::ord, 'a] => bool             ("(_/ <= _)" [50, 51] 50)
  mono          :: ['a::ord => 'b::ord] => bool       (*monotonicity*)
  min, max      :: ['a::ord, 'a] => 'a

  Least         :: ('a::ord=>bool) => 'a             (binder "LEAST " 10)

syntax
  "op <"        :: ['a::ord, 'a] => bool             ("op <")
  "op <="       :: ['a::ord, 'a] => bool             ("op <=")

syntax (symbols)
  "op <="       :: ['a::ord, 'a] => bool             ("(_/ \\<le> _)"  [50, 51] 50)
  "op <="       :: ['a::ord, 'a] => bool             ("op \\<le>")

defs
  mono_def      "mono(f) == (!A B. A <= B --> f(A) <= f(B))"
  min_def       "min a b == (if a <= b then a else b)"
  max_def       "max a b == (if a <= b then b else a)"
  Least_def     "Least P == @x. P(x) & (ALL y. P(y) --> x <= y)"


axclass order < ord
  order_refl    "x <= x"
  order_trans   "[| x <= y; y <= z |] ==> x <= z"
  order_antisym "[| x <= y; y <= x |] ==> x = y"
  order_less_le "x < y = (x <= y & x ~= y)"

end
