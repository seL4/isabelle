(*  Title:      HOL/AxClasses/Tutorial/Xor.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Define overloaded constants "<*>", "inverse", "1" on type "bool".
*)

Xor = Group +

defs
  prod_bool_def     "x <*> y   == x ~= (y::bool)"
  inverse_bool_def  "inverse x == x::bool"
  unit_bool_def     "1         == False"

end
