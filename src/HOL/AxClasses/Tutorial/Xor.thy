(*  Title:      HOL/AxClasses/Tutorial/Xor.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Define overloaded constants "<*>", "inv", "1" on type "bool".
*)

Xor = Group +

defs
  prod_bool_def "x <*> y == x ~= (y::bool)"
  inv_bool_def  "inv x   == x::bool"
  unit_bool_def "1       == False"

end
