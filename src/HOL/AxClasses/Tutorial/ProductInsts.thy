(*  Title:      HOL/AxClasses/Tutorial/ProductInsts.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Instantiate the 'syntactic' class "product", then define "<*>" on type
"bool".

Note: This may look like Haskell-instance, but is not quite the same!
*)

ProductInsts = Product +

instance
  bool :: product

defs
  prod_bool_def "x <*> y  == x & y::bool"

end
