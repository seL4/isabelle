(*  Title:      HOL/AxClasses/Tutorial/Product.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Define a 'syntactic' class "product" that is logically equivalent to
"term".
*)

Product = HOL +

axclass
  product < term

consts
  "<*>" :: "['a::product, 'a] => 'a"      (infixl 70)

end
