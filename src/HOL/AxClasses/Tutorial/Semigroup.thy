(*  Title:      HOL/AxClasses/Tutorial/Semigroup.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Define class "semigroup".
*)

Semigroup = HOL +

consts
  "<*>"         :: "['a, 'a] => 'a"             (infixl 70)

axclass
  semigroup < term
  assoc         "(x <*> y) <*> z = x <*> (y <*> z)"

end
