(*  Title:      HOL/AxClasses/Tutorial/Sigs.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Some polymorphic constants for the 'signature' parts of axclasses.
*)

Sigs = HOL +

consts
  "<*>"         :: "['a, 'a] => 'a"             (infixl 70)
  inverse       :: "'a => 'a"
  "1"           :: "'a"                         ("1")

end
