(*  Title:      Sigs.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

Sigs = HOL +

axclass
  inverse < term

axclass
  one < term

consts
  inverse :: 'a::inverse => 'a
  "1"     :: 'a::one                    ("1")

end
