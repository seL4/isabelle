(*  Title:      Sigs.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

Sigs = HOL +

axclass
  inv < term

axclass
  one < term

consts
  "inv" :: "'a::inv => 'a"
  "1"   :: "'a::one"                    ("1")

end
