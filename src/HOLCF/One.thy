(*  Title:      HOLCF/One.thy
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen
*)

One = Lift +

types one = unit lift

constdefs
  ONE :: "one"
  "ONE == Def ()"

translations
  "one" <= (type) "unit lift" 

end
