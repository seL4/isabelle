(*  Title:      HOLCF/One.thy
    ID:         $Id$
    Author:     Oscar Slotosch
*)

One = Lift +

types one = unit lift

constdefs
  ONE :: "one"
  "ONE == Def ()"

translations
  "one" <= (type) "unit lift" 

end
