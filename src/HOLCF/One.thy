(*  Title:      HOLCF/One.thy
    ID:         $Id$
    Author:     Oscar Slotosch
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

One = Lift +

types one = unit lift

constdefs
  ONE :: "one"
  "ONE == Def ()"

translations
  "one" <= (type) "unit lift" 

end
