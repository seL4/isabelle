(*  Title:      HOLCF/One.thy
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen
*)

One = Lift +

types one = "unit lift"

consts
	ONE             :: "one"

translations
	     "one" == (type) "unit lift" 

rules
  ONE_def     "ONE == Def()"
end


