(*  Title:      HOLCF/Lift1.thy
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1996 Technische Universitaet Muenchen

Lifting types of class term to flat pcpo's
*)

Lift1 = ccc1 + 

default term

datatype 'a lift = Undef | Def 'a

defs 
 
 less_lift_def  "less x y == (x=y | x=Undef)"

end
