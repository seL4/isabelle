(*  Title:      HOLCF/Lift1.thy
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1996 Technische Universitaet Muenchen

Lifting types of class term to flat pcpo's
*)

Lift1 = Cprod3 + 

default term

datatype 'a lift = Undef | Def 'a

instance lift :: (term)sq_ord
defs 
 
 less_lift_def  "x << y == (x=y | x=Undef)"

end
