(*  Title:      HOLCF/Lift2.thy
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1996 Technische Universitaet Muenchen

Class Instance lift::(term)po
*)

Lift2 = Lift1 + 

instance "lift" :: (term)po (refl_less_lift,antisym_less_lift,trans_less_lift)

end


