(*  Title:      HOLCF/Lift2.thy
    ID:         $Id$
    Author:     Olaf Mueller, Robert Sandner
    Copyright   1996 Technische Universitaet Muenchen

Class Instance lift::(term)po
*)

Lift2 = Lift1 + 

default term

arities "lift" :: (term)po

rules

 inst_lift_po   "((op <<)::['a lift,'a lift]=>bool) = less_lift"

end

