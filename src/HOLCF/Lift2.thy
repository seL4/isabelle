(*  Title:      HOLCF/lift2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance u::(pcpo)po

*)

Lift2 = Lift1 + 

(* Witness for the above arity axiom is lift1.ML *)

arities "u" :: (pcpo)po

rules

(* instance of << for type ('a)u  *)

inst_lift_po    "((op <<)::[('a)u,('a)u]=>bool) = less_lift"

end



