(*  Title:      HOLCF/Up2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance u::(pcpo)po

*)

Up2 = Up1 + 

(* Witness for the above arity axiom is up1.ML *)

arities "u" :: (pcpo)po

rules

(* instance of << for type ('a)u  *)

inst_up_po    "((op <<)::[('a)u,('a)u]=>bool) = less_up"

end



