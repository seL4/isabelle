(*  Title: 	HOLCF/ssum2.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance ++::(pcpo,pcpo)po
*)

Ssum2 = Ssum1 + 

arities "++" :: (pcpo,pcpo)po
(* Witness for the above arity axiom is ssum1.ML *)

rules

(* instance of << for type ['a ++ 'b]  *)

inst_ssum_po	"((op <<)::['a ++ 'b,'a ++ 'b]=>bool) = less_ssum"

end



