(*  Title: 	HOLCF/sprod2.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance **::(pcpo,pcpo)po
*)

Sprod2 = Sprod1 + 

arities "**" :: (pcpo,pcpo)po

(* Witness for the above arity axiom is sprod1.ML *)

rules

(* instance of << for type ['a ** 'b]  *)

inst_sprod_po	"((op <<)::['a ** 'b,'a ** 'b]=>bool) = less_sprod"

end



