(*  Title: 	HOLCF/cprod2.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance *::(pcpo,pcpo)po

*)

Cprod2 = Cprod1 + 

(* Witness for the above arity axiom is cprod1.ML *)

arities "*" :: (pcpo,pcpo)po

rules

(* instance of << for type ['a * 'b]  *)

inst_cprod_po	"(op <<)::['a * 'b,'a * 'b]=>bool = less_cprod"

end



