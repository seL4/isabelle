(*  Title: 	HOLCF/cfun2.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance ->::(pcpo,pcpo)po

*)

Cfun2 = Cfun1 + 

(* Witness for the above arity axiom is cfun1.ML *)
arities "->" :: (pcpo,pcpo)po

consts	
	UU_cfun  :: "'a->'b"

rules

(* instance of << for type ['a -> 'b]  *)

inst_cfun_po	"((op <<)::['a->'b,'a->'b]=>bool) = less_cfun"

defs
(* The least element in type 'a->'b *)

UU_cfun_def	"UU_cfun == fabs(% x.UU)"

end

