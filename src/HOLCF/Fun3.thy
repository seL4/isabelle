(*  Title: 	HOLCF/fun3.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class instance of  => (fun) for class pcpo

*)

Fun3 = Fun2 +

(* default class is still term *)

arities fun  :: (term,pcpo)pcpo		(* Witness fun2.ML *)

rules 

inst_fun_pcpo	"(UU::'a=>'b::pcpo) = UU_fun"

end



