(*  Title:      HOLCF/fun2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance =>::(term,po)po
Definiton of least element
*)

Fun2 = Fun1 + 

(* default class is still term !*)

(* Witness for the above arity axiom is fun1.ML *)

arities fun :: (term,po)po

consts  
        UU_fun  :: "'a::term => 'b::pcpo"

rules

(* instance of << for type ['a::term => 'b::po]  *)

inst_fun_po     "((op <<)::['a=>'b::po,'a=>'b::po ]=>bool) = less_fun"

defs

(* The least element in type 'a::term => 'b::pcpo *)

UU_fun_def      "UU_fun == (% x.UU)"

end








