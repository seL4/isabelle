(*  Title:      HOLCF/porder0.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Definition of class porder (partial order)

The prototype theory for this class is void.thy 

*)

Porder0 = Void +

(* Introduction of new class. The witness is type void. *)

classes po < term

(* default type is still term ! *)
(* void is the prototype in po *)

arities void :: po

consts  "<<"    ::      "['a,'a::po] => bool"   (infixl 55)

rules

(* class axioms: justification is theory Void *)

refl_less       "x << x"        
                                (* witness refl_less_void    *)

antisym_less    "[|x<<y ; y<<x |] ==> x = y"    
                                (* witness antisym_less_void *)

trans_less      "[|x<<y ; y<<z |] ==> x<<z"
                                (* witness trans_less_void   *)

(* instance of << for the prototype void *)

inst_void_po    "((op <<)::[void,void]=>bool) = less_void"

(* start 8bit 1 *)
(* end 8bit 1 *)

end 





