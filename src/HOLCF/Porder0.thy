(*  Title:      HOLCF/Porder0.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Definition of class porder (partial order)

*)

Porder0 = Nat +

(* first the global constant for HOLCF type classes *)
consts
  "less"        :: "['a,'a] => bool"

axclass po < term
        (* class axioms: *)
ax_refl_less       "less x x"        
ax_antisym_less    "[|less x y; less y x |] ==> x = y"    
ax_trans_less      "[|less x y; less y z |] ==> less x z"
 
	(* characteristic constant << on po *)
consts
  "<<"          :: "['a,'a::po] => bool"        (infixl 55)

syntax (symbols)
  "op <<"       :: "['a,'a::po] => bool"        (infixl "\\<sqsubseteq>" 55)

defs
po_def             "(op <<) == less"
end 


