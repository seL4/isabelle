(*  Title:      HOLCF/Pcpo.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

introduction of the classes cpo and pcpo 
*)
Pcpo = Porder +

(* The class cpo of chain complete partial orders *)
(* ********************************************** *)
axclass cpo < po
        (* class axiom: *)
  cpo   "is_chain S ==> ? x. range(S) <<| (x::'a::po)" 

(* The class pcpo of pointed cpos *)
(* ****************************** *)
axclass pcpo < cpo

  least         "? x.!y.x<<y"

consts
  UU            :: "'a::pcpo"        

syntax (symbols)
  UU            :: "'a::pcpo"                           ("\\<bottom>")

defs
  UU_def        "UU == @x.!y.x<<y"       

(* further useful classes for HOLCF domains *)

axclass chfin<cpo

chfin 	"!Y.is_chain Y-->(? n.max_in_chain n Y)"

axclass flat<pcpo

ax_flat	 	"! x y.x << y --> (x = UU) | (x=y)"

end 
