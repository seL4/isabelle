(*  Title:      HOLCF/Pcpo.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

introduction of the classes cpo and pcpo 
*)
Pcpo = Porder +

(* The class cpo of chain complete partial orders *)
(* ********************************************** *)
axclass cpo < po
        (* class axiom: *)
  cpo   "chain S ==> ? x. range S <<| x" 

(* The class pcpo of pointed cpos *)
(* ****************************** *)
axclass pcpo < cpo

  least         "? x.!y. x<<y"

consts
  UU            :: "'a::pcpo"        

syntax (xsymbols)
  UU            :: "'a::pcpo"                           ("\\<bottom>")

defs
  UU_def        "UU == @x.!y. x<<y"       

(* further useful classes for HOLCF domains *)

axclass chfin<cpo

chfin 	"!Y. chain Y-->(? n. max_in_chain n Y)"

axclass flat<pcpo

ax_flat	 	"! x y. x << y --> (x = UU) | (x=y)"

end 
