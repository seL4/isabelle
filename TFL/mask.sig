(*  Title:      TFL/mask
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

signature Mask_sig =
sig
 datatype 'a binding = |-> of ('a * 'a)  (* infix 7 |->; *)

 type mask
 val ERR : mask

end
