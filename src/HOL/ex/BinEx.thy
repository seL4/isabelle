(*  Title:      HOL/ex/BinEx.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Definition of normal form for proving that binary arithmetic on
normalized operands yields normalized results.

Normal means no leading 0s on positive numbers and no leading 1s on negatives.
*)

BinEx = Main +

consts normal :: bin set
  
inductive "normal"
  intrs 

    Pls  "Pls: normal"

    Min  "Min: normal"

    BIT_F  "[| w: normal; w ~= Pls |] ==> w BIT False : normal"

    BIT_T  "[| w: normal; w ~= Min |] ==> w BIT True : normal"

end
