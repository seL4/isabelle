(*  Title: 	ZF/ex/Brouwer.thy
    ID:         $ $
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition of the Brouwer ordinals -- demonstrates infinite branching
*)

Brouwer = InfDatatype +
consts
  brouwer :: "i"
 
datatype <= "Vfrom(0, csucc(nat))"
  "brouwer" = Zero | Suc ("b: brouwer") | Lim ("h: nat -> brouwer")
  monos	      "[Pi_mono]"
  type_intrs  "inf_datatype_intrs"

end
