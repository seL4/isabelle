(*  Title: 	ZF/ex/Brouwer.thy
    ID:         $ $
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Infinite branching datatype definitions
  (1) the Brouwer ordinals
  (2) the Martin-Löf wellordering type
*)

Brouwer = InfDatatype +
consts
  brouwer :: "i"
  Well    :: "[i,i=>i]=>i"
 
datatype <= "Vfrom(0, csucc(nat))"
  "brouwer" = Zero | Suc ("b: brouwer") | Lim ("h: nat -> brouwer")
  monos	      "[Pi_mono]"
  type_intrs  "inf_datatype_intrs"

(*The union with nat ensures that the cardinal is infinite*)
datatype <= "Vfrom(A Un (UN x:A. B(x)), csucc(nat Un |UN x:A. B(x)|))"
  "Well(A,B)" = Sup ("a:A", "f: B(a) -> Well(A,B)")
  monos	      "[Pi_mono]"
  type_intrs  "[[UN_upper_cardinal, le_nat_Un_cardinal] MRS le_trans]   
	       @ inf_datatype_intrs"


end
