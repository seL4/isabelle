(*  Title:      ZF/ex/Brouwer.thy
    ID:         $ $
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Infinite branching datatype definitions
  (1) the Brouwer ordinals
  (2) the Martin-Löf wellordering type
*)

Brouwer = Main +

consts
  brouwer :: i
  Well    :: [i,i=>i]=>i
 
datatype <= "Vfrom(0, csucc(nat))"
  "brouwer" = Zero | Suc ("b \\<in> brouwer") | Lim ("h \\<in> nat -> brouwer")
  monos        Pi_mono
  type_intrs  "inf_datatype_intrs"

(*The union with nat ensures that the cardinal is infinite*)
datatype <= "Vfrom(A Un (\\<Union>x \\<in> A. B(x)), csucc(nat Un |\\<Union>x \\<in> A. B(x)|))"
  "Well(A,B)" = Sup ("a \\<in> A", "f \\<in> B(a) -> Well(A,B)")
  monos        Pi_mono
  type_intrs  "[[UN_upper_cardinal, le_nat_Un_cardinal] MRS le_trans]   
               @ inf_datatype_intrs"


end
