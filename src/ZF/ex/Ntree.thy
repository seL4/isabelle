(*  Title: 	ZF/ex/Ntree.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition n-ary branching trees
Demonstrates a simple use of function space in a datatype definition
   and also "nested" monotonicity theorems

Based upon ex/Term.thy
*)

Ntree = InfDatatype +
consts
  ntree :: "i=>i"

datatype
  "ntree(A)" = Branch ("a: A", "h: (UN n:nat. n -> ntree(A))")
  monos	      "[[subset_refl, Pi_mono] MRS UN_mono]"
  type_intrs  "[nat_fun_univ RS subsetD]"
  type_elims  "[UN_E]"

end
