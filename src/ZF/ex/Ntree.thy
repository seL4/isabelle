(*  Title: 	ZF/ex/Ntree.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition n-ary branching trees
Demonstrates a simple use of function space in a datatype definition

Based upon ex/Term.thy
*)

Ntree = InfDatatype +
consts
  ntree    :: i=>i
  maptree  :: i=>i
  maptree2 :: [i,i] => i

datatype
  "ntree(A)" = Branch ("a: A", "h: (UN n:nat. n -> ntree(A))")
  monos	      "[[subset_refl, Pi_mono] MRS UN_mono]"	(*MUST have this form*)
  type_intrs  "[nat_fun_univ RS subsetD]"
  type_elims  "[UN_E]"

datatype
  "maptree(A)" = Sons ("a: A", "h: maptree(A) -||> maptree(A)")
  monos	      "[FiniteFun_mono1]"	(*Use monotonicity in BOTH args*)
  type_intrs  "[FiniteFun_univ1 RS subsetD]"

datatype
  "maptree2(A,B)" = Sons2 ("a: A", "h: B -||> maptree2(A,B)")
  monos	      "[subset_refl RS FiniteFun_mono]"
  type_intrs  "[FiniteFun_in_univ']"

end
