(*  Title:      ZF/ex/Ntree.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition n-ary branching trees
Demonstrates a simple use of function space in a datatype definition

Based upon ex/Term.thy
*)

Ntree = Main +
consts
  ntree    :: i=>i
  maptree  :: i=>i
  maptree2 :: [i,i] => i

datatype
  "ntree(A)" = Branch ("a \\<in> A", "h \\<in> (\\<Union>n \\<in> nat. n -> ntree(A))")
  monos       "[[subset_refl, Pi_mono] MRS UN_mono]"    (*MUST have this form*)
  type_intrs  "[nat_fun_univ RS subsetD]"
  type_elims   UN_E

datatype
  "maptree(A)" = Sons ("a \\<in> A", "h \\<in> maptree(A) -||> maptree(A)")
  monos        FiniteFun_mono1         (*Use monotonicity in BOTH args*)
  type_intrs  "[FiniteFun_univ1 RS subsetD]"

datatype
  "maptree2(A,B)" = Sons2 ("a \\<in> A", "h \\<in> B -||> maptree2(A,B)")
  monos       "[subset_refl RS FiniteFun_mono]"
  type_intrs   FiniteFun_in_univ'


constdefs
  ntree_rec  :: [[i,i,i]=>i, i] => i
   "ntree_rec(b) == 
    Vrecursor(%pr. ntree_case(%x h. b(x, h, \\<lambda>i \\<in> domain(h). pr`(h`i))))"

constdefs
    ntree_copy     :: i=>i
    "ntree_copy(z) == ntree_rec(%x h r. Branch(x,r), z)"

end
