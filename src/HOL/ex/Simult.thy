(*  Title: 	HOL/ex/Simult
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

A simultaneous recursive type definition: trees & forests

This is essentially the same data structure that on ex/term.ML, which is
simpler because it uses list as a new type former.  The approach in this
file may be superior for other simultaneous recursions.

The inductive definition package does not help defining this sort of mutually
recursive data structure because it uses Inl, Inr instead of In0, In1.
*)

Simult = SList +

types    'a tree
         'a forest

arities  tree,forest :: (term)term

consts
  TF          :: "'a item set => 'a item set"
  FNIL        :: "'a item"
  TCONS,FCONS :: "['a item, 'a item] => 'a item"
  Rep_Tree    :: "'a tree => 'a item"
  Abs_Tree    :: "'a item => 'a tree"
  Rep_Forest  :: "'a forest => 'a item"
  Abs_Forest  :: "'a item => 'a forest"
  Tcons       :: "['a, 'a forest] => 'a tree"
  Fcons       :: "['a tree, 'a forest] => 'a forest"
  Fnil        :: "'a forest"
  TF_rec      :: "['a item, ['a item , 'a item, 'b]=>'b,     \
\                 'b, ['a item , 'a item, 'b, 'b]=>'b] => 'b"
  tree_rec    :: "['a tree, ['a, 'a forest, 'b]=>'b,          \
\                 'b, ['a tree, 'a forest, 'b, 'b]=>'b] => 'b"
  forest_rec  :: "['a forest, ['a, 'a forest, 'b]=>'b,        \
\                  'b, ['a tree, 'a forest, 'b, 'b]=>'b] => 'b"

defs
     (*the concrete constants*)
  TCONS_def 	"TCONS M N == In0(M $ N)"
  FNIL_def	"FNIL      == In1(NIL)"
  FCONS_def	"FCONS M N == In1(CONS M N)"
     (*the abstract constants*)
  Tcons_def 	"Tcons a ts == Abs_Tree(TCONS (Leaf a) (Rep_Forest ts))"
  Fnil_def  	"Fnil       == Abs_Forest(FNIL)"
  Fcons_def 	"Fcons t ts == Abs_Forest(FCONS (Rep_Tree t) (Rep_Forest ts))"

  TF_def	"TF(A) == lfp(%Z. A <*> Part Z In1 \
\                           <+> ({Numb(0)} <+> Part Z In0 <*> Part Z In1))"

rules
  (*faking a type definition for tree...*)
  Rep_Tree 	   "Rep_Tree(n): Part (TF(range Leaf)) In0"
  Rep_Tree_inverse "Abs_Tree(Rep_Tree(t)) = t"
  Abs_Tree_inverse "z: Part (TF(range Leaf)) In0 ==> Rep_Tree(Abs_Tree(z)) = z"
    (*faking a type definition for forest...*)
  Rep_Forest 	     "Rep_Forest(n): Part (TF(range Leaf)) In1"
  Rep_Forest_inverse "Abs_Forest(Rep_Forest(ts)) = ts"
  Abs_Forest_inverse 
	"z: Part (TF(range Leaf)) In1 ==> Rep_Forest(Abs_Forest(z)) = z"


defs
     (*recursion*)
  TF_rec_def	
   "TF_rec M b c d == wfrec (trancl pred_sexp) M   \
\               (Case (Split(%x y g. b x y (g y))) \
\	              (List_case (%g.c) (%x y g. d x y (g x) (g y))))"

  tree_rec_def
   "tree_rec t b c d == \
\   TF_rec (Rep_Tree t) (%x y r. b (Inv Leaf x) (Abs_Forest y) r) \
\          c (%x y rt rf. d (Abs_Tree x) (Abs_Forest y) rt rf)"

  forest_rec_def
   "forest_rec tf b c d == \
\   TF_rec (Rep_Forest tf) (%x y r. b (Inv Leaf x) (Abs_Forest y) r) \
\          c (%x y rt rf. d (Abs_Tree x) (Abs_Forest y) rt rf)"
end
