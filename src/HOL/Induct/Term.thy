(*  Title:      HOL/ex/Term
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Terms over a given alphabet -- function applications; illustrates list functor
  (essentially the same type as in Trees & Forests)

There is no constructor APP because it is simply cons ($) 
*)

Term = SList +

types   'a term

arities term :: (term)term

consts
  term          :: 'a item set => 'a item set
  Rep_term      :: 'a term => 'a item
  Abs_term      :: 'a item => 'a term
  Rep_Tlist     :: 'a term list => 'a item
  Abs_Tlist     :: 'a item => 'a term list
  App           :: ['a, ('a term)list] => 'a term
  Term_rec      :: ['a item, ['a item , 'a item, 'b list]=>'b] => 'b
  term_rec      :: ['a term, ['a ,'a term list, 'b list]=>'b] => 'b

inductive "term(A)"
  intrs
    APP_I "[| M: A;  N : list(term(A)) |] ==> M$N : term(A)"
  monos   "[list_mono]"

defs
  (*defining abstraction/representation functions for term list...*)
  Rep_Tlist_def "Rep_Tlist == Rep_map(Rep_term)"
  Abs_Tlist_def "Abs_Tlist == Abs_map(Abs_term)"

  (*defining the abstract constants*)
  App_def       "App a ts == Abs_term(Leaf(a) $ Rep_Tlist(ts))"

  (*list recursion*)
  Term_rec_def  
   "Term_rec M d == wfrec (trancl pred_sexp)
           (%g. Split(%x y. d x y (Abs_map g y))) M"

  term_rec_def
   "term_rec t d == 
   Term_rec (Rep_term t) (%x y r. d (inv Leaf x) (Abs_Tlist(y)) r)"

rules
    (*faking a type definition for term...*)
  Rep_term              "Rep_term(n): term(range(Leaf))"
  Rep_term_inverse      "Abs_term(Rep_term(t)) = t"
  Abs_term_inverse      "M: term(range(Leaf)) ==> Rep_term(Abs_term(M)) = M"
end
