(*  Title: 	ZF/ex/Term.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Terms over an alphabet.
Illustrates the list functor (essentially the same type as in Trees & Forests)
*)

Term = List +
consts
  term_rec  :: [i, [i,i,i]=>i] => i
  term_map  :: [i=>i, i] => i
  term_size :: i=>i
  reflect   :: i=>i
  preorder  :: i=>i

  term      :: i=>i

datatype
  "term(A)" = Apply ("a: A", "l: list(term(A))")
  monos	      "[list_mono]"

  type_elims  "[make_elim (list_univ RS subsetD)]"
(*Or could have
    type_intrs  "[list_univ RS subsetD]"
*)

defs
  term_rec_def
   "term_rec(t,d) == 
   Vrec(t, %t g. term_case(%x zs. d(x, zs, map(%z.g`z, zs)), t))"

  term_map_def	"term_map(f,t) == term_rec(t, %x zs rs. Apply(f(x), rs))"

  term_size_def	"term_size(t) == term_rec(t, %x zs rs. succ(list_add(rs)))"

  reflect_def	"reflect(t) == term_rec(t, %x zs rs. Apply(x, rev(rs)))"

  preorder_def	"preorder(t) == term_rec(t, %x zs rs. Cons(x, flat(rs)))"

end
