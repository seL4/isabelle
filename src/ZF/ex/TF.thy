(*  Title:      ZF/ex/TF.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Trees & forests, a mutually recursive type definition.
*)

TF = List +
consts
  tree, forest, tree_forest    :: i=>i

datatype
  "tree(A)"   = Tcons ("a \\<in> A",  "f \\<in> forest(A)")
and
  "forest(A)" = Fnil  |  Fcons ("t \\<in> tree(A)",  "f \\<in> forest(A)")


consts
  map      :: [i=>i, i] => i
  size     :: i=>i
  preorder :: i=>i
  list_of_TF  :: i=>i
  of_list  :: i=>i
  reflect  :: i=>i

primrec
  "list_of_TF (Tcons(x,f))  = [Tcons(x,f)]"
  "list_of_TF (Fnil)        = []"
  "list_of_TF (Fcons(t,tf)) = Cons (t, list_of_TF(tf))"

primrec
  "of_list([])        = Fnil"
  "of_list(Cons(t,l)) = Fcons(t, of_list(l))"

primrec
  "map (h, Tcons(x,f))  = Tcons(h(x), map(h,f))"
  "map (h, Fnil)        = Fnil"
  "map (h, Fcons(t,tf)) = Fcons (map(h, t), map(h, tf))"

primrec
  "size (Tcons(x,f))  = succ(size(f))"
  "size (Fnil)        = 0"
  "size (Fcons(t,tf)) = size(t) #+ size(tf)"
 
primrec
  "preorder (Tcons(x,f))  = Cons(x, preorder(f))"
  "preorder (Fnil)        = Nil"
  "preorder (Fcons(t,tf)) = preorder(t) @ preorder(tf)"
 
primrec
  "reflect (Tcons(x,f))  = Tcons(x, reflect(f))"
  "reflect (Fnil)        = Fnil"
  "reflect (Fcons(t,tf)) = of_list
                               (list_of_TF (reflect(tf)) @
				Cons(reflect(t), Nil))"

end
