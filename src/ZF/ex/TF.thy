(*  Title: 	ZF/ex/TF.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Trees & forests, a mutually recursive type definition.
*)

TF = List +
consts
  TF_rec      :: [i, [i,i,i]=>i, i, [i,i,i,i]=>i] => i
  TF_map      :: [i=>i, i] => i
  TF_size     :: i=>i
  TF_preorder :: i=>i
  list_of_TF  :: i=>i
  TF_of_list  :: i=>i

  tree, forest, tree_forest    :: i=>i

datatype
  "tree(A)"   = Tcons ("a: A",  "f: forest(A)")
and
  "forest(A)" = Fnil  |  Fcons ("t: tree(A)",  "f: forest(A)")

defs
  TF_rec_def
    "TF_rec(z,b,c,d) == Vrec(z,  			
      %z r. tree_forest_case(%x f. b(x, f, r`f), 	
                             c, 			
		              %t f. d(t, f, r`t, r`f), z))"

  list_of_TF_def
    "list_of_TF(z) == TF_rec(z, %x f r. [Tcons(x,f)], [], 
		             %t f r1 r2. Cons(t, r2))"

  TF_of_list_def
    "TF_of_list(f) == list_rec(f, Fnil,  %t f r. Fcons(t,r))"

  TF_map_def
    "TF_map(h,z) == TF_rec(z, %x f r.Tcons(h(x),r), Fnil, 
                           %t f r1 r2. Fcons(r1,r2))"

  TF_size_def
    "TF_size(z) == TF_rec(z, %x f r.succ(r), 0, %t f r1 r2. r1#+r2)"

  TF_preorder_def
    "TF_preorder(z) == TF_rec(z, %x f r.Cons(x,r), Nil, %t f r1 r2. r1@r2)"

end
