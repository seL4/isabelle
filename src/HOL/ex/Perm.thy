(*  Title: 	HOL/ex/Perm.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Permutations: example of an inductive definition
*)

Perm = List +

consts  perm    :: "('a list * 'a list) set"   
syntax "@perm"  :: "['a list, 'a list] => bool" ("_ <~~> _"  [50] 50)

translations
    "x <~~> y" == "(x,y) : perm"

inductive "perm"
  intrs
    Nil   "[] <~~> []"
    swap  "y#x#l <~~> x#y#l"
    Cons  "xs <~~> ys ==> z#xs <~~> z#ys"
    trans "[| xs <~~> ys;  ys <~~> zs |] ==> xs <~~> zs"

end
