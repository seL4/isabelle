(*  Title:      HOL/FoldSet
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1998  University of Cambridge

A "fold" functional for finite sets.  For n non-negative we have
    fold f e {x1,...,xn} = f x1 (... (f xn e))
where f is an associative-commutative function and e is its identity.
*)

FoldSet = Finite +

consts foldSet :: "[['a,'a] => 'a, 'a] => ('a set * 'a) set"

inductive "foldSet f e"
  intrs
    emptyI   "({}, e) : foldSet f e"

    insertI  "[| x ~: A;  (A,y) : foldSet f e |]
	      ==> (insert x A, f x y) : foldSet f e"

constdefs fold :: "[['a,'a] => 'a, 'a, 'a set] => 'a"
  "fold f e A == @x. (A,x) : foldSet f e"
  
locale ACI =
  fixes 
    f    :: ['a,'a] => 'a
    e    :: 'a
  assumes
    ident    "!! x. f x e = x"
    commute  "!! x y. f x y = f y x"
    assoc    "!! x y z. f (f x y) z = f x (f y z)"
  defines
    (*nothing*)
end


