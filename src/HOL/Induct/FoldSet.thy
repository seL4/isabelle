(*  Title:      HOL/FoldSet
    ID:         $Id$
    Author:     Lawrence C Paulson, Tobias Nipkow
    Copyright   1998  University of Cambridge

A "fold" functional for finite sets.  For n non-negative we have
    fold f e {x1,...,xn} = f x1 (... (f xn e))
where f is at least left-commutative.
*)

FoldSet = Finite +

consts foldSet :: "[['b,'a] => 'a, 'a] => ('b set * 'a) set"

inductive "foldSet f e"
  intrs
    emptyI   "({}, e) : foldSet f e"

    insertI  "[| x ~: A;  (A,y) : foldSet f e |]
	      ==> (insert x A, f x y) : foldSet f e"

constdefs
   fold :: "[['b,'a] => 'a, 'a, 'b set] => 'a"
  "fold f e A == @x. (A,x) : foldSet f e"
  (* A frequent instance: *)
   setsum :: ('a => nat) => 'a set => nat
  "setsum f == fold (%x n. f x + n) 0"

locale LC =
  fixes
    f    :: ['b,'a] => 'a
  assumes
    lcomm    "!! x y z. f x (f y z) = f y (f x z)"
  defines
    (*nothing*)

locale ACe =
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
