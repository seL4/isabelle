(*  Title:      HOL/Finite.thy
    ID:         $Id$
    Author:     Lawrence C Paulson & Tobias Nipkow
    Copyright   1995  University of Cambridge & TU Muenchen

Finite sets, their cardinality, and a fold functional.
*)

Finite = Divides + Power + Inductive + SetInterval +

consts Finites :: 'a set set

inductive "Finites"
  intrs
    emptyI  "{} : Finites"
    insertI "A : Finites ==> insert a A : Finites"

syntax finite :: 'a set => bool
translations  "finite A"  ==  "A : Finites"

axclass	finite<term
  finite "finite UNIV"

(* This definition, although traditional, is ugly to work with
constdefs
  card :: 'a set => nat
  "card A == LEAST n. ? f. A = {f i |i. i<n}"
Therefore we have switched to an inductive one:
*)

consts cardR :: "('a set * nat) set"

inductive cardR
intrs
  EmptyI  "({},0) : cardR"
  InsertI "[| (A,n) : cardR; a ~: A |] ==> (insert a A, Suc n) : cardR"

constdefs
  card :: 'a set => nat
 "card A == @n. (A,n) : cardR"

(*
A "fold" functional for finite sets.  For n non-negative we have
    fold f e {x1,...,xn} = f x1 (... (f xn e))
where f is at least left-commutative.
*)

consts foldSet :: "[['b,'a] => 'a, 'a] => ('b set * 'a) set"

inductive "foldSet f e"
  intrs
    emptyI   "({}, e) : foldSet f e"

    insertI  "[| x ~: A;  (A,y) : foldSet f e |]
	      ==> (insert x A, f x y) : foldSet f e"

constdefs
   fold :: "[['b,'a] => 'a, 'a, 'b set] => 'a"
  "fold f e A == @x. (A,x) : foldSet f e"

   setsum :: "('a => 'b) => 'a set => ('b::{plus, zero})"
  "setsum f A == if finite A then fold (op+ o f) 0 A else 0"

locale LC =
  fixes
    f    :: ['b,'a] => 'a
  assumes
    lcomm    "f x (f y z) = f y (f x z)"

locale ACe =
  fixes 
    f    :: ['a,'a] => 'a
    e    :: 'a
  assumes
    ident    "f x e = x"
    commute  "f x y = f y x"
    assoc    "f (f x y) z = f x (f y z)"

end
