(*  Title:      HOL/Wellfounded_Relations
    ID:         $Id$
    Author:     Konrad Slind
    Copyright   1995 TU Munich

Derived WF relations: inverse image, lexicographic product, measure, ...

The simple relational product, in which (x',y')<(x,y) iff x'<x and y'<y, is a
subset of the lexicographic product, and therefore does not need to be defined
separately.
*)

Wellfounded_Relations = Finite +

(* actually belongs to theory Finite *)
instance unit :: finite                  (finite_unit)
instance "*" :: (finite,finite) finite   (finite_Prod)


constdefs
 less_than :: "(nat*nat)set"
"less_than == trancl pred_nat"

 inv_image :: "('b * 'b)set => ('a => 'b) => ('a * 'a)set"
"inv_image r f == {(x,y). (f(x), f(y)) : r}"

 measure   :: "('a => nat) => ('a * 'a)set"
"measure == inv_image less_than"

 lex_prod  :: "[('a*'a)set, ('b*'b)set] => (('a*'b)*('a*'b))set"
               (infixr "<*lex*>" 80)
"ra <*lex*> rb == {((a,b),(a',b')). (a,a') : ra | a=a' & (b,b') : rb}"

 (* finite proper subset*)
 finite_psubset  :: "('a set * 'a set) set"
"finite_psubset == {(A,B). A < B & finite B}"

(* For rec_defs where the first n parameters stay unchanged in the recursive
   call. See While for an application.
*)
 same_fst :: "('a => bool) => ('a => ('b * 'b)set) => (('a*'b)*('a*'b))set"
"same_fst P R == {((x',y'),(x,y)) . x'=x & P x & (y',y) : R x}"

end
