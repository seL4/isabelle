(*  Title:      HOL/WF_Rel
    ID:         $Id$
    Author:     Konrad Slind
    Copyright   1995 TU Munich

Derived WF relations: inverse image, lexicographic product, measure, ...

The simple relational product, in which (x',y')<(x,y) iff x'<x and y'<y, is a
subset of the lexicographic product, and therefore does not need to be defined
separately.
*)

WF_Rel = Finite +

(* actually belongs to Finite.thy *)
instance "*" :: (finite,finite) finite   (finite_Prod) 

consts
  less_than :: "(nat*nat)set"
  inv_image :: "('b * 'b)set => ('a => 'b) => ('a * 'a)set"
  measure   :: "('a => nat) => ('a * 'a)set"
  "**"      :: "[('a*'a)set, ('b*'b)set] => (('a*'b)*('a*'b))set" (infixl 70)
  finite_psubset  :: "('a set * 'a set) set"


defs
  less_than_def "less_than == trancl pred_nat"

  inv_image_def "inv_image r f == {(x,y). (f(x), f(y)) : r}"

  measure_def   "measure == inv_image less_than"

  lex_prod_def  "ra**rb == {p. ? a a' b b'. 
                                p = ((a,b),(a',b')) & 
                               ((a,a') : ra | a=a' & (b,b') : rb)}"

  (* finite proper subset*)
  finite_psubset_def "finite_psubset == {(A,B). A < B & finite B}"
end
