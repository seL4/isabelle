(*  Title:      HOL/WF_Rel
    ID:         $Id$
    Author:     Konrad Slind
    Copyright   1995 TU Munich

Derived wellfounded relations: inverse image, relational product, measure, ...
*)

WF_Rel = Finite +
consts
  less_than :: "(nat*nat)set"
  inv_image :: "('b * 'b)set => ('a => 'b) => ('a * 'a)set"
  measure   :: "('a => nat) => ('a * 'a)set"
  "**"      :: "[('a*'a)set, ('b*'b)set] => (('a*'b)*('a*'b))set" (infixl 70)
  rprod     :: "[('a*'a)set, ('b*'b)set] => (('a*'b)*('a*'b))set"
  finite_psubset  :: "('a set * 'a set) set"


defs
  less_than_def "less_than == trancl pred_nat"

  inv_image_def "inv_image r f == {(x,y). (f(x), f(y)) : r}"

  measure_def   "measure == inv_image less_than"

  lex_prod_def  "ra**rb == {p. ? a a' b b'. 
                                p = ((a,b),(a',b')) & 
                               ((a,a') : ra | a=a' & (b,b') : rb)}"

  rprod_def     "rprod ra rb == {p. ? a a' b b'. 
                                p = ((a,b),(a',b')) & 
                               ((a,a') : ra & (b,b') : rb)}"

  (* finite proper subset*)
  finite_psubset_def "finite_psubset == {(A,B). A < B & finite B}"
end
