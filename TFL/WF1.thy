(* Derived wellfounded relations, plus customized-for-TFL theorems from WF *)

WF1 = List +
consts
 inv_image  :: "('b * 'b)set => ('a => 'b) => ('a * 'a)set"
 measure    :: "('a => nat) => ('a * 'a)set"
    "**"    :: "[('a*'a)set, ('b*'b)set] => (('a*'b)*('a*'b))set" (infixl 70)
   rprod    :: "[('a*'a)set, ('b*'b)set] => (('a*'b)*('a*'b))set"
   emptyr   :: "('a * 'b) set"
 pred_list  :: "('a list * 'a list) set"

defs
  inv_image_def "inv_image R f == {p. (f(fst p), f(snd p)) : R}"

  measure_def   "measure == inv_image (trancl pred_nat)"

  lex_prod_def  "ra**rb == {p. ? a a' b b'. 
                                p = ((a,b),(a',b')) & 
                               ((a,a') : ra | a=a' & (b,b') : rb)}"

  rprod_def     "rprod ra rb == {p. ? a a' b b'. 
                                p = ((a,b),(a',b')) & 
                               ((a,a') : ra & (b,b') : rb)}"

  emptyr_def    "emptyr == {}"
  pred_list_def "pred_list == {p. ? h. snd p = h#(fst p)}"
end
