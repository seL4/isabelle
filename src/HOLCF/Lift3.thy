Lift3 = Lift2 + 

default term

arities 
 "lift" :: (term)pcpo

consts 
 flift1      :: "('a => 'b::pcpo) => ('a lift -> 'b)"
 blift        :: "bool => tr"  
 plift        :: "('a => bool) => 'a lift -> tr"   
 flift2      :: "('a => 'b) => ('a lift -> 'b lift)"

translations
 "UU" <= "Undef"

defs
 blift_def
  "blift b == (if b then TT else FF)"

 flift1_def
  "flift1 f  == (LAM x. (case x of 
                   Undef => UU
                 | Def y => (f y)))"

 flift2_def
  "flift2 f == (LAM x. (case x of 
                              Undef => Undef
                            | Def y => Def (f y)))"

 plift_def
  "plift p == (LAM x. flift1 (%a. blift (p a))`x)"


rules
 inst_lift_pcpo "(UU::'a lift) = Undef"

end

