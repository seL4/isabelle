(*  Title       : Star.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : defining *-transforms in NSA which extends sets of reals, 
                  and real=>real functions
*) 

Star = NSA +

constdefs
    (* nonstandard extension of sets *)
    starset :: real set => hypreal set          ("*s* _" [80] 80)
    "*s* A  == {x. ALL X: Rep_hypreal(x). {n::nat. X n : A}: FreeUltrafilterNat}"

    (* internal sets *)
    starset_n :: (nat => real set) => hypreal set        ("*sn* _" [80] 80)
    "*sn* As  == {x. ALL X: Rep_hypreal(x). {n::nat. X n : (As n)}: FreeUltrafilterNat}"   
    
    InternalSets :: "hypreal set set"
    "InternalSets == {X. EX As. X = *sn* As}"

    (* nonstandard extension of function *)
    is_starext  ::  [hypreal => hypreal, real => real] => bool
    "is_starext F f == (ALL x y. EX X: Rep_hypreal(x). EX Y: Rep_hypreal(y).
                        ((y = (F x)) = ({n. Y n = f(X n)} : FreeUltrafilterNat)))"
    
    starfun :: (real => real) => hypreal => hypreal        ("*f* _" [80] 80)
    "*f* f  == (%x. Abs_hypreal(UN X: Rep_hypreal(x). hyprel^^{%n. f (X n)}))" 

    (* internal functions *)
    starfun_n :: (nat => (real => real)) => hypreal => hypreal        ("*fn* _" [80] 80)
    "*fn* F  == (%x. Abs_hypreal(UN X: Rep_hypreal(x). hyprel^^{%n. (F n)(X n)}))" 

    InternalFuns :: (hypreal => hypreal) set
    "InternalFuns == {X. EX F. X = *fn* F}"
end



