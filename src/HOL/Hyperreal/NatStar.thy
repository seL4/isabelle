(*  Title       : NatStar.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : defining *-transforms in NSA which extends 
                  sets of reals, and nat=>real, nat=>nat functions
*) 

NatStar = RealPow + HyperPow + 

constdefs

  (* internal sets and nonstandard extensions -- see Star.thy as well *)

    starsetNat :: nat set => hypnat set          ("*sNat* _" [80] 80)
    "*sNat* A  == {x. ALL X: Rep_hypnat(x). {n::nat. X n : A}: FreeUltrafilterNat}"

    starsetNat_n :: (nat => nat set) => hypnat set        ("*sNatn* _" [80] 80)
    "*sNatn* As  == {x. ALL X: Rep_hypnat(x). {n::nat. X n : (As n)}: FreeUltrafilterNat}"   

    InternalNatSets :: "hypnat set set"
    "InternalNatSets == {X. EX As. X = *sNatn* As}"

    (* star transform of functions f:Nat --> Real *)

    starfunNat :: (nat => real) => hypnat => hypreal        ("*fNat* _" [80] 80)
    "*fNat* f  == (%x. Abs_hypreal(UN X: Rep_hypnat(x). hyprel``{%n. f (X n)}))" 

    starfunNat_n :: (nat => (nat => real)) => hypnat => hypreal        ("*fNatn* _" [80] 80)
    "*fNatn* F  == (%x. Abs_hypreal(UN X: Rep_hypnat(x). hyprel``{%n. (F n)(X n)}))" 

    InternalNatFuns :: (hypnat => hypreal) set
    "InternalNatFuns == {X. EX F. X = *fNatn* F}"

    (* star transform of functions f:Nat --> Nat *)

    starfunNat2 :: (nat => nat) => hypnat => hypnat        ("*fNat2* _" [80] 80)
    "*fNat2* f  == (%x. Abs_hypnat(UN X: Rep_hypnat(x). hypnatrel``{%n. f (X n)}))" 

    starfunNat2_n :: (nat => (nat => nat)) => hypnat => hypnat        ("*fNat2n* _" [80] 80)
    "*fNat2n* F  == (%x. Abs_hypnat(UN X: Rep_hypnat(x). hypnatrel``{%n. (F n)(X n)}))" 

    InternalNatFuns2 :: (hypnat => hypnat) set
    "InternalNatFuns2 == {X. EX F. X = *fNat2n* F}"
end


