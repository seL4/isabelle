(*  Title       : CStar.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
    Description : defining *-transforms in NSA which extends sets of complex numbers, 
                  and complex functions
*)

CStar = NSCA + 

constdefs

    (* nonstandard extension of sets *)
    starsetC :: complex set => hcomplex set          ("*sc* _" [80] 80)
    "*sc* A  == {x. ALL X: Rep_hcomplex(x). {n::nat. X n : A}: FreeUltrafilterNat}"

    (* internal sets *)
    starsetC_n :: (nat => complex set) => hcomplex set        ("*scn* _" [80] 80)
    "*scn* As  == {x. ALL X: Rep_hcomplex(x). {n::nat. X n : (As n)}: FreeUltrafilterNat}"   
    
    InternalCSets :: "hcomplex set set"
    "InternalCSets == {X. EX As. X = *scn* As}"

    (* star transform of functions f: Complex --> Complex *)

    starfunC :: (complex => complex) => hcomplex => hcomplex        ("*fc* _" [80] 80)
    "*fc* f  == (%x. Abs_hcomplex(UN X: Rep_hcomplex(x). hcomplexrel``{%n. f (X n)}))" 

    starfunC_n :: (nat => (complex => complex)) => hcomplex => hcomplex  ("*fcn* _" [80] 80)
    "*fcn* F  == (%x. Abs_hcomplex(UN X: Rep_hcomplex(x). hcomplexrel``{%n. (F n)(X n)}))" 

    InternalCFuns :: (hcomplex => hcomplex) set
    "InternalCFuns == {X. EX F. X = *fcn* F}"


    (* star transform of functions f: Real --> Complex *)

    starfunRC :: (real => complex) => hypreal => hcomplex        ("*fRc* _" [80] 80)
    "*fRc* f  == (%x. Abs_hcomplex(UN X: Rep_hypreal(x). hcomplexrel``{%n. f (X n)}))" 

    starfunRC_n :: (nat => (real => complex)) => hypreal => hcomplex  ("*fRcn* _" [80] 80)
    "*fRcn* F  == (%x. Abs_hcomplex(UN X: Rep_hypreal(x). hcomplexrel``{%n. (F n)(X n)}))" 

    InternalRCFuns :: (hypreal => hcomplex) set
    "InternalRCFuns == {X. EX F. X = *fRcn* F}"

    (* star transform of functions f: Complex --> Real; needed for Re and Im parts *)

    starfunCR :: (complex => real) => hcomplex => hypreal        ("*fcR* _" [80] 80)
    "*fcR* f  == (%x. Abs_hypreal(UN X: Rep_hcomplex(x). hyprel``{%n. f (X n)}))" 

    starfunCR_n :: (nat => (complex => real)) => hcomplex => hypreal  ("*fcRn* _" [80] 80)
    "*fcRn* F  == (%x. Abs_hypreal(UN X: Rep_hcomplex(x). hyprel``{%n. (F n)(X n)}))" 

    InternalCRFuns :: (hcomplex => hypreal) set
    "InternalCRFuns == {X. EX F. X = *fcRn* F}"

end