(*  Title       : Lubs.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Upper bounds, lubs definitions
                  suggested by James Margetson
*) 


Lubs = Set +

consts
    
    "*<=" :: ['a set, 'a] => bool     (infixl 70)
    "<=*" :: ['a, 'a set] => bool     (infixl 70)

constdefs
    leastP      :: ['a =>bool,'a] => bool
    "leastP P x == (P x & x <=* Collect P)"

    isLub       :: ['a set, 'a set, 'a] => bool    
    "isLub R S x  == leastP (isUb R S) x"

    isUb        :: ['a set, 'a set, 'a] => bool     
    "isUb R S x   == S *<= x & x: R"

    ubs         :: ['a set, 'a set] => 'a set
    "ubs R S      == Collect (isUb R S)"

defs
    setle_def
    "S *<= x    == (ALL y: S. y <= x)"

    setge_def
    "x <=* S    == (ALL y: S. x <= y)"

end                    

    
