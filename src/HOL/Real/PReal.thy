(*  Title       : PReal.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The positive reals as Dedekind sections of positive
                  rationals. Fundamentals of Abstract Analysis [Gleason- p. 121] 
                  provides some of the definitions.
*)

PReal = PRat +

typedef preal = "{A::prat set. {} < A & A < {q::prat. True} &
                               (!y: A. ((!z. z < y --> z: A) &
                                        (? u: A. y < u)))}"      (preal_1)
instance
   preal :: {ord, plus, times}

constdefs
  preal_of_prat :: prat => preal             
   "preal_of_prat q     == Abs_preal({x::prat. x < q})"

  pinv       :: preal => preal
  "pinv(R)   == Abs_preal({w. ? y. w < y & qinv y ~: Rep_preal(R)})" 

  psup       :: preal set => preal
  "psup(P)   == Abs_preal({w. ? X: P. w: Rep_preal(X)})"

defs

  preal_add_def
        "R + S == Abs_preal({w. ? x: Rep_preal(R). ? y: Rep_preal(S). w = x + y})"

  preal_mult_def
        "R * S == Abs_preal({w. ? x: Rep_preal(R). ? y: Rep_preal(S). w = x * y})"

  preal_less_def
        "R < (S::preal) == Rep_preal(R) < Rep_preal(S)"

  preal_le_def
        "R <= (S::preal) == Rep_preal(R) <= Rep_preal(S)"
 
end

