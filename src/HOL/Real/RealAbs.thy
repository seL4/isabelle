(*  Title       : RealAbs.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Absolute value function for the reals
*) 

RealAbs = RealArith +


defs
  real_abs_def "abs r == (if (Numeral0::real) <= r then r else -r)"

end
