(*  Title       : RealAbs.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Absolute value function for the reals
*) 

RealAbs = RealBin +


defs
  abs_real_def "abs r == (if (#0::real) <= r then r else -r)"

end
