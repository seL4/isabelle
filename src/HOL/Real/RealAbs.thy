(*  Title       : RealAbs.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Absolute value function for the reals
*) 

RealAbs = Real +

constdefs
   rabs   :: real => real
   "rabs r      == if 0r<=r then r else -r" 

end