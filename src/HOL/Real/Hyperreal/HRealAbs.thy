(*  Title       : HRealAbs.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Absolute value function for the hyperreals
*) 

HRealAbs = HyperOrd + RealAbs + 

defs
    hrabs_def "abs r  == if (0::hypreal) <=r then r else -r" 

end