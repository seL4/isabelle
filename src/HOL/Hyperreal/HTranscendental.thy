(*  Title       : HTranscendental.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
    Description : Nonstandard extensions of transcendental functions
*)

HTranscendental = Transcendental + IntFloor + 

constdefs


    (* define exponential function using standard part *)
    exphr :: real => hypreal
    "exphr x ==  st(sumhr (0, whn, %n. inverse(real (fact n)) * (x ^ n)))" 

    sinhr :: real => hypreal
    "sinhr x == st(sumhr (0, whn, %n. (if even(n) then 0 else
             ((-1) ^ ((n - 1) div 2))/(real (fact n))) * (x ^ n)))"
  
    coshr :: real => hypreal
    "coshr x == st(sumhr (0, whn, %n. (if even(n) then
            ((-1) ^ (n div 2))/(real (fact n)) else 0) * x ^ n))"
end