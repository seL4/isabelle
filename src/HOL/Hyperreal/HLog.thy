(*  Title       : HLog.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2000,2001 University of Edinburgh
    Description : hyperreal base logarithms
*)

HLog = Log + HTranscendental + 


constdefs

    powhr  :: [hypreal,hypreal] => hypreal     (infixr 80)
    "x powhr a == ( *f* exp) (a * ( *f* ln) x)"
  
    hlog :: [hypreal,hypreal] => hypreal
    "hlog a x == Abs_hypreal(UN A: Rep_hypreal(a).UN X: Rep_hypreal(x).
			     hyprel `` {%n. log (A n) (X n)})"

end