(*  Title: 	ZF/AC/Transrec2.thy
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

Transfinite recursion introduced to handle definitions based on the three
cases of ordinals.
*)

Transrec2 = OrdQuant + Epsilon +

consts
  
  transrec2               :: "[i, i, [i,i]=>i] =>i"

defs

  transrec2_def  "transrec2(alpha, a, b) ==   			
		         transrec(alpha, %i r. if(i=0,   	
		                  a, if(EX j. i=succ(j),   	
		                  b(THE j. i=succ(j), r`(THE j. i=succ(j))),   
		                  UN j<i. r`j)))"

end
