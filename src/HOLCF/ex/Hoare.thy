(*  Title:	HOLCF/ex/hoare.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright	1993 Technische Universitaet Muenchen

Theory for an example by C.A.R. Hoare 

p x = if b1 x 
         then p (g x)
         else x fi

q x = if b1 x orelse b2 x 
         then q (g x)
         else x fi

Prove: for all b1 b2 g . 
            q o p  = q 

In order to get a nice notation we fix the functions b1,b2 and g in the
signature of this example

*)

Hoare = Tr2 +

consts
	b1:: "'a -> tr"
	b2:: "'a -> tr"
	 g:: "'a -> 'a"
	p :: "'a -> 'a"
	q :: "'a -> 'a"

defs

  p_def  "p == fix`(LAM f. LAM x.
                 If b1`x then f`(g`x) else x fi)"

  q_def  "q == fix`(LAM f. LAM x.
                 If b1`x orelse b2`x then f`(g`x) else x fi)"

end
 
