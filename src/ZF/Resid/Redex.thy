(*  Title: 	Redex.thy
    ID:         $Id$
    Author: 	Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

Redex = Univ +
consts
  redexes     :: "i"

datatype
  "redexes" = Var ("n: nat")	        
            | Fun ("t: redexes")
            | App ("b:bool" ,"f:redexes" , "a:redexes")
  type_intrs "[bool_into_univ]"
  

consts
  redex_rec   	:: "[i, i=>i, [i,i]=>i, [i,i,i,i,i]=>i]=>i"
 
defs
  redex_rec_def
   "redex_rec(p,b,c,d) == \
\   Vrec(p, %p g.redexes_case(b, %x.c(x,g`x),   \
\                             %n x y.d(n, x, y, g`x, g`y), p))"
end

